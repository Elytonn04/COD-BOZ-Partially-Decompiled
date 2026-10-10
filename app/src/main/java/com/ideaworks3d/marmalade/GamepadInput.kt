package com.ideaworks3d.marmalade

import android.hardware.input.InputManager
import android.os.Handler
import android.os.Looper
import android.os.SystemClock
import android.util.Log
import android.view.InputDevice
import android.view.KeyEvent
import android.view.MotionEvent
import java.lang.ref.WeakReference
import kotlin.math.hypot
import kotlin.math.max
import kotlin.math.min

/**
 * Gamepad support for the Marmalade loader.
 *
 * The game logic lives in native code (`boz.s3e` / the .so files) and only
 * understands touch input forwarded through [LoaderThread.onMotionEvent].
 * Instead of touching the native side, this class translates a gamepad into
 * *synthetic touches* placed on top of the on-screen HUD controls:
 *
 *  - left stick   -> drags the on-screen move joystick
 *  - right stick  -> drags a "look" finger (camera), re-anchoring at the edges
 *  - buttons/triggers -> press-and-hold a touch on the matching HUD button
 *
 * The HUD positions below are expressed as fractions of the view size
 * (0.0..1.0) and are PLACEHOLDERS: calibrate them for the real layout.
 * With [LOG_TOUCH_POSITIONS] on, every real finger-down is logged to logcat
 * (tag "GamepadInput") as fractions, so you can tap each HUD button once
 * with a finger and copy the numbers into [Slot] / [Layout].
 *
 * Everything here runs on the UI thread, same as the regular touch path.
 */
object GamepadInput {
    private const val TAG = "GamepadInput"

    /** Log real touch-down positions (as fractions) to help calibrate [Slot]/[Layout]. */
    private const val LOG_TOUCH_POSITIONS = true

    // Same event codes MultiTouch sends to LoaderThread.onMotionEvent.
    private const val TOUCH_DOWN = 4
    private const val TOUCH_UP = 5
    private const val TOUCH_MOVE = 6

    // Marmalade tracks at most 10 touches, indexed by id. Real fingers use the
    // low ids, so synthetic touches are taken from the top of the range.
    private const val FIRST_SYNTHETIC_ID = 4
    private const val LAST_SYNTHETIC_ID = 9

    private const val STICK_DEADZONE = 0.20f
    private const val TRIGGER_PRESS = 0.60f
    private const val TRIGGER_RELEASE = 0.30f
    private const val TICK_MS = 16L

    /** Look speed at full deflection, in "screen heights per second". */
    private const val LOOK_SPEED = 1.1f
    private const val INVERT_LOOK_Y = false

    /** On-screen controls a gamepad input can press. Positions are fractions of the view. */
    // Positions measured from a gameplay screenshot (1600x720, landscape).
    // The game has no on-screen aim button, so there is no AIM slot.
    private enum class Slot(val fx: Float, val fy: Float) {
        FIRE(0.926f, 0.646f),          // crosshair circle, bottom right
        RELOAD(0.859f, 0.139f),        // shells/ammo icon, top right
        KNIFE(0.461f, 0.954f),         // knife icon, bottom centre
        GRENADE(0.922f, 0.414f),       // grenade icon, right side
        SWITCH_WEAPON(0.891f, 0.042f), // weapon icon, top right
        ACTION(0.60f, 0.85f),          // buy/open prompt: position not confirmed yet
        PAUSE(0.016f, 0.049f),         // pause circle, top left
    }

    private object Layout {
        // Left (move) joystick: touch is placed at the centre, then offset by the stick.
        const val MOVE_CX = 0.15f
        const val MOVE_CY = 0.72f
        /** Max drag distance, as a fraction of min(width, height). */
        const val MOVE_RADIUS = 0.18f

        // Look drag: starts at the anchor and wanders inside the region.
        const val LOOK_AX = 0.62f
        const val LOOK_AY = 0.50f
        const val LOOK_MIN_X = 0.40f
        const val LOOK_MAX_X = 0.80f
        const val LOOK_MIN_Y = 0.15f
        const val LOOK_MAX_Y = 0.85f
    }

    private val keyToSlot: Map<Int, Slot> = mapOf(
        KeyEvent.KEYCODE_BUTTON_R2 to Slot.FIRE,
        KeyEvent.KEYCODE_BUTTON_L2 to Slot.FIRE,
        KeyEvent.KEYCODE_BUTTON_R1 to Slot.GRENADE,
        KeyEvent.KEYCODE_BUTTON_L1 to Slot.SWITCH_WEAPON,
        KeyEvent.KEYCODE_BUTTON_A to Slot.ACTION,
        KeyEvent.KEYCODE_BUTTON_X to Slot.RELOAD,
        KeyEvent.KEYCODE_BUTTON_B to Slot.KNIFE,
        KeyEvent.KEYCODE_BUTTON_Y to Slot.SWITCH_WEAPON,
        KeyEvent.KEYCODE_BUTTON_THUMBR to Slot.KNIFE,
        KeyEvent.KEYCODE_BUTTON_START to Slot.PAUSE,
    )

    private val handler = Handler(Looper.getMainLooper())
    private var activityRef: WeakReference<LoaderActivity>? = null
    private var listenerRegistered = false

    private val usedIds = BooleanArray(LAST_SYNTHETIC_ID + 1)
    // Who is currently holding each slot (several sources can map to one slot,
    // e.g. L2 arrives as both a key and an axis on some pads).
    private val holders = HashMap<Slot, MutableSet<String>>()
    private val slotTouchId = HashMap<Slot, Int>()

    // Move stick state
    private var moveId = -1
    private var moveX = 0
    private var moveY = 0

    // Look stick state
    private var lookId = -1
    private var lookStickX = 0f
    private var lookStickY = 0f
    private var lookPosX = 0f
    private var lookPosY = 0f
    private var lastTick = 0L
    private var ticking = false

    private val tick = object : Runnable {
        override fun run() {
            updateLook()
            if (lookStickX != 0f || lookStickY != 0f) {
                handler.postDelayed(this, TICK_MS)
            } else {
                ticking = false
            }
        }
    }

    private val deviceListener = object : InputManager.InputDeviceListener {
        override fun onInputDeviceAdded(deviceId: Int) {}
        override fun onInputDeviceChanged(deviceId: Int) {}
        override fun onInputDeviceRemoved(deviceId: Int) {
            // A pad that vanishes mid-press would leave touches stuck down.
            releaseAll()
        }
    }

    // ------------------------------------------------------------------ entry points

    /** Call from the activity's dispatchKeyEvent. Returns true if the event was consumed. */
    @JvmStatic
    fun onKeyEvent(activity: LoaderActivity, event: KeyEvent): Boolean {
        if (!isGamepadSource(event.source)) return false
        val slot = keyToSlot[event.keyCode] ?: return false
        attach(activity)
        val tag = "k${event.keyCode}"
        when (event.action) {
            KeyEvent.ACTION_DOWN -> if (event.repeatCount == 0) press(slot, tag)
            KeyEvent.ACTION_UP -> release(slot, tag)
        }
        return true
    }

    /** Call from the activity's dispatchGenericMotionEvent. Returns true if consumed. */
    @JvmStatic
    fun onGenericMotionEvent(activity: LoaderActivity, event: MotionEvent): Boolean {
        if (event.source and InputDevice.SOURCE_JOYSTICK != InputDevice.SOURCE_JOYSTICK ||
            event.action != MotionEvent.ACTION_MOVE
        ) return false
        attach(activity)

        // Left stick -> move
        val (mx, my) = applyDeadzone(event.getAxisValue(MotionEvent.AXIS_X), event.getAxisValue(MotionEvent.AXIS_Y))
        updateMove(mx, my)

        // Right stick -> look
        val (rx, ry) = applyDeadzone(event.getAxisValue(MotionEvent.AXIS_Z), event.getAxisValue(MotionEvent.AXIS_RZ))
        setLookStick(rx, ry)

        // Analog triggers (pads report them as LTRIGGER/RTRIGGER or BRAKE/GAS)
        val left = max(event.getAxisValue(MotionEvent.AXIS_LTRIGGER), event.getAxisValue(MotionEvent.AXIS_BRAKE))
        val right = max(event.getAxisValue(MotionEvent.AXIS_RTRIGGER), event.getAxisValue(MotionEvent.AXIS_GAS))
        updateAxisButton(Slot.FIRE, "aL", left)
        updateAxisButton(Slot.FIRE, "aR", right)

        // D-pad up (hat) -> switch weapon
        updateAxisButton(Slot.SWITCH_WEAPON, "hat", -event.getAxisValue(MotionEvent.AXIS_HAT_Y))
        return true
    }

    /** Call from dispatchTouchEvent to log real finger positions for calibration. */
    @JvmStatic
    fun debugLogTouch(activity: LoaderActivity, event: MotionEvent) {
        if (!LOG_TOUCH_POSITIONS) return
        val a = event.actionMasked
        if (a != MotionEvent.ACTION_DOWN && a != MotionEvent.ACTION_POINTER_DOWN) return
        val (w, h) = viewSize(activity)
        val i = event.actionIndex
        Log.d(TAG, "touch fx=%.3f fy=%.3f (px %d,%d of %dx%d)".format(
            event.getX(i) / w, event.getY(i) / h, event.getX(i).toInt(), event.getY(i).toInt(), w.toInt(), h.toInt()))
    }

    /** Lift every synthetic touch (pause, focus loss, pad unplugged). */
    @JvmStatic
    fun releaseAll() {
        handler.removeCallbacks(tick)
        ticking = false
        lookStickX = 0f
        lookStickY = 0f
        if (lookId >= 0) { send(lookId, TOUCH_UP, lookPosX.toInt(), lookPosY.toInt()); freeId(lookId); lookId = -1 }
        if (moveId >= 0) { send(moveId, TOUCH_UP, moveX, moveY); freeId(moveId); moveId = -1 }
        for ((slot, id) in slotTouchId) {
            val (x, y) = slotPos(slot)
            send(id, TOUCH_UP, x, y)
            freeId(id)
        }
        slotTouchId.clear()
        holders.clear()
    }

    // ------------------------------------------------------------------ buttons

    private fun press(slot: Slot, tag: String) {
        val set = holders.getOrPut(slot) { HashSet() }
        val wasEmpty = set.isEmpty()
        set.add(tag)
        if (!wasEmpty) return
        val id = allocId()
        if (id < 0) { set.remove(tag); return }
        slotTouchId[slot] = id
        val (x, y) = slotPos(slot)
        send(id, TOUCH_DOWN, x, y)
    }

    private fun release(slot: Slot, tag: String) {
        val set = holders[slot] ?: return
        if (!set.remove(tag) || set.isNotEmpty()) return
        val id = slotTouchId.remove(slot) ?: return
        val (x, y) = slotPos(slot)
        send(id, TOUCH_UP, x, y)
        freeId(id)
    }

    private fun updateAxisButton(slot: Slot, tag: String, value: Float) {
        val held = holders[slot]?.contains(tag) == true
        if (!held && value > TRIGGER_PRESS) press(slot, tag)
        else if (held && value < TRIGGER_RELEASE) release(slot, tag)
    }

    private fun slotPos(slot: Slot): Pair<Int, Int> {
        val (w, h) = currentSize()
        return Pair((slot.fx * w).toInt(), (slot.fy * h).toInt())
    }

    // ------------------------------------------------------------------ move stick

    private fun updateMove(sx: Float, sy: Float) {
        val (w, h) = currentSize()
        val cx = (Layout.MOVE_CX * w).toInt()
        val cy = (Layout.MOVE_CY * h).toInt()
        if (sx == 0f && sy == 0f) {
            if (moveId >= 0) { send(moveId, TOUCH_UP, moveX, moveY); freeId(moveId); moveId = -1 }
            return
        }
        val radius = Layout.MOVE_RADIUS * min(w, h)
        val x = (cx + sx * radius).toInt()
        val y = (cy + sy * radius).toInt()
        if (moveId < 0) {
            moveId = allocId()
            if (moveId < 0) return
            send(moveId, TOUCH_DOWN, cx, cy)
        }
        if (x != moveX || y != moveY) {
            moveX = x
            moveY = y
            send(moveId, TOUCH_MOVE, x, y)
        }
    }

    // ------------------------------------------------------------------ look stick

    private fun setLookStick(sx: Float, sy: Float) {
        lookStickX = sx
        lookStickY = if (INVERT_LOOK_Y) -sy else sy
        if (sx == 0f && sy == 0f) {
            if (lookId >= 0) { send(lookId, TOUCH_UP, lookPosX.toInt(), lookPosY.toInt()); freeId(lookId); lookId = -1 }
            return
        }
        if (!ticking) {
            ticking = true
            lastTick = SystemClock.uptimeMillis()
            handler.postDelayed(tick, TICK_MS)
        }
    }

    private fun updateLook() {
        val (w, h) = currentSize()
        val now = SystemClock.uptimeMillis()
        val dt = (now - lastTick).coerceIn(1L, 50L) / 1000f
        lastTick = now

        val ax = Layout.LOOK_AX * w
        val ay = Layout.LOOK_AY * h
        if (lookId < 0) {
            lookId = allocId()
            if (lookId < 0) return
            lookPosX = ax
            lookPosY = ay
            send(lookId, TOUCH_DOWN, ax.toInt(), ay.toInt())
        }

        val speed = LOOK_SPEED * h
        lookPosX += lookStickX * speed * dt
        lookPosY += lookStickY * speed * dt

        val outside = lookPosX < Layout.LOOK_MIN_X * w || lookPosX > Layout.LOOK_MAX_X * w ||
            lookPosY < Layout.LOOK_MIN_Y * h || lookPosY > Layout.LOOK_MAX_Y * h
        if (outside) {
            // Lift and put the finger back at the anchor so the camera keeps turning.
            send(lookId, TOUCH_UP, lookPosX.toInt(), lookPosY.toInt())
            lookPosX = ax
            lookPosY = ay
            send(lookId, TOUCH_DOWN, ax.toInt(), ay.toInt())
        } else {
            send(lookId, TOUCH_MOVE, lookPosX.toInt(), lookPosY.toInt())
        }
    }

    // ------------------------------------------------------------------ helpers

    private fun applyDeadzone(x: Float, y: Float): Pair<Float, Float> {
        val mag = hypot(x, y)
        if (mag < STICK_DEADZONE) return Pair(0f, 0f)
        val scaled = min(1f, (mag - STICK_DEADZONE) / (1f - STICK_DEADZONE))
        return Pair(x / mag * scaled, y / mag * scaled)
    }

    private fun isGamepadSource(source: Int): Boolean =
        source and InputDevice.SOURCE_GAMEPAD == InputDevice.SOURCE_GAMEPAD ||
            source and InputDevice.SOURCE_JOYSTICK == InputDevice.SOURCE_JOYSTICK

    private fun allocId(): Int {
        for (i in LAST_SYNTHETIC_ID downTo FIRST_SYNTHETIC_ID) {
            if (!usedIds[i]) { usedIds[i] = true; return i }
        }
        return -1
    }

    private fun freeId(id: Int) {
        if (id in FIRST_SYNTHETIC_ID..LAST_SYNTHETIC_ID) usedIds[id] = false
    }

    private fun attach(activity: LoaderActivity) {
        if (activityRef?.get() !== activity) activityRef = WeakReference(activity)
        if (!listenerRegistered) {
            val im = activity.getSystemService(android.content.Context.INPUT_SERVICE) as? InputManager
            im?.registerInputDeviceListener(deviceListener, handler)
            listenerRegistered = true
        }
    }

    private fun currentSize(): Pair<Float, Float> {
        val act = activityRef?.get() ?: return Pair(1f, 1f)
        return viewSize(act)
    }

    private fun viewSize(activity: LoaderActivity): Pair<Float, Float> {
        val v = activity.m_View
        if (v != null && v.width > 0 && v.height > 0) return Pair(v.width.toFloat(), v.height.toFloat())
        val dm = activity.resources.displayMetrics
        return Pair(dm.widthPixels.toFloat(), dm.heightPixels.toFloat())
    }

    private fun send(id: Int, type: Int, x: Int, y: Int) {
        val act = activityRef?.get() ?: return
        try {
            act.LoaderThread().onMotionEvent(id, type, x, y)
        } catch (e: NullPointerException) {
            // Native loader not started yet; nothing to send the touch to.
            Log.w(TAG, "loader thread not ready, dropping touch $type")
        }
    }
}
