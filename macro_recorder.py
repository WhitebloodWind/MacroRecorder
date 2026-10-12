"""
Macro Recorder - records and replays raw keyboard and mouse input.

Records:  key presses/releases (so any key combination works), mouse button
          presses/releases (left/right/middle/x1/x2), scrolling (vertical and
          horizontal), mouse movement and dragging.

Privacy:  only raw input events are captured - key codes, mouse buttons,
          screen coordinates, scroll amounts and timing. Nothing about the
          applications you use (window titles, process names, screen content,
          clipboard, text fields) is read or stored.

Hotkeys (global, never recorded):
    F9   start / stop recording
    F10  play / stop playback
    Esc  stop playback

Requires:  pip install pynput pillow
"""

import bisect
import ctypes
import json
import math
import queue
import struct
import sys
import threading
import time
import tkinter as tk
from tkinter import filedialog, messagebox, ttk

try:
    from pynput import keyboard, mouse
    from PIL import Image, ImageDraw, ImageTk
except ImportError:
    print("Missing dependencies. Install them with:  pip install pynput pillow")
    sys.exit(1)

IS_WIN = sys.platform == "win32"

if IS_WIN:
    # Physical-pixel coordinates on high-DPI displays.
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
    except Exception:
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            pass
    # Own taskbar identity, so Windows shows our icon instead of Python's.
    try:
        ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("MacroRecorder.App")
    except Exception:
        pass

APP_NAME = "Macro Recorder"

HOTKEY_RECORD = keyboard.Key.f9
HOTKEY_PLAY = keyboard.Key.f10
HOTKEY_ABORT = keyboard.Key.esc
CONTROL_KEYS = {HOTKEY_RECORD, HOTKEY_PLAY}

MOVE_INTERVAL = 0.01  # min seconds between recorded mouse-move samples

WM_MOUSEWHEEL, WM_MOUSEHWHEEL, WHEEL_DELTA = 0x020A, 0x020E, 120
SCROLL_SETTLE = 0.35  # s apps get to finish a smooth scroll before the next key/click

BUTTONS = {b.name: b for b in mouse.Button}

IDLE, RECORDING, PLAYING = "idle", "recording", "playing"

# ---------------------------------------------------------------- theme
C = {
    "bg": "#121419",
    "panel": "#1b1e25",
    "panel2": "#242832",
    "border": "#2e3340",
    "text": "#e7e9ef",
    "muted": "#8a92a6",
    "faint": "#5d6577",
    "accent": "#4c8dff",
    "rec": "#ff4757",
    "rec_hover": "#ff6b78",
    "play": "#2ecc71",
    "play_hover": "#4cdb87",
    "key": "#6ea8ff",
    "click": "#f5b041",
    "scroll": "#b38cff",
    "move": "#6b7385",
}
STATE_COLOR = {IDLE: C["muted"], RECORDING: C["rec"], PLAYING: C["play"]}
FONT = "Segoe UI"
MONO = "Consolas"


# ---------------------------------------------------------------- key codec
def key_to_dict(key):
    """Serialize a pynput key using only its identity (no app context)."""
    if isinstance(key, keyboard.Key):
        return {"special": key.name}
    vk = getattr(key, "vk", None)
    char = getattr(key, "char", None)
    # Control characters (e.g. Ctrl+C -> '\x03') are not useful; keep vk.
    if char is not None and not char.isprintable():
        char = None
    return {"vk": vk, "char": char}


def dict_to_key(d):
    if "special" in d:
        return keyboard.Key[d["special"]]
    if d.get("vk") is not None:
        return keyboard.KeyCode.from_vk(d["vk"])
    return keyboard.KeyCode.from_char(d["char"])


def key_label(d):
    if "special" in d:
        return d["special"].replace("_", " ").title()
    vk = d.get("vk")
    if vk is not None and (0x30 <= vk <= 0x39 or 0x41 <= vk <= 0x5A):
        return chr(vk)
    if d.get("char"):
        return d["char"]
    return f"VK {vk}"


def key_id(d):
    return json.dumps(d, sort_keys=True)


def tidy(events, gui_rect=None):
    """Remove artefacts at the edges of a recording.

    - trailing clicks/moves inside this app's own window (the Stop click)
    - releases at the start whose press happened before recording began
    """
    out = list(events)
    if gui_rect:
        x0, y0, x1, y1 = gui_rect
        while out and out[-1]["type"] in ("move", "mouse_down", "mouse_up") \
                and x0 <= out[-1]["x"] <= x1 and y0 <= out[-1]["y"] <= y1:
            out.pop()
    down, kept = set(), []
    for e in out:
        t = e["type"]
        ident = ("k", key_id(e["key"])) if t.startswith("key") else \
                ("m", e.get("button"))
        if t in ("key_down", "mouse_down"):
            down.add(ident)
        elif t in ("key_up", "mouse_up"):
            if ident not in down:
                continue
            down.discard(ident)
        kept.append(e)
    return kept


# ---------------------------------------------------------------- recorder
class Recorder:
    def __init__(self):
        self.events = []
        self.record_moves = True
        self.recording = False
        self.started = 0.0
        self._last_move = 0.0
        self._last_wheel = 0.0
        self._buttons_down = set()
        self._lock = threading.Lock()

    def start(self, record_moves):
        with self._lock:
            self.events = []
            self.record_moves = record_moves
            self._buttons_down.clear()
            self.started = time.perf_counter()
            self._last_move = 0.0
            self.recording = True

    def stop(self):
        with self._lock:
            self.recording = False
            # Touchpad scrolls are added when the gesture ends, so re-order.
            evs = sorted(self.events, key=lambda e: e["t"])
        # A key press or click stops a touchpad glide, so it never scrolls
        # past input that came after it.
        inputs = [e["t"] for e in evs if e["type"] in ("key_down", "mouse_down")]
        out = []
        for e in evs:
            lift = e.pop("_lift", None)
            if lift is not None:
                i = bisect.bisect_right(inputs, lift)
                if i < len(inputs) and inputs[i] <= e["t"]:
                    continue
            out.append(e)
        return out

    def _add(self, ev):
        with self._lock:
            if not self.recording:
                return
            ev["t"] = round(time.perf_counter() - self.started, 4)
            self.events.append(ev)

    def on_key(self, key, pressed):
        if key in CONTROL_KEYS:
            return
        self._add({"type": "key_down" if pressed else "key_up",
                   "key": key_to_dict(key)})

    def on_move(self, x, y):
        if not self.recording:
            return
        if not (self.record_moves or self._buttons_down):  # always keep drags
            return
        now = time.perf_counter()
        if now - self._last_move < MOVE_INTERVAL:
            return
        self._last_move = now
        self._add({"type": "move", "x": x, "y": y})

    def on_click(self, x, y, button, pressed):
        if pressed:
            self._buttons_down.add(button)
        else:
            self._buttons_down.discard(button)
        self._add({"type": "mouse_down" if pressed else "mouse_up",
                   "button": button.name, "x": x, "y": y})

    def on_scroll(self, x, y, dx, dy):
        self._last_wheel = time.perf_counter()
        self._add({"type": "scroll", "x": x, "y": y, "dx": dx, "dy": dy})

    def add_touch_scroll(self, gesture_start, lift, steps, x, y):
        """Add a finished two-finger touchpad scroll.

        steps: [(perf_counter time, dx, dy, glide), ...]. Skipped when Windows
        already delivered the same gesture as ordinary wheel events.
        """
        with self._lock:
            if not self.recording or self._last_wheel >= gesture_start - 0.1:
                return
            for t, dx, dy, glide in steps:
                rel = t - self.started
                if rel >= 0:
                    ev = {"type": "scroll", "x": x, "y": y, "src": "touchpad",
                          "dx": round(dx, 6), "dy": round(dy, 6), "t": round(rel, 4)}
                    if glide:
                        ev["_lift"] = lift - self.started
                    self.events.append(ev)


# ---------------------------------------------------------------- player
class Player:
    def __init__(self):
        self.kb = keyboard.Controller()
        self.ms = mouse.Controller()
        self._stop = threading.Event()
        self.playing = False
        self.loop = 0
        self.index = 0
        self.total = 0
        self.repeat = 1
        self.touch_scale = 1.0
        self._carry = [0.0, 0.0]

    def stop(self):
        self._stop.set()

    def _wait_until(self, target):
        """Sleep until perf_counter() reaches target; False if stopped."""
        while True:
            if self._stop.is_set():
                return False
            remaining = target - time.perf_counter()
            if remaining <= 0:
                return True
            time.sleep(min(remaining, 0.005))

    def play(self, events, repeat=1, speed=1.0, on_done=None,
             touch_scale=1.0, scroll_settle=0.0):
        """scroll_settle: seconds to let apps finish animating a scroll before
        the next key press or click (later events shift by the same amount)."""
        self._stop.clear()
        self.playing = True
        self.total, self.repeat, self.loop, self.index = len(events), repeat, 0, 0
        self.touch_scale = touch_scale
        self._carry = [0.0, 0.0]

        def run():
            held_keys, held_buttons = {}, set()
            try:
                while repeat == 0 or self.loop < repeat:
                    self.loop += 1
                    start = time.perf_counter()
                    shift, last_scroll = 0.0, None
                    for i, ev in enumerate(events):
                        if not self._wait_until(start + ev["t"] / speed + shift):
                            return
                        if scroll_settle and last_scroll is not None \
                                and ev["type"] in ("key_down", "mouse_down"):
                            ready = last_scroll + scroll_settle
                            delay = ready - time.perf_counter()
                            if delay > 0:
                                if not self._wait_until(ready):
                                    return
                                shift += delay
                            last_scroll = None
                        self._do(ev, held_keys, held_buttons)
                        if ev["type"] == "scroll":
                            last_scroll = time.perf_counter()
                        self.index = i + 1
                    if self._stop.wait(0.05):
                        return
            finally:
                # Never leave keys or buttons stuck down.
                for k in held_keys.values():
                    try:
                        self.kb.release(k)
                    except Exception:
                        pass
                for b in held_buttons:
                    try:
                        self.ms.release(b)
                    except Exception:
                        pass
                self.playing = False
                if on_done:
                    on_done()

        threading.Thread(target=run, daemon=True).start()

    def _do(self, ev, held_keys, held_buttons):
        t = ev["type"]
        if t == "key_down":
            k = dict_to_key(ev["key"])
            self.kb.press(k)
            held_keys[key_id(ev["key"])] = k
        elif t == "key_up":
            k = dict_to_key(ev["key"])
            self.kb.release(k)
            held_keys.pop(key_id(ev["key"]), None)
        elif t == "move":
            self.ms.position = (ev["x"], ev["y"])
        elif t in ("mouse_down", "mouse_up"):
            b = BUTTONS.get(ev["button"], mouse.Button.left)
            self.ms.position = (ev["x"], ev["y"])
            if t == "mouse_down":
                self.ms.press(b)
                held_buttons.add(b)
            else:
                self.ms.release(b)
                held_buttons.discard(b)
        elif t == "scroll":
            self.ms.position = (ev["x"], ev["y"])
            k = self.touch_scale if ev.get("src") == "touchpad" else 1.0
            self._scroll(ev["dx"] * k, ev["dy"] * k)

    def _scroll(self, dx, dy):
        """Scroll in exact wheel units, carrying fractions to the next step.

        pynput truncates dy * 120 to an int, so 1/12 notch (9.99996) would
        become 9; send whole units with a half-unit margin instead.
        """
        units = []
        for axis, d in ((0, dx), (1, dy)):
            u = d * WHEEL_DELTA + self._carry[axis]
            n = round(u)
            self._carry[axis] = u - n
            units.append((n + (0.5 if n > 0 else -0.5)) / WHEEL_DELTA if n else 0)
        if units[0] or units[1]:
            self.ms.scroll(*units)


# ---------------------------------------------------------------- touchpad
class TouchScrollGesture:
    """Turns two-finger touchpad movement into wheel-style scroll steps.

    Precision touchpads scroll without going through the system mouse hook,
    so the recorder never sees those scrolls. This rebuilds them from finger
    positions (in mm), including the glide after the fingers lift.
    """
    NOTCH_MM = 12.0     # finger travel for one wheel notch
    DEADZONE_MM = 1.5   # movement before a scroll starts (ignores 2-finger taps)
    STEP = 1 / 12       # emit a scroll step every 1/12 notch
    FRICTION = 0.20     # glide decay time constant (s)
    GLIDE_MIN = 4.0     # release speed (notches/s) needed to glide

    def __init__(self, on_commit, natural=True):
        self.on_commit = on_commit  # (gesture_start, lift_time, [(t, dx, dy, glide), ...])
        self.natural = natural      # "down motion scrolls up"
        self.reverse = False
        self._lock = threading.Lock()
        self._reset()

    def _reset(self):
        self.ids = None
        self.scrolling = self.pinch = False
        self.start = self.prev = None
        self.t0 = 0.0
        self.spread0 = 0.0
        self.axis = None
        self.acc = 0.0
        self.hist = []
        self.steps = []

    def _sign(self):
        return (1 if self.natural else -1) * (-1 if self.reverse else 1)

    def _emit(self, t, amount, glide=False):
        dx, dy = (-amount, 0.0) if self.axis == "x" else (0.0, amount)
        self.steps.append((t, dx * self._sign(), dy * self._sign(), glide))

    def update(self, contacts, t):
        """contacts: {contact_id: (x_mm, y_mm)} for fingers on the pad."""
        with self._lock:
            if len(contacts) != 2:
                self._finish(t)
                return
            ids = tuple(sorted(contacts))
            (x1, y1), (x2, y2) = contacts[ids[0]], contacts[ids[1]]
            c = ((x1 + x2) / 2, (y1 + y2) / 2)
            spread = math.hypot(x2 - x1, y2 - y1)
            if ids != self.ids:
                self._finish(t)
                self.ids, self.start, self.prev, self.t0, self.spread0 = ids, c, c, t, spread
                return
            if self.pinch:
                return
            if not self.scrolling:
                mx, my = c[0] - self.start[0], c[1] - self.start[1]
                move = math.hypot(mx, my)
                if move < self.DEADZONE_MM:
                    return
                if abs(spread - self.spread0) > move:  # fingers spreading: zoom
                    self.pinch = True
                    return
                self.scrolling = True
                self.axis = "y" if abs(my) >= abs(mx) else "x"
                self.prev = c
                return
            i = 1 if self.axis == "y" else 0
            amount = (c[i] - self.prev[i]) / self.NOTCH_MM
            self.prev = c
            self.hist.append((t, amount))
            self.hist = self.hist[-20:]
            self.acc += amount
            if abs(self.acc) >= self.STEP:
                self._emit(t, self.acc)
                self.acc = 0.0

    def flush(self):
        with self._lock:
            self._finish(time.perf_counter())

    def _finish(self, t):
        if self.scrolling:
            if self.acc:
                self._emit(t, self.acc)
            # Glide: continue with the release velocity, decaying.
            recent = [(ht, a) for ht, a in self.hist if t - ht <= 0.08]
            if recent:
                v = sum(a for _, a in recent) / max(0.016, t - recent[0][0])  # notches/s
                tt, acc, dt = t, 0.0, 0.016
                if abs(v) < self.GLIDE_MIN:  # slow release: no glide
                    v = 0.0
                while abs(v) > 0.5 and tt - t < 1.5:
                    v *= math.exp(-dt / self.FRICTION)
                    tt += dt
                    acc += v * dt
                    if abs(acc) >= self.STEP:
                        self._emit(tt, acc, glide=True)
                        acc = 0.0
            if self.steps:
                self.on_commit(self.t0, t, self.steps)
        self._reset()


if IS_WIN:
    from ctypes import wintypes as wt

    _u32 = ctypes.WinDLL("user32", use_last_error=True)
    _k32 = ctypes.WinDLL("kernel32")
    _hid = ctypes.WinDLL("hid")
    LRESULT = ctypes.c_ssize_t
    WNDPROC = ctypes.WINFUNCTYPE(LRESULT, wt.HWND, wt.UINT, wt.WPARAM, wt.LPARAM)

    class WNDCLASSW(ctypes.Structure):
        _fields_ = [("style", wt.UINT), ("lpfnWndProc", WNDPROC),
                    ("cbClsExtra", ctypes.c_int), ("cbWndExtra", ctypes.c_int),
                    ("hInstance", wt.HINSTANCE), ("hIcon", wt.HICON),
                    ("hCursor", wt.HANDLE), ("hbrBackground", wt.HBRUSH),
                    ("lpszMenuName", wt.LPCWSTR), ("lpszClassName", wt.LPCWSTR)]

    class RAWINPUTDEVICE(ctypes.Structure):
        _fields_ = [("usUsagePage", wt.USHORT), ("usUsage", wt.USHORT),
                    ("dwFlags", wt.DWORD), ("hwndTarget", wt.HWND)]

    class RAWINPUTHEADER(ctypes.Structure):
        _fields_ = [("dwType", wt.DWORD), ("dwSize", wt.DWORD),
                    ("hDevice", wt.HANDLE), ("wParam", wt.WPARAM)]

    class HIDP_CAPS(ctypes.Structure):
        _fields_ = [("Usage", wt.USHORT), ("UsagePage", wt.USHORT),
                    ("InputReportByteLength", wt.USHORT), ("OutputReportByteLength", wt.USHORT),
                    ("FeatureReportByteLength", wt.USHORT), ("Reserved", wt.USHORT * 17),
                    ("NumberLinkCollectionNodes", wt.USHORT), ("NumberInputButtonCaps", wt.USHORT),
                    ("NumberInputValueCaps", wt.USHORT), ("NumberInputDataIndices", wt.USHORT),
                    ("NumberOutputButtonCaps", wt.USHORT), ("NumberOutputValueCaps", wt.USHORT),
                    ("NumberOutputDataIndices", wt.USHORT), ("NumberFeatureButtonCaps", wt.USHORT),
                    ("NumberFeatureValueCaps", wt.USHORT), ("NumberFeatureDataIndices", wt.USHORT)]

    class HIDP_VALUE_CAPS(ctypes.Structure):
        _fields_ = [("UsagePage", wt.USHORT), ("ReportID", ctypes.c_ubyte),
                    ("IsAlias", ctypes.c_ubyte), ("BitField", wt.USHORT),
                    ("LinkCollection", wt.USHORT), ("LinkUsage", wt.USHORT),
                    ("LinkUsagePage", wt.USHORT), ("IsRange", ctypes.c_ubyte),
                    ("IsStringRange", ctypes.c_ubyte), ("IsDesignatorRange", ctypes.c_ubyte),
                    ("IsAbsolute", ctypes.c_ubyte), ("HasNull", ctypes.c_ubyte),
                    ("Reserved", ctypes.c_ubyte), ("BitSize", wt.USHORT),
                    ("ReportCount", wt.USHORT), ("Reserved2", wt.USHORT * 5),
                    ("UnitsExp", wt.ULONG), ("Units", wt.ULONG),
                    ("LogicalMin", wt.LONG), ("LogicalMax", wt.LONG),
                    ("PhysicalMin", wt.LONG), ("PhysicalMax", wt.LONG),
                    ("Usage", wt.USHORT), ("UsageMax", wt.USHORT), ("_union", wt.USHORT * 6)]

    _u32.RegisterClassW.argtypes = [ctypes.POINTER(WNDCLASSW)]
    _u32.RegisterClassW.restype = wt.ATOM
    _u32.CreateWindowExW.argtypes = [wt.DWORD, wt.LPCWSTR, wt.LPCWSTR, wt.DWORD,
                                     ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int,
                                     wt.HWND, wt.HMENU, wt.HINSTANCE, wt.LPVOID]
    _u32.CreateWindowExW.restype = wt.HWND
    _u32.DefWindowProcW.argtypes = [wt.HWND, wt.UINT, wt.WPARAM, wt.LPARAM]
    _u32.DefWindowProcW.restype = LRESULT
    _u32.RegisterRawInputDevices.argtypes = [ctypes.POINTER(RAWINPUTDEVICE), wt.UINT, wt.UINT]
    _u32.RegisterRawInputDevices.restype = wt.BOOL
    _u32.GetRawInputData.argtypes = [wt.HANDLE, wt.UINT, wt.LPVOID, ctypes.POINTER(wt.UINT), wt.UINT]
    _u32.GetRawInputData.restype = wt.UINT
    _u32.GetRawInputDeviceInfoW.argtypes = [wt.HANDLE, wt.UINT, wt.LPVOID, ctypes.POINTER(wt.UINT)]
    _u32.GetRawInputDeviceInfoW.restype = wt.UINT
    _u32.GetMessageW.argtypes = [ctypes.POINTER(wt.MSG), wt.HWND, wt.UINT, wt.UINT]
    _u32.GetMessageW.restype = wt.BOOL
    _u32.TranslateMessage.argtypes = [ctypes.POINTER(wt.MSG)]
    _u32.DispatchMessageW.argtypes = [ctypes.POINTER(wt.MSG)]
    _u32.PostMessageW.argtypes = [wt.HWND, wt.UINT, wt.WPARAM, wt.LPARAM]
    _u32.DestroyWindow.argtypes = [wt.HWND]
    _u32.PostQuitMessage.argtypes = [ctypes.c_int]
    _u32.GetCursorPos.argtypes = [ctypes.POINTER(wt.POINT)]
    _k32.GetModuleHandleW.argtypes = [wt.LPCWSTR]
    _k32.GetModuleHandleW.restype = wt.HMODULE
    _hid.HidP_GetCaps.argtypes = [ctypes.c_void_p, ctypes.POINTER(HIDP_CAPS)]
    _hid.HidP_GetCaps.restype = ctypes.c_long
    _hid.HidP_GetValueCaps.argtypes = [ctypes.c_int, ctypes.POINTER(HIDP_VALUE_CAPS),
                                       ctypes.POINTER(wt.USHORT), ctypes.c_void_p]
    _hid.HidP_GetValueCaps.restype = ctypes.c_long
    _hid.HidP_GetUsageValue.argtypes = [ctypes.c_int, wt.USHORT, wt.USHORT, wt.USHORT,
                                        ctypes.POINTER(wt.ULONG), ctypes.c_void_p,
                                        ctypes.c_char_p, wt.ULONG]
    _hid.HidP_GetUsageValue.restype = ctypes.c_long
    _hid.HidP_GetUsages.argtypes = [ctypes.c_int, wt.USHORT, wt.USHORT, ctypes.POINTER(wt.USHORT),
                                    ctypes.POINTER(wt.ULONG), ctypes.c_void_p,
                                    ctypes.c_char_p, wt.ULONG]
    _hid.HidP_GetUsages.restype = ctypes.c_long

    HIDP_OK = 0x00110000
    WM_INPUT, WM_CLOSE, WM_DESTROY = 0x00FF, 0x0010, 0x0002
    RID_INPUT, RIDI_PREPARSEDDATA, RIM_TYPEHID = 0x10000003, 0x20000005, 2
    RIDEV_INPUTSINK = 0x00000100
    PAGE_DESKTOP, PAGE_DIGITIZER = 0x01, 0x0D
    U_X, U_Y, U_TIP, U_CONTACT_ID, U_CONTACT_COUNT = 0x30, 0x31, 0x42, 0x51, 0x54

    def _extent_mm(vc):
        """Physical size of a HID axis in mm, or None if not reported."""
        span = vc.PhysicalMax - vc.PhysicalMin
        if span <= 0 or (vc.Units >> 4) & 0xF != 1:
            return None
        unit_mm = {1: 10.0, 3: 25.4}.get(vc.Units & 0xF)  # SI cm / inch
        if unit_mm is None:
            return None
        exp = vc.UnitsExp & 0xF
        exp = exp - 16 if exp > 7 else exp
        mm = span * (10 ** exp) * unit_mm
        return mm if 20 < mm < 400 else None

    class _Touchpad:
        """Decodes Precision Touchpad HID reports into finger positions."""

        def __init__(self, hdev):
            size = wt.UINT(0)
            _u32.GetRawInputDeviceInfoW(hdev, RIDI_PREPARSEDDATA, None, ctypes.byref(size))
            self._pp_buf = ctypes.create_string_buffer(size.value)
            _u32.GetRawInputDeviceInfoW(hdev, RIDI_PREPARSEDDATA, self._pp_buf, ctypes.byref(size))
            self.pp = ctypes.cast(self._pp_buf, ctypes.c_void_p)
            caps = HIDP_CAPS()
            _hid.HidP_GetCaps(self.pp, ctypes.byref(caps))
            n = wt.USHORT(caps.NumberInputValueCaps)
            arr = (HIDP_VALUE_CAPS * max(1, n.value))()
            _hid.HidP_GetValueCaps(0, arr, ctypes.byref(n), self.pp)
            axes, self.count_link = {}, None
            for vc in arr[:n.value]:
                if vc.UsagePage == PAGE_DESKTOP and vc.Usage in (U_X, U_Y):
                    axes.setdefault(vc.LinkCollection, {})[vc.Usage] = vc
                elif vc.UsagePage == PAGE_DIGITIZER and vc.Usage == U_CONTACT_COUNT:
                    self.count_link = vc.LinkCollection
            self.links = sorted(l for l, a in axes.items() if U_X in a and U_Y in a)
            self.valid = bool(self.links)
            if self.valid:
                xc, yc = axes[self.links[0]][U_X], axes[self.links[0]][U_Y]
                self.x0, self.y0 = xc.LogicalMin, yc.LogicalMin
                self.sx = (_extent_mm(xc) or 100.0) / max(1, xc.LogicalMax - xc.LogicalMin)
                self.sy = (_extent_mm(yc) or 65.0) / max(1, yc.LogicalMax - yc.LogicalMin)
            self.remaining = 0
            self.frame = {}

        def _value(self, page, link, usage, report):
            v = wt.ULONG(0)
            st = _hid.HidP_GetUsageValue(0, page, link, usage, ctypes.byref(v),
                                         self.pp, report, len(report))
            return v.value if st == HIDP_OK else None

        def _tip(self, link, report):
            buf = (wt.USHORT * 16)()
            n = wt.ULONG(16)
            st = _hid.HidP_GetUsages(0, PAGE_DIGITIZER, link, buf, ctypes.byref(n),
                                     self.pp, report, len(report))
            return st == HIDP_OK and U_TIP in buf[:n.value]

        def parse(self, report):
            """Feed one HID report; returns {id: (x_mm, y_mm)} when a frame completes."""
            if self.count_link is not None:
                count = self._value(PAGE_DIGITIZER, self.count_link, U_CONTACT_COUNT, report)
                if count is None:
                    return None          # some other report (e.g. buttons)
                if count:
                    self.remaining, self.frame = count, {}
                elif self.remaining <= 0:
                    return None
            else:
                self.remaining, self.frame = len(self.links), {}
            for link in self.links:
                if self.remaining <= 0:
                    break
                x = self._value(PAGE_DESKTOP, link, U_X, report)
                y = self._value(PAGE_DESKTOP, link, U_Y, report)
                if x is None or y is None:
                    break
                self.remaining -= 1
                if self._tip(link, report):
                    cid = self._value(PAGE_DIGITIZER, link, U_CONTACT_ID, report)
                    self.frame[link if cid is None else cid] = (
                        (x - self.x0) * self.sx, (y - self.y0) * self.sy)
            return dict(self.frame) if self.remaining <= 0 else None

    class TouchpadListener(threading.Thread):
        """Reads raw finger positions from Precision Touchpads (Raw Input)."""

        def __init__(self, on_frame):
            super().__init__(daemon=True)
            self.on_frame = on_frame
            self.devices = {}
            self.hwnd = None
            self.registered = False
            self.ready = threading.Event()

        def run(self):
            hinst = _k32.GetModuleHandleW(None)
            self._proc = WNDPROC(self._wndproc)  # keep a reference
            wc = WNDCLASSW(lpfnWndProc=self._proc, hInstance=hinst,
                           lpszClassName="MacroRecorderTouchpad")
            _u32.RegisterClassW(ctypes.byref(wc))
            self.hwnd = _u32.CreateWindowExW(0, wc.lpszClassName, "", 0, 0, 0, 0, 0,
                                             None, None, hinst, None)
            rid = RAWINPUTDEVICE(PAGE_DIGITIZER, 0x05, RIDEV_INPUTSINK, self.hwnd)
            self.registered = bool(self.hwnd) and bool(
                _u32.RegisterRawInputDevices(ctypes.byref(rid), 1, ctypes.sizeof(rid)))
            self.ready.set()
            msg = wt.MSG()
            while _u32.GetMessageW(ctypes.byref(msg), None, 0, 0) > 0:
                _u32.TranslateMessage(ctypes.byref(msg))
                _u32.DispatchMessageW(ctypes.byref(msg))

        def _wndproc(self, hwnd, msg, wp, lp):
            if msg == WM_INPUT:
                try:
                    self._on_input(lp)
                except Exception:
                    pass
            elif msg == WM_CLOSE:
                _u32.DestroyWindow(hwnd)
                return 0
            elif msg == WM_DESTROY:
                _u32.PostQuitMessage(0)
                return 0
            return _u32.DefWindowProcW(hwnd, msg, wp, lp)

        def _on_input(self, lp):
            hdr = ctypes.sizeof(RAWINPUTHEADER)
            size = wt.UINT(0)
            _u32.GetRawInputData(lp, RID_INPUT, None, ctypes.byref(size), hdr)
            buf = ctypes.create_string_buffer(size.value)
            if _u32.GetRawInputData(lp, RID_INPUT, buf, ctypes.byref(size), hdr) != size.value:
                return
            head = RAWINPUTHEADER.from_buffer(buf)
            if head.dwType != RIM_TYPEHID:
                return
            dev = self.devices.get(head.hDevice)
            if dev is None:
                dev = self.devices[head.hDevice] = _Touchpad(head.hDevice)
            if not dev.valid:
                return
            n_size, n_count = struct.unpack_from("II", buf, hdr)
            data = buf.raw[hdr + 8: hdr + 8 + n_size * n_count]
            for i in range(n_count):
                frame = dev.parse(data[i * n_size:(i + 1) * n_size])
                if frame is not None:
                    self.on_frame(frame, time.perf_counter())

        def stop(self):
            if self.hwnd:
                _u32.PostMessageW(self.hwnd, WM_CLOSE, 0, 0)

    def cursor_pos():
        pt = wt.POINT()
        _u32.GetCursorPos(ctypes.byref(pt))
        return pt.x, pt.y

    def touchpad_natural_scroll():
        """Windows setting 'Down motion scrolls up' (the default)."""
        try:
            import winreg
            with winreg.OpenKey(winreg.HKEY_CURRENT_USER,
                                r"Software\Microsoft\Windows\CurrentVersion\PrecisionTouchPad") as k:
                return winreg.QueryValueEx(k, "ScrollDirection")[0] == 0
        except OSError:
            return True


# ---------------------------------------------------------------- graphics
def _hex(c, a=255):
    c = c.lstrip("#")
    return tuple(int(c[i:i + 2], 16) for i in (0, 2, 4)) + (a,)


def draw_state_icon(state, size):
    """App icon: dark rounded tile with a state glyph (OBS-style)."""
    ss = 4
    S = size * ss
    im = Image.new("RGBA", (S, S), (0, 0, 0, 0))
    d = ImageDraw.Draw(im)
    d.rounded_rectangle([0, 0, S - 1, S - 1], radius=int(S * 0.24), fill=_hex(C["panel2"]))
    cx = cy = S / 2
    if state == PLAYING:
        r = S * 0.27
        d.polygon([(cx - r * 0.75, cy - r), (cx - r * 0.75, cy + r), (cx + r, cy)],
                  fill=_hex(C["play"]))
    else:
        ring = S * 0.31
        w = max(ss, int(S * 0.07))
        col = C["rec"] if state == RECORDING else "#c9cedb"
        d.ellipse([cx - ring, cy - ring, cx + ring, cy + ring], outline=_hex(col), width=w)
        dot = S * (0.19 if state == RECORDING else 0.13)
        d.ellipse([cx - dot, cy - dot, cx + dot, cy + dot], fill=_hex(col))
    return im.resize((size, size), Image.LANCZOS)


def draw_pill(w, h, fill, bg):
    ss = 4
    im = Image.new("RGBA", (w * ss, h * ss), _hex(bg))
    ImageDraw.Draw(im).rounded_rectangle([0, 0, w * ss - 1, h * ss - 1],
                                         radius=h * ss // 2, fill=_hex(fill))
    return im.resize((w, h), Image.LANCZOS)


def set_win_exstyle(widget, add):
    if not IS_WIN:
        return
    u = ctypes.windll.user32
    hwnd = u.GetParent(widget.winfo_id())
    style = u.GetWindowLongW(hwnd, -20)
    u.SetWindowLongW(hwnd, -20, style | add)


def dark_titlebar(root):
    if not IS_WIN:
        return
    try:
        hwnd = ctypes.windll.user32.GetParent(root.winfo_id())
        on = ctypes.c_int(1)
        for attr in (20, 19):  # DWMWA_USE_IMMERSIVE_DARK_MODE (new / old builds)
            if ctypes.windll.dwmapi.DwmSetWindowAttribute(
                    hwnd, attr, ctypes.byref(on), ctypes.sizeof(on)) == 0:
                break
    except Exception:
        pass


# ---------------------------------------------------------------- widgets
class FlatButton(tk.Label):
    def __init__(self, master, text, command, bg, hover, fg="#ffffff",
                 size=10, bold=True, padx=16, pady=8):
        super().__init__(master, text=text, bg=bg, fg=fg, cursor="hand2",
                         font=(FONT, size, "bold" if bold else "normal"),
                         padx=padx, pady=pady)
        self._bg, self._hover, self._fg = bg, hover, fg
        self._cmd, self._enabled = command, True
        self.bind("<Enter>", lambda e: self._enabled and self.config(bg=self._hover))
        self.bind("<Leave>", lambda e: self.config(bg=self._bg if self._enabled else C["panel2"]))
        self.bind("<ButtonRelease-1>", self._click)

    def _click(self, e):
        inside = 0 <= e.x <= self.winfo_width() and 0 <= e.y <= self.winfo_height()
        if self._enabled and inside:
            self._cmd()

    def set_enabled(self, on):
        self._enabled = on
        self.config(bg=self._bg if on else C["panel2"],
                    fg=self._fg if on else C["faint"],
                    cursor="hand2" if on else "arrow")

    def set_text(self, text):
        self.config(text=text)


class Indicator(tk.Toplevel):
    """Small always-on-top, click-through status pill (like OBS)."""
    KEY = "#010203"  # transparent colour key

    def __init__(self, master, scale):
        super().__init__(master)
        self.withdraw()
        self.overrideredirect(True)
        self.attributes("-topmost", True)
        self.config(bg=self.KEY)
        if IS_WIN:
            self.attributes("-transparentcolor", self.KEY)
        self.s = scale
        self.w, self.h = int(132 * scale), int(30 * scale)
        self.canvas = tk.Canvas(self, width=self.w, height=self.h, bg=self.KEY,
                                highlightthickness=0, bd=0)
        self.canvas.pack()
        self._pill = ImageTk.PhotoImage(draw_pill(self.w, self.h, "#15171c", self.KEY))
        self.canvas.create_image(0, 0, image=self._pill, anchor="nw")
        r, cy = 5 * scale, self.h / 2
        dx = 16 * scale
        self.dot = self.canvas.create_oval(dx - r, cy - r, dx + r, cy + r, outline="")
        self.label = self.canvas.create_text(dx + 13 * scale, cy, anchor="w",
                                             font=(FONT, 9, "bold"), fill=C["text"])
        self.corner = "Top right"
        self.update_idletasks()
        # WS_EX_LAYERED | WS_EX_TRANSPARENT | WS_EX_TOOLWINDOW | WS_EX_NOACTIVATE
        set_win_exstyle(self, 0x80000 | 0x20 | 0x80 | 0x08000000)

    def place_at(self, corner):
        self.corner = corner
        m = int(18 * self.s)
        sw, sh = self.winfo_screenwidth(), self.winfo_screenheight()
        x = m if "left" in corner else sw - self.w - m
        y = m if "Top" in corner else sh - self.h - m - int(48 * self.s)
        self.geometry(f"{self.w}x{self.h}+{x}+{y}")

    def show(self, visible):
        if visible:
            self.deiconify()
            self.attributes("-topmost", True)
        else:
            self.withdraw()

    def update_state(self, state, text, blink_on):
        col = STATE_COLOR[state]
        if state == RECORDING and not blink_on:
            col = "#5a2028"
        self.canvas.itemconfig(self.dot, fill=col)
        self.canvas.itemconfig(self.label, text=text)


# ---------------------------------------------------------------- GUI
def describe(ev):
    """(category, action, details) for the event list."""
    t = ev["type"]
    if t in ("key_down", "key_up"):
        return "key", "Key down" if t == "key_down" else "Key up", key_label(ev["key"])
    if t == "move":
        return "move", "Move", f"{ev['x']}, {ev['y']}"
    if t in ("mouse_down", "mouse_up"):
        verb = "Press" if t == "mouse_down" else "Release"
        return "click", f"Mouse {verb.lower()}", f"{ev['button'].title()}  @  {ev['x']}, {ev['y']}"
    if t == "scroll":
        parts = []
        if ev["dy"]:
            parts.append(("Up" if ev["dy"] > 0 else "Down") + f" {abs(ev['dy']):.4g}")
        if ev["dx"]:
            parts.append(("Right" if ev["dx"] > 0 else "Left") + f" {abs(ev['dx']):.4g}")
        return "scroll", "Scroll", f"{' '.join(parts)}  @  {ev['x']}, {ev['y']}"
    return "move", t, ""


def fmt_time(sec):
    m, s = divmod(int(sec), 60)
    h, m = divmod(m, 60)
    return f"{h:02d}:{m:02d}:{s:02d}"


class App:
    def __init__(self, root):
        self.root = root
        self.recorder = Recorder()
        self.player = Player()
        self.events = []
        self.state = IDLE
        self._pressed = set()
        self._cmds = queue.Queue()  # hotkey -> UI thread
        self._play_started = 0.0
        self._last_icon_state = None

        self.s = root.winfo_fpixels("1i") / 96.0
        root.title(APP_NAME)
        root.configure(bg=C["bg"])
        root.geometry(f"{self.px(760)}x{self.px(600)}")
        root.minsize(self.px(620), self.px(460))

        self._icons = {st: [ImageTk.PhotoImage(draw_state_icon(st, n)) for n in (16, 24, 32, 48, 64, 256)]
                       for st in (IDLE, RECORDING, PLAYING)}
        self._badge_icons = {st: ImageTk.PhotoImage(draw_state_icon(st, self.px(34)))
                             for st in (IDLE, RECORDING, PLAYING)}

        self._style()
        self._build()

        self.indicator = Indicator(root, self.s)
        self.indicator.place_at(self.corner.get())

        self.kb_listener = keyboard.Listener(on_press=self._kb_press, on_release=self._kb_release)
        extra = {"win32_event_filter": self._mouse_filter} if IS_WIN else {}
        self.ms_listener = mouse.Listener(on_move=self.recorder.on_move,
                                          on_click=self.recorder.on_click,
                                          on_scroll=self.recorder.on_scroll, **extra)
        self.kb_listener.start()
        self.ms_listener.start()

        # Precision touchpad two-finger scrolling bypasses the mouse hook.
        self.touch_gesture = TouchScrollGesture(
            self._touch_commit, natural=touchpad_natural_scroll() if IS_WIN else True)
        self.touchpad = None
        if IS_WIN:
            self.touchpad = TouchpadListener(self.touch_gesture.update)
            self.touchpad.start()

        root.protocol("WM_DELETE_WINDOW", self.quit)
        root.update_idletasks()
        dark_titlebar(root)
        self.set_state(IDLE)
        self._tick()

    def px(self, v):
        return int(v * self.s)

    # styling ----------------------------------------------------------
    def _style(self):
        st = ttk.Style(self.root)
        st.theme_use("clam")
        st.configure(".", background=C["panel"], foreground=C["text"],
                     fieldbackground=C["panel2"], bordercolor=C["border"],
                     lightcolor=C["border"], darkcolor=C["border"],
                     troughcolor=C["bg"], font=(FONT, 10))
        st.configure("TFrame", background=C["panel"])
        st.configure("TLabel", background=C["panel"], foreground=C["text"])
        st.configure("Muted.TLabel", foreground=C["muted"], font=(FONT, 9))
        st.configure("TCheckbutton", background=C["panel"], foreground=C["text"],
                     indicatorbackground=C["panel2"], indicatorforeground=C["accent"],
                     indicatorrelief="flat", focuscolor=C["panel"])
        st.map("TCheckbutton", background=[("active", C["panel"])],
               indicatorbackground=[("selected", C["panel2"]), ("active", C["border"])])
        for w in ("TSpinbox", "TCombobox"):
            st.configure(w, fieldbackground=C["panel2"], background=C["panel2"],
                         foreground=C["text"], arrowcolor=C["muted"],
                         insertcolor=C["text"], padding=self.px(4),
                         selectbackground=C["accent"], selectforeground="#fff")
            st.map(w, fieldbackground=[("readonly", C["panel2"]), ("disabled", C["bg"])],
                   foreground=[("disabled", C["faint"])],
                   bordercolor=[("focus", C["accent"])])
        self.root.option_add("*TCombobox*Listbox.background", C["panel2"])
        self.root.option_add("*TCombobox*Listbox.foreground", C["text"])
        self.root.option_add("*TCombobox*Listbox.selectBackground", C["accent"])
        self.root.option_add("*TCombobox*Listbox.font", (FONT, 10))
        st.configure("Treeview", background=C["panel"], fieldbackground=C["panel"],
                     foreground=C["text"], rowheight=self.px(24), borderwidth=0,
                     font=(MONO, 10))
        st.map("Treeview", background=[("selected", "#2b3a57")],
               foreground=[("selected", C["text"])])
        st.configure("Treeview.Heading", background=C["panel2"], foreground=C["muted"],
                     relief="flat", font=(FONT, 9, "bold"), padding=self.px(6))
        st.map("Treeview.Heading", background=[("active", C["border"])])
        st.layout("Treeview", [("Treeview.treearea", {"sticky": "nswe"})])
        st.configure("Vertical.TScrollbar", background=C["panel2"], troughcolor=C["panel"],
                     arrowcolor=C["muted"], bordercolor=C["panel"], relief="flat")
        st.map("Vertical.TScrollbar", background=[("active", C["border"])])
        st.configure("Horizontal.TProgressbar", background=C["play"],
                     troughcolor=C["panel2"], bordercolor=C["panel2"],
                     lightcolor=C["play"], darkcolor=C["play"])

    def _card(self, parent, title=None):
        outer = tk.Frame(parent, bg=C["border"])
        inner = tk.Frame(outer, bg=C["panel"], padx=self.px(14), pady=self.px(12))
        inner.pack(fill="both", expand=True, padx=1, pady=1)
        if title:
            tk.Label(inner, text=title.upper(), bg=C["panel"], fg=C["faint"],
                     font=(FONT, 8, "bold")).pack(anchor="w", pady=(0, self.px(8)))
        return outer, inner

    # layout -----------------------------------------------------------
    def _build(self):
        p = self.px
        root = self.root

        # Header
        head = tk.Frame(root, bg=C["bg"], padx=p(18), pady=p(14))
        head.pack(fill="x")
        self.head_icon = tk.Label(head, bg=C["bg"])
        self.head_icon.pack(side="left")
        titles = tk.Frame(head, bg=C["bg"])
        titles.pack(side="left", padx=(p(10), 0))
        tk.Label(titles, text=APP_NAME, bg=C["bg"], fg=C["text"],
                 font=(FONT, 14, "bold")).pack(anchor="w")
        tk.Label(titles, text="Record and replay keyboard & mouse input",
                 bg=C["bg"], fg=C["muted"], font=(FONT, 9)).pack(anchor="w")

        self.badge = tk.Frame(head, bg=C["panel2"], padx=p(12), pady=p(6))
        self.badge.pack(side="right")
        self.badge_dot = tk.Canvas(self.badge, width=p(10), height=p(10), bg=C["panel2"],
                                   highlightthickness=0)
        self.badge_dot.pack(side="left")
        self.badge_dot_id = self.badge_dot.create_oval(1, 1, p(10) - 1, p(10) - 1, outline="")
        self.badge_text = tk.Label(self.badge, bg=C["panel2"], fg=C["text"],
                                   font=(FONT, 9, "bold"))
        self.badge_text.pack(side="left", padx=(p(8), 0))
        self.badge_time = tk.Label(self.badge, bg=C["panel2"], fg=C["muted"],
                                   font=(MONO, 9))
        self.badge_time.pack(side="left", padx=(p(8), 0))

        body = tk.Frame(root, bg=C["bg"], padx=p(18))
        body.pack(fill="both", expand=True)

        # Transport controls
        bar = tk.Frame(body, bg=C["bg"])
        bar.pack(fill="x", pady=(0, p(12)))
        self.btn_rec = FlatButton(bar, "●  Record   F9", self.toggle_record, C["rec"], C["rec_hover"])
        self.btn_rec.pack(side="left")
        self.btn_play = FlatButton(bar, "▶  Play   F10", self.toggle_play, "#1f9d55", C["play_hover"])
        self.btn_play.pack(side="left", padx=p(8))
        self.btn_stop = FlatButton(bar, "■  Stop   Esc", self.stop_all, C["panel2"], C["border"])
        self.btn_stop.pack(side="left")
        sec = dict(bg=C["panel"], hover=C["panel2"], fg=C["text"], bold=False, padx=12)
        self.btn_clear = FlatButton(bar, "Clear", self.clear, **sec)
        self.btn_clear.pack(side="right")
        self.btn_save = FlatButton(bar, "Save…", self.save, **sec)
        self.btn_save.pack(side="right", padx=p(6))
        self.btn_open = FlatButton(bar, "Open…", self.load, **sec)
        self.btn_open.pack(side="right")

        # Settings cards
        cards = tk.Frame(body, bg=C["bg"])
        cards.pack(fill="x", pady=(0, p(12)))
        cards.columnconfigure((0, 1, 2), weight=1, uniform="c")

        o, c = self._card(cards, "Playback")
        o.grid(row=0, column=0, sticky="nsew", padx=(0, p(6)))
        grid = tk.Frame(c, bg=C["panel"])
        grid.pack(fill="x")
        ttk.Label(grid, text="Repeat").grid(row=0, column=0, sticky="w")
        self.repeat = tk.IntVar(value=1)
        self.repeat_box = ttk.Spinbox(grid, from_=1, to=9999, width=7, textvariable=self.repeat)
        self.repeat_box.grid(row=0, column=1, sticky="w", padx=(p(10), 0))
        ttk.Label(grid, text="Speed").grid(row=1, column=0, sticky="w", pady=(p(6), 0))
        self.speed = tk.StringVar(value="1×")
        ttk.Combobox(grid, textvariable=self.speed, width=7,
                     values=["0.25×", "0.5×", "1×", "1.5×", "2×", "4×", "8×"]
                     ).grid(row=1, column=1, sticky="w", padx=(p(10), 0), pady=(p(6), 0))
        ttk.Label(grid, text="Touchpad").grid(row=2, column=0, sticky="w", pady=(p(6), 0))
        self.touch_scale = tk.StringVar(value="100%")
        ttk.Combobox(grid, textvariable=self.touch_scale, width=7,
                     values=["50%", "75%", "90%", "100%", "110%", "125%", "150%", "200%"]
                     ).grid(row=2, column=1, sticky="w", padx=(p(10), 0), pady=(p(6), 0))
        self.forever = tk.BooleanVar(value=False)
        ttk.Checkbutton(c, text="Loop until stopped", variable=self.forever,
                        command=self._sync_forever).pack(anchor="w", pady=(p(8), 0))
        self.settle = tk.BooleanVar(value=True)
        ttk.Checkbutton(c, text="Let scrolling finish first", variable=self.settle
                        ).pack(anchor="w", pady=(p(4), 0))

        o, c = self._card(cards, "Recording")
        o.grid(row=0, column=1, sticky="nsew", padx=p(6))
        self.record_moves = tk.BooleanVar(value=True)
        ttk.Checkbutton(c, text="Record mouse movement", variable=self.record_moves).pack(anchor="w")
        ttk.Label(c, text="Drags are always captured.", style="Muted.TLabel").pack(anchor="w", pady=(p(4), 0))
        self.reverse_touch = tk.BooleanVar(value=False)
        ttk.Checkbutton(c, text="Reverse touchpad scroll", variable=self.reverse_touch,
                        command=self._sync_reverse).pack(anchor="w", pady=(p(6), 0))
        ttk.Label(c, text="Only raw input is recorded.", style="Muted.TLabel").pack(anchor="w")

        o, c = self._card(cards, "Indicator")
        o.grid(row=0, column=2, sticky="nsew", padx=(p(6), 0))
        self.show_indicator = tk.BooleanVar(value=True)
        ttk.Checkbutton(c, text="Show on-screen indicator", variable=self.show_indicator,
                        command=self._sync_indicator).pack(anchor="w")
        row = tk.Frame(c, bg=C["panel"])
        row.pack(fill="x", pady=(p(10), 0))
        ttk.Label(row, text="Position").pack(side="left")
        self.corner = tk.StringVar(value="Top right")
        cb = ttk.Combobox(row, textvariable=self.corner, width=12, state="readonly",
                          values=["Top left", "Top right", "Bottom left", "Bottom right"])
        cb.pack(side="left", padx=(p(8), 0))
        cb.bind("<<ComboboxSelected>>", lambda e: self.indicator.place_at(self.corner.get()))

        # Event list
        o, c = self._card(body)
        o.pack(fill="both", expand=True)
        c.config(padx=0, pady=0)
        cols = ("n", "time", "action", "details")
        self.tree = ttk.Treeview(c, columns=cols, show="headings", selectmode="browse")
        for col, text, w, anchor, stretch in (
                ("n", "#", 60, "e", False), ("time", "TIME", 90, "e", False),
                ("action", "EVENT", 140, "w", False), ("details", "DETAILS", 300, "w", True)):
            self.tree.heading(col, text=text, anchor=anchor)
            self.tree.column(col, width=self.px(w), anchor=anchor, stretch=stretch)
        for cat in ("key", "click", "scroll", "move"):
            self.tree.tag_configure(cat, foreground=C[cat])
        sb = ttk.Scrollbar(c, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        self.empty = tk.Label(c, text="No events yet\nPress F9 to start recording",
                              bg=C["panel"], fg=C["faint"], font=(FONT, 10), justify="center")

        # Footer
        foot = tk.Frame(root, bg=C["bg"], padx=p(18), pady=p(10))
        foot.pack(fill="x")
        self.stats = tk.Label(foot, bg=C["bg"], fg=C["muted"], font=(FONT, 9))
        self.stats.pack(side="left")
        self.progress = ttk.Progressbar(foot, length=self.px(180), mode="determinate")
        self.message = tk.Label(foot, bg=C["bg"], fg=C["muted"], font=(FONT, 9))
        self.message.pack(side="right")

        self.refresh()

    # global mouse hook filter (listener thread) -------------------------
    def _mouse_filter(self, msg, data):
        """Record wheel events with their exact delta.

        Touchpads and smooth-scrolling mice send partial notches (e.g. 20
        instead of 120). pynput rounds these down to whole notches, which
        drops small upward scrolls and turns small downward ones into a full
        notch, so wheel messages are handled here instead.
        """
        if msg in (WM_MOUSEWHEEL, WM_MOUSEHWHEEL):
            delta = ctypes.c_short(data.mouseData >> 16).value / WHEEL_DELTA
            dx, dy = (delta, 0) if msg == WM_MOUSEHWHEEL else (0, delta)
            self.recorder.on_scroll(data.pt.x, data.pt.y, round(dx, 6), round(dy, 6))
            return False  # handled; skip pynput's rounded version
        return True

    # touchpad (raw input thread) ----------------------------------------
    def _touch_commit(self, gesture_start, lift, steps):
        x, y = cursor_pos() if IS_WIN else (0, 0)
        self.recorder.add_touch_scroll(gesture_start, lift, steps, x, y)

    def _sync_reverse(self):
        self.touch_gesture.reverse = self.reverse_touch.get()

    # global keyboard hook (listener thread) -----------------------------
    def _kb_press(self, key):
        first = key not in self._pressed  # ignore auto-repeat for hotkeys
        self._pressed.add(key)
        if first and key == HOTKEY_RECORD:
            self._cmds.put(self.toggle_record)
        elif first and key == HOTKEY_PLAY:
            self._cmds.put(self.toggle_play)
        elif key == HOTKEY_ABORT and self.player.playing:
            self.player.stop()
        if not self.player.playing:
            self.recorder.on_key(key, True)

    def _kb_release(self, key):
        self._pressed.discard(key)
        if not self.player.playing:
            self.recorder.on_key(key, False)

    # state ------------------------------------------------------------
    def set_state(self, state):
        self.state = state
        if state != self._last_icon_state:
            self._last_icon_state = state
            self.root.iconphoto(False, *self._icons[state])
            self.head_icon.config(image=self._badge_icons[state])
        busy = state != IDLE
        self.btn_rec.set_enabled(state != PLAYING)
        self.btn_rec.set_text("■  Stop recording   F9" if state == RECORDING else "●  Record   F9")
        self.btn_play.set_enabled(state == IDLE and bool(self.events))
        self.btn_stop.set_enabled(busy)
        for b in (self.btn_open, self.btn_clear):
            b.set_enabled(not busy)
        self.btn_save.set_enabled(not busy and bool(self.events))
        title = {IDLE: APP_NAME, RECORDING: f"● REC — {APP_NAME}", PLAYING: f"▶ Playing — {APP_NAME}"}
        self.root.title(title[state])
        if state == PLAYING:
            self.progress.pack(side="right", padx=(self.px(10), 0))
        else:
            self.progress.pack_forget()
        self._sync_indicator()
        self._render_status()

    def _sync_indicator(self):
        self.indicator.show(self.show_indicator.get())

    def _sync_forever(self):
        self.repeat_box.state(["disabled"] if self.forever.get() else ["!disabled"])

    def _render_status(self):
        now = time.perf_counter()
        blink = int(now * 2) % 2 == 0
        if self.state == RECORDING:
            elapsed = now - self.recorder.started
            label, extra = "RECORDING", fmt_time(elapsed)
            pill = f"REC  {fmt_time(elapsed)}"
            dot = C["rec"] if blink else "#5a2028"
        elif self.state == PLAYING:
            elapsed = now - self._play_started
            rep = "∞" if self.player.repeat == 0 else self.player.repeat
            label, extra = "PLAYING", f"{fmt_time(elapsed)}  ·  loop {self.player.loop}/{rep}"
            pill = f"PLAY  {fmt_time(elapsed)}"
            dot = C["play"]
        else:
            label, extra, pill, dot = "IDLE", "", "IDLE", C["muted"]
        self.badge_dot.itemconfig(self.badge_dot_id, fill=dot)
        self.badge_text.config(text=label, fg=STATE_COLOR[self.state] if self.state != IDLE else C["text"])
        self.badge_time.config(text=extra)
        self.indicator.update_state(self.state, pill, blink)

    def _tick(self):
        try:
            while True:
                self._cmds.get_nowait()()
        except queue.Empty:
            pass
        if self.state == RECORDING:
            n = len(self.recorder.events)
            self.stats.config(text=f"{n:,} events captured")
        elif self.state == PLAYING:
            total = max(1, self.player.total)
            self.progress["value"] = 100 * self.player.index / total
            self.stats.config(text=f"Event {self.player.index:,} of {self.player.total:,}")
        self._render_status()
        self.root.after(100, self._tick)

    def flash(self, text):
        self.message.config(text=text)

    # actions ----------------------------------------------------------
    def toggle_record(self):
        if self.state == PLAYING:
            return
        if self.state == RECORDING:
            self.touch_gesture.flush()  # commit a scroll still in progress
            raw = self.recorder.stop()
            r = self.root
            rect = (r.winfo_rootx(), r.winfo_rooty(),
                    r.winfo_rootx() + r.winfo_width(), r.winfo_rooty() + r.winfo_height())
            self.events = tidy(raw, rect)
            self.refresh()
            self.set_state(IDLE)
            self.flash(f"Recorded {len(self.events):,} events")
        else:
            self.recorder.start(self.record_moves.get())
            self.set_state(RECORDING)
            self.flash("Recording — press F9 to stop")

    def toggle_play(self):
        if self.state == PLAYING:
            self.player.stop()
            return
        if self.state != IDLE:
            return
        if not self.events:
            self.flash("Nothing to play — record or open a macro first")
            return
        try:
            repeat = 0 if self.forever.get() else max(1, int(self.repeat.get()))
            speed = float(self.speed.get().replace("×", "").replace("x", "").strip())
            speed = min(max(speed, 0.05), 50)
            touch = float(self.touch_scale.get().replace("%", "").strip()) / 100
            touch = min(max(touch, 0.1), 10)
        except (tk.TclError, ValueError):
            messagebox.showerror("Invalid value", "Repeat, speed and touchpad must be numbers.")
            return
        self._play_started = time.perf_counter()
        self.progress["value"] = 0
        self.set_state(PLAYING)
        self.flash("Playing — F10 or Esc to stop")
        self.player.play(self.events, repeat, speed,
                         on_done=lambda: self._cmds.put(self._play_done),
                         touch_scale=touch,
                         scroll_settle=SCROLL_SETTLE if self.settle.get() else 0.0)

    def stop_all(self):
        if self.state == RECORDING:
            self.toggle_record()
        elif self.state == PLAYING:
            self.player.stop()

    def _play_done(self):
        self.set_state(IDLE)
        self.refresh_stats()
        self.flash("Playback finished")

    def refresh_stats(self):
        dur = self.events[-1]["t"] if self.events else 0
        self.stats.config(text=f"{len(self.events):,} events  ·  {dur:.1f}s")

    def refresh(self):
        self.tree.delete(*self.tree.get_children())
        for i, ev in enumerate(self.events, 1):
            cat, action, details = describe(ev)
            self.tree.insert("", "end", values=(i, f"{ev['t']:.3f}s", action, details), tags=(cat,))
        if self.events:
            self.empty.place_forget()
        else:
            self.empty.place(relx=0.5, rely=0.5, anchor="center")
        self.refresh_stats()

    def clear(self):
        if self.state == IDLE:
            self.events = []
            self.refresh()
            self.set_state(IDLE)
            self.flash("Cleared")

    def save(self):
        if not self.events or self.state != IDLE:
            return
        path = filedialog.asksaveasfilename(defaultextension=".json",
                                            filetypes=[("Macro files", "*.json")])
        if path:
            with open(path, "w", encoding="utf-8") as f:
                json.dump({"version": 1, "events": self.events}, f, indent=1)
            self.flash(f"Saved {len(self.events):,} events")

    def load(self):
        if self.state != IDLE:
            return
        path = filedialog.askopenfilename(filetypes=[("Macro files", "*.json")])
        if not path:
            return
        try:
            with open(path, encoding="utf-8") as f:
                self.events = json.load(f)["events"]
        except Exception as e:
            messagebox.showerror("Open failed", str(e))
            return
        self.refresh()
        self.set_state(IDLE)
        self.flash(f"Opened {len(self.events):,} events")

    def quit(self):
        self.player.stop()
        self.kb_listener.stop()
        self.ms_listener.stop()
        if self.touchpad:
            self.touchpad.stop()
        self.root.destroy()


if __name__ == "__main__":
    root = tk.Tk()
    App(root)
    root.mainloop()
