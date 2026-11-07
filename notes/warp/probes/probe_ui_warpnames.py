"""Probe 24: the Transform gallery's UI names for each warp preset. Opens Shape Format >
Text Effects > Transform through UI Automation, applies each gallery item, and reads which
preset (WarpFormat -> spec name) it set. Takes the screen. Usage: py probe_ui_warpnames.py"""
import time, ctypes, json, threading, sys, re
try: ctypes.windll.shcore.SetProcessDpiAwareness(2)
except Exception: pass
from pywinauto import Desktop, keyboard
from warplab import *
NAME_OF = {v: k for k, v in WARP_ID.items()}
lab = Lab(visible=True); out = {}
def log(*a): print(*a, flush=True)
try:
    win = lab.p.Windows(1); win.Activate(); win.WindowState = 3
    tb = lab.textbox("Text", box=(150, 100, 288, 144))
    h = [x for x in Desktop(backend="uia").windows() if lab.p.Name.split(".")[0] in x.window_text()][0].handle
    w = Desktop(backend="uia").window(handle=h).wrapper_object()
    def bg(f, wait=1.5):
        t = threading.Thread(target=f, daemon=True); t.start(); time.sleep(wait)
    def gallery():
        tb.Select(); time.sleep(0.5)
        [c for c in w.descendants(control_type="TabItem") if "Shape Format" in c.window_text()][0].select(); time.sleep(0.6)
        te = [c for c in w.descendants() if c.window_text() == "Text Effects"][0]; bg(te.expand)
        tr = [c for c in w.descendants(control_type="MenuItem") if c.window_text() == "Transform"][0]; bg(tr.expand, 2.0)
        items = [c for c in w.descendants(control_type="ListItem")]
        i0 = max(i for i, c in enumerate(items) if c.window_text() == "None")
        return items[i0:]
    names = [c.window_text() for c in gallery()]; keyboard.send_keys("{ESC}{ESC}{ESC}"); time.sleep(0.5)
    log("gallery:", names)
    if len(sys.argv) > 1: names = sys.argv[1:]
    for nm in names:
        it = [c for c in gallery() if c.window_text() == nm][0]
        bg(it.invoke, 1.2)
        wf = tb.TextFrame2.WarpFormat; out[nm] = NAME_OF.get(wf, wf)
        if wf == 0 and nm != "None":
            xm = re.findall(r'prstTxWarp prst="(\w+)"', lab.slide_xml()); out[nm] = xm[-1] if xm else 0
        log(f"{nm!r} -> {out[nm]}")
        keyboard.send_keys("{ESC}{ESC}{ESC}"); time.sleep(0.3)
finally:
    json.dump(out, open("ui_warpnames.json" if len(sys.argv) == 1 else "ui_warpnames_extra.json", "w"), indent=1); lab.close()
