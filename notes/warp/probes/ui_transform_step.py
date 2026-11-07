"""Step-by-step: open Shape Format > Text Effects > Transform and list what appears."""
import time, ctypes, threading
try: ctypes.windll.shcore.SetProcessDpiAwareness(2)
except Exception: pass
from pywinauto import Desktop
from warplab import *
lab = Lab(visible=True)
def log(*a): print(f"[{time.strftime('%H:%M:%S')}]", *a, flush=True)
try:
    win = lab.p.Windows(1); win.Activate(); win.WindowState = 3
    tb = lab.textbox("Text", box=(150, 100, 288, 144)); tb.Select(); time.sleep(0.6)
    h = [x for x in Desktop(backend="uia").windows() if lab.p.Name.split(".")[0] in x.window_text()][0].handle
    w = Desktop(backend="uia").window(handle=h).wrapper_object(); log("window ok")
    tab = [c for c in w.descendants(control_type="TabItem") if "Shape Format" in c.window_text()][0]
    tab.select(); time.sleep(0.8); log("tab selected")
    te = [c for c in w.descendants() if c.window_text() == "Text Effects"]
    log("text effects controls:", [(c.element_info.control_type, c.element_info.automation_id) for c in te])
    t = threading.Thread(target=lambda: te[0].expand() if hasattr(te[0], "expand") else te[0].invoke(), daemon=True); t.start()
    time.sleep(2.0); log("expand returned" if not t.is_alive() else "expand still blocking")
    tr = [c for c in w.descendants(control_type="MenuItem") if c.window_text() == "Transform"][0]
    t = threading.Thread(target=tr.expand, daemon=True); t.start(); time.sleep(2.0)
    log("transform expand", "returned" if not t.is_alive() else "blocking")
    items = [c for c in w.descendants(control_type="ListItem")]
    log("list items tail:", [c.window_text() for c in items][-60:])
    menus = [c for c in w.descendants() if c.element_info.control_type in ("Menu", "Group", "List") and "ransform" in c.window_text()]
    log("transform containers:", [(c.window_text(), c.element_info.control_type) for c in menus])
    for d in Desktop(backend="uia").windows():
        if d.element_info.class_name and "Net UI" in d.element_info.class_name:
            log("popup window", d.window_text(), d.element_info.class_name, len(d.descendants(control_type="ListItem")))
    first = []
    if first:
        log("applying", first[0].window_text(), "patterns", first[0].element_info.element.GetCurrentPropertyValue(30044) if False else "")
        t = threading.Thread(target=lambda: first[0].invoke(), daemon=True); t.start(); time.sleep(2.0)
        log("invoke", "returned" if not t.is_alive() else "blocking", "| warp now", tb.TextFrame2.WarpFormat)
finally:
    try:
        from pywinauto import keyboard; keyboard.send_keys("{ESC}{ESC}")
    except Exception: pass
    time.sleep(0.5); lab.close(); log("closed")
