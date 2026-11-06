"""List ribbon controls of the PowerPoint window (UI Automation), for writing probe_ui_inputs.py."""
import time, ctypes, sys
try: ctypes.windll.shcore.SetProcessDpiAwareness(2)
except Exception: pass
from pywinauto import Desktop
from warplab import *
lab = Lab(visible=True)
try:
    win = lab.p.Windows(1); win.Activate(); win.WindowState = 3
    tb = lab.textbox("◗", box=(150, 100, 288, 288))
    tb.TextFrame2.TextRange.Select(); time.sleep(1)
    hwnd = win.HWND if hasattr(win, "HWND") else None
    app_title = lab.p.Name
    w = [x for x in Desktop(backend="uia").windows() if app_title.split(".")[0] in x.window_text()][0]
    print("window:", w.window_text())
    keys = sys.argv[1:] or ["Font", "Size", "Spacing", "Height", "Width"]
    for c in w.descendants():
        try:
            n = c.element_info.name or ""; t = c.element_info.control_type
        except Exception: continue
        if any(k.lower() in n.lower() for k in keys):
            print(repr(n), t, c.element_info.automation_id)
finally:
    lab.close()
