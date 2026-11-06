"""Probe 4: does dragging a warp handle past its stop store the bound exactly?

UI action: a real mouse drag (SendInput via pywinauto.mouse) of the yellow handle of a
warped text box, far past the end of its range. COM only selects the shape (= clicking it),
converts slide points to screen pixels, and reads back Adjustments / the saved XML.
Usage: py probe_handle.py PRESET HX HY DX DY   (handle position and drag target as fractions
of the box: x = L + HX*W, y = T + HY*H)."""
import sys, time, ctypes, re
try: ctypes.windll.shcore.SetProcessDpiAwareness(2)
except Exception: pass
from pywinauto import mouse
from warplab import *
pr = sys.argv[1]; hx, hy, dx, dy = map(float, sys.argv[2:6])
text = sys.argv[6] if len(sys.argv) > 6 else "●●"
BOX = (150, 100, 288, 288)
lab = Lab(visible=True)
try:
    win = lab.p.Windows(1); win.Activate(); win.WindowState = 3  # maximize
    win.ViewType = 9  # normal
    tb = lab.textbox(text, box=BOX)
    tb.TextFrame2.WarpFormat = WARP_ID[pr]
    time.sleep(1.0); tb.Select(); time.sleep(0.8)
    L, T, W, H = BOX
    sx = lambda x: win.PointsToScreenPixelsX(x); sy = lambda y: win.PointsToScreenPixelsY(y)
    p0 = (int(sx(L + hx * W)), int(sy(T + hy * H))); p1 = (int(sx(L + dx * W)), int(sy(T + dy * H)))
    print("before", [tb.Adjustments.Item(i + 1) for i in range(tb.Adjustments.Count)], "drag", p0, "->", p1)
    mouse.press(coords=p0); time.sleep(0.3)
    for k in range(1, 21):
        mouse.move(coords=(p0[0] + (p1[0] - p0[0]) * k // 20, p0[1] + (p1[1] - p0[1]) * k // 20)); time.sleep(0.04)
    mouse.release(coords=p1); time.sleep(0.8)
    adj = [tb.Adjustments.Item(i + 1) for i in range(tb.Adjustments.Count)]
    x = lab.slide_xml()
    av = re.findall(r'<a:prstTxWarp prst="(\w+)">(.*?)</a:prstTxWarp>', x, re.S)
    print("after ", adj, "| shape box", round(tb.Left, 2), round(tb.Top, 2), round(tb.Width, 2), round(tb.Height, 2))
    print("xml:", av)
finally:
    time.sleep(0.5)
    lab.close()
