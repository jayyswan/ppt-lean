import sys, time, ctypes
try: ctypes.windll.shcore.SetProcessDpiAwareness(2)
except Exception: pass
from PIL import ImageGrab
from warplab import *
lab = Lab(visible=True)
try:
    win = lab.p.Windows(1); win.Activate(); win.WindowState = 3
    tb = lab.textbox("●●", box=(150, 100, 288, 288)); tb.TextFrame2.WarpFormat = WARP_ID["textTriangle"]
    time.sleep(1); tb.Select(); time.sleep(1)
    sx = lambda x: win.PointsToScreenPixelsX(x); sy = lambda y: win.PointsToScreenPixelsY(y)
    print("box px", sx(150), sy(100), sx(438), sy(388))
    ImageGrab.grab(all_screens=True).save("shot_handle.png")
finally:
    lab.close()
