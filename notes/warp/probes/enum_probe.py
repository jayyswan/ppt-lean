"""Map PowerPoint's TextFrame2.WarpFormat enum (COM) to the DrawingML prstTxWarp names.

Observation only: COM sets the preset on a scratch text box in a new presentation and
the saved XML is read back. Every value corresponds to a Transform-gallery item in the UI.
"""
import os, re, sys, zipfile, tempfile
import win32com.client as wc
app = wc.Dispatch("PowerPoint.Application")
p = app.Presentations.Add(WithWindow=False)
s = p.Slides.Add(1, 12)
tb = s.Shapes.AddTextbox(1, 100, 100, 288, 288)
tb.TextFrame2.TextRange.Text = "A"
f = os.path.join(tempfile.gettempdir(), "warp_enum.pptx")
out = {}
for k in range(0, 40):
    try:
        tb.TextFrame2.WarpFormat = k
    except Exception as e:
        out[k] = f"ERR {e.__class__.__name__}"; continue
    p.SaveCopyAs(f)
    x = zipfile.ZipFile(f).read("ppt/slides/slide1.xml").decode()
    m = re.search(r'prstTxWarp prst="(\w+)"', x)
    out[k] = (m.group(1) if m else None, tb.TextFrame2.WarpFormat)
p.Close()
for k, v in out.items(): print(k, v)
