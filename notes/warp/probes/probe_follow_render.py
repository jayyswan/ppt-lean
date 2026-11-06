"""Check whether a Follow Path preset survives the XML round trip and how it renders."""
from warplab import *
lab = Lab(visible=True)
try:
    tb = lab.textbox("▦▦▦▦", size=40, box=(100, 100, 288, 288))
    xml_edit_reopen(lab, set_warp_xml("textArchUp"))
    x = lab.slide_xml(); print(re.findall(r'<a:bodyPr.*?</a:bodyPr>', x, re.S))
    sh = lab.s.Shapes(1); print("WarpFormat", sh.TextFrame2.WarpFormat)
    lab.s.Export(os.path.abspath("follow_render.png"), "PNG", 1200, 675)
finally:
    lab.close()
