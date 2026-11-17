"""Integer font metrics Windows (GDI) reports for a font at each pixel size n."""
import ctypes, ctypes.wintypes as W
gdi = ctypes.windll.gdi32; user = ctypes.windll.user32


class TEXTMETRICW(ctypes.Structure):
    _fields_ = [(n, W.LONG) for n in ("tmHeight", "tmAscent", "tmDescent", "tmInternalLeading", "tmExternalLeading",
                                        "tmAveCharWidth", "tmMaxCharWidth", "tmWeight", "tmOverhang",
                                        "tmDigitizedAspectX", "tmDigitizedAspectY")] + \
               [(n, W.WCHAR) for n in ("tmFirstChar", "tmLastChar", "tmDefaultChar", "tmBreakChar")] + \
               [(n, ctypes.c_byte) for n in ("tmItalic", "tmUnderlined", "tmStruckOut", "tmPitchAndFamily", "tmCharSet")]


def metrics(face, n, em=True):
    hdc = user.GetDC(0)
    f = gdi.CreateFontW(-n if em else n, 0, 0, 0, 400, 0, 0, 0, 1, 0, 0, 0, 0, face)
    old = gdi.SelectObject(hdc, f); tm = TEXTMETRICW(); gdi.GetTextMetricsW(hdc, ctypes.byref(tm))
    gdi.SelectObject(hdc, old); gdi.DeleteObject(f); user.ReleaseDC(0, hdc)
    return {k: getattr(tm, k) for k in ("tmHeight", "tmAscent", "tmDescent", "tmInternalLeading", "tmExternalLeading")}


if __name__ == "__main__":
    import json, math
    rows = {r["n"]: r for r in json.load(open("equalize6.json"))}
    for n in list(range(2, 42)):
        m = metrics("Segoe UI Symbol", n); r = rows[n]; H = r["eq"][1] - r["eq"][0]; B = r["plain"][1]
        print(n, "H", H, "B", B, "T", r["eq"][0], m)
