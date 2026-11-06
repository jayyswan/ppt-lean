"""Write an unhinted copy of a TrueType font under a new family name (for testing whether a
PowerPoint metric comes from hinting). Usage: py make_nohint.py SRC DST FAMILY"""
import sys
from fontTools.ttLib import TTFont
from fontTools.ttLib.tables import ttProgram
src, dst, family = sys.argv[1:4]
f = TTFont(src)
for t in ("fpgm", "prep", "cvt ", "hdmx", "VDMX", "LTSH", "DSIG", "gasp"):
    if t in f: del f[t]
glyf = f["glyf"]
for name in f.getGlyphOrder():
    g = glyf[name]
    if hasattr(g, "program"):
        g.program = ttProgram.Program(); g.program.fromBytecode(b"")
f["maxp"].maxSizeOfInstructions = 0
for rec in f["name"].names:
    if rec.nameID in (1, 16): rec.string = family
    elif rec.nameID == 4: rec.string = family
    elif rec.nameID == 6: rec.string = family.replace(" ", "")
    elif rec.nameID == 3: rec.string = family + " test"
f.save(dst); print("wrote", dst)
