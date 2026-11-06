import re, io, sys, os, bisect
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
os.chdir(r'C:\dev\Powerpoint\lean\pptc')
src = open('Pptc/DegreeSeven.lean', encoding='utf-8').read().replace('\r', '')
lines = src.split('\n')
decl = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+)*"
                  r"(theorem|lemma|def|abbrev)\s+([^\s:({\[]+)")
decls = [(i, m.group(2)) for i, l in enumerate(lines, 1) if (m := decl.match(l))]
starts = [d[0] for d in decls] + [len(lines) + 1]
NAMECH = r"A-Za-z0-9_'!?\u2080-\u2089"
tok = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?.\u2080-\u2089]*")
names = {n for _, n in decls}
short = {}
for _, n in decls:
    short.setdefault(n.split('.')[-1], set()).add(n)
deps = {}
for k, (ln, name) in enumerate(decls):
    body = '\n'.join(lines[ln - 1:starts[k + 1] - 1])
    # strip comments
    body = re.sub(r'/-.*?-/', '', body, flags=re.S)
    body = re.sub(r'--[^\n]*', '', body)
    d = set()
    for t in tok.findall(body):
        for piece in {t, t.split('.')[-1]}:
            for full in short.get(piece.split('.')[-1], ()):
                if full != name:
                    d.add(full)
    deps[name] = d
roots = sys.argv[1:] or ['root_Pconstructible_of_nonreal_root']
seen = set()
stack = list(roots)
while stack:
    x = stack.pop()
    if x in seen:
        continue
    seen.add(x)
    stack.extend(deps.get(x, ()))
size = {name: starts[k + 1] - ln for k, (ln, name) in enumerate(decls)}
dead = [(ln, n) for ln, n in decls if n not in seen]
print(f"reachable: {len(seen)} decls; unreachable: {len(dead)} decls, "
      f"{sum(size[n] for _, n in dead)} lines")
for ln, n in dead:
    print(f"{ln:5} {n:55} {size[n]:4}")
