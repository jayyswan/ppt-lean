# Session 40 helper: loads EngineO.gp into cypari (6 lines skipped as comments). Exec this from the other session 40 scripts.
import cypari; P=cypari.pari
P.allocatemem(10**9)
for l in open('EngineO.gp'):
    l=l.strip()
    if l and not l.startswith('\\\\'): P(l)
