# Session 6: run a GP file through cypari (no gp binary here): python3 run_read.py file.gp
import cypari, sys; pari=cypari.pari
pari.allocatemem(3*10**9)
pari('read("%s")' % sys.argv[1])
