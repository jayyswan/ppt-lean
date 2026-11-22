# Session 40: the Engine O member at Delta_h = 0 (a=-3, b=2: h=(x-1)^2(x+2)), generic U: root multiplicities
exec(open('load.py').read())
for U in ['1/3','2','-5/7']:
    g=P(f'substvec(G,[a,b,U],[-3,2,{U}])')
    f=P('factor')(g)
    print(U, [(str(f[0][i]), int(f[1][i])) for i in range(len(f[0]))])
