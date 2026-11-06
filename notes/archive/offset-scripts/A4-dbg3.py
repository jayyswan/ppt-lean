import random
p=(1<<61)-1
exec(open(r'C:\dev\Powerpoint\lean\archived files\offset-scripts\A4-06-degree-modp.py').read().split('for n in (1,2,3):')[0])

# positive control: random points are full-rank
pts=[(random.randrange(p),random.randrange(p)) for _ in range(140)]
for N in (2,3,8):
    mons=[(i,j) for i in range(N+1) for j in range(N+1-i)]
    A=[[ (pow(x,i,p)*pow(y,j,p))%p for (i,j) in mons] for (x,y) in pts]
    print("random pts N=%d rank %d / %d"%(N,rank_mod_p(A,len(mons)),len(mons)))

# control: points on a conic X^2+Y^2=1 (param through rational) -> degree 2
pts=[]
s=1
while len(pts)<140:
    s+=1
    x=(s*s-1)*pow(s*s+1,p-2,p)%p; y=(2*s)*pow(s*s+1,p-2,p)%p
    pts.append((x,y))
for N in (1,2,3):
    mons=[(i,j) for i in range(N+1) for j in range(N+1-i)]
    A=[[ (pow(x,i,p)*pow(y,j,p))%p for (i,j) in mons] for (x,y) in pts]
    print("conic pts N=%d rank %d / %d"%(N,rank_mod_p(A,len(mons)),len(mons)))

# plain offset of gamma (no L): should be degree 10
savedMaps=Maps[:]
Maps[:]=[(1,0,0,1)]
pts=collect(1,140)
for N in (8,9,10,11,12):
    mons=[(i,j) for i in range(N+1) for j in range(N+1-i)]
    A=[[ (pow(pts[k][0],i,p)*pow(pts[k][1],j,p))%p for (i,j) in mons] for k in range(len(pts))]
    print("plain offset N=%d rank %d / %d"%(N,rank_mod_p(A,len(mons)),len(mons)))
Maps[:]=savedMaps
