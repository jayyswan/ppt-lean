using HomotopyContinuation, JSON, LinearAlgebra, Serialization
D = JSON.parsefile("tb_poly_data.json")
bf(s) = parse(BigFloat, s)
setprecision(256)
A=Float64(bf(D["A"])); B=Float64(bf(D["B"])); a1=Float64(bf(D["a1"])); a3=Float64(bf(D["a3"])); b2=Float64(bf(D["b2"]))
q=Float64(bf(D["q"])); c=Float64(bf(D["c"])); d=Float64(bf(D["d"]))
A2=[Float64(bf(D["A2"][i][j])) for i in 1:2, j in 1:2]; A2iT=[Float64(bf(D["A2iT"][i][j])) for i in 1:2, j in 1:2]
E=[(Float64(bf(e[1])),Float64(bf(e[2]))) for e in D["e"]]
x0=ComplexF64[Float64(bf(s)) for s in D["sol"]]
@var d1 d2 XT YT b0 b1 g0 g1 g2 g3 L[1:9] M[1:9] Tau[1:9] p[1:37]
eqs=Expression[YT^2-XT^3-A*XT-B]
for i in 1:9
    x,y=E[i]; l=L[i]; m=M[i]; t=Tau[i]
    push!(eqs, l*(XT-x)-(YT-y))
    X=l^2-x-XT; Y=l*(x-X)-y; xl=X-b2/12; yl=Y-(a1*xl+a3)/2
    push!(eqs, m*yl-(2q*(xl+c)-d^2/(2q)))
    w=-q+m*(m*xl-d)/(2q)
    Den=16*m^2*(1+m^2)*w
    P0D=(4*m*(1-m^2)*(1+m^2)*w, (1-m^2)^2*(1+m^2)*w)
    n1D=(-(1-m^2)*16*m^2*w, 32*m^3*w)
    Q1=(P0D[1]+d1*n1D[1], P0D[2]+d1*n1D[2])
    m2=(-(1-m^2)/2, m); k=16*m^2*(1+m^2)
    PD=[A2[j,1]*Q1[1]+A2[j,2]*Q1[2] + d2*k*(A2iT[j,1]*m2[1]+A2iT[j,2]*m2[2]) for j in 1:2]
    Bx=b0+b1*t+t^3; By=g0+g1*t+g2*t^2+g3*t^3
    push!(eqs, PD[1]-Den*Bx); push!(eqs, PD[2]-Den*By)
end
vars=[d1,d2,XT,YT,b0,b1,g0,g1,g2,g3,L...,M...,Tau...]
F=System(eqs .- p; variables=vars, parameters=p)
r0=F(x0, zeros(37)); println("start residual ", norm(r0))
p0=randn(ComplexF64,37)*1e-3
# move start to a generic base point by a straight-line parameter homotopy
R0=solve(F,[x0]; start_parameters=zeros(ComplexF64,37), target_parameters=p0)
xs0=solutions(R0); println("moved to generic base: ", length(xs0))
mres=monodromy_solve(F, xs0, p0; max_loops_no_progress=parse(Int,get(ENV,"NOPROG","8")), permutations=true, threading=true, timeout=parse(Float64,get(ENV,"HCT","4500")), show_progress=true)
println(mres)
S=solutions(mres); println("generic fibre count found: ", length(S))
serialize("tb_hc_generic.jls", (p0,S,permutations(mres)))
# track to the true system p=0
R=solve(F, S; start_parameters=p0, target_parameters=zeros(ComplexF64,37), threading=true)
println(R)
sols=solutions(R; only_nonsingular=true)
serialize("tb_hc_p0.jls", sols)
function genuine(s)
    Lm=s[20:28]; T=s[29:37]
    ok = all(abs.(Lm).>1e-6) && all(abs.(1 .+ Lm.^2).>1e-6) && all(abs(s[3]-E[i][1])>1e-6 for i in 1:9)
    ok &= minimum(abs(T[i]-T[j]) for i in 1:9 for j in 1:i-1) > 1e-6
    ok
end
G=filter(genuine, sols); println("genuine at p=0: ", length(G), "   real: ", count(s->maximum(abs.(imag.(s)))<1e-7, G))
for s in G
    if maximum(abs.(imag.(s)))<1e-7; println("real d1,d2 = ", real(s[1]), "  ", real(s[2])); end
end
