# 数值核对 C1 证明的前提：真 Fermat 点满足方程组 g1–g4（对棱张角相等 + 三个余弦之和 = −1），且 A > 0、D > 0。
# 需要 circ_scan/mp_circ.py（本地）。用法：在 circ_scan/ 下 python3 proofs/C1/c1_numeric_check.py
import sys; sys.path.insert(0,'.')
from mp_circ import *
mp.mp.dps=50
def fermat(T):
    V=T.V;X=T.G
    for _ in range(400):
        w=[1/nrm(X-v) for v in V];X=sum((w[i]*V[i] for i in range(4)),V3(0,0,0))/sum(w)
    for _ in range(30):
        g=V3(0,0,0);H=mp.zeros(3,3)
        for v in V:
            u=X-v;d=nrm(u);g+=u/d
            for a in range(3):
                for b in range(3):H[a,b]+=((1 if a==b else 0)-u[a]*u[b]/d**2)/d
        X=X-mp.lu_solve(H,g)
    return X
for seed in range(6):
    T=Tet.rand(seed);t=T.t;F=fermat(T);d0,d1,d2,d3=[nrm(F-v) for v in T.V]
    E=lambda i,j:(t[i]+t[j])**2
    g=[d2*d3*(d0**2+d1**2-E(0,1))-d0*d1*(d2**2+d3**2-E(2,3)),
       d1*d3*(d0**2+d2**2-E(0,2))-d0*d2*(d1**2+d3**2-E(1,3)),
       d1*d2*(d0**2+d3**2-E(0,3))-d0*d3*(d1**2+d2**2-E(1,2)),
       d2*d3*(d0**2+d1**2-E(0,1))+d1*d3*(d0**2+d2**2-E(0,2))+d1*d2*(d0**2+d3**2-E(0,3))+2*d0*d1*d2*d3]
    A=sum([d0,d1,d2,d3][i]/t[i] for i in range(4))
    print(seed,'max|g| = %s'%mp.nstr(max(abs(x) for x in g),3),' A = %s'%mp.nstr(A,6))
