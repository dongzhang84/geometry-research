# 《棱切球四面体定理》定理 1–10 的符号证明（Claude Code）：把 exact_check.py 的有理数换成有理函数域 ℚ(t1, t2, t3, u)。
# t0 = 1 不失一般性：每条定理都在相似变换下不变，而把切长同乘一个正数就是相似变换。
# 含 Soddy 球的定理在 ℚ(t)(√D) 里算；D 不是 ℚ(t) 里的平方，所以这是域，判零是精确的。
# 定理 2 里 P = (1−u)G + uM，u 也是符号，所以对直线 GM 上的每一点成立。
# 用法：python3 symbolic_check.py [定理编号 ...]      例如 python3 symbolic_check.py 1 4 8
import sys,random,time,itertools
from sympy import QQ
from sympy.polys.fields import field
FLD,t1s,t2s,t3s,us=field("t1,t2,t3,u",QQ)
def Fr(a,b=1):
    if isinstance(a,int) and isinstance(b,int):return FLD(QQ(a,b))
    return FLD(a)/b if not isinstance(a,int) else FLD(QQ(a))/b
EDGES=list(itertools.combinations(range(4),2));PAIRS=[((0,1),(2,3)),((0,2),(1,3)),((0,3),(1,2))]
class Q2:
    """Q(√D) 的元素 a + b√D，D 是当前样本的全局常数"""
    D=Fr(2)
    __slots__=('a','b')
    def __init__(s,a,b=0):s.a=a if not isinstance(a,int) else Fr(a);s.b=b if not isinstance(b,int) else Fr(b)
    @staticmethod
    def c(x):return x if isinstance(x,Q2) else Q2(x)
    def __add__(s,o):o=Q2.c(o);return Q2(s.a+o.a,s.b+o.b)
    __radd__=__add__
    def __neg__(s):return Q2(-s.a,-s.b)
    def __sub__(s,o):return s+(-Q2.c(o))
    def __rsub__(s,o):return Q2.c(o)-s
    def __mul__(s,o):o=Q2.c(o);return Q2(s.a*o.a+s.b*o.b*Q2.D,s.a*o.b+s.b*o.a)
    __rmul__=__mul__
    def inv(s):n=s.a*s.a-s.b*s.b*Q2.D;return Q2(s.a/n,-s.b/n)
    def __truediv__(s,o):return s*Q2.c(o).inv()
    def __rtruediv__(s,o):return Q2.c(o)*s.inv()
    def iszero(s):return s.a==0 and s.b==0
def Z0(x):return x.iszero() if isinstance(x,Q2) else x==0
def det(M):
    M=[r[:] for r in M];n=len(M);d=1
    for c in range(n):
        p=next((r for r in range(c,n) if not Z0(M[r][c])),None)
        if p is None:return 0
        if p!=c:M[c],M[p]=M[p],M[c];d=-d
        d=d*M[c][c]
        for r in range(c+1,n):
            f=M[r][c]/M[c][c]
            if not Z0(f):M[r]=[a-f*b for a,b in zip(M[r],M[c])]
    return d
def rank(M):
    M=[r[:] for r in M];rk=0;cols=len(M[0])
    for c in range(cols):
        p=next((r for r in range(rk,len(M)) if not Z0(M[r][c])),None)
        if p is None:continue
        M[rk],M[p]=M[p],M[rk]
        for r in range(len(M)):
            if r!=rk and not Z0(M[r][c]):f=M[r][c]/M[rk][c];M[r]=[a-f*b for a,b in zip(M[r],M[rk])]
        rk+=1
    return rk
class Tet:
    def __init__(s,t):
        s.t=t;s.d2=[[0 if i==j else (t[i]+t[j])**2 for j in range(4)] for i in range(4)]
    def nz(s,w):S=sum(w,0*w[0]);return [x/S for x in w]
    def dist2(s,x,y):  # 规范化重心坐标
        u=[a-b for a,b in zip(x,y)];return -sum((u[i]*u[j]*s.d2[i][j] for i in range(4) for j in range(i+1,4)),0*u[0])
    def dot(s,x,a,y,b):  # (x−a)·(y−b)，极化公式
        return (s.dist2(x,b)+s.dist2(a,y)-s.dist2(x,y)-s.dist2(a,b))/2
    def lin(s,*pairs):  # 线性组合 Σ c_k P_k（规范化）
        return [sum((c*P[i] for c,P in pairs),0*pairs[0][1][0]) for i in range(4)]
    def V(s,i):return [Fr(int(j==i)) for j in range(4)]
    def cospherical(s,P):  # 5 点距离平方矩阵行列式 = 0 ⇔ 共球或共面
        return det([[s.dist2(a,b) for b in P] for a in P])
    def coplanar4(s,P):return det([list(p) for p in P])   # 4 个规范化重心坐标行列式
def sample(rng):return [Fr(rng.randint(2,60),rng.randint(1,20)) for _ in range(4)]
def setup(t):
    T=Tet(t);a=[1/x for x in t];Ta=sum(t)
    T.G=T.nz([Fr(1)]*4);T.Z=T.nz(a);S2=[(Ta-x)/x for x in t];T.K=T.nz(S2);T.S2=S2
    Sg=sum(a)/2;T.M=T.nz([ai*(Sg-ai) for ai in a])
    # 外心：解 (E o)_i = 常数，Σo = 1
    E=[[T.d2[i][j] for j in range(4)] for i in range(4)]
    A=[E[i]+[Fr(-1)] for i in range(4)]+[[Fr(1)]*4+[Fr(0)]];b=[Fr(0)]*4+[Fr(1)]
    T.O=solve(A,b)[:4]
    T.R2=T.dist2(T.O,T.V(0));T.rho2=T.dist2(T.M,T.V(0))-t[0]**2
    T.Te={e:T.nz([t[j] if k==i else t[i] if k==j else Fr(0) for k in range(4)]) for (i,j) in [e for e in EDGES] for e in [(i,j)]}
    return T
def solve(A,b):
    n=len(A);M=[A[i][:]+[b[i]] for i in range(n)]
    for c in range(n):
        p=next(r for r in range(c,n) if M[r][c]!=0);M[c],M[p]=M[p],M[c]
        for r in range(n):
            if r!=c and M[r][c]!=0:f=M[r][c]/M[c][c];M[r]=[x-f*y for x,y in zip(M[r],M[c])]
    return [M[i][n]/M[i][i] for i in range(n)]
def inv(T,P,C,r2):d2=T.dist2(P,C);k=r2/d2;return T.lin((k,P),(1-k,C))
def face(T,f):  # 面（顶点下标三元组）上的点：内心、Feuerbach 点（重心坐标用切长写）
    j,k,l=f;t=T.t
    def emb(w):x=[Fr(0)]*4;x[j],x[k],x[l]=w;return T.nz(x)
    I=emb([t[k]+t[l],t[j]+t[l],t[j]+t[k]]);X11=emb([t[j]*(t[k]-t[l])**2,t[k]*(t[j]-t[l])**2,t[l]*(t[j]-t[k])**2])
    return I,X11
def foot(T,P,A,B):  # P 在直线 AB 上的垂足
    k=T.dot(P,A,B,A)/T.dist2(B,A);return T.lin((1-k,A),(k,B))
def mid(T,P,Q):return T.lin((Fr(1,2),P),(Fr(1,2),Q))
def TeOpp(T,p):(a,b),(c,d)=PAIRS[p];return mid(T,T.Te[(a,b)],T.Te[(c,d)])
def lift(T):  # 把所有坐标升到 Q2
    for k in ('G','Z','K','M','O'):setattr(T,k,[Q2(x) for x in getattr(T,k)])
    T.Te={e:[Q2(x) for x in v] for e,v in T.Te.items()};T.R2=Q2(T.R2);T.rho2=Q2(T.rho2)
    T.Vq=lambda i:[Q2(int(j==i)) for j in range(4)]
def soddy(T,sgn):
    """σ1（sgn=+1）或 σ2（sgn=−1）：S ∝ M_raw + sgn·ω·Z_raw，曲率 = Σ + 3·sgn·ω（Fox 等 5.1、5.4），ω = √D"""
    a=[1/x for x in T.t];Sg=sum(a)/2;w=Q2(0,sgn)
    S=T.nz([Q2(ai*(Sg-ai))+w*ai for ai in a]);r=1/(Q2(Sg)+3*w)
    return S,r
CHECKS={}
def check(name):
    def deco(f):CHECKS[name]=f;return f
    return deco
@check('定理 1 中心平面：G、O、K、M、Z 共面')
def th1(T):
    r=rank([T.G,T.O,T.K,T.M,T.Z]);return r==3
@check('定理 2 GM 共轭平面：P∈GM，P*、Pᵗ 与 G、M 共面')
def th2(T):
    u=us;P=T.lin((1-u,T.G),(u,T.M));Ps=T.nz([T.S2[i]/P[i] for i in range(4)]);Pt=T.nz([1/P[i] for i in range(4)])
    return T.coplanar4([T.G,T.M,Ps,Pt])==0
@check('定理 4 四点共圆：λ(K′)=λ(G′)（含中心平面）')
def th4(T):
    Kp=inv(T,T.K,T.M,T.rho2)
    # K′−O = α(M−O)+β(G−O)：在重心坐标里解（K′ 在中心平面上 ⇒ 可解）
    rows=[[T.M[i]-T.O[i],T.G[i]-T.O[i]] for i in range(4)];rhs=[Kp[i]-T.O[i] for i in range(4)]
    # 用前两行解，再检第三、四行
    for i0,i1 in itertools.combinations(range(4),2):
        a,b,c,d=rows[i0][0],rows[i0][1],rows[i1][0],rows[i1][1];D=a*d-b*c
        if D!=0:break
    al=(rhs[i0]*d-b*rhs[i1])/D;be=(a*rhs[i1]-c*rhs[i0])/D
    ok_plane=all(rows[i][0]*al+rows[i][1]*be==rhs[i] for i in range(4))
    lhs=T.dist2(Kp,T.O)-T.R2;rhs2=be*(T.R2-T.dist2(T.G,T.O))
    return ok_plane and lhs==rhs2
@check('定理 5 五点球（T12、两条连线中点、两面 Feuerbach 点）')
def th5(T):
    P=[T.Te[(1,2)],TeOpp(T,0),TeOpp(T,1),face(T,(0,1,2))[1],face(T,(1,2,3))[1]];return T.cospherical(P)==0
@check('定理 6 五点球（V1、面 012 内心、T13、T01T23 中点、面 013 Feuerbach 点）')
def th6(T):
    P=[T.V(1),face(T,(0,1,2))[0],T.Te[(1,3)],TeOpp(T,0),face(T,(0,1,3))[1]];return T.cospherical(P)==0
@check('定理 7 五点球（棱 02 两侧面内心、m02、m02 到 V1V3 的垂足、T13）')
def th7(T):
    m=mid(T,T.V(0),T.V(2));P=[face(T,(0,1,2))[0],face(T,(0,2,3))[0],m,foot(T,m,T.V(1),T.V(3)),T.Te[(1,3)]];return T.cospherical(P)==0
@check('定理 8 引理 D：E_kl 在 Γ_p 平面上，且 Γ_p 与任一对反相似切点共球（6 种情形）')
def th8(T):
    for p in range(3):
        q,r=[x for x in range(3) if x!=p];G3=[T.Z,TeOpp(T,q),TeOpp(T,r)]
        for (k,l) in PAIRS[p]:
            tk,tl=T.t[k],T.t[l]
            if tk==tl:continue
            E=T.lin((tl/(tl-tk),T.V(k)),(-tk/(tl-tk),T.V(l)))
            if T.coplanar4(G3+[E])!=0:return False
            i=[x for x in range(4) if x not in (k,l)][0]       # Σ_i 与 Σ_k、Σ_l 都外切：切点 T_ki、T_li 是一对反相似点
            if T.cospherical(G3+[T.Te[tuple(sorted((k,i)))],T.Te[tuple(sorted((l,i)))]])!=0:return False
    return True
@check('定理 9 引理 B (b)：μ 在 T_ij 的切平面、Π_Z、T_ijT_kl 中垂面三面共线')
def th9(T):
    for (a,b),(c,d) in PAIRS:
        for (e1,e2) in (((a,b),(c,d)),((c,d),(a,b))):
            Tij,Tkl=T.Te[e1],T.Te[e2]
            # 三张平面写成仿射函数，在四个顶点上取值
            f1=[T.dot(T.V(v),Tij,Tij,T.M) for v in range(4)]                     # (X−T_ij)·(T_ij−M)=0
            f2=[T.dot(T.V(v),T.M,T.Z,T.M)-T.rho2 for v in range(4)]              # (X−M)·(Z−M)=ρ²
            md=mid(T,Tij,Tkl);f3=[T.dot(T.V(v),md,Tkl,Tij) for v in range(4)]    # (X−中点)·(T_kl−T_ij)=0
            if rank([f1,f2,f3])!=2:return False
    return True
@check('定理 3 八点球（二次扩域，两个 Soddy 球）')
def th3(T):
    S1,r1=soddy(T,1);S2,r2=soddy(T,-1);t=T.t
    def con(S,r,i):return T.lin((r/(t[i]+r),T.Vq(i)),(t[i]/(t[i]+r),S))
    # 注意：四个棱切点本身共圆，「共圆四点 + 任一点」恒共球，所以要用 3 个切点 + s1_1 定球，再逐个检验其余各点
    base=[T.Te[(0,1)],T.Te[(0,2)],T.Te[(1,3)]];s11=con(S1,r1,1)
    rest=[T.Te[(2,3)],con(S1,r1,2),con(S2,r2,0),con(S2,r2,3)]
    if Z0(T.coplanar4(base+[s11])):return '定球的四点共面'
    return all(Z0(T.cospherical(base+[s11,x])) for x in rest)
@check('定理 10 Soddy 五点球（二次扩域，两个 Soddy 球，3 个对棱对 × 2 条棱）')
def th10(T):
    t=T.t
    for sg in (1,-1):
        S,r=soddy(T,sg)
        # 先核对：S 到每个顶点的距离 = t_i + r（Soddy 球构造正确）
        for i in range(4):
            if not Z0(T.dist2(S,T.Vq(i))-(t[i]+r)*(t[i]+r)):return 'Soddy 构造不对'
        Mi=inv(T,T.M,S,r*r)
        for p in range(3):
            for (k,l) in PAIRS[p]:
                cp=[T.lin((r/(t[i]+r),T.Vq(i)),(t[i]/(t[i]+r),S)) for i in (k,l)]
                if not Z0(T.cospherical([T.Z,TeOpp(T,p)]+cp+[Mi])):return False
    return True
if __name__=='__main__':
    want=sys.argv[1:]
    t=[Fr(1),t1s,t2s,t3s];a=[1/x for x in t]
    Q2.D=((sum(a,Fr(0)))**2-2*sum((x*x for x in a),Fr(0)))/12
    for k,f in CHECKS.items():
        num=k.split()[1]
        if want and num not in want:continue
        T=setup(t)
        if k.startswith(('定理 3','定理 10')):lift(T)
        t0=time.time();ok=f(T)
        print('%-70s %s   用时 %.1fs'%(k,'恒等成立' if ok is True else '不成立：'+str(ok),time.time()-t0),flush=True)
