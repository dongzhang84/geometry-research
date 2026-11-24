# 按 Mathlib / Defs.lean 的定义逐字计算，数值检验 Orthocentric/Statement.lean 的陈述
from mpmath import mp, matrix, mpf, sqrt, lu_solve, eigsy, acos, sin
import random, itertools
mp.dps=40
dot=lambda a,b: sum(a[i]*b[i] for i in range(3)); norm=lambda a: sqrt(dot(a,a))
def vec(*a): return matrix([mpf(x) for x in a])
def cross(a,b): return vec(a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def ortho_tet(a):            # 论文的代数模型：H 在原点，⟪vᵢ,vⱼ⟫ = p + aᵢδᵢⱼ
    a=[mpf(x) for x in a]; p=-1/sum(1/x for x in a)
    Gm=matrix(4,4)
    for i in range(4):
        for j in range(4): Gm[i,j]=p+(a[i] if i==j else 0)
    E,Q=eigsy(Gm); idx=sorted(range(4),key=lambda k:-E[k])[:3]
    V=[vec(*[Q[i,k]*sqrt(max(E[k],0)) for k in idx]) for i in range(4)]
    # 随机平移旋转，避免 H 恰在原点带来的巧合
    sh=vec(0.37,-0.21,0.53); return [v+sh for v in V]
def circum_tet(P):
    A=matrix(3,3);b=matrix(3,1)
    for k in range(1,4):
        for j in range(3): A[k-1,j]=2*(P[k][j]-P[0][j])
        b[k-1]=dot(P[k],P[k])-dot(P[0],P[0])
    return lu_solve(A,b)
def plane_proj(x,P):
    u=P[1]-P[0]; w=P[2]-P[0]; d=x-P[0]
    A=matrix([[dot(u,u),dot(u,w)],[dot(u,w),dot(w,w)]]); s=lu_solve(A,matrix([dot(d,u),dot(d,w)])); return P[0]+s[0]*u+s[1]*w
def circum_tri(P):
    u=P[1]-P[0]; w=P[2]-P[0]; A=matrix([[dot(u,u),dot(u,w)],[dot(u,w),dot(w,w)]]); s=lu_solve(A,matrix([dot(u,u)/2,dot(w,w)/2])); return P[0]+s[0]*u+s[1]*w
def sphere4(P):
    A=matrix(3,3);b=matrix(3,1)
    for k in range(1,4):
        for j in range(3): A[k-1,j]=2*(P[k][j]-P[0][j])
        b[k-1]=dot(P[k],P[k])-dot(P[0],P[0])
    c=lu_solve(A,b); return c,norm(P[0]-c)
secondInter=lambda c,p,v: (-2*dot(v,p-c)/dot(v,v))*v+p
homothety=lambda c,r,x: r*(x-c)+c
mid=lambda x,y:(x+y)/2
class T:
    def __init__(s,V,bad=None):
        s.V=V; s.bad=bad
        s.O=circum_tet(V); s.R=norm(V[0]-s.O); s.G=(V[0]+V[1]+V[2]+V[3])/4
        s.H=2*(s.G-s.O)+s.O                                        # mongePoint, n = 3
        s.face=lambda i:[V[j] for j in range(4) if j!=i]           # faceOpposite i（顶点按下标升序）
        s.Hf=lambda i: plane_proj(V[i],s.face(i))                  # altitudeFoot
        s.p=dot(V[0]-s.H,V[1]-s.H)
        s.a=lambda i: dot(s.H-V[i],s.Hf(i)-V[i])
        s.Gf=lambda i: sum(s.face(i),vec(0,0,0))/3                  # faceOppositeCentroid
    def psi(s,X): return s.H+(s.p/dot(X-s.H,X-s.H))*(X-s.H)
    def S2(s,i):
        F=s.face(i); u=F[1]-F[0]; w=F[2]-F[0]; return (dot(u,u)*dot(w,w)-dot(u,w)**2)/4
    def bary(s,X):
        M=matrix(4,4)
        for j in range(4):
            for k in range(3): M[k,j]=s.V[j][k]
            M[3,j]=1
        return lu_solve(M,matrix([X[0],X[1],X[2],1]))
    def ofW(s,w):
        S=sum(w); return sum([(w[i]/S)*s.V[i] for i in range(4)],vec(0,0,0))
    def isog(s,P):
        x=s.bary(P); w=[s.S2(i)/x[i] for i in range(4)]
        if s.bad=='isog 用 S2(i+1)': w=[s.S2((i+1)%4)/x[i] for i in range(4)]
        return s.ofW(w)
    def isot(s,P): x=s.bary(P); return s.ofW([1/x[i] for i in range(4)])
coll=lambda P: float(norm(cross(P[1]-P[0],P[2]-P[0]))/max(norm(P[1]-P[0]),norm(P[2]-P[0]))**2)
copl=lambda P: float(abs(dot(P[1]-P[0],cross(P[2]-P[0],P[3]-P[0]))))
def online(X,A,B): return coll([A,B,X])
def run(V,bad=None,verbose=True):
    t=T(V,bad); out={}
    # 忠实性
    out['H 在高上']=max(float(abs(dot(t.H-V[i],t.face(i)[k]-t.face(i)[0]))) for i in range(4) for k in (1,2))
    out['⟪Vᵢ−H,Vⱼ−H⟫=p']=max(float(abs(dot(V[i]-t.H,V[j]-t.H)-t.p)) for i in range(4) for j in range(4) if i!=j)
    out['a=|HV|²−p']=max(float(abs(t.a(i)-(dot(V[i]-t.H,V[i]-t.H)-t.p))) for i in range(4))
    out['ψ(Vᵢ)=Hᵢ']=max(float(norm(t.psi(V[i])-t.Hf(i))) for i in range(4))
    w=[mpf(1.3),mpf(-0.4),mpf(2.2),mpf(0.7)]; out['bary∘ofWeights']=float(max(abs(t.bary(t.ofW(w))[i]-w[i]/sum(w)) for i in range(4)))
    def S2ang(i):                                                   # (½·|PQ|·|PR|·sin∠QPR)²
        F=t.face(i); u=F[1]-F[0]; w=F[2]-F[0]; th=acos(dot(u,w)/(norm(u)*norm(w)))
        return (norm(u)*norm(w)*sin(th)/2)**2
    out['S2 = 面积²']=max(float(abs(t.S2(i)-S2ang(i))) for i in range(4))
    rM=norm(mid(V[0],V[1])-t.G)
    out['棱中点到 G 等距']=max(float(abs(norm(mid(V[i],V[j])-t.G)-rM)) for i in range(4) for j in range(4) if i!=j)
    # 定理 1
    e1=0
    for i in range(4):
        F=t.face(i); Of=circum_tri(F); Gf=sum(F,vec(0,0,0))/3
        Nc=mpf(3)/2*(Gf-Of)+Of; Nr=norm(F[0]-Of)/2                 # ninePointCircle（三角形）
        m3=[mid(F[0],F[1]),mid(F[0],F[2]),mid(F[1],F[2])]
        assert max(abs(norm(m-Nc)-Nr) for m in m3)<1e-30          # 中点在九点圆上
        c,r=sphere4([V[i]]+m3)
        X=homothety(t.O,-1,V[i]); Y=secondInter(t.O,V[i],t.H-V[i])
        if bad=='X 用 +1 位似': X=homothety(t.O,1,V[i])
        pts=[t.psi(t.Gf(i)),mid(t.H,X),mid(t.H,Y)]
        e1=max(e1,max(float(abs(norm(q-c)-r)) for q in pts), float(abs(dot(t.H-c,t.H-c)-r*r-mpf(3)/2*t.p)))
    out['定理1 十三点球']=e1
    # 定理 2
    e2=0
    for lam in (mpf(0.3),mpf(-1.7),mpf(2.4)):
        P=t.O+lam*(t.H-t.O); e2=max(e2,copl([t.O,t.H,t.isog(P),t.isot(P)])/float(norm(t.H-t.O))**3)
    out['定理2 共面']=e2
    # 定理 3
    Os=t.isog(t.O); e3=0
    for lam in (mpf(0),mpf(0.4),mpf(-1.3),mpf(2.1)):
        P=t.O+lam*(Os-t.O); e3=max(e3,coll([t.O,t.isog(P),t.isot(P)]))
    out['定理3 共线']=e3
    # 定理 4
    g2=dot(t.H-t.G,t.H-t.G); lam=(4*g2-t.R**2)/(2*g2+t.R**2); X=t.H+lam*(t.G-t.H)
    powO=dot(X-t.O,X-t.O)-t.R**2; r2=dot(mid(V[0],V[1])-t.G,mid(V[0],V[1])-t.G); powM=dot(X-t.G,X-t.G)-r2
    e4=0
    for i in range(4):
        A=t.psi(t.Gf(i)); B=secondInter(t.O,V[i],t.G-V[i])
        e4=max(e4,online(X,A,B),float(abs(dot(A-X,B-X)-powO)))
        out.setdefault('min|AᵢBᵢ|',1e9); out['min|AᵢBᵢ|']=min(out['min|AᵢBᵢ|'],float(norm(A-B)))
    for (i,j,k,l) in itertools.permutations(range(4)):
        A=t.psi(mid(V[i],V[j])); B=t.psi(mid(V[k],V[l]))
        e4=max(e4,online(X,A,B),float(abs(dot(A-X,B-X)-powM)))
        out.setdefault('min|ψ(mᵢⱼ)ψ(mₖₗ)|',1e9); out['min|ψ(mᵢⱼ)ψ(mₖₗ)|']=min(out['min|ψ(mᵢⱼ)ψ(mₖₗ)|'],float(norm(A-B)))
    out['定理4 七线共点']=e4
    out['min|GᵢH|, min|mᵢⱼH|']=float(min([norm(t.Gf(i)-t.H) for i in range(4)]+[norm(mid(V[i],V[j])-t.H) for i in range(4) for j in range(i+1,4)]))
    # 定理 5：Weiszfeld 求 Fermat 点
    Fp=t.G
    for _ in range(3000):
        wts=[1/norm(V[i]-Fp) for i in range(4)]; Fp=sum([wts[i]*V[i] for i in range(4)],vec(0,0,0))/sum(wts)
    d=[norm(Fp-V[i]) for i in range(4)]
    W=t.ofW([t.a(i)/d[i]**2 for i in range(4)])
    out['定理5 F,O,W 共线']=coll([Fp,t.O,W])
    return out
random.seed(3)
for trial in range(3):
    a=[random.uniform(0.5,3) for _ in range(4)]
    o=run(ortho_tet(a))
    print('四面体',trial,'a =',[round(x,2) for x in a]); [print('   %-18s %.1e'%(k,v)) for k,v in o.items()]
print('\n--- 一个 aᵢ 为负（H 在外部）---')
for a in ([-0.4,1.5,2.0,1.2],[1.1,-0.3,0.9,2.5]):
    try:
        o=run(ortho_tet(a)); print('a =',a,' 最大误差 %.1e'%max(v for k,v in o.items() if not k.startswith('min')), ' 最小间距 %.2f'%min(v for k,v in o.items() if k.startswith('min')))
    except Exception as e: print('a =',a,'构造失败',e)
print('\n--- 故意写错定义 ---')
V=ortho_tet([1.09,1.86,1.42,2.01])
for bad,key in (('isog 用 S2(i+1)','定理2 共面'),('isog 用 S2(i+1)','定理3 共线'),('X 用 +1 位似','定理1 十三点球')):
    print('%-14s → %-10s 误差 %.1e'%(bad,key,run(V,bad)[key]))
print('\n--- 一般（非垂心）四面体 ---')
random.seed(9); Vg=[vec(*[random.uniform(-1,1) for _ in range(3)]) for _ in range(4)]
o=run(Vg)
for k in ('定理1 十三点球','定理2 共面','定理3 共线','定理4 七线共点','定理5 F,O,W 共线'): print('   %-18s %.1e'%(k,o[k]))
