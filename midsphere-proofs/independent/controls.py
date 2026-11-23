# 对照组：每条换掉一个点，应当不成立（确认 exact_check.py 的检验不是恒真的）
import random
from fractions import Fraction as Fr
from exact_check import *
rng=random.Random(7);fails={}
def run(name,f):
    bad=0
    for _ in range(5):
        t=sample(rng);a=[1/x for x in t];D=((sum(a))**2-2*sum(x*x for x in a))/12
        if D<=0:continue
        Q2.D=D;T=setup(t)
        if 'Soddy' in name or '八点' in name:lift(T)
        if f(T):bad+=1
    print('%-55s 对照「成立」次数 %d（应为 0）'%(name,bad))
run('定理 1 对照：K 换成 (S_i) 权重点',lambda T:rank([T.G,T.O,T.nz([Fr(1)/s for s in T.S2]),T.M,T.Z])==3)
run('定理 2 对照：P 取 GO 上的点',lambda T:(lambda P:T.coplanar4([T.G,T.M,T.nz([T.S2[i]/P[i] for i in range(4)]),T.nz([1/P[i] for i in range(4)])])==0)(T.lin((Fr(-4,3),T.G),(Fr(7,3),T.O))))
run('定理 5 对照：Feuerbach 点换成面内心',lambda T:T.cospherical([T.Te[(1,2)],TeOpp(T,0),TeOpp(T,1),face(T,(0,1,2))[0],face(T,(1,2,3))[1]])==0)
run('定理 7 对照：T13 换成 T12',lambda T:(lambda m:T.cospherical([face(T,(0,1,2))[0],face(T,(0,2,3))[0],m,foot(T,m,T.V(1),T.V(3)),T.Te[(1,2)]])==0)(mid(T,T.V(0),T.V(2))))
run('定理 9 对照：T_kl 换成相邻棱的切点',lambda T:rank([[T.dot(T.V(v),T.Te[(0,1)],T.Te[(0,1)],T.M) for v in range(4)],[T.dot(T.V(v),T.M,T.Z,T.M)-T.rho2 for v in range(4)],[T.dot(T.V(v),mid(T,T.Te[(0,1)],T.Te[(0,2)]),T.Te[(0,2)],T.Te[(0,1)]) for v in range(4)]])==2)
def c3(T):
    S1,r1=soddy(T,1);S2,r2=soddy(T,-1);t=T.t;con=lambda S,r,i:T.lin((r/(t[i]+r),T.Vq(i)),(t[i]/(t[i]+r),S))
    base=[T.Te[(0,1)],T.Te[(0,2)],T.Te[(1,3)],con(S1,r1,1)];return Z0(T.cospherical(base+[con(S2,r2,1)]))   # σ2 的切点换到 Σ1 上
run('定理 3 八点 对照：σ2 的切点换到 Σ1 上',c3)
def c10(T):
    S,r=soddy(T,1);t=T.t;Mi=inv(T,T.M,S,r*r);cp=[T.lin((r/(t[i]+r),T.Vq(i)),(t[i]/(t[i]+r),S)) for i in (0,2)]   # 棱 02 不在对棱对 0 里
    return Z0(T.cospherical([T.Z,TeOpp(T,0)]+cp+[Mi]))
run('定理 10 Soddy 对照：棱取错（02 配对棱对 0）',c10)
