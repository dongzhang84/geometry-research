# C1 的证明证书独立核对（sympy，不依赖 Singular 的 reduce）：
# 检查 A·D·h1 − Σ L_k·g_k 展开后恒为 0，其中 L_k 由 c1_ideal.sing 的 lift 导出到 c1_cert.txt。
import time, sympy as sp
d0,d1,d2,d3,t0,t1,t2,t3=sp.symbols('d0 d1 d2 d3 t0 t1 t2 t3')
E=lambda i,j:(sp.Symbol(f't{i}')+sp.Symbol(f't{j}'))**2
g=[d2*d3*(d0**2+d1**2-E(0,1))-d0*d1*(d2**2+d3**2-E(2,3)),
   d1*d3*(d0**2+d2**2-E(0,2))-d0*d2*(d1**2+d3**2-E(1,3)),
   d1*d2*(d0**2+d3**2-E(0,3))-d0*d3*(d1**2+d2**2-E(1,2)),
   d2*d3*(d0**2+d1**2-E(0,1))+d1*d3*(d0**2+d2**2-E(0,2))+d1*d2*(d0**2+d3**2-E(0,3))+2*d0*d1*d2*d3]
h1=sp.Matrix([[1,d0,d0**2-t0**2],[1,d1,d1**2-t1**2],[1,d2,d2**2-t2**2]]).det()
A=t1*t2*t3*d0+t0*t2*t3*d1+t0*t1*t3*d2+t0*t1*t2*d3
D=d0*d1*d2*d3
T=time.time()
L=[sp.sympify(s.replace('^','**'),locals={str(v):v for v in (d0,d1,d2,d3,t0,t1,t2,t3)}) for s in open('c1_cert.txt').read().strip().split(';')]
r=sp.expand(A*D*h1-sum(L[k]*g[k] for k in range(4)))
print('残差 =',r,' 用时 %.1f s'%(time.time()-T))
