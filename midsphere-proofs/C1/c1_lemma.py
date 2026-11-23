# 定理 11 用到的一般四面体引理的符号核对（sympy）：
# 设 F 为 Fermat 点（放在原点），u_i = (V_i − F)/d_i。由 Σu_i = 0 可得对棱张角相等，于是四个单位向量可以取成
#   u0 = (x, y, z), u1 = (x, −y, −z), u2 = (−x, y, −z), u3 = (−x, −y, z)，x² + y² + z² = 1。
# 引理的关键一步：等角共轭点 F*（重心坐标 S_i² d_i）满足 (F* − F)·u_k ∝ 1/d_k − W/4，W = Σ 1/d_i。
# 这里在多项式环里核对：g_k = (Σ_i w_i V_i)·u_k（w_i = S_i² d_i），h_k = 1/d_k − W/4，检验 g_k h_l − g_l h_k ≡ 0（用 z² = 1 − x² − y² 化简）。
import time, sympy as sp
x, y, z = sp.symbols('x y z')
d = sp.symbols('d0:4', positive=True)
U = [sp.Matrix([x, y, z]), sp.Matrix([x, -y, -z]), sp.Matrix([-x, y, -z]), sp.Matrix([-x, -y, z])]
V = [d[i] * U[i] for i in range(4)]
FACES = [(1, 2, 3), (0, 2, 3), (0, 1, 3), (0, 1, 2)]
S2 = [((V[b] - V[a]).cross(V[c] - V[a])).dot((V[b] - V[a]).cross(V[c] - V[a])) / 4 for a, b, c in FACES]
w = [S2[i] * d[i] for i in range(4)]
P = sum((w[i] * V[i] for i in range(4)), sp.zeros(3, 1))          # (Σw)·(F* − F)
g = [P.dot(U[k]) for k in range(4)]
W = sum(1 / di for di in d)
h = [1 / d[k] - W / 4 for k in range(4)]
red = lambda e: sp.expand(sp.expand(e).subs(z**2, 1 - x**2 - y**2))
T = time.time(); bad = 0
for k in range(4):
    for l in range(k + 1, 4):
        r = red(sp.together(g[k] * h[l] - g[l] * h[k]) .as_numer_denom()[0])
        r = sp.expand(r.subs(z**2, 1 - x**2 - y**2))
        print(f'g{k}h{l} − g{l}h{k} =', r); bad += (r != 0)
print('全部恒为 0' if not bad else '有不为 0 的', ' 用时 %.1f s' % (time.time() - T))
