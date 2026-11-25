# 按 Mathlib 与 Defs.lean 的定义，在笛卡儿坐标里逐字计算，数值检验 Midsphere/Statement.lean 的陈述。
# 不使用论文的重心坐标公式（Soddy 球直接解方程组，内心按 Mathlib 的权重 1/高，九点圆按 Mathlib 的定义）。
from mpmath import mp, mpf, matrix, sqrt, lu_solve, norm as mnorm
import random, itertools
mp.dps = 40
def vec(*a): return matrix([mpf(x) for x in a])
def dot(a, b): return sum(a[i]*b[i] for i in range(len(a)))
def nrm(a): return sqrt(dot(a, a))
def tet(r):
    """顶点满足 |ViVj| = ri + rj"""
    e = lambda i, j: (r[i]+r[j])**2
    V0 = vec(0, 0, 0); V1 = vec(r[0]+r[1], 0, 0)
    x2 = (e(0, 2)-e(1, 2)+e(0, 1))/(2*(r[0]+r[1])); V2 = vec(x2, sqrt(e(0, 2)-x2**2), 0)
    x3 = (e(0, 3)-e(1, 3)+e(0, 1))/(2*(r[0]+r[1]))
    y3 = (e(0, 3)-e(2, 3)+dot(V2, V2)-2*x3*V2[0])/(2*V2[1])
    return [V0, V1, V2, vec(x3, y3, sqrt(e(0, 3)-x3**2-y3**2))]
def bary(V, X):
    A = matrix(4, 4)
    for j in range(4):
        for k in range(3): A[k, j] = V[j][k]
        A[3, j] = 1
    return lu_solve(A, matrix([X[0], X[1], X[2], 1]))
def ofW(V, w): S = sum(w); return sum([(w[i]/S)*V[i] for i in range(4)], vec(0, 0, 0))
def lineMap(a, b, c): return a + c*(b-a)
def circum(P):  # 3 维中 4 点的外心
    A = matrix(3, 3); b = matrix(3, 1)
    for k in range(3):
        for c in range(3): A[k, c] = 2*(P[k+1][c]-P[0][c])
        b[k] = dot(P[k+1], P[k+1])-dot(P[0], P[0])
    return lu_solve(A, b)
def circum_tri(P):  # 三角形外心（在其平面内）
    a, b = P[1]-P[0], P[2]-P[0]
    M = matrix([[dot(a, a), dot(a, b)], [dot(a, b), dot(b, b)]]); s = lu_solve(M, matrix([dot(a, a)/2, dot(b, b)/2]))
    return P[0]+s[0]*a+s[1]*b
def S2(V, i):
    F = [V[j] for j in range(4) if j != i]; u, w = F[1]-F[0], F[2]-F[0]
    return (dot(u, u)*dot(w, w)-dot(u, w)**2)/4
def isog(V, P): x = bary(V, P); return ofW(V, [S2(V, i)/x[i] for i in range(4)])
def isot(V, P): x = bary(V, P); return ofW(V, [1/x[i] for i in range(4)])
def inversion(c, R, x): return c + (R**2/dot(x-c, x-c))*(x-c)
def proj_line(a, b, x): d = b-a; return a + (dot(x-a, d)/dot(d, d))*d
# 几何关系的数值判据（返回「误差」，0 表示成立）
def rank_err(rows, k):  # 行向量组秩 ≤ k 的程度：第 k+1 个奇异值 / 最大奇异值
    import mpmath
    A = matrix(rows); s = mpmath.svd_r(A, compute_uv=False)
    s = sorted([abs(x) for x in s], reverse=True)
    return float(s[k]/s[0]) if len(s) > k else 0.0
def coplanar(P): return rank_err([[p[0]-P[0][0], p[1]-P[0][1], p[2]-P[0][2]] for p in P[1:]], 2)
def collinear(P): return rank_err([[p[0]-P[0][0], p[1]-P[0][1], p[2]-P[0][2]] for p in P[1:]], 1)
def mcosph(P): return rank_err([[dot(p, p), p[0], p[1], p[2], 1] for p in P], 4)  # 球或平面
def cosph_proper(P):  # 真正的球（不共面）：返回 (误差, 共面误差)
    return mcosph(P), coplanar(P)
def soddy(V, r):
    """解 |S − Vi|² = (ρ + ri)²：S 关于 ρ 线性，代回 i = 0 得 ρ 的二次方程"""
    A = matrix(3, 3); b0 = matrix(3, 1); b1 = matrix(3, 1)
    for k in range(3):
        i = k+1
        for c in range(3): A[k, c] = 2*(V[i][c]-V[0][c])
        b0[k] = dot(V[i], V[i])-dot(V[0], V[0])-(r[i]**2-r[0]**2); b1[k] = -2*(r[i]-r[0])
    s0 = lu_solve(A, b0); s1 = lu_solve(A, b1)   # S = s0 + ρ s1
    d0 = s0-V[0]; qa = dot(s1, s1)-1; qb = 2*dot(d0, s1)-2*r[0]; qc = dot(d0, d0)-r[0]**2
    disc = qb**2-4*qa*qc
    out = []
    for sg in (1, -1):
        rho = (-qb+sg*sqrt(disc))/(2*qa); out.append((s0+rho*s1, rho))
    return out
class Conf:
    def __init__(s, r, bad=None):
        s.r = r; V = s.V = tet(r); s.bad = bad
        s.G = sum(V, vec(0, 0, 0))/4; s.O = circum(V); s.R = nrm(V[0]-s.O)
        s.sInv = sum(1/x for x in r)
        s.Z = ofW(V, [1/x for x in r]); s.M = ofW(V, [s.sInv/(2*x)-1/x**2 for x in r])
        s.K = ofW(V, [S2(V, i) for i in range(4)])
        s.So = soddy(V, r)
    def T(s, i, j): r = s.r; return lineMap(s.V[i], s.V[j], r[i]/(r[i]+r[j]))
    def rho(s): return nrm(s.M-s.T(0, 1))
    def N(s, i, j, k, l): return (s.T(i, j)+s.T(k, l))/2
    def face(s, l): return [s.V[j] for j in range(4) if j != l]   # faceOpposite（顶点按下标升序）
    def Ipt(s, l):  # Mathlib incenter：权重 1/高（∝ 对边长）
        F = s.face(l); a = [nrm(F[1]-F[2]), nrm(F[0]-F[2]), nrm(F[0]-F[1])]
        return sum([a[k]*F[k] for k in range(3)], vec(0, 0, 0))/sum(a)
    def inradius(s, l):
        F = s.face(l); a, b, c = nrm(F[1]-F[2]), nrm(F[0]-F[2]), nrm(F[0]-F[1]); sp = (a+b+c)/2
        return sqrt((sp-a)*(sp-b)*(sp-c)/sp)
    def X11(s, l):
        r = s.r; St = sum(r); P = r[0]*r[1]*r[2]*r[3]
        w = [0 if i == l else r[i]*(St-r[l]-r[i])**2-4*P/r[l] for i in range(4)]
        if s.bad == 'X11 用 rᵢ(rₖ+rₘ)²': w = [0 if i == l else r[i]*(St-r[l]-r[i])**2 for i in range(4)]
        return ofW(s.V, w)
    def npc(s, l):  # Mathlib ninePointCircle（三角形）：球心 = 外心 + (3/2)(重心 − 外心)，半径 = R/2
        F = s.face(l); Oc = circum_tri(F); Gc = sum(F, vec(0, 0, 0))/3
        return Oc+mpf(3)/2*(Gc-Oc), nrm(F[0]-Oc)/2
    def sp(s, S, rho, i): r = s.r; return lineMap(s.V[i], S, r[i]/(r[i]+rho))
def run(r, bad=None):
    c = Conf(r, bad); V = c.V; out = {}
    # 忠实性
    out['T 距离'] = max(float(abs(nrm(V[i]-c.T(i, j))-r[i])) for i in range(4) for j in range(4) if i != j)
    out['M 切于棱'] = max(max(float(abs(nrm(c.T(i, j)-c.M)-c.rho())), float(abs(dot(c.T(i, j)-c.M, V[j]-V[i]))))
                         for i in range(4) for j in range(4) if i != j)
    out['Z 在连线上'] = max(collinear([c.Z, c.T(a, b), c.T(cc, d)]) for (a, b), (cc, d) in [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))])
    out['K=G*'] = float(nrm(c.K-isog(V, c.G)))
    out['Heron'] = max(float(abs(S2(V, i)-(sum(r)-r[i])*r[0]*r[1]*r[2]*r[3]/r[i])) for i in range(4))
    e = 0
    for l in range(4):
        Nc, Nr = c.npc(l); X = c.X11(l)
        e = max(e, float(abs(nrm(X-Nc)-Nr)), float(abs(nrm(X-c.Ipt(l))-c.inradius(l))))
    out['X11 在九点圆与内切圆上'] = e
    out['Soddy 两解'] = max(float(abs(nrm(S-V[i])**2-(rho+r[i])**2)) for S, rho in c.So for i in range(4))
    (S1, r1), (S2s, r2) = c.So
    # 定理 1
    base = [c.G, c.O, c.K, c.M, c.Z]
    out['定理1'] = max(coplanar(base), coplanar(base+[S1]), coplanar(base+[S2s]))
    # 定理 2
    e = 0
    for u in (mpf('0.3'), mpf('-1.4'), mpf('2.2')):
        P = c.G+u*(c.M-c.G); e = max(e, coplanar([c.G, c.M, isog(V, P), isot(V, P)]))
    out['定理2'] = e
    # 定理 3（两种指派）
    e = 0
    for (A, ra), (B, rb) in (((S1, r1), (S2s, r2)), ((S2s, r2), (S1, r1))):
        P8 = [c.T(0, 1), c.T(0, 2), c.T(1, 3), c.T(2, 3), c.sp(A, ra, 1), c.sp(A, ra, 2), c.sp(B, rb, 0), c.sp(B, rb, 3)]
        if bad == '八点球用 σ₁ 四个切点': P8 = P8[:6]+[c.sp(A, ra, 0), c.sp(A, ra, 3)]
        e = max(e, mcosph(P8))
    out['定理3'] = e
    # 定理 4
    u = (c.M-c.O)/nrm(c.M-c.O); A = c.O+c.R*u; B = c.O-c.R*u
    Kp = inversion(c.M, c.rho(), c.K); Gp = inversion(c.O, c.R, c.G); G2 = 2*c.O-c.G
    if bad == 'K′ 关于外接球反演': Kp = inversion(c.O, c.R, c.K)
    P5 = [Kp, Gp, A, B, G2]
    out['定理4 共圆'] = max(rank_err([[dot(p, p), p[0], p[1], p[2], 1] for p in P5], 3), coplanar(P5))
    out['定理4 中心平面'] = coplanar(base+P5)
    # 定理 5–7
    P5a = [c.T(1, 2), c.N(0, 1, 2, 3), c.N(0, 2, 1, 3), c.X11(3), c.X11(0)]
    P6a = [V[1], c.Ipt(3), c.T(1, 3), c.N(0, 1, 2, 3), c.X11(2)]
    m02 = (V[0]+V[2])/2
    P7a = [c.Ipt(3), c.Ipt(1), m02, proj_line(V[1], V[3], m02), c.T(1, 3)]
    out['定理5'] = mcosph(P5a); out['定理6'] = mcosph(P6a); out['定理7'] = mcosph(P7a)
    out['min 不共面度(3,5,6,7,10)'] = min(coplanar(P5a), coplanar(P6a), coplanar(P7a),
        min(coplanar([c.T(0, 1), c.T(0, 2), c.T(1, 3), c.T(2, 3), c.sp(S1, r1, 1)]), 1.0),
        coplanar([c.Z, c.N(0, 1, 2, 3), c.sp(S1, r1, 2), c.sp(S1, r1, 3), inversion(S1, abs(r1), c.M)]))
    # 定理 8：全部 (i,j,k,l)
    e = 0
    for (i, j), (k, l) in [((0, 1), (2, 3)), ((2, 3), (0, 1)), ((0, 2), (1, 3)), ((1, 3), (0, 2)), ((0, 3), (1, 2)), ((1, 2), (0, 3))]:
        for (kk, ll) in ((k, l), (l, k)):
            Zs, N1, N2 = c.Z, c.N(i, kk, j, ll), c.N(i, ll, j, kk); Cc = circum_tri([Zs, N1, N2]); Rc = nrm(Zs-Cc)
            E = lineMap(V[kk], V[ll], -r[kk]/(r[ll]-r[kk]))
            e = max(e, coplanar([Zs, N1, N2, E]), float(abs((dot(E-Cc, E-Cc)-Rc**2)-r[ll]/r[kk]*(dot(E-V[kk], E-V[kk])-r[kk]**2))))
    out['定理8'] = e
    D = (c.sInv**2-2*sum(1/x**2 for x in r))/12
    out['Soddy 曲率'] = max(min(float(abs(1/rho-(c.sInv/2+3*sqrt(D)))), float(abs(1/rho-(c.sInv/2-3*sqrt(D))))) for S, rho in c.So)
    # 定理 9：过 Tij 且与两个 Soddy 球正交的球，球心 X 满足两个线性方程，取直线上的几个点
    e = 0
    for (i, j), (k, l) in [((0, 1), (2, 3)), ((2, 3), (0, 1)), ((0, 2), (1, 3)), ((1, 2), (0, 3))]:
        Tij = c.T(i, j)
        # |X − Sm|² − |X − Tij|² = ρm²  ⇒ 2⟪X, Tij − Sm⟫ = ρm² + |Tij|² − |Sm|²
        n1, n2 = Tij-S1, Tij-S2s; b1 = (r1**2+dot(Tij, Tij)-dot(S1, S1))/2; b2 = (r2**2+dot(Tij, Tij)-dot(S2s, S2s))/2
        dirv = matrix([n1[1]*n2[2]-n1[2]*n2[1], n1[2]*n2[0]-n1[0]*n2[2], n1[0]*n2[1]-n1[1]*n2[0]])
        A2 = matrix([[n1[0], n1[1], n1[2]], [n2[0], n2[1], n2[2]], [dirv[0], dirv[1], dirv[2]]])
        X0 = lu_solve(A2, matrix([b1, b2, 0]))
        for lam in (mpf(0), mpf('1.7'), mpf('-2.3')):
            X = X0+lam*dirv; rad2 = dot(X-Tij, X-Tij)
            e = max(e, float(abs(dot(X-c.T(k, l), X-c.T(k, l))-rad2)/rad2))
    out['定理9'] = e
    # 定理 10
    e = 0
    for S, rho in c.So:
        Mi = inversion(S, abs(rho), c.M)
        for (i, j), (k, l) in [((0, 1), (2, 3)), ((2, 3), (0, 1)), ((0, 2), (1, 3)), ((1, 3), (0, 2)), ((0, 3), (1, 2)), ((1, 2), (0, 3))]:
            e = max(e, mcosph([c.Z, c.N(i, j, k, l), c.sp(S, rho, k), c.sp(S, rho, l), Mi]))
    out['定理10'] = e
    # 定理 11：Weiszfeld 求 Fermat 点
    F = c.G
    for _ in range(4000):
        w = [1/nrm(V[i]-F) for i in range(4)]; F = sum([w[i]*V[i] for i in range(4)], vec(0, 0, 0))/sum(w)
    out['定理11'] = collinear([F, isog(V, F), c.M])
    return out
if __name__ == '__main__':
    random.seed(7)
    for trial in range(3):
        r = [mpf(random.uniform(0.4, 2.5)) for _ in range(4)]
        o = run(r); print('切长', [round(float(x), 3) for x in r])
        for k, v in o.items(): print('   %-24s %.1e' % (k, v))
    print('\n--- 故意写错 ---')
    r = [mpf(x) for x in (0.7, 1.3, 1.9, 1.1)]
    for bad, key in (('X11 用 rᵢ(rₖ+rₘ)²', 'X11 在九点圆与内切圆上'), ('X11 用 rᵢ(rₖ+rₘ)²', '定理5'),
                     ('八点球用 σ₁ 四个切点', '定理3'), ('K′ 关于外接球反演', '定理4 共圆')):
        print('%-22s → %-22s %.1e' % (bad, key, run(r, bad)[key]))
