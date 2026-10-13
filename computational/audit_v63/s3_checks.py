"""Checks for Section 3 of BTP_PBF v62 (exact where possible, mpmath otherwise)."""
from fractions import Fraction as F
from itertools import permutations, combinations_with_replacement
from math import comb, factorial
import random
import mpmath as mp
import sympy as sp

random.seed(13)
mp.mp.dps = 30
ok = lambda cond, msg: print(("OK   " if cond else "FAIL ") + msg)

# -------- generic helpers --------
def eye(N):
    return [[F(int(i == j)) for j in range(N)] for i in range(N)]

def mm(A, B):
    n, k, m = len(A), len(B), len(B[0])
    return [[sum((A[i][t] * B[t][j] for t in range(k) if A[i][t] and B[t][j]), F(0)) for j in range(m)] for i in range(n)]

def chain(Ms):
    P = Ms[0]
    for M in Ms[1:]:
        P = mm(P, M)
    return P

def lower_mat(l, N):
    M = eye(N)
    for n in range(1, N):
        M[n][n - 1] = l[n]
    return M

def upper_mat(d, s, N):
    M = [[F(0)] * N for _ in range(N)]
    for n in range(N):
        M[n][n] = d[n]
        if n + 1 < N:
            M[n][n + 1] = s[n]
    return M

def inv_tri(M, lower=True):
    N = len(M)
    X = [[F(0)] * N for _ in range(N)]
    if lower:
        for c in range(N):
            for r in range(c, N):
                X[r][c] = (F(int(r == c)) - sum((M[r][k] * X[k][c] for k in range(c, r)), F(0))) / M[r][r]
    else:
        Xt = inv_tri([list(col) for col in zip(*M)], True)
        X = [list(col) for col in zip(*Xt)]
    return X

def hcomp(ell, X):
    """complete homogeneous symmetric polynomial h_ell of list X"""
    if ell < 0:
        return 0
    if ell == 0:
        return 1
    tot = 0
    for c in combinations_with_replacement(range(len(X)), ell):
        pr = 1
        for i in c:
            pr = pr * X[i]
        tot = tot + pr
    return tot

def exchange(U, Lw):
    """U=(u,v) upper bidiagonal, Lw = l (lower unit). returns (L', U') with UL=L'U'."""
    u, v = U
    l = Lw
    M = min(len(u), len(l))
    d = [None] * (M - 1)
    d[0] = u[0] + v[0] * l[1]
    for n in range(1, M - 1):
        d[n] = u[n] + v[n] * l[n + 1] - u[n] * l[n] * v[n - 1] / d[n - 1]
    lp = [F(0)] + [u[n] * l[n] / d[n - 1] for n in range(1, M)]
    return lp, (d, v[:M - 1])

def ordered_root_pbf(omega, eta, xi, M=40):
    q, p = len(eta), len(xi)
    fac = [('U', ([F(e)] * M, [F(1)] * M)) for e in eta] + [('L', [F(0)] + [F(x)] * (M - 1)) for x in xi]
    for j in range(p):
        pos = q + j  # position of the j-th lower factor (after j lowers already moved)
        # move left across q upper factors
        for _ in range(q):
            Uf = fac[pos - 1][1]
            Lf = fac[pos][1]
            lp, up = exchange(Uf, Lf)
            fac[pos - 1] = ('L', lp)
            fac[pos] = ('U', up)
            pos -= 1
    Ls = [f[1] for f in fac[:p]]
    Us = [f[1] for f in fac[p:]]
    # diagonal normalization right to left
    Mlen = min(len(f[0]) for f in Us) - 1
    E = [F(1)] * (Mlen + 1)
    hats = [None] * q
    for idx in range(q - 1, -1, -1):
        d, v = Us[idx]
        sup = [v[n] * E[n + 1] / (E[n] * d[n]) for n in range(Mlen)]
        hats[idx] = sup
        E = [E[n] * d[n] for n in range(Mlen + 1)]
    D = [omega * e for e in E]
    # paper labels: U_i = hats[q-i] (U_1 rightmost)
    Upaper = {i: hats[q - i] for i in range(1, q + 1)}
    Lpaper = {j: Ls[j - 1] for j in range(1, p + 1)}
    return Lpaper, D, Upaper

def toeplitz_from_roots(omega, roots, q, N):
    z = sp.Symbol('z')
    P = sp.expand(omega * sp.prod([1 + r * z for r in roots]))
    m = len(roots); p = m - q
    t = {k: sp.Rational(P.coeff(z, k + q)) for k in range(-q, p + 1)}
    T = [[F(int(sp.numer(t[i - j])), int(sp.denom(t[i - j]))) if -q <= i - j <= p else F(0) for j in range(N)] for i in range(N)]
    return T, t

# ---------- Lemma 3.1 exchange ----------
M = 30
u = [F(random.randint(1, 9), random.randint(1, 9)) for _ in range(M)]
v = [F(random.randint(1, 9), random.randint(1, 9)) for _ in range(M)]
l = [F(0)] + [F(random.randint(1, 9), random.randint(1, 9)) for _ in range(M - 1)]
lp, (d, vp) = exchange((u, v), l)
N = 20
UL = mm(upper_mat(u, v, M), lower_mat(l, M))
LU = mm(lower_mat(lp, M - 1), upper_mat(d, vp, M - 1))
ok(all(UL[i][j] == LU[i][j] for i in range(N) for j in range(N)) and all(x > 0 for x in d + lp[1:]), "Lemma 3.1 exchange identity and positivity")

# ---------- Theorem 3.2 / Lemma 3.4 / Thm 3.5 / Cor 3.6 ----------
for (p, q) in ((2, 1), (1, 2), (2, 2), (3, 2), (2, 3)):
    eta = [F(random.randint(1, 9), random.randint(1, 5)) for _ in range(q)]
    xi = [F(random.randint(1, 9), random.randint(1, 5)) for _ in range(p)]
    omega = F(random.randint(1, 5), random.randint(1, 3))
    Lp, D, Up = ordered_root_pbf(omega, eta, xi, M=40)
    N = 14
    T, t = toeplitz_from_roots(sp.Rational(omega.numerator, omega.denominator), [sp.Rational(x.numerator, x.denominator) for x in eta + xi], q, N)
    Lprod = chain([lower_mat(Lp[j][:N], N) for j in range(1, p + 1)])
    Uprod = chain([upper_mat([F(1)] * N, Up[i][:N], N) for i in range(q, 0, -1)])
    Dm = [[D[i] if i == j else F(0) for j in range(N)] for i in range(N)]
    PB = chain([Lprod, Dm, Uprod])
    pos = all(Lp[j][n] > 0 for j in Lp for n in range(1, N)) and all(Up[i][n] > 0 for i in Up for n in range(N - 1)) and all(D[n] > 0 for n in range(N))
    ok(PB == T and pos, f"(p,q)=({p},{q}) ordered-root construction gives PBF of T")
    # H, K
    Ht = [[F(0)] * q for _ in range(q)]
    for i in range(q):
        P_ = chain([upper_mat([F(1)] * N, Up[k][:N], N) for k in range(i, 0, -1)]) if i > 0 else eye(N)
        for j in range(q):
            Ht[i][j] = P_[0][j]
    Kt = [[F(0)] * p for _ in range(p)]
    for j in range(p):
        P_ = chain([lower_mat(Lp[k][:N], N) for k in range(1, j + 1)]) if j > 0 else eye(N)
        for i in range(p):
            Kt[i][j] = P_[i][0]
    H = [[Ht[i][j] / Ht[i][i] for j in range(q)] for i in range(q)]
    K = [[Kt[i][j] / Kt[j][j] for j in range(p)] for i in range(p)]
    Hinv = inv_tri(H, True)
    Kinv = inv_tri(K, False)
    goodH = all(Hinv[n][b - 1] == ((-1) ** (n - b + 1) * hcomp(n - b + 1, eta[q - b:] + xi) if n >= b - 1 else 0) for n in range(q) for b in range(1, q + 1))
    xiv = [1 / xi[p - i] for i in range(1, p + 1)]   # xi^vee_i = 1/xi_{p+1-i}
    etah = [1 / eta[q - j] for j in range(1, q + 1)]  # hat eta_j = 1/eta_{q+1-j}
    goodK = all(Kinv[a - 1][n] == ((-1) ** (n - a + 1) * hcomp(n - a + 1, xiv[p - a:] + etah) if n >= a - 1 else 0) for n in range(p) for a in range(1, p + 1))
    ok(goodH and goodK, f"(p,q)=({p},{q}) Lemma: H^-1 and K^-1 formulas")
    # polynomials: recurrence vs GF / coefficient formula (Cor)
    x = sp.Symbol('x')
    NB = 9
    tS = {k: sp.Rational(t[k]) for k in t}
    Hs = sp.Matrix(q, q, lambda i, j: sp.Rational(Hinv[i][j].numerator, Hinv[i][j].denominator))
    B = [[Hs[n, b] for b in range(q)] for n in range(q)]
    for n in range(0, NB - q):
        # row n: sum_k t_k B_{n-k} = x B_n  -> t_{-q} B_{n+q} = x B_n - sum_{k>-q} t_k B_{n-k}
        new = []
        for b in range(q):
            s = x * B[n][b] - sum(tS[k] * B[n - k][b] for k in range(-q + 1, p + 1) if 0 <= n - k < len(B))
            new.append(sp.expand(s / tS[-q]))
        B.append(new)
    om = sp.Rational(omega.numerator, omega.denominator)
    etaS = [sp.Rational(e.numerator, e.denominator) for e in eta]
    xiS = [sp.Rational(e.numerator, e.denominator) for e in xi]
    good = True
    for b in range(1, q + 1):
        for n in range(NB):
            if n < b - 1:
                good &= B[n][b - 1] == 0
                continue
            tot = 0
            for k in range(0, (n - b + 1) // q + 1):
                Nn = n - b + 1 - q * k
                Xl = etaS[:q - b] * k + (etaS[q - b:] + xiS) * (k + 1)
                tot += (-1) ** Nn * om ** (-k) * hcomp(Nn, Xl) * x ** k
            good &= sp.expand(tot - B[n][b - 1]) == 0
    ok(good, f"(p,q)=({p},{q}) Cor: B coefficient formula matches recurrence")
    # left
    Ks = sp.Matrix(p, p, lambda i, j: sp.Rational(Kinv[i][j].numerator, Kinv[i][j].denominator))
    A = [[Ks[a, n] for a in range(p)] for n in range(p)]
    for n in range(0, NB - p):
        new = []
        for a in range(p):
            s = x * A[n][a] - sum(tS[k] * A[n + k][a] for k in range(-q, p) if 0 <= n + k < len(A))
            new.append(sp.expand(s / tS[p]))
        A.append(new)
    omv = om * sp.prod(etaS) * sp.prod(xiS)
    xivS = [1 / xiS[p - i] for i in range(1, p + 1)]
    etahS = [1 / etaS[q - j] for j in range(1, q + 1)]
    good = True
    for a in range(1, p + 1):
        for n in range(NB):
            if n < a - 1:
                good &= A[n][a - 1] == 0
                continue
            tot = 0
            for k in range(0, (n - a + 1) // p + 1):
                Mm = n - a + 1 - p * k
                Zl = xivS[:p - a] * k + (xivS[p - a:] + etahS) * (k + 1)
                tot += (-1) ** Mm * omv ** (-k) * hcomp(Mm, Zl) * x ** k
            good &= sp.expand(tot - A[n][a - 1]) == 0
    ok(good, f"(p,q)=({p},{q}) Cor: A coefficient formula matches recurrence")

# ---------- Theorem 3.2 direct Metelmann construction ----------
def metelmann_from_L(L, p, N):
    a = {i: [F(0)] * N for i in range(1, p + 1)}
    for n in range(1, N):
        k = min(p, n)
        def partial(i0):
            Ms = [lower_mat(a[i], N) for i in range(i0, p + 1)]
            return chain(Ms) if Ms else eye(N)
        y = {r: L[n][n - r] for r in range(1, k + 1)}
        C = {(r, j): partial(p - j + 2)[n - 1][n - r] for r in range(1, k + 1) for j in range(1, k + 1)}
        xx = {}
        for r in range(k, 0, -1):
            xx[r] = (y[r] - sum((C[(r, j)] * xx[j] for j in range(r + 1, k + 1)), F(0))) / C[(r, r)]
        for j in range(1, k + 1):
            a[p - j + 1][n] = xx[j]
    return a

for (p, q) in ((2, 1), (2, 2), (1, 3)):
    m = p + q
    roots = [F(random.randint(1, 9), random.randint(1, 5)) for _ in range(m)]
    omega = F(2)
    N = 16
    T, t = toeplitz_from_roots(2, [sp.Rational(r.numerator, r.denominator) for r in roots], q, N + 6)
    Cm = [[T[i][j + q] / omega if j + q < N + 6 else F(0) for j in range(N)] for i in range(N)]
    a = metelmann_from_L(Cm, m, N)
    pos = all(a[i][n] > 0 for i in a for n in range(m - i + 1, N)) and all(a[i][n] == 0 for i in a for n in range(1, m - i + 1))
    Bs = {i: [F(0)] + [a[i][n + m] for n in range(1, N - m)] for i in a}
    NN = N - m
    Bprod = chain([lower_mat(Bs[i], NN) for i in range(1, m + 1)])
    ok(pos and Bprod == [row[:NN] for row in Cm[:NN]], f"Thm 3.2 ({p},{q}): Metelmann factors of C positive; shifted product = C")
    c1, cm = Cm[1][0], Cm[m][0]
    ok(all(cm / c1 ** (m - 1) <= Bs[i][n] <= c1 for i in Bs for n in range(1, NN)), f"Thm 3.2 ({p},{q}): bounds c_m/c_1^(m-1) <= b_i(n) <= c_1")
    # V_i identity and T = omega V_1...V_q B_{q+1}...B_m
    Vs = {i: ([Bs[i][n + q - i + 1] for n in range(NN - q - 1)], [F(1)] * (NN - q - 1)) for i in range(1, q + 1)}
    n0 = NN - q - 1
    P = chain([upper_mat(Vs[i][0], Vs[i][1], n0) for i in range(1, q + 1)] + [lower_mat(Bs[i][:n0], n0) for i in range(q + 1, m + 1)])
    nn = n0 - q - 2
    ok(all(omega * P[i][j] == T[i][j] for i in range(nn) for j in range(nn)), f"Thm 3.2 ({p},{q}): T = omega V_1...V_q B_(q+1)...B_m on leading block")

# ---------- Prop constant-factor-orders, uniform Christoffel ----------
for (p, q) in ((2, 1), (2, 2), (3, 2)):
    eta = [F(random.randint(1, 9), random.randint(1, 5)) for _ in range(q)]
    xi = [F(random.randint(1, 9), random.randint(1, 5)) for _ in range(p)]
    Nb = 18
    facs = [('U', e) for e in eta] + [('L', x_) for x_ in xi]
    def mat(f):
        if f[0] == 'U':
            return upper_mat([f[1]] * Nb, [F(1)] * Nb, Nb)
        return lower_mat([F(0)] + [f[1]] * (Nb - 1), Nb)
    T0 = chain([mat(f) for f in facs])
    good = True
    for w in set(permutations(range(p + q))):
        Tw = chain([mat(facs[i]) for i in w])
        n = 10
        for a_ in range(n):
            for b_ in range(n):
                dlt = Tw[a_][b_] - T0[a_][b_]
                if a_ >= p or b_ >= q:
                    good &= dlt == 0
                good &= dlt <= 0
    ok(good, f"Prop const-orders ({p},{q}): support in first p rows & q cols, T_w <= T_0 (all orderings)")
h = F(4, 27)
Nb = 12
Um = upper_mat([h] * Nb, [F(1)] * Nb, Nb)
Lm = lower_mat([F(0)] + [h] * (Nb - 1), Nb)
T0 = chain([Um, Lm, Lm])
d1 = [[a_ - b_ for a_, b_ in zip(r1, r2)] for r1, r2 in zip(chain([Lm, Lm, Um]), T0)]
d2 = [[a_ - b_ for a_, b_ in zip(r1, r2)] for r1, r2 in zip(chain([Lm, Um, Lm]), T0)]
e1 = all(d1[i][j] == ({(0, 0): -2 * h, (1, 0): -h * h}.get((i, j), 0)) for i in range(8) for j in range(8))
e2 = all(d2[i][j] == ({(0, 0): -h}.get((i, j), 0)) for i in range(8) for j in range(8))
ok(e1 and e2, "Ex uniform Christoffel chain: differences from T_0")

# ---------- Binomial: PBF, convolution, (2,1) kappa, Lima, H,K ----------
for (p, q) in ((1, 1), (2, 1), (1, 2), (2, 2), (3, 2)):
    m = p + q
    N = 12
    Lq = lower_mat([F(0)] + [F(n, n + q) for n in range(1, N)], N)
    Lpm = lower_mat([F(0)] + [F(n, n + p) for n in range(1, N)], N)
    Dm = [[F(factorial(n + m) * factorial(n), factorial(n + p) * factorial(n + q)) if n == k else F(0) for k in range(N)] for n in range(N)]
    LT = [list(c) for c in zip(*Lpm)]
    P = chain([Lq] * p + [Dm] + [LT] * q)
    Tb = [[F(comb(m, q + i - j)) if 0 <= q + i - j <= m else F(0) for j in range(N)] for i in range(N)]
    ok(P == Tb, f"Binomial PBF ({p},{q})")
    conv = all(sum(comb(p, i - k) * comb(q, j - k) * comb(m + k, k) for k in range(0, min(i, j) + 1) if 0 <= i - k <= p and 0 <= j - k <= q) == comb(i + q, j) * comb(j + p, i) for i in range(10) for j in range(10))
    ok(conv, f"Binomial convolution identity ({p},{q})")
    # K from partial products
    Kt = [[chain([Lq] * j)[i][0] if j > 0 else F(int(i == 0)) for j in range(p)] for i in range(p)]
    K = [[Kt[i][j] / Kt[j][j] for j in range(p)] for i in range(p)]
    Ht = [[chain([LT] * i)[0][j] if i > 0 else F(int(j == 0)) for j in range(q)] for i in range(q)]
    H = [[Ht[i][j] / Ht[i][i] for j in range(q)] for i in range(q)]
    ok(all(K[i][j] == (comb(j + q, i + q) if i <= j else 0) for i in range(p) for j in range(p)) and all(H[i][j] == (comb(i + p, j + p) if j <= i else 0) for i in range(q) for j in range(q)), f"Binomial H,K ({p},{q})")
    ok(all(Kt[i][j] == F(comb(j, i), comb(i + q, q)) for i in range(p) for j in range(p)), f"Binomial K-tilde formula ({p},{q})")
    Kinv = inv_tri(K, False); Hinv = inv_tri(H, True)
    ok(all(Kinv[i][j] == (-1) ** (i - j) * K[i][j] for i in range(p) for j in range(p)) and all(Hinv[i][j] == (-1) ** (i - j) * H[i][j] for i in range(q) for j in range(q)), f"Binomial inverses by sign change ({p},{q})")
L = chain([lower_mat([F(0)] + [F(n, n + 1) for n in range(1, 30)], 30)] * 2)
Qs = inv_tri(L, True)
Qs = [[(-1) ** (i + j) * Qs[i][j] for j in range(30)] for i in range(30)]
ok(all(Qs[n][0] == 1 and Qs[n][1] == F(2 * n, n + 1) for n in range(1, 30)), "Binomial (2,1): Q_{n,0}=1, Q_{n,1}=2n/(n+1)")
for r in (2, 3, 4):
    hr = F(r ** r, (r + 1) ** (r + 1))
    N = 8
    Tb = [[F(comb(r + 1, 1 + i - j)) if 0 <= 1 + i - j <= r + 1 else F(0) for j in range(N)] for i in range(N)]
    Tr = [[hr * hr ** (i - j) * Tb[i][j] for j in range(N)] for i in range(N)]
    ok(all(Tr[i][i + 1] == 1 for i in range(N - 1)) and all(Tr[i + k][i] == comb(r + 1, k + 1) * hr ** (k + 1) for k in range(0, r + 1) for i in range(N - k)), f"Lima rescaling r={r}")

# ---------- density, moments: general theorem (numerical) ----------
def density_setup(omega, eta, xi, H, K):
    q, p = len(eta), len(xi)
    m = p + q
    z = sp.Symbol('z')
    P = sp.Poly(sp.expand(omega * sp.prod([1 + sp.nsimplify(r) * z for r in eta + xi])), z)
    coeffs = [mp.mpf(sp.Rational(c)) for c in P.all_coeffs()]  # highest first
    betas = sorted([mp.mpf(sp.Rational(r)) for r in eta + xi], reverse=True)
    Fz = lambda zz: sum(b * zz / (1 + b * zz) for b in betas)
    zp = mp.findroot(lambda zz: Fz(zz) - q, (mp.mpf('1e-9'), mp.mpf(1e6)), solver='bisect')
    aa = lambda zz: mp.polyval(coeffs, zz) / zz ** q
    lam_p = aa(zp)
    if betas[q - 1] > betas[q]:
        zm = mp.findroot(lambda zz: Fz(zz) - q, (-1 / betas[q] + mp.mpf('1e-20'), -1 / betas[q - 1] - mp.mpf('1e-20')), solver='bisect')
        lam_m = aa(zm)
    else:
        lam_m = mp.mpf(0)
    Hm = mp.matrix([[mp.mpf(sp.Rational(H[i][j])) for j in range(q)] for i in range(q)])
    Km = mp.matrix([[mp.mpf(sp.Rational(K[i][j])) for j in range(p)] for i in range(p)])
    def dens(xv):
        cs = list(coeffs)
        cs[len(cs) - 1 - q] -= xv
        rts = sorted(mp.polyroots(cs, maxsteps=4000, extraprec=300), key=lambda r: abs(r))
        mid = [rts[q - 1], rts[q]]
        zeta = mid[0] if mp.im(mid[0]) < 0 else mid[1]
        S0 = rts[:q - 1]; Z0 = rts[q + 1:]
        rho = -mp.im(zeta) / (mp.pi * mp.mpf(sp.Rational(omega))) * mp.fprod([abs(u_) for u_ in S0])
        Shat = S0 + [zeta, mp.conj(zeta)]
        Zhat = Z0 + [zeta, mp.conj(zeta)]
        hv = mp.matrix([[hcomp(i, [1 / v_ for v_ in Zhat])] for i in range(q)])
        gv = mp.matrix([[hcomp(j, Shat) for j in range(p)]])
        f = Hm * hv
        g = gv * Km
        return rho, f, g
    return lam_m, lam_p, dens

for (p, q, eta, xi) in ((2, 1, [F(1)], [F(2), F(1, 2)]), (1, 2, [F(3), F(1, 3)], [F(1)]), (2, 2, [F(2), F(1)], [F(3, 2), F(1, 3)])):
    omega = F(1)
    Lp, D, Up = ordered_root_pbf(omega, eta, xi, M=40)
    N = 12
    Ht = [[F(0)] * q for _ in range(q)]
    for i in range(q):
        P_ = chain([upper_mat([F(1)] * N, Up[k][:N], N) for k in range(i, 0, -1)]) if i > 0 else eye(N)
        for j in range(q):
            Ht[i][j] = P_[0][j]
    Kt = [[F(0)] * p for _ in range(p)]
    for j in range(p):
        P_ = chain([lower_mat(Lp[k][:N], N) for k in range(1, j + 1)]) if j > 0 else eye(N)
        for i in range(p):
            Kt[i][j] = P_[i][0]
    H = [[Ht[i][j] / Ht[i][i] for j in range(q)] for i in range(q)]
    K = [[Kt[i][j] / Kt[j][j] for j in range(p)] for i in range(p)]
    lam_m, lam_p, dens = density_setup(omega, eta, xi, H, K)
    NT = 40
    T, t = toeplitz_from_roots(1, [sp.Rational(r.numerator, r.denominator) for r in eta + xi], q, NT)
    mom_ok = True
    maxerr = 0
    for ell in range(0, 4):
        Tl = eye(NT)
        for _ in range(ell):
            Tl = mm(Tl, T)
        exact = [[sum(H[i][a_] * Tl[a_][b_] * K[b_][j] for a_ in range(q) for b_ in range(p)) for j in range(p)] for i in range(q)]
        for i in range(q):
            for j in range(p):
                num = mp.quad(lambda xv: xv ** ell * (lambda r: r[0] * r[1][i] * r[2][j])(dens(xv)), [lam_m, (lam_m + lam_p) / 2, lam_p])
                err = abs(num - mp.mpf(sp.Rational(exact[i][j])))
                maxerr = max(maxerr, err)
    ok(maxerr < mp.mpf('1e-12'), f"Thm general-measure ({p},{q}) eta={eta} xi={xi}: moments 0..3 match H E T^l E^T K (max err {mp.nstr(maxerr, 3)})")
    # eigenvalue check of finite sections vs [lam_-, lam_+]
    import numpy as np
    Tn = np.array([[float(T[i][j]) for j in range(NT)] for i in range(NT)])
    ev = np.sort(np.linalg.eigvals(Tn).real)
    print(f"     sections N={NT}: eig range [{ev[0]:.4f},{ev[-1]:.4f}] vs [{float(lam_m):.4f},{float(lam_p):.4f}]")

# ---------- binomial 2x2 example and hard/soft edges ----------
p = q = 2
Hb = [[F(1), F(0)], [F(3), F(1)]]
Kb = [[F(1), F(3)], [F(0), F(1)]]
lam_m, lam_p, dens = density_setup(F(1), [F(1), F(1)], [F(1), F(1)], Hb, Kb)
good = True
for xv in (mp.mpf('0.3'), mp.mpf(3), mp.mpf(9), mp.mpf('15.5')):
    rho, f, g = dens(xv)
    s = mp.sqrt(xv)
    r = (s + mp.sqrt(s * (s + 4))) / 2
    wv = mp.sqrt(s * (4 - s)) / (2 * mp.pi * (1 + r))
    good &= abs(rho - wv) < 1e-20 and abs(f[1] - r) < 1e-20 and abs(g[1] - r) < 1e-20
ok(good and abs(lam_p - 16) < 1e-20, "Ex two-by-two binomial weight")
for (p, q) in ((2, 1), (1, 2), (2, 2), (3, 2)):
    m = p + q
    Hb = [[F(comb(i + p, j + p)) if j <= i else F(0) for j in range(q)] for i in range(q)]
    Kb = [[F(comb(j + q, i + q)) if i <= j else F(0) for j in range(p)] for i in range(p)]
    lam_m, lam_p, dens = density_setup(F(1), [F(1)] * q, [F(1)] * p, Hb, Kb)
    phi = mp.pi / m
    xv = mp.mpf('1e-24')
    rho, f, g = dens(xv)
    ups = xv ** (mp.mpf(1) / m)
    Fb = [mp.fprod([mp.sin((p + j) * phi) / mp.sin(j * phi) for j in range(1, b)]) for b in range(1, q + 1)]
    Ga = [mp.fprod([mp.sin((q + j) * phi) / mp.sin(j * phi) for j in range(1, a)]) for a in range(1, p + 1)]
    e1 = abs(rho / (mp.sin(q * phi) / mp.pi * ups) - 1)
    e2 = max(abs(f[b - 1] / (Fb[b - 1] * ups ** (b - 1)) - 1) for b in range(1, q + 1))
    e3 = max(abs(g[a - 1] / (Ga[a - 1] * ups ** (a - 1)) - 1) for a in range(1, p + 1))
    c = mp.mpf(m) ** m / (mp.mpf(p) ** p * mp.mpf(q) ** q)
    xs = c - mp.mpf('1e-16')
    rho2, _, _ = dens(xs)
    cs_ = [mp.binomial(m, k) for k in range(m, -1, -1)]
    cs_[m - q] -= xs
    rts = sorted(mp.polyroots(cs_, maxsteps=2000, extraprec=200), key=abs)
    S0c = rts[:q - 1]
    pred = mp.fprod([abs(u_) for u_ in S0c]) / mp.pi * mp.sqrt(2 * m * q / (c * p ** 3)) * mp.sqrt(c - xs)
    e4 = abs(rho2 / pred - 1)
    ok(max(e1, e2, e3) < 5 * ups and e4 < 1e-6 and abs(lam_p - c) < 1e-20, f"Binomial ({p},{q}): hard-edge constants and soft-edge constant (errs {mp.nstr(max(e1,e2,e3),2)}, {mp.nstr(e4,2)})")

# ---------- trig parametrization ----------
good = True
for (p, q) in ((2, 1), (3, 2), (1, 3)):
    m = p + q
    for th in (mp.mpf('0.05'), mp.pi / m / 2, mp.pi / m * mp.mpf('0.9')):
        zeta = mp.sin(q * th) / mp.sin(p * th) * mp.exp(-1j * m * th)
        xth = mp.sin(m * th) ** m / (mp.sin(p * th) ** p * mp.sin(q * th) ** q)
        good &= abs((1 + zeta) ** m - xth * zeta ** q) < 1e-20
        good &= abs(1 + zeta - mp.sin(m * th) / mp.sin(p * th) * mp.exp(-1j * q * th)) < 1e-20
ok(good, "Lemma roots: trigonometric parametrization")

# ---------- geometric family (exact) ----------
def qp(a, t, n):
    out = F(1)
    for nu in range(n):
        out *= (1 - a * t ** nu)
    return out
def gb(N, r, t):
    if r < 0 or r > N:
        return F(0)
    return qp(t, t, N) / (qp(t, t, r) * qp(t, t, N - r))
for t in (F(2, 3), F(3)):
    for (p, q) in ((1, 1), (2, 1), (1, 2), (2, 2), (3, 2)):
        al = F(5, 4)
        m = p + q
        N = 10
        ent = lambda h: al ** h * t ** (h * (h - 1) // 2) * gb(m, h, t) if 0 <= h <= m else F(0)
        Tt = [[ent(q + i - j) for j in range(N)] for i in range(N)]
        La = {a: lower_mat([F(0)] + [al * t ** (q + a) * (1 - t ** n) / (1 - t ** (n + q)) for n in range(1, N)], N) for a in range(p)}
        Ub = {b: upper_mat([F(1)] * N, [t ** (-b) / al * (1 - t ** (n + 1)) / (1 - t ** (n + p + 1)) for n in range(N)], N) for b in range(q)}
        Dm = [[al ** q * t ** (q * (q - 1) // 2) * qp(t ** (n + p + 1), t, q) / qp(t ** (n + 1), t, q) if n == k else F(0) for k in range(N)] for n in range(N)]
        P = chain([La[a] for a in range(p)] + [Dm] + [Ub[b] for b in range(q - 1, -1, -1)])
        ok(P == Tt, f"Geometric tau={t} ({p},{q}): PBF product = T_tau")
        Kt = [[(chain([La[a] for a in range(j)])[i][0] if j > 0 else F(int(i == 0))) for j in range(p)] for i in range(p)]
        Ht = [[(chain([Ub[b] for b in range(i - 1, -1, -1)])[0][j] if i > 0 else F(int(j == 0))) for j in range(q)] for i in range(q)]
        K = [[Kt[i][j] / Kt[j][j] for j in range(p)] for i in range(p)]
        H = [[Ht[i][j] / Ht[i][i] for j in range(q)] for i in range(q)]
        Hf = [[al ** (i - j) * t ** ((i - j) * (i - j - 1) // 2) * gb(p + i, i - j, t) if j <= i else F(0) for j in range(q)] for i in range(q)]
        Kf = [[al ** (-(j - i)) * t ** (-(j - i) * (q + i) - (j - i) * (j - i - 1) // 2) * gb(q + j, j - i, t) if i <= j else F(0) for j in range(p)] for i in range(p)]
        Hif = [[(-al) ** (i - j) * gb(p + i, i - j, t) if j <= i else F(0) for j in range(q)] for i in range(q)]
        Kif = [[(-1 / al) ** (j - i) * t ** (-(j - i) * (q + i)) * gb(q + j, j - i, t) if i <= j else F(0) for j in range(p)] for i in range(p)]
        ok(H == Hf and K == Kf and inv_tri(H, True) == Hif and inv_tri(K, False) == Kif, f"Geometric tau={t} ({p},{q}): H, K and inverses")
        # GF initial coefficients for B and A
        z = sp.Symbol('z')
        tS, aS = sp.Rational(t.numerator, t.denominator), sp.Rational(al.numerator, al.denominator)
        poch = lambda a_, tt, n: sp.prod([1 - a_ * tt ** nu for nu in range(n)])
        good = True
        for b in range(1, q + 1):
            ser = sp.series(z ** (b - 1) * poch(-aS * tS ** (p + b) * z, tS, q - b) / poch(-aS * z, tS, m), z, 0, q).removeO()
            good &= all(sp.Rational(ser.coeff(z, n)) == sp.Rational(Hif[n][b - 1].numerator, Hif[n][b - 1].denominator) for n in range(q))
        tp = aS ** m * tS ** (m * (m - 1) // 2)
        for a_ in range(1, p + 1):
            Pv = tp * poch(-z / aS, 1 / tS, m)
            ser = sp.series(tp * z ** (a_ - 1) * poch(-z / (aS * tS ** (q + a_)), 1 / tS, p - a_) / Pv, z, 0, p).removeO()
            good &= all(sp.Rational(ser.coeff(z, n)) == sp.Rational(Kif[a_ - 1][n].numerator, Kif[a_ - 1][n].denominator) for n in range(p))
        zz = sp.Symbol('zz')
        good &= sp.expand(zz ** m * sp.prod([1 + aS * tS ** nu / zz for nu in range(m)]) - tp * poch(-zz / aS, 1 / tS, m)) == 0
        ok(good, f"Geometric tau={t} ({p},{q}): GF initial coefficients = H^-1, K^-1; P^vee formula")
    # tau-Vandermonde-Pfaff
    good = True
    for (p, q) in ((1, 1), (2, 1), (2, 3), (3, 3)):
        m = p + q
        for i in range(7):
            for j in range(7):
                lhs = sum((t ** ((i - k) * (j - k)) * gb(p, i - k, t) * gb(q, j - k, t) * gb(m + k, k, t) for k in range(0, min(i, j) + 1)), F(0))
                good &= lhs == gb(i + q, j, t) * gb(j + p, i, t)
    ok(good, f"tau-Vandermonde-Pfaff tau={t}")

# ---------- q-affine obstruction p=q=1 ----------
t = F(9, 4); al = F(2)
sq = F(3, 2)
a_ = s_ = al * sq
b_ = al * (sq - 1) ** 2
ok(al * (1 + t) == 2 * a_ + b_ and al * al * t == a_ * s_ and a_ / s_ == 1, "q-affine p=q=1: a=s=alpha sqrt(tau), b=alpha(sqrt(tau)-1)^2")
