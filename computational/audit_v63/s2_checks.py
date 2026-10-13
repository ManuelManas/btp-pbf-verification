"""Exact checks for Section 2 of BTP_PBF v62."""
from fractions import Fraction as F
from itertools import combinations
from math import factorial
import random
import sympy as sp

random.seed(2026)

# ---------------- helpers ----------------
def eye(N):
    return [[F(int(i == j)) for j in range(N)] for i in range(N)]

def lbid(sub, N):
    """unit lower bidiagonal, sub[n] = entry (n,n-1), n=1..N-1 (sub[0] ignored)"""
    M = eye(N)
    for n in range(1, N):
        M[n][n - 1] = F(sub[n])
    return M

def mm(A, B):
    n, k, m = len(A), len(B), len(B[0])
    return [[sum((A[i][t] * B[t][j] for t in range(k) if A[i][t] and B[t][j]), F(0)) for j in range(m)] for i in range(n)]

def prod(Ms):
    P = Ms[0]
    for M in Ms[1:]:
        P = mm(P, M)
    return P

def inv_lower_unit(L):
    N = len(L)
    X = [[F(0)] * N for _ in range(N)]
    for c in range(N):
        for r in range(N):
            X[r][c] = F(int(r == c)) - sum((L[r][k] * X[k][c] for k in range(c, r)), F(0))
    return X

def signed(M):
    return [[(-1) ** (i + j) * M[i][j] for j in range(len(M[0]))] for i in range(len(M))]

def det(M):
    M = [row[:] for row in M]
    n = len(M)
    d = F(1)
    for c in range(n):
        piv = next((r for r in range(c, n) if M[r][c] != 0), None)
        if piv is None:
            return F(0)
        if piv != c:
            M[c], M[piv] = M[piv], M[c]
            d = -d
        d *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            if f:
                for k in range(c, n):
                    M[r][k] -= f * M[c][k]
    return d

def sub(M, rows, cols):
    return [[M[r][c] for c in cols] for r in rows]

def metelmann(p, N, gen):
    """a[i][n] for i=1..p, n=0..N-1; zero for n<=p-i"""
    a = {}
    for i in range(1, p + 1):
        a[i] = [F(0)] * N
        for n in range(p - i + 1, N):
            a[i][n] = F(gen(i, n))
    return a

def build_L(a, p, N):
    return prod([lbid(a[i], N) for i in range(1, p + 1)])

def kappa_data(L, p):
    N = len(L)
    Q = signed(inv_lower_unit(L))
    def Delta(k, n):
        return det(sub(Q, range(n, n + k), range(k)))
    def C1det(k, n):
        return det(sub(Q, range(n, n + k), list(range(k - 1)) + [k]))
    return Q, Delta, C1det

ok = lambda cond, msg: print(("OK   " if cond else "FAIL ") + msg)

# ---------------- Example 2.10 ----------------
u, v, w = sp.symbols('u v w', positive=True)
Lex = sp.Matrix([[1,0,0,0,0],[1,1,0,0,0],[1,2,1,0,0],[1,3,3,1,0],[0,1,3,3,1]])
def symlbid(subs, N):
    M = sp.eye(N)
    for n in range(1, N):
        M[n, n-1] = subs[n]
    return M
ah = {1:[0,0,0,1,1], 2:[0,0,1,1,1], 3:[0,1,1,1,1]}
ok(symlbid(ah[1],5)*symlbid(ah[2],5)*symlbid(ah[3],5) == Lex, "Ex 2.10: Metelmann factors reproduce L")
A = {i: [0]*5 for i in (1,2,3)}
A[1][1] = u; A[2][1] = v; A[1][2] = w
unk = {}
for n in range(1, 5):
    k = min(3, n)
    vars_ = [sp.Symbol(f'a{i}_{n}') for i in range(3 - k + 1, 4)]
    for i, s in zip(range(3 - k + 1, 4), vars_):
        A[i][n] = s
    P = symlbid(A[1],5)*symlbid(A[2],5)*symlbid(A[3],5)
    eqs = [sp.Eq(P[n, n-r], Lex[n, n-r]) for r in range(1, k+1)]
    sol = sp.solve(eqs, vars_, dict=True)[0]
    for i, s in zip(range(3 - k + 1, 4), vars_):
        A[i][n] = sp.factor(sp.simplify(sol[s]))
ok(sp.simplify(A[3][1] - (1-u-v)) == 0, "Ex 2.10: a3(1)=1-u-v")
ok(sp.simplify(A[2][2] - (1-w+u*w)/(1-u-v)) == 0, "Ex 2.10: a2(2)")
ok(sp.simplify(A[3][2] - (1-2*u-2*v+v*w)/(1-u-v)) == 0, "Ex 2.10: a3(2)")
ok(sp.simplify(A[2][3] - (1-u-v)*(1-2*w+3*u*w)/((1-w+u*w)*(1-2*u-2*v+v*w))) == 0, "Ex 2.10: a2(3)")
claimed = [1-u-v, 1-w+u*w, 1-2*u-2*v+v*w, 1-2*w+3*u*w, 1-3*u-3*v+3*v*w, 1-3*w+6*u*w, 1-4*u-4*v+6*v*w]
factors = set()
for i in (1,2,3):
    for n in range(1,5):
        e = sp.factor(A[i][n])
        num, den = sp.fraction(sp.together(e))
        for f_, _ in sp.factor_list(num)[1]:
            factors.add(sp.expand(f_))
        for f_, _ in sp.factor_list(den)[1]:
            factors.add(sp.expand(f_))
print("     Ex 2.10 factor set:", sorted([str(f) for f in factors]))
ok(all(sp.expand(c) in factors or sp.expand(-c) in factors for c in claimed), "Ex 2.10: every claimed inequality polynomial appears")
cl = [sp.expand(c) for c in claimed] + [sp.expand(-c) for c in claimed]
extra = [f for f in factors if f not in cl and f not in (u, v, w)]
ok(len(extra) == 0, "Ex 2.10: no other polynomial factors (%s)" % extra)
vals = {u: sp.Rational(1,10), v: sp.Rational(1,10), w: sp.Rational(1,10)}
ok(all(c.subs(vals) > 0 for c in claimed) and all(A[i][n].subs(vals) > 0 for i in (1,2,3) for n in range(1,5)), "Ex 2.10: u=v=w=1/10 admissible")
# the domain should equal intersection; check signs: all entries are ratios of claimed polys -> fine

# ---------------- Example 2.15 ----------------
p, N = 3, 9
a = metelmann(p, N, lambda i, n: F(random.randint(1, 9), random.randint(1, 9)))
L = build_L(a, p, N)
aa, bb, cc = [F(0)]*N, [F(0)]*N, [F(0)]*N
cc[1] = L[1][0]; bb[2] = L[2][0]/cc[1]; cc[2] = L[2][1]-bb[2]
for n in range(3, N):
    aa[n] = L[n][n-3]/(bb[n-1]*cc[n-2])
    bb[n] = (L[n][n-2]-aa[n]*(bb[n-1]+cc[n-1]))/cc[n-1]
    cc[n] = L[n][n-1]-aa[n]-bb[n]
ok(aa == a[1] and bb == a[2] and cc == a[3], "Ex 2.15: three-factor recursion recovers Metelmann factors")

# ---------------- Prop 2.13 ----------------
p, N = 3, 10
a = metelmann(p, N, lambda i, n: F(random.randint(1, 9), random.randint(1, 9)))
L = build_L(a, p, N)
Q = signed(inv_lower_unit(L))
kap = [None] + [Q[n][0]/Q[n][1] for n in range(1, N)]
ok(all(kap[n] > kap[n+1] > 0 for n in range(1, N-1)), "Prop 2.13: kappa_n strictly decreasing, positive")

# ---------------- Prop 2.17 ----------------
for p in (2, 3, 4):
    N = 12
    a = metelmann(p, N, lambda i, n: F(random.randint(1, 9), random.randint(1, 9)))
    L = build_L(a, p, N)
    Q, Delta, C1 = kappa_data(L, p)
    good = True
    for k in range(1, p):
        al = {j: a[p-k][k+j] for j in range(1, N-k)}
        be = {j: a[p-k+1][k+j] for j in range(0, N-k)}
        for Nn in range(1, N-k-1):
            kap = Delta(k, Nn)/C1(k, Nn)
            # bottom-up fraction
            if Nn == 1:
                K = be[0]
            else:
                d = al[Nn-1] + be[Nn-1]
                for j in range(Nn-2, 0, -1):
                    d = al[j] + be[j] - be[j]*al[j+1]/d
                K = be[0] - be[0]*al[1]/d
            closed = be[0]/(1 + sum(prod_ for prod_ in [
                __import__('functools').reduce(lambda x, y: x*y, [al[i]/be[i] for i in range(1, j+1)], F(1)) for j in range(1, Nn)]))
            good &= (K == kap == closed)
    ok(good, f"Prop 2.17 p={p}: Jacobi convergents = kappa = closed form")

# ---------------- Lemma 2.18 ----------------
for m in (2, 3, 4):
    N = 14
    # random unit lower triangular F with bandwidth m and f_m>0 (not nec. TN)
    Fm = eye(N)
    for n in range(N):
        for s in range(1, m+1):
            if n-s >= 0:
                Fm[n][n-s] = F(random.randint(-5, 9), random.randint(1, 5)) if s < m else F(random.randint(1, 9), random.randint(1, 5))
    init = [None] + [F(random.randint(1, 7), random.randint(1, 7)) for _ in range(m-1)]
    phi = [F(0)]*N
    phi[m-1] = F(1)
    for j in range(m-2, -1, -1):
        phi[j] = phi[j+1]*init[j+1]
    f = lambda s, n: Fm[n][n-s]
    for n in range(m, N):
        phi[n] = sum(((-1)**(j-1)*f(m-j, n-j)*phi[n-j] for j in range(1, m+1)), F(0))/f(m, n)
    R = signed(inv_lower_unit(Fm))
    M = [[F(0)]*(m-1) for _ in range(m)]
    for j in range(m-1):
        M[j][j] = F(1); M[j+1][j] = -init[j+1]
    good = True
    for n in range(0, N-m+1):
        W = det(mm(sub(R, range(n, n+m-1), range(m)), M))
        pr = F(1)
        for t in range(m, n+m):
            pr *= f(m, t)
        good &= (W == phi[n+m-1]*pr)
    ok(good, f"Lemma 2.18 m={m}: W_n = phi_(n+m-1) * prod f_m (random signed F)")

# ---------------- Example 2.28 (p=4) and Theorem 2.19 machinery ----------------
p, N = 4, 44
a = metelmann(p, N, lambda i, n: F(n+2*i-p-1, n))
L = build_L(a, p, N)
Q, Delta, C1 = kappa_data(L, p)
def pi_(j, n):
    out = F(1)
    for t in range(j+1, n+1):
        out *= a[p-j][t]
    return out
def r_(k, n):
    return pi_(k, n)/pi_(k-1, n)
good = all(r_(k, n) == F(k*(p-k), (n+p-2*k)*(n+p-2*k+1)) for k in range(1, p) for n in range(k, N))
ok(good, "Ex 2.28: r_k(n) closed form")
ok(all(sum((r_(k, n) for n in range(Nn, N)), F(0)) + F(k*(p-k), N+p-2*k) == F(k*(p-k), Nn+p-2*k) for k in range(1, p) for Nn in range(k, 10)), "Ex 2.28: tail sums")
S = {k: F(k) for k in range(1, p)}
B = max([F(1)] + [__import__('functools').reduce(lambda x, y: x*y, [S[h] for h in range(l+1, j+1)], F(1)) for l in range(p) for j in range(l+1, p)])
ok(B == 6, "Ex 2.28: B = 6")
# finite reconstruction on section of order p+1 with all six initial entries u
uu = F(1, 4096)
d = p + 1
Lf = [row[:d] for row in L[:d]]
af = {i: [F(0)]*d for i in range(1, p+1)}
for n in range(1, p):
    for i in range(1, p-n+1):
        af[i][n] = uu
for n in range(1, d):
    k = min(p, n)
    # unknowns i = p-k+1..p, solve triangular system as in Lemma 2.4
    # x_j = a_{p-j+1}(n), C_{r,j} = [L_{p-j+2}...L_p]_{n-1,n-r}
    def partial(i0):
        Ms = [lbid(af[i], d) for i in range(i0, p+1)]
        return prod(Ms) if Ms else eye(d)
    y = {}
    for r in range(1, k+1):
        y[r] = Lf[n][n-r] - sum((af[i][n]*partial(i+1)[n-1][n-r] for i in range(1, p-k+1)), F(0))
    C = {(r, j): partial(p-j+2)[n-1][n-r] for r in range(1, k+1) for j in range(1, k+1)}
    x = {}
    for r in range(k, 0, -1):
        x[r] = (y[r] - sum((C[(r, j)]*x[j] for j in range(r+1, k+1)), F(0)))/C[(r, r)]
    for j in range(1, k+1):
        af[p-j+1][n] = x[j]
ok(prod([lbid(af[i], d) for i in range(1, p+1)]) == Lf, "Ex 2.28: finite reconstruction reproduces section")
ok(all(af[i][n] > 0 for i in range(1, p+1) for n in range(1, d)), "Ex 2.28: finite factors positive through row 4")
Sf = [(-1)**i for i in range(d)]
def X(r):
    P = prod([lbid(af[i], d) for i in range(1, r+1)]) if r > 0 else eye(d)
    P = [[Sf[i]*Sf[j]*P[i][j] for j in range(d)] for i in range(d)]
    return [row[:p-r] for row in P[:p]]
eps = {}
for m in range(1, p):
    Xm = X(p-m)
    e = F(0)
    for K in combinations(range(p), m):
        e += abs(det(sub(Xm, K, range(m))) - (1 if K == tuple(range(m)) else 0))
    eps[m] = e
ok(eps[1] == 3*uu+3*uu**2+uu**3 and eps[2] == 2*uu+4*uu**2+2*uu**3+uu**4 and eps[3] == uu+uu**2+uu**3, "Ex 2.28: epsilon_m formulas")
margins = {m: factorial(m)*6**m*eps[m] for m in range(1, p)}
print("     m!6^m eps_m =", {m: float(v) for m, v in margins.items()})
ok(all(v < F(1, 3) for v in margins.values()), "Ex 2.28: m!6^m eps_m < 1/3")
worst = F(10)
for m in range(1, p):
    Xm = X(p-m)
    for n in range(0, N-m-1):
        Wmn = det(mm(sub(Q, range(n, n+m), range(p)), Xm))
        worst = min(worst, Wmn/Delta(m, n))
print("     min_{m,n<=%d} W/Delta =" % (N-p-1), float(worst))
ok(worst > F(2, 3), "Ex 2.28: W_{m,n}/Delta_{m,n} > 2/3 on computed range")
# global extraction through N rows (Lemma 2.18 iterated) and agreement with finite factors
Fr = [row[:] for row in L]
glob = {}
allpos = True
for r in range(0, p-1):
    m = p - r
    init = [None] + [af[r+1][h] for h in range(1, m)]
    phi = [F(0)]*N
    phi[m-1] = F(1)
    for j in range(m-2, -1, -1):
        phi[j] = phi[j+1]*init[j+1]
    for n in range(m, N):
        phi[n] = sum(((-1)**(j-1)*Fr[n-j][n-m]*phi[n-j] for j in range(1, m+1)), F(0))/Fr[n][n-m]
    allpos &= all(x > 0 for x in phi)
    an = [F(0)] + [phi[n-1]/phi[n] for n in range(1, N)]
    glob[r+1] = an
    Fr = mm(inv_lower_unit(lbid(an, N)), Fr)
glob[p] = [F(0)] + [Fr[n][n-1] for n in range(1, N)]
allpos &= all(glob[p][n] > 0 for n in range(1, N))
ok(allpos, f"Ex 2.28: global extraction positive in all {N-1} rows")
ok(all(glob[i][n] == af[i][n] for i in range(1, p+1) for n in range(1, d)), "Ex 2.28: global factors agree with finite factors on section")
ok(prod([lbid(glob[i], N) for i in range(1, p+1)]) == L, "Ex 2.28: product of global factors = L")
# Remark 2.21 reconstruction formula
def Wfun(m, n):
    if m == 0:
        return F(1)
    if m == p:
        return Delta(p, n)
    return det(mm(sub(Q, range(n, n+m), range(p)), X(p-m)))
good = True
for m in range(1, p+1):
    i = p - m + 1
    for n in range(m, N-p-1):
        rhs = Wfun(m, n-m+1)*Wfun(m-1, n-m)/(Wfun(m, n-m)*Wfun(m-1, n-m+1))
        good &= (rhs == glob[i][n])
ok(good, "Rem 2.21: reconstruction formula a_i(n)=W W/(W W)")

# ---------------- Example 2.27 / Prop 2.26 ----------------
for xi in ([2, 1, 3, 4], [1, 3, 2, 4], [1, 2, 4, 3]):
    p, N = 4, 16
    a = metelmann(p, N, lambda i, n: F(xi[i-1]))
    L = build_L(a, p, N)
    Q, Delta, C1 = kappa_data(L, p)
    good = True
    for k in range(1, p):
        x, y = F(xi[p-k-1]), F(xi[p-k])
        for n in range(1, N-k-1):
            good &= Delta(k, n)/C1(k, n) == y**n/sum((x**j*y**(n-1-j) for j in range(n)), F(0))
    ok(good, f"Prop 2.26 formula for kappa_(k,n), xi={xi}")
    print("     limits:", [max(F(xi[p-k])-F(xi[p-k-1]), 0) for k in range(1, p)])
xi = [2, 1, 3, 4]; p = 4; N = 16
a = metelmann(p, N, lambda i, n: F(xi[i-1])); L = build_L(a, p, N); Q, Delta, C1 = kappa_data(L, p)
ok(all(Delta(3, n)/C1(3, n) == F(1, 2**n-1) for n in range(1, N-4)), "Ex 2.27: kappa_(3,n)=1/(2^n-1)")

for p in (2, 3, 4, 5):
    xs = sp.symbols(f'x1:{p+1}')
    Nn = p + 4
    def M_(i):
        return symlbid([0] + [xs[i-1] if n >= p-i+1 else 0 for n in range(1, Nn)], Nn)
    Lsym = sp.eye(Nn)
    for i in range(1, p+1):
        Lsym = Lsym*M_(i)
    def b_(j, n):
        return xs[j-1]-xs[j-n-1] if n <= j-1 else xs[j-1]
    E = sp.eye(Nn)
    for j in range(p, 0, -1):
        E = E*symlbid([0] + [b_(j, n) for n in range(1, Nn)], Nn)
    ok(sp.expand(E - Lsym) == sp.zeros(Nn, Nn), f"Prop 2.26 explicit factorization p={p}")

# ---------------- Remark 2.23 endpoint ----------------
x1, x2 = F(1), F(3)
p, N = 2, 60
a = metelmann(p, N, lambda i, n: x1 if i == 1 else x2)
L = build_L(a, p, N)
Q = signed(inv_lower_unit(L))
for uu, label in ((x2-x1, "endpoint"), (x2-x1+F(1, 1000), "endpoint+1e-3")):
    Fn = [Q[n][0]-uu*Q[n][1] for n in range(N)]
    print(f"     Rem 2.23 u={label}: min F_n over n<{N} =", float(min(Fn)), " first n with F_n<=0:", next((n for n in range(N) if Fn[n] <= 0), None))

# ---------------- Prop 2.24 certificate on Ex 2.28 ----------------
p = 4
for k in range(1, p):
    c = p-2*k
    Ncert = max(k+1, 3*c+2)
    th = lambda n: F(n+c, n+c+2)
    good = all(F(2*n)-th(n)*F(2*(n+1)) >= 1 for n in range(Ncert, Ncert+400))
    s = sum((F(k*(p-k), (n+c)*(n+c+1)) for n in range(k, Ncert)), F(0))
    lower = 1/(s+F(2*Ncert)*F(k*(p-k), (Ncert+c)*(Ncert+c+1)))
    upper = 1/s if s else None
    ok(good and lower <= F(1, k) and (upper is None or F(1, k) <= upper), f"Prop 2.24 certificate b(n)=2n, k={k}, N={Ncert}: [{float(lower):.4f},{float(upper) if upper else 'inf'}] contains 1/k")

# ---------------- Theorem 2.29 ----------------
p, q, N = 3, 2, 10
eps_ = sp.Symbol('e', positive=True)
al = metelmann(p, N, lambda i, n: sp.Rational(random.randint(1, 9), random.randint(1, 9)))
au = metelmann(q, N, lambda i, n: sp.Rational(random.randint(1, 9), random.randint(1, 9)))
Dg = sp.diag(*[sp.Rational(random.randint(1, 9), random.randint(1, 9)) for _ in range(N)])
def symL(i, e):
    return symlbid([0] + [al[i][n] if n > p-i else e for n in range(1, N)], N)
def symU(j, e):
    return symlbid([0] + [au[j][n] if n > q-j else e for n in range(1, N)], N).T
def Tof(e):
    Lm = sp.eye(N); Um = sp.eye(N)
    for i in range(1, p+1): Lm = Lm*symL(i, e)
    for j in range(q, 0, -1): Um = Um*symU(j, e)
    return Lm*Dg*Um
T0 = Tof(0); Te = Tof(eps_)
Dl = sp.expand(Te - T0)
m0 = p+q-1
supp_ok = all(Dl[i, j] == 0 for i in range(N) for j in range(N) if i >= m0 or j >= m0)
rank_ok = Dl.subs(eps_, sp.Rational(1, 3)).rank() <= p+q-2
coef_ok = all(all(c >= 0 for c in sp.Poly(Dl[i, j], eps_).all_coeffs()) and sp.Poly(Dl[i, j], eps_).degree() <= p+q-2 for i in range(m0) for j in range(m0) if Dl[i, j] != 0)
ok(supp_ok and rank_ok and coef_ok, "Thm 2.29: support in m0 block, rank<=p+q-2, nonneg coefficients, degree<=p+q-2")
