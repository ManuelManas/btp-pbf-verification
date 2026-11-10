#!/usr/bin/env python3
"""Independent exact checks for the new Toeplitz root and binomial ODE formulas.

Uses only Python's standard library (Fraction, factorial, comb).  No manuscript
files are edited.  Root identities are tested at exact rational roots, including
the actual ordered-root Toeplitz families at x=0 and general proper rational
functions.  The binomial generating function recurrence, factorial coefficients,
Euler differential equation, and terminating hypergeometric coefficients are
compared independently.  These finite checks support, but do not replace, the
algebraic arguments recorded in the JSON report.
"""
from fractions import Fraction as F
from math import comb, factorial, prod
from pathlib import Path
from collections import Counter
import json

COUNTS = Counter()


def check(category, actual, expected, context):
    if actual != expected:
        raise AssertionError(f"{category}: {context}: {actual!r} != {expected!r}")
    COUNTS[category] += 1


def trim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a or [F(0)]


def add(a, b):
    return trim([(a[i] if i < len(a) else 0) +
                 (b[i] if i < len(b) else 0)
                 for i in range(max(len(a), len(b)))])


def scale(a, s):
    return trim([F(s) * v for v in a])


def mul(a, b):
    ans = [F(0)] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        for j, v in enumerate(b):
            ans[i+j] += u*v
    return trim(ans)


def ev(a, z):
    ans = F(0)
    for v in reversed(a):
        ans = ans*z + v
    return ans


def deriv(a):
    return [i*a[i] for i in range(1, len(a))] or [F(0)]


def series(numerator, denominator, nmax):
    assert denominator[0]
    ans = []
    for n in range(nmax+1):
        rhs = numerator[n] if n < len(numerator) else 0
        rhs -= sum(denominator[j]*ans[n-j]
                   for j in range(1, min(n, len(denominator)-1)+1))
        ans.append(F(rhs)/denominator[0])
    return ans


def linear_product(beta):
    result = [F(1)]
    for b in beta:
        result = mul(result, [F(1), F(b)])
    return result


def binomial_closed(p, q, b, n):
    N = n-b+1
    if N < 0:
        return [F(0)]
    return [F((-1)**(N-q*k)*comb(n+p*(k+1), N-q*k))
            for k in range(N//q+1)]


def binomial_gf(p, q, b, nmax):
    """Obtain coefficients from Q(z;x)F(z;x)=z^(b-1)(1+z)^(q-b)."""
    m = p+q
    arr = []
    for n in range(nmax+1):
        value = [F(comb(q-b, n-b+1))] if b-1 <= n <= q-1 else [F(0)]
        for j in range(1, min(m, n)+1):
            value = add(value, scale(arr[n-j], -comb(m, j)))
        if n >= q:
            value = add(value, [F(0)]+arr[n-q])
        arr.append(trim(value))
    return arr


def check_binomial(p, q, b, n, coeffs, side):
    ctx = dict(p=p, q=q, component=b, n=n, side=side)
    check(f'{side}_closed_vs_gf', coeffs, binomial_closed(p,q,b,n), ctx)
    N = n-b+1
    if N < 0:
        check(f'{side}_zero_components', coeffs, [F(0)], ctx)
        return
    d = N//q
    m = p+q
    for k, ck in enumerate(coeffs):
        expected = F((-1)**(N-q*k)*factorial(n+p+p*k),
                     factorial(N-q*k)*factorial(p+b-1+m*k))
        check(f'{side}_factorial_coefficients', ck, expected, (ctx,k))

    def D(k):
        return prod(m*k+b-q+j for j in range(m))

    def R(k):
        return prod(p*k+n+p+j for j in range(1,p+1))*prod(q*k-N+j for j in range(q))

    for k in range(d+2):
        ck = coeffs[k] if k <= d else 0
        cp = coeffs[k-1] if 1 <= k <= d+1 else 0
        check(f'{side}_euler_ode_coefficients', D(k)*ck, R(k-1)*cp, (ctx,k))
    check(f'{side}_ode_constant_boundary', D(0), 0, ctx)
    check(f'{side}_ode_terminal_boundary', R(d), 0, ctx)

    top = [F(n+p+i,p) for i in range(1,p+1)] + [F(-N+j,q) for j in range(q)]
    bottom = [1+F(b-q+j,m) for j in range(m) if j != q-b]
    c = F(m**m, p**p*q**q)
    check(f'{side}_hypergeometric_parameter_count', (len(top),len(bottom)), (m,m-1), ctx)
    check(f'{side}_omitted_bottom_parameter', 1+F(b-q+(q-b),m), 1, ctx)
    assert all(v > 0 for v in bottom)
    term = F((-1)**N*comb(n+p,N))
    for k in range(d+2):
        check(f'{side}_hypergeometric_coefficients', term,
              coeffs[k] if k <= d else 0, (ctx,k))
        term *= prod(v+k for v in top)
        term /= prod(v+k for v in bottom)*(k+1)*c


def root_check(Q, roots, NB, NA, nmax, context):
    m = len(Q)-1
    Qv = list(reversed(Q))
    dQ, dQv = deriv(Q), deriv(Qv)
    directB = series(NB,Q,nmax)
    directA = series(NA,Qv,nmax)
    for z in roots:
        check('root_vanishing', ev(Q,z), 0, (context,z))
        assert z != 0 and ev(dQ,z) != 0
        check('reciprocal_derivative', ev(dQv,1/z), -z**(2-m)*ev(dQ,z), (context,z))
    for n in range(nmax+1):
        rb = -sum(ev(NB,z)/(ev(dQ,z)*z**(n+1)) for z in roots)
        ra = sum(ev(NA,1/z)*z**(n+m-1)/ev(dQ,z) for z in roots)
        check('right_root_formula', rb, directB[n], (context,n))
        check('left_root_formula', ra, directA[n], (context,n))


def shift_polynomial(a, rho):
    """Coefficients of a(rho+w), exactly; these are a^(k)(rho)/k!."""
    return [sum(a[j]*comb(j,k)*rho**(j-k) for j in range(k,len(a)))
            for k in range(len(a))]


def confluent_check(D, root_multiplicities, numerator, nmax, context):
    degree=sum(mu for rho,mu in root_multiplicities)
    assert len(D)==degree+1 and len(numerator)<=degree
    gamma={}
    reconstructed=[D[-1]]
    for rho,mu in root_multiplicities:
        assert rho != 0
        for _ in range(mu):
            reconstructed=mul(reconstructed,[-rho,F(1)])
    check('confluent_denominator_reconstruction',reconstructed,D,context)
    for j,(rho,mu) in enumerate(root_multiplicities):
        Dj=[D[-1]]
        for i,(other,v) in enumerate(root_multiplicities):
            if i != j:
                for _ in range(v):
                    Dj=mul(Dj,[-other,F(1)])
        taylor=series(shift_polynomial(numerator,rho),shift_polynomial(Dj,rho),mu-1)
        for r in range(1,mu+1):
            gamma[j,r]=taylor[mu-r]
    direct=series(numerator,D,nmax)
    for n in range(nmax+1):
        value=sum((-1)**r*gamma[j,r]*comb(n+r-1,r-1)*rho**(-n-r)
                  for j,(rho,mu) in enumerate(root_multiplicities)
                  for r in range(1,mu+1))
        check('confluent_root_formula',value,direct[n],(context,n))
    return gamma


def check_differential_leading(p,q,b,n):
    m=p+q
    N=n-b+1
    D=[F(1)]
    for j in range(m):
        D=mul(D,[F(b-q+j),F(m)])
    R=[F(1)]
    for j in range(1,p+1):
        R=mul(R,[F(n+p+j),F(p)])
    for j in range(q):
        R=mul(R,[F(-N+j),F(q)])
    S=[[0]*(m+1) for _ in range(m+1)]
    S[0][0]=1
    for k in range(1,m+1):
        for r in range(1,k+1):
            S[k][r]=r*S[k-1][r]+S[k-1][r-1]
    c=F(m**m,p**p*q**q)
    ctx=(p,q,b,n)
    ordinary=[]
    for r in range(m+1):
        ds=sum(D[k]*S[k][r] for k in range(r,m+1))
        rs=sum(R[k]*S[k][r] for k in range(r,m+1))
        # Before division by x, coefficient of derivative r is x^r(ds-x*rs).
        if r==0:
            check('differential_common_x',ds,0,ctx)
            ordinary.append([-rs])
        else:
            ordinary.append([F(0)]*(r-1)+[ds,-rs])
    expected=[F(0)]*(m-1)+[F(m**m),F(-p**p*q**q)]
    check('differential_highest_derivative',ordinary[m],expected,ctx)
    # The zeros of the top coefficient cannot be removed as common factors.
    check('differential_nonzero_first_derivative_at_zero',ev(ordinary[1],F(0)),ev(D,F(1)),ctx)
    assert ev(ordinary[1],F(0))>0
    at_c=ev(ordinary[m-1],c)
    check('differential_penultimate_derivative_at_c',at_c,c**(m-2)*m**m*(F(1,2)-m),ctx)
    assert at_c != 0


def main():
    # Broad exact checks, including every component, zero components, n=0,
    # constant polynomials, highest coefficient and the next (zero) coefficient.
    nmax = 36
    for p in range(1,7):
        for q in range(1,7):
            for b in range(1,q+1):
                arr = binomial_gf(p,q,b,nmax)
                for n, c in enumerate(arr):
                    check_binomial(p,q,b,n,c,'right')
            for a in range(1,p+1):
                arr = binomial_gf(q,p,a,nmax)
                for n,c in enumerate(arr):
                    check_binomial(q,p,a,n,c,'left')

    for n in range(61):
        c = binomial_closed(1,1,1,n)
        for k in range(n+1):
            ck1 = c[k+1] if k < n else 0
            residual = (k+1)*(4*k+6)*ck1+(n*(n+2)-k*(k+2))*c[k]
            check('classical_Chebyshev_ODE',residual,0,(n,k))

    for p in range(1,7):
        for q in range(1,7):
            for b in range(1,q+1):
                for n in sorted({b-1,b,b+q-1,b+q,b+2*q+3}):
                    check_differential_leading(p,q,b,n)

    # Actual ordered-root families, at x=0. Nonunit omega checks scaling.
    for p,q in [(1,1),(1,3),(3,1),(2,2),(2,3),(3,2),(3,3),(4,2)]:
        m=p+q
        beta=[F(j+2,j+1) for j in range(m)]
        omega=F(2,3)
        Q=scale(linear_product(beta),omega)
        roots=[-1/v for v in beta]
        eta,xi=beta[:q],beta[q:]
        xiv=[1/v for v in reversed(xi)]
        for b in range(1,q+1):
            NB=[F(0)]*(b-1)+scale(linear_product(eta[:q-b]),omega)
            for a in range(1,p+1):
                NA=[F(0)]*(a-1)+scale(linear_product(xiv[:p-a]),Q[-1])
                root_check(Q,roots,NB,NA,18,dict(kind='ordered_toeplitz_x0',p=p,q=q,a=a,b=b))

    # Nonzero x in the actual binomial (p,q)=(2,2) family: all roots rational.
    # (1+z)^4-(625/36)z^2 has roots 3/2,2/3,-6,-1/6.
    Q=[F(1),F(4),F(6)-F(625,36),F(4),F(1)]
    roots=[F(3,2),F(2,3),F(-6),F(-1,6)]
    for a in (1,2):
        for b in (1,2):
            NB=[F(0)]*(b-1)+linear_product([F(1)]*(2-b))
            NA=[F(0)]*(a-1)+linear_product([F(1)]*(2-a))
            root_check(Q,roots,NB,NA,25,dict(kind='binomial_nonzero_x',p=2,q=2,x='625/36',a=a,b=b))

    # Full confluence at x=0, including cancellation in each numerator.
    for p in range(1,5):
        for q in range(1,5):
            m=p+q
            D=[F(comb(m,j)) for j in range(m+1)]
            for b in range(1,q+1):
                NB=[F(0)]*(b-1)+linear_product([F(1)]*(q-b))
                gamma=confluent_check(D,[(F(-1),m)],NB,20,dict(kind='binomial_x0_B',p=p,q=q,b=b))
                for r in range(p+b+1,m+1):
                    check('confluent_cancelled_poles',gamma[0,r],0,(p,q,b,r))
            for a in range(1,p+1):
                NA=[F(0)]*(a-1)+linear_product([F(1)]*(p-a))
                gamma=confluent_check(D,[(F(-1),m)],NA,20,dict(kind='binomial_x0_A',p=p,q=q,a=a))
                for r in range(q+a+1,m+1):
                    check('confluent_cancelled_poles',gamma[0,r],0,(p,q,a,r))

    # Mixed multiplicities in an actual ordered-root family, with x=0.
    p,q=2,3
    beta=[F(2),F(2),F(1),F(1),F(3)]
    omega=F(2,3)
    D=scale(linear_product(beta),omega)
    roots_mu=[(F(-1,2),2),(F(-1),2),(F(-1,3),1)]
    for b in range(1,q+1):
        NB=[F(0)]*(b-1)+scale(linear_product(beta[:q-b]),omega)
        confluent_check(D,roots_mu,NB,25,dict(kind='mixed_multiplicities_B',b=b))
    for a in range(1,p+1):
        xiv=[1/v for v in reversed(beta[q:])]
        NA=[F(0)]*(a-1)+scale(linear_product(xiv[:p-a]),D[-1])
        confluent_check(list(reversed(D)),[(1/rho,mu) for rho,mu in roots_mu],NA,25,
                        dict(kind='mixed_multiplicities_A',a=a))

    # Scalar upper support endpoint x=4: Q=(z-1)^2 and U_n(1)=n+1.
    D=[F(1),F(-2),F(1)]
    confluent_check(D,[(F(1),2)],[F(1)],60,dict(kind='scalar_Chebyshev_x4'))
    for n,value in enumerate(series([F(1)],D,60)):
        check('scalar_endpoint_x4',value,n+1,n)

    # The partial-fraction step is universal for any proper numerator and
    # simple nonzero roots. These tests exercise arbitrary signed rational roots.
    for m in range(2,9):
        roots=[F((-1)**j*(j+1),j+2) for j in range(m)]
        Q=[F(3,7)]
        for z in roots:
            Q=mul(Q,[-z,F(1)])
        for q in range(1,m):
            p=m-q
            NB=[F(j+1,j+2) for j in range(q)]
            NA=[F((-1)**j*(j+2),j+3) for j in range(p)]
            root_check(Q,roots,NB,NA,20,dict(kind='general_rational',p=p,q=q))

    report={
        'status':'PASS',
        'arithmetic':'Exact rational arithmetic; Python Fraction/comb/factorial; no sympy.',
        'counts':dict(sorted(COUNTS.items())),
        'total_exact_equalities':sum(COUNTS.values()),
        'ranges':{'binomial_p_q':'1..6 independently','binomial_n':'0..36','components':'all allowed a,b',
                  'classical_n':'0..60','root_cases':'ordered Toeplitz x=0 plus universal proper rational functions, degrees2..8'},
        'scope':[
            'Closed coefficient formula agrees with independently reconstructed generating functions.',
            'All coefficients of Euler ODE checked, including k=0 and k=d+1.',
            'Terminating hypergeometric coefficients and parameter omission checked, including zero terminal term.',
            'Left binomial formulas checked with p/q exchanged.',
            'Right and left finite-root formulas agree with exact formal division at rational roots.',
            'Confluent derivative coefficients checked through exact Taylor expansion, including mixed multiplicities and cancelled poles.',
            'Actual binomial p=q=2 evaluated at x=625/36 with rational simple roots; scalar x=4 double root checked.',
            'Highest differential coefficient after cancellation of x checked, and nonremovable finite singular points 0,c verified.',
            'No floating-point root finding; mpmath unavailable in the selected runtime.'
        ],
        'algebraic_derivation':{
            'ODE':'For k>=1, D(k)c_k=R(k-1)c_(k-1). At k=0, D(0)=0 because j=q-b. At k=d+1, R(d)=0 because j=N-qd lies in {0,...,q-1}.',
            'hypergeometric':'The factorial coefficient quotient gives p numerator parameters and q numerator parameters; the m denominator parameters include exactly one 1, at j=q-b. Removing it supplies k!, and the scaling is p^p*q^q/m^m=1/c.',
            'root_right':'For simple nonzero roots, N/Q=sum_j N(z_j)/(Qprime(z_j)*(z-z_j)); expansion at z=0 gives the minus sign and z_j^(-n-1).',
            'root_left':'Qvee(w)=w^m Q(1/w), hence (Qvee)prime(1/z_j)=-z_j^(2-m)Qprime(z_j). Substitution in the right residue formula gives the positive sign and z_j^(n+m-1).',
            'classical':'At p=q=b=1 the Euler operator is x times [x(4-x)ypp+(6-3x)yp+n(n+2)y]. Polynomial identity permits canceling x.',
            'confluent':'gamma_(j,r) is the coefficient of w^(mu_j-r) in N(rho_j+w)/D_j(rho_j+w), namely the stated derivative divided by factorial.',
            'singularities':'After division by x, highest coefficient is p^p q^q x^(m-1)(c-x). First-derivative coefficient at0 is D(1)>0; derivative-(m-1) coefficient atc is c^(m-2)m^m(1/2-m), nonzero. Thus neither top-coefficient zero is a removable common scalar factor.',
        },
        'assumptions':[
            'p,q>=1; 1<=b<=q and 1<=a<=p.',
            'Hypergeometric formula is stated for n>=b-1 (left: n>=a-1); earlier components vanish.',
            'Finite-root formulas require all m roots of Q simple; omega and the extreme coefficient are nonzero, hence no root is zero.',
            'Repeated roots are handled by the derivative/principal-part formula, as independently checked.'
        ]
    }
    out=Path(__file__).with_suffix('.json')
    out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':report['status'],'total_exact_equalities':report['total_exact_equalities'],'report':str(out)}))


if __name__=='__main__':
    main()
