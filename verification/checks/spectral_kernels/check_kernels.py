"""Independent checks for spectral Chebyshev convolutions and bulk kernels.

Run with the workspace Python; SymPy/mpmath are vendored in the earlier audit.
The numerical tests support the proofs in the companion note; they are not
formal verification. No manuscript or existing delivery is modified.
"""
from pathlib import Path
import sys, json
for parent in Path(__file__).resolve().parents:
    deps = parent / 'research/btp_audit_v63_2026-10-13/python_deps'
    if deps.is_dir():
        sys.path.insert(0, str(deps))
        break
import sympy as sp
import mpmath as mp
mp.mp.dps = 70
HERE = Path(__file__).resolve().parent
checks = []

def record(name, error, tolerance=mp.mpf('1e-48')):
    error = abs(error)
    if error > tolerance:
        raise AssertionError((name, mp.nstr(error, 10), mp.nstr(tolerance, 10)))
    checks.append({'name': name, 'absolute_error': mp.nstr(error, 10),
                   'tolerance': mp.nstr(tolerance, 10)})

def homogeneous(variables, count, exact=False):
    one = sp.Integer(1) if exact else mp.mpf(1)
    out = [one] + [one * 0] * (count - 1)
    for z in variables:
        for n in range(1, count):
            out[n] += z * out[n-1]
    return out

def exact_convolutions():
    r = sp.Rational(3, 2)
    c = sp.Rational(3, 5)
    zeta = r * (c - sp.I * sp.Rational(4, 5))
    small = [sp.Rational(-1, 4), sp.Rational(-1, 3)]
    large = [sp.Rational(-3), sp.Rational(-4)]
    for label, extra, rr in [('left', small, r),
                             ('right', [1/z for z in large], 1/r)]:
        pair = [zeta, sp.conjugate(zeta)] if label == 'left' else [1/zeta, 1/sp.conjugate(zeta)]
        full = homogeneous(extra + pair, 22, exact=True)
        hh = homogeneous(extra, 22, exact=True)
        for n in range(22):
            rhs = sum(hh[j] * rr**(n-j) * sp.chebyshevu(n-j, c) for j in range(n+1))
            assert sp.expand(full[n] - rhs) == 0
            record(f'exact convolution {label} n={n}', 0)

def bisect(fun, lo, hi):
    for _ in range(270):
        mid = (lo+hi)/2
        if fun(mid) > 0:
            hi = mid
        else:
            lo = mid
    return (lo+hi)/2

class Symbol:
    def __init__(self, p, q, betas, omega=1):
        self.p, self.q = p, q
        self.b = sorted([mp.mpf(x) for x in betas], reverse=True)
        self.omega = mp.mpf(omega)
        self.P = [self.omega]
        for b in self.b:
            v = [mp.mpf(0)] * (len(self.P)+1)
            for i, c in enumerate(self.P):
                v[i] += c
                v[i+1] += b*c
            self.P = v
        hi = mp.mpf(1)
        while self.F(hi) < q:
            hi *= 2
        zp = bisect(lambda z: self.F(z)-q, mp.mpf(0), hi)
        self.upper = self.a(zp)
        if self.b[q-1] == self.b[q]:
            self.lower = mp.mpf(0)
        else:
            zm = bisect(lambda z: self.F(z)-q, -1/self.b[q], -1/self.b[q-1])
            self.lower = self.a(zm)

    def F(self, z):
        return sum(b*z/(1+b*z) for b in self.b)

    def a(self, z):
        return mp.polyval(self.P[::-1], z)/z**self.q

    def data(self, x):
        coeff = self.P.copy()
        coeff[self.q] -= x
        roots = mp.polyroots(coeff[::-1], maxsteps=2000, extraprec=150, error=False)
        roots.sort(key=abs)
        mid = roots[self.q-1:self.q+1]
        z = min(mid, key=lambda w: mp.im(w))
        assert mp.im(z) < 0
        r, theta = abs(z), -mp.arg(z)
        small, large = roots[:self.q-1], roots[self.q+1:]
        cm = mp.fprod(1/(1-u/z) for u in small)
        cp = mp.fprod(1/(1-z/v) for v in large)
        rho = -mp.im(z)/(mp.pi*self.omega)*mp.fprod(abs(u) for u in small)
        logder = 1/(x*(self.F(z)-self.q))
        density = mp.im(logder)/mp.pi  # theta' = -Im(z'/z)
        assert density > 0
        return dict(x=x,z=z,r=r,theta=theta,small=small,large=large,
                    cm=cm,cp=cp,rho=rho,logder=logder,d=density)

def scaled_sequences(data, count):
    z, r = data['z'], data['r']
    left = homogeneous([u/r for u in data['small']] + [z/r, mp.conj(z)/r], count)
    right = homogeneous([r/v for v in data['large']] + [r/z, r/mp.conj(z)], count)
    return [mp.re(v) for v in left], [mp.re(v) for v in right]

def kernel(dx, dy, count):
    aa, _ = scaled_sequences(dx, count)
    _, bb = scaled_sequences(dy, count)
    ratio = dx['r']/dy['r']
    return mp.fsum(aa[n]*bb[n]*ratio**n for n in range(count))

def coefficients_from_gf(numerator, denominator, count):
    result=[]
    for n in range(count):
        v = numerator[n] if n < len(numerator) else mp.mpf(0)
        v -= sum(denominator[j]*result[n-j] for j in range(1,min(n,len(denominator)-1)+1))
        result.append(v/denominator[0])
    return result

def ordered_components(symbol, x, count):
    p,q=symbol.p,symbol.q
    eta,xi=symbol.b[:q],symbol.b[q:]
    def numer(base,shift,roots):
        out=[base]
        for z in roots:
            nxt=[mp.mpf(0)]*(len(out)+1)
            for i,c in enumerate(out):
                nxt[i]+=c; nxt[i+1]+=c*z
            out=nxt
        return [mp.mpf(0)]*shift+out
    db=symbol.P.copy(); db[q]-=x
    da=symbol.P[::-1]; da[p]-=x
    B=[coefficients_from_gf(numer(symbol.omega,b-1,eta[:q-b]),db,count) for b in range(1,q+1)]
    xi_dual=[1/v for v in xi[::-1]]
    A=[coefficients_from_gf(numer(symbol.P[-1],a-1,xi_dual[:p-a]),da,count) for a in range(1,p+1)]
    return A,B

def check_components(symbol, data, label):
    count=17
    A,B=ordered_components(symbol,data['x'],count)
    K=mp.matrix([[A[a][n] for n in range(symbol.p)] for a in range(symbol.p)])**-1
    H=mp.matrix([[B[b][n] for b in range(symbol.q)] for n in range(symbol.q)])**-1
    hl=homogeneous(data['small']+[data['z'],mp.conj(data['z'])],count)
    hr=homogeneous([1/v for v in data['large']]+[1/data['z'],1/mp.conj(data['z'])],count)
    g=mp.matrix([hl[:symbol.p]])*K
    f=H*mp.matrix(hr[:symbol.q])
    for n in range(count):
        record(f'{label} left contraction n={n}',sum(g[a]*A[a][n] for a in range(symbol.p))-hl[n],mp.mpf('1e-40'))
        record(f'{label} right contraction n={n}',sum(B[b][n]*f[b] for b in range(symbol.q))-hr[n],mp.mpf('1e-40'))
    # Finite CD: check each component, x != y.
    y=data['x']+mp.mpf('.07')*(symbol.upper-symbol.lower)
    _,By=ordered_components(symbol,y,count)
    N=10
    for a in range(symbol.p):
        for b in range(symbol.q):
            lhs=(data['x']-y)*sum(A[a][n]*By[b][n] for n in range(N))
            rhs=sum(symbol.P[d+symbol.q]*sum(A[a][j+d]*By[b][j] for j in range(N-d,N)) for d in range(1,symbol.p+1))
            rhs-=sum(symbol.P[symbol.q-d]*sum(A[a][i]*By[b][i+d] for i in range(N-d,N)) for d in range(1,symbol.q+1))
            record(f'{label} CD a={a+1},b={b+1}',lhs-rhs,mp.mpf('1e-32'))

def simple_root_poisson(data, r):
    xx=data['small']+[data['z'],mp.conj(data['z'])]
    yy=[1/v for v in data['large']]+[1/data['z'],1/mp.conj(data['z'])]
    cx=[mp.fprod(1/(1-v/u) for j,v in enumerate(xx) if j!=i) for i,u in enumerate(xx)]
    cy=[mp.fprod(1/(1-v/u) for j,v in enumerate(yy) if j!=i) for i,u in enumerate(yy)]
    return sum(cx[i]*cy[j]/(1-r*u*v) for i,u in enumerate(xx) for j,v in enumerate(yy))

def main():
    exact_convolutions()
    cases=[(1,1,[3,1]),(2,1,[5,2,1]),(1,2,[5,2,1]),
           (2,2,[4,3,2,1]),(3,2,[6,3,2,1,'.5']),
           (2,3,[6,3,2,1,'.5']),(3,3,[6,4,3,2,1,'.5']),
           (2,2,[1,1,1,1]),(3,2,[3,2,2,1,1])]
    convergence=[]
    for p,q,b in cases:
        s=Symbol(p,q,b)
        x=s.lower+mp.mpf('.43')*(s.upper-s.lower)
        d=s.data(x)
        label=f'({p},{q}) beta={b}'
        amp=d['rho']*d['cm']*d['cp']/(2*mp.sin(d['theta'])**2)
        record(label+' amplitude identity',amp+1j*d['logder']/mp.pi)
        check_components(s,d,label)
        aa,bb=scaled_sequences(d,450)
        maxratio=max([abs(u)/d['r'] for u in d['small']]+[d['r']/abs(v) for v in d['large']]+[mp.mpf(0)])
        rate=(1+maxratio)/2
        # Two direct asymptotic values; empirical bounds, not a proof of the rate.
        for n in (100,200):
            pa=abs(d['cm'])/mp.sin(d['theta'])*mp.sin((n+1)*d['theta']-mp.arg(d['cm']))
            pb=abs(d['cp'])/mp.sin(d['theta'])*mp.sin((n+1)*d['theta']+mp.arg(d['cp']))
            record(label+f' alpha asymptotic n={n}',aa[n]-pa,100*rate**n+mp.mpf('1e-60'))
            record(label+f' beta asymptotic n={n}',bb[n]-pb,100*rate**n+mp.mpf('1e-60'))
        rr=mp.mpf('.2')
        direct=mp.fsum(rr**n*aa[n]*bb[n] for n in range(160))
        record(label+' rational Poisson',direct-simple_root_poisson(d,rr))
        local=[]
        kappa=mp.re(d['logder'])/d['d']
        for N in (50,100,200,400):
            diag=d['rho']/N*mp.fsum(aa[n]*bb[n] for n in range(N))
            u,v=mp.mpf('.37'),mp.mpf('-.24')
            dx=s.data(x+u/(N*d['d'])); dy=s.data(x+v/(N*d['d']))
            value=d['rho']/(N*d['d'])*mp.exp(-kappa*(u-v))*kernel(dx,dy,N)
            limit=mp.sin(mp.pi*(u-v))/(mp.pi*(u-v))
            local.append({'N':N,'diagonal_error':mp.nstr(abs(diag-d['d']),12),
                          'sine_error':mp.nstr(abs(value-limit),12)})
            record(label+f' diagonal rate N={N}',diag-d['d'],20*(1+d['d'])/N)
            record(label+f' sine rate N={N}',value-limit,20/N)
        convergence.append({'case':label,'x':mp.nstr(x,14),'rho':mp.nstr(d['rho'],14),
                            'limiting_density':mp.nstr(d['d'],14),'gauge_exponent':mp.nstr(kappa,14),
                            'results':local})
        print(label,'OK',local[-1],flush=True)
    report={'precision_decimal_digits':mp.mp.dps,'passed':len(checks),
            'checks':checks,'convergence':convergence,
            'scope':'Exact convolution checks plus numerical tests of proved identities and asymptotic limits. No Lean formalization.'}
    (HERE/'check_results.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASSED',len(checks),flush=True)

if __name__=='__main__':
    main()
