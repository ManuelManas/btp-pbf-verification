"""Independent finite and numerical checks; these do not replace the proofs.
Run with Python 3, numpy and mpmath. No network or manuscript edits.
"""
from fractions import Fraction as F
from pathlib import Path
from collections import Counter
import itertools, json, sys
for parent in Path(__file__).resolve().parents:
    deps=parent/'research/btp_audit_v63_2026-10-13/python_deps'
    if deps.is_dir(): sys.path.insert(0,str(deps)); break
import numpy as np
import mpmath as mp

counts=Counter(); records=[]
def det(A):
    A=[list(row) for row in A]; n=len(A); out=F(1)
    for k in range(n):
        pivot=next((i for i in range(k,n) if A[i][k]),None)
        if pivot is None:return F(0)
        if pivot!=k:A[pivot],A[k]=A[k],A[pivot];out=-out
        a=A[k][k];out*=a
        for i in range(k+1,n):
            r=A[i][k]/a
            for j in range(k+1,n): A[i][j]-=r*A[k][j]
    return out
def coeffs(beta):
    c=[F(1)]
    for b in beta:
        d=[F(0)]*(len(c)+1)
        for i,v in enumerate(c):d[i]+=v;d[i+1]+=b*v
        c=d
    return c
def hs(den,L):
    h=[den[0]*0+1]
    for n in range(1,L+1): h.append(-sum(den[j]*h[n-j] for j in range(1,min(n,len(den)-1)+1)))
    return h
def schur(lam,h,detfun=det):
    if not lam:return h[0]
    A=[[h[v-i+j] if v-i+j>=0 else h[0]*0 for j in range(len(lam))] for i,v in enumerate(lam)]
    return detfun(A)
def data(c,p,q,x,N):
    d=c.copy();d[q]-=x
    hz=hs([v/d[-1] for v in d[::-1]],N+p+2)
    hi=hs([v/d[0] for v in d],N+q+2)
    left=[schur([N]*(p-1)+[n],hz) for n in range(N+1)]
    right=[schur([N]*(q-1)+[n],hi) for n in range(N+1)]
    return left,right,hz,hi
def matrix(c,q,x,N):
    return [[(x if i==j else 0)-(c[q+i-j] if 0<=q+i-j<len(c) else 0) for j in range(N)] for i in range(N)]
def adj(A,i,j):
    return (-1)**(i+j)*det([[v for col,v in enumerate(row) if col!=i] for r,row in enumerate(A) if r!=j])
def eq(a,b,kind):
    assert a==b,(kind,a,b);counts[kind]+=1

for p,q in [(1,1),(1,3),(3,1),(2,2),(3,2),(2,3)]:
    for beta in ([F(1)]*(p+q),[F(i+1) for i in range(p+q)]):
        c=coeffs(beta)
        for N in range(6):
            cm=(-1)**((p-1)*N)*c[-1]**N
            cp=(-1)**((q-1)*N)*c[0]**N
            for x in [F(-2),F(0),F(7)]:
                Q,R,hz,hi=data(c,p,q,x,N)
                M=matrix(c,q,x,N+1)
                chi=det(matrix(c,q,x,N))
                eq(cm*Q[N],chi,'Schur characteristic left')
                eq(cp*R[N],chi,'Schur characteristic right')
                for n in range(N+1):
                    eq(cm*Q[n],adj(M,N,n),'left cofactor')
                    eq(cp*R[n],adj(M,n,N),'right cofactor')
                for k,answer in [(0,(-1)**N*chi),(1,cm*Q[0]),(-1,cp*R[0])]:
                    if not (-q<k<p):continue
                    d=c.copy();d[q]-=x
                    D=det([[d[q+i-j+k] if 0<=q+i-j+k<len(d) else F(0) for j in range(N)] for i in range(N)])
                    eq(D,answer,'shifted determinant')
                y=x+F(2,3);Qy,Ry,_,_=data(c,p,q,y,N)
                chin=det(M);chiy=det(matrix(c,q,y,N));chiny=det(matrix(c,q,y,N+1))
                eq(cm*cp*sum(Q[i]*Ry[i] for i in range(N+1)),(chin*chiy-chi*chiny)/(x-y),'finite CD')
                dchin=sum(adj(M,i,i) for i in range(N+1))
                Msmall=matrix(c,q,x,N)
                dchi=sum(adj(Msmall,i,i) for i in range(N))
                diagonal=cm*cp*sum(Q[i]*R[i] for i in range(N+1))
                eq(diagonal,dchin*chi-dchi*chin,'diagonal CD')
                assert diagonal>0;counts['positive diagonal']+=1

# Check the subset expansion separately, on rational roots without collisions.
for m in range(2,7):
    z=[F(i+1,2) for i in range(m)]
    den=coeffs([-v for v in z]);h=hs(den,12)
    for d in range(m):
        for N in [1,2,4]:
            for n in range(N+1):
                value=F(0)
                for I in itertools.combinations(range(m),d):
                    J=[j for j in range(m) if j not in I]
                    pref=F(1)
                    for i in I:
                        pref*=z[i]**N
                        for j in J:pref/=1-z[j]/z[i]
                    value+=pref*hs(coeffs([-z[j] for j in J]),n)[n]
                eq(value,schur([N]*d+[n],h),'subset Schur expansion')

# Equal-modulus pair locations, including repeated symbol roots.
rng=np.random.default_rng(41)
for p,q in [(1,3),(3,1),(2,2),(2,3),(3,2),(3,3),(4,2)]:
    for beta in [np.ones(p+q),np.linspace(.5,2,p+q),np.exp(rng.uniform(-.8,.8,p+q))]:
        c=np.array([1.])
        for b in beta:c=np.polynomial.polynomial.polymul(c,[1.,b])
        for x in np.r_[-np.geomspace(.003,1000,70),np.geomspace(.003,1000,70)]:
            d=c.copy();d[q]-=x
            z=np.roots(d[::-1]);z=z[np.argsort(np.abs(z))]
            for j in range(len(z)-1):
                if abs(z[j].imag)>1e-7 and abs(z[j]-z[j+1].conjugate())<1e-7*(1+abs(z[j])):
                    assert np.sign(x)==(-1.)**(j+1-q)
                    counts['alternating semiaxis numerical pairs']+=1

# High-precision limits for a quartic with four distinct negative symbol roots.
mp.mp.dps=220
c=list(map(mp.mpf,[1,7,14,7,1]));p=q=2;x0=mp.mpf(12)
def md(A):return mp.det(mp.matrix(A)) if A else mp.mpf(1)
def char(N,x):
    d=c.copy();d[q]-=x
    h=hs([v/d[-1] for v in d[::-1]],N+p)
    return (-1)**N*schur([N,N],h,md)
def qr(n,N,x):
    d=c.copy();d[q]-=x;h=hs([v/d[-1] for v in d[::-1]],N+p)
    return schur([N,n],h,md)
def kval(N,x,y):
    f=char(N,x);g=char(N+1,x)
    if x==y:return mp.diff(lambda t:char(N+1,t),x)*f-mp.diff(lambda t:char(N,t),x)*g
    return (g*char(N,y)-f*char(N+1,y))/(x-y)
s=(-7+3*mp.sqrt(5))/2
spectral=hs([mp.mpf(1),-s,mp.mpf(1),-s],5) # (1-st)(1+t^2)
ratio_errors=[]
for N in [6,10,20]:
    errors=[abs(qr(n,N,x0)/qr(0,N,x0)-spectral[n]) for n in range(1,5)]
    ratio_errors.append(float(max(errors)))
    assert max(errors)<{6:mp.mpf('.001'),10:mp.mpf('1e-6'),20:mp.mpf('1e-12')}[N]
    counts['high precision boundary limits']+=4
u=mp.mpf('.3');v=mp.mpf('-.2');varpi=1/(14*mp.pi)
target=mp.sin(mp.pi*(u-v))/(mp.pi*(u-v))
kernel=[]
for N in [20,40,80,120]:
    x=x0+u/(N*varpi);y=x0+v/(N*varpi)
    value=kval(N,x,y)/mp.sqrt(kval(N,x,x)*kval(N,y,y))
    error=abs(value-target)
    assert error<mp.mpf('.65')/N,(N,error)
    kernel.append({'N':N,'value':mp.nstr(value,22),'error':float(error)})
    counts['high precision sine limits']+=1
assert all(kernel[j+1]['error']<kernel[j]['error'] for j in range(len(kernel)-1))
counts['sine error decay']+=1
out={'counts':dict(counts),'total_checks':sum(counts.values()),'boundary_ratio_errors':ratio_errors,'sine_limit_target':mp.nstr(target,22),'sine_limit':kernel,'precision_digits':mp.mp.dps,'formalized_in_Lean':False,'all_passed':True}
Path(__file__).with_name('check_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
