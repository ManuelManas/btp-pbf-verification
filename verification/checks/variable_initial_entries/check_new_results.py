"""Finite identity checks; these complement the infinite-dimensional proofs.

Run with Python 3 and sympy. No manuscript files are modified.
"""
from pathlib import Path
from itertools import permutations, combinations
from fractions import Fraction as F
import json, math
import sympy as sp

HERE=Path(__file__).resolve().parent
counts={'free_derivative_entries':0,'compound_entries':0,'schur_companion':0,
        'endpoint_identity':0,'backward_solution':0}

def coeff_product(seqs,N):
    # Row n, subdiagonal s. Right multiplication by each bidiagonal.
    rows=[[F(int(s==0)) for s in range(len(seqs)+1)] for n in range(N+1)]
    for b in seqs:
        prev=[v[:] for v in rows]
        for n in range(1,N+1):
            for s in range(1,min(n,len(seqs))+1):
                rows[n][s]=prev[n][s]+prev[n][s-1]*b[n-s+1]
    return rows

def extraction(seqs,E,N):
    m=len(seqs);a=seqs[0];bs=seqs[1:]
    G=coeff_product(bs,N)
    f={}
    for n in range(m,N+1):
        pi=F(1);total=F(0)
        for r in range(m):
            total+=(-1)**r*pi*E[n-r][m-r]
            pi*=a[n-r]
        f[n]=total
    # Undo D_(m-1),...,D_1; each map drops its first entry.
    v=f
    for j in range(m-1,0,-1):
        b=bs[j-1];h={}
        if a[-1]<b[-1]:
            h[j]=F(0)
            for n in range(j+1,N+1):
                h[n]=(v[n]+a[n]*h[n-1])/b[n-j]
        else:
            h[N]=F(0)
            for n in range(N,j,-1):
                h[n-1]=(b[n-j]*h[n]-v[n])/a[n]
        v=h
    h=v
    R=[[F(0) for _ in range(m)] for _ in range(N+1)]
    for n in range(1,N+1):
        for s in range(1,min(m-1,n)+1):
            pi=F(1)
            for r in range(s):
                R[n][s]+=(-1)**r*pi*(E[n-r][s-r]-h[n-r]*G[n-r-1][s-r-1])
                pi*=a[n-r]
    for n in range(1,N+1):
        for s in range(1,min(m,n)+1):
            actual=h[n]*G[n-1][s-1]
            if s<m:actual+=R[n][s]
            if s>1:actual+=a[n]*R[n-1][s-1]
            assert actual==E[n][s],(m,n,s,actual,E[n][s])
            counts['free_derivative_entries']+=1
    return [h[n] for n in range(1,N+1)],R

# Every ordering, including mixed increasing/decreasing extraction stages.
for p in range(2,6):
    for order in permutations(range(1,p+1)):
        N=14
        seqs=[[F(0)]+[F(c)*(1+F(((i+2)*n)%5-2,30)) if n<6 else F(c)
                     for n in range(1,N+1)] for i,c in enumerate(order)]
        E=[[F(0)]+[F((n*7+s*3)%11-5,7) if s<=n else F(0)
                     for s in range(1,p+1)] for n in range(N+1)]
        # Repeat every extraction, then verify the whole factor derivative.
        errors=[];current=E
        for i in range(p-1):
            hi,current=extraction(seqs[i:],current,N);errors.append(hi)
        errors.append([current[n][1] for n in range(1,N+1)])
        # Independent multiplication in the dual numbers evaluates D Phi.
        val=[[F(int(s==0)) for s in range(p+1)] for _ in range(N+1)]
        der=[[F(0) for _ in range(p+1)] for _ in range(N+1)]
        for a,h in zip(seqs,errors):
            old=[v[:] for v in val];od=[v[:] for v in der]
            for n in range(1,N+1):
                for s in range(1,min(n,p)+1):
                    k=n-s+1
                    val[n][s]=old[n][s]+old[n][s-1]*a[k]
                    der[n][s]=od[n][s]+od[n][s-1]*a[k]+old[n][s-1]*h[k-1]
        for n in range(1,N+1):
            for s in range(1,min(n,p)+1):
                assert der[n][s]==E[n][s]
                counts['free_derivative_entries']+=1

# p=2 backward inverse for finite forcing, with the exact zero tail.
for gamma in [F(3,2),F(2),F(7,3)]:
    forcing={n:F((n*3)%7-3,5) for n in range(2,20)}
    h={n:-sum((f/gamma**(j-n) for j,f in forcing.items() if j>n),F(0))
       for n in range(1,22)}
    for n in range(2,22):
        assert h[n]-gamma*h[n-1]==forcing.get(n,F(0))
        counts['backward_solution']+=1

# Signed-inverse identity, not restricted to constant factors.
N=16
a=[F(0)]+[F(2)+F(1,n+3) for n in range(1,N+1)]
b=[F(0)]+[F(1)-F(1,2*n+5) for n in range(1,N+1)]
def inv(a,n,j):
    return math.prod(a[j+1:n+1],start=F(1)) if n>=j else F(0)
for n in range(1,N+1):
    q0=sum(inv(b,n,j)*inv(a,j,0) for j in range(n+1))
    q1=sum(inv(b,n,j)*inv(a,j,1) for j in range(1,n+1))
    assert q0-a[1]*q1==math.prod(b[1:n+1])
    assert q1>=math.prod(a[2:n+1])
    counts['endpoint_identity']+=1

def complete(roots,limit):
    h=[sp.Integer(1)]+[sp.Integer(0)]*limit
    for z in roots:
        for k in range(1,limit+1):h[k]+=z*h[k-1]
    return lambda k:h[k] if k>=0 else sp.Integer(0)

for roots in [[1,2,3,4],[1,1,2,2],[1,1,1,1],[sp.Rational(1,2),2,2,3,4]]:
    m=len(roots);x=sp.Symbol('x')
    es=[sp.Poly(sp.prod(1+z*x for z in roots),x).nth(j) for j in range(m+1)]
    C=sp.zeros(m)
    for j in range(m):C[0,j]=(-1)**j*es[j+1]
    for j in range(1,m):C[j,j-1]=1
    v=sp.eye(m)[:,0];h=complete(roots,15)
    for N in [0,1,3,5]:
        assert C**N*v==sp.Matrix([h(N-i) for i in range(m)])
        counts['compound_entries']+=m
        for d in range(1,m):
            inds=list(combinations(range(m),d))
            compound=sp.Matrix([[C.extract(i,j).det() for j in inds] for i in inds])
            CN=C**N;CNcompound=compound**N
            assert CNcompound==sp.Matrix([[CN.extract(i,j).det() for j in inds] for i in inds])
            counts['compound_entries']+=len(inds)**2
            for n in range(min(N,3)+1):
                JT=sp.Matrix(d+1,d+1,lambda i,j:h((N if i<d else n)-i+j))
                J=JT.copy()
                for j in range(d+1):
                    col=C**N*C**j*v
                    for i in range(d):J[i,j]=col[i]
                assert J==JT
                functional=0
                for j in range(d+1):
                    columns=[C**t*v for t in range(d+1) if t!=j]
                    W=sp.Matrix.hstack(*columns)
                    minor=sum(CNcompound[inds.index(tuple(range(d))),k]*W.extract(I,range(d)).det()
                              for k,I in enumerate(inds))
                    functional+=(-1)**(d+j)*h(n-d+j)*minor
                assert sp.expand(functional-JT.det())==0
                counts['schur_companion']+=1

result={'status':'passed','counts':counts,'total_exact_assertion_units':sum(counts.values()),
        'scope':'Finite exact identities for new proofs, including all permutations up to p=5 and multiple roots. Not a formal proof of analytic or infinite-dimensional assertions.'}
(HERE/'new_results_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
