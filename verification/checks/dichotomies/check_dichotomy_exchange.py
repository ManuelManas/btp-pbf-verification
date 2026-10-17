"""Independent finite checks of the displayed formulas, not a proof of infinite assertions."""
from fractions import Fraction as F
from itertools import permutations
from math import prod
from pathlib import Path
import json
import mpmath as mp
counts={};worst={}
def ck(cond,key):
    assert cond,key
    counts[key]=counts.get(key,0)+1
# Both telescoping identities used in the necessity proof, including a sign crossing.
for h in [[F(3)+F((n%5),7) for n in range(55)],[-F(1)-F(n%7,9) for n in range(55)], [F(-3),F(-1),F(1,2),F(3,2)]+[F(2)+F(n%4,8) for n in range(51)]]:
    gamma=[None]+[(h[n]-1)/h[n-1] for n in range(1,len(h))]
    ck(all(x>0 for x in gamma[1:]),'positive weights')
    for start in range(1,20):
        for size in range(1,25):
            end=start+size-1
            if h[start-1]>0:
                rhs=h[end]/h[start-1]*prod((1-1/h[t]) for t in range(start,end+1))
                ck(prod(gamma[start:end+1])==rhs,'forward telescoping identity')
                ck(rhs<=4*(F(3,4)**size),'forward uniform bound')
            elif all(v<0 for v in h):
                v=[-x for x in h]
                rhs=(1+v[start-1])/(1+v[end])*prod(v[t-1]/(1+v[t-1]) for t in range(start,end+1))
                ck(prod(1/g for g in gamma[start:end+1])==rhs,'backward telescoping identity')
                ck(rhs<=5*(F(4,5)**size),'backward uniform bound')
# Shifted pairwise weights for arbitrary periodic orders: period product is exact.
for p in range(2,6):
    patterns=[[F(i+1)*z for z in (F(1,4),F(3),F(4,3))] for i in range(p)]
    for order in permutations(range(p)):
        for i in range(p):
            for k in range(i+1,p):
                for start in range(k-i+1,k-i+5):
                    val=prod(patterns[order[i]][n%3]/patterns[order[k]][(n-k+i)%3] for n in range(start,start+3))
                    ck(val==F(order[i]+1,order[k]+1)**3,'periodic pair product')
# Exchange uses the excess recurrence; check the original UL=L'U' equations independently.
def exchange(u,ell,exact=True):
    size=min(len(u),len(ell)-1)
    d=[u[0]+ell[1]];low=[u[0]*0];delta=u[0]
    for n in range(1,size):
        delta=u[n]*delta/(ell[n]+delta)
        d.append(ell[n+1]+delta)
        low.append(u[n]*ell[n]/d[n-1])
        if exact:
            ck(d[n]+low[n]==u[n]+ell[n+1],'exchange diagonal')
            ck(low[n]*d[n-1]==u[n]*ell[n],'exchange subdiagonal')
            ck(low[n]==u[n]-delta,'exchange swapped-entry identity')
    return low,d

def factor(upper,lower,length,exact):
    conv=F if exact else mp.mpf
    U=[[conv(x)]*length for x in upper];L=[]
    for x in lower:
        v=[conv(0)]+[conv(x)]*(length-1)
        for i in range(len(U)-1,-1,-1):v,U[i]=exchange(U[i],v,exact)
        L.append(v)
    return L,U

def matrix_product(L,U,size):
    mat=[[F(int(i==j)) for j in range(size)] for i in range(size)]
    for low in L:
        mat=[[mat[i][j]+(mat[i][j+1]*low[j+1] if j+1<size else 0) for j in range(size)] for i in range(size)]
    for d in U:
        mat=[[mat[i][j]*d[j]+(mat[i][j-1] if j else 0) for j in range(size)] for i in range(size)]
    return mat
ordered_partitions=0
for m in range(2,6):
    roots=list(range(1,m+1));coef=[F(1)]
    for x in roots:
        coef=[coef[0]]+[coef[j]+x*coef[j-1] for j in range(1,len(coef))]+[x*coef[-1]]
    for order in permutations(roots):
        for q in range(1,m):
            p=m-q;L,U=factor(order[:q],order[q:],18,True)
            # Matrix product with extra rows so upper multiplication cannot cut the target block.
            mat=matrix_product(L,U,4+q)
            for i in range(4):
                for j in range(4):
                    idx=i-j+q;want=coef[idx] if 0<=idx<=m else 0
                    ck(mat[i][j]==want,'all-partition Toeplitz product')
            # Comparator interpretation, independent of numerical limits.
            ups=list(order[:q]);lows=[]
            for x in order[q:]:
                for i in range(q-1,-1,-1):x,ups[i]=min(x,ups[i]),max(x,ups[i])
                lows.append(x)
            ck(sorted(ups)==roots[p:] and sorted(lows)==roots[:p],'limiting group selection')
            ordered_partitions+=1
# High precision tests of limits for every partition at p+q=4, and variable-input swapped limits.
mp.mp.dps=70
maxerr=mp.mpf(0)
for order in permutations([1,2,3,4]):
    for q in range(1,4):
        L,U=factor(order[:q],order[q:],220,False)
        ups=list(order[:q]);lows=[]
        for x in order[q:]:
            for i in range(q-1,-1,-1):x,ups[i]=min(x,ups[i]),max(x,ups[i])
            lows.append(x)
        err=max([abs(x[-1]-v) for x,v in zip(L,lows)]+[abs(x[-1]-v) for x,v in zip(U,ups)])
        maxerr=max(maxerr,err);ck(err<mp.mpf('1e-23'),'all-partition numerical limits')
worst['all_partition_limit_error']=mp.nstr(maxerr,12)
u=[mp.mpf(1)+1/mp.mpf(n+2) for n in range(240)]
ell=[mp.mpf(3)+1/mp.mpf(n+2) for n in range(241)]
low,d=exchange(u,ell,False)
for n in range(1,120):
    delta=d[n]-ell[n+1]
    ck(abs(low[n]-(u[n]-delta))<mp.mpf('1e-65'),'variable-entry swap identity')
    # Input coefficients converge only at rate 1/n; exchanged residual is geometric.
    ck(abs(d[n]-ell[n+1])<=u[0]*mp.mpf('.5')**n,'variable-entry geometric residual')
ck(abs(d[120]-3)>mp.mpf('.007'),'constant-limit convergence need not be geometric')
report={'status':'passed','exact_ordered_partitions':ordered_partitions,'counts':counts,'total_assertions':sum(counts.values()),'numerical':worst,'scope':'Finite exact identities and finite high-precision limit checks; infinite-dimensional and analytic statements are established by the manuscript proofs, not by these computations.'}
Path(__file__).with_name('dichotomy_exchange_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
