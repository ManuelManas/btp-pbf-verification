"""Finite exact checks of the identities explained in section 3, v79.
Uses Python's standard library only. These checks supplement the proofs;
they do not constitute a formal verification of the infinite-dimensional theorems.
"""
from fractions import Fraction as F
from pathlib import Path
from random import Random
import json
rng=Random(16102026)
report={}
def zero(n):return [[F(0) for j in range(n)] for i in range(n)]
def eye(n):
 a=zero(n)
 for i in range(n):a[i][i]=F(1)
 return a
def mul(a,b):
 n=len(a); c=zero(n)
 for i in range(n):
  for k in range(n):
   if a[i][k]:
    for j in range(n):
     if b[k][j]:c[i][j]+=a[i][k]*b[k][j]
 return c
def add(*aa):return [[sum(a[i][j] for a in aa) for j in range(len(aa[0]))] for i in range(len(aa[0]))]
def transpose(a):return list(map(list,zip(*a)))
def bidi(a):
 b=eye(len(a))
 for n in range(1,len(a)):b[n][n-1]=a[n]
 return b
def lowerinv(a):
 n=len(a);v=zero(n)
 for i in range(n):
  v[i][i]=1/a[i][i]
  for j in range(i):v[i][j]=-sum(a[i][k]*v[k][j] for k in range(j,i))/a[i][i]
 return v
def prod(xs):
 z=F(1)
 for x in xs:z*=x
 return z
def sequence(n):return [F(0)]+[F(rng.randrange(1,8),rng.randrange(2,9)) for _ in range(1,n)]
checks=[]
for m in range(2,9):
 n=2*m+5;a=sequence(n);bs=[sequence(n) for j in range(m-1)];G=eye(n)
 for b in bs:G=mul(G,bidi(b))
 operators=[]
 for j in range(1,m):
  dj=zero(n-m)
  for t in range(m,n):
   dj[t-m][t-m]=bs[j-1][t-j]
   if t>m:dj[t-m][t-m-1]=-a[t]
  operators.append(dj)
 P=eye(n-m)
 for dj in operators:P=mul(dj,P)
 expected=zero(n-m)
 for t in range(m,n):
  for r in range(m):
   if t-r>=m:expected[t-m][t-r-m]=(-1)**r*prod(a[t-r+1:t+1])*G[t-r-1][t-m]
 assert P==expected
 E=zero(n)
 for t in range(1,n):
  for s in range(1,min(m,t)+1):E[t][t-s]=F(rng.randrange(-8,9),11)
 f=[sum((-1)**r*prod(a[t-r+1:t+1])*E[t-r][t-m] for r in range(m)) for t in range(m,n)]
 h=[F(0)]*n
 for t in range(m,n):h[t]=(f[t-m]-sum(P[t-m][s-m]*h[s] for s in range(m,t)))/P[t-m][t-m]
 R=zero(n);H=zero(n)
 for t in range(1,n):
  H[t][t-1]=h[t]
  for s in range(1,min(m-1,t)+1):
   R[t][t-s]=E[t][t-s]-h[t]*G[t-1][t-s]-a[t]*R[t-1][t-s]
   explicit=sum((-1)**r*prod(a[t-r+1:t+1])*(E[t-r][t-s]-h[t-r]*G[t-r-1][t-s]) for r in range(s))
   assert explicit==R[t][t-s]
 assert add(mul(H,G),mul(bidi(a),R))==E
 checks.append({'width':m,'rows':n,'first_order_product':True,'remainder_formula_including_initial_rows':True,'full_derivative_equation':True})
report['extraction']=checks
checks=[]
for p,q in [(1,1),(2,1),(3,2),(4,3),(1,4)]:
 n=14;L=eye(n);Ut=eye(n);aa=[sequence(n) for _ in range(p)];bb=[sequence(n) for _ in range(q)]
 for a in aa:L=mul(L,bidi(a))
 for b in bb:Ut=mul(Ut,bidi(b))
 U=transpose(Ut);Li=lowerinv(L);Ui=transpose(lowerinv(Ut));D=zero(n);Di=zero(n)
 for i in range(n):D[i][i]=F(i%4+2,3);Di[i][i]=1/D[i][i]
 E=zero(n)
 for i in range(n):
  for j in range(max(0,i-p),min(n,i+q+1)):E[i][j]=F(rng.randrange(-7,8),9)
 V=mul(mul(Li,E),Ui);Vm=zero(n);V0=zero(n);Vp=zero(n)
 for i in range(n):
  for j in range(n):
   (Vm if i>j else Vp if i<j else V0)[i][j]=V[i][j]
 X=mul(mul(L,Vm),Di);Y=mul(mul(Di,Vp),U)
 assert add(mul(mul(X,D),U),mul(mul(L,V0),U),mul(mul(L,D),Y))==E
 assert all(X[i][j]==0 for i in range(n) for j in range(n) if i<=j or i-j>p)
 assert all(Y[i][j]==0 for i in range(n) for j in range(n) if j<=i or j-i>q)
 # Diagonal perturbation E=I; signed inverse lower bound.
 diagvariation=mul(Li,Ui)
 for i in range(n):
  Q=[(-1)**(i-s)*Li[i][s] for s in range(i+1)]
  Qp=[(-1)**(i-s)*Ui[s][i] for s in range(i+1)]
  rhs=sum(prod(aa[-1][s+1:i+1])*prod(bb[-1][s+1:i+1]) for s in range(i+1))
  assert diagvariation[i][i]==sum(a*b for a,b in zip(Q,Qp))>=rhs
 if p==q==1:
  for i in range(1,n):
   assert V0[i][i]==aa[0][i]*bb[0][i]*V0[i-1][i-1]+E[i][i]-bb[0][i]*E[i][i-1]-aa[0][i]*E[i-1][i]
 checks.append({'p':p,'q':q,'rows':n,'inverse_derivative_identity':True,'band_preservation':True,'positive_diagonal_lower_bound':True})
report['full_ldu']=checks
# Check the combinatorial count used in the near-diagonal inverse estimate.
num=0
for p,q in [(1,1),(2,3),(4,2),(5,5)]:
 h=max(p,q)
 for i in range(20):
  for j in range(20):
   if abs(i-j)>h:continue
   for delta in range(-q,p+1):
    lengths=[]
    for u in range(i+1):
     v=u-delta
     if not 0<=v<=j:continue
     overlap=max(0,min(i,j)-max(u,v));unmatched=(i-u)+(j-v)-2*overlap
     assert unmatched<=2*h
     lengths.append(overlap);num+=1
    assert lengths.count(0)<=2*h+1
    positives=[r for r in lengths if r>0]
    assert len(positives)==len(set(positives))
report['overlap_count']={'terms_checked':num,'all_bounds_hold':True}
report['all_passed']=True
Path(__file__).with_name('stability_details_results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
