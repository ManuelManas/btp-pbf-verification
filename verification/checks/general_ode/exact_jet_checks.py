#!/usr/bin/env python3
"""Exact rational audit of the general-symbol differential construction.

Uses no symbolic/numerical packages. Truncated x-jets in Q[z]/(P-xz^q)
compute the derivatives of every algebraic branch. A separate formal power
series recursion computes the polynomial, against which all traces and a
Krylov annihilator are checked exactly.
"""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json, time

def pmul(a,b):
 c=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b): c[i+j]+=x*y
 return c

def poly_from_roots(beta,omega=1):
 a=[F(omega)]
 for b in beta: a=pmul(a,[F(1),F(b)])
 return a

def gauss(A,b):
 n=len(A); M=[list(row)+[v] for row,v in zip(A,b)]
 for j in range(n):
  i=next(i for i in range(j,n) if M[i][j])
  M[i],M[j]=M[j],M[i]
  t=M[j][j]; M[j]=[v/t for v in M[j]]
  for i in range(n):
   if i!=j and M[i][j]:
    t=M[i][j]; M[i]=[v-t*w for v,w in zip(M[i],M[j])]
 return [M[i][-1] for i in range(n)]

def nullvector(columns):
 # An exact nonzero dependence, with last free column chosen.
 rows=len(columns[0]); cols=len(columns)
 M=[[columns[j][i] for j in range(cols)] for i in range(rows)]
 piv=[]; r=0
 for c in range(cols):
  p=next((i for i in range(r,rows) if M[i][c]),None)
  if p is None: continue
  M[r],M[p]=M[p],M[r]
  v=M[r][c]; M[r]=[t/v for t in M[r]]
  for i in range(rows):
   if i!=r and M[i][c]:
    v=M[i][c]; M[i]=[t-v*u for t,u in zip(M[i],M[r])]
  piv.append(c); r+=1
  if r==rows: break
 free=[c for c in range(cols) if c not in piv]
 c=free[-1]; ans=[F(0)]*cols; ans[c]=1
 for i,p in enumerate(piv): ans[p]=-M[i][c]
 return ans

class JetAlgebra:
 def __init__(self,P,q,x0,L):
  self.P=list(map(F,P)); self.q=q; self.x0=F(x0); self.m=len(P)-1; self.L=L
  self.Q=self.P[:]; self.Q[q]-=F(x0)
  self.zero=lambda:[F(0)]*(L+1)
  self.one=self.scalar(1)
 def scalar(self,x):
  a=[self.zero() for _ in range(self.m)]; a[0][0]=F(x); return a
 def frompoly(self,a):
  out=[self.zero() for _ in range(self.m)]
  for i,v in enumerate(a): out[i][0]=F(v)
  return out
 def add(self,a,b): return [[v+w for v,w in zip(x,y)] for x,y in zip(a,b)]
 def scale(self,a,s): return [[v*s for v in x] for x in a]
 def conv(self,a,b):
  c=self.zero()
  for i,x in enumerate(a):
   if x:
    for j in range(self.L+1-i):
     if b[j]: c[i+j]+=x*b[j]
  return c
 def mul(self,a,b):
  L=self.L; m=self.m; c=[self.zero() for _ in range(2*m-1)]
  for i,x in enumerate(a):
   if any(x):
    for j,y in enumerate(b):
     if any(y):
      t=self.conv(x,y); c[i+j]=[v+w for v,w in zip(c[i+j],t)]
  for h in range(2*m-2,m-1,-1):
   v=c[h]
   if not any(v): continue
   for j in range(m):
    factor=-self.Q[j]/self.P[m]
    for t in range(L+1): c[h-m+j][t]+=factor*v[t]
   for t in range(1,L+1): c[h-m+self.q][t]+=v[t-1]/self.P[m]
  return c[:m]
 def power(self,a,n):
  b=self.one
  while n:
   if n%2: b=self.mul(a,b)
   a=self.mul(a,a); n//=2
  return b
 def inv(self,a):
  mat=[]
  for i in range(self.m):
   e=self.frompoly([0]*i+[1]); mat.append([v[0] for v in self.mul(a,e)])
  sol=gauss(list(map(list,zip(*mat))),[F(1)]+[F(0)]*(self.m-1))
  ans=self.frompoly(sol); precision=1
  while precision<=self.L:
   ans=self.mul(ans,self.add(self.scalar(2),self.scale(self.mul(a,ans),-1)))
   precision*=2
  assert self.mul(a,ans)==self.one
  return ans
 def dx(self,a): return [[(i+1)*x[i+1] for i in range(self.L)]+[F(0)] for x in a]
 def dz(self,a): return [[(i+1)*v for v in a[i+1]] for i in range(self.m-1)]+[self.zero()]
 def setup(self):
  self.z=self.frompoly([0,1]); self.zi=self.inv(self.z)
  qz=self.frompoly([i*self.P[i] for i in range(1,self.m+1)])
  qz[self.q-1][0]-=self.q*self.x0
  qz[self.q-1][1]-=self.q
  self.qzi=self.inv(qz)
  self.velocity=self.mul(self.power(self.z,self.q),self.qzi)
  self.logvel=self.mul(self.velocity,self.zi)
 def deriv(self,a,n):
  return self.add(self.dx(a),self.add(self.mul(self.velocity,self.dz(a)),self.scale(self.mul(self.logvel,a),-n)))
 def trace_at_zero(self,a):
  # Newton identities: s_k=sum roots^k, k<=m-1.
  s=[F(self.m)]
  for k in range(1,self.m):
   value=-k*self.Q[self.m-k]/self.P[self.m]
   for j in range(1,k): value-=self.Q[self.m-j]/self.P[self.m]*s[k-j]
   s.append(value)
  return sum(a[k][0]*s[k] for k in range(self.m))

def gf_polynomial(P,q,N,n):
 # y_r=(N_r-sum_{j>=1} P_j y_{r-j}+x y_{r-q})/P0.
 ys=[]
 for r in range(n+1):
  y=[F(0)]*(r//q+1)
  if r<len(N): y[0]=N[r]
  for j in range(1,min(r,len(P)-1)+1):
   for k,v in enumerate(ys[r-j]): y[k]-=P[j]*v
  if r>=q:
   for k,v in enumerate(ys[r-q]): y[k+1]+=v
  ys.append([v/P[0] for v in y])
 return ys[n]

def derivative_at(a,j,x):
 return sum(v*F(factorial(k),factorial(k-j))*x**(k-j) for k,v in enumerate(a) if k>=j)

def run_case(P,q,N,n,x0):
 m=len(P)-1; alg=JetAlgebra(P,q,x0,m+1); alg.setup()
 f=alg.mul(alg.frompoly(N),alg.mul(alg.zi,alg.qzi))
 vals=[]; tracevals=[]; invpower=alg.power(alg.zi,n)
 y=gf_polynomial(P,q,N,n)
 for j in range(m+1):
  vals.append([v[0] for v in f]); tr=alg.trace_at_zero(alg.mul(invpower,f))
  expected=-derivative_at(y,j,F(x0))
  assert tr==expected,(m,q,n,x0,j,tr,expected)
  tracevals.append(tr)
  if j<m: f=alg.deriv(f,n)
 coeff=nullvector(vals)
 assert any(coeff)
 assert all(sum(coeff[j]*vals[j][i] for j in range(m+1))==0 for i in range(m))
 assert sum(coeff[j]*derivative_at(y,j,F(x0)) for j in range(m+1))==0
 return {'m':m,'q':q,'n':n,'x0':str(x0),'numerator':[str(v) for v in N],
         'order_at_sample':max(j for j,c in enumerate(coeff) if c),
         'checks':m+3,'polynomial_degree':max((i for i,c in enumerate(y) if c),default=-1),
         'sample_coefficients':[str(c) for c in coeff]}

def main():
 start=time.time(); results=[]
 configurations=[
  (2,2,[4,3,2,1],2),
  (3,2,[6,4,3,2,1],3),
  (2,2,[1,1,1,1],2),
  (3,2,[3,3,2,1,1],2)]
 for p,q,beta,x0 in configurations:
  P=poly_from_roots(beta)
  # Both the right (q) and reversed left (p) numerators.
  for side in ('right','left'):
   if side=='right': D=P; w=q; pars=list(map(F,beta[:q])); omega=P[0]
   else: D=P[::-1]; w=p; pars=[1/F(v) for v in reversed(beta[q:])]; omega=P[-1]
   for b in range(1,w+1):
    N=[F(0)]*(b-1)+poly_from_roots(pars[:w-b],omega)
    for n in (b-1,b+4,b+10):
     r=run_case(D,w,N,n,x0); r.update(p=p,q_original=q,side=side,b=b,beta=beta)
     results.append(r)
     print(p,q,side,b,n,'ok',flush=True)
 report={'method':'exact rational Taylor jets and independent formal coefficient recurrence',
         'elapsed_seconds':round(time.time()-start,3),'cases':len(results),
         'checks':sum(r['checks'] for r in results),'all_passed':True,'results':results}
 out=Path(__file__).with_name('exact_jet_checks.json'); out.write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:v for k,v in report.items() if k!='results'}),flush=True)
if __name__=='__main__': main()
