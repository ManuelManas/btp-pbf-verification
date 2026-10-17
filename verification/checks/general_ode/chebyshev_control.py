#!/usr/bin/env python3
from exact_jet_checks import F, pmul, gf_polynomial, JetAlgebra
import json
from pathlib import Path

def add(a,b):
 c=[F(0)]*max(len(a),len(b))
 for i,v in enumerate(a):c[i]+=v
 for i,v in enumerate(b):c[i]+=v
 return c

def scale(a,t): return [v*t for v in a]
def deriv(a): return [i*a[i] for i in range(1,len(a))] or [F(0)]
checks=0
for c0,c1,c2 in ((2,5,2),(1,2,1),(3,8,4)):
 P=list(map(F,(c0,c1,c2))); N=[F(c0)]
 for n in range(21):
  y=gf_polynomial(P,1,N,n)
  residue=add(add(pmul([c1*c1-4*c0*c2,-2*c1,1],deriv(deriv(y))),pmul([-3*c1,3],deriv(y))),scale(y,-n*(n+2)))
  assert not any(residue)
  checks+=1
  for x in (-3,-1,11):
   alg=JetAlgebra(P,1,x,3); alg.setup()
   f0=alg.mul(alg.frompoly(N),alg.mul(alg.zi,alg.qzi)); f1=alg.deriv(f0,n); f2=alg.deriv(f1,n)
   r=alg.add(alg.add(alg.scale(f2,(x-c1)**2-4*c0*c2),alg.scale(f1,3*(x-c1))),alg.scale(f0,-n*(n+2)))
   assert not any(v[0] for v in r)
   checks+=1
report={'case':'p=q=1, arbitrary positive symbol coefficients in three tests','indices':list(range(21)), 'checks':checks,'all_passed':True,'operator':'((x-c1)^2-4*c0*c2)D^2+3(x-c1)D-n(n+2)'}
Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
print(report)
