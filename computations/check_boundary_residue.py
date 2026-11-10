"""Exact independent residue reconstruction for qt:eq:zero-mass.
Only the displayed p=q=2 finite-boundary example is checked.
"""
from fractions import Fraction as F
from pathlib import Path
import json


def add(A,B): return [[a+b for a,b in zip(ar,br)] for ar,br in zip(A,B)]
def neg(A): return [[-a for a in ar] for ar in A]
def mul(A,B): return [[sum(A[i][k]*B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]
def scale(c,A): return [[c*a for a in ar] for ar in A]
def adj(A): return [[A[1][1],-A[0][1]],[-A[1][0],A[0][0]]]

def root_derivative(z):
    # P(z) = product(1+b*z); implicit Q=P-lambda*z^2.
    pd=sum(F(b)*prod(1+F(c)*z for c in [1,2,3,4] if c!=b) for b in [1,2,3,4])
    return z*z/pd

def prod(xs):
    out=F(1)
    for x in xs: out*=x
    return out

roots=[F(-1,4),F(-1,3),F(-1,2),F(-1)]
droots=[root_derivative(z) for z in roots]
a,b,c,d=roots;ap,bp,cp,dp=droots
g=-a*b;gp=-(ap*b+a*bp)
s=a+b;sp=ap+bp;t=1/c+1/d;tp=-cp/c**2-dp/d**2
G=scale(g,[[1,s],[t,1+s*t]])
Gp=add(scale(gp,[[1,s],[t,1+s*t]]),scale(g,[[0,sp],[tp,sp*t+s*tp]]))
C=[[-31,-5],[-30,-6]];I=[[1,0],[0,1]]
D=add(I,neg(mul(G,C)));Dp=neg(mul(Gp,C))
detp=Dp[0][0]*D[1][1]+D[0][0]*Dp[1][1]-Dp[0][1]*D[1][0]-D[0][1]*Dp[1][0]
H=[[1,0],[4,1]];K=[[1,F(1,2)],[0,1]]
mass=scale(1/detp,mul(mul(mul(H,adj(D)),G),K))
assert G==[[F(-1,12),F(7,144)],[F(1,4),F(-11,48)]]
assert Gp==[[F(-5,72),F(59,864)],[F(13,36),F(-157,432)]]
assert D==scale(F(1,8),[[-1,-1],[7,7]])
assert Dp==scale(F(1,48),[[-5,3],[14,-18]])
assert detp==F(-1,16)
assert mass==[[F(2,3),F(1,9)],[F(2),F(1,3)]]
result={'date':'2026-11-04','arithmetic':'exact fractions','root_derivatives':[str(x) for x in droots],'G':[[str(x) for x in row] for row in G],'G_derivative':[[str(x) for x in row] for row in Gp],'determinant_derivative':str(detp),'mass':[[str(x) for x in row] for row in mass],'checks':6,'passed':True,'scope':'Only the displayed boundary example; does not certify the general boundary theorems.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
