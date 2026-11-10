"""Interior collision of two NONCENTRAL roots; all roots of P are distinct."""
from pathlib import Path
import mpmath as mp
import json
mp.mp.dps=180
beta=[mp.mpf(i) for i in [10,9,8,7,6]]+[mp.mpf(6919)/9439]
x=mp.mpf(38102400)/9439;p=q=3
# Exact algebra: Q(z;x)=(z+1)^2 (209230560 z^4+2060796 z^3+5529884 z^2+365601 z+9439)/9439.
other=mp.polyroots(list(map(mp.mpf,[209230560,2060796,5529884,365601,9439])),maxsteps=5000,extraprec=200)
z=sorted(other+[mp.mpf(-1),mp.mpf(-1)],key=abs)
zeta=min(z[2:4],key=mp.im);small=z[:2];large=z[4:]
assert large==[-1,-1]
c=[mp.mpf(1)]
for b in beta:
    a=[mp.mpf(0)]*(len(c)+1)
    for j,v in enumerate(c):a[j]+=v;a[j+1]+=b*v
    c=a
Q=c[:];Q[q]-=x

def hs(den,N):
    h=[mp.mpf(1)]
    for n in range(1,N+1):h.append(-sum(den[j]/den[0]*h[n-j] for j in range(1,min(n,len(den)-1)+1)))
    return h

def schur(lam,h):
    return mp.det(mp.matrix([[h[r-i+j] if r-i+j>=0 else 0 for j in range(len(lam))] for i,r in enumerate(lam)]))

def hom(vals,N):
    h=[mp.mpf(1)]+[mp.mpf(0)]*N
    for v in vals:
        for n in range(1,N+1):h[n]+=v*h[n-1]
    return h
spectral=hom(small+[zeta,mp.conj(zeta)],5)
r=abs(zeta);theta=-mp.arg(zeta);R=c[-1]*r
V=large+[zeta];U=small+[mp.conj(zeta)]
C=mp.fprod(1/(1-u/v) for v in V for u in U)
records=[]
for N in [10,20,40,80]:
    h=hs(Q[::-1],N+4)
    denom=schur([N,N],h)
    err=max(abs(schur([N,N,n],h)/denom-spectral[n]) for n in range(6))
    chi=c[-1]**N*schur([N,N,N],h)
    er2=abs(chi/R**N-2*abs(C)*mp.cos(N*theta-mp.arg(C)))
    assert err<mp.mpf('.3')**N
    assert er2<mp.mpf('.3')**N
    records.append({'N':N,'boundary_error':mp.nstr(err,20),'characteristic_error':mp.nstr(er2,20)})
result={'p':p,'q':q,'beta':[str(v) for v in [10,9,8,7,6,'6919/9439']],'x':'38102400/9439','colliding_roots':[-1,-1],'location':'two largest roots, inside central support','records':records,'checks':8,'passed':True}
Path(__file__).with_name('collision_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
