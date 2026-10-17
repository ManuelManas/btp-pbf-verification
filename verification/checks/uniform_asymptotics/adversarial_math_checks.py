"""Independent adversarial checks. No manuscript is modified."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import hashlib, json, zipfile, re
import mpmath as mp
HERE=Path(__file__).resolve().parent
counts=Counter(); records=[]
def checked(cond,kind,detail=None):
    if not cond: raise AssertionError((kind,detail))
    counts[kind]+=1

def determinant(A):
    if not A:return F(1)
    A=[list(r) for r in A]; ans=F(1)
    for j in range(len(A)):
        k=next((k for k in range(j,len(A)) if A[k][j]),None)
        if k is None:return F(0)
        if k!=j:A[j],A[k]=A[k],A[j];ans=-ans
        a=A[j][j];ans*=a
        for k in range(j+1,len(A)):
            w=A[k][j]/a
            for h in range(j+1,len(A)):A[k][h]-=w*A[j][h]
    return ans

def poly(beta,omega=F(1)):
    c=[omega]
    for b in beta:
        a=[c[0]*0]*(len(c)+1)
        for j,v in enumerate(c):a[j]+=v;a[j+1]+=b*v
        c=a
    return c

def hs(den,N):
    h=[den[0]*0+1]
    for n in range(1,N+1):h.append(-sum(den[j]/den[0]*h[n-j] for j in range(1,min(n,len(den)-1)+1)))
    return h

def schur(lam,h):
    return determinant([[h[r-i+j] if r-i+j>=0 else h[0]*0 for j in range(len(lam))] for i,r in enumerate(lam)])

def matrix(c,q,x,N):
    return [[(x if i==j else 0)-(c[q+i-j] if 0<=q+i-j<len(c) else 0) for j in range(N)] for i in range(N)]

def cofactor(A,i,j):
    return (-1)**(i+j)*determinant([[v for col,v in enumerate(row) if col!=i] for r,row in enumerate(A) if r!=j])

metadata={}
cases=[(1,4,[1,1,2,2,3]),(4,1,[1,2,2,3,3]),(2,4,[1,1,1,2,3,3]),(4,2,[1,2,2,2,3,3]),(3,3,[1,1,2,2,3,3]),(5,2,[1,1,1,1,1,1,1]),(2,5,[1,2,3,4,5,6,7]),(4,4,[1,1,1,1,2,2,2,2])]
for p,q,beta in cases:
    c=poly(list(map(F,beta)),F(2,3))
    for N in range(7):
        cm=(-1)**((p-1)*N)*c[-1]**N;cp=(-1)**((q-1)*N)*c[0]**N
        for x in [F(-3,7),F(0),F(5,3)]:
            den=c[:];den[q]-=x
            hz=hs(den[::-1],N+p+1);hi=hs(den,N+q+1)
            Q=[schur([N]*(p-1)+[n],hz) for n in range(N+1)]
            R=[schur([N]*(q-1)+[n],hi) for n in range(N+1)]
            M=matrix(c,q,x,N+1);chi=determinant(matrix(c,q,x,N))
            checked(cm*Q[N]==chi,'exact Schur characteristic left')
            checked(cp*R[N]==chi,'exact Schur characteristic right')
            for n in range(N+1):
                checked(cm*Q[n]==cofactor(M,N,n),'exact adjugate left')
                checked(cp*R[n]==cofactor(M,n,N),'exact adjugate right')
            checked(cm*cp*sum(Q[n]*R[n] for n in range(N+1))>0,'exact diagonal kernel positivity')
            for k,want in [(1,cm*Q[0]),(-1,cp*R[0])]:
                if -q<k<p:
                    actual=determinant([[den[q+i-j+k] if 0<=q+i-j+k<len(den) else 0 for j in range(N)] for i in range(N)])
                    checked(actual==want,'exact shifted determinant signs')
print('Exact finite tests completed',sum(counts.values()),flush=True)

mp.mp.dps=180

def bisect(f,a,b):
    for _ in range(650):
        c=(a+b)/2
        if f(c)>0:b=c
        else:a=c
    return (a+b)/2

def spectral_data(beta,p,q,omega,x=None,fraction=mp.mpf('.43')):
    beta=sorted(map(mp.mpf,beta),reverse=True);c=poly(beta,mp.mpf(omega))
    fun=lambda z:sum(b*z/(1+b*z) for b in beta)-q
    a=lambda z:mp.polyval(c[::-1],z)/z**q
    hi=mp.mpf(1)
    while fun(hi)<0:hi*=2
    upper=a(bisect(fun,mp.mpf(0),hi))
    lower=0 if beta[q-1]==beta[q] else a(bisect(fun,-1/beta[q],-1/beta[q-1]))
    if x is None:x=lower+fraction*(upper-lower)
    den=c[:];den[q]-=x
    z=mp.polyroots(den[::-1],maxsteps=4000,extraprec=300)
    z=sorted(z,key=abs);zeta=min(z[q-1:q+1],key=mp.im)
    checked(mp.im(zeta)<0,'interior root pair exists')
    r=abs(zeta);small=z[:q-1];large=z[q+1:]
    theta=-mp.arg(zeta);logder=1/(x*fun(zeta));varpi=mp.im(logder)/mp.pi
    rho=-mp.im(zeta)*mp.fprod(abs(v) for v in small)/(mp.pi*omega)
    ca=mp.fprod(1/(1-v/zeta) for v in small);cb=mp.fprod(1/(1-zeta/v) for v in large)
    checked(abs(rho*ca*cb/(2*mp.sin(theta)**2)+1j*logder/mp.pi)<mp.mpf('1e-120'),'high precision complex amplitude identity')
    return dict(c=c,x=x,z=z,zeta=zeta,r=r,small=small,large=large,d=varpi,rho=rho,p=p,q=q,beta=beta,omega=omega)

def hom(vals,N):
    h=[mp.mpf(1)]+[mp.mpf(0)]*N
    for v in vals:
        for n in range(1,N+1):h[n]+=v*h[n-1]
    return h

def kernel(d1,d2,N):
    ra=d1['r'];rb=d2['r'];za=d1['zeta'];zb=d2['zeta']
    aa=hom([v/ra for v in d1['small']]+[za/ra,mp.conj(za)/ra],N-1)
    bb=hom([rb/v for v in d2['large']]+[rb/zb,rb/mp.conj(zb)],N-1)
    return mp.re(sum(aa[n]*bb[n]*(ra/rb)**(n-N) for n in range(N)))

for p,q,beta in [(1,3,[4,2,2,1]),(3,1,[4,3,3,1]),(2,3,[4,3,2,2,1]),(3,3,[3,3,2,2,1,1]),(4,2,[1,1,1,1,1,1])]:
    d=spectral_data(beta,p,q,mp.mpf('1.3'))
    nrec={'p':p,'q':q,'beta':beta,'x':mp.nstr(d['x'],20),'sine_errors':[]}
    for N in [40,120,360]:
        u=mp.mpf('.23');v=mp.mpf('-.31')
        dx=spectral_data(beta,p,q,d['omega'],d['x']+u/(N*d['d']))
        dy=spectral_data(beta,p,q,d['omega'],d['x']+v/(N*d['d']))
        val=d['rho']/(N*d['d'])*kernel(dx,dy,N)
        target=mp.sin(mp.pi*(u-v))/(mp.pi*(u-v))
        err=abs(val-target)
        nrec['sine_errors'].append({'N':N,'absolute_error':mp.nstr(err,18)})
        checked(err<mp.mpf(8)/N,'high precision asymmetric sine limit',(p,q,N,err))
    records.append(nrec)
    print('Asymptotic case',p,q,beta,'completed',flush=True)

out={'date':'2026-10-17','counts':dict(counts),'total':sum(counts.values()),'metadata':metadata,'asymptotics':records,'all_passed':True,'formal_proof':False}
(HERE/'results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
