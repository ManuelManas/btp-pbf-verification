"""Exact rational certificates for adjacent Metelmann series.

Polynomial sign certificates hold on an entire real half-line: coefficients
of P(N+x) are nonnegative. No finite sampling is used to certify a tail.
"""
from fractions import Fraction as F
from itertools import combinations
from math import comb, factorial, prod
from pathlib import Path
import json

def trim(p):
    p=list(map(F,p))
    while len(p)>1 and not p[-1]: p.pop()
    return p
def add(p,q):
    return trim([(p[i] if i<len(p) else 0)+(q[i] if i<len(q) else 0)
                 for i in range(max(len(p),len(q)))])
def scale(p,c): return trim([c*x for x in p])
def sub(p,q): return add(p,scale(q,-1))
def mul(p,q):
    z=[F(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q): z[i+j]+=a*b
    return trim(z)
def shift(p,N):
    return trim([sum((p[j]*comb(j,i)*F(N)**(j-i) for j in range(i,len(p))),F(0))
                 for i in range(len(p))])
def val(p,n):
    z=F(0)
    for c in reversed(p): z=z*n+c
    return z
def nonnegative(p,N): return all(c>=0 for c in shift(p,N))
def positive(p,N): return nonnegative(p,N) and val(p,N)>0

def rational_tail_certificate(P,Q,start=1):
    """Decide convergence for positive, eventually rational term ratios P/Q.

    The returned start applies to the tail, not to any exceptional prefix.
    P and Q are polynomials with rational coefficients, in ascending order.
    """
    P,Q=trim(P),trim(Q)
    assert P[-1]*Q[-1]>0
    if Q[-1]<0: P,Q=scale(P,-1),scale(Q,-1)
    dp,dq=len(P)-1,len(Q)-1
    c2=None;alpha=None
    if dp<dq: limit=F(0)
    elif dp>dq: limit=None
    else: limit=P[-1]/Q[-1]
    if limit is not None and limit<1:
        typ='convergent';kind='geometric';rho=(1+limit)/2
        potential=[1/(1-rho)]
        residual=sub(sub(mul(potential,Q),mul(shift(potential,1),P)),Q)
        h=F(0)
    elif limit is None or limit>1:
        typ='divergent';kind='nondecreasing';potential=None
        residual=sub(P,Q);h=F(0)
    else:
        p1=P[-2]/P[-1] if dp else F(0)
        q1=Q[-2]/Q[-1] if dq else F(0)
        p2=P[-3]/P[-1] if dp>=2 else F(0)
        q2=Q[-3]/Q[-1] if dq>=2 else F(0)
        alpha=q1-p1
        c2=p2-q2+q1*q1-p1*q1
        if alpha>1:
            typ='convergent';kind='linear-potential'
            potential=[F(0),2/(alpha-1)]
            residual=sub(sub(mul(potential,Q),mul(shift(potential,1),P)),Q)
            h=F(0)
        else:
            typ='divergent';kind='harmonic-comparison';potential=None
            h=c2-2 if alpha==1 else F(0)
            # rho(n) >= (n+h)/(n+h+1), so terms dominate a harmonic sequence.
            residual=sub(mul(P,[h+1,1]),mul(Q,[h,1]))
    N=max(start,1)
    for _ in range(100):
        if (positive(P,N) and positive(Q,N) and nonnegative(residual,N)
            and (potential is None or positive(potential,N)) and N+h>0): break
        N*=2
    else: raise AssertionError('Certificate search did not terminate')
    return dict(status=typ,kind=kind,start=N,P=P,Q=Q,potential=potential,
                residual=residual,shifted_residual=shift(residual,N),
                limit=limit,alpha=alpha,h=h)

def bound_series(P,Q,r0,k,certificate,stop=None):
    assert certificate['status']=='convergent'
    N=max(k+1,certificate['start'],stop or 0)
    r=F(r0);s=F(0)
    for n in range(k,N):
        s+=r
        assert val(P,n)>0 and val(Q,n)>0
        r*=val(P,n)/val(Q,n)
    tail=r*val(certificate['potential'],N)
    assert tail>0 and s>0
    return dict(first_tail_index=N,partial=s,tail_upper=tail,
                series_upper=s+tail,limit_lower=1/(s+tail),limit_upper=1/s)

def eye(d): return [[F(i==j) for j in range(d)] for i in range(d)]
def mm(A,B):
    d=len(A)
    return [[sum((A[i][h]*B[h][j] for h in range(d)),F(0)) for j in range(d)] for i in range(d)]
def bidiagonal_product(a,p,d):
    z=eye(d)
    for i in range(1,p+1):
        factor=eye(d)
        for n in range(1,d):factor[n][n-1]=a[i][n]
        z=mm(z,factor)
    return z
def determinant(A):
    A=[row[:] for row in A];z=F(1)
    for j in range(len(A)):
        pivot=next((i for i in range(j,len(A)) if A[i][j]),None)
        if pivot is None:return F(0)
        if pivot!=j:A[pivot],A[j]=A[j],A[pivot];z=-z
        a=A[j][j];z*=a
        for i in range(j+1,len(A)):
            c=A[i][j]/a
            for h in range(j+1,len(A)):A[i][h]-=c*A[j][h]
    return z

def product_entry(a,p,n,r,first=1):
    return sum((prod((a[j][n-h] for h,j in enumerate(js)),start=F(1))
                for js in combinations(range(first,p+1),r)),F(0))

def reconstruct(a_hat,p,d,epsilon):
    a={i:[F(0)]*d for i in range(1,p+1)}
    for n in range(1,d):
        k=min(n,p)
        for i in range(1,p-k+1):a[i][n]=epsilon
        C=[[product_entry(a,p,n-1,r-1,p-j+2) for j in range(1,k+1)]
            for r in range(1,k+1)]
        y=[product_entry(a_hat,p,n,r)-sum((a[i][n]*product_entry(a,p,n-1,r-1,i+1)
            for i in range(1,p-k+1)),F(0)) for r in range(1,k+1)]
        x=[F(0)]*k
        for j in reversed(range(k)):
            if C[j][j]<=0:return None
            x[j]=(y[j]-sum((C[j][h]*x[h] for h in range(j+1,k)),F(0)))/C[j][j]
            if x[j]<=0:return None
            a[p-j][n]=x[j]
        for r in range(1,k+1):
            assert product_entry(a,p,n,r)==product_entry(a_hat,p,n,r)
    return a

def finite_margins(a,p,B):
    d=p+1;product=eye(d);errors={}
    for r in range(1,p):
        factor=eye(d)
        for n in range(1,d):factor[n][n-1]=a[r][n]
        product=mm(product,factor)
        m=p-r
        X=[[(-1)**(i+j)*product[i][j] for j in range(m)] for i in range(p)]
        e=sum((abs(determinant([X[i] for i in K])-F(K==tuple(range(m))))
              for K in combinations(range(p),m)),F(0))
        errors[m]=dict(error=e,loss=factorial(m)*B**m*e,margin=1-factorial(m)*B**m*e)
    return errors

def run():
    reports={};tests=0
    families=[('geometric',[1],[2],F(1,2),F(1)),
              ('slow_geometric',[9999],[10000],F(1),F(10000)),
              ('factorial',[1],[1,1],F(1),None),
              ('p4_k1',[2,1],[4,1],F(1,4),F(1)),
              ('p4_k2',[0,1],[2,1],F(2,3),F(2)),
              ('p4_k3',[-2,1],[0,1],F(3,2),F(3)),
              ('near_critical',[1,1],[F(201,100),1],F(1),F(201)),
              ('divergent_geometric',[2],[1],F(1),None),
              ('harmonic',[0,1],[1,1],F(1),None),
              ('harmonic_with_correction',[2,2,1],[3,3,1],F(1),None),
              ('constant',[1],[1],F(1),None)]
    for name,P,Q,r0,total in families:
        k=2 if name=='p4_k2' else 3 if name=='p4_k3' else 1
        c=rational_tail_certificate(P,Q,k)
        rec={'certificate':c}
        if c['status']=='convergent':
            bounds=bound_series(P,Q,r0,k,c,stop=max(64,c['start']))
            rec['bounds']=bounds
            if total is not None:
                assert bounds['partial']<total<=bounds['series_upper']
                assert bounds['limit_lower']<=1/total<=bounds['limit_upper'];tests+=2
            # Independent finite-prefix containment, computed exactly beyond the cutoff.
            r=r0;partial=F(0)
            for n in range(k,bounds['first_tail_index']+40):
                partial+=r;r*=F(val(P,n),val(Q,n))
            assert partial<=bounds['series_upper'];tests+=1
        else:
            assert name in ['divergent_geometric','harmonic','harmonic_with_correction','constant']
        reports[name]=rec
    # Exact tails for all three equal-limit Metelmann series of the manuscript.
    p=4;series_upper=[];tail_results=[]
    for k,P,Q,r0,total in [(1,[2,1],[4,1],F(1,4),F(1)),
                           (2,[0,1],[2,1],F(2,3),F(2)),
                           (3,[-2,1],[0,1],F(3,2),F(3))]:
        aa,bb=F(P[0]),F(Q[0]);d=bb-aa
        potential=[(bb-1)/(d-1),1/(d-1)]
        residual=sub(sub(mul(potential,Q),mul(shift(potential,1),P)),Q)
        assert residual==[0]
        c=dict(status='convergent',start=k,potential=potential)
        b=bound_series(P,Q,r0,k,c,stop=64)
        assert b['series_upper']==total
        series_upper.append(total);tail_results.append(b);tests+=2
    B=max([F(1)]+[prod(series_upper[i:j],start=F(1))
                   for i in range(p-1) for j in range(i+1,p)])
    a_hat={i:[F(0) if n<=p-i else F(n+2*i-5,n) for n in range(33)]
           for i in range(1,p+1)}
    for h in range(1,50):
        eps=F(1,2**h)
        a=reconstruct(a_hat,p,p+1,eps)
        if a is None:continue
        margins=finite_margins(a,p,B)
        if all(v['loss']<F(1,2) for v in margins.values()):break
    else:raise AssertionError('No common parameter found')
    extended=reconstruct(a_hat,p,33,eps)
    assert extended is not None
    assert bidiagonal_product(extended,p,12)==bidiagonal_product(a_hat,p,12)
    tests+=1
    expected_errors={1:3*eps+3*eps**2+eps**3,
                     2:2*eps+4*eps**2+2*eps**3+eps**4,
                     3:eps+eps**2+eps**3}
    for m,v in margins.items():
        assert v['error']==expected_errors[m]
        assert v['margin']>F(2,3)
        tests+=2
    reports['constructive_bandwidth_four']={
        'exact_series':series_upper,'B':B,'all_six_free_parameters':eps,
        'finite_errors_and_uniform_margins':margins,
        'exact_tail_checks_at_64':tail_results,
        'additional_positive_rows_checked':32,
        'all_row_certificate':'For every n and m=1,2,3: W_{m,n}/Delta_{m,n} >= margin[m] > 2/3.',
        'first_rows':{i:extended[i][1:5] for i in extended}}
    # Arbitrary bandwidth: a_hat_i(n)=(n+2i-p-1)/n beyond its initial zeros.
    # Its adjacent series have exact sums S_k=k, even though every tail tends to 1.
    for pp in range(2,13):
        for k in range(1,pp):
            P=[F(pp-2*k),F(1)];Q=[F(pp-2*k+2),F(1)]
            potential=[F(pp-2*k+1),F(1)]
            assert sub(sub(mul(potential,Q),mul(shift(potential,1),P)),Q)==[0]
            c=dict(status='convergent',start=k,potential=potential)
            b=bound_series(P,Q,F(k,pp-k+1),k,c,stop=40)
            assert b['series_upper']==k
            tests+=2
    reports['arbitrary_bandwidth_family']={
        'formula':'a_hat_i(n)=(n+2*i-p-1)/n for n>=p-i+1; zero earlier',
        'exact_series':'S_k=k, for k=1,...,p-1',
        'exact_limits':'kappa_k=1/k',
        'exact_checks_bandwidths':list(range(2,13)),
        'two_sided_example_p4_q3':{'lower_limits':[F(1),F(1,2),F(1,3)],
                                 'upper_limits':[F(1),F(1,2)]}}
    # A slowly convergent example whose full sum is recovered without truncation.
    P=[F(1),F(1)];Q=[F(201,100),F(1)];potential=[F(101),F(100)]
    assert sub(sub(mul(potential,Q),mul(shift(potential,1),P)),Q)==[0]
    assert val(potential,1)==201
    reports['near_critical_exact_tail']={'potential':potential,'series':F(201),
                                        'positive_limit':F(1,201)}
    tests+=2
    result={'arithmetic':'exact rational, Python Fraction',
            'tail_validation':'nonnegative shifted polynomial coefficients on the whole half-line',
            'number_of_ratio_families':len(families),'independent_exact_checks':tests,
            'reports':reports}
    Path(__file__).with_name('results.json').write_text(json.dumps(result,indent=2,default=str)+'\n')
    print('All rational certificate checks passed.')
    for name,rec in reports.items():
        if 'certificate' not in rec:continue
        c=rec['certificate'];line=f'{name}: {c["status"]}; certificate starts at {c["start"]}'
        if 'bounds' in rec:
            b=rec['bounds'];line+=f'; limit in [{float(b["limit_lower"]):.8g}, {float(b["limit_upper"]):.8g}]'
        print(line)
    print('p=4: common free parameter =',eps,'; B =',B)
    for m,v in sorted(margins.items()): print('m =',m,'; certified all-row margin >',float(v['margin']))

if __name__=='__main__':run()
