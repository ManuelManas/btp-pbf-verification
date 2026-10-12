from fractions import Fraction as F
from math import comb
from pathlib import Path
import json

def coefficients(roots):
    c = [F(1)]
    for beta in roots:
        new = [F(0)] * (len(c) + 1)
        for i, x in enumerate(c):
            new[i] += x
            new[i+1] += beta*x
        c = new
    return c

counts = {'cases': 0, 'binomial_identities': 0, 'scalar_identities': 0,
          'strict_obstructions': 0, 'q_one_invariants': 0}
samples = []
for p in range(1, 7):
    for q in range(1, 7):
        m = p+q
        for alpha in [F(1), F(2,3)]:
            for root_tau in [F(1,2), F(1), F(2)]:
                tau = root_tau**2
                c = coefficients([alpha*tau**nu for nu in range(m)])
                s = alpha*root_tau**(m-1)
                a = s**q
                target = [a*s**(r-q)*comb(m,r) for r in range(m+1)]
                assert c[0] == target[0] and c[-1] == target[-1]
                b = c[q]-target[q]
                differences = [r for r in range(m+1) if r != q and c[r] != target[r]]
                counts['cases'] += 1
                if tau == 1:
                    assert not differences and b == 0
                    counts['binomial_identities'] += 1
                elif m == 2:
                    assert not differences and a == s == alpha*root_tau
                    assert b == alpha*(root_tau-1)**2
                    counts['scalar_identities'] += 1
                else:
                    tested_index = 1 if q >= 2 else m-1
                    assert tested_index in differences
                    assert c[tested_index] > target[tested_index]
                    counts['strict_obstructions'] += 1
                if q == 1 and p >= 2:
                    invariant = c[p]**(p+1)/c[p+1]**p
                    geometric = sum(root_tau**(p-2*nu) for nu in range(p+1))**(p+1)
                    assert invariant == geometric
                    assert invariant >= (p+1)**(p+1)
                    assert (invariant == (p+1)**(p+1)) == (tau == 1)
                    counts['q_one_invariants'] += 1
                    if alpha == 1 and p == 2:
                        samples.append({'p':p,'q':q,'tau':str(tau),
                                        'invariant':str(invariant), 'binomial_value':27})

result = {'status':'passed', 'arithmetic':'exact rational', 'counts':counts,
          'ranges':{'p':'1..6','q':'1..6','alpha':['1','2/3'],'tau':['1/4','1','4']},
          'scope':'Independent coefficient expansion checks the new affine-comparison proposition and the scalar exception. The proof in the manuscript covers all parameters; these checks do not replace it.',
          'samples':samples, 'lean':'No new Lean formalization is asserted for this proposition.'}
Path(__file__).with_name('exact_validation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
