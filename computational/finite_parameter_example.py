"""Exact, independent verification of the d=5, p=3 parameter example.

Run with Python 3 and SymPy:
python3 finite_parameter_example.py

No manuscript files are read or modified.
"""
from pathlib import Path
import json
import sympy as S

W = Path(__file__).resolve().parent
u, v, w = S.symbols("u v w")

# Reconstruct directly from the three product equations, independently of
# the proposed closed table.
a, b, c = {1: u, 2: w}, {1: v}, {1: 1-u-v}
b[2] = S.factor((1-w*(b[1]+c[1]))/c[1])
c[2] = S.factor(2-w-b[2])
for n in (3, 4):
    a[n] = S.factor(1/(b[n-1]*c[n-2]))
    b[n] = S.factor((3-a[n]*(b[n-1]+c[n-1]))/c[n-1])
    c[n] = S.factor(3-a[n]-b[n])

# Internal abbreviations used only for checking the seven explicit polynomials.
p = {n: 1-n*(u+v)+S.Rational(n*(n-1),2)*v*w for n in range(1,5)}
q = {n: 1-n*w+S.Rational(n*(n+1),2)*u*w for n in range(1,4)}
closed_table = [
    (u, v, p[1]),
    (w, q[1]/p[1], p[2]/p[1]),
    (1/q[1], p[1]*q[2]/(q[1]*p[2]), p[3]/p[2]),
    (q[1]/q[2], p[2]*q[3]/(q[2]*p[3]), p[4]/p[3]),
]
for n in range(1,5):
    for actual, expected in zip((a[n],b[n],c[n]), closed_table[n-1]):
        assert S.cancel(actual-expected) == 0

factors = []
for entries in (a,b,c):
    M = S.eye(5)
    for n in range(1,5):
        M[n,n-1] = entries[n]
    factors.append(M)
target = S.Matrix([
    [1,0,0,0,0], [1,1,0,0,0], [1,2,1,0,0],
    [1,3,3,1,0], [0,1,3,3,1],
])
assert (factors[0]*factors[1]*factors[2]-target).applyfunc(S.cancel) == S.zeros(5)

cut = {w:S.Rational(1,10)}
q_cut = [S.expand(q[n].subs(cut)) for n in range(1,4)]
assert q_cut == [S.Rational(9,10)+u/10, S.Rational(4,5)+3*u/10,
                 S.Rational(7,10)+3*u/5]
p_differences = [S.expand((p[n]-p[n+1]).subs(cut)) for n in range(1,4)]
assert p_differences == [u+S.Rational(9,10)*v,
                         u+S.Rational(8,10)*v,
                         u+S.Rational(7,10)*v]
p4_cut = S.expand(p[4].subs(cut))
assert p4_cut == 1-4*u-S.Rational(17,5)*v

point = {u:S.Rational(1,10),v:S.Rational(1,10),w:S.Rational(1,10)}
point_table = [[S.factor(x.subs(point)) for x in row] for row in closed_table]
assert point_table == [
    [S.Rational(1,10),S.Rational(1,10),S.Rational(4,5)],
    [S.Rational(1,10),S.Rational(91,80),S.Rational(61,80)],
    [S.Rational(100,91),S.Rational(6640,5551),S.Rational(43,61)],
    [S.Rational(91,83),S.Rational(4636,3569),S.Rational(26,43)],
]

report = {
    "status":"passed",
    "engine":"SymPy "+S.__version__,
    "matrix_order":5, "lower_bandwidth":3,
    "free_parameters":{"a_1(1)":"u","a_2(1)":"v","a_1(2)":"w"},
    "exact_symbolic_product_verified":True,
    "closed_table_matches_independent_recurrence":True,
    "reconstructed_table":[[str(S.factor(x)) for x in row] for row in closed_table],
    "positive_parameters":["u > 0","v > 0","w > 0"],
    "additional_strict_inequalities_by_row":{
        "1":[str(S.expand(p[1]))+" > 0"],
        "2":[str(S.expand(q[1]))+" > 0",str(S.expand(p[2]))+" > 0"],
        "3":[str(S.expand(q[2]))+" > 0",str(S.expand(p[3]))+" > 0"],
        "4":[str(S.expand(q[3]))+" > 0",str(S.expand(p[4]))+" > 0"],
    },
    "equivalence_argument":[
        "Row 1: c(1)>0 is exactly p1>0.",
        "Row 2: since p1>0, b(2)>0 and c(2)>0 are exactly q1>0 and p2>0.",
        "Row 3: a(3)=1/q1 is already positive; b(3)>0 and c(3)>0 are exactly q2>0 and p3>0.",
        "Row 4: a(4)=q1/q2 is already positive; b(4)>0 and c(4)>0 are exactly q3>0 and p4>0.",
        "Conversely, all seven inequalities and u,v,w>0 make every table entry positive and every denominator nonzero; the exact product identity then gives the required factorization.",
    ],
    "section_w_1_10":{
        "q_values":[str(x) for x in q_cut],
        "p_n_minus_p_next":[str(x) for x in p_differences],
        "domain":"u>0, v>0, 4*u+17*v/5<1",
        "boundary_line":"v=(5/17)*(1-4*u)",
        "closure_vertices":[["0","0"],["1/4","0"],["0","5/17"]],
        "all_boundary_segments_excluded":True,
        "oblique_boundary":"On its interior, a_3(4)=0 and all other subdiagonal entries are positive.",
        "coordinate_boundaries":"u=0 gives a_1(1)=0; v=0 gives a_2(1)=0.",
        "check_point":["1/10","1/10"],
    },
    "table_at_all_parameters_1_10":[[str(x) for x in row] for row in point_table],
}
(W/"independent_symbolic_check.json").write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps(report,indent=2))
