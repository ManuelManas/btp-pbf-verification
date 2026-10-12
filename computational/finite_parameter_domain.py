"""Exact checks for the full positive parameter domain of the d=5 example.

Requires Python 3 and SymPy; modifies no manuscript.
The sign arguments and closure proof are in independent_domain_review.txt.
"""
from pathlib import Path
import json
import sympy as S

u, v, w, t, s = S.symbols('u v w t s')
A = 1-u-v
B = 1-w+u*w
C = 1-2*u-2*v+v*w
D = 1-2*w+3*u*w
E = 1-3*u-3*v+3*v*w
H = 1-3*w+6*u*w
F = 1-4*u-4*v+6*v*w
polys = dict(A=A, B=B, C=C, D=D, E=E, H=H, F=F)

checks = {}
def check(name, expression):
    assert S.cancel(expression) == 0, (name, S.factor(expression))
    checks[name] = True

check('first_elimination_identity', B-((2-w)*A-C))
check('second_elimination_identity', D-(3*(1-w)*C-(2-w)*E))
check('third_elimination_identity', H-((4-6*w)*E-3*(1-w)*F))
check('D_minus_H', D-H-w*(1-3*u))
check('B_minus_D', B-D-w*(1-2*u))

W = 1/(3*(1-2*u))
V = (1-4*u)/(4-6*w)
check('roof_at_H_boundary', V.subs(w,W)-(S.Rational(1,2)-u))
umin = S.Rational(1,2)-1/(6*w)
check('roof_in_high_horizontal_section', V.subs(u,umin)-1/(6*w))

surfaces = {
    'F_low_w': {u:(1-s)/4, v:s/(4-6*t), w:t},
    'F_high_w': {u:(1+s)/4-s/(6*t), v:s/(6*t), w:t},
    'H': {u:S.Rational(1,2)-1/(6*t), v:s/(6*t), w:t},
    'u_zero': {u:S.Integer(0), v:s/(4-6*t), w:t},
}
check('F_low_surface_exact', F.subs(surfaces['F_low_w'], simultaneous=True))
check('F_high_surface_exact', F.subs(surfaces['F_high_w'], simultaneous=True))
check('H_surface_exact', H.subs(surfaces['H'], simultaneous=True))
for face in ('F_high_w','H'):
    check(face+'_corner_u', surfaces[face][u].subs(t,S.Rational(2,3))-S.Rational(1,4))
    check(face+'_corner_v', surfaces[face][v].subs(t,S.Rational(2,3))-s/4)

corner = {u:S.Rational(1,4), w:S.Rational(2,3)}
check('corner_F', F.subs(corner))
check('corner_H', H.subs(corner))
check('corner_E', E.subs(corner)-(S.Rational(1,4)-v))
scale = {u:t*u, v:t*v, w:t*w}
check('radial_H', H.subs(scale, simultaneous=True)-(t*H+(1-t)*(1-6*t*u*w)))
check('radial_F', F.subs(scale, simultaneous=True)-(t*F+(1-t)*(1-6*t*v*w)))

spurious = {u:S.Rational(3,4), v:S.Rational(1,4), w:S.Integer(4)}
weak_values = {name:str(P.subs(spurious)) for name,P in polys.items()}
assert all(P.subs(spurious) >= 0 for P in polys.values())

result = {
    'status':'passed',
    'engine':'SymPy '+S.__version__,
    'checks':checks,
    'exact_open_domain':[
        '0 < u < 1/4',
        '0 < w < 1/(3*(1-2*u))',
        '0 < v < (1-4*u)/(4-6*w)',
    ],
    'exact_closure':[
        '0 <= u <= 1/4',
        '0 <= w <= 1/(3*(1-2*u))',
        '0 <= v <= 1/2-u',
        '(4-6*w)*v <= 1-4*u',
    ],
    'horizontal_sections':{
        '0<w<=1/3':{'u_min':'0', 'u_max':'1/4', 'v_max_at_u_min':'1/(4-6*w)'},
        '1/3<=w<2/3':{'u_min':'1/2-1/(6*w)', 'u_max':'1/4', 'v_max_at_u_min':'1/(6*w)'},
    },
    'boundary_surfaces':{name:{str(k):str(val) for k,val in params.items()} for name,params in surfaces.items()},
    'surface_parameter_ranges':{'F_low_w':'0<=t<=1/3, 0<=s<=1', 'F_high_w':'1/3<=t<=2/3, 0<=s<=1', 'H':'1/3<=t<=2/3, 0<=s<=1', 'u_zero':'0<=t<=1/3, 0<=s<=1'},
    'singular_corner_fiber':'u=1/4, w=2/3, 0<=v<=1/4; an edge, not an extra two-dimensional face',
    'weak_inequalities_are_not_the_closure':{
        'point':{'u':'3/4','v':'1/4','w':'4'},
        'polynomial_values':weak_values,
    },
    'scope':'Exact algebraic identities verified symbolically. Sign reasoning and closure proof recorded separately. No manuscript modifications.',
}
out=Path(__file__).with_name('domain_verification.json')
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
