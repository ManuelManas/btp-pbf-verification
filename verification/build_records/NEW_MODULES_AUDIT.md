# Independent semantic audit of the new stability modules

Audit date: 19 October 2026. The audited sources are `AnalyticRadius.lean`,
`PeriodicStability.lean`, and the supporting `WeightedShift.lean` as copied
into `audit_existing/new_modules/`. No source written by another agent was
edited during this audit.

## Findings

No mathematical or indexing error was found in either requested module.
The scope statement in `AnalyticRadius_SCOPE.md` accurately distinguishes
proved results from assumptions and missing matrix-specific assembly.
Neither module proves an entire analytic PBF dependence theorem. The
correspondence table must keep that boundary explicit.

## Quantitative perturbation radius

Correspondence: `stab:rem:general-radius`, **A quantitative perturbation radius**.

The formal theorem treats possibly different real normed spaces X and Y,
with X complete. It assumes a continuous linear equivalence D:X→Y and an
inverse bound M, then proves existence and uniqueness in a closed radius-r
ball for D h + R(h) = e. It does not assume a solution or its uniqueness.
Its only nonlinear hypotheses are the two displayed remainder estimates.
The proof derives a self-map bound 3r/4 and contraction factor 1/2, then
uses the complete-ball contraction theorem. The factor 2M in the separate
Lipschitz theorem follows from the same contraction estimate.

This is the actual fixed-point mechanism in the manuscript. The formal
inequalities use ≤ for the data ball, and allow r=0; the paper's strict
positive radius and open data ball are covered by restriction. M>0 is
explicit. C need not be assumed positive in the abstract contraction
lemma: the estimates themselves suffice, while the radius-conversion
lemma explicitly assumes C>0. This does not create a hidden inconsistency
or a vacuous hypothesis. `Nonvacuity.lean` supplies a positive-radius scalar
instance D=id, R=0, M=C=1, r=1/8.

The exact arbitrary-bandwidth scalar constant is formalized. Writing
p=d+2, the source defines

    C_p = choose(d+2,2) (2+A)^d
        = p(p-1)(2+A)^(p-2)/2.

The sums run through j=0,...,d, precisely k=j+2=2,...,p.
Both binomial comparisons and both complete scalar majorants are proved,
including p=2. The two-factor expansion and its quadratic/Lipschitz
bounds are proved for a possibly noncommutative normed ring, so they are
not accidentally restricted to scalar multiplication.

Remaining written assembly: identify X with the prescribed-entry factor
variation space, identify Y with the actual band space and operator norm,
construct D and its inverse from the factor conditions, prove the actual
arbitrary-p product remainder bounds by the scalar majorants, and prove
real analytic dependence. These are not supplied by the source. The
current SCOPE file states all these limitations correctly. The introductory
Lean comment says the “combinatorial proof ... for bidiagonal multiplication”
is not claimed; the intended distinction is between the proved scalar
combinatorics and its unformalized operator-product assembly. The SCOPE is
more precise and should control the public description.

## Periodic ratios

Correspondence: the scalar criterion in `stab:cor:periodic-general` and
`stab:cor:periodic-full`.

The formal definition is

    blockProduct w s N = product_{i=0}^{N-1} w(s+i+1).

For adjacent factors the source uses w(t)=a(t+1)/b(t). The paper uses
γ(n)=a(n)/b(n-1), n≥2. Thus w(t)=γ(t+1), and the formal block covers
γ(s+2),...,γ(s+N+1). Every paper starting row n≥2 is obtained by s=n-2.
There is no off-by-one error.

`periodic_adjacent_product` proves exactly the period-product quotient:
the numerator a(2)...a(h+1) equals a(1)...a(h) by periodicity, and the
denominator is b(1)...b(h). Positivity makes cancellation and division
legitimate. The lemma itself only needs periodicity of a; the final
criterion also assumes positivity and periodicity of b.

`periodic_block_contraction_iff` is non-tautological: an arbitrary uniform
contractive block length is shown equivalent to a period product <1 by
comparing a common length. The converse picks one full period.
The final extension adds `periodic_bounded`, `periodic_geometric_iff`, and
`periodic_adjacent_geometric_iff`, so the reduction to uniform geometric
decay for every starting row and every length is now completely assembled.
It invokes the independently proved fixed-block equivalence from
WeightedShift. Bounds over all periods and remainders are therefore
proved, not assumed.

The source sequences are indexed from zero, whereas the paper's factor
entries begin at one. For h>0 a positive h-periodic sequence on positive
indices has the harmless extension a(0)=a(h); no displayed product or
weight uses a(0) or b(0). This translation is mathematically immediate,
but the extension itself is not packaged as a separate Lean theorem.

For full bandwidth, the generic `periodic_geometric_iff` applies to
w=a_p b_q. The source does not yet package the product-of-period-products
identity, conversion to geometric means, all p−1 and q−1 inequalities,
or application of the analytic matrix-factor theorem. Thus it formalizes
the scalar periodic criterion, not the complete matrix corollaries.

## Reproduction and axioms

The copy in `new_modules/` uses the freshly reproduced, checksum-verified
Mathlib dependencies from `dependency_reproduction/.deps`. Its local
`.build` began empty. Commands, in that directory:

```sh
./run_lean.sh -DwarningAsError=true -o .build/WeightedShift.olean WeightedShift.lean
./run_lean.sh -DwarningAsError=true -o .build/AnalyticRadius.olean AnalyticRadius.lean
./run_lean.sh -DwarningAsError=true -o .build/PeriodicStability.olean PeriodicStability.lean
./run_lean.sh -DwarningAsError=true Nonvacuity.lean
./run_lean.sh -DwarningAsError=true AxiomAudit.lean
```

The environment audit collects the transitive axiom dependencies of all
project theorem constants under both `BTP.Stability` and `PBFStability`.
This checks more than the individually printed principal declarations.
Source scans found no custom axiom declaration, sorry, admit, unsafe,
implemented_by or native_decide in the copied modules.

All three modules compiled successfully with warnings treated as errors.
The nonvacuity example also compiled successfully. The environment audit
checked **110 project theorem constants**, including auxiliary/generated
proofs, and found only subsets of `propext`, `Classical.choice`, and
`Quot.sound`. There was no `sorryAx` or application-specific axiom.
The copied modules were byte-compared with the current source files and
all three matched. Logs: `weighted_clean_build.log`,
`radius_clean_build.log`, `periodic_clean_build.log`, `nonvacuity.log`,
and `axioms.log`; summary: `audit_summary.json`.

Recommended public wording: the weighted-shift equivalence, its inverse
bound, the scalar periodic criterion, and the quantitative contraction
argument (with exact scalar remainder constants) have formal Lean proofs.
The principal matrix analytic-dependence criteria and the full matrix
perturbation-radius proposition are not yet completely formalized.
