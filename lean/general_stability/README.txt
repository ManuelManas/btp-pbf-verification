General positive bidiagonal factorization stability

Run python3 bootstrap.py and then sh check.sh.
The latter recompiles every listed local module into a new empty directory
and audits every theorem, including generated auxiliaries, for transitive axioms.
Only propext, Classical.choice and Quot.sound are accepted.

Main entry points: AnalyticLowerStability, AnalyticFreeLowerStability,
FullFixedEquivalence, FullFreeCriterion, FullDifferentiableCriterion,
ActualAnalyticLDU, RelativeLowerCriterion, RelativeFullCriterion and
OperatorStability. Exact scope and manuscript labels:
../../verification/LEAN_CORRESPONDENCE.txt.

Finite matrices in the proofs are compatible principal sections used to
construct and prove results on actual infinite Banach sequence spaces.
They are not finite experimental substitutes for the infinite theorems.
The raw relative maps impose no absolute bound on their base sequences.
