# Auxiliary stability project

Run `python3 bootstrap.py` followed by `sh check.sh` in this directory.
The project and its module list are preserved as a complete reproducible unit.
`WeightedShift.lean` is mapped to the current manuscript in
`../../verification/LEAN_CORRESPONDENCE.txt`.

`PeriodicStability.lean` and `AnalyticRadius.lean` remain unchanged parts of
this project. Their presence adds no claims to the current correspondence
table. The general analytic PBF criteria, including relative stability,
are in `../general_stability`.

The checker starts with an empty directory of compiled local modules and
audits every project theorem for transitive axiom dependencies. It accepts
only `propext`, `Classical.choice`, and `Quot.sound`. Bootstrap verifies the
pinned dependency cache; it does not rebuild Mathlib from source.
