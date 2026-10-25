# Verification records

The current [correspondence table](LEAN_CORRESPONDENCE.txt) records the
manuscript numbers in both editions, stable labels, declaration names and
explicit hypotheses. It includes complete and partial formalization separately.
The current result numbers and page references were read from both compiled editions on 25 October
2026; earlier values are preserved in [history/2026-10-19](history/2026-10-19).

The formal build and axiom-audit records dated 19 October 2026 are retained
in [build_records](build_records). The documentation update of 25 October
2026 changes the correspondence and descriptions only; it does not report
a new Lean compilation or axiom audit. The independent reviews also compare
the actual definitions and hypotheses with the manuscript. Successful Lean
compilation alone does not establish that this translation is correct.

The precise current coverage is recorded in [VERIFICATION_SCOPE.json](VERIFICATION_SCOPE.json).
The general fixed-data, variable-data and arbitrary-growth relative criteria
have complete analytic equivalence proofs for the actual matrix products.
See the table for the coverage of subsidiary conclusions and the results that
remain outside Lean.

## Preserved computational checks

The scripts below and their outputs are historical finite checks. They were
not rerun in this documentation update. Their original scope and counts
are retained in [historical_computational_scope.json](build_records/historical_computational_scope.json).
They are neither substitutes for written proofs nor Lean proofs of the full
infinite-dimensional statements.

## Run the computational checks


Use Python 3 with the packages in `requirements.txt`. From this directory:

```sh
python checks/dichotomies/check_dichotomy_exchange.py
python checks/variable_initial_entries/check_new_results.py
python checks/uniform_asymptotics/collision_check.py
python checks/uniform_asymptotics/adversarial_math_checks.py
python checks/fixed_initial_entries/check_stability_details.py
python checks/root_formulas/new_formula_checks.py
python checks/general_ode/exact_jet_checks.py
python checks/general_ode/chebyshev_control.py
python checks/spectral_kernels/check_kernels.py
python checks/determinants_equilibrium/check_determinants_equilibrium.py
```


Each script writes its report beside its source. Use the listed package
requirements. The old build records and releases remain available unchanged.
No Zenodo deposit or DOI is claimed by this update.
