# Verification records

The current [correspondence table](LEAN_CORRESPONDENCE.txt) records the
manuscript numbers in both editions, stable labels, declaration names and
explicit hypotheses. It includes complete and partial formalization separately.

The three Lean projects have fresh compilation logs and exhaustive axiom
audits in [build_records](build_records). The independent reviews also compare
the actual definitions and hypotheses with the manuscript. Successful Lean
compilation alone does not establish that this translation is correct.

The precise current coverage is recorded in [VERIFICATION_SCOPE.json](VERIFICATION_SCOPE.json).
The complete scalar weighted-shift lemma, the scalar periodic criterion and
the abstract radius mechanism are new formal proofs. The general PBF analytic
criteria and the spectral theory are not formalized.

## Preserved computational checks

The scripts below and their outputs are historical finite checks. They were
not rerun in the current formalization update. Their original scope and counts
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
