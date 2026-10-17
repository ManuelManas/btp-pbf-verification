# Verification archive

Banded Totally Positive Matrices and Positive Bidiagonal Factorizations:
Existence, Stability, and Toeplitz Orthogonality — Manuel Mañas.

17 October 2026. The manuscript has Normal and Memoirs AMS editions.

The Lean sources in the repository's `lean` directory are the unchanged
formal core. The current correspondence table links
manuscript labels and numbers to the complete Lean declarations, records
hypotheses and source hashes, and identifies results outside formalization.
No fresh Lean build is claimed. Original build records are retained.

The mathematical developments distinguish analytic reconstruction with
fixed initial entries from reconstruction allowing those entries to vary.
Written proofs cover two factors, arbitrary lower bandwidth with distinct
limiting constants in any order, and every internal ordering of separated
Toeplitz root groups. A matrix-power contour argument supplies uniform
remainder and derivative estimates through nondominant root collisions.

## Run the computational checks

Use Python 3 with the packages in `requirements.txt`. From this directory:

```sh
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

Each script writes its JSON output beside itself. Recorded outputs distinguish
the earlier calculations from the newly executed checks. The new exact
checks include all permutations for lower bandwidths 2 through 5, free
initial-row variations, signed inverse endpoint identities, companion/compound
matrix identities, and multiple roots. These are finite tests, not Lean proofs
of the analytic or infinite-dimensional results.

The full archive also contains the unchanged formal source and build
records. `SHA256SUMS.txt` identifies the included files. No Zenodo DOI has
been assigned at the time this archive was prepared.
