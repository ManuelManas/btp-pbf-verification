# Verification archive

Banded Totally Positive Matrices and Positive Bidiagonal Factorizations:
Existence, Stability, and Toeplitz Orthogonality — Manuel Mañas.

17 October 2026. The manuscript has Normal and Memoirs AMS editions.

The Lean sources in the repository's `lean` directory are the unchanged
formal core. The current correspondence table links
manuscript labels and numbers to the complete Lean declarations, records
hypotheses and source hashes, and identifies results outside formalization.
No fresh Lean build is claimed. Original build records are retained.

The manuscript distinguishes analytic reconstruction with fixed initial
entries from reconstruction allowing those entries to vary. The present
extension gives an equivalence for two lower factors, a sufficient condition
in terms of every pair in arbitrary lower bandwidth, and a transfer result
through analytic normalized LDU. The exchange limit rule covers every ordered
partition of distinct Toeplitz roots and upper-lower products with distinct
limiting parameters. The necessary direction in the two-factor equivalence
is proved by an elementary bounded-positive-forcing argument.

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

Each script writes its JSON output beside itself. Recorded outputs distinguish
the earlier calculations from the newly executed checks. The new exact
checks include all permutations for lower bandwidths 2 through 5, free
initial-row variations, signed inverse endpoint identities, companion/compound
matrix identities, and multiple roots. These are finite tests, not Lean proofs
of the analytic or infinite-dimensional results.

The full archive also contains the unchanged formal source and build
records. `SHA256SUMS.txt` identifies the included files. No Zenodo DOI has
been assigned at the time this archive was prepared.

The new dichotomy checks verify the two telescoping identities, shifted
periodic pair products, and the exact Toeplitz product for all 566 ordered
partitions with 2 through 5 parameters. Separate 70-digit computations
check limits for the 72 ordered partitions with four parameters. A varying
input example distinguishes geometric residual decay from the input's
slower convergence to constants. None of these finite computations is a
formal proof of an infinite-dimensional assertion.
