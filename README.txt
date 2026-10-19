BTP/PBF: formal proofs and exact computational checks

README.md describes the scope and build instructions.
verification/LEAN_CORRESPONDENCE.txt maps the current manuscript numbers and
stable LaTeX labels to Lean declarations, with explicit hypotheses.

Run bootstrap.py and check.sh in each of lean/semi_infinite, lean/toeplitz,
and lean/stability. The current build includes 74 mathematical source modules
(29 + 42 + 3), with shared modules counted in both original projects.
Each build starts with no local compiled modules and audits every theorem's
axioms. Only Lean's standard foundational axioms occur.

The complete weighted-shift lemma, the scalar periodic reduction and the
abstract quantitative-radius argument are included. The general PBF stability
criteria, Jacobi-fraction reformulation and spectral theory remain outside
formalization. Explicit mathematical hypotheses are listed in the table.

Earlier archives are preserved. The package is identified by the work's title,
not a manuscript version or the preliminary arXiv upload.
