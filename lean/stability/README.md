# Stability proofs

The stable manuscript labels, declarations, hypotheses and scope are listed
in ../../verification/LEAN_CORRESPONDENCE.txt. Numbering is read from the
current manuscript auxiliary files; identifiers containing older numbers are
code names and are not references to current theorem numbers.

- WeightedShift.lean proves the weighted-shift lemma on the real Banach
  space of bounded sequences, including the inverse norm and block criterion.
- PeriodicStability.lean proves the exact scalar periodic reduction,
  including the shifted adjacent ratio and strict ordering of period products.
- AnalyticRadius.lean proves the abstract contraction theorem, its sharp
  displayed constants and positivity bound. A bounded inverse and remainder
  estimates are explicit inputs. The identification of the general band-matrix
  multiplication remainder and the analytic PBF criteria are not formalized.

Run `python3 bootstrap.py` followed by `sh check.sh` in this directory.
The latter starts with no compiled local modules and audits every project
theorem for unexpected axioms. It fails on any dependency other than
propext, Classical.choice and Quot.sound. The pinned Mathlib cache is verified
by bootstrap.py; it is not a source rebuild of Mathlib itself.
