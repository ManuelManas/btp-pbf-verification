BTP/PBF - Verification supplement - 2026-10-12, v48

CONTENTS

lean/semi_infinite: finite row reconstruction, inverse bounds and minors,
the determinant extraction identity, and the global two-sided criterion.
The global criterion starts from compatible Metelmann factors.
The concluding theorem is in CompleteResults.lean.

lean/toeplitz: the direct Toeplitz implication BTP => PBF and the converse,
including uniform entry bounds, in BTPToPBF.lean. The older files about
TN and negative roots retain their expressly stated classical hypotheses.
The file modules.txt lists all modules to check, in dependency order.

The Lean sources are unchanged from the previous verification packages.
Manuscript numbering has evolved; identify results by their mathematical
statements and the correspondence below. This supplement adds no new
claim that the polynomial or measure theorems have been formalized.

LEAN REPRODUCTION

Both projects pin Lean 4.34.0-rc2 in lean-toolchain and mathlib commit
85e3a25e006c35636f0e53b0e9296caca2685bc0 in lakefile.toml.
Install the indicated Lean toolchain with elan. In each project run:

  python3 bootstrap.py
  chmod +x run_lean.sh
  sh check.sh

bootstrap.py obtains checksum-verified dependency archives. Use
python3 bootstrap.py --offline when those archives are already cached.
check.sh compiles all listed modules in a fresh local output directory,
with warnings treated as errors. Set BTP_LEAN_BIN to a matching Lean
executable if it is installed outside the standard elan location.

MANUSCRIPT CORRESPONDENCE

Lemma rowwise: Lemma24.lean.
Successive recurrences: Proposition29.lean and RecurrenceParameters.lean.
Inverse-entry bounds: Proposition215.lean.
Inverse minors and uniform bounds: InverseMinors.lean, AdjacentRatios.lean,
UniformMinors.lean and OrderedMinors.lean.
Extraction identity: OneFactorFormula.lean and UnrestrictedDeterminant.lean.
Global existence: Necessity.lean, GlobalConstruction.lean,
TwoSidedCriterion.lean and CompleteResults.lean.
Toeplitz BTP <=> PBF: BTPToPBF.lean.

EXACT COMPUTATIONAL CHECKS

Run the following from computational/ with Python 3:
  python3 geometric_coefficients.py
  python3 constant_factor_orders.py

The following additionally require SymPy (validated with version 1.13.2):
  python3 finite_parameter_example.py
  python3 finite_parameter_domain.py

The scripts use rational or symbolic arithmetic and write their reports
beside the scripts. They check specified finite examples and identities.
The original dates and version identifiers in their output record when
those checks were introduced. They do not assert exhaustive verification
of all parameter values or of all results of the manuscript.

SHA256SUMS.txt records the checksums of the supplied files.
