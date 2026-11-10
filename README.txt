VERIFICATION SUPPLEMENT — MEMOIRS OF THE AMS

Manuscript: Banded Totally Positive Matrices and Positive Bidiagonal Factorizations: Existence, Stability, and Toeplitz Orthogonality

This supplement supplies the formal sources, their correspondence with the
Memoirs manuscript, and targeted exact/numerical checks. The manuscript
contains the proofs; the supplement is supporting material for examination
and reproduction. It does not claim a formal verification of every result.

1. Start with verification/LEAN_CORRESPONDENCE.txt. Its 18 rows give current
   Memoirs theorem numbers and printed pages, stable manuscript labels,
   precise hypotheses and scope, and Lean declaration paths, lines and
   SHA256 hashes. The JSON file contains the same information. Paths are
   relative to this directory. The scope file lists excluded results and
   explicit classical inputs. No other manuscript edition is packaged.

2. Formal verification. Lean 4.34.0-rc2 compiled all
   188 listed modules across the four projects with warnings treated as
   errors. Each project used an empty local build directory. The four
   audits of transitive axiom dependencies passed. The 52 references in
   the correspondence table occur in the audit logs of their projects.
   The logs and RESULTS.json are in verification/lean_audit/. The counts
   include generated auxiliaries and count shared declarations per project.
   PROVENANCE.json records the origin of the formal sources.

3. Reproduce the Lean checks. Requirements: Python 3, a POSIX shell, and
   Lean/elan with the toolchain named in each project's lean-toolchain.
   Each of lean/semi_infinite, lean/toeplitz, lean/stability, and
   lean/general_stability is a standalone project. In each directory:

       elan toolchain install "$(cat lean-toolchain)"
       python3 bootstrap.py
       sh check.sh

   Bootstrap downloads the pinned dependency cache, checks SHA256 hashes,
   and prepares local .deps/ and .cache/ directories. Internet access is
   needed unless those verified cache archives already exist; --offline
   requires them in advance. The general-stability project also compiles
   its included, checksum-verified Mathlib source exception. This uses
   cached Mathlib dependencies, not a full Mathlib source rebuild.
   check.sh creates a fresh local build directory, compiles every module
   listed in modules.txt with warnings treated as errors, and audits every
   project theorem for transitive axiom dependencies. Only propext,
   Classical.choice and Quot.sound are accepted. BTP_LEAN_BIN and
   BTP_LEANTAR can select existing compatible executables. Large dependency
   downloads and nontrivial build time should be expected.

4. Computational checks. computations/ contains five scripts with their
   outputs from the recorded 4 November 2026 execution: 225181 exact root
   formula checks, 516 spectral-kernel checks, 2227 exact/asymptotic checks,
   eight noncentral-collision checks and six exact boundary-residue checks.
   Embedded earlier preparation dates are retained. These finite examples
   support the formulas; they do not prove their general statements.
   The boundary-residue script was rerun after editing its introductory
   docstring. All six checks passed and reproduced the recorded JSON output.
   RECORDED_CHECKS.json records the scripts, outputs and execution dates.

   To reproduce without overwriting the supplied outputs, use a copy:

       python3 -m venv .venv
       . .venv/bin/activate
       python3 -m pip install -r computations/requirements.txt
       cp -R computations rerun_computations
       python3 rerun_computations/root_formulas/new_formula_checks.py
       python3 rerun_computations/spectral_kernels/check_kernels.py
       python3 rerun_computations/uniform_asymptotics/adversarial_math_checks.py
       python3 rerun_computations/uniform_asymptotics/collision_check.py
       python3 rerun_computations/check_boundary_residue.py

   SymPy 1.14.0 and mpmath 1.3.0 are pinned, matching the targeted run.
   The exact root-formula and
   boundary-residue scripts use only the Python standard library. Outputs
   are written beside each script. Floating-point text can depend on the
   runtime; the scripts test the stated tolerances internally.

5. Integrity and attribution. MANIFEST.json lists file sizes and SHA256
   hashes; SHA256SUMS.txt is suitable for `sha256sum -c SHA256SUMS.txt`
   (or `shasum -a 256 -c SHA256SUMS.txt`). Those manifests cover every
   other included file. Mathlib's source header and Apache 2.0 license
   remain in dependency_sources/. Formal declarations and their source attributions are preserved. Original PBF sources had no separate
   license declaration in the archive, so none is inferred here.
