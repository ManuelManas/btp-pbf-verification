Computational checks recorded for manuscript v63, retained in v64.

The mathematical text and numbering are unchanged in v64. These scripts
are separate from the Lean proofs. The supplied s2/s3 scripts retain their
original v62 labels. Their outputs record 40 and 105 successful checks,
respectively, with no FAIL or traceback. The rational certification script
records 166 exact checks. Exact symbolic and rational calculations and
numerical density integrals are identified in the source files.

Install requirements.txt in a Python virtual environment, then run:
  python s2_checks.py
  python s3_checks.py
  python certify.py

The s2/s3 scripts print failures rather than raising exceptions. Check
the final output for FAIL and traceback as well as the process exit code.
These are the actual v63 run records; they have not been relabelled as new runs.
