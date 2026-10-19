# Independent semantic review

This review concerns `WeightedShift.lean` and
`audit_existing/semi_infinite/ArbitraryDiagonalBridge.lean`. It checks their
mathematical meaning and correspondence with the manuscript, separately from
whether the Lean elaborator and kernel accept their proofs.

## WeightedShift.lean

**Conclusion:** the complete assertion of the manuscript lemma
`stab:lem:weighted-shift` is represented, with a harmless extension from
strictly positive to nonnegative weights. This is Lemma 3.6 in the presently
compiled manuscript; the stable correspondence is its label and title,
**Bounded inverse and products over blocks**.

### Space and norm

`BoundedSequence := BoundedContinuousFunction ℕ ℝ` is a genuine model of
real ℓ∞. Natural numbers have the discrete topology, so continuity imposes no
extra restriction. The norm is the supremum of the absolute values. The
constructor `ofAbsBound` uses a diameter bound `2M` to establish boundedness;
the later norm estimates use the actual pointwise bound `M`. There is no
factor-of-two loss hidden in the operator norm estimate.

### Initial equation and indexing

`differenceFun w f 0 = f 0` and
`differenceFun w f (n+1) = f (n+1) - w (n+1)*f n` are exactly `I-W`, with
`(Wf)_0=0`. The corresponding inverse has initial equation `v₀=f₀`, not a
free initial value. Thus this is the fixed-initial-value lemma; it does not
assert the free-initial-value or quotient-space dichotomy theorem.

The paper's starting row `n₀` is translated to zero. The formal product
`blockProduct w s N` is the product of weights in rows `s+1,...,s+N`, so
`s=n-n₀-1` matches the manuscript's product starting at row `n≥n₀+1`.
The value `w 0` never enters the operator or any product. Requiring it to be
nonnegative is harmless: it can be set to zero when encoding the paper's
weights. Products of length zero are included and equal one; the required
constant `C≥1` makes this equivalent to the paper's restriction `N≥1`.

As a direct index check, the first Green row sums are
`1`, `1+w₁`, and `1+w₂+w₂w₁`, which are exactly those of the stated forward
recurrence.

### Inverse and estimates

The inverse is constructed by forward substitution, not postulated.
`solutionMap` is proved linear and continuous; both inverse identities are
proved. `differenceMap_bijective_iff_geometric` assumes only bijectivity in
the difficult direction. Its use of the bounded preimage of the constant
one sequence is valid: positivity identifies that sequence with all Green
row sums. The proof then derives uniform geometric decay using a bounded
positive diagonal weight `rowSum`; it is a different valid proof of the
same manuscript implication.

`weighted_shift_inverse_norm_bound` constructs a continuous linear
equivalence whose forward map is exactly `I-W` and proves the stated norm
bound `1+Cρ/(1-ρ)` for its inverse. The unit term is separated correctly.

### One fixed block length

`geometric_iff_block_contraction` explicitly assumes uniformly bounded
weights. That hypothesis is essential for this formulation and is present
in the manuscript. The finite remainder of a block decomposition is bounded
by the global bound on individual weights. The positive root used for the
geometric rate is formed from `(1+θ)/2`, so it remains positive even if the
formal statement permits `θ=0`. Allowing `0≤θ<1` instead of `0<θ<1` gives
the same existence condition: enlarge θ to `(1+θ)/2`. Under the paper's
strictly positive weights, θ is automatically positive anyway.

The more general scalar row-sum equivalence needs no prior bound on the
weights; its conclusion implies such a bound from products of length one.
This should not be confused with the extra boundedness hypothesis used in
the fixed-block statement.

### Scope

This module establishes the infinite-dimensional weighted recurrence lemma
itself, including the inverse norm and block criterion. It does not by
itself establish the nonlinear analytic PBF dependence criterion, the
free-initial-value pairwise dichotomy criterion, or the LDU row-sum theorem.

## ArbitraryDiagonalBridge.lean

**Conclusion:** the new bridge correctly removes the unintended restriction
that a candidate PBF have the same diagonal sequence as the prescribed
normalized factorization. It closes the normalization step needed for the
inverse-minor part of `cor:global-two-sided-criterion` (currently Corollary
2.20).

`HasArbitraryTwoSidedPBF` quantifies over single global arrays `b,e` and a
single positive diagonal sequence `E`, and then requires equality for every
finite leading section. The quantifier order is `∃ b,e,E, ∀ d`; it is not the
weaker statement that unrelated factorizations exist separately for each
dimension.

The definition `triangularSections` uses actual finite products of unit
lower bidiagonal matrices, a diagonal matrix, and the transpose of a unit
lower product. Hence each determinant is the product of the diagonal
entries. This is also faithful to a semi-infinite normalized LDU product:
an entry `(i,j)` only sums over indices at most `min(i,j)`, so taking leading
sections does not omit contributions.

`normalized_diagonal_unique` first obtains equality of all finite products
`∏_{i<d}E_i = ∏_{i<d}D_i`. Comparing `d=n+1` with `d=n` and cancelling
the nonzero preceding product of `D_i` proves `E_n=D_n`. It does not assume
this conclusion. It only needs the reference diagonal nonzero; positivity
of the candidate diagonal is not used in that uniqueness argument.

After substituting `E=D`, the existing theorem on uniqueness of normalized
triangular products identifies the lower and upper products. The established
one-sided criteria then yield the two-sided inverse-minor equivalence.
No uniform bound on the diagonal or factor entries is used or required.

### Scope

The result takes compatible Metelmann arrays and a positive diagonal as
input. It does not supply the antecedent BTP-to-Metelmann representation of
an arbitrary matrix, nor the identification of the inverse-minor limits
with the Jacobi continued fractions. Those limits and their strict
positivity are the formalized part of the manuscript corollary. Describing
the entire corollary, including its continued-fraction formulation, as
formalized would overstate the result.

## Axioms and findings

The new files contain no custom axioms, `sorry`, `admit`, `unsafe`, or
`native_decide` proof shortcuts. Their reported dependencies are Lean's
standard `propext`, `Classical.choice`, and `Quot.sound`.

No mathematical or semantic error was found in either reviewed file.
The limitations above concern precise reporting of what is formalized,
not defects in the proved statements.
