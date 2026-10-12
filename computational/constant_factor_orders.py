#!/usr/bin/env python3
"""Exact, finite checks supporting the constant-bidiagonal word construction.

Run with Python 3; only the standard library is needed.  All matrix arithmetic
uses fractions.Fraction.  The default JSON is written beside this script.

For each 1 <= p,q <= 4 and each of two positive parameter profiles, this checks
every stable interleaving of the labelled upper and lower factors.  It does not
claim to enumerate every permutation of distinct labels or every possible
eventually Toeplitz matrix.  The analytic proof of the infinite support bound
uses U_i L_j - L_j U_i = xi_j e_0 e_0^T; these finite checks support that proof.

The tested block has order p+q+3.  Products are formed with p+q extra rows and
columns.  A path of p+q bidiagonal factors cannot reach that artificial bottom
boundary and return to the tested block, so the tested entries are the exact
semi-infinite entries.  In particular, separately truncated factors are NOT
mistaken for the leading principal block of their semi-infinite product.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
from itertools import combinations
import json
from math import comb
from pathlib import Path


def identity(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def product(word, eta, xi, n):
    """Multiply rightwards by U=Lambda+eta I or L=I+xi Lambda^T."""
    a = identity(n)
    for kind, label in word:
        if kind == "U":
            coefficient = eta[label]
            a = [
                [coefficient * row[j] + (row[j-1] if j else 0)
                 for j in range(n)]
                for row in a
            ]
        else:
            coefficient = xi[label]
            a = [
                [row[j] + (coefficient * row[j+1] if j+1 < n else 0)
                 for j in range(n)]
                for row in a
            ]
    return a


def stable_interleavings(p, q):
    for lower_positions in combinations(range(p+q), p):
        lower_positions = set(lower_positions)
        a = b = 0
        word = []
        for k in range(p+q):
            if k in lower_positions:
                word.append(("L", a))
                a += 1
            else:
                word.append(("U", b))
                b += 1
        yield tuple(word)


def polynomial_coefficients(parameters):
    """Independent coefficient expansion of prod(1+parameter*z)."""
    coefficients = [F(1)]
    for value in parameters:
        out = [F(0)] * (len(coefficients)+1)
        for degree, coefficient in enumerate(coefficients):
            out[degree] += coefficient
            out[degree+1] += value * coefficient
        coefficients = out
    return coefficients


def exact_rank(matrix):
    a = [row[:] for row in matrix]
    rows, cols = len(a), len(a[0]) if a else 0
    rank = 0
    for column in range(cols):
        pivot = next((i for i in range(rank, rows) if a[i][column]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        pivot_value = a[rank][column]
        a[rank] = [value / pivot_value for value in a[rank]]
        for i in range(rank+1, rows):
            multiplier = a[i][column]
            if multiplier:
                a[i] = [a[i][j] - multiplier*a[rank][j] for j in range(cols)]
        rank += 1
        if rank == rows:
            break
    return rank


def check_case(p, q, profile):
    if profile == "repeated_root":
        eta, xi = [F(1)]*q, [F(1)]*p
    else:
        eta = [F(i+2, 2*i+5) for i in range(q)]
        xi = [F(j+3, j+2) for j in range(p)]
    m = p+q
    checked_order, product_order = m+3, 2*m+3
    reference_word = tuple([("U", i) for i in range(q)] +
                           [("L", j) for j in range(p)])
    reference = product(reference_word, eta, xi, product_order)
    coefficients = polynomial_coefficients(eta+xi)
    for i in range(checked_order):
        for j in range(checked_order):
            degree = i-j+q
            expected = coefficients[degree] if 0 <= degree < len(coefficients) else 0
            assert reference[i][j] == expected, ("Toeplitz-symbol", p, q, profile, i, j)

    commutators_checked = 0
    for upper in range(q):
        for lower in range(p):
            ul = product((("U", upper), ("L", lower)), eta, xi, product_order)
            lu = product((("L", lower), ("U", upper)), eta, xi, product_order)
            for i in range(checked_order):
                for j in range(checked_order):
                    expected = xi[lower] if (i, j) == (0, 0) else 0
                    assert ul[i][j]-lu[i][j] == expected, ("commutator", p, q, i, j)
            commutators_checked += 1

    ranks, unique_blocks, words_checked = Counter(), set(), 0
    for word in stable_interleavings(p, q):
        value = product(word, eta, xi, product_order)
        difference = [[reference[i][j]-value[i][j] for j in range(checked_order)]
                      for i in range(checked_order)]
        for i, row in enumerate(difference):
            for j, entry in enumerate(row):
                assert entry >= 0, ("entrywise-order", p, q, profile, word, i, j)
                if i >= p or j >= q:
                    assert entry == 0, ("boundary-support", p, q, profile, word, i, j)
        boundary = [row[:q] for row in difference[:p]]
        rank = exact_rank(boundary)
        assert rank <= min(p, q), ("rank", p, q, profile, word, rank)
        ranks[rank] += 1
        unique_blocks.add(tuple(tuple(row[:checked_order]) for row in value[:checked_order]))
        words_checked += 1
    assert words_checked == comb(m, p)
    return {
        "p": p, "q": q, "profile": profile,
        "eta": [str(x) for x in eta], "xi": [str(x) for x in xi],
        "tested_block_order": checked_order, "padded_product_order": product_order,
        "words_checked": words_checked,
        "distinct_tested_products": len(unique_blocks),
        "commutators_checked": commutators_checked,
        "rank_histogram": dict(sorted(ranks.items())),
        "symbol_match": True, "support_first_p_rows_q_columns": True,
        "T0_minus_Tw_entrywise_nonnegative": True, "rank_bound": True,
    }


def check_uniform():
    h = F(4, 27)
    eta, xi = [h], [h, h]
    checked_order, product_order = 8, 12
    words = {
        "4.1": (("L", 0), ("L", 1), ("U", 0)),
        "4.2": (("L", 0), ("U", 0), ("L", 1)),
        "4.3": (("U", 0), ("L", 0), ("L", 1)),
    }
    expected_changes = {
        "4.1": {(0, 0): -2*h, (1, 0): -h*h},
        "4.2": {(0, 0): -h},
        "4.3": {},
    }
    reference = product(words["4.3"], eta, xi, product_order)
    for i in range(checked_order):
        for j in range(checked_order):
            expected = {-1: F(1), 0: 3*h, 1: 3*h*h, 2: h**3}.get(i-j, 0)
            assert reference[i][j] == expected, ("Uniform-reference", i, j)
    rows = []
    for section, word in words.items():
        value = product(word, eta, xi, product_order)
        for i in range(checked_order):
            for j in range(checked_order):
                expected = expected_changes[section].get((i, j), 0)
                assert value[i][j]-reference[i][j] == expected, ("Uniform", section, i, j)
        rows.append({
            "section": section, "word": "".join(kind for kind, label in word),
            "nonzero_Tw_minus_T0": [
                {"row": i, "column": j, "value": str(value)}
                for (i, j), value in expected_changes[section].items()
            ], "passed": True,
        })
    return {"h": str(h), "tested_block_order": checked_order,
            "padded_product_order": product_order, "cases": rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-band", type=int, default=4)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("check_words_results.json"))
    args = parser.parse_args()
    if args.max_band < 1:
        parser.error("--max-band must be positive")
    cases = [check_case(p, q, profile)
             for p in range(1, args.max_band+1)
             for q in range(1, args.max_band+1)
             for profile in ("repeated_root", "distinct_positive_roots")]
    uniform = check_uniform()
    output = {
        "status": "PASS", "date": "2026-10-11", "manuscript_version": "v37",
        "arithmetic": "Python standard-library fractions.Fraction; no floating point",
        "scope": "Every stable interleaving, preserving relative order of each labelled factor type",
        "analytic_role": "Supporting finite checks; the commutator proof establishes infinite support",
        "boundary_convention": "Zero-based indices; corrections have row < p and column < q",
        "bottom_boundary_handling": "p+q extra coordinates beyond each tested principal block",
        "max_p": args.max_band, "max_q": args.max_band,
        "parameter_cases": len(cases),
        "word_products_checked": sum(case["words_checked"] for case in cases),
        "pair_commutators_checked": sum(case["commutators_checked"] for case in cases),
        "uniform_cases_checked": len(uniform["cases"]),
        "cases": cases, "uniform_h_4_over_27": uniform,
    }
    args.output.write_text(json.dumps(output, indent=2, ensure_ascii=False)+"\n", encoding="utf-8")
    print(json.dumps({key: output[key] for key in (
        "status", "parameter_cases", "word_products_checked",
        "pair_commutators_checked", "uniform_cases_checked")}, indent=2))
    print(f"Results: {args.output.resolve()}")


if __name__ == "__main__":
    main()
