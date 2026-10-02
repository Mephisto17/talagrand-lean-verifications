# Kahn–Kalai theorem: Lean code and verification scope

This project proves

    p_c(F) ≤ 100000 · q(F) · log₂ ell(F),

where ell(F) = max(2, the largest size of a minimal member of F), and q is
**the integral expectation threshold**, defined by a cover of cost at most 1/2.
It does not substitute the fractional expectation threshold.

## What this verifies

The complete quantitative proof follows Tran–Vu's inductive proof, using
Dan Clemens Posch's existing formalization. The files under `KahnKalai/` and
`Solution.lean` are copied without modification from:

- https://github.com/dcposch/kahn-kalai-lean
- Commit: `641aa75f8e873d31442f2f7c317b2e7582a26d94`
- License: Apache-2.0; original author and copyright notices are retained.

`Paper.lean` adds a bridge to the definitions in the supplied attachment,
Park–Pham, *A Proof of the Kahn–Kalai Conjecture*, arXiv:2203.17207v2,
and directly formalizes several steps of that paper.

| Paper statement | Lean declaration | Scope |
|---|---|---|
| Minimum fragment exists, §2.1 | `ParkPhamPaper.exists_minimumFragment` | Proved from a finite minimum |
| T is contained in S and disjoint from W | `fragment_subset`, `fragment_disjoint` | Proved |
| Equation (16), T ⊆ S-hat | `ParkPhamPaper.equation_16` | Proved, including arbitrary ties |
| Counting the pairs in (15) | `ParkPhamPaper.fragmentPairs_card_le` | Proved with the stronger factor binomial(ell,m) |
| Weighted fixed-size counting bound | `ParkPhamPaper.weighted_fragmentPairs_bound` | Proved |
| Iteration invariants (8), (9) | `residual_cover_invariant`, `residual_lift_invariant` | Proved for the chosen-fragment recursion |
| Proposition 2.3 | `ParkPhamPaper.proposition_2_3` | Proved, given the terminal size bound |
| Cheap cover implies success | `ParkPhamPaper.success_of_cheap_cover` | Proved |
| Original definition of p-smallness | `isPSmall_iff_coverCost` | Proved equivalent to the attained minimum cost |
| Reduction to minimal members | `threshold_minimals`, `expectationThreshold_minimals` | Proved |
| Theorem 1.1, with ell(F) | `ParkPhamPaper.theorem_1_1_explicit` | Complete proof via Tran–Vu |
| Theorem 1.1 for increasing F, with direct definitions of both thresholds | `ParkPhamPaper.theorem_1_1_increasing` | Complete proof via Tran–Vu |

This is **not a line-by-line Lean verification of the entire attached
Park–Pham proof**. In particular, its particular random iteration, choice
of sampling sizes, and asymptotic error estimate (20) are not formalized
here. The completed theorem uses Tran–Vu's induction in their place.
No unproved version of any of these omitted claims is imported or assumed.

The thresholds use infimum/supremum definitions. For a nontrivial increasing
family these are the standard critical and expectation thresholds; the
formal statement does not additionally prove the characterization of the
critical probability as the unique root of mu_p(F) = 1/2. Degenerate families
are allowed in the code with Lean's infimum conventions.

The finite ground set is represented by a finite type `α`; a hypergraph is
`Finset (Finset α)`. Subsets of `α` are exactly subsets of this ground set.
All logarithms in the main bound are base 2. The constant 100000 is explicit
and is not asserted to be optimal.

## Files

- `KahnKalaiVerified.lean`: self-contained source, apart from mathlib. It
  combines the same proofs into one file; it does not import this project's
  compiled modules.
- `KahnKalai/` and `Solution.lean`: the original, licensed theorem proof.
- `Paper.lean`: added paper-specific formalization and theorem statements.
- `Audit.lean`: transitive axiom reports for eleven substantive results.
- `verification/`: compiler version, build log, and axiom reports.
- `verify.sh`: rebuilds the proofs and rejects nonstandard axioms.

The upstream `Challenge.lean`, a statement-only comparison file containing
proof placeholders, is deliberately excluded from this deliverable. It is
not imported by any of the delivered proof files.

## Reproduce

Install Lean using https://lean-lang.org/install/ and ensure `lean` and
`lake` are available. In this directory run:

```sh
lake exe cache get
./verify.sh
```

The project pins Lean 4.32.0 and mathlib v4.32.0 (exact dependency commits
are in `lake-manifest.json`). With that version of mathlib already available,
the standalone file can also be checked with:

```sh
lake env lean KahnKalaiVerified.lean
```

Run it by itself, not after importing `Paper` into the same file: it already
contains all project definitions and proofs.

The permitted transitive axioms are only `propext`, `Classical.choice`, and
`Quot.sound`, the standard foundations used by mathlib. The verification
script rejects `sorryAx` and any additional axioms. None of the delivered
proofs uses `native_decide` or an externally trusted boolean reduction.

## Mathematical sources

- Jinyoung Park and Huy Tuan Pham, *A Proof of the Kahn–Kalai Conjecture*,
  https://arxiv.org/abs/2203.17207v2 (the supplied PDF).
- Phuc Tran and Van Vu, *A Short Proof of Kahn–Kalai Conjecture*,
  Electronic Journal of Combinatorics 31(3), P3.2 (2024),
  https://doi.org/10.37236/12266 and https://arxiv.org/abs/2303.02144.
- The code source and exact revision are listed above. Reuse of that code
  is attribution to an existing formalization, not a claim to have written
  its entire proof from scratch.
