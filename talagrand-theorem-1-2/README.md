# Corrected Talagrand selector theorem in Lean

This project proves the positive-finite-expectation version of Theorem 1.2
of Park and Pham, with the explicit universal constant **L = 2048**.
The normalized selector bound used in the reduction is also proved here;
it is not a hypothesis of the final theorem.

## Statement

Let X be a finite set, 0 < p < 1, and let Lambda be any collection of
nonnegative real weight vectors on X. The collection may be infinite.
Write

```
Z(S) = sup { sum (i in S) w(i) : w in Lambda }
E    = sum (S subset X) p^|S| (1-p)^(|X|-|S|) Z(S).
```

The supremum and expectation in the public interface take values in
the extended nonnegative reals. Assuming **0 < E < infinity**, the family

```
F = { S subset X : 2048 * E <= Z(S) }
```

is p-small: there is a family G such that every S in F contains some T in G,
and the sum of p^|T| over T in G is at most 1/2.

The final declaration is
`TalagrandSelector.theorem_1_2_finite_expectation`. Its only mathematical
hypotheses are 0 < p < 1, nonnegative weights, and 0 < E < infinity.
Nonemptiness and boundedness of Lambda's full-set sums are derived from
these hypotheses. No attainment of the supremum is assumed.

Strict positivity matters: for the zero process, a non-strict tail inequality
includes the empty set, which cannot belong to a p-small family.

## Build and check

Requirements: a normal Lean/Elan installation, Git, and network access for
the pinned dependencies on the first build.

```
lake exe cache get
lake build
lake env lean Audit.lean
lake env lean TalagrandTheorem12.lean
```

Lean is pinned to **4.32.0**. Mathlib is pinned to
`81a5d257c8e410db227a6665ed08f64fea08e997`; the remaining dependency revisions
are recorded in `lake-manifest.json`.

`TalagrandTheorem12.lean` is the complete single-file version: it imports
only Mathlib and contains all the proofs in this project. Compile this file
on its own; do not import it together with `TalagrandSelector`, since the
two versions intentionally declare the same names.

`Audit.lean` prints the full theorem type and the axiom dependencies of the
normalized bound and both final interfaces. The verified dependencies are
exactly `propext`, `Classical.choice`, and `Quot.sound`. There are no proof
placeholders or additional axioms. The actual compilation and audit output
is included in `verification/`.

The zip contains source code and dependency pins. Mathlib and compiled
dependency caches are fetched by the build commands above.

## Proof structure

The proof adapts the clipped-threshold and minimum-witness argument of
Bednorz, Martynek, and Meller to Bernoulli sampling. It proves the corrected
Park--Pham theorem, rather than transcribing the original proof line by line.

| Module | Proved content |
| --- | --- |
| `Reduction` | Definitions of p-smallness and selector expectations; reduction using approximate maximizers. |
| `Threshold` | Clipped-weight thresholds, sparse heavy sets, and the exchange inequality. |
| `Witness` | Lexicographically minimal witnesses and fragment recovery. |
| `Bernoulli` | Finite-sum probability identities, independent thinning, and augmentation weights. |
| `Counting` | Encoding fibers inject into the powerset of one witness. |
| `Numeric` | The finite geometric estimates. |
| `CoverCost` | Expected covering cost and the bound on the probability of a bad sample. |
| `Main` | The normalized bound with C = 512, and Theorem 1.2 with L = 4C = 2048. |
| `Extended` | The final interface with exactly positive, finite extended expectation. |

At density q = 128p, the witness count bounds the expected bad-sample cover
cost by 1/4. Non-smallness then gives an expected selector value at least
1/4. Independent thinning yields the normalized lower bound 1/512 at
density p. For larger p, the elementary linear expectation bound suffices.
Approximate maximizers transfer this finite-family result to an arbitrary
weight collection without assuming its supremum is attained.

## References

- Jinyoung Park and Huy Tuan Pham, *On a conjecture of Talagrand on selector
  processes and a consequence on positive empirical processes*,
  [arXiv:2204.10309v2](https://arxiv.org/abs/2204.10309v2), Theorems 1.2 and 1.4.
- Witold Bednorz, Rafal Martynek, and Rafal Meller, *The suprema of selector
  processes with the application to positive infinitely divisible processes*,
  [arXiv:2212.14636v3](https://arxiv.org/abs/2212.14636v3), Section 3.1.
