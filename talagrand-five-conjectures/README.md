# Five Talagrand conjectures: complete Lean proofs

This project proves the intended statements of Conjectures 9.1, 7.12, 7.9,
7.3, and 7.2. Version 0.2 replaces the public results for 7.9 and 7.2 using
the direct proofs in the two newly supplied articles:

- Chen Li, *On p-spread measures*, arXiv:2609.08967v1, Theorem 1.9.
- Xuan Fang and Tianyu Wang, *A Note on a Result of Chen Li*,
  arXiv:2609.18458v1, Theorem 1.2 and Corollary 1.3.

The previous Park--Talagrand proofs of 9.1, 7.12, and 7.3 and the
parameter-dependent Theorem 2.1 remain included. The direct arguments for
Li and Fang--Wang use the shared finite Walsh identities and second-moment
calculations; they do not invoke the logarithmic inequality or Conjecture 9.1.

All supporting lemmas are included. None of the conjectures, the Walsh
identities, the key vanishing lemma, or the covering implications are assumed.

## Results and constants

All names below are in the namespace `TalagrandConjectures`.

| Result | Constant | Public declaration |
| --- | --- | --- |
| Park--Talagrand Theorem 2.1 | rho = p(1-a)/((1-p)a) | `park_talagrand_theorem_2_1` |
| Conjecture 9.1, logarithmic down-class form | a = 1/2 | `conjecture_9_1` |
| Conjecture 9.1, up-class form with corrected sign | a = 1/2 | `conjecture_9_1_up` |
| Multiplicative formulation (9.2) | a = 1/2 | `conjecture_9_1_multiplicative` |
| Conjecture 7.12, probability certificate | a = 1/2 | `conjecture_7_12` |
| Conjecture 7.9, stochastic domination on all up-classes | every 0 < a <= (sqrt(5)-1)/2 | `conjecture_7_9` |
| Conjecture 7.3, fractional covering of the exceptional family | a = 1/2 | `conjecture_7_3` |
| Conjecture 7.2, original cost-1/2 formulation | q = 3 | `conjecture_7_2` |
| Li Theorem 1.9 | mu_p(A) <= (1-p)/(2-p) if Bad_2(A) carries a p-spread law | `li_theorem_1_9` |
| Li two-union spread conclusion | density >= 1/2 | `li_no_spread_badTwo` |
| Explicit two-union weak p-smallness | density >= 2/3; cover cost <= 1/2 | `li_weaklySmall_badTwo` |
| Explicit two-union weak (p/2)-smallness | density >= 1/2; cover cost <= 1/2 | `li_weaklySmall_badTwo_half` |
| Fang--Wang Theorem 1.2 | tq(1-p)/(p(1-t)) <= 1 | `fang_wang_theorem_1_2` |
| Fang--Wang equation (1.4) | target density tq/(1-t+tq) | `fang_wang_target_density` |

For 7.9, the universal constant increases from 1/2 to approximately
0.618034, and the theorem accepts every positive smaller constant. The
full parameter-dependent domination theorem is also provided. Domination
is formalized by inequalities for **all increasing events**, exactly the
paper's equation (1.2) and the original Talagrand Definition 7.8. An explicit
containing coupling is not constructed.

For 7.2, there are two different normalizations to keep distinct. Li's
Theorem 1.9 and its two-union no-spread conclusion are proved exactly.
Absence of a supported p-spread probability is not silently equated with a
fractional cover of cost at most 1/2. We additionally construct the coefficients

```
c(I) = 0                                      if I is empty,
c(I) = fhat_p(I)^2 ((1-p)/p)^|I| / mu_p(A)^2   otherwise.
```

For a nonempty-density family, these cover Bad_2(A). At radius r, their
cost is at most b*r*(mu_p(A)-mu_p(A)^2)/mu_p(A)^2 whenever
b=(1-p)/p and 0 <= b*r <= 1. This is `li_fractional_certificate`.
At density >= 2/3 it proves original weak p-smallness with **two unions**.
The exact original statement couples the density threshold to the number
of unions as 1-1/q; the updated `conjecture_7_2` therefore uses **q=3**
instead of q=4. At density >= 1/2 the certificate proves weak (p/2)-smallness.
We do not label the no-spread result a cost-1/2 cover at p and density 1/2.

The previous constants remain available as `conjecture_7_9_half` and
`conjecture_7_2_q4` for comparison; the main public names above use the
improved results. The numbering 7.9 and 7.12 follows the original Talagrand
PDF and the user's request; Fang--Wang refers to these as 7.8 and 7.11.

## Precise conventions and corrections

`Cube X` is the set of functions from the finite ground type X to Bool.
It represents subsets of X. Its pointwise order is inclusion, `support`
gives the corresponding finite set, and `monoWeight_eq_pow` proves that
`monoWeight r I` is exactly r to the cardinality of I.

`mass p` is the independent Bernoulli-p law. `measure p A` is its finite
sum on A. `theta a A J` is the probability that an independently thinned
subset of J, retaining each coordinate with probability a, belongs to A.
`Law` consists of nonnegative weights with total exactly one; `Law.Spread r`
bounds the probability of containing I by r to the cardinality of I.

`WeaklySmall` uses nonnegative coefficients c(I), covering each target J
by sum over I contained in J at least one, with total cost
sum c(I) r^|I| at most **1/2**. The theorem
`WeaklySmall.probability_form` explicitly converts this into Talagrand's
Definition 6.1. `Law.Carried` means that every positive-weight atom belongs
to the family, equivalent to giving that family probability one on this finite cube.

Two printing inconsistencies in the 2010 paper need explicit treatment:

1. Its displayed (9.1) omits a minus sign on the right. We prove
   minus the average of log(1-theta) <= minus log(1-mu), equivalently
   log(mu(D)) <= the average of log(theta(D)) for nonempty down-classes D.
   This agrees with its multiplicative formula (9.2) and the uploaded proof.
2. We use the kernel in displayed (7.13), including value **1** at the
   empty set. The sentence assigning h(empty,J)=0 near (7.12) conflicts
   with that displayed formula and the subsequent constant-term argument.
   The probability certificate constructed here may put mass at the empty set.

These choices are visible in the final theorem types. The code does not
claim to prove the inconsistent literal variants.

## Build and verification

The project pins Lean **4.32.0** and Mathlib commit
`81a5d257c8e410db227a6665ed08f64fea08e997`.

With Lean/Elan, Git, and Python 3 installed:

```
lake exe cache get
python3 scripts/verify.py
```

The verification script executes these commands and checks all reported
axiom dependencies:

```
lake build
lake env lean Audit.lean
lake env lean TalagrandFiveConjectures.lean
```

The standalone file imports only Mathlib and contains the entire proof.
Do not import it together with the modular `TalagrandConjectures` library:
both intentionally declare the same theorem names. To regenerate it after
editing the modules, run `python3 scripts/amalgamate.py`.

The axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
There are no proof placeholders or custom axioms. Actual build logs, theorem
types, axiom reports, exit codes, and source hashes are in `verification/`.
The archive includes sources and dependency pins; dependency sources and
compiled caches are downloaded by the first build command.

## Proof map

| Module | Contents |
| --- | --- |
| `Basic` | Finite Bernoulli law, thinning, spreadness, and fractional covers. |
| `Fourier` | Biased Walsh reconstruction, Parseval, multilinear interpolation, and product moments. |
| `Extrapolation` | The extrapolated random coordinates, exact first and second moments, vanishing on hereditary forbidden faces, and Cauchy--Schwarz. |
| `Energy` | The nonnegative Fourier-square polynomial and its cost under a spread law. |
| `Logarithmic` | The logarithmic bound, Conjecture 9.1, and the earlier half-thinning result. |
| `FangWang` | Signed kernel, normalization, pointwise square bound, positive majorant, direct domination, and the golden-ratio constant. |
| `Certificates` | Explicit fractional certificates, padding to a probability measure, and Conjectures 7.12 and 7.3. |
| `Unions` | Union obstructions, complementary thinning, and the earlier q=4 result. |
| `Li` | Signed-kernel diagonalization and vanishing, the exact spectral bound, explicit fractional certificates, and the improved Conjecture 7.2. |
| `Main` | The uploaded theorem's exact parameters, the multiplicative and corrected up-class forms, and the cardinality bridge. |

The direct kernel proofs share algebraic infrastructure with the existing
formalization. `lifted_eq_extension` identifies Fang--Wang's signed kernel
operator with the multilinear lift; `li_lift_is_kernel` does the same for
Li's kernel. The zero pattern, square/spectral bounds, and all covering
certificates are proved. No separation theorem or conjecture is assumed.
Only the results listed above are formalized: Li's additional functional
and coupling theorems in Section 3 are outside this revision.

## Sources

- Chen Li, *On p-spread measures*,
  [arXiv:2609.08967v1](https://arxiv.org/abs/2609.08967v1), Theorem 1.9 and Corollary 3.1.
- Xuan Fang and Tianyu Wang, *A Note on a Result of Chen Li*,
  [arXiv:2609.18458v1](https://arxiv.org/abs/2609.18458v1), Theorem 1.2,
  Corollary 1.3, and Sections 2--4.

- Jinyoung Park and Michel Talagrand, *AI's solution of Conjecture 9.1*,
  [arXiv:2609.33644v1](https://arxiv.org/abs/2609.33644v1), Theorem 2.1 and Section 3.
- Michel Talagrand, *Are many small sets explicitly small?*, STOC 2010,
  [author's PDF](https://michel.talagrand.net/prizes/small.pdf), Sections 6, 7, and 9.
