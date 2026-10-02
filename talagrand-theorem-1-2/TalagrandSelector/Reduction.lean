/-
Park--Pham, arXiv:2204.10309v2, Theorem 1.2 with positive finite expectation.

This module proves the reduction from the normalized selector bound to
the corrected Theorem 1.2. The normalized bound is proved unconditionally
in TalagrandSelector.Main, which applies this reduction with C = 512.
TalagrandSelector.Extended provides the final positive-finite-expectation
statement, with L = 2048 and no assumption of the normalized bound.

The added hypothesis is `0 < expectation p (selectorValue Lambda)`.
Finiteness is encoded by `BddAbove (weightValues Lambda univ)`. On a finite
ground set with nonnegative weights and 0 < p < 1 this is exactly the
boundedness needed for a finite-valued selector process. The full-set event
has positive probability, so an unbounded full-set value cannot have finite
expectation. The collection Lambda itself may be infinite.

Approximate maximizers avoid any assumption that a supremum is attained.
The reduction supplies the universal constant L = 4*C from the constant C
in Theorem 1.4. There are no custom axioms or proof placeholders.

Lean 4.32.0; mathlib v4.32.0.
Run the whole project: lake build
-/
import Mathlib

open Finset

namespace TalagrandPositiveReduction

noncomputable section

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The covering cost in the paper's definition of p-smallness. -/
def coverCost (p : ℝ) (G : Finset (Finset X)) : ℝ :=
  ∑ T ∈ G, p ^ T.card

/-- Integral, rather than fractional, p-smallness. -/
def IsPSmall (p : ℝ) (F : Finset (Finset X)) : Prop :=
  ∃ G : Finset (Finset X),
    (∀ S ∈ F, ∃ T ∈ G, T ⊆ S) ∧ coverCost p G ≤ (1 : ℝ) / 2

omit [Fintype X] [DecidableEq X] in
theorem isPSmall_empty (p : ℝ) : IsPSmall p (∅ : Finset (Finset X)) := by
  refine ⟨∅, by simp, ?_⟩
  norm_num [coverCost]

omit [Fintype X] [DecidableEq X] in
theorem IsPSmall.mono {p : ℝ} {F G : Finset (Finset X)}
    (hG : IsPSmall p G) (hFG : F ⊆ G) : IsPSmall p F := by
  obtain ⟨A, hA, hcost⟩ := hG
  exact ⟨A, fun S hS => hA S (hFG hS), hcost⟩

/-- Probability that independent Bernoulli-p selectors produce exactly S. -/
def subsetMass (p : ℝ) (S : Finset X) : ℝ :=
  p ^ S.card * (1 - p) ^ (Fintype.card X - S.card)

omit [DecidableEq X] in
theorem subsetMass_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset X) : 0 ≤ subsetMass p S := by
  unfold subsetMass
  positivity

/-- Expectation on the finite Bernoulli sample space. -/
def expectation (p : ℝ) (Z : Finset X → ℝ) : ℝ :=
  ∑ S : Finset X, subsetMass p S * Z S

omit [DecidableEq X] in
theorem expectation_mono {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {Z V : Finset X → ℝ} (h : ∀ S, Z S ≤ V S) :
    expectation p Z ≤ expectation p V := by
  apply Finset.sum_le_sum
  intro S _
  exact mul_le_mul_of_nonneg_left (h S) (subsetMass_nonneg hp hp1 S)

omit [DecidableEq X] in
theorem expectation_div (p d : ℝ) (Z : Finset X → ℝ) :
    expectation p (fun S => Z S / d) = expectation p Z / d := by
  simp only [expectation, mul_div_assoc, Finset.sum_div]

/-- All sums obtainable on S; Lambda may be an arbitrary infinite collection. -/
def weightValues (Lambda : Set (X → ℝ)) (S : Finset X) : Set ℝ :=
  (fun w => ∑ i ∈ S, w i) '' Lambda

def selectorValue (Lambda : Set (X → ℝ)) (S : Finset X) : ℝ :=
  sSup (weightValues Lambda S)

def NonnegativeWeights (Lambda : Set (X → ℝ)) : Prop :=
  ∀ w ∈ Lambda, ∀ i, 0 ≤ w i

/-- Uniform boundedness of the full-set sums. -/
def BoundedWeights (Lambda : Set (X → ℝ)) : Prop :=
  BddAbove (weightValues Lambda Finset.univ)

omit [Fintype X] [DecidableEq X] in
theorem weightValues_nonempty {Lambda : Set (X → ℝ)}
    (hLambda : Lambda.Nonempty) (S : Finset X) :
    (weightValues Lambda S).Nonempty :=
  hLambda.image _

omit [DecidableEq X] in
theorem weightValues_bddAbove {Lambda : Set (X → ℝ)}
    (hnonneg : NonnegativeWeights Lambda) (hbound : BoundedWeights Lambda)
    (S : Finset X) : BddAbove (weightValues Lambda S) := by
  obtain ⟨B, hB⟩ := hbound
  refine ⟨B, ?_⟩
  rintro y ⟨w, hw, rfl⟩
  apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun i _ _ => hnonneg w hw i))
  exact hB ⟨w, hw, rfl⟩

omit [DecidableEq X] in
theorem weight_sum_le_value {Lambda : Set (X → ℝ)}
    (hnonneg : NonnegativeWeights Lambda) (hbound : BoundedWeights Lambda)
    {w : X → ℝ} (hw : w ∈ Lambda) (S : Finset X) :
    ∑ i ∈ S, w i ≤ selectorValue Lambda S :=
  le_csSup (weightValues_bddAbove hnonneg hbound S) ⟨w, hw, rfl⟩

omit [DecidableEq X] in
theorem selectorValue_nonneg {Lambda : Set (X → ℝ)}
    (hLambda : Lambda.Nonempty) (hnonneg : NonnegativeWeights Lambda)
    (hbound : BoundedWeights Lambda) (S : Finset X) :
    0 ≤ selectorValue Lambda S := by
  obtain ⟨w, hw⟩ := hLambda
  exact le_trans (Finset.sum_nonneg (fun i _ => hnonneg w hw i))
    (weight_sum_le_value hnonneg hbound hw S)

omit [Fintype X] [DecidableEq X] in
theorem selectorValue_empty {Lambda : Set (X → ℝ)}
    (hLambda : Lambda.Nonempty) : selectorValue Lambda ∅ = 0 := by
  have hvals : weightValues Lambda ∅ = {0} := by
    ext y
    simp only [weightValues, Set.mem_image, Finset.sum_empty, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, _, rfl⟩; rfl
    · intro hy
      obtain ⟨w, hw⟩ := hLambda
      exact ⟨w, hw, hy.symm⟩
  simp [selectorValue, hvals]

omit [DecidableEq X] in
/-- A strict lower threshold has a witness even when the supremum is not attained. -/
theorem exists_weight_of_lt_value {Lambda : Set (X → ℝ)}
    (hLambda : Lambda.Nonempty) (hnonneg : NonnegativeWeights Lambda)
    (hbound : BoundedWeights Lambda) {S : Finset X} {a : ℝ}
    (ha : a < selectorValue Lambda S) :
    ∃ w ∈ Lambda, a < ∑ i ∈ S, w i := by
  obtain ⟨y, ⟨w, hw, rfl⟩, hy⟩ :=
    (lt_csSup_iff (weightValues_bddAbove hnonneg hbound S)
      (weightValues_nonempty hLambda S)).mp ha
  exact ⟨w, hw, hy⟩

def tailFamily (L p : ℝ) (Lambda : Set (X → ℝ)) : Finset (Finset X) :=
  Finset.univ.filter (fun S => L * expectation p (selectorValue Lambda) ≤
    selectorValue Lambda S)

/-- Maximum of the finitely many local weight sums used in Theorem 1.4. -/
def localValue (F : Finset (Finset X)) (hF : F.Nonempty)
    (w : Finset X → X → ℝ) (W : Finset X) : ℝ :=
  F.sup' hF (fun S => ∑ i ∈ W, w S i)

/-- The substantive Theorem 1.4, expressed with the positive constant C.
Its conclusion `1 <= C*E` is equivalent to `1/C <= E` when C>0.
This is a named PROPOSITION, not a proved theorem or a new axiom.
Weights are extended by zero off S, as allowed in the paper. -/
def NormalizedSelectorBound (C : ℝ) : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X]
    (p : ℝ) (F : Finset (Finset X)) (hF : F.Nonempty)
    (w : Finset X → X → ℝ),
    0 < p → p < 1 →
    (∀ S ∈ F, ∀ i, 0 ≤ w S i) →
    (∀ S ∈ F, ∀ i, i ∉ S → w S i = 0) →
    (∀ S ∈ F, 1 ≤ ∑ i ∈ S, w S i) →
    ¬ IsPSmall p F →
    1 ≤ C * expectation p (localValue F hF w)

/-- The corrected Theorem 1.2 with universal constant L and arbitrary Lambda.
Positive expectation is an explicit hypothesis; boundedness handles finiteness. -/
def PositiveTheorem12 (L : ℝ) : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X]
    (p : ℝ) (Lambda : Set (X → ℝ)),
    0 < p → p < 1 → Lambda.Nonempty →
    NonnegativeWeights Lambda → BoundedWeights Lambda →
    0 < expectation p (selectorValue Lambda) →
    IsPSmall p (tailFamily L p Lambda)

/-- The normalized selector bound implies positive-expectation Theorem 1.2.
The parameter hcore is supplied by `normalized_selector_bound` in Main. -/
theorem positive_theorem12_of_normalized_bound
    {C : ℝ} (hC : 0 < C) (hcore : NormalizedSelectorBound C) :
    PositiveTheorem12 (4 * C) := by
  intro X _ _ p Lambda hp hp1 hLambda hnonneg hbound hM
  classical
  let M := expectation p (selectorValue Lambda)
  let F := tailFamily (4 * C) p Lambda
  let d := 2 * C * M
  have hd : 0 < d := by dsimp [d, M]; positivity
  by_contra hsmall
  have hF : F.Nonempty := by
    by_contra hn
    have hFe : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    apply hsmall
    change IsPSmall p F
    rw [hFe]
    exact isPSmall_empty p
  have hwitness : ∀ S ∈ F, ∃ w ∈ Lambda, d < ∑ i ∈ S, w i := by
    intro S hS
    have ht : (4 * C) * M ≤ selectorValue Lambda S :=
      (Finset.mem_filter.mp hS).2
    apply exists_weight_of_lt_value hLambda hnonneg hbound
    have hCM : 0 < C * M := mul_pos hC hM
    dsimp [d]
    nlinarith
  choose v hv hlarge using hwitness
  let w : Finset X → X → ℝ := fun S i =>
    if hS : S ∈ F then (if i ∈ S then v S hS i / d else 0) else 0
  have hw_nonneg : ∀ S ∈ F, ∀ i, 0 ≤ w S i := by
    intro S hS i
    dsimp [w]
    rw [dif_pos hS]
    split_ifs
    · exact div_nonneg (hnonneg _ (hv S hS) i) hd.le
    · exact le_rfl
  have hw_support : ∀ S ∈ F, ∀ i, i ∉ S → w S i = 0 := by
    intro S hS i hi
    simp [w, hS, hi]
  have hw_normalized : ∀ S ∈ F, 1 ≤ ∑ i ∈ S, w S i := by
    intro S hS
    have heq : (∑ i ∈ S, w S i) = (∑ i ∈ S, v S hS i) / d := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      simp [w, hS, hi]
    rw [heq]
    exact (le_div_iff₀ hd).mpr (by simpa using (hlarge S hS).le)
  have hlocal : ∀ W, localValue F hF w W ≤ selectorValue Lambda W / d := by
    intro W
    apply Finset.sup'_le hF
    intro S hS
    calc
      (∑ i ∈ W, w S i) ≤ ∑ i ∈ W, v S hS i / d := by
        apply Finset.sum_le_sum
        intro i _
        dsimp [w]
        rw [dif_pos hS]
        split_ifs with hi
        · exact le_rfl
        · exact div_nonneg (hnonneg _ (hv S hS) i) hd.le
      _ = (∑ i ∈ W, v S hS i) / d := (Finset.sum_div _ _ _).symm
      _ ≤ selectorValue Lambda W / d :=
        div_le_div_of_nonneg_right (weight_sum_le_value hnonneg hbound (hv S hS) W)
          hd.le
  have hE : expectation p (localValue F hF w) ≤ M / d := by
    calc
      expectation p (localValue F hF w) ≤
          expectation p (fun W => selectorValue Lambda W / d) :=
        expectation_mono hp.le hp1.le hlocal
      _ = M / d := expectation_div p d _
  have hlower : 1 ≤ C * expectation p (localValue F hF w) :=
    hcore X p F hF w hp hp1 hw_nonneg hw_support hw_normalized hsmall
  have hupper := mul_le_mul_of_nonneg_left hE hC.le
  have hhalf : C * (M / d) = (1 : ℝ) / 2 := by
    dsimp [d]
    field_simp [ne_of_gt hC, show M ≠ 0 from ne_of_gt hM]
  rw [hhalf] at hupper
  linarith

/-- Existence of a universal constant, still conditional on Theorem 1.4. -/
theorem exists_positive_theorem12_of_normalized_bound
    (hcore : ∃ C : ℝ, 0 < C ∧ NormalizedSelectorBound C) :
    ∃ L : ℝ, 0 < L ∧ PositiveTheorem12 L := by
  obtain ⟨C, hC, hcore⟩ := hcore
  exact ⟨4 * C, by positivity, positive_theorem12_of_normalized_bound hC hcore⟩

end
end TalagrandPositiveReduction

#print axioms TalagrandPositiveReduction.positive_theorem12_of_normalized_bound
#print axioms TalagrandPositiveReduction.exists_positive_theorem12_of_normalized_bound
