import Mathlib

/-!
# Corrected Park--Pham Conjecture 5.7: complete proof

For an arbitrary collection of nonnegative weights on a finite ground set,
0 < p < 1 and 0 < E[Z] < infinity imply that {S | Z(S) >= 2048 * E[Z]}
is p-small.

Final theorem: TalagrandSelector.conjecture_5_7_finite_expectation.
The normalized bound is PROVED in this file, not assumed.
The proof adapts the clipped-threshold witness argument of
Bednorz--Martynek--Meller, arXiv:2212.14636v3, Section 3.1.
Target: Park--Pham, arXiv:2204.10309v2, Conjecture 5.7 with positive finite
expectation. No proof placeholders or custom axioms are used.

Lean 4.32.0; mathlib commit 81a5d257c8e410db227a6665ed08f64fea08e997.
Run within the supplied project: lake env lean TalagrandConjecture57.lean
This single file imports only Mathlib. Do not combine it with imports of
the modular TalagrandSelector library, which defines the same names.
-/


/-! ## Reduction -/

/-
Park--Pham, arXiv:2204.10309v2, Conjecture 5.7 with positive finite expectation.

This module proves the reduction from the normalized selector bound to
the corrected Conjecture 5.7. The normalized bound is proved unconditionally
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

/-- The corrected Conjecture 5.7 with universal constant L and arbitrary Lambda.
Positive expectation is an explicit hypothesis; boundedness handles finiteness. -/
def PositiveConjecture57 (L : ℝ) : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X]
    (p : ℝ) (Lambda : Set (X → ℝ)),
    0 < p → p < 1 → Lambda.Nonempty →
    NonnegativeWeights Lambda → BoundedWeights Lambda →
    0 < expectation p (selectorValue Lambda) →
    IsPSmall p (tailFamily L p Lambda)

/-- The normalized selector bound implies positive-expectation Conjecture 5.7.
The parameter hcore is supplied by `normalized_selector_bound` in Main. -/
theorem positive_conjecture_5_7_of_normalized_bound
    {C : ℝ} (hC : 0 < C) (hcore : NormalizedSelectorBound C) :
    PositiveConjecture57 (4 * C) := by
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
theorem exists_positive_conjecture_5_7_of_normalized_bound
    (hcore : ∃ C : ℝ, 0 < C ∧ NormalizedSelectorBound C) :
    ∃ L : ℝ, 0 < L ∧ PositiveConjecture57 L := by
  obtain ⟨C, hC, hcore⟩ := hcore
  exact ⟨4 * C, by positivity, positive_conjecture_5_7_of_normalized_bound hC hcore⟩

end
end TalagrandPositiveReduction


/-! ## Threshold -/

/-! Clipped-weight thresholds, following Bednorz--Martynek--Meller,
arXiv:2212.14636v3, Section 3.1. All arguments here are proved. -/

open Finset
namespace TalagrandSelector
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

def clipped (w : X → ℝ) (a : ℝ) (W : Finset X) : ℝ :=
  ∑ i ∈ W, min (w i) a

def balance (w : X → ℝ) (W : Finset X) (a : ℝ) : ℝ :=
  clipped w a W - clipped w a univ / 2

def thresholdSet (w : X → ℝ) (W : Finset X) : Set ℝ :=
  {a | 0 ≤ a ∧ a ≤ ∑ i, w i ∧ 0 ≤ balance w W a}

def threshold (w : X → ℝ) (W : Finset X) : ℝ :=
  sSup (thresholdSet w W)

def heavy (w : X → ℝ) (W : Finset X) : Finset X :=
  univ.filter (fun i => threshold w W < w i)

theorem clipped_zero (w : X → ℝ) (hn : ∀ i, 0 ≤ w i) (W : Finset X) :
    clipped w 0 W = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact min_eq_right (hn i)

theorem threshold_greatest (w : X → ℝ) (hn : ∀ i, 0 ≤ w i)
    (W : Finset X) : IsGreatest (thresholdSet w W) (threshold w W) := by
  have hc : Continuous (balance w W) := by
    unfold balance clipped
    fun_prop
  have hclosed : IsClosed (thresholdSet w W) :=
    isClosed_Ici.inter (isClosed_Iic.inter (isClosed_le continuous_const hc))
  have hne : (thresholdSet w W).Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨le_rfl, Finset.sum_nonneg (fun i _ => hn i), ?_⟩
    simp [balance, clipped_zero w hn]
  have hb : BddAbove (thresholdSet w W) :=
    ⟨∑ i, w i, fun _ ha => ha.2.1⟩
  exact hclosed.isGreatest_csSup hne hb

theorem threshold_nonneg (w : X → ℝ) (hn : ∀ i, 0 ≤ w i) (W : Finset X) :
    0 ≤ threshold w W := (threshold_greatest w hn W).1.1

theorem balance_threshold_nonneg (w : X → ℝ) (hn : ∀ i, 0 ≤ w i)
    (W : Finset X) : 0 ≤ balance w W (threshold w W) :=
  (threshold_greatest w hn W).1.2.2

theorem threshold_lt_total (w : X → ℝ) (hn : ∀ i, 0 ≤ w i)
    (W : Finset X) (hbad : (∑ i ∈ W, w i) < (∑ i, w i) / 2) :
    threshold w W < ∑ i, w i := by
  have hi : ∀ i, w i ≤ ∑ j, w j := fun i =>
    Finset.single_le_sum (fun j _ => hn j) (mem_univ i)
  have hbal : balance w W (∑ i, w i) < 0 := by
    simpa [balance, clipped, min_eq_left (hi _)] using sub_neg.mpr hbad
  have ha := (threshold_greatest w hn W).1
  apply lt_of_le_of_ne ha.2.1
  intro heq
  rw [heq] at ha
  linarith [ha.2.2]

theorem clipped_step (w : X → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hb : ∀ i, a < w i → b ≤ w i) (W : Finset X) :
    clipped w b W = clipped w a W +
      (b - a) * ((W.filter (fun i => a < w i)).card : ℝ) := by
  have heq : ∀ i, min (w i) b = min (w i) a + if a < w i then b - a else 0 := by
    intro i
    by_cases hi : a < w i
    · rw [if_pos hi, min_eq_right (hb i hi), min_eq_right hi.le]
      ring
    · rw [if_neg hi, min_eq_left (le_of_not_gt hi),
        min_eq_left ((le_of_not_gt hi).trans hab), add_zero]
  simp only [clipped, heq, Finset.sum_add_distrib]
  simp [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_comm]
  <;> ring

/-- The threshold leaves fewer than half of the heavy coordinates in a bad sample. -/
theorem heavy_sparse (w : X → ℝ) (hn : ∀ i, 0 ≤ w i)
    (W : Finset X) (hbad : (∑ i ∈ W, w i) < (∑ i, w i) / 2) :
    2 * (W ∩ heavy w W).card < (heavy w W).card := by
  classical
  let a := threshold w W
  let B := ∑ i, w i
  let A := insert B ((heavy w W).image w)
  have hA : A.Nonempty := Finset.insert_nonempty _ _
  let b := A.min' hA
  have hab : a < b := by
    have hm : b ∈ A := Finset.min'_mem A hA
    rcases Finset.mem_insert.mp hm with he | he
    · exact he ▸ threshold_lt_total w hn W hbad
    · obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp he
      rw [← heq]
      exact (Finset.mem_filter.mp hi).2
  have hbB : b ≤ B := Finset.min'_le A B (Finset.mem_insert_self _ _)
  have hbw : ∀ i, a < w i → b ≤ w i := by
    intro i hi
    apply Finset.min'_le A
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨i, Finset.mem_filter.mpr ⟨mem_univ _, hi⟩, rfl⟩)
  have hnegative : balance w W b < 0 := by
    by_contra h
    have hmem : b ∈ thresholdSet w W :=
      ⟨(threshold_nonneg w hn W).trans hab.le, hbB, le_of_not_gt h⟩
    exact (not_le_of_gt hab) ((threshold_greatest w hn W).2 hmem)
  have hW : W.filter (fun i => a < w i) = W ∩ heavy w W := by
    ext i
    simp [heavy, a]
  have hu : univ.filter (fun i => a < w i) = heavy w W := rfl
  have hstepW := clipped_step w a b hab.le hbw W
  have hstepU := clipped_step w a b hab.le hbw univ
  rw [hW] at hstepW
  rw [hu] at hstepU
  have hpositive := balance_threshold_nonneg w hn W
  change 0 ≤ clipped w a W - clipped w a univ / 2 at hpositive
  unfold balance at hnegative
  rw [hstepW, hstepU] at hnegative
  have hcard : (2 : ℝ) * ((W ∩ heavy w W).card : ℝ) < (heavy w W).card := by
    by_contra hc
    have hm : 0 ≤ (b-a) *
        (((W ∩ heavy w W).card : ℝ) - (heavy w W).card / 2) :=
      mul_nonneg (sub_nonneg.mpr hab.le) (by linarith)
    nlinarith
  exact_mod_cast hcard

/-- Removing a fixed number of coordinates from Z loses at most that number
times the clipping level. The original removed coordinates all have that level. -/
theorem clipped_exchange (w : X → ℝ) (a : ℝ) (W T Y : Finset X)
    (hd : Disjoint W T) (hT : ∀ i ∈ T, a ≤ w i)
    (hY : Y ⊆ W ∪ T) (hcard : Y.card = W.card) :
    clipped w a W ≤ clipped w a Y := by
  have hclipT : clipped w a T = (T.card : ℝ) * a := by
    simp only [clipped]
    calc
      (∑ i ∈ T, min (w i) a) = ∑ i ∈ T, a := by
        apply Finset.sum_congr rfl
        intro i hi
        exact min_eq_right (hT i hi)
      _ = _ := by simp
  have hsplit : clipped w a (W ∪ T) = clipped w a W + clipped w a T :=
    Finset.sum_union hd
  have hsplitY : clipped w a (W ∪ T) = clipped w a Y +
      clipped w a ((W ∪ T) \ Y) := by
    simpa [clipped, add_comm] using
      (Finset.sum_sdiff (f := fun i => min (w i) a) hY).symm
  have hc : ((W ∪ T) \ Y).card = T.card := by
    rw [Finset.card_sdiff_of_subset hY, Finset.card_union_of_disjoint hd, hcard]
    omega
  have hle : clipped w a ((W ∪ T) \ Y) ≤ (T.card : ℝ) * a := by
    calc
      clipped w a ((W ∪ T) \ Y) ≤ ∑ _i ∈ (W ∪ T) \ Y, a :=
        Finset.sum_le_sum (fun i _ => min_le_right _ _)
      _ = _ := by simp [hc]
  rw [hclipT] at hsplit
  linarith

/-- Equal-size samples with the same augmented set compare their clipping thresholds. -/
theorem threshold_exchange (w : X → ℝ) (hn : ∀ i, 0 ≤ w i)
    (W T Y : Finset X) (hd : Disjoint W T)
    (hT : T ⊆ heavy w W) (hY : Y ⊆ W ∪ T) (hcard : Y.card = W.card) :
    threshold w W ≤ threshold w Y := by
  apply (threshold_greatest w hn Y).2
  have hmem := (threshold_greatest w hn W).1
  refine ⟨hmem.1, hmem.2.1, ?_⟩
  have hex := clipped_exchange w (threshold w W) W T Y hd
    (fun i hi => ((Finset.mem_filter.mp (hT hi)).2).le) hY hcard
  have hm := hmem.2.2
  change 0 ≤ clipped w (threshold w W) W - clipped w (threshold w W) univ / 2 at hm
  unfold balance
  linarith

theorem heavy_antitone_threshold {w : X → ℝ} {W Y : Finset X}
    (h : threshold w W ≤ threshold w Y) : heavy w Y ⊆ heavy w W := by
  intro i hi
  exact Finset.mem_filter.mpr ⟨mem_univ _, h.trans_lt (Finset.mem_filter.mp hi).2⟩

end
end TalagrandSelector


/-! ## Witness -/

open Finset
namespace TalagrandSelector
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

structure WeightSystem (X : Type) [Fintype X] [DecidableEq X] where
  family : Finset (Finset X)
  weight : Finset X → X → ℝ
  nonneg : ∀ H ∈ family, ∀ i, 0 ≤ weight H i
  support : ∀ H ∈ family, ∀ i, i ∉ H → weight H i = 0
  normalized : ∀ H ∈ family, 1 ≤ ∑ i ∈ H, weight H i

namespace WeightSystem
variable (D : WeightSystem X)

def Bad (W : Finset X) : Prop :=
  ∀ H ∈ D.family, (∑ i ∈ W, D.weight H i) < (1 : ℝ) / 2

theorem heavy_subset {H : Finset X} (hH : H ∈ D.family) (W : Finset X) :
    heavy (D.weight H) W ⊆ H := by
  intro i hi
  by_contra hn
  have hw := (Finset.mem_filter.mp hi).2
  rw [D.support H hH i hn] at hw
  exact (not_lt_of_ge (threshold_nonneg _ (D.nonneg H hH) W)) hw

def candidates (W I : Finset X) : Finset (Finset X) :=
  D.family.filter (fun H => heavy (D.weight H) W \ W ⊆ I)

def score (W H : Finset X) : ℕ ×ₗ ℕ :=
  toLex ((heavy (D.weight H) W).card, (heavy (D.weight H) W \ W).card)

theorem candidates_nonempty (W I : Finset X) (hI : I ∈ D.family) :
    (D.candidates W I).Nonempty :=
  ⟨I, Finset.mem_filter.mpr ⟨hI, Finset.sdiff_subset.trans (D.heavy_subset hI W)⟩⟩

def chosen (W I : Finset X) (hI : I ∈ D.family) : Finset X :=
  Classical.choose (Finset.exists_min_image (D.candidates W I) (D.score W)
    (D.candidates_nonempty W I hI))

theorem chosen_spec (W I : Finset X) (hI : I ∈ D.family) :
    D.chosen W I hI ∈ D.candidates W I ∧
    ∀ H ∈ D.candidates W I, D.score W (D.chosen W I hI) ≤ D.score W H :=
  Classical.choose_spec (Finset.exists_min_image (D.candidates W I) (D.score W)
    (D.candidates_nonempty W I hI))

theorem chosen_mem (W I : Finset X) (hI : I ∈ D.family) :
    D.chosen W I hI ∈ D.family :=
  (Finset.mem_filter.mp (D.chosen_spec W I hI).1).1

def witness (W I : Finset X) (hI : I ∈ D.family) : Finset X :=
  heavy (D.weight (D.chosen W I hI)) W

def fragment (W I : Finset X) (hI : I ∈ D.family) : Finset X :=
  D.witness W I hI \ W

theorem fragment_subset (W I : Finset X) (hI : I ∈ D.family) :
    D.fragment W I hI ⊆ I :=
  (Finset.mem_filter.mp (D.chosen_spec W I hI).1).2

theorem fragment_disjoint (W I : Finset X) (hI : I ∈ D.family) :
    Disjoint W (D.fragment W I hI) := Finset.disjoint_sdiff

theorem witness_subset_union (W I : Finset X) (hI : I ∈ D.family) :
    D.witness W I hI ⊆ W ∪ D.fragment W I hI := by
  intro i hi
  by_cases hw : i ∈ W
  · exact Finset.mem_union_left _ hw
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hi, hw⟩)

theorem bad_relative {W H : Finset X} (hbad : D.Bad W) (hH : H ∈ D.family) :
    (∑ i ∈ W, D.weight H i) < (∑ i, D.weight H i) / 2 := by
  have ht : 1 ≤ ∑ i, D.weight H i := (D.normalized H hH).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H)
      (fun i _ _ => D.nonneg H hH i))
  linarith [hbad H hH]

theorem fragment_size (W I : Finset X) (hI : I ∈ D.family) (hbad : D.Bad W) :
    0 < (D.fragment W I hI).card ∧
    (D.witness W I hI).card ≤ 2 * (D.fragment W I hI).card := by
  have hs := heavy_sparse (D.weight (D.chosen W I hI))
    (D.nonneg _ (D.chosen_mem W I hI)) W
    (D.bad_relative hbad (D.chosen_mem W I hI))
  have hc := Finset.card_sdiff_add_card_inter (D.witness W I hI) W
  change 2 * (W ∩ D.witness W I hI).card < (D.witness W I hI).card at hs
  rw [Finset.inter_comm] at hs
  change (D.fragment W I hI).card + (D.witness W I hI ∩ W).card =
    (D.witness W I hI).card at hc
  omega

/-- The recovery property: two entries with the same augmentation, witness
size and fragment size recover the second fragment inside the first witness. -/
theorem fragment_recovery (W Y I J : Finset X) (hI : I ∈ D.family) (hJ : J ∈ D.family)
    (hz : W ∪ D.fragment W I hI = Y ∪ D.fragment Y J hJ)
    (hj : (D.witness W I hI).card = (D.witness Y J hJ).card)
    (ht : (D.fragment W I hI).card = (D.fragment Y J hJ).card) :
    D.witness W I hI \ Y = D.fragment Y J hJ := by
  let H := D.chosen W I hI
  have hH : H ∈ D.family := D.chosen_mem W I hI
  have hY : Y ⊆ W ∪ D.fragment W I hI := by
    rw [hz]
    exact Finset.subset_union_left
  have hcard : Y.card = W.card := by
    have he := congrArg Finset.card hz
    rw [Finset.card_union_of_disjoint (D.fragment_disjoint W I hI),
      Finset.card_union_of_disjoint (D.fragment_disjoint Y J hJ)] at he
    omega
  have heps := threshold_exchange (D.weight H) (D.nonneg H hH)
    W (D.fragment W I hI) Y (D.fragment_disjoint W I hI)
    Finset.sdiff_subset hY hcard
  have hheavy : heavy (D.weight H) Y ⊆ D.witness W I hI :=
    heavy_antitone_threshold heps
  have hcont : D.witness W I hI \ Y ⊆ D.fragment Y J hJ := by
    intro i hi
    have hiZ := D.witness_subset_union W I hI (Finset.mem_sdiff.mp hi).1
    rw [hz] at hiZ
    exact (Finset.mem_union.mp hiZ).resolve_left (Finset.mem_sdiff.mp hi).2
  have hsub : heavy (D.weight H) Y \ Y ⊆ J :=
    (show heavy (D.weight H) Y \ Y ⊆ D.witness W I hI \ Y from
      fun i hi => Finset.mem_sdiff.mpr
        ⟨hheavy (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hi).2⟩).trans
      (hcont.trans (D.fragment_subset Y J hJ))
  have hmin := (D.chosen_spec Y J hJ).2 H (Finset.mem_filter.mpr ⟨hH, hsub⟩)
  have hp := Prod.Lex.toLex_le_toLex'.mp hmin
  change (D.witness Y J hJ).card ≤ (heavy (D.weight H) Y).card ∧
    ((D.witness Y J hJ).card = (heavy (D.weight H) Y).card →
      (D.fragment Y J hJ).card ≤ (heavy (D.weight H) Y \ Y).card) at hp
  have heq : heavy (D.weight H) Y = D.witness W I hI :=
    Finset.eq_of_subset_of_card_le hheavy (hj.trans_le hp.1)
  have hj' : (D.witness Y J hJ).card = (heavy (D.weight H) Y).card := by
    rw [heq, hj]
  have hcount := hp.2 hj'
  rw [heq] at hcount
  exact Finset.eq_of_subset_of_card_le hcont hcount

/-- Distinct fragments in one encoding class inject into the powerset of a
single witness, whose size is at most twice the fragment size. -/
theorem fragment_in_container (W Y I J : Finset X) (hI : I ∈ D.family) (hJ : J ∈ D.family)
    (hz : W ∪ D.fragment W I hI = Y ∪ D.fragment Y J hJ)
    (hj : (D.witness W I hI).card = (D.witness Y J hJ).card)
    (ht : (D.fragment W I hI).card = (D.fragment Y J hJ).card) :
    D.fragment Y J hJ ⊆ D.witness W I hI := by
  rw [← D.fragment_recovery W Y I J hI hJ hz hj ht]
  exact Finset.sdiff_subset

end WeightSystem
end
end TalagrandSelector


/-! ## Bernoulli -/

open Finset
namespace TalagrandSelector
noncomputable section
variable {X : Type} [DecidableEq X]

def massOn (U : Finset X) (p : ℝ) (W : Finset X) : ℝ :=
  p ^ W.card * (1-p) ^ (U.card-W.card)

def average (U : Finset X) (p : ℝ) (f : Finset X → ℝ) : ℝ :=
  ∑ W ∈ U.powerset, massOn U p W * f W

theorem average_congr (U : Finset X) (p : ℝ) {f g : Finset X → ℝ}
    (h : ∀ W ⊆ U, f W = g W) : average U p f = average U p g := by
  apply Finset.sum_congr rfl
  intro W hW
  rw [h W (Finset.mem_powerset.mp hW)]

theorem average_add (U : Finset X) (p : ℝ) (f g : Finset X → ℝ) :
    average U p (fun W => f W + g W) = average U p f + average U p g := by
  simp [average, mul_add, Finset.sum_add_distrib]

theorem average_mul (U : Finset X) (p c : ℝ) (f : Finset X → ℝ) :
    average U p (fun W => c * f W) = c * average U p f := by
  simp [average, Finset.mul_sum, mul_left_comm]

theorem average_insert {a : X} {U : Finset X} (ha : a ∉ U)
    (p : ℝ) (f : Finset X → ℝ) :
    average (insert a U) p f =
      (1-p)*average U p f + p*average U p (fun W => f (insert a W)) := by
  have h0 : ∀ W ∈ U.powerset, massOn (insert a U) p W = (1-p)*massOn U p W := by
    intro W hW
    have hc := Finset.card_le_card (Finset.mem_powerset.mp hW)
    have hn : U.card + 1 - W.card = (U.card-W.card)+1 := by omega
    simp only [massOn, Finset.card_insert_of_notMem ha, hn, pow_succ]
    ring
  have h1 : ∀ W ∈ U.powerset,
      massOn (insert a U) p (insert a W) = p*massOn U p W := by
    intro W hW
    have haw : a ∉ W := fun hw => ha ((Finset.mem_powerset.mp hW) hw)
    simp only [massOn, Finset.card_insert_of_notMem ha,
      Finset.card_insert_of_notMem haw, Nat.add_sub_add_right, pow_succ]
    ring
  unfold average
  rw [Finset.sum_powerset_insert ha, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro W hW
    rw [h0 W hW]
    ring
  · apply Finset.sum_congr rfl
    intro W hW
    rw [h1 W hW]
    ring

@[simp] theorem average_empty (p : ℝ) (f : Finset X → ℝ) : average ∅ p f = f ∅ := by
  simp [average, massOn]

@[simp] theorem average_const (U : Finset X) (p c : ℝ) :
    average U p (fun _ => c) = c := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert a U ha ih => rw [average_insert ha, ih]; ring

theorem average_mono (U : Finset X) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : Finset X → ℝ} (h : ∀ W ⊆ U, f W ≤ g W) :
    average U p f ≤ average U p g := by
  apply Finset.sum_le_sum
  intro W hW
  apply mul_le_mul_of_nonneg_left (h W (Finset.mem_powerset.mp hW))
  unfold massOn
  positivity

/-- The intersection of independent p and q samples is a pq sample. -/
theorem average_inter (U : Finset X) (p q : ℝ) (f : Finset X → ℝ) :
    average U p (fun W => average U q (fun V => f (W ∩ V))) =
      average U (p*q) f := by
  induction U using Finset.induction_on generalizing f with
  | empty => simp
  | @insert a U ha ih =>
    have h0 : average U p (fun W => average (insert a U) q (fun V => f (W ∩ V))) =
        average U p (fun W => average U q (fun V => f (W ∩ V))) := by
      apply average_congr
      intro W hW
      have haw : a ∉ W := fun hw => ha (hW hw)
      rw [average_insert ha]
      have he : average U q (fun V => f (W ∩ insert a V)) =
          average U q (fun V => f (W ∩ V)) := by
        apply average_congr
        intro V _
        have hs : W ∩ insert a V = W ∩ V := by ext i; simp; aesop
        rw [hs]
      rw [he]
      ring
    have h1 : average U p (fun W =>
        average (insert a U) q (fun V => f (insert a W ∩ V))) =
        (1-q)*average U p (fun W => average U q (fun V => f (W ∩ V))) +
        q*average U p (fun W => average U q (fun V => f (insert a (W ∩ V)))) := by
      rw [← average_mul, ← average_mul, ← average_add]
      apply average_congr
      intro W _
      rw [average_insert ha]
      have he : average U q (fun V => f (insert a W ∩ V)) =
          average U q (fun V => f (W ∩ V)) := by
        apply average_congr
        intro V hV
        have hav : a ∉ V := fun hv => ha (hV hv)
        have hs : insert a W ∩ V = W ∩ V := by ext i; simp; aesop
        rw [hs]
      have he' : average U q (fun V => f (insert a W ∩ insert a V)) =
          average U q (fun V => f (insert a (W ∩ V))) := by
        apply average_congr
        intro V _
        have hs : insert a W ∩ insert a V = insert a (W ∩ V) := by
          ext i
          simp only [Finset.mem_inter, Finset.mem_insert]
          tauto
        rw [hs]
      rw [he, he']
    rw [average_insert ha, h0, h1, ih f, ih (fun S => f (insert a S)), average_insert ha]
    ring

theorem average_sum_weights (U : Finset X) (p : ℝ) (w : X → ℝ) :
    average U p (fun W => ∑ i ∈ W, w i) = p * ∑ i ∈ U, w i := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert a U ha ih =>
    rw [average_insert ha]
    have he : average U p (fun W => ∑ i ∈ insert a W, w i) =
        w a + average U p (fun W => ∑ i ∈ W, w i) := by
      calc
        average U p (fun W => ∑ i ∈ insert a W, w i) =
            average U p (fun W => w a + ∑ i ∈ W, w i) := by
          apply average_congr
          intro W hW
          exact Finset.sum_insert (fun hw => ha (hW hw))
        _ = _ := by rw [average_add, average_const]
    rw [he, ih, Finset.sum_insert ha]
    ring

theorem average_inter_sum (U W : Finset X) (hW : W ⊆ U) (p : ℝ) (w : X → ℝ) :
    average U p (fun V => ∑ i ∈ W ∩ V, w i) = p * ∑ i ∈ W, w i := by
  have he : ∀ V : Finset X, (∑ i ∈ W ∩ V, w i) = ∑ i ∈ V, if i ∈ W then w i else 0 := by
    intro V
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp [and_comm]
  simp_rw [he]
  rw [average_sum_weights, ← Finset.sum_filter]
  have hu : U.filter (fun i => i ∈ W) = W := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hW h, h⟩⟩
  rw [hu]

variable [Fintype X]
open TalagrandPositiveReduction

theorem average_univ (p : ℝ) (f : Finset X → ℝ) :
    average univ p f = expectation p f := by
  simp [average, massOn, expectation, subsetMass]

theorem subsetMass_sum (p : ℝ) : (∑ W : Finset X, subsetMass p W) = 1 := by
  have h := average_const (univ : Finset X) p 1
  rw [average_univ] at h
  simpa [average_univ, expectation] using h

theorem subsetMass_augment {p q : ℝ} (hq : 0 < q) (W T : Finset X)
    (hd : Disjoint W T) :
    subsetMass q W * p ^ T.card =
      subsetMass q (W ∪ T) * (p*(1-q)/q) ^ T.card := by
  have hc := Finset.card_le_univ (W ∪ T)
  rw [Finset.card_union_of_disjoint hd] at hc
  have he : Fintype.card X - W.card =
      (Fintype.card X - (W.card+T.card)) + T.card := by omega
  unfold subsetMass
  rw [Finset.card_union_of_disjoint hd, he, pow_add, pow_add, div_pow, mul_pow]
  field_simp [ne_of_gt hq]

end
end TalagrandSelector


/-! ## Counting -/

open Finset Classical TalagrandPositiveReduction
namespace TalagrandSelector
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

abbrev Record (X : Type) [Fintype X] := Fin (Fintype.card X + 1) × Finset X
abbrev Entry (X : Type) [Fintype X] := Finset X × Record X
abbrev Key (X : Type) [Fintype X] :=
  Fin (Fintype.card X + 1) × Fin (Fintype.card X + 1) × Finset X

def encode (e : Entry X) : Key X :=
  (e.2.1, ⟨e.2.2.card, Nat.lt_succ_of_le (Finset.card_le_univ _)⟩, e.1 ∪ e.2.2)

namespace WeightSystem
variable (D : WeightSystem X)

def records (W : Finset X) : Finset (Record X) :=
  D.family.attach.image (fun I =>
    (⟨(D.witness W I.val I.property).card,
      Nat.lt_succ_of_le (Finset.card_le_univ _)⟩, D.fragment W I.val I.property))

theorem mem_records {W : Finset X} {r : Record X} : r ∈ D.records W ↔
    ∃ I, ∃ hI : I ∈ D.family,
      r.1.val = (D.witness W I hI).card ∧ r.2 = D.fragment W I hI := by
  constructor
  · intro h
    obtain ⟨I, _, he⟩ := Finset.mem_image.mp h
    refine ⟨I.val, I.property, ?_, ?_⟩
    · exact (congrArg (fun x : Record X => x.1.val) he).symm
    · exact (congrArg Prod.snd he).symm
  · rintro ⟨I, hI, hj, ht⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨I, hI⟩, Finset.mem_attach _ _, ?_⟩
    apply Prod.ext
    · exact Fin.ext hj.symm
    · exact ht.symm

def entries : Finset (Entry X) :=
  univ.filter (fun e => D.Bad e.1 ∧ e.2 ∈ D.records e.1)

def fiber (k : Key X) : Finset (Entry X) := D.entries.filter (fun e => encode e = k)

theorem entry_spec {e : Entry X} (he : e ∈ D.entries) :
    D.Bad e.1 ∧ ∃ I, ∃ hI : I ∈ D.family,
      e.2.1.val = (D.witness e.1 I hI).card ∧ e.2.2 = D.fragment e.1 I hI :=
  ⟨(Finset.mem_filter.mp he).2.1, D.mem_records.mp (Finset.mem_filter.mp he).2.2⟩

theorem entry_disjoint {e : Entry X} (he : e ∈ D.entries) : Disjoint e.1 e.2.2 := by
  obtain ⟨_, I, hI, _, ht⟩ := D.entry_spec he
  rw [ht]
  exact D.fragment_disjoint _ _ _

theorem entry_shape {e : Entry X} (he : e ∈ D.entries) :
    0 < e.2.2.card ∧ e.2.1.val ≤ 2 * e.2.2.card := by
  obtain ⟨hb, I, hI, hj, ht⟩ := D.entry_spec he
  rw [hj, ht]
  exact D.fragment_size _ _ _ hb

theorem entry_recover {e : Entry X} (he : e ∈ D.entries) :
    (e.1 ∪ e.2.2) \ e.2.2 = e.1 := by
  have hd := Finset.disjoint_left.mp (D.entry_disjoint he)
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · intro h
    exact h.1.resolve_right h.2
  · intro h
    exact ⟨Or.inl h, hd h⟩

theorem fiber_card (k : Key X) :
    (D.fiber k).card ≤
      if 0 < k.2.1.val ∧ k.1.val ≤ 2*k.2.1.val then 2 ^ k.1.val else 0 := by
  classical
  by_cases hne : (D.fiber k).Nonempty
  · obtain ⟨e₀, he₀⟩ := hne
    have hbase := (Finset.mem_filter.mp he₀).1
    have hk₀ := (Finset.mem_filter.mp he₀).2
    obtain ⟨_, I, hI, hj₀, ht₀⟩ := D.entry_spec hbase
    have hkt : k.2.1.val = e₀.2.2.card :=
      (congrArg (fun a : Key X => a.2.1.val) hk₀).symm
    have hkj : k.1.val = e₀.2.1.val :=
      (congrArg (fun a : Key X => a.1.val) hk₀).symm
    have hshape : 0 < k.2.1.val ∧ k.1.val ≤ 2*k.2.1.val := by
      rw [hkt, hkj]
      exact D.entry_shape hbase
    rw [if_pos hshape]
    let R := D.witness e₀.1 I hI
    have hmap : ∀ e ∈ D.fiber k, e.2.2 ∈ R.powerset := by
      intro e he
      have he' := (Finset.mem_filter.mp he).1
      have hk := (Finset.mem_filter.mp he).2
      obtain ⟨_, J, hJ, hj, ht⟩ := D.entry_spec he'
      apply Finset.mem_powerset.mpr
      rw [ht]
      apply D.fragment_in_container e₀.1 e.1 I J hI hJ
      · have hz := congrArg (fun a : Key X => a.2.2) (hk₀.trans hk.symm)
        simpa only [encode, ht₀, ht] using hz
      · have hx := congrArg (fun a : Key X => a.1.val) (hk₀.trans hk.symm)
        simpa only [encode, hj₀, hj] using hx
      · have hx := congrArg (fun a : Key X => a.2.1.val) (hk₀.trans hk.symm)
        simpa only [encode, ht₀, ht] using hx
    have hinj : Set.InjOn (fun e : Entry X => e.2.2) (D.fiber k) := by
      intro e he e' he' ht
      change e.2.2 = e'.2.2 at ht
      have hke := (Finset.mem_filter.mp he).2
      have hke' := (Finset.mem_filter.mp he').2
      have hz := congrArg (fun a : Key X => a.2.2) (hke.trans hke'.symm)
      have hj := congrArg (fun a : Key X => a.1) (hke.trans hke'.symm)
      change e.1 ∪ e.2.2 = e'.1 ∪ e'.2.2 at hz
      have hw : e.1 = e'.1 := by
        rw [← D.entry_recover (Finset.mem_filter.mp he).1,
          ← D.entry_recover (Finset.mem_filter.mp he').1]
        change (e.1 ∪ e.2.2) \ e.2.2 = (e'.1 ∪ e'.2.2) \ e'.2.2
        rw [hz, ht]
      exact Prod.ext hw (Prod.ext hj ht)
    have hc := Finset.card_le_card_of_injOn (fun e : Entry X => e.2.2) hmap hinj
    simpa only [Finset.card_powerset, R, ← hj₀, ← hkj] using hc
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le _

def entryWeight (p q : ℝ) (e : Entry X) : ℝ := subsetMass q e.1 * p ^ e.2.2.card

theorem entryWeight_encode {p q : ℝ} (hq : 0 < q) {e : Entry X}
    (he : e ∈ D.entries) : entryWeight p q e =
      subsetMass q (encode e).2.2 * (p*(1-q)/q) ^ (encode e).2.1.val :=
  subsetMass_augment hq _ _ (D.entry_disjoint he)

theorem total_cost_encoding {p q : ℝ} (hq : 0 < q) :
    (∑ e ∈ D.entries, entryWeight p q e) =
      ∑ k : Key X, ((D.fiber k).card : ℝ) *
        (subsetMass q k.2.2 * (p*(1-q)/q) ^ k.2.1.val) := by
  rw [← Finset.sum_fiberwise D.entries encode (entryWeight p q)]
  apply Finset.sum_congr rfl
  intro k _
  calc
    (∑ e ∈ D.fiber k, entryWeight p q e) =
        ∑ _e ∈ D.fiber k, subsetMass q k.2.2 * (p*(1-q)/q)^k.2.1.val := by
      apply Finset.sum_congr rfl
      intro e he
      rw [D.entryWeight_encode hq (Finset.mem_filter.mp he).1,
        (Finset.mem_filter.mp he).2]
    _ = _ := by simp

end WeightSystem
end
end TalagrandSelector


/-! ## Numeric -/

open Finset
namespace TalagrandSelector

theorem index_sum_bound (n t : ℕ) :
    (∑ j : Fin (n+1), if (j : ℕ) ≤ 2*t then (2 : ℝ)^(j : ℕ) else 0) ≤ 16^t := by
  have hnat : ∀ t : ℕ, 2*t+1 ≤ 4^t := by
    intro t
    induction t with
    | zero => norm_num
    | succ t ih => rw [pow_succ]; nlinarith
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j ≤ 2*t then (2 : ℝ)^j else 0) (n+1),
    ← Finset.sum_filter]
  have hs : (range (n+1)).filter (fun j => j ≤ 2*t) ⊆ range (2*t+1) := by
    intro j hj
    exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hj).2; omega)
  calc
    (∑ j ∈ (range (n+1)).filter (fun j => j ≤ 2*t), (2 : ℝ)^j) ≤
        ∑ j ∈ range (2*t+1), (2 : ℝ)^j :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)
    _ ≤ ∑ _j ∈ range (2*t+1), (2 : ℝ)^(2*t) := by
      apply Finset.sum_le_sum
      intro j hj
      exact pow_le_pow_right₀ (by norm_num) (by have := Finset.mem_range.mp hj; omega)
    _ = (2*t+1 : ℝ) * (4 : ℝ)^t := by
      simp [pow_mul]
      norm_num
    _ ≤ (4 : ℝ)^t * (4 : ℝ)^t := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hnat t
    _ = 16^t := by rw [← mul_pow]; norm_num

theorem geometric_tail_bound (n : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1/128) :
    (∑ t : Fin (n+1), if 0 < (t : ℕ) then (16*r)^(t : ℕ) else 0) ≤ (1 : ℝ)/4 := by
  calc
    (∑ t : Fin (n+1), if 0 < (t : ℕ) then (16*r)^(t : ℕ) else 0) ≤
        ∑ t : Fin (n+1), if 0 < (t : ℕ) then (1/8 : ℝ)^(t : ℕ) else 0 := by
      apply Finset.sum_le_sum
      intro t _
      split_ifs
      · exact pow_le_pow_left₀ (by positivity) (by linarith) t.val
      · exact le_rfl
    _ ≤ 1/4 := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, lt_self_iff_false, if_false, Fin.val_succ,
        Nat.zero_lt_succ, if_true, zero_add]
      rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => (1/8 : ℝ)^(t+1)) n]
      simp_rw [pow_succ]
      rw [← Finset.sum_mul]
      have h := geom_sum_mul (1/8 : ℝ) n
      have hn : 0 ≤ (1/8 : ℝ)^n := by positivity
      nlinarith

end TalagrandSelector


/-! ## CoverCost -/

open Finset Classical TalagrandPositiveReduction
namespace TalagrandSelector
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]
namespace WeightSystem
variable (D : WeightSystem X)

/-- The encoding bound summed over all Bernoulli samples. -/
theorem total_cost_upper {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (hq1 : q ≤ 1)
    (hr : p*(1-q)/q ≤ 1/128) :
    (∑ e ∈ D.entries, entryWeight p q e) ≤ (1 : ℝ)/4 := by
  let r := p*(1-q)/q
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  rw [D.total_cost_encoding hq]
  have hbound :
      (∑ k : Key X, ((D.fiber k).card : ℝ) * (subsetMass q k.2.2 * r^k.2.1.val)) ≤
      ∑ k : Key X, if 0 < k.2.1.val ∧ k.1.val ≤ 2*k.2.1.val then
        (2 : ℝ)^k.1.val * (subsetMass q k.2.2 * r^k.2.1.val) else 0 := by
    apply Finset.sum_le_sum
    intro k _
    have hc : ((D.fiber k).card : ℝ) ≤
        if 0 < k.2.1.val ∧ k.1.val ≤ 2*k.2.1.val then (2 : ℝ)^k.1.val else 0 := by
      exact_mod_cast D.fiber_card k
    have hm := mul_le_mul_of_nonneg_right hc
      (mul_nonneg (subsetMass_nonneg hq.le hq1 k.2.2) (pow_nonneg hr0 k.2.1.val))
    simpa only [ite_mul, zero_mul] using hm
  have hinner (j t : Fin (Fintype.card X+1)) :
      (∑ Z : Finset X, if 0 < t.val ∧ j.val ≤ 2*t.val then
        (2 : ℝ)^j.val * (subsetMass q Z * r^t.val) else 0) =
      if 0 < t.val ∧ j.val ≤ 2*t.val then (2 : ℝ)^j.val * r^t.val else 0 := by
    by_cases h : 0 < t.val ∧ j.val ≤ 2*t.val
    · simp only [if_pos h]
      have halg : ∀ Z : Finset X,
          (2 : ℝ)^j.val * (subsetMass q Z * r^t.val) =
            subsetMass q Z * ((2 : ℝ)^j.val*r^t.val) := by intro Z; ring
      simp_rw [halg]
      rw [← Finset.sum_mul, subsetMass_sum, one_mul]
    · simp only [if_neg h, Finset.sum_const_zero]
  calc
    (∑ k : Key X, ((D.fiber k).card : ℝ) * (subsetMass q k.2.2 * r^k.2.1.val)) ≤
        ∑ k : Key X, if 0 < k.2.1.val ∧ k.1.val ≤ 2*k.2.1.val then
          (2 : ℝ)^k.1.val * (subsetMass q k.2.2 * r^k.2.1.val) else 0 := hbound
    _ = ∑ j : Fin (Fintype.card X+1), ∑ t : Fin (Fintype.card X+1),
        if 0 < t.val ∧ j.val ≤ 2*t.val then (2 : ℝ)^j.val * r^t.val else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro j _
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro t _
      exact hinner j t
    _ = ∑ t : Fin (Fintype.card X+1), if 0 < t.val then
        (∑ j : Fin (Fintype.card X+1), if j.val ≤ 2*t.val then (2 : ℝ)^j.val else 0)
          * r^t.val else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : 0 < t.val
      · rw [if_pos ht, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j.val ≤ 2*t.val <;> simp [ht, hj]
      · simp [ht]
    _ ≤ ∑ t : Fin (Fintype.card X+1), if 0 < t.val then (16*r)^t.val else 0 := by
      apply Finset.sum_le_sum
      intro t _
      split_ifs
      · rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (index_sum_bound _ _) (pow_nonneg hr0 _)
      · exact le_rfl
    _ ≤ 1/4 := geometric_tail_bound _ hr0 hr

theorem records_cover (W : Finset X) :
    ∀ I ∈ D.family, ∃ T ∈ (D.records W).image Prod.snd, T ⊆ I := by
  intro I hI
  refine ⟨D.fragment W I hI, ?_, D.fragment_subset W I hI⟩
  apply Finset.mem_image.mpr
  let r : Record X := (⟨(D.witness W I hI).card,
    Nat.lt_succ_of_le (Finset.card_le_univ _)⟩, D.fragment W I hI)
  exact ⟨r, D.mem_records.mpr ⟨I, hI, rfl, rfl⟩, rfl⟩

theorem record_cost_gt_half {p : ℝ} (hp : 0 ≤ p)
    (hnot : ¬ IsPSmall p D.family) (W : Finset X) :
    (1 : ℝ)/2 < ∑ r ∈ D.records W, p^r.2.card := by
  by_contra h
  apply hnot
  refine ⟨(D.records W).image Prod.snd, D.records_cover W, ?_⟩
  have hle : coverCost p ((D.records W).image Prod.snd) ≤
      ∑ r ∈ D.records W, p^r.2.card :=
    Finset.sum_image_le_of_nonneg (fun _ _ => pow_nonneg hp _)
  exact hle.trans (le_of_not_gt h)

theorem total_cost_samples (p q : ℝ) :
    (∑ e ∈ D.entries, entryWeight p q e) =
      ∑ W : Finset X, if D.Bad W then
        subsetMass q W * (∑ r ∈ D.records W, p^r.2.card) else 0 := by
  unfold entries
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro W _
  by_cases hb : D.Bad W
  · simp only [hb, true_and, if_true, entryWeight]
    have hf : (univ : Finset (Record X)).filter (fun r => r ∈ D.records W) =
        D.records W := by ext r; simp
    rw [← Finset.sum_filter, hf, ← Finset.mul_sum]
  · simp [hb]

def badProbability (q : ℝ) : ℝ :=
  ∑ W : Finset X, if D.Bad W then subsetMass q W else 0

theorem badProbability_le_half {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (hq1 : q ≤ 1)
    (hr : p*(1-q)/q ≤ 1/128) (hnot : ¬ IsPSmall p D.family) :
    D.badProbability q ≤ (1 : ℝ)/2 := by
  have hlow : D.badProbability q / 2 ≤ ∑ e ∈ D.entries, entryWeight p q e := by
    rw [D.total_cost_samples]
    unfold badProbability
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro W _
    by_cases hb : D.Bad W
    · simp only [if_pos hb]
      have hmul := mul_le_mul_of_nonneg_left (D.record_cost_gt_half hp hnot W).le
        (subsetMass_nonneg hq.le hq1 W)
      nlinarith
    · simp [hb]
  have hu := D.total_cost_upper hp hq hq1 hr
  linarith

end WeightSystem
end
end TalagrandSelector


/-! ## Main -/

open Finset Classical TalagrandPositiveReduction
namespace TalagrandSelector
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]
namespace WeightSystem
variable (D : WeightSystem X)

def value (hF : D.family.Nonempty) (W : Finset X) : ℝ :=
  localValue D.family hF D.weight W

theorem sum_le_value (hF : D.family.Nonempty) {H : Finset X} (hH : H ∈ D.family)
    (W : Finset X) : (∑ i ∈ W, D.weight H i) ≤ D.value hF W :=
  Finset.le_sup' (f := fun H => ∑ i ∈ W, D.weight H i) hH

theorem value_nonneg (hF : D.family.Nonempty) (W : Finset X) : 0 ≤ D.value hF W := by
  have hF' := hF
  obtain ⟨H, hH⟩ := hF'
  exact (Finset.sum_nonneg (fun i _ => D.nonneg H hH i)).trans (D.sum_le_value hF hH W)

theorem value_ge_half_of_not_bad (hF : D.family.Nonempty) (W : Finset X)
    (hbad : ¬ D.Bad W) : (1 : ℝ)/2 ≤ D.value hF W := by
  apply le_of_not_gt
  intro h
  apply hbad
  intro H hH
  exact (D.sum_le_value hF hH W).trans_lt h

theorem expectation_ge_quarter (hF : D.family.Nonempty)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (hq1 : q ≤ 1)
    (hr : p*(1-q)/q ≤ 1/128) (hnot : ¬ IsPSmall p D.family) :
    (1 : ℝ)/4 ≤ expectation q (D.value hF) := by
  have hbad := D.badProbability_le_half hp hq hq1 hr hnot
  have hle : expectation q (fun W => if D.Bad W then 0 else (1 : ℝ)/2) ≤
      expectation q (D.value hF) := by
    apply expectation_mono hq.le hq1
    intro W
    by_cases hb : D.Bad W
    · simpa [hb] using D.value_nonneg hF W
    · simpa [hb] using D.value_ge_half_of_not_bad hF W hb
  have he : expectation q (fun W => if D.Bad W then 0 else (1 : ℝ)/2) =
      (1-D.badProbability q)/2 := by
    unfold expectation badProbability
    calc
      (∑ W : Finset X, subsetMass q W * (if D.Bad W then 0 else (1 : ℝ)/2)) =
          (∑ W : Finset X, subsetMass q W)/2 -
          (∑ W : Finset X, if D.Bad W then subsetMass q W else 0)/2 := by
        rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro W _
        by_cases hb : D.Bad W <;> simp [hb] <;> ring
      _ = _ := by rw [subsetMass_sum]; ring
  rw [he] at hle
  linarith

/-- Jensen's inequality for thinning, proved here by finite sums and an
actual maximizing member of the finite family. -/
theorem thinning (hF : D.family.Nonempty) {q r : ℝ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    r * expectation q (D.value hF) ≤ expectation (q*r) (D.value hF) := by
  have hpoint : ∀ W : Finset X,
      r * D.value hF W ≤ average univ r (fun V => D.value hF (W ∩ V)) := by
    intro W
    obtain ⟨H, hH, hmax⟩ :=
      Finset.exists_mem_eq_sup' hF (fun H => ∑ i ∈ W, D.weight H i)
    change D.value hF W = ∑ i ∈ W, D.weight H i at hmax
    rw [hmax]
    calc
      r * (∑ i ∈ W, D.weight H i) =
          average univ r (fun V => ∑ i ∈ W ∩ V, D.weight H i) :=
        (average_inter_sum univ W (Finset.subset_univ _) r (D.weight H)).symm
      _ ≤ average univ r (fun V => D.value hF (W ∩ V)) :=
        average_mono univ hr hr1 (fun V _ => D.sum_le_value hF hH (W ∩ V))
  have h := average_mono (univ : Finset X) hq hq1 (fun W _ => hpoint W)
  rw [average_mul, average_inter, average_univ, average_univ] at h
  exact h

theorem density_lower_bound (hF : D.family.Nonempty) {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) : p ≤ expectation p (D.value hF) := by
  have hF' := hF
  obtain ⟨H, hH⟩ := hF'
  have ht : 1 ≤ ∑ i, D.weight H i := (D.normalized H hH).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => D.nonneg H hH i))
  have h := average_mono (univ : Finset X) hp hp1
    (fun W _ => D.sum_le_value hF hH W)
  rw [average_sum_weights, average_univ] at h
  have hm : p ≤ p * ∑ i, D.weight H i := by
    simpa using mul_le_mul_of_nonneg_left ht hp
  exact hm.trans h

/-- The normalized selector theorem with explicit universal constant 512. -/
theorem normalized_bound (hF : D.family.Nonempty) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hnot : ¬ IsPSmall p D.family) :
    1 ≤ 512 * expectation p (D.value hF) := by
  by_cases hlarge : (1 : ℝ)/128 ≤ p
  · have h := D.density_lower_bound hF hp.le hp1.le
    linarith
  · have hsmall : p < 1/128 := lt_of_not_ge hlarge
    have hq : 0 < 128*p := by positivity
    have hq1 : 128*p ≤ 1 := by linarith
    have hr : p*(1-128*p)/(128*p) ≤ 1/128 := by
      apply (div_le_iff₀ hq).mpr
      nlinarith [sq_nonneg p]
    have he := D.expectation_ge_quarter hF hp.le hq hq1 hr hnot
    have ht := D.thinning hF hq.le hq1
      (by norm_num : (0 : ℝ) ≤ 1/128) (by norm_num : (1/128 : ℝ) ≤ 1)
    have hpq : (128*p)*(1/128) = p := by ring
    rw [hpq] at ht
    linarith

end WeightSystem

/-- This DISCHARGES the hypothesis left open in the previous reduction file. -/
theorem normalized_selector_bound : NormalizedSelectorBound 512 := by
  intro X _ _ p F hF w hp hp1 hn hs hnorm hnot
  let D : WeightSystem X := ⟨F, w, hn, hs, hnorm⟩
  exact D.normalized_bound hF hp hp1 hnot

/-- Corrected Park--Pham Conjecture 5.7, for arbitrary collections of weights,
with the explicit universal constant L = 2048. No core theorem is assumed. -/
theorem conjecture_5_7 : PositiveConjecture57 2048 := by
  convert positive_conjecture_5_7_of_normalized_bound
    (C := 512) (by norm_num) normalized_selector_bound
    using 1 <;> norm_num

/-- Expanded public statement. BoundedWeights encodes finiteness of the
selector supremum, and hM is the missing strict positivity hypothesis. -/
theorem conjecture_5_7_positive (p : ℝ) (Lambda : Set (X → ℝ))
    (hp : 0 < p) (hp1 : p < 1) (hLambda : Lambda.Nonempty)
    (hnonneg : NonnegativeWeights Lambda) (hfinite : BoundedWeights Lambda)
    (hM : 0 < expectation p (selectorValue Lambda)) :
    IsPSmall p (tailFamily 2048 p Lambda) :=
  conjecture_5_7 X p Lambda hp hp1 hLambda hnonneg hfinite hM

theorem exists_universal_constant : ∃ L : ℝ, 0 < L ∧ PositiveConjecture57 L :=
  ⟨2048, by norm_num, conjecture_5_7⟩

end
end TalagrandSelector


/-! ## Extended -/

/-! The literal positive-finite-expectation interface. No boundedness or
nonemptiness hypothesis on the collection is added to the public theorem:
both are derived from the two assumptions on the extended expectation. -/

open Finset Classical TalagrandPositiveReduction
open scoped ENNReal
namespace TalagrandSelector
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

/-- The supremum can genuinely equal infinity for an unbounded collection. -/
def extendedValue (Lambda : Set (X → ℝ)) (W : Finset X) : ℝ≥0∞ :=
  ⨆ w : Lambda, ENNReal.ofReal (∑ i ∈ W, w.val i)

/-- Extended nonnegative expectation on the finite Bernoulli sample space. -/
def extendedExpectation (p : ℝ) (Lambda : Set (X → ℝ)) : ℝ≥0∞ :=
  ∑ W : Finset X, ENNReal.ofReal (subsetMass p W) * extendedValue Lambda W

def extendedTail (L p : ℝ) (Lambda : Set (X → ℝ)) : Finset (Finset X) :=
  univ.filter (fun W => ENNReal.ofReal L * extendedExpectation p Lambda ≤
    extendedValue Lambda W)

theorem nonempty_of_positive_extended {p : ℝ} {Lambda : Set (X → ℝ)}
    (hE : 0 < extendedExpectation p Lambda) : Lambda.Nonempty := by
  by_contra h
  have he : Lambda = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  simp [extendedExpectation, extendedValue, he] at hE

theorem bounded_of_finite_expectation {p : ℝ} {Lambda : Set (X → ℝ)}
    (hp : 0 < p) (hn : NonnegativeWeights Lambda)
    (hE : extendedExpectation p Lambda < ⊤) : BoundedWeights Lambda := by
  have hmass : 0 < subsetMass p (univ : Finset X) := by
    simp only [subsetMass, Finset.card_univ, Nat.sub_self, pow_zero, mul_one]
    positivity
  have hmass' : ENNReal.ofReal (subsetMass p (univ : Finset X)) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hmass)
  have hterm : ENNReal.ofReal (subsetMass p (univ : Finset X)) *
      extendedValue Lambda univ ≤ extendedExpectation p Lambda := by
    unfold extendedExpectation
    exact Finset.single_le_sum
      (f := fun W => ENNReal.ofReal (subsetMass p W) * extendedValue Lambda W)
      (fun _ _ => bot_le) (Finset.mem_univ _)
  have hfinite : extendedValue Lambda univ ≠ ⊤ := by
    intro he
    rw [he, ENNReal.mul_top hmass'] at hterm
    exact (not_le_of_gt hE) hterm
  refine ⟨(extendedValue Lambda univ).toReal, ?_⟩
  rintro y ⟨w, hw, rfl⟩
  have hval : ENNReal.ofReal (∑ i : X, w i) ≤ extendedValue Lambda univ :=
    le_iSup (fun v : Lambda => ENNReal.ofReal (∑ i : X, v.val i)) ⟨w, hw⟩
  have h := ENNReal.toReal_mono hfinite hval
  simpa only [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun i _ => hn w hw i))] using h

theorem extendedValue_eq_ofReal {Lambda : Set (X → ℝ)}
    (hLambda : Lambda.Nonempty) (hn : NonnegativeWeights Lambda)
    (hb : BoundedWeights Lambda) (W : Finset X) :
    extendedValue Lambda W = ENNReal.ofReal (selectorValue Lambda W) := by
  apply le_antisymm
  · apply iSup_le
    intro w
    exact ENNReal.ofReal_le_ofReal (weight_sum_le_value hn hb w.property W)
  · by_cases htop : extendedValue Lambda W = ⊤
    · rw [htop]; exact le_top
    · have hz : selectorValue Lambda W ≤ (extendedValue Lambda W).toReal := by
        apply csSup_le (weightValues_nonempty hLambda W)
        rintro y ⟨w, hw, rfl⟩
        have hval : ENNReal.ofReal (∑ i ∈ W, w i) ≤ extendedValue Lambda W :=
          le_iSup (fun v : Lambda => ENNReal.ofReal (∑ i ∈ W, v.val i)) ⟨w, hw⟩
        have h := ENNReal.toReal_mono htop hval
        simpa only [ENNReal.toReal_ofReal
          (Finset.sum_nonneg (fun i _ => hn w hw i))] using h
      have h := ENNReal.ofReal_le_ofReal hz
      rw [ENNReal.ofReal_toReal htop] at h
      exact h

theorem extendedExpectation_eq_ofReal {p : ℝ} {Lambda : Set (X → ℝ)}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hLambda : Lambda.Nonempty)
    (hn : NonnegativeWeights Lambda) (hb : BoundedWeights Lambda) :
    extendedExpectation p Lambda = ENNReal.ofReal (expectation p (selectorValue Lambda)) := by
  unfold extendedExpectation expectation
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun W _ => mul_nonneg (subsetMass_nonneg hp hp1 W)
      (selectorValue_nonneg hLambda hn hb W))]
  apply Finset.sum_congr rfl
  intro W _
  rw [extendedValue_eq_ofReal hLambda hn hb W,
    ENNReal.ofReal_mul (subsetMass_nonneg hp hp1 W)]

/-- THE FINAL THEOREM: corrected Conjecture 5.7 with precisely positive finite
expectation, arbitrary nonnegative weight collection, and L=2048.
There is no NormalizedSelectorBound argument, no boundedness assumption,
and no assumption that the supremum is attained. -/
theorem conjecture_5_7_finite_expectation (p : ℝ) (Lambda : Set (X → ℝ))
    (hp : 0 < p) (hp1 : p < 1) (hn : NonnegativeWeights Lambda)
    (hEpos : 0 < extendedExpectation p Lambda)
    (hEfinite : extendedExpectation p Lambda < ⊤) :
    IsPSmall p (extendedTail 2048 p Lambda) := by
  have hLambda := nonempty_of_positive_extended hEpos
  have hb := bounded_of_finite_expectation hp hn hEfinite
  have hEE := extendedExpectation_eq_ofReal hp.le hp1.le hLambda hn hb
  have hM : 0 < expectation p (selectorValue Lambda) :=
    ENNReal.ofReal_pos.mp (hEE ▸ hEpos)
  apply (conjecture_5_7_positive p Lambda hp hp1 hLambda hn hb hM).mono
  intro W hW
  have h := (Finset.mem_filter.mp hW).2
  change ENNReal.ofReal 2048 * extendedExpectation p Lambda ≤ extendedValue Lambda W at h
  rw [hEE, extendedValue_eq_ofReal hLambda hn hb W,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2048)] at h
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (ENNReal.ofReal_le_ofReal_iff (selectorValue_nonneg hLambda hn hb W)).mp h⟩

end
end TalagrandSelector


set_option pp.fullNames true
#print axioms TalagrandSelector.normalized_selector_bound
#print axioms TalagrandSelector.conjecture_5_7_finite_expectation
