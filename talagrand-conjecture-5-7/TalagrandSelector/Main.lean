import TalagrandSelector.CoverCost

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

#print axioms TalagrandSelector.normalized_selector_bound
#print axioms TalagrandSelector.conjecture_5_7_positive
#print axioms TalagrandSelector.exists_universal_constant
