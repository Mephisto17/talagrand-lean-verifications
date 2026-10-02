import TalagrandSelector.Counting
import TalagrandSelector.Numeric

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
