import TalagrandSelector.Main

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

/-- THE FINAL THEOREM: corrected Theorem 1.2 with precisely positive finite
expectation, arbitrary nonnegative weight collection, and L=2048.
There is no NormalizedSelectorBound argument, no boundedness assumption,
and no assumption that the supremum is attained. -/
theorem theorem_1_2_finite_expectation (p : ℝ) (Lambda : Set (X → ℝ))
    (hp : 0 < p) (hp1 : p < 1) (hn : NonnegativeWeights Lambda)
    (hEpos : 0 < extendedExpectation p Lambda)
    (hEfinite : extendedExpectation p Lambda < ⊤) :
    IsPSmall p (extendedTail 2048 p Lambda) := by
  have hLambda := nonempty_of_positive_extended hEpos
  have hb := bounded_of_finite_expectation hp hn hEfinite
  have hEE := extendedExpectation_eq_ofReal hp.le hp1.le hLambda hn hb
  have hM : 0 < expectation p (selectorValue Lambda) :=
    ENNReal.ofReal_pos.mp (hEE ▸ hEpos)
  apply (theorem_1_2_positive p Lambda hp hp1 hLambda hn hb hM).mono
  intro W hW
  have h := (Finset.mem_filter.mp hW).2
  change ENNReal.ofReal 2048 * extendedExpectation p Lambda ≤ extendedValue Lambda W at h
  rw [hEE, extendedValue_eq_ofReal hLambda hn hb W,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2048)] at h
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (ENNReal.ofReal_le_ofReal_iff (selectorValue_nonneg hLambda hn hb W)).mp h⟩

end
end TalagrandSelector

#print axioms TalagrandSelector.theorem_1_2_finite_expectation
