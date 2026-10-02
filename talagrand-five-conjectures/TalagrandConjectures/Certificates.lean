import TalagrandConjectures.Logarithmic

open Finset Classical
namespace TalagrandConjectures
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

theorem weaklySmall_empty (r : ℝ) : WeaklySmall r (∅ : Set (Cube X)) := by
  refine ⟨fun _ => 0, by simp, by norm_num, by simp⟩
theorem WeaklySmall.mono {r : ℝ} {A B : Set (Cube X)}
    (h : WeaklySmall r A) (hBA : B ⊆ A) : WeaklySmall r B := by
  obtain ⟨c, hc, hcost, hcover⟩ := h
  exact ⟨c, hc, hcost, fun J hJ => hcover J (hBA hJ)⟩

/-- A fractional certificate with cost at most M can be padded at the empty
set and normalized to give the probability measure in Conjecture 7.12. -/
theorem certificate_to_law {r M : ℝ} (hr : 0 < r) (hM : 0 < M)
    (c : Cube X → ℝ) (hc : ∀ I, 0 ≤ c I)
    (hcost : (∑ I, c I*monoWeight r I) ≤ M) :
    ∃ η : Law X, ∀ J : Cube X,
      (∑ I, if I ≤ J then c I else 0) ≤
        M * ∑ I, if I ≤ J then η.weight I / monoWeight r I else 0 := by
  let C := ∑ I, c I*monoWeight r I
  let w : Cube X → ℝ := fun I =>
    (c I*monoWeight r I + if I = ⊥ then M-C else 0)/M
  have hw : ∀ I, 0 ≤ w I := by
    intro I
    apply div_nonneg _ hM.le
    apply add_nonneg (mul_nonneg (hc I) (monoWeight_pos hr I).le)
    split_ifs <;> linarith
  have hs : ∑ I, w I = 1 := by
    simp only [w, ← Finset.sum_div, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    change (C + (M-C))/M = 1
    field_simp
    <;> ring
  refine ⟨⟨w, hw, hs⟩, ?_⟩
  intro J
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro I _
  by_cases hi : I ≤ J
  · simp only [if_pos hi]
    change c I ≤ M * (w I / monoWeight r I)
    have he : M * (w I / monoWeight r I) =
        c I + (if I = ⊥ then M-C else 0)/monoWeight r I := by
      dsimp [w]
      field_simp [ne_of_gt hM, ne_of_gt (monoWeight_pos hr I)]
      <;> ring
    rw [he]
    have h0 : 0 ≤ (if I = ⊥ then M-C else 0) := by split_ifs <;> linarith
    exact le_add_of_nonneg_right (div_nonneg h0 (monoWeight_pos hr I).le)
  · simp [hi]

/-- Bridge to the probability-measure formulation in Talagrand's Definition 6.1. -/
theorem WeaklySmall.probability_form {r : ℝ} (hr : 0 < r) {A : Set (Cube X)}
    (h : WeaklySmall r A) :
    ∃ η : Law X, ∀ J ∈ A, 1 ≤ (1/2:ℝ) *
      ∑ I, if I ≤ J then η.weight I / monoWeight r I else 0 := by
  obtain ⟨c, hc, hcost, hcover⟩ := h
  obtain ⟨η, hη⟩ := certificate_to_law hr (by norm_num : (0:ℝ)<1/2) c hc hcost
  exact ⟨η, fun J hJ => (hcover J hJ).trans (hη J)⟩

def polyCoeff (p a : ℝ) (A : Set (Cube X)) (I : Cube X) : ℝ :=
  (if I = ⊥ then (measure p A)^2 else 0) + highCoeff p a Aᶜ I

theorem polyCoeff_nonneg {p a : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (ha1 : a < 1) (A : Set (Cube X)) (I : Cube X) :
    0 ≤ polyCoeff p a A I := by
  apply add_nonneg _ (highCoeff_nonneg hp hp1 ha ha1 Aᶜ I)
  split_ifs <;> positivity

theorem poly_eval (p a : ℝ) (A : Set (Cube X)) (J : Cube X) :
    (∑ I, if I ≤ J then polyCoeff p a A I else 0) =
      (measure p A)^2 + highEnergy p a Aᶜ J := by
  have h (I : Cube X) : (if I ≤ J then polyCoeff p a A I else 0) =
      (if I = ⊥ then (measure p A)^2 else 0) +
        (if I ≤ J then highCoeff p a Aᶜ I else 0) := by
    by_cases hb : I = ⊥
    · subst I; simp [polyCoeff]
    · simp [polyCoeff, hb]
  simp_rw [h, Finset.sum_add_distrib]
  simp [highEnergy]

theorem poly_cost {p a r : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (ha1 : a < 1) (hr : 0 ≤ r) (hbr : beta p a*r ≤ 1)
    (A : Set (Cube X)) :
    (∑ I, polyCoeff p a A I * monoWeight r I) ≤ measure p A := by
  have he : (∑ I, polyCoeff p a A I * monoWeight r I) =
      (measure p A)^2 + ∑ I, highCoeff p a Aᶜ I * monoWeight r I := by
    simp [polyCoeff, add_mul, Finset.sum_add_distrib, ite_mul, monoWeight_bot]
  rw [he]
  have hc := high_cost hp hp1 ha ha1 hr hbr Aᶜ
  have hvar : 0 ≤ measure p Aᶜ - (measure p Aᶜ)^2 := by
    have h0 := measure_nonneg hp.le hp1.le Aᶜ
    have h1 := measure_le_one hp.le hp1.le Aᶜ
    nlinarith
  have hm := mul_le_of_le_one_left hvar hbr
  rw [measure_compl] at hc hm
  nlinarith

/-- Conjecture 7.12, including the constant monomial I=empty in the displayed
formula (7.13), with alpha=1/2. -/
theorem conjecture_7_12 {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {A : Set (Cube X)} (hA : Up A) :
    ∃ η : Law X, ∀ J : Cube X, theta (1/2) A J ≤
      measure p A * ∑ I, if I ≤ J then η.weight I / monoWeight ((1/2)*p) I else 0 := by
  by_cases hne : A.Nonempty
  · have hm := measure_pos hp hp1 hne
    obtain ⟨η, hη⟩ := certificate_to_law (show 0 < (1/2)*p by positivity) hm
      (polyCoeff p (1/2) A)
      (polyCoeff_nonneg hp hp1 (by norm_num) (by norm_num) A)
      (poly_cost hp hp1 (by norm_num) (by norm_num) (by positivity)
        (show beta p (1/2)*((1/2)*p) ≤ 1 by nlinarith [beta_half hp hp1]) A)
    refine ⟨η, fun J => ?_⟩
    have h := hη J
    rw [poly_eval] at h
    exact (theta_up_bound hp hp1 (by norm_num) (by norm_num) hA J).trans h
  · have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    let η : Law X := ⟨fun I => if I = ⊥ then 1 else 0,
      fun I => by split_ifs <;> norm_num, by simp⟩
    refine ⟨η, ?_⟩
    intro J
    simp [he, theta, measure, ind, avg]

/-- Conjecture 7.3, in Talagrand's original cost-at-most-one-half definition,
with alpha=1/2. -/
theorem conjecture_7_3 {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {A : Set (Cube X)} (hA : Up A) :
    WeaklySmall ((1/2)*p) {J | measure p A < theta (1/2) A J} := by
  by_cases hne : A.Nonempty
  · by_cases hfull : A = Set.univ
    · have he : {J : Cube X | measure p A < theta (1/2) A J} = ∅ := by
        ext J; simp [hfull, measure, theta, ind, avg, mass_sum]
      rw [he]; exact weaklySmall_empty _
    · have hu := measure_pos hp hp1 hne
      have hcompl : Aᶜ.Nonempty := Set.nonempty_compl.mpr hfull
      have hm := measure_pos hp hp1 hcompl
      rw [measure_compl] at hm
      have hv : 0 < measure p A - (measure p A)^2 := by nlinarith
      let v := measure p A - (measure p A)^2
      refine ⟨fun I => highCoeff p (1/2) Aᶜ I / v, ?_, ?_, ?_⟩
      · intro I
        exact div_nonneg (highCoeff_nonneg hp hp1 (by norm_num) (by norm_num) Aᶜ I) hv.le
      · have h := high_cost hp hp1 (by norm_num : (0:ℝ)<1/2)
          (by norm_num : (1/2:ℝ)<1) (by positivity : 0 ≤ (1/2)*p)
          (show beta p (1/2)*((1/2)*p) ≤ 1 by nlinarith [beta_half hp hp1]) Aᶜ
        rw [measure_compl] at h
        have hb : beta p (1/2)*((1/2)*p) ≤ 1/2 := by nlinarith [beta_half hp hp1]
        have halg : ∀ I : Cube X, highCoeff p (1/2) Aᶜ I / v * monoWeight ((1/2)*p) I =
            (highCoeff p (1/2) Aᶜ I * monoWeight ((1/2)*p) I)/v := by intro I; ring
        simp_rw [halg]
        rw [← Finset.sum_div]
        apply (div_le_iff₀ hv).mpr
        have hmul := mul_le_mul_of_nonneg_right hb hv.le
        dsimp [v] at *
        nlinarith
      · intro J hJ
        change measure p A < theta (1/2) A J at hJ
        have hb := theta_up_bound hp hp1 (by norm_num : (0:ℝ)<1/2)
          (by norm_num : (1/2:ℝ)<1) hA J
        have hcover : v ≤ highEnergy p (1/2) Aᶜ J := by
          dsimp [v]
          linarith only [hJ, hb]
        have he : (∑ I : Cube X, if I ≤ J then highCoeff p (1/2) Aᶜ I / v else 0) =
            highEnergy p (1/2) Aᶜ J / v := by
          simp [highEnergy, Finset.sum_div, ite_div]
        rw [he]
        exact (one_le_div hv).mpr hcover
  · have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hempty : {J : Cube X | measure p A < theta (1/2) A J} = ∅ := by
      ext J; simp [he, measure, theta, ind, avg]
    rw [hempty]; exact weaklySmall_empty _

end
end TalagrandConjectures
