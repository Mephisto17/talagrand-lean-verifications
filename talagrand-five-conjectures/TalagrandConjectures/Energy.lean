import TalagrandConjectures.Extrapolation

open Finset Classical
namespace TalagrandConjectures
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

theorem beta_pos {p a : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (ha1 : a < 1) : 0 < beta p a := by unfold beta; positivity

def highCoeff (p a : ℝ) (A : Set (Cube X)) (I : Cube X) : ℝ :=
  if I = ⊥ then 0 else (coeff p (ind A) I)^2 * monoWeight (beta p a) I
def highEnergy (p a : ℝ) (A : Set (Cube X)) (J : Cube X) : ℝ :=
  ∑ I, if I ≤ J then highCoeff p a A I else 0

theorem highCoeff_nonneg {p a : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (ha1 : a < 1) (A : Set (Cube X)) (I : Cube X) :
    0 ≤ highCoeff p a A I := by
  unfold highCoeff; split_ifs
  · exact le_rfl
  · exact mul_nonneg (sq_nonneg _) (monoWeight_nonneg (beta_pos hp hp1 ha ha1).le I)
theorem energy_nonneg {p a : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (ha1 : a < 1) (A : Set (Cube X)) (J : Cube X) :
    0 ≤ energy p a A J := by
  apply Finset.sum_nonneg
  intro I _
  split_ifs
  · exact mul_nonneg (sq_nonneg _) (monoWeight_nonneg (beta_pos hp hp1 ha ha1).le I)
  · exact le_rfl

theorem energy_split (p a : ℝ) (A : Set (Cube X)) (J : Cube X) :
    energy p a A J = (measure p A)^2 + highEnergy p a A J := by
  have hpoint (I : Cube X) :
      (if I ≤ J then (coeff p (ind A) I)^2 * monoWeight (beta p a) I else 0) =
      (if I = ⊥ then (measure p A)^2 else 0) +
        (if I ≤ J then highCoeff p a A I else 0) := by
    by_cases h : I = ⊥
    · subst I; simp [highCoeff, coeff_bot, monoWeight_bot, measure]
    · simp [highCoeff, h]
  simp_rw [energy, hpoint, Finset.sum_add_distrib]
  simp [highEnergy]

theorem variance_identity {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (A : Set (Cube X)) :
    (∑ I : Cube X, if I = ⊥ then 0 else (coeff p (ind A) I)^2) =
      measure p A - (measure p A)^2 := by
  have h := parseval hp hp1 (ind A)
  rw [avg_square_ind] at h
  have hs : (∑ I, (coeff p (ind A) I)^2) = (measure p A)^2 +
      (∑ I : Cube X, if I = ⊥ then 0 else (coeff p (ind A) I)^2) := by
    have he (I : Cube X) : (coeff p (ind A) I)^2 =
        (if I = ⊥ then (measure p A)^2 else 0) +
          (if I = ⊥ then 0 else (coeff p (ind A) I)^2) := by
      by_cases hi : I = ⊥
      · subst I; simp [coeff_bot, measure]
      · simp [hi]
    calc
      (∑ I, (coeff p (ind A) I)^2) = ∑ I,
          ((if I = ⊥ then (measure p A)^2 else 0) +
            (if I = ⊥ then 0 else (coeff p (ind A) I)^2)) :=
        Finset.sum_congr rfl (fun I _ => he I)
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  linarith

theorem monoWeight_le_self {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    {I : Cube X} (hI : I ≠ ⊥) : monoWeight r I ≤ r := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hI
  have hit : I i = true := by cases h : I i <;> simp_all
  have h := Finset.prod_le_prod_of_subset_of_le_one
    (f := fun j => if I j then r else 1)
    (Finset.singleton_subset_iff.mpr (Finset.mem_univ i))
    (fun j _ => by split_ifs <;> positivity)
    (fun j _ _ => by split_ifs <;> simp_all)
  simpa [monoWeight, hit] using h

theorem high_cost {p a r : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (ha1 : a < 1) (hr : 0 ≤ r) (hbr : beta p a*r ≤ 1)
    (A : Set (Cube X)) :
    (∑ I, highCoeff p a A I * monoWeight r I) ≤
      (beta p a*r) * (measure p A - (measure p A)^2) := by
  rw [← variance_identity hp hp1 A, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro I _
  by_cases hi : I = ⊥
  · simp [highCoeff, hi]
  · simp only [highCoeff, if_neg hi]
    rw [mul_assoc, ← monoWeight_mul]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left
      (monoWeight_le_self (mul_nonneg (beta_pos hp hp1 ha ha1).le hr) hbr hi) (sq_nonneg (coeff p (ind A) I))

theorem energy_average {p a r : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (ha1 : a < 1) (hr : 0 ≤ r) (hbr : beta p a*r ≤ 1)
    (ν : Law X) (hν : ν.Spread r) (A : Set (Cube X)) :
    (∑ J, ν.weight J * energy p a A J) ≤ measure p A := by
  have he : (∑ J, ν.weight J * energy p a A J) =
      ∑ I, (coeff p (ind A) I)^2 * monoWeight (beta p a) I *
        (∑ J, if I ≤ J then ν.weight J else 0) := by
    simp only [energy, Finset.mul_sum, Finset.sum_mul, mul_ite, mul_zero, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I _
    apply Finset.sum_congr rfl
    intro J _
    split_ifs <;> ring
  rw [he]
  calc
    _ ≤ ∑ I, (coeff p (ind A) I)^2 * monoWeight (beta p a*r) I := by
      apply Finset.sum_le_sum
      intro I _
      rw [monoWeight_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (hν I)
        (mul_nonneg (sq_nonneg _) (monoWeight_nonneg (beta_pos hp hp1 ha ha1).le I))
    _ ≤ ∑ I, (coeff p (ind A) I)^2 := by
      apply Finset.sum_le_sum
      intro I _
      exact mul_le_of_le_one_right (sq_nonneg _)
        (monoWeight_le_one (mul_nonneg (beta_pos hp hp1 ha ha1).le hr) hbr I)
    _ = measure p A := by rw [parseval hp hp1, avg_square_ind]

/-- An explicit polynomial majorant of the thinned indicator of an up-class. -/
theorem theta_up_bound {p a : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (ha1 : a < 1) {A : Set (Cube X)} (hA : Up A) (J : Cube X) :
    theta a A J ≤ (measure p A)^2 + highEnergy p a Aᶜ J := by
  have hc := core_inequality hp hp1 ha ha1 hA.compl J
  have h := two_mul_le_add_of_sq_le_mul
    (theta_nonneg ha.le ha1.le Aᶜ J) (energy_nonneg hp hp1 ha ha1 Aᶜ J) hc
  rw [theta_compl, energy_split, measure_compl] at h
  nlinarith

end
end TalagrandConjectures
