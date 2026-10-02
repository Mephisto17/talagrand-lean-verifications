import TalagrandConjectures.Energy

open Finset Classical
namespace TalagrandConjectures
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

theorem measure_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {A : Set (Cube X)} (hA : A.Nonempty) : 0 < measure p A := by
  obtain ⟨x, hx⟩ := hA
  have h : mass p x * ind A x ≤ measure p A :=
    Finset.single_le_sum
      (f := fun y => mass p y * ind A y)
      (fun y _ => mul_nonneg (mass_nonneg hp.le hp1.le y) (ind_nonneg A y))
      (Finset.mem_univ x)
  simpa [ind, hx] using (mass_pos hp hp1 x).trans_le (by simpa [ind, hx] using h)

theorem Law.log_bound (ν : Law X) {M : ℝ} (hM : 0 < M)
    (f : Cube X → ℝ) (hf : ∀ J, 0 < f J)
    (havg : (∑ J, ν.weight J * f J) ≤ M) :
    (∑ J, ν.weight J * Real.log (f J)) ≤ Real.log M := by
  have ht (J : Cube X) : Real.log (f J) ≤ Real.log M + (f J/M - 1) := by
    have h := Real.log_le_sub_one_of_pos (div_pos (hf J) hM)
    rw [Real.log_div (ne_of_gt (hf J)) (ne_of_gt hM)] at h
    linarith
  have hs := Finset.sum_le_sum (s := (univ : Finset (Cube X)))
    (fun J _ => mul_le_mul_of_nonneg_left (ht J) (ν.nonneg J))
  have he : (∑ J, ν.weight J * (Real.log M + (f J/M - 1))) =
      Real.log M + (∑ J, ν.weight J*f J)/M - 1 := by
    simp only [mul_add, mul_sub, mul_one, mul_div_assoc,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
      ← Finset.sum_mul, ν.total, one_mul]
    simp only [div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
    ring
  rw [he] at hs
  have hd : (∑ J, ν.weight J*f J)/M ≤ 1 := (div_le_one hM).mpr havg
  linarith

/-- The strong logarithmic inequality of Park--Talagrand, proved from the
finite Walsh expansion and the vanishing/Cauchy--Schwarz argument. -/
theorem logarithmic_inequality {p a r : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (ha1 : a < 1) (hr : 0 ≤ r) (hbr : beta p a*r ≤ 1)
    (ν : Law X) (hν : ν.Spread r) {A : Set (Cube X)} (hA : Down A)
    (hne : A.Nonempty) :
    Real.log (measure p A) ≤ ∑ J, ν.weight J * Real.log (theta a A J) := by
  have hm := measure_pos hp hp1 hne
  have hc (J : Cube X) := core_inequality hp hp1 ha ha1 hA J
  have hQ (J : Cube X) : 0 < energy p a A J := by
    have hn := theta_nonneg ha.le ha1.le A J
    by_contra h
    have hh := mul_nonpos_of_nonneg_of_nonpos hn (le_of_not_gt h)
    nlinarith [sq_pos_of_pos hm, hc J]
  have hT (J : Cube X) : 0 < theta a A J := by
    by_contra h
    have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) (hQ J).le
    nlinarith [sq_pos_of_pos hm, hc J]
  have hpoint (J : Cube X) : 2*Real.log (measure p A) ≤
      Real.log (theta a A J) + Real.log (energy p a A J) := by
    have h := Real.log_le_log (sq_pos_of_pos hm) (hc J)
    rw [Real.log_pow, Real.log_mul (ne_of_gt (hT J)) (ne_of_gt (hQ J))] at h
    norm_num at h ⊢
    exact h
  have hs := Finset.sum_le_sum (s := (univ : Finset (Cube X)))
    (fun J _ => mul_le_mul_of_nonneg_left (hpoint J) (ν.nonneg J))
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, ν.total, one_mul] at hs
  have hlog := ν.log_bound hm (energy p a A) hQ
    (energy_average hp hp1 ha ha1 hr hbr ν hν A)
  linarith

theorem beta_half {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    beta p (1/2) * p = 1-p := by
  unfold beta
  field_simp
  <;> ring

/-- Conjecture 9.1 in its consistent down-class/logarithmic form (9.2),
with the explicit universal constant alpha=1/2. -/
theorem conjecture_9_1 {p : ℝ} (hp : 0 < p) (hp1 : p < 1/2)
    (ν : Law X) (hν : ν.Spread ((1/2)*p))
    {A : Set (Cube X)} (hA : Down A) (hne : A.Nonempty) :
    Real.log (measure p A) ≤ ∑ J, ν.weight J * Real.log (theta (1/2) A J) := by
  have hp' : p < 1 := by linarith
  apply logarithmic_inequality hp hp' (by norm_num) (by norm_num)
    (by positivity) ?_ ν hν hA hne
  have h := beta_half hp hp'
  nlinarith

/-- Conjecture 7.9: domination of the thinned law on every up-class,
with alpha=1/2 and the same alpha in the spreadness parameter. -/
theorem conjecture_7_9_half {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ν : Law X) (hν : ν.Spread ((1/2)*p))
    {A : Set (Cube X)} (hA : Up A) :
    (∑ J, ν.weight J * theta (1/2) A J) ≤ measure p A := by
  have hpoint (J : Cube X) : theta (1/2) A J ≤
      1 - 2*measure p Aᶜ + energy p (1/2) Aᶜ J := by
    have h := theta_up_bound hp hp1 (by norm_num : (0:ℝ)<1/2)
      (by norm_num : (1/2:ℝ)<1) hA J
    rw [energy_split, measure_compl]
    nlinarith
  have hs := Finset.sum_le_sum (s := (univ : Finset (Cube X)))
    (fun J _ => mul_le_mul_of_nonneg_left (hpoint J) (ν.nonneg J))
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, ν.total, one_mul] at hs
  have he := energy_average hp hp1 (by norm_num : (0:ℝ)<1/2)
    (by norm_num : (1/2:ℝ)<1) (by positivity : 0 ≤ (1/2)*p)
    (show beta p (1/2)*((1/2)*p) ≤ 1 by nlinarith [beta_half hp hp1]) ν hν Aᶜ
  rw [measure_compl] at he hs
  linarith

end
end TalagrandConjectures
