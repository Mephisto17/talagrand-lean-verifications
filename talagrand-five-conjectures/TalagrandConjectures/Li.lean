import TalagrandConjectures.Unions

open Finset Classical
namespace TalagrandConjectures
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

/-- Li's eigenvalue lambda = -(1-p)/p. -/
def liLambda (p : ℝ) : ℝ := -(1-p)/p
def liCoord (p : ℝ) (J x : Cube X) (i : X) : ℝ :=
  if J i then p + liLambda p*(bval (x i)-p) else p
def liEnergy (p : ℝ) (A : Set (Cube X)) (J : Cube X) : ℝ :=
  ∑ I, if I ≤ J then (coeff p (ind A) I)^2 * monoWeight (liLambda p) I else 0

theorem liLambda_eq_beta (p : ℝ) : liLambda p = -beta p (1/2) := by
  unfold liLambda beta
  ring

theorem chi_liCoord (p : ℝ) (J x : Cube X) (i : X) :
    chi p (liCoord p J x i) =
      if J i then liLambda p * chi p (bval (x i)) else 0 := by
  cases h : J i <;> simp [liCoord, chi, h] <;> ring

/-- Li's product kernel (2.1), with h(0,0)=0 and eigenvalue liLambda. -/
def liKernel (p : ℝ) (J x y : Cube X) : ℝ :=
  ∏ i, if J i then 1 + liLambda p*chi p (bval (x i))*chi p (bval (y i)) else 1

theorem li_lift_is_kernel {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (J x : Cube X) (f : Cube X → ℝ) :
    avg p (fun y => liKernel p J x y * f y) = extension f (liCoord p J x) := by
  unfold avg extension
  apply Finset.sum_congr rfl
  intro y _
  rw [← mul_assoc, mul_comm (mass p y), mass, liKernel,
    ← Finset.prod_mul_distrib, mul_comm _ (f y)]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [← bit_kernel hp hp1 (y i) (liCoord p J x i), chi_liCoord]
  cases J i <;> simp <;> ring

theorem liCoord_zero {p : ℝ} (hp : 0 < p) (J x : Cube X) (i : X)
    (hJ : J i = true) (hx : x i = false) : liCoord p J x i = 1 := by
  simp [liCoord, liLambda, bval, hJ, hx, ne_of_gt hp]

/-- Diagonalization of Li's product kernel, expressed as a multilinear lift. -/
theorem basis_liCoord (p : ℝ) (I J x : Cube X) :
    basis p I (liCoord p J x) =
      (if I ≤ J then monoWeight (liLambda p) I else 0) *
        basis p I (fun i => bval (x i)) := by
  rw [← diagonal_weight, basis, basis, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [chi_liCoord]
  cases I i <;> cases J i <;> simp

/-- Li Lemma 2.3: the quadratic form vanishes on a two-union obstruction.
The extension weights are the Bernoulli mass times Li's signed kernel. -/
theorem li_extension_vanish {p : ℝ} (hp : 0 < p)
    {A : Set (Cube X)} {J x : Cube X} (hJ : J ∈ badTwo A) (hx : x ∈ A) :
    extension (ind A) (liCoord p J x) = 0 := by
  apply Finset.sum_eq_zero
  intro y _
  by_cases hy : y ∈ A
  · have hn : ¬ J ≤ fun i => x i || y i := fun h => hJ ⟨x, hx, y, hy, h⟩
    obtain ⟨i, hi⟩ := not_forall.mp hn
    have hJi : J i = true := by cases h : J i <;> simp_all
    have hxi : x i = false := by cases h : x i <;> simp_all
    have hyi : y i = false := by cases h : y i <;> simp_all
    have hz : (∏ j, if y j then liCoord p J x j else 1-liCoord p J x j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hyi, liCoord_zero hp J x i hJi hxi])
    rw [hz, mul_zero]
  · simp [ind, hy]

theorem li_quadratic_form {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (Cube X)) (J : Cube X) :
    avg p (fun x => ind A x * extension (ind A) (liCoord p J x)) = liEnergy p A J := by
  simp_rw [extension_eq_fourier hp hp1, Finset.mul_sum, avg_sum, basis_liCoord]
  unfold liEnergy
  apply Finset.sum_congr rfl
  intro I _
  have he (x : Cube X) : ind A x *
      (coeff p (ind A) I * ((if I ≤ J then monoWeight (liLambda p) I else 0) *
        basis p I (fun i => bval (x i)))) =
      (coeff p (ind A) I * (if I ≤ J then monoWeight (liLambda p) I else 0)) *
        (ind A x * basis p I (fun i => bval (x i))) := by ring
  simp_rw [he, avg_mul]
  change coeff p (ind A) I * (if I ≤ J then monoWeight (liLambda p) I else 0) *
      coeff p (ind A) I = _
  split_ifs <;> ring

theorem liEnergy_zero {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {A : Set (Cube X)} {J : Cube X} (hJ : J ∈ badTwo A) : liEnergy p A J = 0 := by
  rw [← li_quadratic_form hp hp1]
  have h (x : Cube X) : ind A x * extension (ind A) (liCoord p J x) = 0 := by
    by_cases hx : x ∈ A
    · rw [li_extension_vanish hp hJ hx, mul_zero]
    · simp [ind, hx]
  simp_rw [h, avg_const]

theorem monoWeight_neg_lower {b : ℝ} (hb : 0 ≤ b) (I : Cube X) :
    -monoWeight b I ≤ monoWeight (-b) I := by
  have he : |monoWeight (-b) I| = monoWeight b I := by
    rw [monoWeight, Finset.abs_prod]
    apply Finset.prod_congr rfl
    intro i _
    cases I i <;> simp [abs_of_nonneg hb]
  simpa only [he] using neg_abs_le (monoWeight (-b) I)

/-- The nonconstant Fourier squares give an explicit covering certificate.
This is the pointwise form of Li's spectral lower bound. -/
theorem li_cover_bound {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {A : Set (Cube X)} {J : Cube X} (hJ : J ∈ badTwo A) :
    (measure p A)^2 ≤ highEnergy p (1/2) A J := by
  have hpoint (I : Cube X) : (if I = ⊥ then (measure p A)^2 else 0) ≤
      (if I ≤ J then (coeff p (ind A) I)^2 * monoWeight (liLambda p) I else 0) +
      (if I ≤ J then highCoeff p (1/2) A I else 0) := by
    by_cases hi : I = ⊥
    · subst I; simp [coeff_bot, measure, monoWeight_bot, highCoeff]
    · simp only [if_neg hi, highCoeff]
      by_cases hij : I ≤ J
      · simp only [if_pos hij, if_neg hi, liLambda_eq_beta]
        have h := mul_le_mul_of_nonneg_left
          (monoWeight_neg_lower (beta_pos hp hp1 (by norm_num : (0:ℝ)<1/2)
            (by norm_num : (1/2:ℝ)<1)).le I)
          (sq_nonneg (coeff p (ind A) I))
        linarith
      · simp [hij]
  have hs := Finset.sum_le_sum (s := (univ : Finset (Cube X))) (fun I _ => hpoint I)
  rw [Finset.sum_add_distrib] at hs
  have hz := liEnergy_zero hp hp1 hJ
  unfold liEnergy at hz
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true,
    hz, zero_add, highEnergy] using hs

theorem highEnergy_average {p a r : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (ha1 : a < 1) (hr : 0 ≤ r) (hbr : beta p a*r ≤ 1)
    (ν : Law X) (hν : ν.Spread r) (A : Set (Cube X)) :
    (∑ J, ν.weight J * highEnergy p a A J) ≤
      (beta p a*r)*(measure p A-(measure p A)^2) := by
  have he : (∑ J, ν.weight J * highEnergy p a A J) =
      ∑ I, highCoeff p a A I * (∑ J, if I ≤ J then ν.weight J else 0) := by
    simp only [highEnergy, Finset.mul_sum, mul_ite, mul_zero, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I _
    apply Finset.sum_congr rfl
    intro J _
    split_ifs <;> ring
  rw [he]
  exact (Finset.sum_le_sum (fun I _ => mul_le_mul_of_nonneg_left
    (hν I) (highCoeff_nonneg hp hp1 ha ha1 A I))).trans
      (high_cost hp hp1 ha ha1 hr hbr A)

/-- A probability is carried by A exactly when all positive atoms belong to A. -/
def Law.Carried (ν : Law X) (A : Set (Cube X)) : Prop :=
  ∀ J, 0 < ν.weight J → J ∈ A

/-- Chen Li, Theorem 1.9, with its exact quantitative constant. -/
theorem li_theorem_1_9 {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (Cube X)) (ν : Law X) (hν : ν.Spread p) (hcar : ν.Carried (badTwo A)) :
    measure p A ≤ (1-p)/(2-p) := by
  have hpoint (J : Cube X) : ν.weight J*(measure p A)^2 ≤
      ν.weight J*highEnergy p (1/2) A J := by
    by_cases hJ : 0 < ν.weight J
    · exact mul_le_mul_of_nonneg_left (li_cover_bound hp hp1 (hcar J hJ)) (ν.nonneg J)
    · have hz : ν.weight J = 0 := le_antisymm (le_of_not_gt hJ) (ν.nonneg J)
      simp [hz]
  have hs := Finset.sum_le_sum (s := (univ : Finset (Cube X))) (fun J _ => hpoint J)
  rw [← Finset.sum_mul, ν.total, one_mul] at hs
  have hc := highEnergy_average hp hp1 (by norm_num : (0:ℝ)<1/2)
    (by norm_num : (1/2:ℝ)<1) hp.le
    (show beta p (1/2)*p ≤ 1 by rw [beta_half hp hp1]; linarith) ν hν A
  rw [beta_half hp hp1] at hc
  have hm0 := measure_nonneg hp.le hp1.le A
  have hd : 0 < 2-p := by linarith
  rw [le_div_iff₀ hd]
  by_cases hm : measure p A = 0
  · rw [hm]; linarith
  · have hmpos : 0 < measure p A := lt_of_le_of_ne hm0 (Ne.symm hm)
    have hprod : measure p A*((2-p)*measure p A-(1-p)) ≤ 0 := by nlinarith
    have hf : (2-p)*measure p A-(1-p) ≤ 0 := by
      by_contra hn
      have hc := mul_pos hmpos (lt_of_not_ge hn)
      linarith
    nlinarith

/-- Li's two-union conclusion holds even at density exactly one half. -/
theorem li_no_spread_badTwo {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (Cube X)) (hm : (1:ℝ)/2 ≤ measure p A) :
    ¬ ∃ ν : Law X, ν.Spread p ∧ ν.Carried (badTwo A) := by
  rintro ⟨ν, hν, hcar⟩
  have h := li_theorem_1_9 hp hp1 A ν hν hcar
  have hd : 0 < 2-p := by linarith
  have h' := (le_div_iff₀ hd).mp h
  nlinarith [mul_le_mul_of_nonneg_right hm hd.le]

/-- Explicit certificate extracted from Li's vanishing quadratic form. -/
def liCertificate (p : ℝ) (A : Set (Cube X)) (I : Cube X) : ℝ :=
  highCoeff p (1/2) A I / (measure p A)^2

theorem li_fractional_certificate {p r : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (Cube X)) (hm : 0 < measure p A) (hr : 0 ≤ r)
    (hbr : beta p (1/2)*r ≤ 1) :
    (∀ I, 0 ≤ liCertificate p A I) ∧
    (∑ I, liCertificate p A I * monoWeight r I) ≤
      (beta p (1/2)*r)*(measure p A-(measure p A)^2)/(measure p A)^2 ∧
    ∀ J ∈ badTwo A, 1 ≤ ∑ I, if I ≤ J then liCertificate p A I else 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro I
    exact div_nonneg (highCoeff_nonneg hp hp1 (by norm_num) (by norm_num) A I) (sq_nonneg _)
  · have h := high_cost hp hp1 (by norm_num : (0:ℝ)<1/2)
      (by norm_num : (1/2:ℝ)<1) hr hbr A
    simpa only [liCertificate, div_mul_eq_mul_div, ← Finset.sum_div] using
      div_le_div_of_nonneg_right h (sq_nonneg (measure p A))
  · intro J hJ
    have he : (∑ I : Cube X, if I ≤ J then liCertificate p A I else 0) =
        highEnergy p (1/2) A J / (measure p A)^2 := by
      simp only [liCertificate, highEnergy, Finset.sum_div, ite_div, zero_div]
    rw [he, one_le_div (sq_pos_of_pos hm)]
    exact li_cover_bound hp hp1 hJ

theorem li_weaklySmall_of_bound {p r : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (Cube X)) (hm : 0 < measure p A) (hr : 0 ≤ r)
    (hbr : beta p (1/2)*r ≤ 1)
    (hcost : (beta p (1/2)*r)*(measure p A-(measure p A)^2) ≤ (measure p A)^2/2) :
    WeaklySmall r (badTwo A) := by
  obtain ⟨hc, hsum, hcover⟩ := li_fractional_certificate hp hp1 A hm hr hbr
  refine ⟨liCertificate p A, hc, hsum.trans ?_, hcover⟩
  rw [div_le_iff₀ (sq_pos_of_pos hm)]
  linarith

/-- Original cost-1/2 weak p-smallness, with density improved from 3/4 to 2/3
and only two unions. No duality normalization is hidden in this statement. -/
theorem li_weaklySmall_badTwo {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (Cube X)) (hm : (2:ℝ)/3 ≤ measure p A) :
    WeaklySmall p (badTwo A) := by
  have hm0 : 0 < measure p A := by linarith
  have hm1 := measure_le_one hp.le hp1.le A
  have hv : 0 ≤ measure p A-(measure p A)^2 := by nlinarith
  apply li_weaklySmall_of_bound hp hp1 A hm0 hp.le
    (show beta p (1/2)*p ≤ 1 by rw [beta_half hp hp1]; linarith)
  rw [beta_half hp hp1]
  have h1 := mul_le_of_le_one_left hv (show 1-p ≤ 1 by linarith)
  nlinarith [mul_nonneg (show 0 ≤ measure p A-2/3 by linarith) hm0.le]

/-- At density one half, the explicit certificate has cost <= 1/2 at p/2. -/
theorem li_weaklySmall_badTwo_half {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (Cube X)) (hm : (1:ℝ)/2 ≤ measure p A) :
    WeaklySmall (p/2) (badTwo A) := by
  have hm0 : 0 < measure p A := by linarith
  have hm1 := measure_le_one hp.le hp1.le A
  have hv : 0 ≤ measure p A-(measure p A)^2 := by nlinarith
  have hb : beta p (1/2)*(p/2) = (1-p)/2 := by nlinarith [beta_half hp hp1]
  apply li_weaklySmall_of_bound hp hp1 A hm0 (by positivity)
    (show beta p (1/2)*(p/2) ≤ 1 by rw [hb]; linarith)
  rw [hb]
  have h1 := mul_le_of_le_one_left hv (show 1-p ≤ 1 by linarith)
  nlinarith [mul_nonneg (show 0 ≤ measure p A-1/2 by linarith) hm0.le]

theorem badThree_subset_badTwo (A : Set (Cube X)) : badUnions 3 A ⊆ badTwo A := by
  intro J hJ
  rintro ⟨Y, hY, Z, hZ, hc⟩
  apply hJ
  let f : Fin 3 → Cube X := fun j => if j.val = 0 then Y else Z
  refine ⟨f, ?_, ?_⟩
  · intro j; dsimp [f]; split_ifs <;> assumption
  · intro i
    apply (hc i).trans
    apply sup_le
    · have h := Finset.le_sup (f := fun j : Fin 3 => f j i) (Finset.mem_univ (0 : Fin 3))
      simpa [f, unionOf] using h
    · have h := Finset.le_sup (f := fun j : Fin 3 => f j i) (Finset.mem_univ (1 : Fin 3))
      simpa [f, unionOf] using h

/-- The original Conjecture 7.2 with q=3, replacing q=4. The stronger
two-union statement is `li_weaklySmall_badTwo`; Li's exact spread-measure
statement is `li_theorem_1_9` and its half-density consequence above. -/
theorem conjecture_7_2 {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (Cube X)) (hm : 1-(1:ℝ)/3 ≤ measure p A) :
    WeaklySmall p (badUnions 3 A) := by
  exact (li_weaklySmall_badTwo hp hp1 A (by linarith)).mono (badThree_subset_badTwo A)

end
end TalagrandConjectures
