import TalagrandConjectures.Fourier

open Finset Classical
namespace TalagrandConjectures
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

def beta (p a : ℝ) : ℝ := a*(1-p)/((1-a)*p)
def zcoord (p a : ℝ) (J : Cube X) (i : X) (b : Bool) : ℝ :=
  if J i then if b then 1 else (p-a)/(1-a) else p
def energy (p a : ℝ) (A : Set (Cube X)) (J : Cube X) : ℝ :=
  ∑ I, if I ≤ J then (coeff p (ind A) I)^2 * monoWeight (beta p a) I else 0

theorem zmean (p a : ℝ) (ha1 : a < 1) (J : Cube X) (i : X) :
    (1-a)*chi p (zcoord p a J i false) + a*chi p (zcoord p a J i true) = 0 := by
  have ha : 1-a ≠ 0 := by linarith
  cases h : J i <;> simp [zcoord, h, chi]
  field_simp [ha]
  <;> ring

theorem zvariance {p a : ℝ} (hp : 0 < p) (hp1 : p < 1) (ha1 : a < 1)
    (J : Cube X) (i : X) :
    (1-a)*(chi p (zcoord p a J i false))^2 + a*(chi p (zcoord p a J i true))^2 =
      if J i then beta p a else 0 := by
  have ha : 1-a ≠ 0 := by linarith
  have h1 : 1-p ≠ 0 := by linarith
  cases h : J i <;> simp only [zcoord, h, Bool.false_eq_true, ↓reduceIte]
  · simp [chi]
  · simp only [pow_two, chi_mul hp hp1, beta]
    field_simp [ha, h1, ne_of_gt hp]
    <;> ring

theorem diagonal_weight (b : ℝ) (I J : Cube X) :
    (∏ i, if I i then if J i then b else 0 else 1) =
      if I ≤ J then monoWeight b I else 0 := by
  by_cases h : I ≤ J
  · rw [if_pos h]
    apply Finset.prod_congr rfl
    intro i _
    have hi := h i
    cases hI : I i <;> cases hJ : J i <;> simp_all [monoWeight, Bool.le_iff_imp]
  · rw [if_neg h]
    have h' : ∃ i, ¬ I i ≤ J i := not_forall.mp h
    obtain ⟨i, hi⟩ := h'
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases hI : I i <;> cases hJ : J i <;> simp_all

theorem z_basis_product {p a : ℝ} (hp : 0 < p) (hp1 : p < 1) (ha1 : a < 1)
    (I K J : Cube X) :
    avg a (fun x => basis p I (fun i => zcoord p a J i (x i)) *
      basis p K (fun i => zcoord p a J i (x i))) =
      if I = K then if I ≤ J then monoWeight (beta p a) I else 0 else 0 := by
  rw [product_moments p a (zcoord p a J) (fun i => if J i then beta p a else 0)
    (zmean p a ha1 J) (zvariance hp hp1 ha1 J), diagonal_weight]

theorem z_basis_mean {p a : ℝ} (hp : 0 < p) (hp1 : p < 1) (ha1 : a < 1)
    (I J : Cube X) :
    avg a (fun x => basis p I (fun i => zcoord p a J i (x i))) =
      if I = ⊥ then 1 else 0 := by
  have h := z_basis_product hp hp1 ha1 I ⊥ J
  by_cases he : I = ⊥
  · subst I; simpa [basis_bot, monoWeight_bot] using h
  · simpa [basis_bot, he] using h

theorem z_extension_mean {p a : ℝ} (hp : 0 < p) (hp1 : p < 1) (ha1 : a < 1)
    (f : Cube X → ℝ) (J : Cube X) :
    avg a (fun x => extension f (fun i => zcoord p a J i (x i))) = avg p f := by
  simp_rw [extension_eq_fourier hp hp1, avg_sum, avg_mul, z_basis_mean hp hp1 ha1]
  simp [coeff_bot]

theorem avg_square_sum {Y : Type} [Fintype Y] (a : ℝ)
    (c : Y → ℝ) (f : Y → Cube X → ℝ) :
    avg a (fun x => (∑ I, c I * f I x)^2) =
      ∑ I, ∑ K, c I*c K*avg a (fun x => f I x*f K x) := by
  have h (x : Cube X) : (∑ I, c I*f I x)^2 =
      ∑ I, ∑ K, (c I*c K)*(f I x*f K x) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I _
    apply Finset.sum_congr rfl
    intro K _; ring
  simp_rw [h, avg_sum, avg_mul]

theorem z_extension_square {p a : ℝ} (hp : 0 < p) (hp1 : p < 1) (ha1 : a < 1)
    (A : Set (Cube X)) (J : Cube X) :
    avg a (fun x => (extension (ind A) (fun i => zcoord p a J i (x i)))^2) =
      energy p a A J := by
  simp_rw [extension_eq_fourier hp hp1]
  rw [avg_square_sum]
  simp_rw [z_basis_product hp hp1 ha1]
  simp [energy, mul_ite, pow_two]

/-- A hereditary indicator's multilinear extension vanishes on every face
whose fixed 1-coordinates do not form a member of the family. -/
theorem extension_vanish {A : Set (Cube X)} (hA : Down A) (I : Cube X)
    (hI : I ∉ A) (z : X → ℝ) (hz : ∀ i, I i = true → z i = 1) :
    extension (ind A) z = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : x ∈ A
  · have hn : ¬ I ≤ x := fun h => hI (hA x hx I h)
    obtain ⟨i, hi⟩ := not_forall.mp hn
    have hiI : I i = true := by cases h : I i <;> simp_all
    have hix : x i = false := by cases h : x i <;> simp_all
    have hprod : (∏ j, if x j then z j else 1-z j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hix, hz i hiI])
    rw [hprod, mul_zero]
  · simp [ind, hx]

/-- The pointwise Cauchy--Schwarz inequality at the heart of Park--Talagrand. -/
theorem core_inequality {p a : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (ha1 : a < 1) {A : Set (Cube X)} (hA : Down A) (J : Cube X) :
    (measure p A)^2 ≤ theta a A J * energy p a A J := by
  let F : Cube X → ℝ := fun x => extension (ind A) (fun i => zcoord p a J i (x i))
  have hzero (x : Cube X) (hx : restrict J x ∉ A) : F x = 0 := by
    apply extension_vanish hA (restrict J x) hx
    intro i hi
    have hJ : J i = true := by cases h : J i <;> simp_all [restrict]
    have hx : x i = true := by cases h : x i <;> simp_all [restrict]
    simp [zcoord, hJ, hx]
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (univ : Finset (Cube X))
    (r := fun x => mass a x * F x)
    (f := fun x => mass a x * ind A (restrict J x))
    (g := fun x => mass a x * (F x)^2)
    (fun x _ => mul_nonneg (mass_nonneg ha.le ha1.le x) (ind_nonneg A _))
    (fun x _ => mul_nonneg (mass_nonneg ha.le ha1.le x) (sq_nonneg _))
    (fun x _ => by
      by_cases hx : restrict J x ∈ A
      · simp only [ind, if_pos hx]; nlinarith [sq_nonneg (mass a x * F x)]
      · rw [hzero x hx]; simp)
  change (avg a F)^2 ≤ theta a A J * avg a (fun x => (F x)^2) at h
  rw [z_extension_mean hp hp1 ha1, z_extension_square hp hp1 ha1] at h
  exact h

end
end TalagrandConjectures
