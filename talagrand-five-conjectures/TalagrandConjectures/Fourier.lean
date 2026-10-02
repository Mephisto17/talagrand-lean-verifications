import TalagrandConjectures.Basic

open Finset Classical
namespace TalagrandConjectures
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

def bval (b : Bool) : ℝ := if b then 1 else 0
def chi (p z : ℝ) : ℝ := (z-p) / Real.sqrt (p*(1-p))
def basis (p : ℝ) (I : Cube X) (z : X → ℝ) : ℝ :=
  ∏ i, if I i then chi p (z i) else 1
def coeff (p : ℝ) (f : Cube X → ℝ) (I : Cube X) : ℝ :=
  avg p (fun x => f x * basis p I (fun i => bval (x i)))
def extension (f : Cube X → ℝ) (z : X → ℝ) : ℝ :=
  ∑ x, f x * ∏ i, if x i then z i else 1-z i

theorem chi_mul {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (z t : ℝ) :
    chi p z * chi p t = (z-p)*(t-p)/(p*(1-p)) := by
  rw [chi, chi, div_mul_div_comm, ← pow_two, Real.sq_sqrt (by positivity)]
theorem chi_mean (p : ℝ) : (1-p)*chi p 0 + p*chi p 1 = 0 := by
  unfold chi; ring
theorem chi_variance {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (1-p)*(chi p 0)^2 + p*(chi p 1)^2 = 1 := by
  simp only [pow_two, chi_mul hp hp1]
  have h1 : 1-p ≠ 0 := by linarith
  field_simp [ne_of_gt hp, h1]
  <;> ring
theorem bit_kernel {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (b : Bool) (z : ℝ) :
    bit p b * (1 + chi p (bval b) * chi p z) = if b then z else 1-z := by
  rw [chi_mul hp hp1]
  have h1 : 1-p ≠ 0 := by linarith
  cases b <;> simp only [bit, bval, Bool.false_eq_true, ↓reduceIte]
  all_goals field_simp; ring

theorem basis_bot (p : ℝ) (z : X → ℝ) : basis p (⊥ : Cube X) z = 1 := by
  simp [basis]
theorem coeff_bot (p : ℝ) (f : Cube X → ℝ) : coeff p f ⊥ = avg p f := by
  simp [coeff, basis_bot]

theorem basis_kernel (p : ℝ) (z t : X → ℝ) :
    (∑ I : Cube X, basis p I z * basis p I t) =
      ∏ i, (1+chi p (z i)*chi p (t i)) := by
  simp only [basis, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : X) (b : Bool) =>
    (if b then chi p (z i) else 1) * (if b then chi p (t i) else 1))]
  apply Finset.prod_congr rfl
  intro i _
  simp [Fintype.sum_bool, add_comm]

theorem extension_eq_fourier {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : Cube X → ℝ) (z : X → ℝ) :
    extension f z = ∑ I, coeff p f I * basis p I z := by
  simp only [coeff, avg, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have he : (∑ I : Cube X,
      mass p x * (f x * basis p I (fun i => bval (x i))) * basis p I z) =
      f x * (mass p x * ∑ I, basis p I (fun i => bval (x i)) * basis p I z) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I _; ring
  rw [he, basis_kernel, mass, ← Finset.prod_mul_distrib]
  simp_rw [bit_kernel hp hp1]

theorem extension_vertex (f : Cube X → ℝ) (x : Cube X) :
    extension f (fun i => bval (x i)) = f x := by
  unfold extension
  rw [Finset.sum_eq_single x]
  · have h : ∀ i, (if x i then bval (x i) else 1-bval (x i)) = 1 := by
      intro i; cases x i <;> simp [bval]
    simp [h]
  · intro y _ hy
    have hne : ∃ i, y i ≠ x i := Function.ne_iff.mp hy
    obtain ⟨i, hi⟩ := hne
    have hz : (∏ j, if y j then bval (x j) else 1-bval (x j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      cases hyi : y i <;> cases hxi : x i <;> simp_all [bval]
    rw [hz, mul_zero]
  · simp

theorem parseval {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (f : Cube X → ℝ) :
    (∑ I, (coeff p f I)^2) = avg p (fun x => (f x)^2) := by
  calc
    (∑ I, (coeff p f I)^2) =
        ∑ I, avg p (fun x => coeff p f I * (f x * basis p I (fun i => bval (x i)))) := by
      simp [avg_mul, coeff, pow_two]
    _ = avg p (fun x => ∑ I, coeff p f I * (f x * basis p I (fun i => bval (x i)))) :=
      (avg_sum p _).symm
    _ = avg p (fun x => (f x)^2) := by
      congr 1
      funext x
      have h := (extension_eq_fourier hp hp1 f (fun i => bval (x i))).symm
      rw [extension_vertex] at h
      calc
        (∑ I, coeff p f I * (f x * basis p I (fun i => bval (x i)))) =
            f x * ∑ I, coeff p f I * basis p I (fun i => bval (x i)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro I _; ring
        _ = (f x)^2 := by rw [h]; ring

theorem product_moments (p a : ℝ) (z : X → Bool → ℝ) (v : X → ℝ)
    (hm : ∀ i, (1-a)*chi p (z i false) + a*chi p (z i true) = 0)
    (hv : ∀ i, (1-a)*(chi p (z i false))^2 + a*(chi p (z i true))^2 = v i)
    (I K : Cube X) :
    avg a (fun x => basis p I (fun i => z i (x i)) * basis p K (fun i => z i (x i))) =
      if I = K then ∏ i, if I i then v i else 1 else 0 := by
  simp only [basis, ← Finset.prod_mul_distrib]
  rw [avg_prod a (fun (i : X) (b : Bool) =>
    (if I i then chi p (z i b) else 1) * (if K i then chi p (z i b) else 1))]
  have hpoint (i : X) :
      (1-a)*((if I i then chi p (z i false) else 1)*(if K i then chi p (z i false) else 1)) +
        a*((if I i then chi p (z i true) else 1)*(if K i then chi p (z i true) else 1)) =
      if I i = K i then if I i then v i else 1 else 0 := by
    cases hi : I i <;> cases hk : K i <;> simp [hm i, ← pow_two, hv i] <;> ring
  simp_rw [hpoint]
  by_cases h : I = K
  · subst K; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

end
end TalagrandConjectures
