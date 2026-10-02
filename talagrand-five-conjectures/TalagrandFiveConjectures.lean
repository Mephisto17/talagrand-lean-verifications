import Mathlib

/-!
# Complete Lean proofs of five Talagrand conjectures

Conjectures 9.1, 7.12, 7.3: alpha = 1/2.
Conjecture 7.9: every 0 < alpha <= (sqrt(5)-1)/2, by Fang--Wang's direct proof.
Conjecture 7.2: q = 3, with the original fractional-cover cost <= 1/2.
Li's stronger two-union results: no p-spread law at density >= 1/2;
an explicit weak p-smallness certificate at density >= 2/3.
Includes Li Theorem 1.9 and Fang--Wang Theorem 1.2 with their exact parameters
(arXiv:2609.08967v1 and arXiv:2609.18458v1, respectively).
Also proves Theorem 2.1 of Park--Talagrand, arXiv:2609.33644v1.

Main names are TalagrandConjectures.conjecture_9_1, conjecture_7_12,
conjecture_7_9, conjecture_7_3, conjecture_7_2; all supporting lemmas are proved.

Conjecture 9.1 is interpreted consistently with formula (9.2): the printed
up-class formula (9.1) needs a minus sign on its right. The explicit up-class
and multiplicative forms are provided below.
For 7.12 we use displayed formula (7.13), whose empty-set kernel is 1.
The inconsistent adjacent convention h(empty,J)=0 is not used.

Lean 4.32.0; Mathlib 81a5d257c8e410db227a6665ed08f64fea08e997.
No proof placeholders or custom axioms. Run in the supplied Lake project:
  lake env lean TalagrandFiveConjectures.lean
This file imports only Mathlib; do not combine it with the modular library,
which intentionally defines the same names.
-/


/-! ## Basic -/

open Finset Classical
namespace TalagrandConjectures
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

abbrev Cube (X : Type) := X → Bool
def bit (p : ℝ) (b : Bool) : ℝ := if b then p else 1-p
def mass (p : ℝ) (x : Cube X) : ℝ := ∏ i, bit p (x i)
def avg (p : ℝ) (f : Cube X → ℝ) : ℝ := ∑ x, mass p x * f x
def ind (A : Set (Cube X)) (x : Cube X) : ℝ := if x ∈ A then 1 else 0
def measure (p : ℝ) (A : Set (Cube X)) : ℝ := avg p (ind A)
def Down (A : Set (Cube X)) : Prop := ∀ x ∈ A, ∀ y, y ≤ x → y ∈ A
def Up (A : Set (Cube X)) : Prop := ∀ x ∈ A, ∀ y, x ≤ y → y ∈ A
theorem Up.compl {A : Set (Cube X)} (h : Up A) : Down Aᶜ := by
  intro x hx y hy hya
  exact hx (h y hya x hy)
theorem Down.compl {A : Set (Cube X)} (h : Down A) : Up Aᶜ := by
  intro x hx y hy hya
  exact hx (h y hya x hy)
def restrict (J x : Cube X) : Cube X := fun i => J i && x i
def theta (a : ℝ) (A : Set (Cube X)) (J : Cube X) : ℝ :=
  avg a (fun x => ind A (restrict J x))
def monoWeight (r : ℝ) (I : Cube X) : ℝ := ∏ i, if I i then r else 1
def WeaklySmall (r : ℝ) (A : Set (Cube X)) : Prop :=
  ∃ c : Cube X → ℝ, (∀ I, 0 ≤ c I) ∧
    (∑ I, c I * monoWeight r I) ≤ 1/2 ∧
    ∀ J ∈ A, 1 ≤ ∑ I, if I ≤ J then c I else 0

structure Law (X : Type) [Fintype X] [DecidableEq X] where
  weight : Cube X → ℝ
  nonneg : ∀ J, 0 ≤ weight J
  total : ∑ J, weight J = 1

def Law.Spread (ν : Law X) (r : ℝ) : Prop :=
  ∀ I, (∑ J, if I ≤ J then ν.weight J else 0) ≤ monoWeight r I

theorem bit_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) : 0 ≤ bit p b := by
  cases b <;> simp [bit] <;> linarith
theorem mass_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (x : Cube X) : 0 ≤ mass p x :=
  Finset.prod_nonneg (fun i _ => bit_nonneg hp hp1 (x i))
theorem mass_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (x : Cube X) : 0 < mass p x := by
  apply Finset.prod_pos
  intro i _
  cases x i <;> simp [bit] <;> linarith

theorem avg_prod (p : ℝ) (f : X → Bool → ℝ) :
    avg p (fun x => ∏ i, f i (x i)) = ∏ i, ((1-p)*f i false + p*f i true) := by
  simp only [avg, mass, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i b => bit p b * f i b)]
  apply Finset.prod_congr rfl
  intro i _
  simp [Fintype.sum_bool, bit, add_comm]

theorem mass_sum (p : ℝ) : (∑ x : Cube X, mass p x) = 1 := by
  have h := avg_prod p (fun (_ : X) (_ : Bool) => (1 : ℝ))
  simpa [avg] using h
theorem avg_const (p c : ℝ) : avg p (fun _ : Cube X => c) = c := by
  simp [avg, ← Finset.sum_mul, mass_sum]
theorem avg_sum {Y : Type} [Fintype Y] (p : ℝ) (f : Y → Cube X → ℝ) :
    avg p (fun x => ∑ y, f y x) = ∑ y, avg p (f y) := by
  simp only [avg, Finset.mul_sum]
  exact Finset.sum_comm
theorem avg_mul (p c : ℝ) (f : Cube X → ℝ) :
    avg p (fun x => c*f x) = c * avg p f := by
  simp only [avg, Finset.mul_sum]
  congr 1
  funext x
  ring
theorem avg_add (p : ℝ) (f g : Cube X → ℝ) :
    avg p (fun x => f x + g x) = avg p f + avg p g := by
  simp [avg, mul_add, Finset.sum_add_distrib]
theorem avg_mono {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : Cube X → ℝ} (h : ∀ x, f x ≤ g x) : avg p f ≤ avg p g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (mass_nonneg hp hp1 x))
theorem avg_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {f : Cube X → ℝ} (h : ∀ x, 0 ≤ f x) : 0 ≤ avg p f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (mass_nonneg hp hp1 x) (h x))
theorem ind_nonneg (A : Set (Cube X)) (x : Cube X) : 0 ≤ ind A x := by
  unfold ind; split_ifs <;> norm_num
theorem ind_le_one (A : Set (Cube X)) (x : Cube X) : ind A x ≤ 1 := by
  unfold ind; split_ifs <;> norm_num
theorem measure_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (A : Set (Cube X)) :
    0 ≤ measure p A := avg_nonneg hp hp1 (ind_nonneg A)
theorem measure_le_one {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (A : Set (Cube X)) :
    measure p A ≤ 1 := (avg_mono hp hp1 (ind_le_one A)).trans_eq (avg_const p 1)
theorem theta_nonneg {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (A : Set (Cube X)) (J : Cube X) :
    0 ≤ theta a A J := avg_nonneg ha ha1 (fun x => ind_nonneg A _)
theorem theta_le_one {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (A : Set (Cube X)) (J : Cube X) :
    theta a A J ≤ 1 := (avg_mono ha ha1 (fun x => ind_le_one A _)).trans_eq (avg_const a 1)
theorem ind_compl (A : Set (Cube X)) (x : Cube X) : ind Aᶜ x = 1 - ind A x := by
  by_cases h : x ∈ A <;> simp [ind, h]
theorem measure_compl (p : ℝ) (A : Set (Cube X)) : measure p Aᶜ = 1-measure p A := by
  simp only [measure, avg, ind_compl, mul_sub, mul_one, Finset.sum_sub_distrib, mass_sum]
theorem theta_compl (a : ℝ) (A : Set (Cube X)) (J : Cube X) : theta a Aᶜ J = 1-theta a A J := by
  simp only [theta, avg, ind_compl, mul_sub, mul_one, Finset.sum_sub_distrib, mass_sum]
theorem avg_square_ind (p : ℝ) (A : Set (Cube X)) :
    avg p (fun x => (ind A x)^2) = measure p A := by
  congr 1
  funext x
  unfold ind; split_ifs <;> norm_num

theorem monoWeight_bot (r : ℝ) : monoWeight r (⊥ : Cube X) = 1 := by
  simp [monoWeight]
theorem monoWeight_nonneg {r : ℝ} (hr : 0 ≤ r) (I : Cube X) : 0 ≤ monoWeight r I := by
  apply Finset.prod_nonneg
  intro i _; split_ifs <;> positivity
theorem monoWeight_pos {r : ℝ} (hr : 0 < r) (I : Cube X) : 0 < monoWeight r I := by
  apply Finset.prod_pos
  intro i _; split_ifs <;> positivity
theorem monoWeight_mul (r s : ℝ) (I : Cube X) :
    monoWeight (r*s) I = monoWeight r I * monoWeight s I := by
  rw [monoWeight, monoWeight, monoWeight, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _; cases I i <;> simp
theorem monoWeight_le_one {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (I : Cube X) :
    monoWeight r I ≤ 1 := by
  apply Finset.prod_le_one
  · intro i _; split_ifs <;> positivity
  · intro i _; split_ifs <;> simp_all

end
end TalagrandConjectures


/-! ## Fourier -/

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


/-! ## Extrapolation -/

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


/-! ## Energy -/

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


/-! ## FangWang -/

open Finset Classical
namespace TalagrandConjectures
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

/-- Fang--Wang's signed one-coordinate kernel, in its rational form (2.3). -/
def thinningKernel (p t : ℝ) (x w : Bool) : ℝ :=
  1 + (bval x-t)*(bval w-p)/(p*(1-t))
def parentKernel (p t : ℝ) (J x w : Cube X) : ℝ :=
  ∏ i, if J i then thinningKernel p t (x i) (w i) else 1
def lifted (p t : ℝ) (J : Cube X) (f : Cube X → ℝ) (x : Cube X) : ℝ :=
  avg p (fun w => parentKernel p t J x w * f w)

theorem thinningKernel_zero {p t : ℝ} (hp : 0 < p) (ht : t < 1) :
    thinningKernel p t true false = 0 := by
  have ht' : 1-t ≠ 0 := by linarith
  simp only [thinningKernel, bval, Bool.false_eq_true, ↓reduceIte]
  field_simp
  <;> ring

theorem parentKernel_zero {p t : ℝ} (hp : 0 < p) (ht : t < 1)
    (J x w : Cube X) (h : ¬ restrict J x ≤ w) : parentKernel p t J x w = 0 := by
  obtain ⟨i, hi⟩ := not_forall.mp h
  have hJ : J i = true := by cases h' : J i <;> simp_all [restrict]
  have hx : x i = true := by cases h' : x i <;> simp_all [restrict]
  have hw : w i = false := by cases h' : w i <;> simp_all [restrict]
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (by simp [hJ, hx, hw, thinningKernel_zero hp ht])

/-- The signed kernel is exactly the previously formalized multilinear lift.
This identity connects Fang--Wang's direct proof to the shared Walsh moments. -/
theorem lifted_eq_extension {p t : ℝ} (hp : 0 < p) (ht : t < 1)
    (J x : Cube X) (f : Cube X → ℝ) :
    lifted p t J f x = extension f (fun i => zcoord p t J i (x i)) := by
  have ht' : 1-t ≠ 0 := by linarith
  unfold lifted avg extension
  apply Finset.sum_congr rfl
  intro w _
  rw [← mul_assoc, mul_comm (mass p w), mass, parentKernel,
    ← Finset.prod_mul_distrib, mul_comm _ (f w)]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases hJ : J i <;> cases hx : x i <;> cases hw : w i <;>
    simp [zcoord, thinningKernel, bval, bit, hJ, hx, hw]
  all_goals field_simp <;> (try simp) <;> ring

theorem parentKernel_normalized {p t : ℝ} (hp : 0 < p) (ht : t < 1)
    (J x : Cube X) : avg p (parentKernel p t J x) = 1 := by
  have hm (i : X) :
      (1-p)*(if J i then thinningKernel p t (x i) false else 1) +
      p*(if J i then thinningKernel p t (x i) true else 1) = 1 := by
    have ht' : 1-t ≠ 0 := by linarith
    cases hJ : J i <;> cases hx : x i <;>
      simp [thinningKernel, bval, hJ, hx]
    all_goals field_simp; ring
  rw [show parentKernel p t J x =
    fun w => ∏ i, if J i then thinningKernel p t (x i) (w i) else 1 from rfl,
    avg_prod p (fun i b => if J i then thinningKernel p t (x i) b else 1)]
  simp only [hm, Finset.prod_const_one]

/-- Fang--Wang Lemma 3.1. Positivity of the signed kernel is not assumed. -/
theorem fang_wang_square_bound {p t : ℝ} (hp : 0 < p) (ht : t < 1)
    {A : Set (Cube X)} (hA : Up A) (J x : Cube X) :
    ind A (restrict J x) ≤ (lifted p t J (ind A) x)^2 := by
  by_cases hx : restrict J x ∈ A
  · have hw (w : Cube X) : parentKernel p t J x w * ind A w =
        parentKernel p t J x w := by
      by_cases hle : restrict J x ≤ w
      · simp [ind, hA _ hx _ hle]
      · simp [parentKernel_zero hp ht J x w hle]
    have hl : lifted p t J (ind A) x = 1 := by
      unfold lifted
      simp_rw [hw]
      exact parentKernel_normalized hp ht J x
    simp [ind, hx, hl]
  · simpa [ind, hx] using sq_nonneg (lifted p t J (ind A) x)

/-- Fang--Wang Proposition 3.3: their positive Fourier-square certificate. -/
theorem fang_wang_positive_majorant {p t : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (ht1 : t < 1) {A : Set (Cube X)} (hA : Up A) (J : Cube X) :
    theta t A J ≤ energy p t A J := by
  have h := avg_mono ht.le ht1.le (fang_wang_square_bound hp ht1 hA J)
  simp_rw [lifted_eq_extension hp ht1] at h
  simpa only [z_extension_square hp hp1 ht1, theta] using h

/-- Fang--Wang Theorem 1.2, in the all-increasing-events characterization
of stochastic domination (their equation (1.2)). -/
theorem fang_wang_theorem_1_2 {p t q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (ht1 : t < 1) (hq : 0 ≤ q)
    (heta : t*q*(1-p)/(p*(1-t)) ≤ 1)
    (ν : Law X) (hν : ν.Spread q) {A : Set (Cube X)} (hA : Up A) :
    (∑ J, ν.weight J * theta t A J) ≤ measure p A := by
  have hb : beta p t*q ≤ 1 := by
    convert heta using 1 <;> unfold beta <;> ring
  exact (Finset.sum_le_sum (fun J _ => mul_le_mul_of_nonneg_left
    (fang_wang_positive_majorant hp hp1 ht ht1 hA J) (ν.nonneg J))).trans
    (energy_average hp hp1 ht ht1 hq hb ν hν A)

/-- Fang--Wang equation (1.4), the explicit target product density. -/
theorem fang_wang_target_density {t q : ℝ} (ht : 0 < t) (ht1 : t < 1) (hq : 0 < q)
    (ν : Law X) (hν : ν.Spread q) {A : Set (Cube X)} (hA : Up A) :
    (∑ J, ν.weight J * theta t A J) ≤ measure (t*q/(1-t+t*q)) A := by
  have hd : 0 < 1-t+t*q := by positivity
  have hp : 0 < t*q/(1-t+t*q) := by positivity
  have hp1 : t*q/(1-t+t*q) < 1 := by
    rw [div_lt_one hd]; linarith
  apply fang_wang_theorem_1_2 hp hp1 ht ht1 hq.le ?_ ν hν hA
  rw [div_le_one (mul_pos hp (by linarith : 0 < 1-t))]
  have he : t*q*(1-t*q/(1-t+t*q)) = t*q/(1-t+t*q)*(1-t) := by
    field_simp
    <;> ring
  exact he.le

/-- The dimension-independent improved thinning constant. -/
def goldenAlpha : ℝ := (Real.sqrt 5-1)/2
theorem goldenAlpha_pos : 0 < goldenAlpha := by
  have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have hn := Real.sqrt_nonneg (5:ℝ)
  dsimp [goldenAlpha]; nlinarith
theorem goldenAlpha_lt_one : goldenAlpha < 1 := by
  have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have hn := Real.sqrt_nonneg (5:ℝ)
  dsimp [goldenAlpha]; nlinarith
theorem goldenAlpha_equation : goldenAlpha^2 = 1-goldenAlpha := by
  have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  dsimp [goldenAlpha]; nlinarith

/-- Conjecture 7.9 with every 0 < alpha <= (sqrt(5)-1)/2, replacing the
previous alpha=1/2 theorem. Fang--Wang label this Conjecture 7.8. -/
theorem conjecture_7_9 {p a : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (hgold : a ≤ goldenAlpha)
    (ν : Law X) (hν : ν.Spread (a*p)) {A : Set (Cube X)} (hA : Up A) :
    (∑ J, ν.weight J * theta a A J) ≤ measure p A := by
  have ha1 : a < 1 := hgold.trans_lt goldenAlpha_lt_one
  apply fang_wang_theorem_1_2 hp hp1 ha ha1 (by positivity : 0 ≤ a*p) ?_ ν hν hA
  rw [div_le_one (by positivity : 0 < p*(1-a))]
  have hsq : a^2 ≤ 1-a := by
    nlinarith [goldenAlpha_equation,
      mul_nonneg (sub_nonneg.mpr hgold) (show 0 ≤ goldenAlpha+a by linarith [goldenAlpha_pos])]
  have hp2 : a^2*(1-p) ≤ 1-a := by
    nlinarith [mul_nonneg (sq_nonneg a) hp.le]
  nlinarith [mul_le_mul_of_nonneg_left hp2 hp.le]

end
end TalagrandConjectures


/-! ## Logarithmic -/

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


/-! ## Certificates -/

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


/-! ## Unions -/

open Finset Classical
namespace TalagrandConjectures
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

def flip (x : Cube X) : Cube X := fun i => !(x i)
theorem flip_flip (x : Cube X) : flip (flip x) = x := by
  funext i; simp [flip]
theorem avg_half_flip (f : Cube X → ℝ) :
    avg (1/2) (fun x => f (flip x)) = avg (1/2) f := by
  let e : Cube X ≃ Cube X := ⟨flip, flip, flip_flip, flip_flip⟩
  have hm (x : Cube X) : mass (1/2) (flip x) = mass (1/2) x := by
    apply Finset.prod_congr rfl
    intro i _
    cases h : x i <;> norm_num [bit, flip, h]
  have h := Equiv.sum_comp e (fun x => mass (1/2) x * f x)
  change (∑ x, mass (1/2) (flip x) * f (flip x)) = ∑ x, mass (1/2) x * f x at h
  simpa only [hm, avg] using h

def badTwo (A : Set (Cube X)) : Set (Cube X) :=
  {J | ¬ ∃ Y ∈ A, ∃ Z ∈ A, J ≤ fun i => Y i || Z i}
def unionOf {q : ℕ} (f : Fin q → Cube X) : Cube X :=
  fun i => univ.sup (fun j => f j i)
def badUnions (q : ℕ) (A : Set (Cube X)) : Set (Cube X) :=
  {J | ¬ ∃ f : Fin q → Cube X, (∀ j, f j ∈ A) ∧ J ≤ unionOf f}

theorem badTwo_theta {A : Set (Cube X)} {J : Cube X} (hJ : J ∈ badTwo A) :
    theta (1/2) A J ≤ 1/2 := by
  have hpoint (x : Cube X) : ind A (restrict J x) + ind A (restrict J (flip x)) ≤ 1 := by
    by_cases hx : restrict J x ∈ A
    · have hn : restrict J (flip x) ∉ A := by
        intro hy
        apply hJ
        refine ⟨restrict J x, hx, restrict J (flip x), hy, ?_⟩
        intro i
        cases h1 : J i <;> cases h2 : x i <;> simp [restrict, flip, h1, h2]
      simp [ind, hx, hn]
    · have h1 := ind_le_one A (restrict J (flip x))
      simpa [ind, hx] using h1
  have h := avg_mono (p := (1/2 : ℝ)) (by norm_num) (by norm_num) hpoint
  rw [avg_add, avg_half_flip (fun x => ind A (restrict J x)), avg_const] at h
  change theta (1/2) A J + theta (1/2) A J ≤ 1 at h
  linarith

theorem weaklySmall_badTwo_down {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {A : Set (Cube X)} (hA : Down A) (hm : (3 : ℝ)/4 ≤ measure p A) :
    WeaklySmall p (badTwo A) := by
  have hm1 := measure_le_one hp.le hp1.le A
  have hv : 0 ≤ measure p A - (measure p A)^2 := by
    have hm0 := measure_nonneg hp.le hp1.le A
    nlinarith
  refine ⟨fun I => (8/3 : ℝ) * highCoeff p (1/2) A I, ?_, ?_, ?_⟩
  · intro I
    exact mul_nonneg (by norm_num) (highCoeff_nonneg hp hp1 (by norm_num) (by norm_num) A I)
  · have h := high_cost hp hp1 (by norm_num : (0:ℝ)<1/2)
      (by norm_num : (1/2:ℝ)<1) hp.le
      (show beta p (1/2)*p ≤ 1 by rw [beta_half hp hp1]; linarith) A
    rw [beta_half hp hp1] at h
    have hmul : (1-p)*(measure p A - (measure p A)^2) ≤ measure p A - (measure p A)^2 :=
      mul_le_of_le_one_left hv (by linarith)
    simp only [mul_assoc, ← Finset.mul_sum]
    nlinarith [sq_nonneg (measure p A - 3/4)]
  · intro J hJ
    have hθ := badTwo_theta hJ
    have hbound := theta_up_bound hp hp1 (by norm_num : (0:ℝ)<1/2)
      (by norm_num : (1/2:ℝ)<1) hA.compl J
    rw [theta_compl, measure_compl, compl_compl] at hbound
    have hsq : (1-measure p A)^2 ≤ 1/16 := by
      nlinarith [mul_nonneg (show 0 ≤ measure p A-3/4 by linarith)
        (show 0 ≤ 1-measure p A by linarith)]
    have he : (∑ I : Cube X, if I ≤ J then (8/3:ℝ)*highCoeff p (1/2) A I else 0) =
        (8/3:ℝ)*highEnergy p (1/2) A J := by
      simp [highEnergy, Finset.mul_sum, mul_ite]
    rw [he]
    nlinarith

def downClosure (A : Set (Cube X)) : Set (Cube X) := {x | ∃ y ∈ A, x ≤ y}
theorem downClosure_down (A : Set (Cube X)) : Down (downClosure A) := by
  rintro x ⟨z, hz, hxz⟩ y hy
  exact ⟨z, hz, hy.trans hxz⟩
theorem subset_downClosure (A : Set (Cube X)) : A ⊆ downClosure A :=
  fun x hx => ⟨x, hx, le_rfl⟩
theorem measure_mono {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {A B : Set (Cube X)} (h : A ⊆ B) : measure p A ≤ measure p B := by
  apply avg_mono hp hp1
  intro x
  by_cases hx : x ∈ A
  · simp [ind, hx, h hx]
  · simp [ind, hx]; split_ifs <;> norm_num

theorem badTwo_subset_downClosure (A : Set (Cube X)) :
    badTwo A ⊆ badTwo (downClosure A) := by
  intro J hJ
  rintro ⟨Y, ⟨Y', hY', hY⟩, Z, ⟨Z', hZ', hZ⟩, hc⟩
  apply hJ
  refine ⟨Y', hY', Z', hZ', ?_⟩
  intro i
  exact (hc i).trans (sup_le_sup (hY i) (hZ i))

theorem weaklySmall_badTwo {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {A : Set (Cube X)} (hm : (3 : ℝ)/4 ≤ measure p A) :
    WeaklySmall p (badTwo A) := by
  have hm' := hm.trans (measure_mono hp.le hp1.le (subset_downClosure A))
  exact (weaklySmall_badTwo_down hp hp1 (downClosure_down A) hm').mono
    (badTwo_subset_downClosure A)

theorem badFour_subset_badTwo (A : Set (Cube X)) : badUnions 4 A ⊆ badTwo A := by
  intro J hJ
  rintro ⟨Y, hY, Z, hZ, hc⟩
  apply hJ
  let f : Fin 4 → Cube X := fun j => if j.val = 0 then Y else Z
  refine ⟨f, ?_, ?_⟩
  · intro j; dsimp [f]; split_ifs <;> assumption
  · intro i
    apply (hc i).trans
    apply sup_le
    · have h := Finset.le_sup (f := fun j : Fin 4 => f j i) (Finset.mem_univ (0 : Fin 4))
      simpa [f, unionOf] using h
    · have h := Finset.le_sup (f := fun j : Fin 4 => f j i) (Finset.mem_univ (1 : Fin 4))
      simpa [f, unionOf] using h

/-- Conjecture 7.2 with q=4, for arbitrary families, in the original
fractional-cover definition of weak p-smallness. -/
theorem conjecture_7_2_q4 {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (Cube X)) (hm : 1-(1:ℝ)/4 ≤ measure p A) :
    WeaklySmall p (badUnions 4 A) := by
  exact (weaklySmall_badTwo hp hp1 (by linarith : (3:ℝ)/4 ≤ measure p A)).mono
    (badFour_subset_badTwo A)

end
end TalagrandConjectures


/-! ## Li -/

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


/-! ## Main -/

open Finset Classical
namespace TalagrandConjectures
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

def support (I : Cube X) : Finset X := univ.filter (fun i => I i = true)
theorem monoWeight_eq_pow (r : ℝ) (I : Cube X) :
    monoWeight r I = r ^ (support I).card := by
  simp [monoWeight, support, Finset.prod_ite]

/-- Precisely Theorem 2.1 of the uploaded Park--Talagrand note. -/
theorem park_talagrand_theorem_2_1 {p a : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (ha1 : a < 1)
    (ν : Law X) (hν : ν.Spread (p*(1-a)/((1-p)*a)))
    {A : Set (Cube X)} (hA : Down A) (hne : A.Nonempty) :
    Real.log (measure p A) ≤ ∑ J, ν.weight J * Real.log (theta a A J) := by
  apply logarithmic_inequality hp hp1 ha ha1 (by positivity) ?_ ν hν hA hne
  have h1 : 1-p ≠ 0 := by linarith
  have h2 : 1-a ≠ 0 := by linarith
  have he : beta p a * (p*(1-a)/((1-p)*a)) = 1 := by
    unfold beta
    field_simp [ne_of_gt hp, ne_of_gt ha, h1, h2]
  exact he.le

/-- Conjecture 9.1 in up-class notation. The minus sign on the right is
necessary; it is missing in the printed formula (9.1) of the 2010 paper. -/
theorem conjecture_9_1_up {p : ℝ} (hp : 0 < p) (hp1 : p < 1/2)
    (ν : Law X) (hν : ν.Spread ((1/2)*p))
    {A : Set (Cube X)} (hA : Up A) (hproper : A ≠ Set.univ) :
    -(∑ J, ν.weight J * Real.log (1-theta (1/2) A J)) ≤
      -Real.log (1-measure p A) := by
  have h := conjecture_9_1 hp hp1 ν hν hA.compl (Set.nonempty_compl.mpr hproper)
  simp_rw [measure_compl, theta_compl] at h
  linarith

/-- The multiplicative formulation (9.2), equivalent to the logarithmic
form for nonempty down-classes. -/
theorem conjecture_9_1_multiplicative {p : ℝ} (hp : 0 < p) (hp1 : p < 1/2)
    (ν : Law X) (hν : ν.Spread ((1/2)*p))
    {A : Set (Cube X)} (hA : Down A) (hne : A.Nonempty) :
    measure p A ≤ ∏ J, (theta (1/2) A J) ^ (ν.weight J) := by
  have hp' : p < 1 := by linarith
  have hm := measure_pos hp hp' hne
  have ht (J : Cube X) : 0 < theta (1/2) A J := by
    have hc := core_inequality hp hp' (by norm_num : (0:ℝ)<1/2)
      (by norm_num : (1/2:ℝ)<1) hA J
    by_contra h
    have hmul := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h)
      (energy_nonneg hp hp' (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1) A J)
    nlinarith [sq_pos_of_pos hm]
  have he : (∏ J, (theta (1/2) A J) ^ (ν.weight J)) =
      Real.exp (∑ J, ν.weight J * Real.log (theta (1/2) A J)) := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro J _
    rw [Real.rpow_def_of_pos (ht J)]
    congr 1; ring
  rw [he]
  exact (Real.log_le_iff_le_exp hm).mp (conjecture_9_1 hp hp1 ν hν hA hne)

end
end TalagrandConjectures



set_option pp.fullNames true

#check @TalagrandConjectures.park_talagrand_theorem_2_1
#check @TalagrandConjectures.conjecture_9_1_up
#check @TalagrandConjectures.conjecture_9_1_multiplicative
#check @TalagrandConjectures.conjecture_7_12
#check @TalagrandConjectures.conjecture_7_9
#check @TalagrandConjectures.conjecture_7_3
#check @TalagrandConjectures.conjecture_7_2
#check @TalagrandConjectures.fang_wang_theorem_1_2
#check @TalagrandConjectures.fang_wang_target_density
#check @TalagrandConjectures.li_theorem_1_9
#check @TalagrandConjectures.li_no_spread_badTwo
#check @TalagrandConjectures.li_fractional_certificate
#check @TalagrandConjectures.li_weaklySmall_badTwo
#check @TalagrandConjectures.li_weaklySmall_badTwo_half

#print axioms TalagrandConjectures.park_talagrand_theorem_2_1
#print axioms TalagrandConjectures.conjecture_9_1
#print axioms TalagrandConjectures.conjecture_9_1_up
#print axioms TalagrandConjectures.conjecture_9_1_multiplicative
#print axioms TalagrandConjectures.conjecture_7_12
#print axioms TalagrandConjectures.conjecture_7_9
#print axioms TalagrandConjectures.conjecture_7_3
#print axioms TalagrandConjectures.conjecture_7_2
#print axioms TalagrandConjectures.fang_wang_theorem_1_2
#print axioms TalagrandConjectures.fang_wang_target_density
#print axioms TalagrandConjectures.li_theorem_1_9
#print axioms TalagrandConjectures.li_no_spread_badTwo
#print axioms TalagrandConjectures.li_fractional_certificate
#print axioms TalagrandConjectures.li_weaklySmall_badTwo
#print axioms TalagrandConjectures.li_weaklySmall_badTwo_half
