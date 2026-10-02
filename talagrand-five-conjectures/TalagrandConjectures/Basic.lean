import Mathlib

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
