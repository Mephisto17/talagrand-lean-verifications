import TalagrandConjectures.FangWang
import TalagrandConjectures.Li

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
