import TalagrandConjectures.Energy

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
