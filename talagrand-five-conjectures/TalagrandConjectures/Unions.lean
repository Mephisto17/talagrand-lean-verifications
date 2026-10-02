import TalagrandConjectures.Certificates

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
