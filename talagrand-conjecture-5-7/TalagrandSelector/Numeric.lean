import Mathlib

open Finset
namespace TalagrandSelector

theorem index_sum_bound (n t : ℕ) :
    (∑ j : Fin (n+1), if (j : ℕ) ≤ 2*t then (2 : ℝ)^(j : ℕ) else 0) ≤ 16^t := by
  have hnat : ∀ t : ℕ, 2*t+1 ≤ 4^t := by
    intro t
    induction t with
    | zero => norm_num
    | succ t ih => rw [pow_succ]; nlinarith
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j ≤ 2*t then (2 : ℝ)^j else 0) (n+1),
    ← Finset.sum_filter]
  have hs : (range (n+1)).filter (fun j => j ≤ 2*t) ⊆ range (2*t+1) := by
    intro j hj
    exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hj).2; omega)
  calc
    (∑ j ∈ (range (n+1)).filter (fun j => j ≤ 2*t), (2 : ℝ)^j) ≤
        ∑ j ∈ range (2*t+1), (2 : ℝ)^j :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)
    _ ≤ ∑ _j ∈ range (2*t+1), (2 : ℝ)^(2*t) := by
      apply Finset.sum_le_sum
      intro j hj
      exact pow_le_pow_right₀ (by norm_num) (by have := Finset.mem_range.mp hj; omega)
    _ = (2*t+1 : ℝ) * (4 : ℝ)^t := by
      simp [pow_mul]
      norm_num
    _ ≤ (4 : ℝ)^t * (4 : ℝ)^t := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hnat t
    _ = 16^t := by rw [← mul_pow]; norm_num

theorem geometric_tail_bound (n : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1/128) :
    (∑ t : Fin (n+1), if 0 < (t : ℕ) then (16*r)^(t : ℕ) else 0) ≤ (1 : ℝ)/4 := by
  calc
    (∑ t : Fin (n+1), if 0 < (t : ℕ) then (16*r)^(t : ℕ) else 0) ≤
        ∑ t : Fin (n+1), if 0 < (t : ℕ) then (1/8 : ℝ)^(t : ℕ) else 0 := by
      apply Finset.sum_le_sum
      intro t _
      split_ifs
      · exact pow_le_pow_left₀ (by positivity) (by linarith) t.val
      · exact le_rfl
    _ ≤ 1/4 := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, lt_self_iff_false, if_false, Fin.val_succ,
        Nat.zero_lt_succ, if_true, zero_add]
      rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => (1/8 : ℝ)^(t+1)) n]
      simp_rw [pow_succ]
      rw [← Finset.sum_mul]
      have h := geom_sum_mul (1/8 : ℝ) n
      have hn : 0 ≤ (1/8 : ℝ)^n := by positivity
      nlinarith

end TalagrandSelector
