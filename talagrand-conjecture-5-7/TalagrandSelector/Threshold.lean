import Mathlib

/-! Clipped-weight thresholds, following Bednorz--Martynek--Meller,
arXiv:2212.14636v3, Section 3.1. All arguments here are proved. -/

open Finset
namespace TalagrandSelector
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

def clipped (w : X → ℝ) (a : ℝ) (W : Finset X) : ℝ :=
  ∑ i ∈ W, min (w i) a

def balance (w : X → ℝ) (W : Finset X) (a : ℝ) : ℝ :=
  clipped w a W - clipped w a univ / 2

def thresholdSet (w : X → ℝ) (W : Finset X) : Set ℝ :=
  {a | 0 ≤ a ∧ a ≤ ∑ i, w i ∧ 0 ≤ balance w W a}

def threshold (w : X → ℝ) (W : Finset X) : ℝ :=
  sSup (thresholdSet w W)

def heavy (w : X → ℝ) (W : Finset X) : Finset X :=
  univ.filter (fun i => threshold w W < w i)

theorem clipped_zero (w : X → ℝ) (hn : ∀ i, 0 ≤ w i) (W : Finset X) :
    clipped w 0 W = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact min_eq_right (hn i)

theorem threshold_greatest (w : X → ℝ) (hn : ∀ i, 0 ≤ w i)
    (W : Finset X) : IsGreatest (thresholdSet w W) (threshold w W) := by
  have hc : Continuous (balance w W) := by
    unfold balance clipped
    fun_prop
  have hclosed : IsClosed (thresholdSet w W) :=
    isClosed_Ici.inter (isClosed_Iic.inter (isClosed_le continuous_const hc))
  have hne : (thresholdSet w W).Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨le_rfl, Finset.sum_nonneg (fun i _ => hn i), ?_⟩
    simp [balance, clipped_zero w hn]
  have hb : BddAbove (thresholdSet w W) :=
    ⟨∑ i, w i, fun _ ha => ha.2.1⟩
  exact hclosed.isGreatest_csSup hne hb

theorem threshold_nonneg (w : X → ℝ) (hn : ∀ i, 0 ≤ w i) (W : Finset X) :
    0 ≤ threshold w W := (threshold_greatest w hn W).1.1

theorem balance_threshold_nonneg (w : X → ℝ) (hn : ∀ i, 0 ≤ w i)
    (W : Finset X) : 0 ≤ balance w W (threshold w W) :=
  (threshold_greatest w hn W).1.2.2

theorem threshold_lt_total (w : X → ℝ) (hn : ∀ i, 0 ≤ w i)
    (W : Finset X) (hbad : (∑ i ∈ W, w i) < (∑ i, w i) / 2) :
    threshold w W < ∑ i, w i := by
  have hi : ∀ i, w i ≤ ∑ j, w j := fun i =>
    Finset.single_le_sum (fun j _ => hn j) (mem_univ i)
  have hbal : balance w W (∑ i, w i) < 0 := by
    simpa [balance, clipped, min_eq_left (hi _)] using sub_neg.mpr hbad
  have ha := (threshold_greatest w hn W).1
  apply lt_of_le_of_ne ha.2.1
  intro heq
  rw [heq] at ha
  linarith [ha.2.2]

theorem clipped_step (w : X → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hb : ∀ i, a < w i → b ≤ w i) (W : Finset X) :
    clipped w b W = clipped w a W +
      (b - a) * ((W.filter (fun i => a < w i)).card : ℝ) := by
  have heq : ∀ i, min (w i) b = min (w i) a + if a < w i then b - a else 0 := by
    intro i
    by_cases hi : a < w i
    · rw [if_pos hi, min_eq_right (hb i hi), min_eq_right hi.le]
      ring
    · rw [if_neg hi, min_eq_left (le_of_not_gt hi),
        min_eq_left ((le_of_not_gt hi).trans hab), add_zero]
  simp only [clipped, heq, Finset.sum_add_distrib]
  simp [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_comm]
  <;> ring

/-- The threshold leaves fewer than half of the heavy coordinates in a bad sample. -/
theorem heavy_sparse (w : X → ℝ) (hn : ∀ i, 0 ≤ w i)
    (W : Finset X) (hbad : (∑ i ∈ W, w i) < (∑ i, w i) / 2) :
    2 * (W ∩ heavy w W).card < (heavy w W).card := by
  classical
  let a := threshold w W
  let B := ∑ i, w i
  let A := insert B ((heavy w W).image w)
  have hA : A.Nonempty := Finset.insert_nonempty _ _
  let b := A.min' hA
  have hab : a < b := by
    have hm : b ∈ A := Finset.min'_mem A hA
    rcases Finset.mem_insert.mp hm with he | he
    · exact he ▸ threshold_lt_total w hn W hbad
    · obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp he
      rw [← heq]
      exact (Finset.mem_filter.mp hi).2
  have hbB : b ≤ B := Finset.min'_le A B (Finset.mem_insert_self _ _)
  have hbw : ∀ i, a < w i → b ≤ w i := by
    intro i hi
    apply Finset.min'_le A
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨i, Finset.mem_filter.mpr ⟨mem_univ _, hi⟩, rfl⟩)
  have hnegative : balance w W b < 0 := by
    by_contra h
    have hmem : b ∈ thresholdSet w W :=
      ⟨(threshold_nonneg w hn W).trans hab.le, hbB, le_of_not_gt h⟩
    exact (not_le_of_gt hab) ((threshold_greatest w hn W).2 hmem)
  have hW : W.filter (fun i => a < w i) = W ∩ heavy w W := by
    ext i
    simp [heavy, a]
  have hu : univ.filter (fun i => a < w i) = heavy w W := rfl
  have hstepW := clipped_step w a b hab.le hbw W
  have hstepU := clipped_step w a b hab.le hbw univ
  rw [hW] at hstepW
  rw [hu] at hstepU
  have hpositive := balance_threshold_nonneg w hn W
  change 0 ≤ clipped w a W - clipped w a univ / 2 at hpositive
  unfold balance at hnegative
  rw [hstepW, hstepU] at hnegative
  have hcard : (2 : ℝ) * ((W ∩ heavy w W).card : ℝ) < (heavy w W).card := by
    by_contra hc
    have hm : 0 ≤ (b-a) *
        (((W ∩ heavy w W).card : ℝ) - (heavy w W).card / 2) :=
      mul_nonneg (sub_nonneg.mpr hab.le) (by linarith)
    nlinarith
  exact_mod_cast hcard

/-- Removing a fixed number of coordinates from Z loses at most that number
times the clipping level. The original removed coordinates all have that level. -/
theorem clipped_exchange (w : X → ℝ) (a : ℝ) (W T Y : Finset X)
    (hd : Disjoint W T) (hT : ∀ i ∈ T, a ≤ w i)
    (hY : Y ⊆ W ∪ T) (hcard : Y.card = W.card) :
    clipped w a W ≤ clipped w a Y := by
  have hclipT : clipped w a T = (T.card : ℝ) * a := by
    simp only [clipped]
    calc
      (∑ i ∈ T, min (w i) a) = ∑ i ∈ T, a := by
        apply Finset.sum_congr rfl
        intro i hi
        exact min_eq_right (hT i hi)
      _ = _ := by simp
  have hsplit : clipped w a (W ∪ T) = clipped w a W + clipped w a T :=
    Finset.sum_union hd
  have hsplitY : clipped w a (W ∪ T) = clipped w a Y +
      clipped w a ((W ∪ T) \ Y) := by
    simpa [clipped, add_comm] using
      (Finset.sum_sdiff (f := fun i => min (w i) a) hY).symm
  have hc : ((W ∪ T) \ Y).card = T.card := by
    rw [Finset.card_sdiff_of_subset hY, Finset.card_union_of_disjoint hd, hcard]
    omega
  have hle : clipped w a ((W ∪ T) \ Y) ≤ (T.card : ℝ) * a := by
    calc
      clipped w a ((W ∪ T) \ Y) ≤ ∑ _i ∈ (W ∪ T) \ Y, a :=
        Finset.sum_le_sum (fun i _ => min_le_right _ _)
      _ = _ := by simp [hc]
  rw [hclipT] at hsplit
  linarith

/-- Equal-size samples with the same augmented set compare their clipping thresholds. -/
theorem threshold_exchange (w : X → ℝ) (hn : ∀ i, 0 ≤ w i)
    (W T Y : Finset X) (hd : Disjoint W T)
    (hT : T ⊆ heavy w W) (hY : Y ⊆ W ∪ T) (hcard : Y.card = W.card) :
    threshold w W ≤ threshold w Y := by
  apply (threshold_greatest w hn Y).2
  have hmem := (threshold_greatest w hn W).1
  refine ⟨hmem.1, hmem.2.1, ?_⟩
  have hex := clipped_exchange w (threshold w W) W T Y hd
    (fun i hi => ((Finset.mem_filter.mp (hT hi)).2).le) hY hcard
  have hm := hmem.2.2
  change 0 ≤ clipped w (threshold w W) W - clipped w (threshold w W) univ / 2 at hm
  unfold balance
  linarith

theorem heavy_antitone_threshold {w : X → ℝ} {W Y : Finset X}
    (h : threshold w W ≤ threshold w Y) : heavy w Y ⊆ heavy w W := by
  intro i hi
  exact Finset.mem_filter.mpr ⟨mem_univ _, h.trans_lt (Finset.mem_filter.mp hi).2⟩

end
end TalagrandSelector
