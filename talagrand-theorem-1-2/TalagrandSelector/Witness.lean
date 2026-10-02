import TalagrandSelector.Threshold

open Finset
namespace TalagrandSelector
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

structure WeightSystem (X : Type) [Fintype X] [DecidableEq X] where
  family : Finset (Finset X)
  weight : Finset X → X → ℝ
  nonneg : ∀ H ∈ family, ∀ i, 0 ≤ weight H i
  support : ∀ H ∈ family, ∀ i, i ∉ H → weight H i = 0
  normalized : ∀ H ∈ family, 1 ≤ ∑ i ∈ H, weight H i

namespace WeightSystem
variable (D : WeightSystem X)

def Bad (W : Finset X) : Prop :=
  ∀ H ∈ D.family, (∑ i ∈ W, D.weight H i) < (1 : ℝ) / 2

theorem heavy_subset {H : Finset X} (hH : H ∈ D.family) (W : Finset X) :
    heavy (D.weight H) W ⊆ H := by
  intro i hi
  by_contra hn
  have hw := (Finset.mem_filter.mp hi).2
  rw [D.support H hH i hn] at hw
  exact (not_lt_of_ge (threshold_nonneg _ (D.nonneg H hH) W)) hw

def candidates (W I : Finset X) : Finset (Finset X) :=
  D.family.filter (fun H => heavy (D.weight H) W \ W ⊆ I)

def score (W H : Finset X) : ℕ ×ₗ ℕ :=
  toLex ((heavy (D.weight H) W).card, (heavy (D.weight H) W \ W).card)

theorem candidates_nonempty (W I : Finset X) (hI : I ∈ D.family) :
    (D.candidates W I).Nonempty :=
  ⟨I, Finset.mem_filter.mpr ⟨hI, Finset.sdiff_subset.trans (D.heavy_subset hI W)⟩⟩

def chosen (W I : Finset X) (hI : I ∈ D.family) : Finset X :=
  Classical.choose (Finset.exists_min_image (D.candidates W I) (D.score W)
    (D.candidates_nonempty W I hI))

theorem chosen_spec (W I : Finset X) (hI : I ∈ D.family) :
    D.chosen W I hI ∈ D.candidates W I ∧
    ∀ H ∈ D.candidates W I, D.score W (D.chosen W I hI) ≤ D.score W H :=
  Classical.choose_spec (Finset.exists_min_image (D.candidates W I) (D.score W)
    (D.candidates_nonempty W I hI))

theorem chosen_mem (W I : Finset X) (hI : I ∈ D.family) :
    D.chosen W I hI ∈ D.family :=
  (Finset.mem_filter.mp (D.chosen_spec W I hI).1).1

def witness (W I : Finset X) (hI : I ∈ D.family) : Finset X :=
  heavy (D.weight (D.chosen W I hI)) W

def fragment (W I : Finset X) (hI : I ∈ D.family) : Finset X :=
  D.witness W I hI \ W

theorem fragment_subset (W I : Finset X) (hI : I ∈ D.family) :
    D.fragment W I hI ⊆ I :=
  (Finset.mem_filter.mp (D.chosen_spec W I hI).1).2

theorem fragment_disjoint (W I : Finset X) (hI : I ∈ D.family) :
    Disjoint W (D.fragment W I hI) := Finset.disjoint_sdiff

theorem witness_subset_union (W I : Finset X) (hI : I ∈ D.family) :
    D.witness W I hI ⊆ W ∪ D.fragment W I hI := by
  intro i hi
  by_cases hw : i ∈ W
  · exact Finset.mem_union_left _ hw
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hi, hw⟩)

theorem bad_relative {W H : Finset X} (hbad : D.Bad W) (hH : H ∈ D.family) :
    (∑ i ∈ W, D.weight H i) < (∑ i, D.weight H i) / 2 := by
  have ht : 1 ≤ ∑ i, D.weight H i := (D.normalized H hH).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H)
      (fun i _ _ => D.nonneg H hH i))
  linarith [hbad H hH]

theorem fragment_size (W I : Finset X) (hI : I ∈ D.family) (hbad : D.Bad W) :
    0 < (D.fragment W I hI).card ∧
    (D.witness W I hI).card ≤ 2 * (D.fragment W I hI).card := by
  have hs := heavy_sparse (D.weight (D.chosen W I hI))
    (D.nonneg _ (D.chosen_mem W I hI)) W
    (D.bad_relative hbad (D.chosen_mem W I hI))
  have hc := Finset.card_sdiff_add_card_inter (D.witness W I hI) W
  change 2 * (W ∩ D.witness W I hI).card < (D.witness W I hI).card at hs
  rw [Finset.inter_comm] at hs
  change (D.fragment W I hI).card + (D.witness W I hI ∩ W).card =
    (D.witness W I hI).card at hc
  omega

/-- The recovery property: two entries with the same augmentation, witness
size and fragment size recover the second fragment inside the first witness. -/
theorem fragment_recovery (W Y I J : Finset X) (hI : I ∈ D.family) (hJ : J ∈ D.family)
    (hz : W ∪ D.fragment W I hI = Y ∪ D.fragment Y J hJ)
    (hj : (D.witness W I hI).card = (D.witness Y J hJ).card)
    (ht : (D.fragment W I hI).card = (D.fragment Y J hJ).card) :
    D.witness W I hI \ Y = D.fragment Y J hJ := by
  let H := D.chosen W I hI
  have hH : H ∈ D.family := D.chosen_mem W I hI
  have hY : Y ⊆ W ∪ D.fragment W I hI := by
    rw [hz]
    exact Finset.subset_union_left
  have hcard : Y.card = W.card := by
    have he := congrArg Finset.card hz
    rw [Finset.card_union_of_disjoint (D.fragment_disjoint W I hI),
      Finset.card_union_of_disjoint (D.fragment_disjoint Y J hJ)] at he
    omega
  have heps := threshold_exchange (D.weight H) (D.nonneg H hH)
    W (D.fragment W I hI) Y (D.fragment_disjoint W I hI)
    Finset.sdiff_subset hY hcard
  have hheavy : heavy (D.weight H) Y ⊆ D.witness W I hI :=
    heavy_antitone_threshold heps
  have hcont : D.witness W I hI \ Y ⊆ D.fragment Y J hJ := by
    intro i hi
    have hiZ := D.witness_subset_union W I hI (Finset.mem_sdiff.mp hi).1
    rw [hz] at hiZ
    exact (Finset.mem_union.mp hiZ).resolve_left (Finset.mem_sdiff.mp hi).2
  have hsub : heavy (D.weight H) Y \ Y ⊆ J :=
    (show heavy (D.weight H) Y \ Y ⊆ D.witness W I hI \ Y from
      fun i hi => Finset.mem_sdiff.mpr
        ⟨hheavy (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hi).2⟩).trans
      (hcont.trans (D.fragment_subset Y J hJ))
  have hmin := (D.chosen_spec Y J hJ).2 H (Finset.mem_filter.mpr ⟨hH, hsub⟩)
  have hp := Prod.Lex.toLex_le_toLex'.mp hmin
  change (D.witness Y J hJ).card ≤ (heavy (D.weight H) Y).card ∧
    ((D.witness Y J hJ).card = (heavy (D.weight H) Y).card →
      (D.fragment Y J hJ).card ≤ (heavy (D.weight H) Y \ Y).card) at hp
  have heq : heavy (D.weight H) Y = D.witness W I hI :=
    Finset.eq_of_subset_of_card_le hheavy (hj.trans_le hp.1)
  have hj' : (D.witness Y J hJ).card = (heavy (D.weight H) Y).card := by
    rw [heq, hj]
  have hcount := hp.2 hj'
  rw [heq] at hcount
  exact Finset.eq_of_subset_of_card_le hcont hcount

/-- Distinct fragments in one encoding class inject into the powerset of a
single witness, whose size is at most twice the fragment size. -/
theorem fragment_in_container (W Y I J : Finset X) (hI : I ∈ D.family) (hJ : J ∈ D.family)
    (hz : W ∪ D.fragment W I hI = Y ∪ D.fragment Y J hJ)
    (hj : (D.witness W I hI).card = (D.witness Y J hJ).card)
    (ht : (D.fragment W I hI).card = (D.fragment Y J hJ).card) :
    D.fragment Y J hJ ⊆ D.witness W I hI := by
  rw [← D.fragment_recovery W Y I J hI hJ hz hj ht]
  exact Finset.sdiff_subset

end WeightSystem
end
end TalagrandSelector
