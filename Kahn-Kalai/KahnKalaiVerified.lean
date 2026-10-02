/-
Kahn--Kalai theorem: consolidated Lean 4.32.0 / mathlib v4.32.0 source.

The full theorem is proved via Tran--Vu's argument. Several original
Park--Pham minimum-fragment and deterministic-iteration steps are also
formalized. This is not a line-by-line formalization of the entire supplied
Park--Pham randomized proof. See the companion README for the exact scope.

Upstream theorem code: Dan Clemens Posch, https://github.com/dcposch/kahn-kalai-lean
Commit: 641aa75f8e873d31442f2f7c317b2e7582a26d94
Modifications in this single-file edition: imports have been consolidated;
Paper.lean and axiom reports have been added. All upstream proof bodies and
copyright notices are retained. Apache-2.0 license text is included below.

Run in a mathlib v4.32.0 environment:
  lake env lean KahnKalaiVerified.lean

Main declarations:
  ParkPhamPaper.theorem_1_1_explicit
  ParkPhamPaper.theorem_1_1_increasing
  ParkPhamPaper.theorem_1_1
-/
import Mathlib


/- ===== Source module: KahnKalai/Basic.lean ===== -/

/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch
-/

/-!
Foundational lemmas for the Tran–Vu covering argument: upset calculus,
cover cost as an attained infimum, and Fact 2.1 (level fractions of an
upset are nondecreasing).
-/

open Finset

namespace KahnKalai

variable {α : Type*} [DecidableEq α] [Fintype α]

def generate (F : Finset (Finset α)) : Finset (Finset α) :=
  univ.filter fun T => ∃ S ∈ F, S ⊆ T

def Covers (G F : Finset (Finset α)) : Prop := F ⊆ generate G

def expectation (p : ℝ) (G : Finset (Finset α)) : ℝ :=
  ∑ S ∈ G, p ^ S.card

noncomputable def coverCost (p : ℝ) (H : Finset (Finset α)) : ℝ :=
  sInf ((fun G : Finset (Finset α) => expectation p G) '' {G | Covers G H})

def measure (p : ℝ) (S : Finset α) : ℝ :=
  p ^ S.card * (1 - p) ^ (Fintype.card α - S.card)

def measureFamily (p : ℝ) (F : Finset (Finset α)) : ℝ :=
  ∑ S ∈ F, measure p S

noncomputable def threshold (F : Finset (Finset α)) : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc 0 1 ∧ 1 / 2 ≤ measureFamily p (generate F)}

noncomputable def expectationThreshold (F : Finset (Finset α)) : ℝ :=
  sSup {p : ℝ | p ∈ Set.Icc 0 1 ∧ coverCost p F ≤ 1 / 2}

def IsBounded (F : Finset (Finset α)) (ℓ : ℕ) : Prop :=
  ∀ S ∈ F, S.card ≤ ℓ

def coveringConstant : ℝ := 1000

noncomputable def coveringLevel (p : ℝ) (N ℓ : ℕ) : ℕ :=
  ⌊coveringConstant * p * N * Real.logb 2 (ℓ + 1 : ℝ)⌋₊

lemma mem_generate {F : Finset (Finset α)} {T : Finset α} :
    T ∈ generate F ↔ ∃ S ∈ F, S ⊆ T := by
  simp [generate]

lemma subset_mem_generate {F : Finset (Finset α)} {S T : Finset α}
    (hST : S ⊆ T) (hS : S ∈ generate F) : T ∈ generate F := by
  rw [mem_generate] at hS ⊢
  obtain ⟨U, hU, hUS⟩ := hS
  exact ⟨U, hU, hUS.trans hST⟩

lemma generate_mono {F G : Finset (Finset α)} (h : F ⊆ G) :
    generate F ⊆ generate G := by
  intro T hT
  rw [mem_generate] at hT ⊢
  obtain ⟨S, hS, hST⟩ := hT
  exact ⟨S, h hS, hST⟩

lemma covers_self (H : Finset (Finset α)) : Covers H H := by
  intro T hT
  exact mem_generate.mpr ⟨T, hT, Subset.rfl⟩

omit [DecidableEq α] [Fintype α] in
lemma expectation_nonneg {p : ℝ} (hp : 0 ≤ p) (G : Finset (Finset α)) :
    0 ≤ expectation p G :=
  sum_nonneg fun _ _ => pow_nonneg hp _

lemma coverCost_nonneg {p : ℝ} (hp : 0 ≤ p) (H : Finset (Finset α)) :
    0 ≤ coverCost p H := by
  refine Real.sInf_nonneg fun x hx => ?_
  obtain ⟨G, _, rfl⟩ := hx
  exact expectation_nonneg hp G

lemma coverCost_le_expectation {p : ℝ} (hp : 0 ≤ p) {G H : Finset (Finset α)}
    (h : Covers G H) : coverCost p H ≤ expectation p G := by
  refine csInf_le ?_ ⟨G, h, rfl⟩
  exact ⟨0, fun x hx => by
    obtain ⟨G', _, rfl⟩ := hx
    exact expectation_nonneg hp G'⟩

/-- Fact 2.1, integer form: an upset’s level sizes satisfy the shadow inequality. -/
lemma generate_card_mono (F : Finset (Finset α)) (t : ℕ)
    (_ht : t < Fintype.card α) :
    #((generate F).filter (fun S => S.card = t)) * (Fintype.card α - t)
      ≤ #((generate F).filter (fun S => S.card = t + 1)) * (t + 1) := by
  classical
  set N := Fintype.card α
  set Ft := (generate F).filter (fun S => S.card = t)
  set Ft1 := (generate F).filter (fun S => S.card = t + 1)
  let Src := (A : ↥Ft) × ↥(univ \ A.1)
  let Tgt := (B : ↥Ft1) × ↥B.1
  have hx_not_mem : ∀ (A : ↥Ft) (x : ↥(univ \ A.1)), (x : α) ∉ (A : Finset α) := by
    intro A x
    exact (mem_sdiff.mp x.2).2
  let f : Src → Tgt := fun ⟨A, x⟩ =>
    ⟨⟨insert (x : α) (A : Finset α), by
        have hA := A.2
        have hAgen : (A : Finset α) ∈ generate F := (mem_filter.mp hA).1
        have hAcard : (A : Finset α).card = t := (mem_filter.mp hA).2
        refine mem_filter.mpr ⟨subset_mem_generate (subset_insert _ _) hAgen, ?_⟩
        rw [card_insert_of_notMem (hx_not_mem A x), hAcard]⟩,
      ⟨x, mem_insert_self _ _⟩⟩
  have hf : Function.Injective f := by
    intro a b h
    rcases a with ⟨A, x⟩
    rcases b with ⟨A', x'⟩
    have hx : (x : α) = (x' : α) := congrArg (fun z : Tgt => (z.2 : α)) h
    have hB :
        insert (x : α) (A : Finset α) = insert (x' : α) (A' : Finset α) :=
      congrArg (fun z : Tgt => (z.1 : Finset α)) h
    have hxA' : (x : α) ∉ (A' : Finset α) := by
      simpa [hx] using hx_not_mem A' x'
    have hB' : insert (x : α) (A : Finset α) = insert (x : α) (A' : Finset α) := by
      simpa [hx] using hB
    have hAeq : (A : Finset α) = (A' : Finset α) :=
      (erase_insert (hx_not_mem A x)).symm.trans <|
        (congrArg (fun s : Finset α => s.erase (x : α)) hB').trans
          (erase_insert hxA')
    have hA' : A = A' := Subtype.ext hAeq
    subst hA'
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext hx))
  have hSrc : Fintype.card Src = #Ft * (N - t) := by
    dsimp [Src]
    rw [Fintype.card_sigma]
    have hA : ∀ A : ↥Ft, Fintype.card ↥(univ \ A.1) = N - t := by
      intro A
      rw [Fintype.card_coe, card_sdiff_of_subset (subset_univ _), card_univ]
      have : A.1.card = t := (mem_filter.mp A.2).2
      rw [this]
    simp_rw [hA]
    simp [sum_const, nsmul_eq_mul, Fintype.card_coe, Nat.mul_comm]
  have hTgt : Fintype.card Tgt = #Ft1 * (t + 1) := by
    dsimp [Tgt]
    rw [Fintype.card_sigma]
    have hB : ∀ B : ↥Ft1, Fintype.card ↥B.1 = t + 1 := by
      intro B
      have : B.1.card = t + 1 := (mem_filter.mp B.2).2
      simpa [Fintype.card_coe] using this
    simp_rw [hB]
    simp [sum_const, nsmul_eq_mul, Fintype.card_coe, Nat.mul_comm]
  have : Fintype.card Src ≤ Fintype.card Tgt :=
    Fintype.card_le_of_injective f hf
  calc
    #Ft * (N - t) = Fintype.card Src := hSrc.symm
    _ ≤ Fintype.card Tgt := this
    _ = #Ft1 * (t + 1) := hTgt

/-- Fact 2.1: the fraction of an upset on level `t` is nondecreasing in `t`. -/
lemma generate_level_frac_mono (F : Finset (Finset α)) (t : ℕ)
    (ht : t < Fintype.card α) :
    (((generate F).filter (fun S => S.card = t)).card : ℝ) /
        ((Fintype.card α).choose t : ℝ) ≤
      (((generate F).filter (fun S => S.card = t + 1)).card : ℝ) /
        ((Fintype.card α).choose (t + 1) : ℝ) := by
  set N := Fintype.card α
  set a := #((generate F).filter (fun S => S.card = t))
  set b := #((generate F).filter (fun S => S.card = t + 1))
  have hch0 : 0 < (N.choose t : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos ht.le)
  have hch1 : 0 < (N.choose (t + 1) : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (Nat.succ_le_of_lt ht))
  have hmul : a * N.choose (t + 1) ≤ b * N.choose t := by
    have h0 : a * (N - t) ≤ b * (t + 1) := generate_card_mono F t ht
    have hC : N.choose (t + 1) * (t + 1) = N.choose t * (N - t) :=
      Nat.choose_succ_right_eq N t
    have h5 : a * (N.choose (t + 1) * (t + 1)) ≤ b * (N.choose t * (t + 1)) := by
      calc
        a * (N.choose (t + 1) * (t + 1))
            = a * (N.choose t * (N - t)) := by rw [hC]
        _ = N.choose t * (a * (N - t)) := by ring
        _ ≤ N.choose t * (b * (t + 1)) := Nat.mul_le_mul_left _ h0
        _ = b * (N.choose t * (t + 1)) := by ring
    have h6 : a * N.choose (t + 1) * (t + 1) ≤ b * N.choose t * (t + 1) := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h5
    exact Nat.le_of_mul_le_mul_right h6 (Nat.succ_pos t)
  rw [div_le_div_iff₀ hch0 hch1]
  exact_mod_cast hmul

end KahnKalai

/- ===== Source module: KahnKalai/Cost.lean ===== -/

/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch
-/

/-!
Cover-cost calculus for Tran–Vu: the infimum is a minimum, subadditivity,
empty-family / empty-set evaluation, and `⊆`-minimals.
-/

open Finset

namespace KahnKalai

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α] [Fintype α]

noncomputable section

lemma generate_empty : generate (∅ : Finset (Finset α)) = ∅ := by
  ext T
  simp [mem_generate]

lemma generate_eq_univ_of_empty_mem {F : Finset (Finset α)} (h : ∅ ∈ F) :
    generate F = univ := by
  ext T
  simp [mem_generate]
  exact ⟨∅, h, empty_subset T⟩

lemma expectation_empty (p : ℝ) : expectation p (∅ : Finset (Finset α)) = 0 := by
  simp [expectation]

lemma expectation_singleton_empty (p : ℝ) :
    expectation p ({∅} : Finset (Finset α)) = 1 := by
  simp [expectation]

lemma expectation_mono {p : ℝ} (hp : 0 ≤ p) {G₁ G₂ : Finset (Finset α)}
    (h : G₁ ⊆ G₂) : expectation p G₁ ≤ expectation p G₂ :=
  sum_le_sum_of_subset_of_nonneg h fun _ _ _ => pow_nonneg hp _

lemma expectation_union_le {p : ℝ} (hp : 0 ≤ p) (G₁ G₂ : Finset (Finset α)) :
    expectation p (G₁ ∪ G₂) ≤ expectation p G₁ + expectation p G₂ := by
  simp only [expectation]
  have h := sum_union_inter (f := fun S : Finset α => p ^ S.card) (s₁ := G₁) (s₂ := G₂)
  have : 0 ≤ ∑ S ∈ G₁ ∩ G₂, p ^ S.card := sum_nonneg fun _ _ => pow_nonneg hp _
  linarith

lemma covers_empty (G : Finset (Finset α)) : Covers G (∅ : Finset (Finset α)) :=
  empty_subset _

lemma covers_union {G H₁ H₂ : Finset (Finset α)} (h₁ : Covers G H₁) (h₂ : Covers G H₂) :
    Covers G (H₁ ∪ H₂) :=
  union_subset h₁ h₂

lemma covers_union_covers {G₁ G₂ H₁ H₂ : Finset (Finset α)}
    (h₁ : Covers G₁ H₁) (h₂ : Covers G₂ H₂) : Covers (G₁ ∪ G₂) (H₁ ∪ H₂) := by
  intro T hT
  rw [mem_union] at hT
  rcases hT with hT | hT
  · exact generate_mono subset_union_left (h₁ hT)
  · exact generate_mono subset_union_right (h₂ hT)

lemma covers_of_subset {G H₁ H₂ : Finset (Finset α)} (hH : H₁ ⊆ H₂) (h : Covers G H₂) :
    Covers G H₁ :=
  hH.trans h

lemma covers_singleton_empty (H : Finset (Finset α)) :
    Covers ({∅} : Finset (Finset α)) H := by
  intro T _
  exact mem_generate.mpr ⟨∅, mem_singleton_self _, empty_subset T⟩

lemma coverCost_le_one {p : ℝ} (hp : 0 ≤ p) (H : Finset (Finset α)) :
    coverCost p H ≤ 1 := by
  simpa [expectation_singleton_empty] using
    coverCost_le_expectation hp (covers_singleton_empty (H := H))

lemma covers_set_nonempty (p : ℝ) (H : Finset (Finset α)) :
    ((fun G : Finset (Finset α) => expectation p G) '' {G | Covers G H}).Nonempty :=
  ⟨expectation p H, ⟨H, covers_self H, rfl⟩⟩

lemma covers_set_finite (p : ℝ) (H : Finset (Finset α)) :
    ((fun G : Finset (Finset α) => expectation p G) '' {G | Covers G H}).Finite :=
  (Set.toFinite _).image _

lemma exists_cover_eq_coverCost (p : ℝ) (H : Finset (Finset α)) :
    ∃ G, Covers G H ∧ expectation p G = coverCost p H := by
  have hne := covers_set_nonempty p H
  have hf := covers_set_finite p H
  have hmem := hne.csInf_mem hf
  obtain ⟨G, hG, hEq⟩ := hmem
  exact ⟨G, hG, hEq⟩

lemma coverCost_empty {p : ℝ} (hp : 0 ≤ p) :
    coverCost p (∅ : Finset (Finset α)) = 0 := by
  refine le_antisymm ?_ (coverCost_nonneg hp _)
  simpa [expectation_empty] using
    coverCost_le_expectation hp (covers_empty (∅ : Finset (Finset α)))

lemma coverCost_eq_zero_of_empty {p : ℝ} (hp : 0 ≤ p) {H : Finset (Finset α)}
    (hH : H = ∅) : coverCost p H = 0 := by
  subst hH
  exact coverCost_empty hp

lemma coverCost_pos_imp_nonempty {p : ℝ} (hp : 0 ≤ p) {H : Finset (Finset α)}
    (h : 0 < coverCost p H) : H.Nonempty := by
  rw [nonempty_iff_ne_empty]
  intro hH
  exact h.ne' (coverCost_eq_zero_of_empty hp hH)

lemma coverCost_of_mem_empty {p : ℝ} (hp : 0 ≤ p) {H : Finset (Finset α)}
    (h : ∅ ∈ H) : coverCost p H = 1 := by
  refine le_antisymm (coverCost_le_one hp H) ?_
  obtain ⟨G, hG, hGe⟩ := exists_cover_eq_coverCost p H
  have hempty : ∅ ∈ generate G := hG h
  obtain ⟨S, hS, hSempty⟩ := mem_generate.mp hempty
  have hS' : S = ∅ := subset_empty.mp hSempty
  subst hS'
  have : (1 : ℝ) ≤ expectation p G := by
    have := single_le_sum (f := fun T : Finset α => p ^ T.card)
      (fun T _ => pow_nonneg hp _) hS
    simpa [expectation] using this
  exact this.trans_eq hGe

lemma coverCost_mono {p : ℝ} (hp : 0 ≤ p) {H₁ H₂ : Finset (Finset α)}
    (h : H₁ ⊆ H₂) : coverCost p H₁ ≤ coverCost p H₂ := by
  obtain ⟨G, hG, hGe⟩ := exists_cover_eq_coverCost p H₂
  have : coverCost p H₁ ≤ expectation p G :=
    coverCost_le_expectation hp (covers_of_subset h hG)
  exact this.trans_eq hGe

lemma coverCost_union_le {p : ℝ} (hp : 0 ≤ p) (H₁ H₂ : Finset (Finset α)) :
    coverCost p (H₁ ∪ H₂) ≤ coverCost p H₁ + coverCost p H₂ := by
  obtain ⟨G₁, hG₁, hE₁⟩ := exists_cover_eq_coverCost p H₁
  obtain ⟨G₂, hG₂, hE₂⟩ := exists_cover_eq_coverCost p H₂
  have hcov : Covers (G₁ ∪ G₂) (H₁ ∪ H₂) := covers_union_covers hG₁ hG₂
  have : coverCost p (H₁ ∪ H₂) ≤ expectation p (G₁ ∪ G₂) :=
    coverCost_le_expectation hp hcov
  have hsum := expectation_union_le hp G₁ G₂
  linarith

lemma coverCost_sdiff_ge {p : ℝ} (hp : 0 ≤ p) (H₁ H₂ : Finset (Finset α)) :
    coverCost p H₁ - coverCost p H₂ ≤ coverCost p (H₁ \ H₂) := by
  have h := coverCost_union_le hp (H₁ \ H₂) H₂
  rw [sdiff_union_self_eq_union] at h
  have hmono : coverCost p H₁ ≤ coverCost p (H₁ ∪ H₂) :=
    coverCost_mono hp subset_union_left
  linarith

lemma coverCost_union_ge_sub {p : ℝ} (hp : 0 ≤ p) (A B : Finset (Finset α)) :
    coverCost p A - coverCost p B ≤ coverCost p (A ∪ B) - coverCost p B := by
  have := coverCost_mono hp (subset_union_left (s₁ := A) (s₂ := B))
  linarith

/-- Subadditivity rearranged: `f(A) ≥ f(A ∪ B) - f(B)`. -/
lemma coverCost_ge_union_sub {p : ℝ} (hp : 0 ≤ p) (A B : Finset (Finset α)) :
    coverCost p (A ∪ B) - coverCost p B ≤ coverCost p A := by
  have := coverCost_union_le hp A B
  linarith

def minimals (F : Finset (Finset α)) : Finset (Finset α) :=
  F.filter fun T => ∀ U ∈ F, U ⊆ T → U = T

lemma minimals_subset (F : Finset (Finset α)) : minimals F ⊆ F :=
  filter_subset _ _

lemma mem_minimals {F : Finset (Finset α)} {T : Finset α} :
    T ∈ minimals F ↔ T ∈ F ∧ ∀ U ∈ F, U ⊆ T → U = T :=
  mem_filter

lemma exists_minimal_subset {F : Finset (Finset α)} {S : Finset α} (hS : S ∈ F) :
    ∃ T ∈ minimals F, T ⊆ S := by
  classical
  let C := F.filter (fun U => U ⊆ S)
  have hC : C.Nonempty := ⟨S, mem_filter.mpr ⟨hS, Subset.rfl⟩⟩
  obtain ⟨T, hT, hTmin⟩ := C.exists_min_image (fun U => U.card) hC
  have hTF : T ∈ F := (mem_filter.mp hT).1
  have hTS : T ⊆ S := (mem_filter.mp hT).2
  refine ⟨T, mem_filter.mpr ⟨hTF, fun U hU hUT => ?_⟩, hTS⟩
  have hUC : U ∈ C := mem_filter.mpr ⟨hU, hUT.trans hTS⟩
  have hcard : T.card ≤ U.card := hTmin U hUC
  exact eq_of_subset_of_card_le hUT (by simpa using hcard)

lemma covers_minimals (F : Finset (Finset α)) : Covers (minimals F) F := by
  intro S hS
  obtain ⟨T, hT, hTS⟩ := exists_minimal_subset hS
  exact mem_generate.mpr ⟨T, hT, hTS⟩

lemma covers_of_covers_minimals {G F : Finset (Finset α)}
    (h : Covers G (minimals F)) : Covers G F := by
  intro S hS
  obtain ⟨T, hT, hTS⟩ := exists_minimal_subset hS
  obtain ⟨U, hU, hUT⟩ := mem_generate.mp (h hT)
  exact mem_generate.mpr ⟨U, hU, hUT.trans hTS⟩

lemma coverCost_minimals {p : ℝ} (hp : 0 ≤ p) (F : Finset (Finset α)) :
    coverCost p (minimals F) = coverCost p F := by
  apply le_antisymm
  · exact coverCost_mono hp (minimals_subset F)
  · obtain ⟨G, hG, hGe⟩ := exists_cover_eq_coverCost p (minimals F)
    have : coverCost p F ≤ expectation p G :=
      coverCost_le_expectation hp (covers_of_covers_minimals hG)
    exact this.trans_eq hGe

def restrictFamily (H : Finset (Finset α)) (W : Finset α) : Finset (Finset α) :=
  H.image fun S => S \ W

lemma mem_restrictFamily {H : Finset (Finset α)} {W T : Finset α} :
    T ∈ restrictFamily H W ↔ ∃ S ∈ H, S \ W = T :=
  mem_image

lemma restrictFamily_disjoint {H : Finset (Finset α)} {W T : Finset α}
    (h : T ∈ restrictFamily H W) : Disjoint T W := by
  obtain ⟨S, _, rfl⟩ := mem_restrictFamily.mp h
  exact disjoint_sdiff_self_left

lemma restrictFamily_subset_sdiff {H : Finset (Finset α)} {W T : Finset α}
    (h : T ∈ restrictFamily H W) : T ⊆ univ \ W := by
  intro x hx
  exact mem_sdiff.mpr ⟨mem_univ x, disjoint_left.mp (restrictFamily_disjoint h) hx⟩

lemma covers_restrict_of_covers {G H : Finset (Finset α)} {W : Finset α}
    (h : Covers G (restrictFamily H W)) : Covers G H := by
  intro S hS
  have hSW : S \ W ∈ restrictFamily H W := mem_image.mpr ⟨S, hS, rfl⟩
  obtain ⟨T, hT, hTS⟩ := mem_generate.mp (h hSW)
  exact mem_generate.mpr ⟨T, hT, hTS.trans sdiff_subset⟩

lemma coverCost_le_restrict {p : ℝ} (hp : 0 ≤ p) (H : Finset (Finset α)) (W : Finset α) :
    coverCost p H ≤ coverCost p (restrictFamily H W) := by
  obtain ⟨G, hG, hGe⟩ := exists_cover_eq_coverCost p (restrictFamily H W)
  have : coverCost p H ≤ expectation p G :=
    coverCost_le_expectation hp (covers_restrict_of_covers hG)
  exact this.trans_eq hGe

lemma coverCost_le_minimals_restrict {p : ℝ} (hp : 0 ≤ p)
    (H : Finset (Finset α)) (W : Finset α) :
    coverCost p H ≤ coverCost p (minimals (restrictFamily H W)) := by
  rw [coverCost_minimals hp]
  exact coverCost_le_restrict hp H W

/-- Members of `F` with size strictly larger than `0.9 ℓ`. -/
def largeMinimals (H : Finset (Finset α)) (W : Finset α) (ℓ : ℕ) : Finset (Finset α) :=
  (minimals (restrictFamily H W)).filter fun T => ⌊((9 : ℝ) / 10) * ℓ⌋₊ + 1 ≤ T.card

def smallMinimals (H : Finset (Finset α)) (W : Finset α) (ℓ : ℕ) : Finset (Finset α) :=
  (minimals (restrictFamily H W)).filter fun T => T.card ≤ ⌊((9 : ℝ) / 10) * ℓ⌋₊

lemma largeMinimals_union_small (H : Finset (Finset α)) (W : Finset α) (ℓ : ℕ) :
    largeMinimals H W ℓ ∪ smallMinimals H W ℓ = minimals (restrictFamily H W) := by
  classical
  ext T
  simp only [largeMinimals, smallMinimals, mem_union, mem_filter]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro h
    rcases Nat.lt_or_ge T.card (⌊((9 : ℝ) / 10) * ℓ⌋₊ + 1) with hlt | hle
    · exact Or.inr ⟨h, Nat.lt_succ_iff.mp hlt⟩
    · exact Or.inl ⟨h, hle⟩

lemma largeMinimals_disjoint_small (H : Finset (Finset α)) (W : Finset α) (ℓ : ℕ) :
    Disjoint (largeMinimals H W ℓ) (smallMinimals H W ℓ) := by
  classical
  refine disjoint_left.mpr ?_
  intro T hL hS
  have h1 := (mem_filter.mp hL).2
  have h2 := (mem_filter.mp hS).2
  exact (not_le_of_gt (Nat.lt_succ_iff.mpr h2)) h1

lemma coverCost_small_ge {p : ℝ} (hp : 0 ≤ p) (H : Finset (Finset α))
    (W : Finset α) (ℓ : ℕ) :
    coverCost p (minimals (restrictFamily H W)) - coverCost p (largeMinimals H W ℓ)
      ≤ coverCost p (smallMinimals H W ℓ) := by
  have hU := largeMinimals_union_small H W ℓ
  have h := coverCost_union_le hp (smallMinimals H W ℓ) (largeMinimals H W ℓ)
  rw [union_comm, hU] at h
  linarith

lemma IsBounded.image_sdiff {H : Finset (Finset α)} {ℓ : ℕ} (hb : IsBounded H ℓ)
    (W : Finset α) : IsBounded (restrictFamily H W) ℓ := by
  intro T hT
  obtain ⟨S, hS, rfl⟩ := mem_restrictFamily.mp hT
  exact (card_le_card sdiff_subset).trans (hb S hS)

lemma IsBounded.minimals {F : Finset (Finset α)} {ℓ : ℕ} (hb : IsBounded F ℓ) :
    IsBounded (minimals F) ℓ :=
  fun T hT => hb T (minimals_subset F hT)

lemma IsBounded.largeMinimals {H : Finset (Finset α)} {ℓ : ℕ} (hb : IsBounded H ℓ)
    (W : Finset α) : IsBounded (largeMinimals H W ℓ) ℓ :=
  fun T hT =>
    (hb.image_sdiff W).minimals T (filter_subset _ _ hT)

lemma IsBounded.smallMinimals {H : Finset (Finset α)} {W : Finset α} {ℓ ℓ₁ : ℕ}
    (hℓ₁ : ℓ₁ = ⌊((9 : ℝ) / 10) * ℓ⌋₊) :
    IsBounded (smallMinimals H W ℓ) ℓ₁ := by
  intro T hT
  exact hℓ₁ ▸ (mem_filter.mp hT).2

lemma largeMinimals_card_gt {H : Finset (Finset α)} {W T : Finset α} {ℓ : ℕ}
    (h : T ∈ largeMinimals H W ℓ) : ⌊((9 : ℝ) / 10) * ℓ⌋₊ + 1 ≤ T.card :=
  (mem_filter.mp h).2

lemma largeMinimals_mem_minimals {H : Finset (Finset α)} {W T : Finset α} {ℓ : ℕ}
    (h : T ∈ largeMinimals H W ℓ) : T ∈ minimals (restrictFamily H W) :=
  (mem_filter.mp h).1

lemma filter_card_eq_powersetCard (n : ℕ) :
    univ.filter (fun S : Finset α => S.card = n) = powersetCard n univ := by
  ext S
  simp [mem_powersetCard, subset_univ]

lemma card_level (n : ℕ) :
    #{S : Finset α | S.card = n} = (Fintype.card α).choose n := by
  rw [filter_card_eq_powersetCard, card_powersetCard, card_univ]

lemma generate_level_frac_le (F : Finset (Finset α)) {s t : ℕ}
    (hst : s ≤ t) (ht : t ≤ Fintype.card α) :
    (((generate F).filter (fun S => S.card = s)).card : ℝ) /
        ((Fintype.card α).choose s : ℝ) ≤
      (((generate F).filter (fun S => S.card = t)).card : ℝ) /
        ((Fintype.card α).choose t : ℝ) := by
  revert ht
  induction t, hst using Nat.le_induction with
  | base => intro; exact le_rfl
  | succ n hn ih =>
    intro ht
    have hnN : n < Fintype.card α := Nat.lt_of_succ_le ht
    exact (ih hnN.le).trans (generate_level_frac_mono F n hnN)

lemma expectation_mono_p {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q)
    (G : Finset (Finset α)) :
    expectation p G ≤ expectation q G :=
  sum_le_sum fun S _ => pow_le_pow_left₀ hp hpq S.card

lemma coverCost_mono_p {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q)
    (H : Finset (Finset α)) :
    coverCost p H ≤ coverCost q H := by
  obtain ⟨G, hG, hGe⟩ := exists_cover_eq_coverCost q H
  have : coverCost p H ≤ expectation p G := coverCost_le_expectation hp hG
  exact this.trans ((expectation_mono_p hp hpq G).trans_eq hGe)

lemma expectation_zero (G : Finset (Finset α)) :
    expectation 0 G = if ∅ ∈ G then 1 else 0 := by
  classical
  have hterm : ∀ S ∈ G, (0 : ℝ) ^ S.card = if S = ∅ then 1 else 0 := by
    intro S _
    by_cases hS : S = ∅
    · simp [hS]
    · have hc : 0 < S.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hS)
      rw [zero_pow hc.ne', if_neg hS]
  simp only [expectation]
  rw [sum_congr rfl hterm, sum_ite_eq']

lemma coverCost_zero_of_not_mem_empty {H : Finset (Finset α)} (h : ∅ ∉ H) :
    coverCost 0 H = 0 := by
  refine le_antisymm ?_ (coverCost_nonneg le_rfl H)
  have : expectation 0 H = 0 := by simp [expectation_zero, h]
  simpa [this] using coverCost_le_expectation (le_rfl : (0 : ℝ) ≤ 0) (covers_self H)

end

end KahnKalai

/- ===== Source module: KahnKalai/Numeric.lean ===== -/

/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch
-/

/-!
Numeric inequalities for Tran–Vu’s covering induction (`L = 1000`).
-/

namespace KahnKalai

open Nat Finset

/-- Least integer strictly larger than `0.9 ℓ`. -/
noncomputable def kmin (ℓ : ℕ) : ℕ := ⌊((9 : ℝ) / 10) * ℓ⌋₊ + 1

lemma kmin_pos (ℓ : ℕ) : 1 ≤ kmin ℓ := Nat.succ_le_succ (Nat.zero_le _)

lemma kmin_gt (ℓ : ℕ) : ((9 : ℝ) / 10) * ℓ < kmin ℓ := by
  unfold kmin
  have := Nat.lt_floor_add_one (((9 : ℝ) / 10) * (ℓ : ℝ))
  simpa [add_comm] using this

lemma kmin_le_add_one (ℓ : ℕ) : (kmin ℓ : ℝ) ≤ ((9 : ℝ) / 10) * ℓ + 1 := by
  unfold kmin
  have hnn : 0 ≤ ((9 : ℝ) / 10) * (ℓ : ℝ) := by positivity
  have hf : (⌊((9 : ℝ) / 10) * ℓ⌋₊ : ℝ) ≤ ((9 : ℝ) / 10) * ℓ := Nat.floor_le hnn
  push_cast
  linarith

lemma kmin_le (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : kmin ℓ ≤ ℓ := by
  by_cases h : ℓ ≤ 9
  · interval_cases ℓ <;> unfold kmin <;> norm_num
  · have hk := kmin_le_add_one ℓ
    have h10 : (10 : ℝ) ≤ ℓ := by
      exact_mod_cast (Nat.succ_le_of_lt (lt_of_not_ge h) : 10 ≤ ℓ)
    have : ((9 : ℝ) / 10) * ℓ + 1 ≤ ℓ := by nlinarith
    exact_mod_cast hk.trans this

lemma eleven_mul_kmin_le (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    11 * kmin ℓ ≤ 10 * (ℓ + 1) := by
  by_cases h : ℓ ≤ 9
  · interval_cases ℓ <;> unfold kmin <;> norm_num
  · have hk : (kmin ℓ : ℝ) ≤ ((9 : ℝ) / 10) * ℓ + 1 := kmin_le_add_one ℓ
    have h10 : (10 : ℝ) ≤ ℓ := by
      exact_mod_cast (Nat.succ_le_of_lt (lt_of_not_ge h) : 10 ≤ ℓ)
    have h' : (11 : ℝ) * (((9 : ℝ) / 10) * ℓ + 1) ≤ 10 * (ℓ + 1) := by nlinarith
    have : (11 : ℝ) * kmin ℓ ≤ 10 * (ℓ + 1) :=
      (mul_le_mul_of_nonneg_left hk (by norm_num)).trans h'
    exact_mod_cast this

lemma two_rpow_one_div_ten_le :
    (2 : ℝ) ^ ((1 : ℝ) / 10) ≤ (11 : ℝ) / 10 := by
  have hpos : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) / 10) := Real.rpow_nonneg (by norm_num) _
  have h10 : ((2 : ℝ) ^ ((1 : ℝ) / 10)) ^ (10 : ℕ) ≤ ((11 : ℝ) / 10) ^ (10 : ℕ) := by
    have lhs : ((2 : ℝ) ^ ((1 : ℝ) / 10)) ^ (10 : ℕ) = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have rhs : ((11 : ℝ) / 10) ^ (10 : ℕ) = 11 ^ 10 / 10 ^ 10 := div_pow _ _ _
    rw [lhs, rhs]
    exact (le_div_iff₀ (by positivity)).mpr (by norm_num)
  exact (pow_le_pow_iff_left₀ hpos (by positivity) (by norm_num)).1 h10

lemma fifty_pow_le_hundred_rpow :
    (50 : ℝ) ≤ (100 : ℝ) ^ ((9 : ℝ) / 10) := by
  have hpow : (50 : ℝ) ^ (10 : ℕ) ≤ (100 : ℝ) ^ (9 : ℕ) := by norm_num
  have h50 : (50 : ℝ) = ((50 : ℝ) ^ (10 : ℕ)) ^ ((1 : ℝ) / 10) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have h100 : ((100 : ℝ) ^ (9 : ℕ)) ^ ((1 : ℝ) / 10) = (100 : ℝ) ^ ((9 : ℝ) / 10) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hle : ((50 : ℝ) ^ (10 : ℕ)) ^ ((1 : ℝ) / 10)
      ≤ ((100 : ℝ) ^ (9 : ℕ)) ^ ((1 : ℝ) / 10) :=
    Real.rpow_le_rpow (by positivity) hpow (by positivity)
  calc
    (50 : ℝ) = ((50 : ℝ) ^ (10 : ℕ)) ^ ((1 : ℝ) / 10) := h50
    _ ≤ ((100 : ℝ) ^ (9 : ℕ)) ^ ((1 : ℝ) / 10) := hle
    _ = (100 : ℝ) ^ ((9 : ℝ) / 10) := h100

lemma fifty_pow_le_hundred_kmin (ℓ : ℕ) :
    (50 : ℝ) ^ ℓ ≤ (100 : ℝ) ^ kmin ℓ := by
  have h1 : (50 : ℝ) ^ ℓ ≤ ((100 : ℝ) ^ ((9 : ℝ) / 10)) ^ ℓ :=
    pow_le_pow_left₀ (by positivity) fifty_pow_le_hundred_rpow ℓ
  have h2 : ((100 : ℝ) ^ ((9 : ℝ) / 10)) ^ ℓ = (100 : ℝ) ^ (((9 : ℝ) / 10) * ℓ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_comm]
  have h3 : (100 : ℝ) ^ (((9 : ℝ) / 10) * ℓ) ≤ (100 : ℝ) ^ (kmin ℓ : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_of_lt (kmin_gt ℓ))
  have h4 : (100 : ℝ) ^ (kmin ℓ : ℝ) = (100 : ℝ) ^ kmin ℓ := Real.rpow_natCast _ _
  calc
    (50 : ℝ) ^ ℓ ≤ ((100 : ℝ) ^ ((9 : ℝ) / 10)) ^ ℓ := h1
    _ = (100 : ℝ) ^ (((9 : ℝ) / 10) * ℓ) := h2
    _ ≤ (100 : ℝ) ^ (kmin ℓ : ℝ) := h3
    _ = (100 : ℝ) ^ kmin ℓ := h4

lemma fortyfour_eight_le_three_fifty (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    (44 : ℝ) * 8 ^ ℓ ≤ 3 * 50 ^ ℓ := by
  induction ℓ, hℓ using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h8 : (8 : ℝ) ≤ 50 := by norm_num
    calc
      (44 : ℝ) * 8 ^ (n + 1) = 8 * (44 * 8 ^ n) := by ring
      _ ≤ 50 * (3 * 50 ^ n) := mul_le_mul h8 ih (by positivity) (by positivity)
      _ = 3 * 50 ^ (n + 1) := by ring

lemma eleven_two_pow_le_twelve_fifty (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    (11 : ℝ) * 2 ^ (3 * ℓ + 4) ≤ 12 * 50 ^ ℓ := by
  have h := fortyfour_eight_le_three_fifty ℓ hℓ
  have hpow : (2 : ℝ) ^ (3 * ℓ + 4) = 16 * 8 ^ ℓ := by
    calc
      (2 : ℝ) ^ (3 * ℓ + 4) = 2 ^ (4 + 3 * ℓ) := by ring_nf
      _ = 2 ^ 4 * 2 ^ (3 * ℓ) := pow_add _ _ _
      _ = 16 * (2 ^ 3) ^ ℓ := by
        rw [pow_mul]
        norm_num
      _ = 16 * 8 ^ ℓ := by norm_num
  have : (11 : ℝ) * 16 * 8 ^ ℓ ≤ 12 * 50 ^ ℓ := by
    have h' : (176 : ℝ) * 8 ^ ℓ ≤ 12 * 50 ^ ℓ := by
      have : (176 : ℝ) * 8 ^ ℓ = (4 : ℝ) * (44 * 8 ^ ℓ) := by ring
      have : (12 : ℝ) * 50 ^ ℓ = 4 * (3 * 50 ^ ℓ) := by ring
      nlinarith
    convert h' using 1
    ring
  rw [hpow]
  convert this using 1
  ring

lemma eleven_two_pow_le_twelve_hundred (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    (11 : ℝ) * 2 ^ (3 * ℓ + 4) ≤ 12 * 100 ^ kmin ℓ :=
  (eleven_two_pow_le_twelve_fifty ℓ hℓ).trans <|
    mul_le_mul_of_nonneg_left (fifty_pow_le_hundred_kmin ℓ) (by positivity)

lemma choose_geom_tail_le (ℓ : ℕ) :
    ∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ k * ℓ.choose k
      ≤ ((1 : ℝ) / 100) ^ kmin ℓ * 2 ^ ℓ := by
  have hsum :
      ∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ k * ℓ.choose k
        ≤ ∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ kmin ℓ * ℓ.choose k := by
    refine sum_le_sum ?_
    intro k hk
    have hk' : kmin ℓ ≤ k := (mem_Icc.mp hk).1
    have hpow : ((1 : ℝ) / 100) ^ k ≤ ((1 : ℝ) / 100) ^ kmin ℓ :=
      pow_le_pow_of_le_one (by positivity) (by norm_num) hk'
    exact mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)
  have hre : ∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ kmin ℓ * ℓ.choose k
      = ((1 : ℝ) / 100) ^ kmin ℓ * ∑ k ∈ Icc (kmin ℓ) ℓ, (ℓ.choose k : ℝ) := by
    simp [mul_sum]
  have hchoose : ∑ k ∈ Icc (kmin ℓ) ℓ, (ℓ.choose k : ℝ)
      ≤ ∑ k ∈ range (ℓ + 1), (ℓ.choose k : ℝ) := by
    refine sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro k hk
      exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hk).2)
    · intro _ _ _; exact Nat.cast_nonneg _
  have hbin : ∑ k ∈ range (ℓ + 1), (ℓ.choose k : ℝ) = (2 : ℝ) ^ ℓ := by
    simpa using congrArg (fun n : ℕ => (n : ℝ)) (sum_range_choose ℓ)
  calc
    ∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ k * ℓ.choose k
        ≤ ∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ kmin ℓ * ℓ.choose k := hsum
    _ = ((1 : ℝ) / 100) ^ kmin ℓ * ∑ k ∈ Icc (kmin ℓ) ℓ, (ℓ.choose k : ℝ) := hre
    _ ≤ ((1 : ℝ) / 100) ^ kmin ℓ * ∑ k ∈ range (ℓ + 1), (ℓ.choose k : ℝ) :=
      mul_le_mul_of_nonneg_left hchoose (by positivity)
    _ = ((1 : ℝ) / 100) ^ kmin ℓ * 2 ^ ℓ := by rw [hbin]

lemma bad_frac_le_of_two (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    ((1 : ℝ) / 100) ^ kmin ℓ * 2 ^ ℓ * 2 ^ (ℓ + 2)
      ≤ (12 / 11) * (1 / (2 : ℝ) ^ (ℓ + 2)) := by
  have h := eleven_two_pow_le_twelve_hundred ℓ hℓ
  have hA : (0 : ℝ) < (100 : ℝ) ^ kmin ℓ := by positivity
  have hE : (0 : ℝ) < (2 : ℝ) ^ (ℓ + 2) := by positivity
  have hD : (0 : ℝ) < (11 : ℝ) := by norm_num
  have hpow : ((1 : ℝ) / 100) ^ kmin ℓ * 2 ^ ℓ * 2 ^ (ℓ + 2)
      = ((1 : ℝ) / 100) ^ kmin ℓ * 2 ^ (2 * ℓ + 2) := by
    have : (2 : ℝ) ^ ℓ * 2 ^ (ℓ + 2) = 2 ^ (2 * ℓ + 2) := by
      rw [← pow_add]; ring_nf
    ring
  rw [hpow, one_div_pow]
  have : (2 : ℝ) ^ (2 * ℓ + 2) / 100 ^ kmin ℓ
      ≤ 12 / (11 * 2 ^ (ℓ + 2)) := by
    rw [div_le_div_iff₀ hA (mul_pos hD hE)]
    have hexp : (2 : ℝ) ^ (2 * ℓ + 2) * (11 * 2 ^ (ℓ + 2)) = 11 * 2 ^ (3 * ℓ + 4) := by
      have : (2 : ℝ) ^ (2 * ℓ + 2) * 2 ^ (ℓ + 2) = 2 ^ (3 * ℓ + 4) := by
        rw [← pow_add]; ring_nf
      ring
    simpa [hexp] using h
  convert this using 1
  · ring
  · field_simp

lemma bad_frac_le_one :
    ((1 : ℝ) / 100) * 2 ^ (1 + 2) ≤ (12 / 11) * (1 / (2 : ℝ) ^ (1 + 2)) := by
  norm_num

lemma frac_gap (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (1 : ℝ) / 2 ^ (ℓ + 2) ≤ 1 / 2 ^ (kmin ℓ - 1 + 2) - 1 / 2 ^ (ℓ + 2) := by
  have hk : kmin ℓ ≤ ℓ := kmin_le ℓ hℓ
  have hle : kmin ℓ - 1 + 2 ≤ ℓ + 1 := by omega
  have hpow : (2 : ℝ) ^ (kmin ℓ - 1 + 2) ≤ 2 ^ (ℓ + 1) :=
    pow_le_pow_right₀ (by norm_num) hle
  have hle' : (1 : ℝ) / 2 ^ (ℓ + 1) ≤ 1 / 2 ^ (kmin ℓ - 1 + 2) :=
    one_div_le_one_div_of_le (by positivity) hpow
  have h2 : (1 : ℝ) / 2 ^ (ℓ + 1) = 2 * (1 / 2 ^ (ℓ + 2)) := by
    have : (2 : ℝ) ^ (ℓ + 2) = 2 ^ (ℓ + 1) * 2 := pow_succ _ _
    field_simp [this]
    ring
  have hle'' : 2 * (1 / (2 : ℝ) ^ (ℓ + 2)) ≤ 1 / 2 ^ (kmin ℓ - 1 + 2) := by
    simpa [h2] using hle'
  linarith

lemma two_div_three_add_le :
    (2 : ℝ) / 3 + 1 / 2 ^ (0 + 2) ≤ (11 : ℝ) / 12 := by
  norm_num

lemma occupation_mul_le (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {β : ℝ}
    (hβ : β ≤ (12 / 11) * (1 / (2 : ℝ) ^ (ℓ + 2))) :
    (2 / 3 + 1 / (2 : ℝ) ^ (ℓ + 2)) ≤
      ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (kmin ℓ - 1 + 2)) * (1 - β) := by
  set a : ℝ := (2 : ℝ) / 3
  set b : ℝ := 1 / (2 : ℝ) ^ (kmin ℓ - 1 + 2)
  set d : ℝ := 1 / (2 : ℝ) ^ (ℓ + 2)
  have hb0 : 0 ≤ b := by positivity
  have hd0 : 0 ≤ d := by positivity
  have ha0 : 0 < a := by norm_num [a]
  have hgap : d ≤ b - d := frac_gap ℓ hℓ
  have hb_le : b ≤ (1 : ℝ) / 4 := by
    have : 2 ≤ kmin ℓ - 1 + 2 := by
      have := kmin_pos ℓ
      omega
    have : (2 : ℝ) ^ (2 : ℕ) ≤ 2 ^ (kmin ℓ - 1 + 2) :=
      pow_le_pow_right₀ (by norm_num) this
    have : (1 : ℝ) / 2 ^ (kmin ℓ - 1 + 2) ≤ 1 / 4 := by
      have h4 : (2 : ℝ) ^ (2 : ℕ) = 4 := by norm_num
      simpa [h4] using one_div_le_one_div_of_le (by positivity) this
    simpa [b] using this
  have hab : a + b ≤ (11 : ℝ) / 12 := by
    have : a + 1 / 4 = (11 : ℝ) / 12 := by norm_num [a]
    linarith
  have hden : (0 : ℝ) < a + b := add_pos_of_pos_of_nonneg ha0 hb0
  have hfrac : (12 / 11) * d ≤ (b - d) / (a + b) := by
    have hde : (0 : ℝ) < (11 : ℝ) / 12 := by norm_num
    have h1 : d / ((11 : ℝ) / 12) ≤ (b - d) / (a + b) :=
      div_le_div₀ (le_trans hd0 hgap) hgap hden hab
    have h2 : d / ((11 : ℝ) / 12) = (12 / 11) * d := by field_simp
    simpa [h2] using h1
  have hc : β ≤ (b - d) / (a + b) := hβ.trans (by simpa [d] using hfrac)
  have hmul : β * (a + b) ≤ b - d := (le_div_iff₀ hden).mp hc
  have : a + d ≤ (a + b) * (1 - β) := by nlinarith
  simpa [a, b, d] using this

end KahnKalai

/- ===== Source module: KahnKalai/DoubleCount.lean ===== -/

/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch
-/

/-!
Tran–Vu Lemma 2.4 (double counting of large minimals `G_W`).
-/

open Finset

set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace KahnKalai

variable {α : Type*} [DecidableEq α] [Fintype α]

noncomputable section

/-- `w = ⌊0.1 L p N⌋`. -/
noncomputable def coveringWidth (p : ℝ) (N : ℕ) : ℕ :=
  ⌊((1 : ℝ) / 10) * coveringConstant * p * N⌋₊

lemma coveringWidth_eq (p : ℝ) (N : ℕ) :
    coveringWidth p N = ⌊(100 : ℝ) * p * N⌋₊ := by
  unfold coveringWidth coveringConstant
  ring_nf

lemma choose_add_le (N w k : ℕ) :
    (N.choose (w + k) : ℝ) ≤ N.choose w * ((N : ℝ) / (w + 1)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc]
    by_cases h0 : N.choose (w + k + 1) = 0
    · simp [h0]
      exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_nonneg (Nat.cast_nonneg _) (by positivity)) _)
    · have hratio :
          (N.choose (w + k + 1) : ℝ)
            = N.choose (w + k) * ((N - (w + k) : ℕ) / (w + k + 1) : ℝ) := by
        have hmul := Nat.choose_succ_right_eq N (w + k)
        have hk : (w + k + 1 : ℝ) ≠ 0 := by positivity
        rw [← mul_div_assoc, eq_div_iff hk]
        exact_mod_cast hmul
      have hfrac : ((N - (w + k) : ℕ) : ℝ) / (w + k + 1) ≤ (N : ℝ) / (w + 1) := by
        have hnum : ((N - (w + k) : ℕ) : ℝ) ≤ N := Nat.cast_le.mpr (Nat.sub_le _ _)
        have hden : (w + 1 : ℝ) ≤ w + k + 1 := by
          exact_mod_cast (by omega : w + 1 ≤ w + k + 1)
        exact div_le_div₀ (Nat.cast_nonneg _) hnum (by positivity) hden
      have hstep : (N.choose (w + k + 1) : ℝ)
          ≤ N.choose (w + k) * ((N : ℝ) / (w + 1)) := by
        rw [hratio]
        exact mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg _)
      have hpow : ((N : ℝ) / (w + 1)) ^ (k + 1)
          = ((N : ℝ) / (w + 1)) ^ k * ((N : ℝ) / (w + 1)) := pow_succ _ _
      calc
        (N.choose (w + k + 1) : ℝ)
            ≤ N.choose (w + k) * ((N : ℝ) / (w + 1)) := hstep
        _ ≤ (N.choose w * ((N : ℝ) / (w + 1)) ^ k) * ((N : ℝ) / (w + 1)) :=
          mul_le_mul_of_nonneg_right ih (by positivity)
        _ = N.choose w * ((N : ℝ) / (w + 1)) ^ (k + 1) := by rw [hpow]; ring

lemma np_div_width_succ_le (p : ℝ) (N : ℕ) :
    (N : ℝ) * p / (coveringWidth p N + 1) ≤ 1 / 100 := by
  set w := coveringWidth p N
  have hx : (100 : ℝ) * p * N < (w + 1 : ℝ) := by
    have := Nat.lt_floor_add_one ((100 : ℝ) * p * N)
    simpa [coveringWidth_eq, w, add_comm] using this
  have hden : (0 : ℝ) < (w + 1 : ℝ) := by positivity
  refine (div_le_iff₀ hden).mpr ?_
  nlinarith

lemma largeMinimals_disjoint {H : Finset (Finset α)} {W T : Finset α} {ℓ : ℕ}
    (h : T ∈ largeMinimals H W ℓ) : Disjoint T W :=
  restrictFamily_disjoint (minimals_subset _ (largeMinimals_mem_minimals h))

lemma exists_mem_subset_union {H : Finset (Finset α)} {W' S₀ : Finset α}
    (h : S₀ ∈ restrictFamily H (W' \ S₀)) (hsub : S₀ ⊆ W') :
    ∃ S ∈ H, S ⊆ W' ∧ S₀ ⊆ S := by
  obtain ⟨S, hS, hSeq⟩ := mem_restrictFamily.mp h
  have hS0S : S₀ ⊆ S := by
    rw [← hSeq]
    exact sdiff_subset
  have hSW' : S ⊆ W' := by
    intro x hxS
    by_contra hxW'
    have hx_not : x ∉ W' \ S₀ := by
      simp [mem_sdiff, hxW']
    have hxS0 : x ∈ S₀ := by
      have : x ∈ S \ (W' \ S₀) := mem_sdiff.mpr ⟨hxS, hx_not⟩
      rwa [hSeq] at this
    exact hxW' (hsub hxS0)
  exact ⟨S, hS, hSW', hS0S⟩

lemma subset_of_minimal_fiber {H : Finset (Finset α)} {W' S S' : Finset α}
    (hS' : S' ∈ minimals (restrictFamily H (W' \ S')))
    (hS : S ∈ H) (hSW' : S ⊆ W') :
    S' ⊆ S := by
  set W := W' \ S'
  have hres : S \ W ∈ restrictFamily H W := mem_restrictFamily.mpr ⟨S, hS, rfl⟩
  have hsub : S \ W ⊆ S' := by
    intro x hx
    have hxS : x ∈ S := (mem_sdiff.mp hx).1
    have hxW : x ∉ W := (mem_sdiff.mp hx).2
    have hxW' : x ∈ W' := hSW' hxS
    by_contra hxS'
    exact hxW (mem_sdiff.mpr ⟨hxW', hxS'⟩)
  have hmin := (mem_minimals.mp hS').2 (S \ W) hres hsub
  exact hmin ▸ sdiff_subset

lemma card_fiber_le {H : Finset (Finset α)} {ℓ : ℕ} (hb : IsBounded H ℓ)
    (W' : Finset α) (k : ℕ) :
    #{S' : Finset α | S'.card = k ∧ S' ⊆ W' ∧ S' ∈ largeMinimals H (W' \ S') ℓ}
      ≤ ℓ.choose k := by
  classical
  set Fiber := univ.filter
    (fun S' : Finset α => S'.card = k ∧ S' ⊆ W' ∧ S' ∈ largeMinimals H (W' \ S') ℓ)
  by_cases hF : Fiber.Nonempty
  · obtain ⟨S₀, hS₀mem⟩ := hF
    have hS₀ : S₀.card = k ∧ S₀ ⊆ W' ∧ S₀ ∈ largeMinimals H (W' \ S₀) ℓ :=
      (mem_filter.mp hS₀mem).2
    have hres : S₀ ∈ restrictFamily H (W' \ S₀) :=
      minimals_subset _ (largeMinimals_mem_minimals hS₀.2.2)
    obtain ⟨S, hSH, hSW', _hS₀S⟩ := exists_mem_subset_union hres hS₀.2.1
    have hcardS : S.card ≤ ℓ := hb S hSH
    have hinj : Fiber ⊆ S.powersetCard k := by
      intro S' hS'
      have h' : S'.card = k ∧ S' ⊆ W' ∧ S' ∈ largeMinimals H (W' \ S') ℓ :=
        (mem_filter.mp hS').2
      have hsub : S' ⊆ S :=
        subset_of_minimal_fiber (largeMinimals_mem_minimals h'.2.2) hSH hSW'
      exact mem_powersetCard.mpr ⟨hsub, h'.1⟩
    have : #Fiber ≤ #(S.powersetCard k) := card_le_card hinj
    have hch : #(S.powersetCard k) = S.card.choose k := card_powersetCard _ _
    have hch' : S.card.choose k ≤ ℓ.choose k := Nat.choose_le_choose k hcardS
    exact this.trans (hch.trans_le hch')
  · have : Fiber = ∅ := not_nonempty_iff_eq_empty.mp hF
    simp [this]

def largePairs (H : Finset (Finset α)) (ℓ w k : ℕ) : Finset (Finset α × Finset α) :=
  (univ.filter (fun W : Finset α => W.card = w)).biUnion fun W =>
    ((largeMinimals H W ℓ).filter (fun S' => S'.card = k)).image fun S' => (W, S')

lemma mem_largePairs {H : Finset (Finset α)} {ℓ w k : ℕ} {p : Finset α × Finset α} :
    p ∈ largePairs H ℓ w k ↔
      p.1.card = w ∧ p.2.card = k ∧ p.2 ∈ largeMinimals H p.1 ℓ := by
  simp only [largePairs, mem_biUnion, mem_filter, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨W, hw, S', ⟨hL, hk⟩, rfl⟩
    exact ⟨hw, hk, hL⟩
  · rintro ⟨hw, hk, hL⟩
    exact ⟨p.1, hw, p.2, ⟨hL, hk⟩, rfl⟩

lemma card_pairs_le {H : Finset (Finset α)} {ℓ w k : ℕ} (hb : IsBounded H ℓ) :
    #(largePairs H ℓ w k) ≤ (Fintype.card α).choose (w + k) * ℓ.choose k := by
  classical
  let L := univ.filter (fun W' : Finset α => W'.card = w + k)
  have htoL : ∀ p ∈ largePairs H ℓ w k, p.1 ∪ p.2 ∈ L := by
    intro p hp
    obtain ⟨hw, hk, hL⟩ := mem_largePairs.mp hp
    have hdis := (largeMinimals_disjoint hL).symm
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    rw [card_union_of_disjoint hdis, hw, hk]
  have hP := card_eq_sum_card_fiberwise (s := largePairs H ℓ w k) (t := L)
    (f := fun p => p.1 ∪ p.2) (fun p hp => htoL p hp)
  have hfib : ∀ W' ∈ L, #{p ∈ largePairs H ℓ w k | p.1 ∪ p.2 = W'} ≤ ℓ.choose k := by
    intro W' _
    let i : Finset α → Finset α × Finset α := fun S' => (W' \ S', S')
    let Fiber := univ.filter fun S' : Finset α =>
      S'.card = k ∧ S' ⊆ W' ∧ S' ∈ largeMinimals H (W' \ S') ℓ
    have himage : {p ∈ largePairs H ℓ w k | p.1 ∪ p.2 = W'} ⊆ Fiber.image i := by
      intro p hp
      obtain ⟨hpP, hU⟩ := mem_filter.mp hp
      obtain ⟨_hw, hk, hL⟩ := mem_largePairs.mp hpP
      have hdis := (largeMinimals_disjoint hL).symm
      have hW : p.1 = W' \ p.2 := by
        rw [← hU, union_sdiff_cancel_right hdis]
      refine mem_image.mpr ⟨p.2, mem_filter.mpr ⟨mem_univ _, hk, ?_, ?_⟩, ?_⟩
      · intro x hx
        rw [← hU]
        exact mem_union.mpr (Or.inr hx)
      · simpa [hW] using hL
      · simp [i, Prod.ext_iff, hW]
    exact ((card_le_card himage).trans card_image_le).trans (card_fiber_le hb W' k)
  have hsum : #(largePairs H ℓ w k) ≤ ∑ _W' ∈ L, ℓ.choose k := by
    rw [hP]
    exact sum_le_sum hfib
  have : #(largePairs H ℓ w k) ≤ #L * ℓ.choose k := by
    simpa [sum_const, nsmul_eq_mul, mul_comm] using hsum
  simpa [L, card_level] using this

lemma card_pairs_fst {H : Finset (Finset α)} {ℓ w k : ℕ} {W : Finset α}
    (hW : W.card = w) :
    #{p ∈ largePairs H ℓ w k | p.1 = W} =
      #{S' ∈ largeMinimals H W ℓ | S'.card = k} := by
  classical
  let f : Finset α → Finset α × Finset α := fun S' => (W, S')
  have himg :
      ((largeMinimals H W ℓ).filter (fun S' => S'.card = k)).image f =
        (largePairs H ℓ w k).filter (fun p => p.1 = W) := by
    ext p
    simp only [mem_image, mem_filter, f]
    constructor
    · rintro ⟨S', ⟨hL, hk⟩, rfl⟩
      exact ⟨mem_largePairs.mpr ⟨hW, hk, hL⟩, rfl⟩
    · rintro ⟨hp, hfst⟩
      obtain ⟨_hw, hk, hL⟩ := mem_largePairs.mp hp
      subst hfst
      exact ⟨p.2, ⟨hL, hk⟩, rfl⟩
  have hinj : Set.InjOn f ((largeMinimals H W ℓ).filter (fun S' => S'.card = k)) := by
    intro S₁ _ S₂ _ h
    exact (Prod.ext_iff.mp h).2
  rw [← himg, card_image_of_injOn hinj]

lemma sum_card_large_eq_pairs (H : Finset (Finset α)) (ℓ w k : ℕ) :
    ∑ W ∈ univ.filter (fun W : Finset α => W.card = w),
        #{S' ∈ largeMinimals H W ℓ | S'.card = k}
      = #(largePairs H ℓ w k) := by
  classical
  set Lw := univ.filter (fun W : Finset α => W.card = w)
  have hto : ∀ p ∈ largePairs H ℓ w k, p.1 ∈ Lw := by
    intro p hp
    exact mem_filter.mpr ⟨mem_univ _, (mem_largePairs.mp hp).1⟩
  have hsum := card_eq_sum_card_fiberwise (s := largePairs H ℓ w k) (t := Lw)
    (f := fun p => p.1) (fun p hp => hto p hp)
  calc
    ∑ W ∈ Lw, #{S' ∈ largeMinimals H W ℓ | S'.card = k}
        = ∑ W ∈ Lw, #{p ∈ largePairs H ℓ w k | p.1 = W} := by
          refine sum_congr rfl ?_
          intro W hW
          exact (card_pairs_fst (mem_filter.mp hW).2).symm
    _ = #(largePairs H ℓ w k) := hsum.symm

lemma expectation_eq_sum_level {p : ℝ} (G : Finset (Finset α)) (ℓ : ℕ)
    (hb : IsBounded G ℓ) :
    expectation p G = ∑ k ∈ Icc 0 ℓ, p ^ k * (#{S ∈ G | S.card = k} : ℝ) := by
  classical
  have hmap : ∀ S ∈ G, S.card ∈ Icc 0 ℓ := fun S hS =>
    mem_Icc.mpr ⟨Nat.zero_le _, hb S hS⟩
  simp only [expectation]
  rw [← sum_fiberwise_of_maps_to' hmap (fun k => p ^ k)]
  refine sum_congr rfl ?_
  intro k _hk
  rw [sum_const, nsmul_eq_mul, mul_comm]

lemma sum_expectation_large {p : ℝ} (H : Finset (Finset α)) (ℓ : ℕ)
    (hb : IsBounded H ℓ) (w : ℕ) :
    ∑ W ∈ univ.filter (fun W : Finset α => W.card = w),
        expectation p (largeMinimals H W ℓ)
      = ∑ k ∈ Icc 0 ℓ, p ^ k * (#(largePairs H ℓ w k) : ℝ) := by
  have hbW : ∀ W, IsBounded (largeMinimals H W ℓ) ℓ := fun W => hb.largeMinimals W
  have h1 :
      ∑ W ∈ univ.filter (fun W : Finset α => W.card = w),
          expectation p (largeMinimals H W ℓ)
        = ∑ W ∈ univ.filter (fun W : Finset α => W.card = w),
            ∑ k ∈ Icc 0 ℓ, p ^ k * (#{S ∈ largeMinimals H W ℓ | S.card = k} : ℝ) :=
    sum_congr rfl fun W _ => expectation_eq_sum_level _ ℓ (hbW W)
  rw [h1, sum_comm]
  refine sum_congr rfl ?_
  intro k hk
  rw [← mul_sum, ← Nat.cast_sum, sum_card_large_eq_pairs]

lemma largePairs_eq_empty_of_lt_kmin {H : Finset (Finset α)} {ℓ w k : ℕ}
    (hk : k < kmin ℓ) : largePairs H ℓ w k = ∅ := by
  ext p
  constructor
  · intro hp
    obtain ⟨_hw, hkcard, hL⟩ := mem_largePairs.mp hp
    have : kmin ℓ ≤ p.2.card := by
      simpa [kmin] using largeMinimals_card_gt hL
    omega
  · intro h
    cases h

lemma sum_expectation_large_tail {p : ℝ} (H : Finset (Finset α)) (ℓ : ℕ)
    (hb : IsBounded H ℓ) (w : ℕ) :
    ∑ W ∈ univ.filter (fun W : Finset α => W.card = w),
        expectation p (largeMinimals H W ℓ)
      = ∑ k ∈ Icc (kmin ℓ) ℓ, p ^ k * (#(largePairs H ℓ w k) : ℝ) := by
  rw [sum_expectation_large H ℓ hb w]
  have hsub : Icc (kmin ℓ) ℓ ⊆ Icc 0 ℓ := by
    intro k hk
    have hk' := mem_Icc.mp hk
    exact mem_Icc.mpr ⟨Nat.zero_le _, hk'.2⟩
  have hzero : ∀ k ∈ Icc 0 ℓ, k ∉ Icc (kmin ℓ) ℓ →
      p ^ k * (#(largePairs H ℓ w k) : ℝ) = 0 := by
    intro k hk hkmin
    have hkI := mem_Icc.mp hk
    have : k < kmin ℓ := lt_of_not_ge fun hle =>
      hkmin (mem_Icc.mpr ⟨hle, hkI.2⟩)
    simp [largePairs_eq_empty_of_lt_kmin this]
  exact (sum_subset hsub hzero).symm

lemma double_counting_tail {p : ℝ} (hp0 : 0 ≤ p) (H : Finset (Finset α))
    (ℓ : ℕ) (hb : IsBounded H ℓ) :
    ∑ W ∈ univ.filter (fun W : Finset α => W.card = coveringWidth p (Fintype.card α)),
        coverCost p (largeMinimals H W ℓ)
      ≤ ((Fintype.card α).choose (coveringWidth p (Fintype.card α)) : ℝ) *
          ∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ k * ℓ.choose k := by
  set N := Fintype.card α
  set w := coveringWidth p N
  have hE :
      ∑ W ∈ univ.filter (fun W : Finset α => W.card = w),
          expectation p (largeMinimals H W ℓ)
        ≤ (N.choose w : ℝ) *
            ∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ k * ℓ.choose k := by
    rw [sum_expectation_large_tail H ℓ hb w]
    have hterm : ∀ k ∈ Icc (kmin ℓ) ℓ,
        p ^ k * (#(largePairs H ℓ w k) : ℝ)
          ≤ (N.choose w : ℝ) * ((1 : ℝ) / 100) ^ k * ℓ.choose k := by
      intro k _hk
      have hcard : (#(largePairs H ℓ w k) : ℝ) ≤ N.choose (w + k) * ℓ.choose k := by
        exact_mod_cast (card_pairs_le hb)
      have hch := choose_add_le N w k
      have hpW := np_div_width_succ_le p N
      have hr : (N : ℝ) / (w + 1) * p ≤ 1 / 100 := by
        have : (N : ℝ) / (w + 1) * p = N * p / (w + 1) := by ring
        simpa [this, w] using hpW
      have hnonneg : (0 : ℝ) ≤ N / (w + 1) * p :=
        mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by positivity)) hp0
      have hpow : ((N : ℝ) / (w + 1) * p) ^ k ≤ ((1 : ℝ) / 100) ^ k :=
        pow_le_pow_left₀ hnonneg hr k
      have hpkn : 0 ≤ p ^ k := pow_nonneg hp0 _
      have hchN : 0 ≤ (ℓ.choose k : ℝ) := Nat.cast_nonneg _
      calc
        p ^ k * (#(largePairs H ℓ w k) : ℝ)
            ≤ p ^ k * (N.choose (w + k) * ℓ.choose k) :=
          mul_le_mul_of_nonneg_left hcard hpkn
        _ = N.choose (w + k) * p ^ k * ℓ.choose k := by ring
        _ ≤ N.choose w * ((N : ℝ) / (w + 1)) ^ k * p ^ k * ℓ.choose k :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hch hpkn) hchN
        _ = N.choose w * ((N : ℝ) / (w + 1) * p) ^ k * ℓ.choose k := by
          rw [mul_pow]; ring
        _ ≤ N.choose w * ((1 : ℝ) / 100) ^ k * ℓ.choose k :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)) hchN
    have hsum := sum_le_sum hterm
    have hfactor :
        ∑ k ∈ Icc (kmin ℓ) ℓ, (N.choose w : ℝ) * ((1 : ℝ) / 100) ^ k * ℓ.choose k
          = (N.choose w : ℝ) * ∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ k * ℓ.choose k := by
      simp [mul_sum, mul_left_comm, mul_comm]
    calc
      ∑ k ∈ Icc (kmin ℓ) ℓ, p ^ k * (#(largePairs H ℓ w k) : ℝ)
          ≤ ∑ k ∈ Icc (kmin ℓ) ℓ,
              (N.choose w : ℝ) * ((1 : ℝ) / 100) ^ k * ℓ.choose k := hsum
      _ = (N.choose w : ℝ) *
            ∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ k * ℓ.choose k := hfactor
  have hcost :
      ∑ W ∈ univ.filter (fun W : Finset α => W.card = w),
          coverCost p (largeMinimals H W ℓ)
        ≤ ∑ W ∈ univ.filter (fun W : Finset α => W.card = w),
            expectation p (largeMinimals H W ℓ) :=
    sum_le_sum fun W _ => coverCost_le_expectation hp0 (covers_self _)
  calc
    ∑ W ∈ univ.filter (fun W : Finset α => W.card = w),
          coverCost p (largeMinimals H W ℓ)
        ≤ ∑ W ∈ univ.filter (fun W : Finset α => W.card = w),
            expectation p (largeMinimals H W ℓ) := hcost
    _ ≤ (N.choose w : ℝ) *
          ∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ k * ℓ.choose k := hE

lemma double_counting {p : ℝ} (hp0 : 0 ≤ p) (H : Finset (Finset α))
    (ℓ : ℕ) (hb : IsBounded H ℓ) :
    ∑ W ∈ univ.filter (fun W : Finset α => W.card = coveringWidth p (Fintype.card α)),
        coverCost p (largeMinimals H W ℓ)
      ≤ ((Fintype.card α).choose (coveringWidth p (Fintype.card α)) : ℝ) *
          ((1 : ℝ) / 100) ^ kmin ℓ * 2 ^ ℓ := by
  have htail := double_counting_tail hp0 H ℓ hb
  have hgeom := choose_geom_tail_le ℓ
  have hmul :=
    mul_le_mul_of_nonneg_left hgeom
      (Nat.cast_nonneg ((Fintype.card α).choose (coveringWidth p (Fintype.card α))))
  calc
    _ ≤ _ := htail
    _ ≤ ((Fintype.card α).choose (coveringWidth p (Fintype.card α)) : ℝ) *
          (((1 : ℝ) / 100) ^ kmin ℓ * 2 ^ ℓ) := hmul
    _ = _ := by ring

end

end KahnKalai

/- ===== Source module: KahnKalai/Covering.lean ===== -/

/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch
-/

/-!
Tran–Vu Theorem 2.3: the covering theorem.
-/

open Finset

namespace KahnKalai

variable {α : Type*} [DecidableEq α] [Fintype α]

noncomputable section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

lemma frac_le_one (ℓ : ℕ) :
    (2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ + 2) ≤ 1 := by
  have : (1 : ℝ) / (2 : ℝ) ^ (ℓ + 2) ≤ 1 / 4 := by
    have : (2 : ℝ) ^ (2 : ℕ) ≤ 2 ^ (ℓ + 2) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h4 : (2 : ℝ) ^ (2 : ℕ) = 4 := by norm_num
    simpa [h4] using one_div_le_one_div_of_le (by positivity) this
  linarith

lemma covering_of_empty_mem {H : Finset (Finset α)} {ℓ : ℕ} {p : ℝ}
    (h : ∅ ∈ H) :
    ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ + 2)) *
        ((Fintype.card α).choose (coveringLevel p (Fintype.card α) ℓ) : ℝ) ≤
      (((generate H).filter
          (fun S => S.card = coveringLevel p (Fintype.card α) ℓ)).card : ℝ) := by
  set N := Fintype.card α
  set m := coveringLevel p N ℓ
  have hgen : generate H = univ := generate_eq_univ_of_empty_mem h
  have hfilter : (generate H).filter (fun S => S.card = m) =
      univ.filter (fun S => S.card = m) := by rw [hgen]
  have hcard : (((generate H).filter (fun S => S.card = m)).card : ℝ) = N.choose m := by
    rw [hfilter, card_level]
  rw [hcard]
  have hfrac := frac_le_one ℓ
  by_cases hm : m ≤ N
  · have hpos : (0 : ℝ) ≤ N.choose m := Nat.cast_nonneg _
    exact mul_le_of_le_one_left hpos hfrac
  · have : N.choose m = 0 := Nat.choose_eq_zero_of_lt (lt_of_not_ge hm)
    simp [this]

lemma covering_of_level_ge_card {H : Finset (Finset α)} {ℓ : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hf : (1 : ℝ) / 2 - 1 / (2 : ℝ) ^ (ℓ + 2) ≤ coverCost p H)
    (hm : Fintype.card α ≤ coveringLevel p (Fintype.card α) ℓ) :
    ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ + 2)) *
        ((Fintype.card α).choose (coveringLevel p (Fintype.card α) ℓ) : ℝ) ≤
      (((generate H).filter
          (fun S => S.card = coveringLevel p (Fintype.card α) ℓ)).card : ℝ) := by
  set N := Fintype.card α
  set m := coveringLevel p N ℓ
  have hpos : (0 : ℝ) < (1 : ℝ) / 2 - 1 / (2 : ℝ) ^ (ℓ + 2) := by
    have : (1 : ℝ) / (2 : ℝ) ^ (ℓ + 2) ≤ 1 / 4 := by
      have : (2 : ℝ) ^ (2 : ℕ) ≤ 2 ^ (ℓ + 2) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have h4 : (2 : ℝ) ^ (2 : ℕ) = 4 := by norm_num
      simpa [h4] using one_div_le_one_div_of_le (by positivity) this
    linarith
  have hH : H.Nonempty := coverCost_pos_imp_nonempty hp0 (lt_of_lt_of_le hpos hf)
  rcases lt_or_eq_of_le hm with hlt | heq
  · have : N.choose m = 0 := Nat.choose_eq_zero_of_lt hlt
    simp [this]
  · -- m = N: the unique N-set is `univ`, which is in `generate H`.
    have hch : N.choose m = 1 := by
      rw [heq, Nat.choose_self]
    have huniv : univ ∈ generate H := by
      obtain ⟨S, hS⟩ := hH
      exact mem_generate.mpr ⟨S, hS, subset_univ _⟩
    have hmem : univ ∈ (generate H).filter (fun S => S.card = m) := by
      refine mem_filter.mpr ⟨huniv, ?_⟩
      rw [card_univ]
      exact heq
    have hone : (1 : ℝ) ≤ (((generate H).filter (fun S => S.card = m)).card : ℝ) := by
      have : 0 < ((generate H).filter (fun S => S.card = m)).card :=
        card_pos.mpr ⟨univ, hmem⟩
      exact_mod_cast this
    have hfrac := frac_le_one ℓ
    have : ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ + 2)) * (N.choose m : ℝ)
        ≤ (((generate H).filter (fun S => S.card = m)).card : ℝ) := by
      rw [hch]
      simpa using (hfrac.trans hone)
    simpa [m] using this

lemma ell1_lt {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : ⌊((9 : ℝ) / 10) * ℓ⌋₊ < ℓ := by
  have hk : kmin ℓ ≤ ℓ := kmin_le ℓ hℓ
  have : ⌊((9 : ℝ) / 10) * ℓ⌋₊ + 1 ≤ ℓ := by simpa [kmin] using hk
  omega

lemma coveringLevel_nonneg (p : ℝ) (N ℓ : ℕ) (hp0 : 0 ≤ p) :
    0 ≤ coveringConstant * p * N * Real.logb 2 (ℓ + 1 : ℝ) := by
  have hL : 0 ≤ coveringConstant := by simp [coveringConstant]
  have hlog : 0 ≤ Real.logb 2 (ℓ + 1 : ℝ) :=
    Real.logb_nonneg (by norm_num) (by
      have : (1 : ℝ) ≤ ℓ + 1 := by exact_mod_cast (Nat.le_add_left 1 ℓ)
      exact this)
  positivity

lemma floor_add_floor_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ⌊a⌋₊ + ⌊b⌋₊ ≤ ⌊a + b⌋₊ := by
  have h : (⌊a⌋₊ : ℝ) + ⌊b⌋₊ ≤ a + b :=
    add_le_add (Nat.floor_le ha) (Nat.floor_le hb)
  have : ((⌊a⌋₊ + ⌊b⌋₊ : ℕ) : ℝ) ≤ a + b := by
    push_cast
    exact h
  exact (Nat.le_floor_iff (add_nonneg ha hb)).mpr this

lemma log_ell1_add_le (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    Real.logb 2 (⌊((9 : ℝ) / 10) * ℓ⌋₊ + 1 : ℝ) + (1 : ℝ) / 10
      ≤ Real.logb 2 (ℓ + 1 : ℝ) := by
  set ℓ₁ := ⌊((9 : ℝ) / 10) * ℓ⌋₊
  have hℓ₁ : ℓ₁ + 1 = kmin ℓ := by simp [ℓ₁, kmin]
  have h2 := two_rpow_one_div_ten_le
  have hk := eleven_mul_kmin_le ℓ hℓ
  have hmul : (ℓ₁ + 1 : ℝ) * ((11 : ℝ) / 10) ≤ ℓ + 1 := by
    have : (11 : ℝ) * (ℓ₁ + 1) ≤ 10 * (ℓ + 1) := by
      have hcast : (ℓ₁ + 1 : ℝ) = kmin ℓ := by exact_mod_cast hℓ₁
      rw [hcast]
      exact_mod_cast hk
    calc
      (ℓ₁ + 1 : ℝ) * (11 / 10) = 11 * (ℓ₁ + 1) / 10 := by ring
      _ ≤ 10 * (ℓ + 1) / 10 :=
        div_le_div_of_nonneg_right this (by positivity)
      _ = ℓ + 1 := by ring
  have hmul' : (ℓ₁ + 1 : ℝ) * (2 : ℝ) ^ ((1 : ℝ) / 10) ≤ ℓ + 1 :=
    le_trans (mul_le_mul_of_nonneg_left h2 (by positivity)) hmul
  have hx : 0 < (ℓ₁ + 1 : ℝ) := by exact_mod_cast Nat.succ_pos ℓ₁
  have hprod : 0 < (ℓ₁ + 1 : ℝ) * (2 : ℝ) ^ ((1 : ℝ) / 10) := by positivity
  have hlogprod :
      Real.logb 2 ((ℓ₁ + 1 : ℝ) * 2 ^ ((1 : ℝ) / 10))
        = Real.logb 2 (ℓ₁ + 1 : ℝ) + (1 : ℝ) / 10 := by
    have := Real.logb_mul (b := 2) (hx.ne') (by positivity : (2 : ℝ) ^ ((1 : ℝ) / 10) ≠ 0)
    have hpow : Real.logb 2 ((2 : ℝ) ^ ((1 : ℝ) / 10)) = (1 : ℝ) / 10 :=
      Real.logb_rpow (by norm_num) (by norm_num)
    simpa [hpow] using this
  have hle : Real.logb 2 ((ℓ₁ + 1 : ℝ) * 2 ^ ((1 : ℝ) / 10))
      ≤ Real.logb 2 (ℓ + 1 : ℝ) :=
    (Real.logb_le_logb (by norm_num) hprod (by positivity)).2 hmul'
  linarith [hlogprod, hle]

lemma coveringLevel_lift {p : ℝ} {N w ℓ : ℕ} (hp0 : 0 ≤ p) (hℓ : 1 ≤ ℓ)
    (hw : w = coveringWidth p N) (_hwN : w ≤ N) :
    coveringLevel p (N - w) ⌊((9 : ℝ) / 10) * ℓ⌋₊ + w ≤
      coveringLevel p N ℓ := by
  set ℓ₁ := ⌊((9 : ℝ) / 10) * ℓ⌋₊
  have ha := coveringLevel_nonneg p (N - w) ℓ₁ hp0
  have hb : 0 ≤ ((1 : ℝ) / 10) * coveringConstant * p * N := by
    have : 0 ≤ coveringConstant := by simp [coveringConstant]
    positivity
  have hw' : w = ⌊((1 : ℝ) / 10) * coveringConstant * p * N⌋₊ := by
    simpa [coveringWidth] using hw
  have hfl := floor_add_floor_le ha hb
  have hsum : coveringLevel p (N - w) ℓ₁ + w
      ≤ ⌊coveringConstant * p * ((N - w : ℕ) : ℝ) * Real.logb 2 (ℓ₁ + 1 : ℝ)
          + ((1 : ℝ) / 10) * coveringConstant * p * N⌋₊ := by
    simpa [coveringLevel, hw'] using hfl
  have hre :
      coveringConstant * p * ((N - w : ℕ) : ℝ) * Real.logb 2 (ℓ₁ + 1 : ℝ)
        + ((1 : ℝ) / 10) * coveringConstant * p * N
        ≤ coveringConstant * p * N * Real.logb 2 (ℓ + 1 : ℝ) := by
    have hlog := log_ell1_add_le ℓ hℓ
    have hNw : ((N - w : ℕ) : ℝ) ≤ N := Nat.cast_le.mpr (Nat.sub_le _ _)
    have hL : 0 ≤ coveringConstant * p := by
      have : 0 ≤ coveringConstant := by simp [coveringConstant]
      positivity
    have hlog0 : 0 ≤ Real.logb 2 (ℓ₁ + 1 : ℝ) :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast (Nat.le_add_left 1 ℓ₁))
    have h1 : coveringConstant * p * ((N - w : ℕ) : ℝ) * Real.logb 2 (ℓ₁ + 1 : ℝ)
        ≤ coveringConstant * p * N * Real.logb 2 (ℓ₁ + 1 : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNw hL) hlog0
    have h2 : coveringConstant * p * N * Real.logb 2 (ℓ₁ + 1 : ℝ)
        + ((1 : ℝ) / 10) * coveringConstant * p * N
        = coveringConstant * p * N * (Real.logb 2 (ℓ₁ + 1 : ℝ) + 1 / 10) := by
      ring
    have h3 : coveringConstant * p * N * (Real.logb 2 (ℓ₁ + 1 : ℝ) + 1 / 10)
        ≤ coveringConstant * p * N * Real.logb 2 (ℓ + 1 : ℝ) :=
      mul_le_mul_of_nonneg_left hlog (mul_nonneg hL (Nat.cast_nonneg _))
    linarith [h1, h2, h3]
  exact hsum.trans (Nat.floor_le_floor hre)

lemma card_subtype_not_mem (W : Finset α) :
    Fintype.card {x : α // x ∉ W} = Fintype.card α - W.card := by
  classical
  rw [Fintype.card_subtype]
  have : univ.filter (fun x : α => x ∉ W) = univ \ W := by
    ext x
    simp [mem_sdiff]
  rw [this, card_sdiff_of_subset (subset_univ _), card_univ]

def toSub (W : Finset α) (S : Finset α) : Finset {x : α // x ∉ W} :=
  S.subtype fun x => x ∉ W

def ofSub (W : Finset α) (T : Finset {x : α // x ∉ W}) : Finset α :=
  T.map ⟨Subtype.val, Subtype.val_injective⟩

lemma ofSub_card (W : Finset α) (T : Finset {x : α // x ∉ W}) :
    (ofSub W T).card = T.card :=
  card_map _

lemma ofSub_toSub {W S : Finset α} (h : Disjoint S W) :
    ofSub W (toSub W S) = S :=
  subtype_map_of_mem fun _ hx => disjoint_left.mp h hx

lemma toSub_subset {W S T : Finset α} (h : S ⊆ T) :
    toSub W S ⊆ toSub W T :=
  subtype_mono h

lemma ofSub_subset {W : Finset α} {T₁ T₂ : Finset {x : α // x ∉ W}} (h : T₁ ⊆ T₂) :
    ofSub W T₁ ⊆ ofSub W T₂ :=
  map_subset_map.mpr h

lemma smallMinimals_disjoint {H : Finset (Finset α)} {W T : Finset α} {ℓ : ℕ}
    (h : T ∈ smallMinimals H W ℓ) : Disjoint T W :=
  restrictFamily_disjoint (minimals_subset _ (filter_subset _ _ h))

lemma toSub_card {W S : Finset α} (h : Disjoint S W) :
    (toSub W S).card = S.card := by
  rw [toSub, card_subtype, filter_eq_self.2 fun x hx => disjoint_left.mp h hx]

lemma coverCost_toSub {p : ℝ} (hp0 : 0 ≤ p)
    (F : Finset (Finset α)) (W : Finset α)
    (hF : ∀ S ∈ F, Disjoint S W) :
    coverCost p (F.image (toSub W)) = coverCost p F := by
  apply le_antisymm
  · obtain ⟨G, hG, hGe⟩ := exists_cover_eq_coverCost p F
    let G₀ := G.filter fun T => Disjoint T W
    have hG₀ : Covers G₀ F := by
      intro S hS
      obtain ⟨T, hT, hTS⟩ := mem_generate.mp (hG hS)
      have hdis : Disjoint T W := Disjoint.mono_left hTS (hF S hS)
      exact mem_generate.mpr ⟨T, mem_filter.mpr ⟨hT, hdis⟩, hTS⟩
    have hcov : Covers (G₀.image (toSub W)) (F.image (toSub W)) := by
      intro S' hS'
      obtain ⟨S, hS, rfl⟩ := mem_image.mp hS'
      obtain ⟨T, hT, hTS⟩ := mem_generate.mp (hG₀ hS)
      exact mem_generate.mpr ⟨toSub W T, mem_image.mpr ⟨T, hT, rfl⟩, toSub_subset hTS⟩
    have hinj : Set.InjOn (toSub W) (G₀ : Set (Finset α)) := by
      intro T₁ hT₁ T₂ hT₂ h
      have d1 := (mem_filter.mp (by exact hT₁)).2
      have d2 := (mem_filter.mp (by exact hT₂)).2
      simpa [ofSub_toSub d1, ofSub_toSub d2] using congrArg (ofSub W) h
    have hE : expectation p (G₀.image (toSub W)) = expectation p G₀ := by
      simp only [expectation]
      rw [sum_image hinj]
      refine sum_congr rfl ?_
      intro T hT
      rw [toSub_card (mem_filter.mp hT).2]
    have : coverCost p (F.image (toSub W)) ≤ expectation p G :=
      (coverCost_le_expectation hp0 hcov).trans <|
        (le_of_eq hE).trans (expectation_mono hp0 (filter_subset _ _))
    exact this.trans_eq hGe
  · obtain ⟨G, hG, hGe⟩ := exists_cover_eq_coverCost p (F.image (toSub W))
    have hcov : Covers (G.image (ofSub W)) F := by
      intro S hS
      have hS' : toSub W S ∈ F.image (toSub W) := mem_image.mpr ⟨S, hS, rfl⟩
      obtain ⟨T, hT, hTS⟩ := mem_generate.mp (hG hS')
      have hsub : ofSub W T ⊆ S := by
        have h1 : ofSub W T ⊆ ofSub W (toSub W S) := ofSub_subset hTS
        simpa [ofSub_toSub (hF S hS)] using h1
      exact mem_generate.mpr ⟨ofSub W T, mem_image.mpr ⟨T, hT, rfl⟩, hsub⟩
    have hinj : Function.Injective (ofSub W) :=
      map_injective ⟨Subtype.val, Subtype.val_injective⟩
    have hE : expectation p (G.image (ofSub W)) = expectation p G := by
      simp only [expectation]
      rw [sum_image (Set.injOn_of_injective hinj)]
      simp [ofSub_card]
    exact (coverCost_le_expectation hp0 hcov).trans_eq (hE.trans hGe)

lemma generate_union_mem {H : Finset (Finset α)} {W : Finset α} {ℓ : ℕ}
    {T : Finset {x : α // x ∉ W}}
    (hT : T ∈ generate ((smallMinimals H W ℓ).image (toSub W))) :
    ofSub W T ∪ W ∈ generate H := by
  obtain ⟨U, hU, hUT⟩ := mem_generate.mp hT
  obtain ⟨S', hS', rfl⟩ := mem_image.mp hU
  have hdis := smallMinimals_disjoint hS'
  have hS'sub : S' ⊆ ofSub W T := by
    have : ofSub W (toSub W S') ⊆ ofSub W T := ofSub_subset hUT
    rwa [ofSub_toSub hdis] at this
  have hres : S' ∈ restrictFamily H W :=
    minimals_subset _ (filter_subset _ _ hS')
  obtain ⟨S, hSH, hSeq⟩ := mem_restrictFamily.mp hres
  have hSsub : S ⊆ ofSub W T ∪ W := by
    intro x hxS
    by_cases hxW : x ∈ W
    · exact mem_union.mpr (Or.inr hxW)
    · have : x ∈ S' := by
        have : x ∈ S \ W := mem_sdiff.mpr ⟨hxS, hxW⟩
        rwa [hSeq] at this
      exact mem_union.mpr (Or.inl (hS'sub this))
  exact mem_generate.mpr ⟨S, hSH, hSsub⟩

lemma ofSub_union_card {W : Finset α} (T : Finset {x : α // x ∉ W}) :
    (ofSub W T ∪ W).card = T.card + W.card := by
  have hdis : Disjoint (ofSub W T) W := by
    refine disjoint_left.mpr ?_
    intro x hxT hxW
    rcases mem_map.mp hxT with ⟨⟨_, hx⟩, _, rfl⟩
    exact hx hxW
  rw [card_union_of_disjoint hdis, ofSub_card, Nat.add_comm]

/-- Strong inductive form of Tran–Vu Theorem 2.3. -/
lemma covering_aux (ℓ : ℕ) :
    ∀ {α : Type*} [DecidableEq α] [Fintype α]
      (H : Finset (Finset α)) (p : ℝ),
      ℓ ≤ Fintype.card α → 0 ≤ p → p ≤ 1 → IsBounded H ℓ →
      (1 : ℝ) / 2 - 1 / (2 : ℝ) ^ (ℓ + 2) ≤ coverCost p H →
      ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ + 2)) *
          ((Fintype.card α).choose (coveringLevel p (Fintype.card α) ℓ) : ℝ) ≤
        (((generate H).filter
            (fun S => S.card = coveringLevel p (Fintype.card α) ℓ)).card : ℝ) := by
  induction ℓ using Nat.strong_induction_on with
  | h ℓ ih =>
    intro α _ _ H p hℓN hp0 hp1 hb hf
    by_cases hempty : ∅ ∈ H
    · exact covering_of_empty_mem hempty
    by_cases hlev : Fintype.card α ≤ coveringLevel p (Fintype.card α) ℓ
    · exact covering_of_level_ge_card hp0 hf hlev
    have hℓ : 1 ≤ ℓ := by
      by_contra h0
      have : ℓ = 0 := Nat.le_zero.mp (Nat.le_of_not_gt h0)
      subst this
      have : ∀ S ∈ H, S.card = 0 := fun S hS => Nat.le_zero.mp (hb S hS)
      have hH : H.Nonempty := by
        have hpos : (0 : ℝ) < (1 : ℝ) / 2 - 1 / (2 : ℝ) ^ (0 + 2) := by norm_num
        exact coverCost_pos_imp_nonempty hp0 (lt_of_lt_of_le hpos hf)
      obtain ⟨S, hS⟩ := hH
      have : S = ∅ := card_eq_zero.mp (this S hS)
      exact hempty (this ▸ hS)
    set N := Fintype.card α
    set w := coveringWidth p N
    set ℓ₁ := ⌊((9 : ℝ) / 10) * ℓ⌋₊
    set m := coveringLevel p N ℓ
    have hN : 1 ≤ N := le_trans hℓ hℓN
    have hwN : w ≤ N := by
      by_contra hgt
      have hw' : N + 1 ≤ w := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hgt)
      have h100 : (N : ℝ) + 1 ≤ 100 * p * N := by
        have hwle : (w : ℝ) ≤ 100 * p * N := by
          have := Nat.floor_le (by positivity : (0 : ℝ) ≤ 100 * p * N)
          simpa [w, coveringWidth_eq] using this
        have : (N : ℝ) + 1 ≤ w := by exact_mod_cast hw'
        exact this.trans hwle
      have hlog : (1 : ℝ) ≤ Real.logb 2 (ℓ + 1 : ℝ) := by
        have h2 : (2 : ℝ) ≤ ℓ + 1 := by exact_mod_cast Nat.succ_le_succ hℓ
        have hself : Real.logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
        have hle : Real.logb 2 (2 : ℝ) ≤ Real.logb 2 (ℓ + 1 : ℝ) :=
          (Real.logb_le_logb (b := (2 : ℝ)) (by norm_num) (by norm_num)
            (by positivity)).mpr h2
        simpa [hself] using hle
      have harg : (N : ℝ) < coveringConstant * p * N * Real.logb 2 (ℓ + 1 : ℝ) := by
        have hC : coveringConstant = (1000 : ℝ) := rfl
        have hge : 10 * (100 * p * N)
            ≤ coveringConstant * p * N * Real.logb 2 (ℓ + 1 : ℝ) := by
          rw [hC]
          have : (1000 : ℝ) * p * N * 1
              ≤ 1000 * p * N * Real.logb 2 (ℓ + 1 : ℝ) :=
            mul_le_mul_of_nonneg_left hlog (by positivity)
          convert this using 1
          ring
        have hlt : (N : ℝ) < 10 * (100 * p * N) := by
          have : (N : ℝ) < 10 * (N + 1) := by linarith
          have : 10 * ((N : ℝ) + 1) ≤ 10 * (100 * p * N) :=
            mul_le_mul_of_nonneg_left h100 (by positivity)
          linarith
        exact hlt.trans_le hge
      have : N ≤ m :=
        (Nat.le_floor_iff (coveringLevel_nonneg p N ℓ hp0)).mpr (le_of_lt (by
          simpa [m, coveringLevel] using harg))
      exact hlev this
    have hℓ₁lt : ℓ₁ < ℓ := ell1_lt hℓ
    have hlift := coveringLevel_lift (p := p) (N := N) (w := w) (ℓ := ℓ) hp0 hℓ rfl hwN
    have hℓ₁le : ℓ₁ ≤ N - w := by
      by_contra h
      have hlt : N - w < ℓ₁ := Nat.lt_of_not_ge h
      have hcast : ((N - w : ℕ) : ℝ) = (N : ℝ) - w := Nat.cast_sub hwN
      have hfl : (ℓ₁ : ℝ) ≤ ((9 : ℝ) / 10) * ℓ :=
        Nat.floor_le (by positivity)
      have : (N : ℝ) - w < ((9 : ℝ) / 10) * N := by
        have : ((N - w : ℕ) : ℝ) < ℓ₁ := by exact_mod_cast hlt
        have hℓN' : (ℓ : ℝ) ≤ N := by exact_mod_cast hℓN
        nlinarith [hcast, hfl, hℓN']
      have hltw : (1 : ℝ) / 10 * N < w := by linarith
      have hwle : (w : ℝ) ≤ 100 * p * N := by
        have := Nat.floor_le (by positivity : (0 : ℝ) ≤ 100 * p * N)
        simpa [w, coveringWidth_eq] using this
      have : (1 : ℝ) / 1000 < p := by
        have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.succ_le_iff.mp hN)
        have : (1 : ℝ) / 10 * N < 100 * p * N := hltw.trans_le hwle
        have : (1 : ℝ) / 10 < 100 * p := by
          have := (mul_lt_mul_iff_left₀ hNpos).mp this
          simpa [mul_comm] using this
        linarith
      have hlog : (1 : ℝ) ≤ Real.logb 2 (ℓ + 1 : ℝ) := by
        have h2 : (2 : ℝ) ≤ ℓ + 1 := by exact_mod_cast Nat.succ_le_succ hℓ
        have hself : Real.logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
        have hle : Real.logb 2 (2 : ℝ) ≤ Real.logb 2 (ℓ + 1 : ℝ) :=
          (Real.logb_le_logb (b := (2 : ℝ)) (by norm_num) (by norm_num)
            (by positivity)).mpr h2
        simpa [hself] using hle
      have : (N : ℝ) < coveringConstant * p * N * Real.logb 2 (ℓ + 1 : ℝ) := by
        have hC : coveringConstant = (1000 : ℝ) := rfl
        have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.succ_le_iff.mp hN)
        have h1 : (1 : ℝ) < 1000 * p := by linarith
        have h1' : (1 : ℝ) < 1000 * p * Real.logb 2 (ℓ + 1 : ℝ) :=
          one_lt_mul_of_lt_of_le h1 hlog
        have : N * 1 < N * (1000 * p * Real.logb 2 (ℓ + 1 : ℝ)) :=
          mul_lt_mul_of_pos_left h1' hNpos
        rw [hC]
        convert this using 1 <;> ring
      have : N ≤ m :=
        (Nat.le_floor_iff (coveringLevel_nonneg p N ℓ hp0)).mpr (le_of_lt (by
          simpa [m, coveringLevel] using this))
      exact hlev this
    let Lw := univ.filter (fun W : Finset α => W.card = w)
    let Good := Lw.filter fun W =>
      coverCost p (largeMinimals H W ℓ) ≤ 1 / (2 : ℝ) ^ (ℓ + 2)
    have htail := double_counting_tail hp0 H ℓ hb
    have hgeom := choose_geom_tail_le ℓ
    have hβ :
        (∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ k * ℓ.choose k) *
          (2 : ℝ) ^ (ℓ + 2)
        ≤ (12 / 11) * (1 / (2 : ℝ) ^ (ℓ + 2)) := by
      by_cases h1 : ℓ = 1
      · subst h1
        have hk : kmin 1 = 1 := by unfold kmin; norm_num
        have : ∑ k ∈ Icc (kmin 1) 1, ((1 : ℝ) / 100) ^ k * (1 : ℕ).choose k
            = (1 : ℝ) / 100 := by
          simp [hk, Nat.choose_self]
        rw [this]
        norm_num
      · have h2 : 2 ≤ ℓ := Nat.succ_le_iff.mpr (lt_of_le_of_ne hℓ (Ne.symm h1))
        have hbf := bad_frac_le_of_two ℓ h2
        have : (∑ k ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ k * ℓ.choose k) *
            (2 : ℝ) ^ (ℓ + 2)
            ≤ ((1 : ℝ) / 100) ^ kmin ℓ * 2 ^ ℓ * 2 ^ (ℓ + 2) :=
          mul_le_mul_of_nonneg_right hgeom (by positivity)
        exact this.trans hbf
    set k := coveringLevel p (N - w) ℓ₁
    have hkN : k + w ≤ N :=
      (hlift.trans (Nat.le_of_lt (lt_of_not_ge hlev)))
    have hocc := occupation_mul_le ℓ hℓ hβ
    -- For each good W, apply IH to the restricted family on X \ W.
    have hgood : ∀ W ∈ Good,
        ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) *
            ((N - w).choose k : ℝ) ≤
          (((generate ((smallMinimals H W ℓ).image (toSub W))).filter
              (fun T => T.card = k)).card : ℝ) := by
      intro W hW
      have hWcard : W.card = w := (mem_filter.mp (mem_filter.mp hW).1).2
      have hβcard : Fintype.card {x : α // x ∉ W} = N - w := by
        rw [card_subtype_not_mem, hWcard]
      have hb' : IsBounded ((smallMinimals H W ℓ).image (toSub W)) ℓ₁ := by
        intro T hT
        obtain ⟨S, hS, rfl⟩ := mem_image.mp hT
        have := (IsBounded.smallMinimals (H := H) (W := W) (ℓ := ℓ) (ℓ₁ := ℓ₁) rfl) S hS
        rwa [toSub_card (smallMinimals_disjoint hS)]
      have hf' : (1 : ℝ) / 2 - 1 / (2 : ℝ) ^ (ℓ₁ + 2) ≤
          coverCost p ((smallMinimals H W ℓ).image (toSub W)) := by
        rw [coverCost_toSub hp0 _ _ fun S hS => smallMinimals_disjoint hS]
        have hsm := coverCost_small_ge hp0 H W ℓ
        have hHle := coverCost_le_minimals_restrict hp0 H W
        have hLg : coverCost p (largeMinimals H W ℓ) ≤ 1 / (2 : ℝ) ^ (ℓ + 2) :=
          (mem_filter.mp hW).2
        have h1 : coverCost p (smallMinimals H W ℓ)
            ≥ coverCost p H - 1 / (2 : ℝ) ^ (ℓ + 2) := by linarith
        have h2 : (1 : ℝ) / 2 - 1 / (2 : ℝ) ^ (ℓ + 1)
            ≤ coverCost p H - 1 / (2 : ℝ) ^ (ℓ + 2) := by
          have hexp : (1 : ℝ) / (2 : ℝ) ^ (ℓ + 1) = 2 / (2 : ℝ) ^ (ℓ + 2) := by
            have hpow : (2 : ℝ) ^ (ℓ + 2) = 2 ^ (ℓ + 1) * 2 := pow_succ _ _
            field_simp [hpow]
            ring
          calc
            (1 : ℝ) / 2 - 1 / (2 : ℝ) ^ (ℓ + 1)
                = 1 / 2 - 2 / (2 : ℝ) ^ (ℓ + 2) := by rw [hexp]
            _ = (1 / 2 - 1 / (2 : ℝ) ^ (ℓ + 2)) - 1 / (2 : ℝ) ^ (ℓ + 2) := by ring
            _ ≤ coverCost p H - 1 / (2 : ℝ) ^ (ℓ + 2) :=
              sub_le_sub_right hf _
        have h3 : (1 : ℝ) / (2 : ℝ) ^ (ℓ + 1) ≤ 1 / (2 : ℝ) ^ (ℓ₁ + 2) := by
          have : ℓ₁ + 2 ≤ ℓ + 1 := by omega
          exact one_div_le_one_div_of_le (by positivity)
            (pow_le_pow_right₀ (by norm_num) this)
        linarith
      have := ih ℓ₁ hℓ₁lt ((smallMinimals H W ℓ).image (toSub W)) p
        (by rw [hβcard]; exact hℓ₁le) hp0 hp1 hb' hf'
      simpa [hβcard, k, coveringLevel] using this
    -- Map each good fibre into level `k+w` of `⟨H⟩` and average.
    have hmap : ∀ W ∈ Good,
        (((generate ((smallMinimals H W ℓ).image (toSub W))).filter
            (fun T => T.card = k)).card : ℝ) ≤
          (((generate H).filter (fun S => S.card = k + w ∧ W ⊆ S)).card : ℝ) := by
      intro W hW
      let src := (generate ((smallMinimals H W ℓ).image (toSub W))).filter
        (fun T => T.card = k)
      let tgt := (generate H).filter (fun S => S.card = k + w ∧ W ⊆ S)
      let f := fun T : Finset {x : α // x ∉ W} => ofSub W T ∪ W
      have himg : src.image f ⊆ tgt := by
        intro U hU
        obtain ⟨T, hT, rfl⟩ := mem_image.mp hU
        have ⟨hgen, hkT⟩ := mem_filter.mp hT
        refine mem_filter.mpr ⟨generate_union_mem hgen, ?_⟩
        constructor
        · rw [ofSub_union_card, hkT]
          have : W.card = w := (mem_filter.mp (mem_filter.mp hW).1).2
          rw [this]
        · exact subset_union_right
      have hinj : Set.InjOn f src := by
        intro T₁ h1 T₂ h2 heq
        have d1 : Disjoint (ofSub W T₁) W := by
          refine disjoint_left.mpr ?_
          intro x hxT hxW
          rcases mem_map.mp hxT with ⟨⟨_, hx⟩, _, rfl⟩
          exact hx hxW
        have d2 : Disjoint (ofSub W T₂) W := by
          refine disjoint_left.mpr ?_
          intro x hxT hxW
          rcases mem_map.mp hxT with ⟨⟨_, hx⟩, _, rfl⟩
          exact hx hxW
        have : ofSub W T₁ = ofSub W T₂ := by
          have h1' : ofSub W T₁ = (ofSub W T₁ ∪ W) \ W :=
            (union_sdiff_cancel_right d1).symm
          have h2' : ofSub W T₂ = (ofSub W T₂ ∪ W) \ W :=
            (union_sdiff_cancel_right d2).symm
          rw [h1', h2']
          exact congrArg (fun s : Finset α => s \ W) heq
        exact map_injective ⟨Subtype.val, Subtype.val_injective⟩ this
      have : #src ≤ #tgt :=
        ((card_image_of_injOn hinj).symm.trans_le (card_le_card himg))
      exact Nat.cast_le.mpr this
    let Flev := (generate H).filter (fun S => S.card = k + w)
    let Bad := Lw.filter fun W =>
      1 / (2 : ℝ) ^ (ℓ + 2) < coverCost p (largeMinimals H W ℓ)
    have hpart : Good ∪ Bad = Lw := by
      ext W
      simp only [Good, Bad, mem_union, mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro h
        by_cases hle : coverCost p (largeMinimals H W ℓ) ≤ 1 / (2 : ℝ) ^ (ℓ + 2)
        · exact Or.inl ⟨h, hle⟩
        · exact Or.inr ⟨h, lt_of_not_ge hle⟩
    have hdisGB : Disjoint Good Bad := by
      refine disjoint_left.mpr ?_
      intro W hG hB
      exact (not_le_of_gt (mem_filter.mp hB).2) (mem_filter.mp hG).2
    have hBad : (#Bad : ℝ) * (1 / (2 : ℝ) ^ (ℓ + 2)) ≤
        ∑ W ∈ Lw, coverCost p (largeMinimals H W ℓ) := by
      have h1 : ∑ W ∈ Bad, (1 / (2 : ℝ) ^ (ℓ + 2)) ≤
          ∑ W ∈ Bad, coverCost p (largeMinimals H W ℓ) :=
        sum_le_sum fun W hW => le_of_lt (mem_filter.mp hW).2
      have h2 : ∑ W ∈ Bad, (1 / (2 : ℝ) ^ (ℓ + 2)) =
          (#Bad : ℝ) * (1 / (2 : ℝ) ^ (ℓ + 2)) := by
        simp [sum_const, nsmul_eq_mul]
      have h3 : ∑ W ∈ Bad, coverCost p (largeMinimals H W ℓ) ≤
          ∑ W ∈ Lw, coverCost p (largeMinimals H W ℓ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          fun _ _ _ => coverCost_nonneg hp0 _
      linarith
    have hGood : ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) *
          ((N - w).choose k : ℝ) * (#Good : ℝ) ≤
        ∑ W ∈ Good,
          (((generate ((smallMinimals H W ℓ).image (toSub W))).filter
              (fun T => T.card = k)).card : ℝ) := by
      have h := sum_le_sum hgood
      have hconst :
          ∑ W ∈ Good, ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) * ((N - w).choose k : ℝ) =
            ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) * ((N - w).choose k : ℝ) * (#Good : ℝ) := by
        simp [sum_const, nsmul_eq_mul, mul_comm, mul_assoc]
      rwa [hconst] at h
    have hsum_le : ∑ W ∈ Good,
          (((generate ((smallMinimals H W ℓ).image (toSub W))).filter
              (fun T => T.card = k)).card : ℝ) ≤
        ∑ W ∈ Good, (((generate H).filter
            (fun S => S.card = k + w ∧ W ⊆ S)).card : ℝ) :=
      sum_le_sum hmap
    have hswap : ∑ W ∈ Good,
          #((generate H).filter (fun S => S.card = k + w ∧ W ⊆ S)) =
        ∑ S ∈ Flev, #(Good.filter (fun W => W ⊆ S)) := by
      have hF : ∀ W, (generate H).filter (fun S => S.card = k + w ∧ W ⊆ S) =
          Flev.filter (fun S => W ⊆ S) := by
        intro W
        ext S
        simp [Flev, mem_filter, and_comm, and_left_comm]
      simp_rw [hF]
      simp only [card_eq_sum_ones, sum_filter]
      rw [sum_comm]
    have hchW : ∀ S ∈ Flev, #(Good.filter (fun W => W ⊆ S)) ≤ (k + w).choose w := by
      intro S hS
      have hSc : S.card = k + w := (mem_filter.mp hS).2
      have : Good.filter (fun W => W ⊆ S) ⊆ S.powersetCard w := by
        intro W hW
        have hG := (mem_filter.mp hW).1
        have hsub := (mem_filter.mp hW).2
        have hw : W.card = w := (mem_filter.mp (filter_subset _ _ hG)).2
        exact mem_powersetCard.mpr ⟨hsub, hw⟩
      simpa [card_powersetCard, hSc] using card_le_card this
    have hchoose :
        (N.choose w : ℝ) * ((N - w).choose k : ℝ) =
          (N.choose (k + w) : ℝ) * ((k + w).choose w : ℝ) := by
      have h := Nat.choose_mul (n := N) (k := w + k) (s := w) (Nat.le_add_right w k)
      have hk : k + w = w + k := Nat.add_comm _ _
      have hkw : (w + k - w : ℕ) = k := Nat.add_sub_cancel_left w k
      rw [hk]
      simpa [hkw] using (congrArg (fun n : ℕ => (n : ℝ)) h.symm)
    have hFlev : ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ + 2)) * (N.choose (k + w) : ℝ) ≤
        (#Flev : ℝ) := by
      set β : ℝ :=
        (∑ i ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ i * ℓ.choose i) * (2 : ℝ) ^ (ℓ + 2)
      have h12 : (12 / 11 : ℝ) * (1 / (2 : ℝ) ^ (ℓ + 2)) ≤ 1 := by
        have hpow : (2 : ℝ) ^ (2 : ℕ) ≤ 2 ^ (ℓ + 2) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have h4 : (1 : ℝ) / (2 : ℝ) ^ (ℓ + 2) ≤ 1 / 4 := by
          have : (2 : ℝ) ^ (2 : ℕ) = 4 := by norm_num
          simpa [this] using one_div_le_one_div_of_le (by positivity) hpow
        have hmul : (12 / 11 : ℝ) * (1 / (2 : ℝ) ^ (ℓ + 2)) ≤ (12 / 11) * (1 / 4) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
        have : (12 / 11 : ℝ) * (1 / 4) ≤ 1 := by norm_num
        exact hmul.trans this
      have hβ' : β ≤ (12 / 11 : ℝ) * (1 / (2 : ℝ) ^ (ℓ + 2)) := by
        simpa [β] using hβ
      have hβle : β ≤ 1 := hβ'.trans h12
      have hG : (#Good : ℝ) ≥ (N.choose w : ℝ) * (1 - β) := by
        have hadd : #Good + #Bad = #Lw := by
          rw [← card_union_of_disjoint hdisGB, hpart]
        have hsub : (#Good : ℝ) = (#Lw : ℝ) - (#Bad : ℝ) := by
          have : (#Good : ℝ) + (#Bad : ℝ) = (#Lw : ℝ) := by exact_mod_cast hadd
          linarith
        have hLw : (#Lw : ℝ) = (N.choose w : ℝ) := by
          simp [Lw, N]
        have hBd : (#Bad : ℝ) * (1 / (2 : ℝ) ^ (ℓ + 2)) ≤
            (N.choose w : ℝ) *
              ∑ i ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ i * ℓ.choose i :=
          hBad.trans (by simpa [Lw, w, N] using htail)
        have hpow : (0 : ℝ) < (2 : ℝ) ^ (ℓ + 2) := by positivity
        have hBadle : (#Bad : ℝ) ≤ (N.choose w : ℝ) * β := by
          have hmul : (#Bad : ℝ) * (1 / (2 : ℝ) ^ (ℓ + 2)) * (2 : ℝ) ^ (ℓ + 2)
              ≤ ((N.choose w : ℝ) *
                  ∑ i ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ i * ℓ.choose i) *
                (2 : ℝ) ^ (ℓ + 2) :=
            mul_le_mul_of_nonneg_right hBd (le_of_lt hpow)
          have hL : (#Bad : ℝ) * (1 / (2 : ℝ) ^ (ℓ + 2)) * (2 : ℝ) ^ (ℓ + 2)
              = (#Bad : ℝ) := by
            rw [mul_assoc, one_div_mul_cancel (ne_of_gt hpow), mul_one]
          have hR : ((N.choose w : ℝ) *
                ∑ i ∈ Icc (kmin ℓ) ℓ, ((1 : ℝ) / 100) ^ i * ℓ.choose i) *
              (2 : ℝ) ^ (ℓ + 2)
              = (N.choose w : ℝ) * β := by
            simp only [β]
            ring
          rwa [hL, hR] at hmul
        have hdiff : (N.choose w : ℝ) - (#Bad : ℝ) ≥ (N.choose w : ℝ) * (1 - β) := by
          have : (N.choose w : ℝ) - (#Bad : ℝ) ≥
              (N.choose w : ℝ) - (N.choose w : ℝ) * β :=
            sub_le_sub_left hBadle _
          have hre : (N.choose w : ℝ) - (N.choose w : ℝ) * β =
              (N.choose w : ℝ) * (1 - β) := by ring
          rwa [hre] at this
        rw [hsub, hLw]
        exact hdiff
      have havg : (#Flev : ℝ) * ((k + w).choose w : ℝ) ≥
          ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) * ((N - w).choose k : ℝ) *
            (#Good : ℝ) := by
        have h1 := hGood.trans hsum_le
        have hsw : ∑ W ∈ Good,
              (((generate H).filter (fun S => S.card = k + w ∧ W ⊆ S)).card : ℝ) =
            ∑ S ∈ Flev, ((Good.filter (fun W => W ⊆ S)).card : ℝ) := by
          exact_mod_cast hswap
        have h2 : ∑ S ∈ Flev, ((Good.filter (fun W => W ⊆ S)).card : ℝ) ≤
            ∑ S ∈ Flev, ((k + w).choose w : ℝ) :=
          sum_le_sum fun S hS => Nat.cast_le.mpr (hchW S hS)
        have h3 : ∑ S ∈ Flev, ((k + w).choose w : ℝ) =
            (#Flev : ℝ) * ((k + w).choose w : ℝ) := by
          simp [sum_const, nsmul_eq_mul]
        linarith
      have ha : (0 : ℝ) ≤ (2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2) := by positivity
      have hCnk : (0 : ℝ) ≤ ((N - w).choose k : ℝ) := Nat.cast_nonneg _
      have hCkw : (0 : ℝ) ≤ ((k + w).choose w : ℝ) := Nat.cast_nonneg _
      have hCnkw : (0 : ℝ) ≤ (N.choose (k + w) : ℝ) := Nat.cast_nonneg _
      have hocc' :
          (2 / 3 + 1 / (2 : ℝ) ^ (ℓ + 2)) ≤
            ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) * (1 - β) := by
        simpa [β, kmin, ℓ₁] using hocc
      have hstep : ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) *
            ((N - w).choose k : ℝ) * (#Good : ℝ)
          ≥ ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) * ((N - w).choose k : ℝ) *
              ((N.choose w : ℝ) * (1 - β)) :=
        mul_le_mul_of_nonneg_left hG (mul_nonneg ha hCnk)
      have hcomb : (#Flev : ℝ) * ((k + w).choose w : ℝ) ≥
          ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ + 2)) * (N.choose (k + w) : ℝ) *
            ((k + w).choose w : ℝ) := by
        have hL : (#Flev : ℝ) * ((k + w).choose w : ℝ)
            ≥ ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) * (1 - β) *
              (N.choose (k + w) : ℝ) * ((k + w).choose w : ℝ) := by
          calc
            (#Flev : ℝ) * ((k + w).choose w : ℝ)
                ≥ ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) *
                    ((N - w).choose k : ℝ) * (#Good : ℝ) := havg
            _ ≥ ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) *
                    ((N - w).choose k : ℝ) * ((N.choose w : ℝ) * (1 - β)) := hstep
            _ = ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) * (1 - β) *
                    ((N.choose w : ℝ) * ((N - w).choose k : ℝ)) := by ring
            _ = ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) * (1 - β) *
                    ((N.choose (k + w) : ℝ) * ((k + w).choose w : ℝ)) := by
              rw [hchoose]
            _ = ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) * (1 - β) *
                    (N.choose (k + w) : ℝ) * ((k + w).choose w : ℝ) := by ring
        have hR :
            ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ₁ + 2)) * (1 - β) *
                (N.choose (k + w) : ℝ) * ((k + w).choose w : ℝ)
              ≥ ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ + 2)) * (N.choose (k + w) : ℝ) *
                ((k + w).choose w : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hocc' hCnkw) hCkw
        exact (ge_iff_le.mp hR).trans (ge_iff_le.mp hL)
      have hpos' : (0 : ℝ) < ((k + w).choose w : ℝ) :=
        Nat.cast_pos.mpr (Nat.choose_pos (Nat.le_add_left w k))
      exact (mul_le_mul_iff_of_pos_right hpos').mp (ge_iff_le.mp hcomb)
    have hmfrac : ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ + 2)) * (N.choose m : ℝ) ≤
        (((generate H).filter (fun S => S.card = m)).card : ℝ) := by
      have hle : k + w ≤ m := hlift
      have hkw : k + w ≤ N := hkN
      have hch0 : 0 < (N.choose (k + w) : ℝ) :=
        Nat.cast_pos.mpr (Nat.choose_pos hkw)
      have hch1 : 0 < (N.choose m : ℝ) :=
        Nat.cast_pos.mpr (Nat.choose_pos (le_of_lt (lt_of_not_ge hlev)))
      have hfrac := generate_level_frac_le (α := α) H hle (le_of_lt (lt_of_not_ge hlev))
      have hfrac' : (#Flev : ℝ) / (N.choose (k + w) : ℝ) ≤
          (((generate H).filter (fun S => S.card = m)).card : ℝ) / (N.choose m : ℝ) := by
        simpa [Flev, N] using hfrac
      have hα : ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ + 2)) ≤
          (#Flev : ℝ) / (N.choose (k + w) : ℝ) :=
        (le_div_iff₀ hch0).mpr hFlev
      exact (le_div_iff₀ hch1).mp (hα.trans hfrac')
    simpa [m, N] using hmfrac

end

end KahnKalai

/- ===== Source module: KahnKalai/ParkPham.lean ===== -/

/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch
-/

/-!
Tran–Vu Remark 2.5: binomial mixture of level fractions plus a `2^{-X}` Markov
tail, yielding Park–Pham from the covering theorem.
-/

open Finset

namespace KahnKalai

variable {α : Type*} [DecidableEq α] [Fintype α]

noncomputable section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

def parkPhamK : ℝ := 100000

lemma parkPhamK_pos : 0 < parkPhamK := by
  simp [parkPhamK]

lemma parkPhamK_ge_two : (2 : ℝ) ≤ parkPhamK := by
  simp [parkPhamK]
  norm_num

lemma logb_two_ell_ge_one {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    (1 : ℝ) ≤ Real.logb 2 (ℓ : ℝ) := by
  have h2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hself : Real.logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
  have hle : Real.logb 2 (2 : ℝ) ≤ Real.logb 2 (ℓ : ℝ) :=
    (Real.logb_le_logb (b := (2 : ℝ)) (by norm_num) (by norm_num)
      (by positivity)).mpr h2
  simpa [hself] using hle

lemma ell_add_one_le_sq {ℓ : ℕ} (hℓ : 2 ≤ ℓ) : ℓ + 1 ≤ ℓ ^ 2 := by
  have h1 : 1 ≤ ℓ := le_trans (Nat.le_succ 1) hℓ
  calc
    ℓ + 1 ≤ ℓ + ℓ := Nat.add_le_add_left h1 _
    _ = 2 * ℓ := by ring
    _ ≤ ℓ * ℓ := Nat.mul_le_mul_right ℓ hℓ
    _ = ℓ ^ 2 := (Nat.pow_two ℓ).symm

lemma logb_ell_add_one_le_two {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    Real.logb 2 (ℓ + 1 : ℝ) ≤ 2 * Real.logb 2 (ℓ : ℝ) := by
  have hx : 0 < (ℓ + 1 : ℝ) := by exact_mod_cast Nat.succ_pos ℓ
  have hy : 0 < (ℓ : ℝ) ^ 2 := by positivity
  have hle : (ℓ + 1 : ℝ) ≤ (ℓ : ℝ) ^ 2 := by exact_mod_cast (ell_add_one_le_sq hℓ)
  have hlog : Real.logb 2 (ℓ + 1 : ℝ) ≤ Real.logb 2 ((ℓ : ℝ) ^ 2) :=
    (Real.logb_le_logb (b := (2 : ℝ)) (by norm_num) hx hy).mpr hle
  have hpow : Real.logb 2 ((ℓ : ℝ) ^ 2) = 2 * Real.logb 2 (ℓ : ℝ) := by
    simpa [pow_two] using Real.logb_pow (2 : ℝ) (ℓ : ℝ) 2
  rwa [hpow] at hlog

lemma logb_min_add_one_le {ℓ N : ℕ} (hℓ : 2 ≤ ℓ) :
    Real.logb 2 ((min ℓ N) + 1 : ℝ) ≤ 2 * Real.logb 2 (ℓ : ℝ) := by
  have hle : ((min ℓ N) + 1 : ℝ) ≤ (ℓ + 1 : ℝ) := by
    exact_mod_cast Nat.add_le_add_right (min_le_left ℓ N) 1
  have hx : 0 < ((min ℓ N) + 1 : ℝ) := by exact_mod_cast Nat.succ_pos _
  have hy : 0 < (ℓ + 1 : ℝ) := by exact_mod_cast Nat.succ_pos ℓ
  have := (Real.logb_le_logb (b := (2 : ℝ)) (by norm_num) hx hy).mpr hle
  exact this.trans (logb_ell_add_one_le_two hℓ)

lemma coveringLevel_cast_le (p : ℝ) (N ℓ : ℕ) (hp0 : 0 ≤ p) :
    (coveringLevel p N ℓ : ℝ)
      ≤ coveringConstant * p * N * Real.logb 2 (ℓ + 1 : ℝ) :=
  Nat.floor_le (coveringLevel_nonneg p N ℓ hp0)

lemma IsBounded.min_card {F : Finset (Finset α)} {ℓ : ℕ} (hb : IsBounded F ℓ) :
    IsBounded F (min ℓ (Fintype.card α)) :=
  fun S hS => le_min (hb S hS) (card_le_univ S)

/-- Binomial point mass `C(N,k) p^k (1-p)^{N-k}`. -/
def binomProb (N : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (N.choose k : ℝ) * p ^ k * (1 - p) ^ (N - k)

lemma binomProb_nonneg {N : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    0 ≤ binomProb N p k :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
    (pow_nonneg (sub_nonneg.mpr hp1) _)

lemma binom_sum (N : ℕ) (p : ℝ) :
    ∑ k ∈ range (N + 1), binomProb N p k = (p + (1 - p)) ^ N := by
  have h := add_pow p (1 - p) N
  simp only [binomProb]
  convert h.symm using 1
  exact sum_congr rfl fun k _ => by ring

lemma binom_sum_one (N : ℕ) (p : ℝ) :
    ∑ k ∈ range (N + 1), binomProb N p k = 1 := by
  rw [binom_sum, add_sub_cancel, one_pow]

lemma binom_mgf_half (N : ℕ) (p : ℝ) :
    ∑ k ∈ range (N + 1), ((1 : ℝ) / 2) ^ k * binomProb N p k
      = (1 - p / 2) ^ N := by
  have h := add_pow (p / 2) (1 - p) N
  have hre : p / 2 + (1 - p) = 1 - p / 2 := by ring
  have hterm : ∀ k ∈ range (N + 1),
      ((1 : ℝ) / 2) ^ k * binomProb N p k
        = (p / 2) ^ k * (1 - p) ^ (N - k) * N.choose k := by
    intro k _
    simp only [binomProb]
    ring
  calc
    ∑ k ∈ range (N + 1), ((1 : ℝ) / 2) ^ k * binomProb N p k
        = ∑ k ∈ range (N + 1),
            (p / 2) ^ k * (1 - p) ^ (N - k) * N.choose k :=
      sum_congr rfl hterm
    _ = (p / 2 + (1 - p)) ^ N := by
      convert h.symm using 1
    _ = (1 - p / 2) ^ N := by rw [hre]

lemma binom_left_tail (N m : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hm : m ≤ N) :
    ∑ k ∈ range m, binomProb N p k
      ≤ (2 : ℝ) ^ m * (1 - p / 2) ^ N := by
  have hsub : range m ⊆ range (N + 1) :=
    range_subset_range.mpr (Nat.le_succ_of_le hm)
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hhalf1 : (1 : ℝ) / 2 ≤ 1 := by norm_num
  have hle : ∀ k ∈ range m, ((1 : ℝ) / 2) ^ m ≤ ((1 : ℝ) / 2) ^ k := by
    intro k hk
    exact pow_le_pow_of_le_one hhalf hhalf1 (le_of_lt (mem_range.mp hk))
  have hweight :
      ((1 : ℝ) / 2) ^ m * ∑ k ∈ range m, binomProb N p k
        ≤ ∑ k ∈ range m, ((1 : ℝ) / 2) ^ k * binomProb N p k := by
    have h : ∑ k ∈ range m, ((1 : ℝ) / 2) ^ m * binomProb N p k
        ≤ ∑ k ∈ range m, ((1 : ℝ) / 2) ^ k * binomProb N p k :=
      sum_le_sum fun k hk =>
        mul_le_mul_of_nonneg_right (hle k hk) (binomProb_nonneg (N := N) hp0 hp1 k)
    simpa [mul_sum] using h
  have hpart :
      ∑ k ∈ range m, ((1 : ℝ) / 2) ^ k * binomProb N p k
        ≤ ∑ k ∈ range (N + 1), ((1 : ℝ) / 2) ^ k * binomProb N p k :=
    sum_le_sum_of_subset_of_nonneg hsub fun k _ _ =>
      mul_nonneg (pow_nonneg hhalf _) (binomProb_nonneg hp0 hp1 k)
  have hmgf := binom_mgf_half N p
  have hbound := hweight.trans (hpart.trans_eq hmgf)
  have hcancel : (2 : ℝ) ^ m * (((1 : ℝ) / 2) ^ m *
        ∑ k ∈ range m, binomProb N p k)
      = ∑ k ∈ range m, binomProb N p k := by
    have : (2 : ℝ) ^ m * ((1 : ℝ) / 2) ^ m = 1 := by
      rw [← mul_pow]
      norm_num
    rw [← mul_assoc, this, one_mul]
  have := mul_le_mul_of_nonneg_left hbound (pow_nonneg (by positivity : (0 : ℝ) ≤ 2) m)
  rwa [hcancel] at this

lemma one_sub_half_p_le_exp {p : ℝ} (_hp0 : 0 ≤ p) :
    1 - p / 2 ≤ Real.exp (-(p / 2)) := by
  have h := Real.add_one_le_exp (-(p / 2))
  have hre : -(p / 2) + 1 = 1 - p / 2 := by ring
  rwa [hre] at h

lemma two_pow_le_exp (m : ℕ) : (2 : ℝ) ^ m ≤ Real.exp (m : ℝ) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
  have hpow : (2 : ℝ) ^ m ≤ Real.exp 1 ^ m :=
    pow_le_pow_left₀ (by positivity) h2 m
  have : Real.exp 1 ^ m = Real.exp (m : ℝ) := by
    have h := (Real.exp_nat_mul (1 : ℝ) m).symm
    simpa [mul_one] using h
  rwa [this] at hpow

lemma exp_neg_four_le_one_div_five : Real.exp (-4) ≤ 1 / 5 := by
  have he1 : (2 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
  have hexp2 : Real.exp 2 = Real.exp 1 ^ 2 := by
    have h := Real.exp_nat_mul (1 : ℝ) 2
    simpa [mul_one] using h
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have hpow : (2 : ℝ) ^ 2 ≤ Real.exp 1 ^ 2 :=
      pow_le_pow_left₀ (by positivity) he1 2
    have hsq : (2 : ℝ) ^ 2 = 4 := by norm_num
    rwa [hsq, ← hexp2] at hpow
  have hexp4 : Real.exp 4 = Real.exp 2 ^ 2 := by
    have h := Real.exp_nat_mul (2 : ℝ) 2
    have hmul : ((2 : ℕ) : ℝ) * 2 = (4 : ℝ) := by norm_num
    rw [hmul] at h
    exact h
  have he4 : (16 : ℝ) ≤ Real.exp 4 := by
    have hpow : (4 : ℝ) ^ 2 ≤ Real.exp 2 ^ 2 :=
      pow_le_pow_left₀ (by positivity) he2 2
    have hsq : (4 : ℝ) ^ 2 = 16 := by norm_num
    rwa [hsq, ← hexp4] at hpow
  have h5 : (5 : ℝ) ≤ Real.exp 4 := le_trans (by norm_num) he4
  have hneg : Real.exp (-4) = 1 / Real.exp 4 := by
    rw [Real.exp_neg, one_div]
  rwa [hneg, one_div_le_one_div (Real.exp_pos _) (by positivity)]

lemma binom_left_tail_of_mean {N m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hmN : m ≤ N) (hmμ : (m : ℝ) ≤ (N * p) / 4) (hμ : (16 : ℝ) ≤ N * p) :
    ∑ k ∈ range m, binomProb N p k ≤ 1 / 5 := by
  have htail := binom_left_tail N m hp0 hp1 hmN
  have hbase := one_sub_half_p_le_exp hp0
  have hnn : 0 ≤ 1 - p / 2 := by
    have : p / 2 ≤ 1 := by
      have : p ≤ 2 := hp1.trans (by norm_num)
      linarith
    linarith
  have hpow : (1 - p / 2) ^ N ≤ Real.exp (-(p / 2)) ^ N :=
    pow_le_pow_left₀ hnn hbase N
  have hexp : Real.exp (-(p / 2)) ^ N = Real.exp (-(N * p / 2)) := by
    have h := (Real.exp_nat_mul (-(p / 2)) N).symm
    have : (N : ℝ) * (-(p / 2)) = -(N * p / 2) := by ring
    simpa [this] using h
  have h2 := two_pow_le_exp m
  have hprod : (2 : ℝ) ^ m * (1 - p / 2) ^ N
      ≤ Real.exp (m : ℝ) * Real.exp (-(N * p / 2)) :=
    mul_le_mul h2 (hpow.trans_eq hexp) (pow_nonneg hnn _) (Real.exp_nonneg _)
  have hsum : Real.exp (m : ℝ) * Real.exp (-(N * p / 2))
      = Real.exp ((m : ℝ) - N * p / 2) := by
    rw [← Real.exp_add]
    ring_nf
  have hle : Real.exp ((m : ℝ) - N * p / 2) ≤ Real.exp (-((N * p) / 4)) := by
    apply Real.exp_le_exp.mpr
    have : (m : ℝ) - N * p / 2 ≤ N * p / 4 - N * p / 2 :=
      sub_le_sub_right hmμ _
    have : N * p / 4 - N * p / 2 = -((N * p) / 4) := by ring
    linarith
  have h16 : Real.exp (-((N * p) / 4)) ≤ Real.exp (-4) :=
    Real.exp_le_exp.mpr (by linarith [hμ])
  exact (htail.trans (hprod.trans_eq hsum)).trans
    (hle.trans (h16.trans exp_neg_four_le_one_div_five))

lemma measure_one (S : Finset α) :
    measure (1 : ℝ) S = if S = univ then 1 else 0 := by
  simp only [measure, one_pow]
  by_cases h : S = univ
  · simp [h, card_univ]
  · have hlt : S.card < Fintype.card α := by
      have hle : S.card ≤ Fintype.card α := card_le_univ S
      have hne : S.card ≠ Fintype.card α := by
        intro hc
        exact h (S.card_eq_iff_eq_univ.mp hc)
      omega
    have hz : (0 : ℝ) ^ (Fintype.card α - S.card) = 0 :=
      zero_pow (Nat.sub_pos_of_lt hlt).ne'
    simp [h, hz]

lemma measureFamily_one (G : Finset (Finset α)) :
    measureFamily (1 : ℝ) G = if univ ∈ G then 1 else 0 := by
  classical
  simp only [measureFamily]
  have hterm : ∀ S ∈ G, measure (1 : ℝ) S = if S = univ then 1 else 0 :=
    fun S _ => measure_one S
  rw [sum_congr rfl hterm, sum_ite_eq']

lemma measureFamily_univ (p : ℝ) :
    measureFamily p (univ : Finset (Finset α)) = (p + (1 - p)) ^ Fintype.card α := by
  simpa [measureFamily, measure] using
    (Fintype.sum_pow_mul_eq_add_pow α p (1 - p))

lemma measureFamily_univ_one {p : ℝ} :
    measureFamily p (univ : Finset (Finset α)) = 1 := by
  rw [measureFamily_univ, add_sub_cancel, one_pow]

lemma measureFamily_generate_eq (p : ℝ) (F : Finset (Finset α)) :
    measureFamily p (generate F) =
      ∑ k ∈ range (Fintype.card α + 1),
        (((generate F).filter (fun S => S.card = k)).card : ℝ) *
          p ^ k * (1 - p) ^ (Fintype.card α - k) := by
  set N := Fintype.card α
  simp only [measureFamily, measure]
  have hmap : ∀ S ∈ generate F, S.card ∈ range (N + 1) :=
    fun S _ => mem_range.mpr (Nat.lt_succ_of_le (card_le_univ S))
  have hfib :=
    (sum_fiberwise_of_maps_to (g := fun S : Finset α => S.card) (t := range (N + 1))
      hmap (fun S => p ^ S.card * (1 - p) ^ (N - S.card))).symm
  rw [hfib]
  refine sum_congr rfl fun k _ => ?_
  have hconst : ∀ S ∈ (generate F).filter (fun S => S.card = k),
      p ^ S.card * (1 - p) ^ (N - S.card) = p ^ k * (1 - p) ^ (N - k) := by
    intro S hS
    have hc : S.card = k := (mem_filter.mp hS).2
    simp [hc]
  rw [sum_congr rfl hconst, sum_const, nsmul_eq_mul]
  ring

lemma threshold_le_of_measure {F : Finset (Finset α)} {p : ℝ}
    (hp : p ∈ Set.Icc 0 1)
    (h : (1 : ℝ) / 2 ≤ measureFamily p (generate F)) :
    threshold F ≤ p :=
  csInf_le ⟨0, fun _ hx => hx.1.1⟩ ⟨hp, h⟩

lemma threshold_le_one_of_nonempty {F : Finset (Finset α)} (hF : F.Nonempty) :
    threshold F ≤ 1 := by
  have huniv : univ ∈ generate F := by
    obtain ⟨S, hS⟩ := hF
    exact mem_generate.mpr ⟨S, hS, subset_univ _⟩
  have hμ : (1 : ℝ) / 2 ≤ measureFamily 1 (generate F) := by
    simp [measureFamily_one, huniv]
    norm_num
  exact threshold_le_of_measure ⟨zero_le_one, le_rfl⟩ hμ

lemma threshold_eq_zero_of_empty_mem {F : Finset (Finset α)} (h : ∅ ∈ F) :
    threshold F = 0 := by
  have hgen := generate_eq_univ_of_empty_mem h
  have h0 : (0 : ℝ) ∈ {p : ℝ | p ∈ Set.Icc 0 1 ∧
      1 / 2 ≤ measureFamily p (generate F)} := by
    refine ⟨⟨le_rfl, zero_le_one⟩, ?_⟩
    rw [hgen, measureFamily_univ_one]
    norm_num
  refine le_antisymm ?_ (le_csInf ⟨_, h0⟩ fun x hx => hx.1.1)
  exact csInf_le ⟨0, fun x hx => hx.1.1⟩ h0

lemma threshold_eq_zero_of_empty {F : Finset (Finset α)} (hF : F = ∅) :
    threshold F = 0 := by
  subst hF
  have hempty : {p : ℝ | p ∈ Set.Icc 0 1 ∧
      1 / 2 ≤ measureFamily p (generate (∅ : Finset (Finset α)))} = ∅ := by
    ext p
    constructor
    · intro hp
      have : measureFamily p (generate (∅ : Finset (Finset α))) = 0 := by
        simp [generate_empty, measureFamily]
      have : (1 : ℝ) / 2 ≤ 0 := hp.2.trans_eq this
      linarith
    · intro hp
      exact hp.elim
  unfold threshold
  rw [hempty, Real.sInf_empty]

lemma expectationThreshold_nonneg (F : Finset (Finset α)) :
    0 ≤ expectationThreshold F :=
  Real.sSup_nonneg fun _ hx => hx.1.1

lemma expectationThreshold_le_one (F : Finset (Finset α)) :
    expectationThreshold F ≤ 1 := by
  by_cases h : {p : ℝ | p ∈ Set.Icc 0 1 ∧ coverCost p F ≤ 1 / 2}.Nonempty
  · exact csSup_le h fun x hx => hx.1.2
  · have hempty : {p : ℝ | p ∈ Set.Icc 0 1 ∧ coverCost p F ≤ 1 / 2} = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp h
    unfold expectationThreshold
    rw [hempty, Real.sSup_empty]
    norm_num

lemma coverCost_gt_half_of_gt_q {F : Finset (Finset α)} {p : ℝ}
    (hp : p ∈ Set.Icc 0 1) (h : expectationThreshold F < p) :
    (1 : ℝ) / 2 < coverCost p F := by
  have hbdd : BddAbove {q : ℝ | q ∈ Set.Icc 0 1 ∧ coverCost q F ≤ 1 / 2} :=
    ⟨1, fun x hx => hx.1.2⟩
  have : p ∉ {q : ℝ | q ∈ Set.Icc 0 1 ∧ coverCost q F ≤ 1 / 2} := fun hpS =>
    (le_csSup hbdd hpS).not_gt h
  exact lt_of_not_ge fun hle => this ⟨hp, hle⟩

lemma empty_mem_of_q_eq_zero {F : Finset (Finset α)}
    (h : expectationThreshold F = 0) : ∅ ∈ F := by
  by_contra hF
  set N := Fintype.card α
  set r : ℝ := (1 : ℝ) / 2 ^ (N + 2)
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 := by
    have : (1 : ℝ) ≤ 2 ^ (N + 2) := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    exact (div_le_one (by positivity)).mpr this
  have hterm : ∀ S ∈ F, r ^ S.card ≤ r := by
    intro S hS
    have hne : S ≠ ∅ := fun he => hF (he ▸ hS)
    have hc : 1 ≤ S.card := Nat.pos_of_ne_zero (mt card_eq_zero.mp hne)
    have := pow_le_pow_of_le_one (le_of_lt hr0) hr1 hc
    simpa using this
  have hE : expectation r F ≤ (1 : ℝ) / 4 := by
    have hsum : expectation r F ≤ ∑ _S ∈ F, r := sum_le_sum hterm
    have hconst : ∑ _S ∈ F, r = (#F : ℝ) * r := by
      simp [sum_const, nsmul_eq_mul]
    have hFcard : (#F : ℝ) ≤ 2 ^ N := by
      have : F.card ≤ Fintype.card (Finset α) := card_le_univ F
      have h2 : Fintype.card (Finset α) = 2 ^ N := by
        simp [Fintype.card_finset, N]
      exact_mod_cast this.trans_eq h2
    have hmul : (#F : ℝ) * r ≤ 2 ^ N * r :=
      mul_le_mul_of_nonneg_right hFcard (le_of_lt hr0)
    have hval : (2 : ℝ) ^ N * r = 1 / 4 := by
      simp only [r]
      rw [pow_add]
      have : (2 : ℝ) ^ 2 = 4 := by norm_num
      rw [this]
      field_simp
    linarith
  have hcost : coverCost r F ≤ 1 / 2 :=
    (coverCost_le_expectation (le_of_lt hr0) (covers_self F)).trans
      (hE.trans (by norm_num))
  have hrS : r ∈ {q : ℝ | q ∈ Set.Icc 0 1 ∧ coverCost q F ≤ 1 / 2} :=
    ⟨⟨le_of_lt hr0, hr1⟩, hcost⟩
  have hbdd : BddAbove {q : ℝ | q ∈ Set.Icc 0 1 ∧ coverCost q F ≤ 1 / 2} :=
    ⟨1, fun x hx => hx.1.2⟩
  have : r ≤ expectationThreshold F := le_csSup hbdd hrS
  have : r ≤ 0 := by
    simpa [h] using this
  exact (not_le_of_gt hr0) this

lemma sdiff_range_binom (N m : ℕ) (p : ℝ) (hm : m ≤ N) :
    ∑ k ∈ range (N + 1) \ range m, binomProb N p k
      = 1 - ∑ k ∈ range m, binomProb N p k := by
  have hsub : range m ⊆ range (N + 1) :=
    range_subset_range.mpr (Nat.le_succ_of_le hm)
  have hU : range m ∪ (range (N + 1) \ range m) = range (N + 1) :=
    union_sdiff_of_subset hsub
  have hdis : Disjoint (range m) (range (N + 1) \ range m) :=
    disjoint_sdiff
  have hsum := sum_union (s₁ := range m) (s₂ := range (N + 1) \ range m)
    (f := binomProb N p) hdis
  have h1 := binom_sum_one N p
  rw [hU] at hsum
  linarith

lemma measureFamily_ge_occupation {F : Finset (Finset α)} {p : ℝ} {m : ℕ}
    {α0 : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hm : m ≤ Fintype.card α)
    (_hα0 : 0 ≤ α0)
    (hocc : α0 * ((Fintype.card α).choose m : ℝ) ≤
      (((generate F).filter (fun S => S.card = m)).card : ℝ)) :
    α0 * ∑ k ∈ range (Fintype.card α + 1) \ range m,
          binomProb (Fintype.card α) p k
      ≤ measureFamily p (generate F) := by
  set N := Fintype.card α
  have hsum := measureFamily_generate_eq p F
  have hterm : ∀ k ∈ range (N + 1) \ range m,
      α0 * binomProb N p k ≤
        (((generate F).filter (fun S => S.card = k)).card : ℝ) *
          p ^ k * (1 - p) ^ (N - k) := by
    intro k hk
    have hkN : k ∈ range (N + 1) := (mem_sdiff.mp hk).1
    have hkm : m ≤ k := le_of_not_gt fun hlt =>
      (mem_sdiff.mp hk).2 (mem_range.mpr hlt)
    have hkN' : k ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hkN)
    have hch0 : 0 < (N.choose m : ℝ) :=
      Nat.cast_pos.mpr (Nat.choose_pos hm)
    have hfrac := generate_level_frac_le (α := α) F hkm hkN'
    have hαm : α0 ≤
        (((generate F).filter (fun S => S.card = m)).card : ℝ) /
          (N.choose m : ℝ) :=
      (le_div_iff₀ hch0).mpr hocc
    have hch1 : 0 < (N.choose k : ℝ) :=
      Nat.cast_pos.mpr (Nat.choose_pos hkN')
    have hαk : α0 ≤
        (((generate F).filter (fun S => S.card = k)).card : ℝ) /
          (N.choose k : ℝ) :=
      hαm.trans (by simpa [N] using hfrac)
    have hmul : α0 * (N.choose k : ℝ) ≤
        (((generate F).filter (fun S => S.card = k)).card : ℝ) :=
      (le_div_iff₀ hch1).mp hαk
    have hnn : 0 ≤ p ^ k * (1 - p) ^ (N - k) :=
      mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)
    have : α0 * ((N.choose k : ℝ) * p ^ k * (1 - p) ^ (N - k))
        ≤ (((generate F).filter (fun S => S.card = k)).card : ℝ) *
            p ^ k * (1 - p) ^ (N - k) := by
      calc
        α0 * ((N.choose k : ℝ) * p ^ k * (1 - p) ^ (N - k))
            = (α0 * N.choose k) * (p ^ k * (1 - p) ^ (N - k)) := by ring
        _ ≤ (((generate F).filter (fun S => S.card = k)).card : ℝ) *
              (p ^ k * (1 - p) ^ (N - k)) :=
          mul_le_mul_of_nonneg_right hmul hnn
        _ = (((generate F).filter (fun S => S.card = k)).card : ℝ) *
              p ^ k * (1 - p) ^ (N - k) := by ring
    simpa [binomProb] using this
  have hleft :
      α0 * ∑ k ∈ range (N + 1) \ range m, binomProb N p k
        ≤ ∑ k ∈ range (N + 1) \ range m,
            (((generate F).filter (fun S => S.card = k)).card : ℝ) *
              p ^ k * (1 - p) ^ (N - k) := by
    rw [mul_sum]
    exact sum_le_sum hterm
  have hrest :
      ∑ k ∈ range (N + 1) \ range m,
          (((generate F).filter (fun S => S.card = k)).card : ℝ) *
            p ^ k * (1 - p) ^ (N - k)
        ≤ ∑ k ∈ range (N + 1),
            (((generate F).filter (fun S => S.card = k)).card : ℝ) *
              p ^ k * (1 - p) ^ (N - k) :=
    sum_le_sum_of_subset_of_nonneg sdiff_subset fun k _ _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
        (pow_nonneg (sub_nonneg.mpr hp1) _)
  have := hleft.trans hrest
  simpa [hsum, N] using this

/-- Explicit Park–Pham bound. -/
lemma park_pham_bound {α : Type} [DecidableEq α] [Fintype α]
    (F : Finset (Finset α)) (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (_hb : IsBounded F ℓ) :
    threshold F ≤ parkPhamK * expectationThreshold F * Real.logb 2 (ℓ : ℝ) := by
  set q := expectationThreshold F
  set N := Fintype.card α
  have hq0 : 0 ≤ q := expectationThreshold_nonneg F
  have hlog : (1 : ℝ) ≤ Real.logb 2 (ℓ : ℝ) := logb_two_ell_ge_one hℓ
  have hKlog : 0 ≤ parkPhamK * q * Real.logb 2 (ℓ : ℝ) :=
    mul_nonneg (mul_nonneg (le_of_lt parkPhamK_pos) hq0)
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) hlog)
  by_cases hempty : ∅ ∈ F
  · simpa [threshold_eq_zero_of_empty_mem hempty] using hKlog
  by_cases hF0 : F = ∅
  · simpa [threshold_eq_zero_of_empty hF0] using hKlog
  have hFne : F.Nonempty := nonempty_iff_ne_empty.mpr hF0
  have hqpos : 0 < q := by
    have : q ≠ 0 := fun hz => hempty (empty_mem_of_q_eq_zero hz)
    exact lt_of_le_of_ne hq0 this.symm
  have hth1 : threshold F ≤ 1 := threshold_le_one_of_nonempty hFne
  by_cases h2q : (1 : ℝ) ≤ 2 * q
  · have hmain : (1 : ℝ) ≤ parkPhamK * q * Real.logb 2 (ℓ : ℝ) := by
      have h2 : (1 : ℝ) ≤ 2 * q * Real.logb 2 (ℓ : ℝ) := by
        calc
          (1 : ℝ) = 1 * 1 := by ring
          _ ≤ (2 * q) * Real.logb 2 (ℓ : ℝ) :=
            mul_le_mul h2q hlog (by norm_num)
              (le_trans (by norm_num : (0 : ℝ) ≤ 1) h2q)
      have hK : (2 : ℝ) * q * Real.logb 2 (ℓ : ℝ)
          ≤ parkPhamK * q * Real.logb 2 (ℓ : ℝ) := by
        have : (2 : ℝ) ≤ parkPhamK := parkPhamK_ge_two
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right this hq0)
          (le_trans (by norm_num : (0 : ℝ) ≤ 1) hlog)
      exact h2.trans hK
    exact hth1.trans hmain
  set p : ℝ := 2 * q
  have hp0 : 0 ≤ p := mul_nonneg (by norm_num) hq0
  have hp1 : p < 1 := lt_of_not_ge h2q
  have hpI : p ∈ Set.Icc 0 1 := ⟨hp0, le_of_lt hp1⟩
  have hpq : q < p := by
    change q < 2 * q
    linarith [hqpos]
  have hcost : (1 : ℝ) / 2 < coverCost p F := coverCost_gt_half_of_gt_q hpI hpq
  set ℓ' := min ℓ N
  have hℓ'N : ℓ' ≤ N := min_le_right _ _
  have hb' : IsBounded F ℓ' := IsBounded.min_card _hb
  have hf' : (1 : ℝ) / 2 - 1 / (2 : ℝ) ^ (ℓ' + 2) ≤ coverCost p F := by
    have : (1 : ℝ) / 2 - 1 / (2 : ℝ) ^ (ℓ' + 2) ≤ 1 / 2 := by
      have : 0 ≤ (1 : ℝ) / (2 : ℝ) ^ (ℓ' + 2) := by positivity
      linarith
    exact this.trans (le_of_lt hcost)
  have hcov := covering_aux ℓ' F p hℓ'N hp0 (le_of_lt hp1) hb' hf'
  set m := coveringLevel p N ℓ'
  have hmle : (m : ℝ) ≤ 1000 * p * N * Real.logb 2 (ℓ' + 1 : ℝ) := by
    simpa [m, coveringConstant] using coveringLevel_cast_le p N ℓ' hp0
  have hlog' := logb_min_add_one_le (N := N) hℓ
  by_cases hmN : N < m
  · have hNpos : (0 : ℝ) < N := by
      have hpos : 0 < N := Nat.pos_of_ne_zero fun hN0 => by
        have hm0 : m = 0 := by
          have hNcast : (N : ℝ) = 0 := by exact_mod_cast hN0
          have : coveringLevel p N ℓ' = 0 := by
            simp [coveringLevel, hNcast]
          simpa [m] using this
        omega
      exact_mod_cast hpos
    have hml : (N : ℝ) < 1000 * p * N * Real.logb 2 (ℓ' + 1 : ℝ) :=
      (Nat.cast_lt.mpr hmN).trans_le hmle
    have hre : (1000 : ℝ) * p * N * Real.logb 2 (ℓ' + 1 : ℝ)
        = N * (1000 * p * Real.logb 2 (ℓ' + 1 : ℝ)) := by ring
    have h1 : (1 : ℝ) < 1000 * p * Real.logb 2 (ℓ' + 1 : ℝ) := by
      have : (N : ℝ) * 1 < N * (1000 * p * Real.logb 2 (ℓ' + 1 : ℝ)) := by
        rw [mul_one, ← hre]
        exact hml
      exact (mul_lt_mul_iff_of_pos_left hNpos).mp this
    have h1' : (1 : ℝ) < 2000 * q * Real.logb 2 (ℓ' + 1 : ℝ) := by
      have hre' : (1000 : ℝ) * p * Real.logb 2 (ℓ' + 1 : ℝ)
          = 2000 * q * Real.logb 2 (ℓ' + 1 : ℝ) := by
        simp only [p]
        ring
      rwa [hre'] at h1
    have h1'' : (1 : ℝ) < 4000 * q * Real.logb 2 (ℓ : ℝ) := by
      have hstep : (1 : ℝ) < 2000 * q * (2 * Real.logb 2 (ℓ : ℝ)) :=
        h1'.trans_le (mul_le_mul_of_nonneg_left hlog'
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2000) hq0))
      have hre'' : (2000 : ℝ) * q * (2 * Real.logb 2 (ℓ : ℝ))
          = 4000 * q * Real.logb 2 (ℓ : ℝ) := by ring
      rwa [hre''] at hstep
    have hK : (4000 : ℝ) ≤ parkPhamK := by
      simp [parkPhamK]
      norm_num
    have : (1 : ℝ) < parkPhamK * q * Real.logb 2 (ℓ : ℝ) := by
      have := mul_le_mul_of_nonneg_right hK
        (mul_nonneg hq0 (le_trans (by norm_num : (0 : ℝ) ≤ 1) hlog))
      have hre' : (4000 : ℝ) * q * Real.logb 2 (ℓ : ℝ)
          = 4000 * (q * Real.logb 2 (ℓ : ℝ)) := by ring
      have hreK : parkPhamK * q * Real.logb 2 (ℓ : ℝ)
          = parkPhamK * (q * Real.logb 2 (ℓ : ℝ)) := by ring
      have : (4000 : ℝ) * q * Real.logb 2 (ℓ : ℝ)
          ≤ parkPhamK * q * Real.logb 2 (ℓ : ℝ) := by
        rw [hre', hreK]
        exact mul_le_mul_of_nonneg_right hK
          (mul_nonneg hq0 (le_trans (by norm_num : (0 : ℝ) ≤ 1) hlog))
      exact h1''.trans_le this
    exact hth1.trans this.le
  have hmN' : m ≤ N := le_of_not_gt hmN
  by_cases hm0 : m = 0
  · have hch : (N.choose m : ℝ) = 1 := by simp [hm0]
    have hα : (2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ' + 2) ≤
        (((generate F).filter (fun S => S.card = m)).card : ℝ) := by
      simpa [hch, m, N] using hcov
    have hpos : (1 : ℝ) / 2 < (2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ' + 2) := by
      have : 0 < (1 : ℝ) / (2 : ℝ) ^ (ℓ' + 2) := by positivity
      linarith
    have hcardpos : 0 < ((generate F).filter (fun S => S.card = m)).card := by
      have : (0 : ℝ) <
          (((generate F).filter (fun S => S.card = m)).card : ℝ) :=
        lt_trans (by norm_num : (0 : ℝ) < 1 / 2) (hpos.trans_le hα)
      exact Nat.cast_pos.mp this
    obtain ⟨S, hS⟩ := card_pos.mp hcardpos
    have ⟨hgen, hc⟩ := mem_filter.mp hS
    have hSemp : S = ∅ := card_eq_zero.mp (hc.trans hm0)
    have : ∅ ∈ generate F := by rwa [← hSemp]
    obtain ⟨T, hT, hTsub⟩ := mem_generate.mp this
    have : T = ∅ := subset_empty.mp hTsub
    exact (hempty (this ▸ hT)).elim
  have hmpos : 1 ≤ m := Nat.pos_of_ne_zero hm0
  by_cases hbig : (1 : ℝ) ≤ parkPhamK * q * Real.logb 2 (ℓ : ℝ)
  · exact hth1.trans hbig
  set p' : ℝ := parkPhamK * q * Real.logb 2 (ℓ : ℝ)
  have hp'0 : 0 ≤ p' := hKlog
  have hp'1 : p' < 1 := lt_of_not_ge hbig
  have hp'I : p' ∈ Set.Icc 0 1 := ⟨hp'0, le_of_lt hp'1⟩
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
  have hml1 : (1 : ℝ) ≤ 1000 * p * N * Real.logb 2 (ℓ' + 1 : ℝ) :=
    hm1.trans hmle
  have h4000 : (1 : ℝ) ≤ 4000 * q * N * Real.logb 2 (ℓ : ℝ) := by
    have h2000 : (1 : ℝ) ≤ 2000 * q * N * Real.logb 2 (ℓ' + 1 : ℝ) := by
      have hre : (1000 : ℝ) * p * N * Real.logb 2 (ℓ' + 1 : ℝ)
          = 2000 * q * N * Real.logb 2 (ℓ' + 1 : ℝ) := by
        simp only [p]
        ring
      rwa [hre] at hml1
    have hmul : (2000 : ℝ) * q * N * Real.logb 2 (ℓ' + 1 : ℝ)
        ≤ 2000 * q * N * (2 * Real.logb 2 (ℓ : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog'
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2000) hq0)
          (Nat.cast_nonneg N))
    have hre : (2000 : ℝ) * q * N * (2 * Real.logb 2 (ℓ : ℝ))
        = 4000 * q * N * Real.logb 2 (ℓ : ℝ) := by ring
    exact h2000.trans (hmul.trans_eq hre)
  have hμ : (16 : ℝ) ≤ N * p' := by
    have hK : (64000 : ℝ) ≤ parkPhamK := by
      simp [parkPhamK]
      norm_num
    have : (16 : ℝ) * (4000 * q * N * Real.logb 2 (ℓ : ℝ))
        ≤ parkPhamK * q * N * Real.logb 2 (ℓ : ℝ) := by
      have hreL : (16 : ℝ) * (4000 * q * N * Real.logb 2 (ℓ : ℝ))
          = 64000 * (q * N * Real.logb 2 (ℓ : ℝ)) := by ring
      have hreR : parkPhamK * q * N * Real.logb 2 (ℓ : ℝ)
          = parkPhamK * (q * N * Real.logb 2 (ℓ : ℝ)) := by ring
      rw [hreL, hreR]
      exact mul_le_mul_of_nonneg_right hK
        (mul_nonneg (mul_nonneg hq0 (Nat.cast_nonneg N))
          (le_trans (by norm_num : (0 : ℝ) ≤ 1) hlog))
    have : (16 : ℝ) ≤ 16 * (4000 * q * N * Real.logb 2 (ℓ : ℝ)) := by
      have := mul_le_mul_of_nonneg_left h4000 (by positivity : (0 : ℝ) ≤ 16)
      simpa using this
    have hre : parkPhamK * q * N * Real.logb 2 (ℓ : ℝ) = N * p' := by
      simp only [p']
      ring
    linarith
  have hmμ : (m : ℝ) ≤ (N * p') / 4 := by
    have hm4000 : (m : ℝ) ≤ 4000 * q * N * Real.logb 2 (ℓ : ℝ) := by
      have hm2000 : (m : ℝ) ≤ 2000 * q * N * Real.logb 2 (ℓ' + 1 : ℝ) := by
        have hre : (1000 : ℝ) * p * N * Real.logb 2 (ℓ' + 1 : ℝ)
            = 2000 * q * N * Real.logb 2 (ℓ' + 1 : ℝ) := by
          simp only [p]
          ring
        rwa [hre] at hmle
      have hmul : (2000 : ℝ) * q * N * Real.logb 2 (ℓ' + 1 : ℝ)
          ≤ 2000 * q * N * (2 * Real.logb 2 (ℓ : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog'
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2000) hq0)
            (Nat.cast_nonneg N))
      have hre : (2000 : ℝ) * q * N * (2 * Real.logb 2 (ℓ : ℝ))
          = 4000 * q * N * Real.logb 2 (ℓ : ℝ) := by ring
      exact hm2000.trans (hmul.trans_eq hre)
    have : (4000 : ℝ) * q * N * Real.logb 2 (ℓ : ℝ) ≤ (N * p') / 4 := by
      have hK : (16000 : ℝ) ≤ parkPhamK := by
        simp [parkPhamK]
        norm_num
      have hreL : (4 : ℝ) * (4000 * q * N * Real.logb 2 (ℓ : ℝ))
          = 16000 * (q * N * Real.logb 2 (ℓ : ℝ)) := by ring
      have hreR : parkPhamK * q * N * Real.logb 2 (ℓ : ℝ)
          = parkPhamK * (q * N * Real.logb 2 (ℓ : ℝ)) := by ring
      have : (4 : ℝ) * (4000 * q * N * Real.logb 2 (ℓ : ℝ))
          ≤ N * p' := by
        have : 16000 * (q * N * Real.logb 2 (ℓ : ℝ))
            ≤ parkPhamK * (q * N * Real.logb 2 (ℓ : ℝ)) :=
          mul_le_mul_of_nonneg_right hK
            (mul_nonneg (mul_nonneg hq0 (Nat.cast_nonneg N))
              (le_trans (by norm_num : (0 : ℝ) ≤ 1) hlog))
        have : parkPhamK * (q * N * Real.logb 2 (ℓ : ℝ)) = N * p' := by
          simp only [p']
          ring
        linarith
      linarith
    linarith
  have htail : ∑ k ∈ range m, binomProb N p' k ≤ 1 / 5 :=
    binom_left_tail_of_mean (N := N) (m := m) (p := p') hp'0 (le_of_lt hp'1)
      hmN' hmμ hμ
  have hα0 : (0 : ℝ) ≤ (2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ' + 2) := by positivity
  have hocc :
      ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ' + 2)) * (N.choose m : ℝ) ≤
        (((generate F).filter (fun S => S.card = m)).card : ℝ) := by
    simpa [m, N] using hcov
  have hge := measureFamily_ge_occupation (F := F) (p := p') (m := m)
      (α0 := (2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ' + 2))
      hp'0 (le_of_lt hp'1) hmN' hα0 hocc
  have hmass :
      (4 : ℝ) / 5 ≤ ∑ k ∈ range (N + 1) \ range m, binomProb N p' k := by
    have := sdiff_range_binom N m p' hmN'
    linarith [htail]
  have hμF : (1 : ℝ) / 2 ≤ measureFamily p' (generate F) := by
    have hmul : ((2 : ℝ) / 3) * (4 / 5) ≤
        ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ' + 2)) *
          ∑ k ∈ range (N + 1) \ range m, binomProb N p' k := by
      have h1 : (2 : ℝ) / 3 ≤ (2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ' + 2) := by
        have : 0 ≤ (1 : ℝ) / (2 : ℝ) ^ (ℓ' + 2) := by positivity
        linarith
      exact mul_le_mul h1 hmass (by positivity) (by positivity)
    have h815 : ((2 : ℝ) / 3) * (4 / 5) = 8 / 15 := by norm_num
    have : (8 : ℝ) / 15 ≤ measureFamily p' (generate F) := by
      rw [← h815]
      exact hmul.trans hge
    have : (1 : ℝ) / 2 ≤ 8 / 15 := by norm_num
    exact this.trans ‹(8 : ℝ) / 15 ≤ measureFamily p' (generate F)›
  have : threshold F ≤ p' := threshold_le_of_measure hp'I hμF
  simpa [p'] using this

end

end KahnKalai

/- ===== Source module: Solution.lean ===== -/

/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch
-/

/-!
# Proved solution

Comparator matches the identically named declarations in `Challenge.lean`.
The compared definitions live in `KahnKalai.Basic` and are repeated
verbatim in `Challenge.lean` (Challenge does not import this library).
-/

namespace KahnKalai

theorem covering_theorem {α : Type*} [DecidableEq α] [Fintype α]
    (H : Finset (Finset α)) (ℓ : ℕ) (p : ℝ)
    (hℓ : ℓ ≤ Fintype.card α)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hb : IsBounded H ℓ)
    (hf : (1 : ℝ) / 2 - 1 / (2 : ℝ) ^ (ℓ + 2) ≤ coverCost p H) :
    ((2 : ℝ) / 3 + 1 / (2 : ℝ) ^ (ℓ + 2)) *
        ((Fintype.card α).choose (coveringLevel p (Fintype.card α) ℓ) : ℝ) ≤
      (((generate H).filter
          (fun S => S.card = coveringLevel p (Fintype.card α) ℓ)).card : ℝ) :=
  covering_aux ℓ H p hℓ hp0 hp1 hb hf

theorem park_pham :
    ∃ K : ℝ, 0 < K ∧
      ∀ {α : Type} [DecidableEq α] [Fintype α]
        (F : Finset (Finset α)) (ℓ : ℕ),
        2 ≤ ℓ → IsBounded F ℓ →
        threshold F ≤ K * expectationThreshold F * Real.logb 2 (ℓ : ℝ) :=
  ⟨parkPhamK, parkPhamK_pos, park_pham_bound⟩

end KahnKalai

/- ===== Source module: Paper.lean ===== -/

/-
Additional formalization of the supplied Park--Pham paper (arXiv:2203.17207v2).
Released under the Apache License, Version 2.0; see LICENSE.

Scope: the exact minimum-fragment definition and equation (16), the
deterministic iteration, and the main theorem with the paper's minimal-edge
parameter. The final quantitative theorem uses the separate Tran--Vu proof
in Solution.lean. It is NOT a verification of the paper's entire randomized
iteration or its asymptotic error estimate (20).
-/

open Finset

namespace ParkPhamPaper

open KahnKalai

variable {α : Type} [DecidableEq α] [Fintype α]

/-- Section 2.1: a minimum-cardinality `(S,W)`-fragment. -/
def IsMinimumFragment (H : Finset (Finset α)) (S W T : Finset α) : Prop :=
  (∃ S' ∈ H, S' ⊆ W ∪ S ∧ T = S' \ W) ∧
  ∀ R ∈ H, R ⊆ W ∪ S → T.card ≤ (R \ W).card

theorem exists_minimumFragment {H : Finset (Finset α)} {S W : Finset α}
    (hS : S ∈ H) : ∃ T, IsMinimumFragment H S W T := by
  classical
  let C := H.filter (fun R => R ⊆ W ∪ S)
  have hC : C.Nonempty := ⟨S, mem_filter.mpr ⟨hS, subset_union_right⟩⟩
  obtain ⟨R, hR, hmin⟩ := C.exists_min_image (fun R => (R \ W).card) hC
  refine ⟨R \ W, ⟨R, (mem_filter.mp hR).1, (mem_filter.mp hR).2, rfl⟩, ?_⟩
  intro R' hR' hsub
  exact hmin R' (mem_filter.mpr ⟨hR', hsub⟩)

theorem fragment_subset {H : Finset (Finset α)} {S W T : Finset α}
    (h : IsMinimumFragment H S W T) : T ⊆ S := by
  obtain ⟨R, _, hsub, rfl⟩ := h.1
  intro x hx
  exact (mem_union.mp (hsub (mem_sdiff.mp hx).1)).resolve_left (mem_sdiff.mp hx).2

theorem fragment_disjoint {H : Finset (Finset α)} {S W T : Finset α}
    (h : IsMinimumFragment H S W T) : Disjoint T W := by
  obtain ⟨R, _, _, rfl⟩ := h.1
  exact disjoint_sdiff_self_left

theorem fragment_union_contains_edge {H : Finset (Finset α)} {S W T : Finset α}
    (h : IsMinimumFragment H S W T) : W ∪ T ∈ generate H := by
  obtain ⟨R, hR, _, rfl⟩ := h.1
  refine mem_generate.mpr ⟨R, hR, ?_⟩
  intro x hx
  by_cases hxW : x ∈ W
  · exact mem_union_left _ hxW
  · exact mem_union_right _ (mem_sdiff.mpr ⟨hx, hxW⟩)

/-- Equation (16): every edge in `W ∪ T` contains the minimum fragment `T`.
No uniqueness of the minimum fragment and no tie-breaking assumption is used. -/
theorem equation_16 {H : Finset (Finset α)} {S W T R : Finset α}
    (h : IsMinimumFragment H S W T) (hR : R ∈ H) (hRsub : R ⊆ W ∪ T) :
    T ⊆ R := by
  have hRT : R \ W ⊆ T := by
    intro x hx
    exact (mem_union.mp (hRsub (mem_sdiff.mp hx).1)).resolve_left (mem_sdiff.mp hx).2
  have hRW : R ⊆ W ∪ S :=
    hRsub.trans (union_subset_union_right (fragment_subset h))
  have hEq : R \ W = T := eq_of_subset_of_card_le hRT (h.2 R hR hRW)
  rw [← hEq]
  exact sdiff_subset

/-- A cardinality-minimum fragment is also an inclusion-minimal residual edge. -/
theorem fragment_mem_minimals {H : Finset (Finset α)} {S W T : Finset α}
    (h : IsMinimumFragment H S W T) : T ∈ minimals (restrictFamily H W) := by
  obtain ⟨R, hR, _, hT⟩ := h.1
  refine mem_minimals.mpr ⟨mem_restrictFamily.mpr ⟨R, hR, hT.symm⟩, ?_⟩
  intro U hU hUT
  obtain ⟨Q, hQ, rfl⟩ := mem_restrictFamily.mp hU
  have hQsub : Q ⊆ W ∪ T := by
    intro x hx
    by_cases hxW : x ∈ W
    · exact mem_union_left _ hxW
    · exact mem_union_right _ (hUT (mem_sdiff.mpr ⟨hx, hxW⟩))
  have hTS := fragment_subset h
  exact eq_of_subset_of_card_le hUT
    (h.2 Q hQ (hQsub.trans (union_subset_union_right hTS)))

noncomputable section

/-- Choose one of the minimum fragments, with arbitrary tie-breaking. -/
def fragment (H : Finset (Finset α)) (W S : Finset α) : Finset α :=
  if hS : S ∈ H then Classical.choose (exists_minimumFragment (W := W) hS) else ∅

theorem fragment_spec {H : Finset (Finset α)} {S W : Finset α} (hS : S ∈ H) :
    IsMinimumFragment H S W (fragment H W S) := by
  simp only [fragment, dif_pos hS]
  exact Classical.choose_spec (exists_minimumFragment (W := W) hS)

def fragments (H : Finset (Finset α)) (W : Finset α) : Finset (Finset α) :=
  H.image (fragment H W)

theorem mem_fragments_minimal {H : Finset (Finset α)} {W T : Finset α}
    (hT : T ∈ fragments H W) : T ∈ minimals (restrictFamily H W) := by
  obtain ⟨S, hS, rfl⟩ := mem_image.mp hT
  exact fragment_mem_minimals (fragment_spec hS)

theorem mem_fragments_disjoint {H : Finset (Finset α)} {W T : Finset α}
    (hT : T ∈ fragments H W) : Disjoint T W := by
  obtain ⟨S, hS, rfl⟩ := mem_image.mp hT
  exact fragment_disjoint (fragment_spec hS)

/-- The pairs in equation (15), for the actual chosen minimum fragments. -/
def fragmentPairs (H : Finset (Finset α)) (w m : ℕ) : Finset (Finset α × Finset α) :=
  univ.filter (fun P => P.1.card = w ∧ P.2.card = m ∧ P.2 ∈ fragments H P.1)

theorem mem_fragmentPairs {H : Finset (Finset α)} {w m : ℕ} {P : Finset α × Finset α} :
    P ∈ fragmentPairs H w m ↔ P.1.card = w ∧ P.2.card = m ∧ P.2 ∈ fragments H P.1 := by
  simp [fragmentPairs]

/- The next two counting proofs adapt the finite-fiber argument from
Dan Clemens Posch's KahnKalai/DoubleCount.lean (Apache-2.0), applying it to
the paper's chosen minimum fragments instead of Tran--Vu's large minimals. -/
theorem fragment_fiber_card_le {H : Finset (Finset α)} {ell : ℕ}
    (hb : IsBounded H ell) (Z : Finset α) (m : ℕ) :
    #{T : Finset α | T.card = m ∧ T ⊆ Z ∧ T ∈ fragments H (Z \ T)} ≤ ell.choose m := by
  classical
  let Fiber := univ.filter (fun T : Finset α =>
    T.card = m ∧ T ⊆ Z ∧ T ∈ fragments H (Z \ T))
  by_cases hF : Fiber.Nonempty
  · obtain ⟨T₀, hT₀⟩ := hF
    have h₀ : T₀.card = m ∧ T₀ ⊆ Z ∧ T₀ ∈ fragments H (Z \ T₀) :=
      (mem_filter.mp hT₀).2
    have hres := minimals_subset _ (mem_fragments_minimal h₀.2.2)
    obtain ⟨R, hRH, hRZ, _⟩ := exists_mem_subset_union hres h₀.2.1
    have hsub : Fiber ⊆ R.powersetCard m := by
      intro T hT
      have ht : T.card = m ∧ T ⊆ Z ∧ T ∈ fragments H (Z \ T) :=
        (mem_filter.mp hT).2
      exact mem_powersetCard.mpr
        ⟨subset_of_minimal_fiber (mem_fragments_minimal ht.2.2) hRH hRZ, ht.1⟩
    have hc : #Fiber ≤ R.card.choose m := by
      simpa only [card_powersetCard] using card_le_card hsub
    exact hc.trans (Nat.choose_le_choose m (hb R hRH))
  · have hEmpty : Fiber = ∅ := not_nonempty_iff_eq_empty.mp hF
    change #Fiber ≤ ell.choose m
    simp [hEmpty]

/-- The counting part of Lemma 2.1, stronger than its `2^ell` bound:
there are at most `choose(n,w+m) * choose(ell,m)` distinct pairs `(W,T)`. -/
theorem fragmentPairs_card_le {H : Finset (Finset α)} {ell w m : ℕ}
    (hb : IsBounded H ell) :
    #(fragmentPairs H w m) ≤ (Fintype.card α).choose (w + m) * ell.choose m := by
  classical
  let L := univ.filter (fun Z : Finset α => Z.card = w + m)
  have htoL : ∀ P ∈ fragmentPairs H w m, P.1 ∪ P.2 ∈ L := by
    intro P hP
    obtain ⟨hw, hm, hT⟩ := mem_fragmentPairs.mp hP
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    rw [card_union_of_disjoint (mem_fragments_disjoint hT).symm, hw, hm]
  have hcount := card_eq_sum_card_fiberwise (s := fragmentPairs H w m) (t := L)
    (f := fun P : Finset α × Finset α => P.1 ∪ P.2) (fun P hP => htoL P hP)
  have hfib : ∀ Z ∈ L,
      #{P ∈ fragmentPairs H w m | P.1 ∪ P.2 = Z} ≤ ell.choose m := by
    intro Z _
    let f : Finset α → Finset α × Finset α := fun T => (Z \ T, T)
    let Fiber := univ.filter (fun T : Finset α =>
      T.card = m ∧ T ⊆ Z ∧ T ∈ fragments H (Z \ T))
    have himage : {P ∈ fragmentPairs H w m | P.1 ∪ P.2 = Z} ⊆ Fiber.image f := by
      intro P hP
      obtain ⟨hPair, hZ⟩ := mem_filter.mp hP
      obtain ⟨_, hm, hT⟩ := mem_fragmentPairs.mp hPair
      have hW : P.1 = Z \ P.2 := by
        rw [← hZ, union_sdiff_cancel_right (mem_fragments_disjoint hT).symm]
      refine mem_image.mpr ⟨P.2, mem_filter.mpr ⟨mem_univ _, hm, ?_, ?_⟩, ?_⟩
      · rw [← hZ]
        exact subset_union_right
      · simpa only [hW] using hT
      · exact Prod.ext hW.symm rfl
    exact ((card_le_card himage).trans card_image_le).trans (fragment_fiber_card_le hb Z m)
  have hsum : #(fragmentPairs H w m) ≤ ∑ _Z ∈ L, ell.choose m := by
    rw [hcount]
    exact sum_le_sum hfib
  simpa [L, card_level, sum_const, nsmul_eq_mul] using hsum

/-- Recovering Step 1's binomial-ratio bound, with `w+1` to avoid division by zero. -/
theorem weighted_fragmentPairs_bound {H : Finset (Finset α)} {ell w m : ℕ}
    {p : ℝ} (hp : 0 ≤ p) (hb : IsBounded H ell) :
    p ^ m * (#(fragmentPairs H w m) : ℝ) ≤
      ((Fintype.card α).choose w : ℝ) *
        ((Fintype.card α : ℝ) * p / (w + 1)) ^ m * (ell.choose m : ℝ) := by
  have hc : (#(fragmentPairs H w m) : ℝ) ≤
      ((Fintype.card α).choose (w + m) : ℝ) * (ell.choose m : ℝ) := by
    exact_mod_cast fragmentPairs_card_le (w := w) (m := m) hb
  have hr := choose_add_le (Fintype.card α) w m
  calc
    p ^ m * (#(fragmentPairs H w m) : ℝ)
        ≤ p ^ m * (((Fintype.card α).choose (w + m) : ℝ) * (ell.choose m : ℝ)) :=
      mul_le_mul_of_nonneg_left hc (pow_nonneg hp _)
    _ ≤ p ^ m * ((((Fintype.card α).choose w : ℝ) *
          ((Fintype.card α : ℝ) / (w + 1)) ^ m) * (ell.choose m : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg _)) (pow_nonneg hp _)
    _ = _ := by rw [div_pow, div_pow, mul_pow]; ring

/-- The integer cutoff `r` can be chosen as `ceil (0.9 * ell)` in the paper. -/
def largeFragments (H : Finset (Finset α)) (W : Finset α) (r : ℕ) :=
  (fragments H W).filter (fun T => r ≤ T.card)

def smallFragments (H : Finset (Finset α)) (W : Finset α) (r : ℕ) :=
  (fragments H W).filter (fun T => T.card < r)

theorem fragment_step_covers (H : Finset (Finset α)) (W : Finset α) (r : ℕ) :
    Covers (largeFragments H W r ∪ smallFragments H W r) H := by
  intro S hS
  have hmem : fragment H W S ∈ fragments H W := mem_image.mpr ⟨S, hS, rfl⟩
  refine mem_generate.mpr ⟨fragment H W S, ?_, fragment_subset (fragment_spec hS)⟩
  by_cases hr : r ≤ (fragment H W S).card
  · exact mem_union_left _ (mem_filter.mpr ⟨hmem, hr⟩)
  · exact mem_union_right _ (mem_filter.mpr ⟨hmem, Nat.lt_of_not_ge hr⟩)

theorem small_fragment_lifts {H : Finset (Finset α)} {W T : Finset α} {r : ℕ}
    (hT : T ∈ smallFragments H W r) : W ∪ T ∈ generate H := by
  obtain ⟨S, hS, rfl⟩ := mem_image.mp (mem_filter.mp hT).1
  exact fragment_union_contains_edge (fragment_spec hS)

theorem small_fragment_card {H : Finset (Finset α)} {W T : Finset α} {r : ℕ}
    (hT : T ∈ smallFragments H W r) : T.card < r :=
  (mem_filter.mp hT).2

def residual (H : Finset (Finset α)) (W : ℕ → Finset α) (r : ℕ → ℕ) :
    ℕ → Finset (Finset α)
  | 0 => H
  | i + 1 => smallFragments (residual H W r i) (W i) (r i)

def accumulatedCover (H : Finset (Finset α)) (W : ℕ → Finset α) (r : ℕ → ℕ) :
    ℕ → Finset (Finset α)
  | 0 => ∅
  | i + 1 => accumulatedCover H W r i ∪ largeFragments (residual H W r i) (W i) (r i)

def selected (W : ℕ → Finset α) : ℕ → Finset α
  | 0 => ∅
  | i + 1 => selected W i ∪ W i

/-- Iterated form of (8): the accumulated cover and the surviving edges cover H. -/
theorem residual_cover_invariant (H : Finset (Finset α)) (W : ℕ → Finset α)
    (r : ℕ → ℕ) (i : ℕ) :
    Covers (accumulatedCover H W r i ∪ residual H W r i) H := by
  induction i with
  | zero => simpa [accumulatedCover, residual] using covers_self H
  | succ i ih =>
    intro S hS
    obtain ⟨T, hT, hTS⟩ := mem_generate.mp (ih hS)
    rcases mem_union.mp hT with hOld | hNew
    · exact mem_generate.mpr ⟨T,
        mem_union_left _ (mem_union_left _ hOld), hTS⟩
    · obtain ⟨U, hU, hUT⟩ := mem_generate.mp
        (fragment_step_covers (residual H W r i) (W i) (r i) hNew)
      refine mem_generate.mpr ⟨U, ?_, hUT.trans hTS⟩
      rcases mem_union.mp hU with hLarge | hSmall
      · exact mem_union_left _ (mem_union_right _ hLarge)
      · exact mem_union_right _ hSmall

/-- Equation (9), proved for the actual chosen-fragment recursion. -/
theorem residual_lift_invariant (H : Finset (Finset α)) (W : ℕ → Finset α)
    (r : ℕ → ℕ) (i : ℕ) :
    ∀ T ∈ residual H W r i, selected W i ∪ T ∈ generate H := by
  induction i with
  | zero =>
    intro T hT
    simpa [selected, residual] using mem_generate.mpr ⟨T, hT, Subset.rfl⟩
  | succ i ih =>
    intro T hT
    obtain ⟨R, hR, hRT⟩ := mem_generate.mp (small_fragment_lifts hT)
    have hLift := ih R hR
    apply subset_mem_generate (T := selected W (i + 1) ∪ T) ?_ hLift
    intro x hx
    rcases mem_union.mp hx with hxOld | hxR
    · exact mem_union_left _ (mem_union_left _ hxOld)
    · rcases mem_union.mp (hRT hxR) with hxW | hxT
      · exact mem_union_left _ (mem_union_right _ hxW)
      · exact mem_union_right _ hxT

/-- Proposition 2.3. The hypothesis is the terminal cardinality bound from (10).
The random laws and the quantitative cost estimates are not hypotheses here. -/
theorem proposition_2_3 (H : Finset (Finset α)) (W : ℕ → Finset α)
    (r : ℕ → ℕ) (k : ℕ)
    (hterminal : ∀ T ∈ residual H W r k, T.card < 1) :
    selected W k ∈ generate H ∨ Covers (accumulatedCover H W r k) H := by
  by_cases hE : (∅ : Finset α) ∈ residual H W r k
  · left
    simpa using residual_lift_invariant H W r k ∅ hE
  · right
    have hEmpty : residual H W r k = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro T hT
      have hc : T.card = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (hterminal T hT))
      have hT0 : T = ∅ := card_eq_zero.mp hc
      exact hE (hT0 ▸ hT)
    simpa [hEmpty] using residual_cover_invariant H W r k

/-- In particular, a final integer cutoff at most one supplies the terminal bound. -/
theorem proposition_2_3_of_final_cutoff (H : Finset (Finset α)) (W : ℕ → Finset α)
    (r : ℕ → ℕ) (k : ℕ) (hk : r k ≤ 1) :
    selected W (k + 1) ∈ generate H ∨ Covers (accumulatedCover H W r (k + 1)) H := by
  apply proposition_2_3 H W r (k + 1)
  intro T hT
  exact (small_fragment_card hT).trans_le hk

/-- The paper's definition (1)--(2). -/
def IsPSmall (p : ℝ) (H : Finset (Finset α)) : Prop :=
  ∃ G : Finset (Finset α), Covers G H ∧ expectation p G ≤ 1 / 2

theorem isPSmall_iff_coverCost {p : ℝ} (hp : 0 ≤ p) (H : Finset (Finset α)) :
    IsPSmall p H ↔ coverCost p H ≤ 1 / 2 := by
  constructor
  · rintro ⟨G, hG, hc⟩
    exact (coverCost_le_expectation hp hG).trans hc
  · intro hc
    obtain ⟨G, hG, heq⟩ := exists_cover_eq_coverCost p H
    exact ⟨G, hG, heq.trans_le hc⟩

/-- The expectation threshold defined directly by the existence of a cheap cover. -/
def paperExpectationThreshold (F : Finset (Finset α)) : ℝ :=
  sSup {p : ℝ | p ∈ Set.Icc 0 1 ∧ IsPSmall p F}

theorem paperExpectationThreshold_eq (F : Finset (Finset α)) :
    paperExpectationThreshold F = expectationThreshold F := by
  unfold paperExpectationThreshold expectationThreshold
  congr 1
  ext p
  constructor <;> rintro ⟨hp, h⟩
  · exact ⟨hp, (isPSmall_iff_coverCost hp.1 F).mp h⟩
  · exact ⟨hp, (isPSmall_iff_coverCost hp.1 F).mpr h⟩

/-- The deterministic implication behind (21) and Markov's inequality. -/
theorem success_of_cheap_cover (H : Finset (Finset α)) (W : ℕ → Finset α)
    (r : ℕ → ℕ) (k : ℕ) (p : ℝ)
    (hterminal : ∀ T ∈ residual H W r k, T.card < 1)
    (hnot : ¬ IsPSmall p H)
    (hcost : expectation p (accumulatedCover H W r k) ≤ 1 / 2) :
    selected W k ∈ generate H := by
  rcases proposition_2_3 H W r k hterminal with hSuccess | hCover
  · exact hSuccess
  · exact False.elim (hnot ⟨accumulatedCover H W r k, hCover, hcost⟩)

/-- Upward closure is unchanged upon passing to the minimal members. -/
theorem generate_minimals (F : Finset (Finset α)) : generate (minimals F) = generate F := by
  apply Subset.antisymm
  · exact generate_mono (minimals_subset F)
  · intro T hT
    obtain ⟨S, hS, hST⟩ := mem_generate.mp hT
    obtain ⟨U, hU, hUS⟩ := exists_minimal_subset hS
    exact mem_generate.mpr ⟨U, hU, hUS.trans hST⟩

theorem threshold_minimals (F : Finset (Finset α)) : threshold (minimals F) = threshold F := by
  simp only [threshold, generate_minimals]

theorem expectationThreshold_minimals (F : Finset (Finset α)) :
    expectationThreshold (minimals F) = expectationThreshold F := by
  unfold expectationThreshold
  congr 1
  ext p
  constructor <;> rintro ⟨hp, hc⟩
  · exact ⟨hp, (coverCost_minimals hp.1 F) ▸ hc⟩
  · exact ⟨hp, (coverCost_minimals hp.1 F).symm ▸ hc⟩

/-- The attachment's ell(F): max(2, largest cardinality of a minimal member). -/
def ell (F : Finset (Finset α)) : ℕ := max 2 ((minimals F).sup Finset.card)

theorem minimals_bounded_ell (F : Finset (Finset α)) : IsBounded (minimals F) (ell F) := by
  intro S hS
  exact (le_sup (f := Finset.card) hS).trans (le_max_right _ _)

/-- Theorem 1.1's inequality, with an explicit absolute constant.
This uses the fully proved Tran--Vu route from the imported source files.
For an increasing nontrivial family, these threshold definitions coincide
with the usual threshold and expectation threshold. -/
theorem theorem_1_1_explicit (F : Finset (Finset α)) :
    threshold F ≤ (100000 : ℝ) * expectationThreshold F * Real.logb 2 (ell F : ℝ) := by
  have h := park_pham_bound (minimals F) (ell F)
    (le_max_left _ _) (minimals_bounded_ell F)
  simpa only [threshold_minimals, expectationThreshold_minimals, parkPhamK] using h

def IsIncreasing (F : Finset (Finset α)) : Prop :=
  ∀ S ∈ F, ∀ T : Finset α, S ⊆ T → T ∈ F

theorem generate_eq_of_increasing {F : Finset (Finset α)} (hF : IsIncreasing F) :
    generate F = F := by
  apply Subset.antisymm
  · intro T hT
    obtain ⟨S, hS, hST⟩ := mem_generate.mp hT
    exact hF S hS T hST
  · exact covers_self F

/-- Standard infimum definition of the critical probability, using F itself. -/
def criticalProbability (F : Finset (Finset α)) : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc 0 1 ∧ 1 / 2 ≤ measureFamily p F}

theorem criticalProbability_eq {F : Finset (Finset α)} (hF : IsIncreasing F) :
    criticalProbability F = threshold F := by
  simp only [criticalProbability, threshold, generate_eq_of_increasing hF]

/-- The increasing-family version with both thresholds defined directly as in
the paper, using infimum/supremum in place of unique-root/maximum notation. -/
theorem theorem_1_1_increasing (F : Finset (Finset α)) (hF : IsIncreasing F) :
    criticalProbability F ≤ (100000 : ℝ) * paperExpectationThreshold F *
      Real.logb 2 (ell F : ℝ) := by
  rw [criticalProbability_eq hF, paperExpectationThreshold_eq]
  exact theorem_1_1_explicit F

theorem theorem_1_1 :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : Type) [DecidableEq α] [Fintype α]
      (F : Finset (Finset α)),
      threshold F ≤ K * expectationThreshold F * Real.logb 2 (ell F : ℝ) := by
  refine ⟨100000, by norm_num, ?_⟩
  intro α _ _ F
  exact theorem_1_1_explicit F

end
end ParkPhamPaper

/- ===== Source module: Audit.lean ===== -/


#print axioms KahnKalai.covering_theorem
#print axioms KahnKalai.park_pham
#print axioms ParkPhamPaper.exists_minimumFragment
#print axioms ParkPhamPaper.equation_16
#print axioms ParkPhamPaper.fragmentPairs_card_le
#print axioms ParkPhamPaper.weighted_fragmentPairs_bound
#print axioms ParkPhamPaper.proposition_2_3
#print axioms ParkPhamPaper.success_of_cheap_cover
#print axioms ParkPhamPaper.theorem_1_1_explicit
#print axioms ParkPhamPaper.theorem_1_1_increasing
#print axioms ParkPhamPaper.theorem_1_1

/-
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
