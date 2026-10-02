/-
Additional formalization of the supplied Park--Pham paper (arXiv:2203.17207v2).
Released under the Apache License, Version 2.0; see LICENSE.

Scope: the exact minimum-fragment definition and equation (16), the
deterministic iteration, and the main theorem with the paper's minimal-edge
parameter. The final quantitative theorem uses the separate Tran--Vu proof
in Solution.lean. It is NOT a verification of the paper's entire randomized
iteration or its asymptotic error estimate (20).
-/
import Solution

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
