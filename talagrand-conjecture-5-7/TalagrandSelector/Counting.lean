import TalagrandSelector.Witness
import TalagrandSelector.Bernoulli

open Finset Classical TalagrandPositiveReduction
namespace TalagrandSelector
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

abbrev Record (X : Type) [Fintype X] := Fin (Fintype.card X + 1) × Finset X
abbrev Entry (X : Type) [Fintype X] := Finset X × Record X
abbrev Key (X : Type) [Fintype X] :=
  Fin (Fintype.card X + 1) × Fin (Fintype.card X + 1) × Finset X

def encode (e : Entry X) : Key X :=
  (e.2.1, ⟨e.2.2.card, Nat.lt_succ_of_le (Finset.card_le_univ _)⟩, e.1 ∪ e.2.2)

namespace WeightSystem
variable (D : WeightSystem X)

def records (W : Finset X) : Finset (Record X) :=
  D.family.attach.image (fun I =>
    (⟨(D.witness W I.val I.property).card,
      Nat.lt_succ_of_le (Finset.card_le_univ _)⟩, D.fragment W I.val I.property))

theorem mem_records {W : Finset X} {r : Record X} : r ∈ D.records W ↔
    ∃ I, ∃ hI : I ∈ D.family,
      r.1.val = (D.witness W I hI).card ∧ r.2 = D.fragment W I hI := by
  constructor
  · intro h
    obtain ⟨I, _, he⟩ := Finset.mem_image.mp h
    refine ⟨I.val, I.property, ?_, ?_⟩
    · exact (congrArg (fun x : Record X => x.1.val) he).symm
    · exact (congrArg Prod.snd he).symm
  · rintro ⟨I, hI, hj, ht⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨I, hI⟩, Finset.mem_attach _ _, ?_⟩
    apply Prod.ext
    · exact Fin.ext hj.symm
    · exact ht.symm

def entries : Finset (Entry X) :=
  univ.filter (fun e => D.Bad e.1 ∧ e.2 ∈ D.records e.1)

def fiber (k : Key X) : Finset (Entry X) := D.entries.filter (fun e => encode e = k)

theorem entry_spec {e : Entry X} (he : e ∈ D.entries) :
    D.Bad e.1 ∧ ∃ I, ∃ hI : I ∈ D.family,
      e.2.1.val = (D.witness e.1 I hI).card ∧ e.2.2 = D.fragment e.1 I hI :=
  ⟨(Finset.mem_filter.mp he).2.1, D.mem_records.mp (Finset.mem_filter.mp he).2.2⟩

theorem entry_disjoint {e : Entry X} (he : e ∈ D.entries) : Disjoint e.1 e.2.2 := by
  obtain ⟨_, I, hI, _, ht⟩ := D.entry_spec he
  rw [ht]
  exact D.fragment_disjoint _ _ _

theorem entry_shape {e : Entry X} (he : e ∈ D.entries) :
    0 < e.2.2.card ∧ e.2.1.val ≤ 2 * e.2.2.card := by
  obtain ⟨hb, I, hI, hj, ht⟩ := D.entry_spec he
  rw [hj, ht]
  exact D.fragment_size _ _ _ hb

theorem entry_recover {e : Entry X} (he : e ∈ D.entries) :
    (e.1 ∪ e.2.2) \ e.2.2 = e.1 := by
  have hd := Finset.disjoint_left.mp (D.entry_disjoint he)
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · intro h
    exact h.1.resolve_right h.2
  · intro h
    exact ⟨Or.inl h, hd h⟩

theorem fiber_card (k : Key X) :
    (D.fiber k).card ≤
      if 0 < k.2.1.val ∧ k.1.val ≤ 2*k.2.1.val then 2 ^ k.1.val else 0 := by
  classical
  by_cases hne : (D.fiber k).Nonempty
  · obtain ⟨e₀, he₀⟩ := hne
    have hbase := (Finset.mem_filter.mp he₀).1
    have hk₀ := (Finset.mem_filter.mp he₀).2
    obtain ⟨_, I, hI, hj₀, ht₀⟩ := D.entry_spec hbase
    have hkt : k.2.1.val = e₀.2.2.card :=
      (congrArg (fun a : Key X => a.2.1.val) hk₀).symm
    have hkj : k.1.val = e₀.2.1.val :=
      (congrArg (fun a : Key X => a.1.val) hk₀).symm
    have hshape : 0 < k.2.1.val ∧ k.1.val ≤ 2*k.2.1.val := by
      rw [hkt, hkj]
      exact D.entry_shape hbase
    rw [if_pos hshape]
    let R := D.witness e₀.1 I hI
    have hmap : ∀ e ∈ D.fiber k, e.2.2 ∈ R.powerset := by
      intro e he
      have he' := (Finset.mem_filter.mp he).1
      have hk := (Finset.mem_filter.mp he).2
      obtain ⟨_, J, hJ, hj, ht⟩ := D.entry_spec he'
      apply Finset.mem_powerset.mpr
      rw [ht]
      apply D.fragment_in_container e₀.1 e.1 I J hI hJ
      · have hz := congrArg (fun a : Key X => a.2.2) (hk₀.trans hk.symm)
        simpa only [encode, ht₀, ht] using hz
      · have hx := congrArg (fun a : Key X => a.1.val) (hk₀.trans hk.symm)
        simpa only [encode, hj₀, hj] using hx
      · have hx := congrArg (fun a : Key X => a.2.1.val) (hk₀.trans hk.symm)
        simpa only [encode, ht₀, ht] using hx
    have hinj : Set.InjOn (fun e : Entry X => e.2.2) (D.fiber k) := by
      intro e he e' he' ht
      change e.2.2 = e'.2.2 at ht
      have hke := (Finset.mem_filter.mp he).2
      have hke' := (Finset.mem_filter.mp he').2
      have hz := congrArg (fun a : Key X => a.2.2) (hke.trans hke'.symm)
      have hj := congrArg (fun a : Key X => a.1) (hke.trans hke'.symm)
      change e.1 ∪ e.2.2 = e'.1 ∪ e'.2.2 at hz
      have hw : e.1 = e'.1 := by
        rw [← D.entry_recover (Finset.mem_filter.mp he).1,
          ← D.entry_recover (Finset.mem_filter.mp he').1]
        change (e.1 ∪ e.2.2) \ e.2.2 = (e'.1 ∪ e'.2.2) \ e'.2.2
        rw [hz, ht]
      exact Prod.ext hw (Prod.ext hj ht)
    have hc := Finset.card_le_card_of_injOn (fun e : Entry X => e.2.2) hmap hinj
    simpa only [Finset.card_powerset, R, ← hj₀, ← hkj] using hc
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le _

def entryWeight (p q : ℝ) (e : Entry X) : ℝ := subsetMass q e.1 * p ^ e.2.2.card

theorem entryWeight_encode {p q : ℝ} (hq : 0 < q) {e : Entry X}
    (he : e ∈ D.entries) : entryWeight p q e =
      subsetMass q (encode e).2.2 * (p*(1-q)/q) ^ (encode e).2.1.val :=
  subsetMass_augment hq _ _ (D.entry_disjoint he)

theorem total_cost_encoding {p q : ℝ} (hq : 0 < q) :
    (∑ e ∈ D.entries, entryWeight p q e) =
      ∑ k : Key X, ((D.fiber k).card : ℝ) *
        (subsetMass q k.2.2 * (p*(1-q)/q) ^ k.2.1.val) := by
  rw [← Finset.sum_fiberwise D.entries encode (entryWeight p q)]
  apply Finset.sum_congr rfl
  intro k _
  calc
    (∑ e ∈ D.fiber k, entryWeight p q e) =
        ∑ _e ∈ D.fiber k, subsetMass q k.2.2 * (p*(1-q)/q)^k.2.1.val := by
      apply Finset.sum_congr rfl
      intro e he
      rw [D.entryWeight_encode hq (Finset.mem_filter.mp he).1,
        (Finset.mem_filter.mp he).2]
    _ = _ := by simp

end WeightSystem
end
end TalagrandSelector
