import TalagrandSelector.Reduction

open Finset
namespace TalagrandSelector
noncomputable section
variable {X : Type} [DecidableEq X]

def massOn (U : Finset X) (p : ℝ) (W : Finset X) : ℝ :=
  p ^ W.card * (1-p) ^ (U.card-W.card)

def average (U : Finset X) (p : ℝ) (f : Finset X → ℝ) : ℝ :=
  ∑ W ∈ U.powerset, massOn U p W * f W

theorem average_congr (U : Finset X) (p : ℝ) {f g : Finset X → ℝ}
    (h : ∀ W ⊆ U, f W = g W) : average U p f = average U p g := by
  apply Finset.sum_congr rfl
  intro W hW
  rw [h W (Finset.mem_powerset.mp hW)]

theorem average_add (U : Finset X) (p : ℝ) (f g : Finset X → ℝ) :
    average U p (fun W => f W + g W) = average U p f + average U p g := by
  simp [average, mul_add, Finset.sum_add_distrib]

theorem average_mul (U : Finset X) (p c : ℝ) (f : Finset X → ℝ) :
    average U p (fun W => c * f W) = c * average U p f := by
  simp [average, Finset.mul_sum, mul_left_comm]

theorem average_insert {a : X} {U : Finset X} (ha : a ∉ U)
    (p : ℝ) (f : Finset X → ℝ) :
    average (insert a U) p f =
      (1-p)*average U p f + p*average U p (fun W => f (insert a W)) := by
  have h0 : ∀ W ∈ U.powerset, massOn (insert a U) p W = (1-p)*massOn U p W := by
    intro W hW
    have hc := Finset.card_le_card (Finset.mem_powerset.mp hW)
    have hn : U.card + 1 - W.card = (U.card-W.card)+1 := by omega
    simp only [massOn, Finset.card_insert_of_notMem ha, hn, pow_succ]
    ring
  have h1 : ∀ W ∈ U.powerset,
      massOn (insert a U) p (insert a W) = p*massOn U p W := by
    intro W hW
    have haw : a ∉ W := fun hw => ha ((Finset.mem_powerset.mp hW) hw)
    simp only [massOn, Finset.card_insert_of_notMem ha,
      Finset.card_insert_of_notMem haw, Nat.add_sub_add_right, pow_succ]
    ring
  unfold average
  rw [Finset.sum_powerset_insert ha, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro W hW
    rw [h0 W hW]
    ring
  · apply Finset.sum_congr rfl
    intro W hW
    rw [h1 W hW]
    ring

@[simp] theorem average_empty (p : ℝ) (f : Finset X → ℝ) : average ∅ p f = f ∅ := by
  simp [average, massOn]

@[simp] theorem average_const (U : Finset X) (p c : ℝ) :
    average U p (fun _ => c) = c := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert a U ha ih => rw [average_insert ha, ih]; ring

theorem average_mono (U : Finset X) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : Finset X → ℝ} (h : ∀ W ⊆ U, f W ≤ g W) :
    average U p f ≤ average U p g := by
  apply Finset.sum_le_sum
  intro W hW
  apply mul_le_mul_of_nonneg_left (h W (Finset.mem_powerset.mp hW))
  unfold massOn
  positivity

/-- The intersection of independent p and q samples is a pq sample. -/
theorem average_inter (U : Finset X) (p q : ℝ) (f : Finset X → ℝ) :
    average U p (fun W => average U q (fun V => f (W ∩ V))) =
      average U (p*q) f := by
  induction U using Finset.induction_on generalizing f with
  | empty => simp
  | @insert a U ha ih =>
    have h0 : average U p (fun W => average (insert a U) q (fun V => f (W ∩ V))) =
        average U p (fun W => average U q (fun V => f (W ∩ V))) := by
      apply average_congr
      intro W hW
      have haw : a ∉ W := fun hw => ha (hW hw)
      rw [average_insert ha]
      have he : average U q (fun V => f (W ∩ insert a V)) =
          average U q (fun V => f (W ∩ V)) := by
        apply average_congr
        intro V _
        have hs : W ∩ insert a V = W ∩ V := by ext i; simp; aesop
        rw [hs]
      rw [he]
      ring
    have h1 : average U p (fun W =>
        average (insert a U) q (fun V => f (insert a W ∩ V))) =
        (1-q)*average U p (fun W => average U q (fun V => f (W ∩ V))) +
        q*average U p (fun W => average U q (fun V => f (insert a (W ∩ V)))) := by
      rw [← average_mul, ← average_mul, ← average_add]
      apply average_congr
      intro W _
      rw [average_insert ha]
      have he : average U q (fun V => f (insert a W ∩ V)) =
          average U q (fun V => f (W ∩ V)) := by
        apply average_congr
        intro V hV
        have hav : a ∉ V := fun hv => ha (hV hv)
        have hs : insert a W ∩ V = W ∩ V := by ext i; simp; aesop
        rw [hs]
      have he' : average U q (fun V => f (insert a W ∩ insert a V)) =
          average U q (fun V => f (insert a (W ∩ V))) := by
        apply average_congr
        intro V _
        have hs : insert a W ∩ insert a V = insert a (W ∩ V) := by
          ext i
          simp only [Finset.mem_inter, Finset.mem_insert]
          tauto
        rw [hs]
      rw [he, he']
    rw [average_insert ha, h0, h1, ih f, ih (fun S => f (insert a S)), average_insert ha]
    ring

theorem average_sum_weights (U : Finset X) (p : ℝ) (w : X → ℝ) :
    average U p (fun W => ∑ i ∈ W, w i) = p * ∑ i ∈ U, w i := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert a U ha ih =>
    rw [average_insert ha]
    have he : average U p (fun W => ∑ i ∈ insert a W, w i) =
        w a + average U p (fun W => ∑ i ∈ W, w i) := by
      calc
        average U p (fun W => ∑ i ∈ insert a W, w i) =
            average U p (fun W => w a + ∑ i ∈ W, w i) := by
          apply average_congr
          intro W hW
          exact Finset.sum_insert (fun hw => ha (hW hw))
        _ = _ := by rw [average_add, average_const]
    rw [he, ih, Finset.sum_insert ha]
    ring

theorem average_inter_sum (U W : Finset X) (hW : W ⊆ U) (p : ℝ) (w : X → ℝ) :
    average U p (fun V => ∑ i ∈ W ∩ V, w i) = p * ∑ i ∈ W, w i := by
  have he : ∀ V : Finset X, (∑ i ∈ W ∩ V, w i) = ∑ i ∈ V, if i ∈ W then w i else 0 := by
    intro V
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp [and_comm]
  simp_rw [he]
  rw [average_sum_weights, ← Finset.sum_filter]
  have hu : U.filter (fun i => i ∈ W) = W := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hW h, h⟩⟩
  rw [hu]

variable [Fintype X]
open TalagrandPositiveReduction

theorem average_univ (p : ℝ) (f : Finset X → ℝ) :
    average univ p f = expectation p f := by
  simp [average, massOn, expectation, subsetMass]

theorem subsetMass_sum (p : ℝ) : (∑ W : Finset X, subsetMass p W) = 1 := by
  have h := average_const (univ : Finset X) p 1
  rw [average_univ] at h
  simpa [average_univ, expectation] using h

theorem subsetMass_augment {p q : ℝ} (hq : 0 < q) (W T : Finset X)
    (hd : Disjoint W T) :
    subsetMass q W * p ^ T.card =
      subsetMass q (W ∪ T) * (p*(1-q)/q) ^ T.card := by
  have hc := Finset.card_le_univ (W ∪ T)
  rw [Finset.card_union_of_disjoint hd] at hc
  have he : Fintype.card X - W.card =
      (Fintype.card X - (W.card+T.card)) + T.card := by omega
  unfold subsetMass
  rw [Finset.card_union_of_disjoint hd, he, pow_add, pow_add, div_pow, mul_pow]
  field_simp [ne_of_gt hq]

end
end TalagrandSelector
