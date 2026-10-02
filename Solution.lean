/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch
-/
import KahnKalai
import Mathlib

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
