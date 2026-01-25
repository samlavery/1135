/-
Copyright (c) 2024. All rights reserved.
Released under MIT license.
-/
import Collatz.TiltBalance

/-!
# Tilt Core - Profile Alias

This file provides a `Profile` alias for `CriticalLineCycleProfile` from TiltBalance.lean.
This allows existing code using `Profile` to continue working while the actual
implementation lives in TiltBalance.

## Main Definitions

* `Profile` = `CriticalLineCycleProfile` (alias)
* `trivialProfile`: The all-2s profile (ν = [2,2,...,2])

All the core definitions (Δ, weight, foldedWeight, etc.) come from
CriticalLineCycleProfile in TiltBalance.lean.
-/

namespace Collatz.Tilt

open Collatz

/-- Profile is an alias for CriticalLineCycleProfile.
    This provides backwards compatibility with code that uses the Profile name. -/
abbrev Profile := CriticalLineCycleProfile

/-- The trivial profile: all νⱼ = 2.
    This corresponds to n = 1 (the trivial fixed point). -/
def trivialProfile (m : ℕ) (_hm : 0 < m) : Profile m where
  ν := fun _ => 2
  ν_pos := fun _ => by norm_num
  sum_ν := by simp [Finset.sum_const, Finset.card_fin, mul_comm]

/-- The trivial profile has Δⱼ = 0 for all j. -/
@[simp]
lemma trivialProfile_Δ_eq_zero {m : ℕ} (hm : 0 < m) (j : Fin m) :
    (trivialProfile m hm).Δ j = 0 := by
  unfold Profile.Δ trivialProfile
  by_cases hj : j.val = 0
  · simp [hj]
  · simp only [hj, ↓reduceDIte]
    apply Finset.sum_eq_zero
    intro i _
    simp

/-- The trivial profile has all weights = 1. -/
lemma trivialProfile_weight_eq_one {m : ℕ} (hm : 0 < m) (j : Fin m)
    (h_nonneg : 0 ≤ (trivialProfile m hm).Δ j) :
    (trivialProfile m hm).weight j h_nonneg = 1 := by
  unfold Profile.weight
  simp [trivialProfile_Δ_eq_zero hm j]

/-- The trivial profile is realizable (corresponds to n = 1). -/
lemma trivialProfile_isRealizable {m : ℕ} (hm : 0 < m) :
    (trivialProfile m hm).isRealizable := by
  unfold Profile.isRealizable CriticalLineCycleProfile.isRealizable
  use 1
  constructor
  · exact Nat.one_pos
  · -- waveSum of trivial profile equals D
    -- This follows from waveSum_all_two
    have h_all_two : ∀ j : Fin m, (trivialProfile m hm).ν j = 2 := fun _ => rfl
    have h_nonneg : ∀ j : Fin m, (trivialProfile m hm).Δ j ≥ 0 := by
      intro j
      simp [trivialProfile_Δ_eq_zero hm j]
    exact waveSum_all_two hm (trivialProfile m hm) h_nonneg h_all_two

end Collatz.Tilt
