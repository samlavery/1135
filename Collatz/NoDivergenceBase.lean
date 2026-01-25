/-
Copyright (c) 2025. All rights reserved.
Released under MIT license.

# No Divergence Base Definitions

This file contains the base definitions for orbit analysis that are used by both
NoDivergence.lean and WanderingTarget.lean. Extracted to break circular imports.
-/

import Collatz.PatternDefs
import Collatz.OrbitPatternBridge
import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace Collatz.NoDivergence

open Collatz

/-! ## Local Definitions (formerly from LZComplexity) -/

/-- The 2-adic valuation -/
def ν (n : ℕ) : ℕ := padicValNat 2 n

/-- Syracuse transformation: T(n) = n/2 if even, (3n+1)/2^ν(3n+1) if odd -/
def T (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2^(ν (3 * n + 1))

/-- Orbit iteration -/
def orbit (n₀ : ℕ) : ℕ → ℕ
  | 0 => n₀
  | m + 1 => T (orbit n₀ m)

/-- Bit length of a natural number -/
def bits (n : ℕ) : ℕ := if n = 0 then 0 else Nat.log 2 n + 1

/-! ## Common Definitions -/

/-- A diverging orbit would have bits → ∞ -/
def isDivergentOrbit (n₀ : ℕ) : Prop :=
  ∀ B : ℕ, ∃ m : ℕ, bits (orbit n₀ m) > B

/-- A bounded orbit stays below some fixed bit length -/
def isBoundedOrbit (n₀ : ℕ) : Prop :=
  ∃ B : ℕ, ∀ m : ℕ, bits (orbit n₀ m) ≤ B

/-- Bounded and divergent are complementary -/
lemma bounded_or_divergent (n₀ : ℕ) : isBoundedOrbit n₀ ∨ isDivergentOrbit n₀ := by
  by_cases h : isBoundedOrbit n₀
  · left; exact h
  · right
    unfold isBoundedOrbit at h
    push_neg at h
    unfold isDivergentOrbit
    intro B
    obtain ⟨m, hm⟩ := h B
    exact ⟨m, hm⟩

/-! ## Positivity Lemmas -/

/-- T maps positive to positive -/
lemma T_pos (n : ℕ) (hn : n > 0) : T n > 0 := by
  unfold T ν
  by_cases heven : n % 2 = 0
  · simp only [heven, ↓reduceIte]
    have h2_le_n : 2 ≤ n := Nat.le_of_dvd hn (Nat.dvd_of_mod_eq_zero heven)
    exact Nat.div_pos h2_le_n (by omega)
  · simp only [heven, ↓reduceIte]
    have h3n1_pos : 3 * n + 1 > 0 := by omega
    have hν_pos : padicValNat 2 (3 * n + 1) ≥ 1 := by
      have h2_dvd : 2 ∣ 3 * n + 1 := by omega
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact (padicValNat_dvd_iff_le (by omega)).mp h2_dvd
    have hdvd : 2^(padicValNat 2 (3 * n + 1)) ∣ 3 * n + 1 := pow_padicValNat_dvd
    exact Nat.div_pos (Nat.le_of_dvd h3n1_pos hdvd) (Nat.pow_pos (by omega : 0 < 2))

/-- Orbit values are always positive -/
lemma orbit_pos (n₀ : ℕ) (hn₀ : n₀ > 0) (m : ℕ) : orbit n₀ m > 0 := by
  induction m with
  | zero => simp [orbit]; exact hn₀
  | succ k ih => simp only [orbit]; exact T_pos _ ih

/-! ## Bridge Lemmas -/

/-- T equals OrbitPatternBridge.T for odd inputs -/
lemma LZ_T_eq_OrbitPatternBridge_T_of_odd (n : ℕ) (hn : Odd n) :
    T n = OrbitPatternBridge.T n := by
  have h_odd : n % 2 ≠ 0 := by obtain ⟨k, hk⟩ := hn; omega
  simp only [T, h_odd, ↓reduceIte, ν, OrbitPatternBridge.T, OrbitPatternBridge.nu]

/-- orbit equals OrbitPatternBridge.orbit for odd starting points -/
lemma LZ_orbit_eq_OrbitPatternBridge_orbit_of_odd (n : ℕ) (hn : Odd n) (m : ℕ) :
    orbit n m = OrbitPatternBridge.orbit n m := by
  induction m with
  | zero => rfl
  | succ k ih =>
    simp only [orbit, OrbitPatternBridge.orbit]
    rw [ih]
    have h_odd_orbit : Odd (OrbitPatternBridge.orbit n k) := OrbitPatternBridge.orbit_is_odd n hn k
    exact LZ_T_eq_OrbitPatternBridge_T_of_odd _ h_odd_orbit

end Collatz.NoDivergence
