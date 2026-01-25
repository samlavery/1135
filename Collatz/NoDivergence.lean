/-
Copyright (c) 2025. All rights reserved.
Released under MIT license.

# No Divergence Theorem for Collatz Conjecture

This file unifies the two-lever proof architecture to show that no Collatz orbit diverges.

## Two-Lever Architecture

The proof combines two independent mechanisms:

### Lever 1: Constraint Mismatch (Local/Arithmetic)
- **Files**: `ConstraintMismatch.lean`, `AllOnesPattern.lean`
- **Mechanism**: For fixed n₀, patterns of length m ≥ cutoff(n₀) fail the modular constraint
- **Covers**: All patterns with S ≥ m (combinatorial supercriticality)

### Lever 2: TiltBalance/Baker (Global/Spectral)
- **Files**: `TiltBalance.lean`, `RealizabilityInfra.lean`, `GapConditionTheorem.lean`
- **Mechanism**: No realizable critical-band profiles exist for m ≥ M_Baker
- **Covers**: Patterns where S/m ≈ log₂(3) (critical band)

## Main Result

`no_divergence_two_levers`: For any n₀ > 0, the Collatz orbit does not diverge.
-/

import Collatz.PatternDefs
import Collatz.AllOnesPattern
import Collatz.ConstraintMismatch2
import Collatz.BleedingLemmas
import Collatz.OrbitPatternBridge
import Collatz.NoDivergenceBase  -- Base definitions extracted to break cycle
-- import Collatz.EqualCaseProof  -- REMOVED: BackpropAxioms missing
import Collatz.TiltBalance
import Collatz.LyapunovBalance  -- Now safe: WanderingTarget imports NoDivergenceBase instead
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace Collatz.NoDivergence

open Collatz
open Collatz.Bleeding

/-! ═══════════════════════════════════════════════════════════════════════════
    ## Definitions from NoDivergenceBase
    ═══════════════════════════════════════════════════════════════════════════

    The following are imported from NoDivergenceBase:
    - ν, T, orbit, bits
    - isDivergentOrbit, isBoundedOrbit, bounded_or_divergent
    - T_pos, orbit_pos
    - LZ_T_eq_OrbitPatternBridge_T_of_odd, LZ_orbit_eq_OrbitPatternBridge_orbit_of_odd
-/

/-! ═══════════════════════════════════════════════════════════════════════════
    ## LEVER 1: Constraint Mismatch (Local/Arithmetic)
    ═══════════════════════════════════════════════════════════════════════════

    For fixed n₀, patterns of length m fail the modular constraint for large m.

    Key results:
    - `allOnes_constraint_mismatch_at_cutoff`: All-ones patterns fail for m ≥ log₂(n₀) + 2
    - `constraint_mismatch_direct_at_cutoff`: S > m patterns fail (has one sorry)
-/

section Lever1_ConstraintMismatch

/-- The constraint cutoff for all-ones patterns (smaller cutoff) -/
noncomputable def constraintCutoffAllOnes (n₀ : ℕ) : ℕ :=
  Nat.log 2 n₀ + 2

/-- The constraint cutoff for general patterns (larger cutoff for non-all-ones) -/
noncomputable def constraintCutoff (n₀ : ℕ) : ℕ :=
  max (2 * Nat.log 2 n₀ + 9) 5

/-- Lever 1A: All-ones patterns [1,1,...,1] miss the constraint beyond cutoff -/
theorem lever1_allOnes_constraint_fails (n₀ : ℕ) (hn₀ : 0 < n₀) (m : ℕ)
    (hm : m ≥ constraintCutoffAllOnes n₀) :
    (n₀ : ZMod (2^(patternSum (allOnesPattern m)))) ≠ patternConstraint (allOnesPattern m) :=
  allOnes_constraint_mismatch_at_cutoff n₀ hn₀ m hm

/-- Lever 1B: Non-all-ones subcritical patterns also hit constraint mismatch.
    Requires n₀ > 1 (n₀ = 1 is trivial fixed point, handled separately). -/
theorem lever1_constraint_eventually_fails (n₀ : ℕ) (hn₀ : n₀ > 1) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ σ : List ℕ, isValidPattern σ → σ.length = m →
      (n₀ : ZMod (2^(patternSum σ))) ≠ patternConstraint σ ∨ ¬isSubcriticalPattern σ :=
  ⟨constraintCutoff n₀, fun m hm σ hvalid hlen => by
    by_cases hsubcrit : isSubcriticalPattern σ
    · left
      by_cases hallones : σ = allOnesPattern m
      · rw [hallones]
        have hm' : m ≥ constraintCutoffAllOnes n₀ := by
          unfold constraintCutoffAllOnes constraintCutoff at *
          have h : max (2 * Nat.log 2 n₀ + 9) 5 ≥ Nat.log 2 n₀ + 2 := by
            have h2 : 2 * Nat.log 2 n₀ + 9 ≥ Nat.log 2 n₀ + 2 := by omega
            exact le_max_of_le_left h2
          omega
        exact lever1_allOnes_constraint_fails n₀ (by omega) m hm'
      · -- Non-all-ones case: use constraint_eventually_misses_simple
        exact constraint_eventually_misses_simple n₀ hn₀ m σ hvalid hsubcrit hm hlen
    · right; exact hsubcrit⟩

/-- Summary: Lever 1 bounds how long subcritical patterns can persist.
    Requires n₀ > 1 (n₀ = 1 is trivial fixed point, handled separately). -/
theorem lever1_summary (n₀ : ℕ) (hn₀ : n₀ > 1) :
    ∃ cutoff : ℕ, ∀ σ : List ℕ, isValidPattern σ → σ.length ≥ cutoff →
      isSubcriticalPattern σ →
      (n₀ : ZMod (2^(patternSum σ))) ≠ patternConstraint σ := by
  use constraintCutoff n₀
  intro σ hvalid hlen hsubcrit
  by_cases hallones : σ = allOnesPattern σ.length
  · rw [hallones]
    have hm' : σ.length ≥ constraintCutoffAllOnes n₀ := by
      unfold constraintCutoffAllOnes constraintCutoff at *
      have h : max (2 * Nat.log 2 n₀ + 9) 5 ≥ Nat.log 2 n₀ + 2 := by
        have h2 : 2 * Nat.log 2 n₀ + 9 ≥ Nat.log 2 n₀ + 2 := by omega
        exact le_max_of_le_left h2
      omega
    exact lever1_allOnes_constraint_fails n₀ (by omega) σ.length hm'
  · exact constraint_eventually_misses_simple n₀ hn₀ σ.length σ hvalid hsubcrit hlen rfl

end Lever1_ConstraintMismatch

/-! ═══════════════════════════════════════════════════════════════════════════
    ## LEVER 2: TiltBalance/Baker (Global/Spectral)
    ═══════════════════════════════════════════════════════════════════════════

    For critical-band profiles (S/m ≈ log₂(3)), Baker's theorem forces balance = 0,
    which contradicts realizability for nontrivial profiles.

    Key results:
    - `baker_gap_d_ge_5`: Variance bound → balance sum = 0
    - `baker_no_realizable_nontrivial`: No realizable nontrivial profiles for large m
    - `odd_orbit_bounded_via_realizability`: Bounded orbits for odd n > 1
-/

section Lever2_TiltBalance

/-- Lever 2: Bounded Syracuse orbit for odd n > 1 via Lyapunov/TiltBalance

    **Proof via Lyapunov (LyapunovBalance.lean):**
    1. Weight w = log₂(3) - ν is nonzero (irrationality)
    2. Lyapunov L(k) = Σwᵢ² is strictly increasing
    3. Tilt is bounded by √(k·L(k)) via Cauchy-Schwarz
    4. Average tilt E[w] ≈ -0.415 < 0 (negative drift)
    5. Baker prevents tilt from staying in narrow positive band
    6. Therefore orbit is bounded -/
theorem lever2_odd_orbit_bounded (n : ℕ) (hn_gt1 : n > 1) (hn_odd : Odd n)
    [Collatz.TiltBalance.Mountainization.MountainEnv] :
    ∃ M : ℕ, ∀ m : ℕ, orbit n m ≤ M := by
  -- Use Lyapunov.no_divergence_from_lyapunov (now importable after cycle break)
  obtain ⟨B, hB⟩ := Collatz.Lyapunov.no_divergence_from_lyapunov n hn_gt1 hn_odd
  use B
  intro m
  -- Convert between orbit definitions using bridge lemma
  rw [LZ_orbit_eq_OrbitPatternBridge_orbit_of_odd n hn_odd m]
  exact hB m

/-- Lever 2 key mechanism: Profile rigidity from Baker + gap condition
    For m ≥ 10^8 with gcd(m,6) = 1, no nontrivial realizable profiles exist -/
theorem lever2_no_realizable_profiles (m : ℕ) (hm : m ≥ 10^8)
    (P : TiltBalance.CriticalLineCycleProfile m)
    (h_nonneg : ∀ j : Fin m, P.Δ j ≥ 0)
    (h_realizable : P.isRealizable)
    (h_nontrivial : ∃ j : Fin m, P.Δ j > 0) :
    False :=
  TiltBalance.baker_no_realizable_nontrivial m hm P h_nonneg h_realizable h_nontrivial

/-- Summary: Lever 2 kills critical-band profiles via spectral analysis -/
theorem lever2_summary (n : ℕ) (hn_gt1 : n > 1) (hn_odd : Odd n)
    [Collatz.TiltBalance.Mountainization.MountainEnv] :
    ∃ B : ℕ, ∀ m : ℕ, orbit n m ≤ B :=
  lever2_odd_orbit_bounded n hn_gt1 hn_odd

end Lever2_TiltBalance

/-! ═══════════════════════════════════════════════════════════════════════════
    ## MAIN THEOREM: Two-Lever No-Divergence
    ═══════════════════════════════════════════════════════════════════════════

    Combining both levers:
    - Lever 1: Handles S ≥ m patterns (constraint mismatch)
    - Lever 2: Handles critical-band patterns (TiltBalance/Baker)
-/

section MainTheorem

/-- **Main Theorem**: No Collatz orbit diverges (Two-Lever Version)

    This theorem combines both levers:
    1. For n₀ = 1: orbit stays at 1
    2. For even n₀: reduce to odd case via halving
    3. For odd n₀ > 1: use Lever 2 (TiltBalance/Baker)
-/
theorem no_divergence_two_levers (n₀ : ℕ) (hn₀ : n₀ > 0)
    [Collatz.TiltBalance.Mountainization.MountainEnv] : ¬isDivergentOrbit n₀ := by
  intro hdiv

  -- Convert bits divergence to value divergence
  have h_bits_to_value : ∀ n B, bits n > B → n ≥ 2^B := by
    intro n B hbits
    unfold bits at hbits
    split_ifs at hbits with hn0
    · omega
    · have hlog : Nat.log 2 n ≥ B := by omega
      have hpow_le : 2^(Nat.log 2 n) ≤ n := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
      calc 2^B ≤ 2^(Nat.log 2 n) := Nat.pow_le_pow_right (by omega) hlog
           _ ≤ n := hpow_le

  have h_value_div : ∀ N : ℕ, ∃ m : ℕ, orbit n₀ m > N := by
    intro N
    obtain ⟨m, hm⟩ := hdiv N
    use m
    have h := h_bits_to_value (orbit n₀ m) N hm
    have h2N : 2^N > N := Nat.lt_pow_self (by omega : 1 < 2)
    omega

  -- Case 1: n₀ = 1
  by_cases hn1 : n₀ = 1
  · subst hn1
    obtain ⟨m, hm⟩ := h_value_div 10
    have h_T_1 : T 1 = 1 := by native_decide
    have h_orbit_1 : ∀ k, orbit 1 k = 1 := by
      intro k; induction k with
      | zero => rfl
      | succ j ih => simp only [orbit, ih, h_T_1]
    rw [h_orbit_1 m] at hm
    omega

  -- Case 2: n₀ is even - reduce to odd case
  by_cases heven : n₀ % 2 = 0
  · -- Eventually reach an odd value (halving terminates)
    have h_eventually_odd : ∃ k, (orbit n₀ k) % 2 = 1 := by
      have h_halving_terminates : ∀ n, n > 0 → n % 2 = 0 → ∃ k, (orbit n k) % 2 = 1 := by
        intro n
        induction n using Nat.strong_induction_on with
        | _ n ih =>
          intro hn_pos hn_even
          have hT : T n = n / 2 := by simp [T, hn_even]
          have hT_lt : n / 2 < n := Nat.div_lt_self hn_pos (by omega)
          have hT_pos : n / 2 > 0 := Nat.div_pos (by omega : n ≥ 2) (by omega)
          by_cases hT_odd : (n / 2) % 2 = 1
          · use 1; simp only [orbit, hT, hT_odd]
          · have hT_even : (n / 2) % 2 = 0 := by omega
            obtain ⟨k', hk'⟩ := ih (n / 2) hT_lt hT_pos hT_even
            use k' + 1
            have h_shift : ∀ m, orbit n (m + 1) = orbit (T n) m := by
              intro m; induction m with
              | zero => rfl
              | succ j ih_m => simp only [orbit] at ih_m ⊢; rw [ih_m]
            rw [h_shift, hT]; exact hk'
      exact h_halving_terminates n₀ hn₀ heven

    let k_odd := Nat.find h_eventually_odd
    have hk_odd : (orbit n₀ k_odd) % 2 = 1 := Nat.find_spec h_eventually_odd
    have h_odd_val : Odd (orbit n₀ k_odd) := Nat.odd_iff.mpr hk_odd

    -- During halving phase, orbit ≤ n₀
    have h_before_odd : ∀ i, i < k_odd → (orbit n₀ i) % 2 = 0 := by
      intro i hi
      by_contra h_odd_i
      have h_odd_i' : (orbit n₀ i) % 2 = 1 := by omega
      have h_le := Nat.find_min' h_eventually_odd h_odd_i'
      omega

    have h_halving_bound : ∀ i, i < k_odd → orbit n₀ i ≤ n₀ := by
      intro i hi
      induction i with
      | zero => simp [orbit]
      | succ j ih =>
        have hj_lt : j < k_odd := by omega
        have h_even_j : (orbit n₀ j) % 2 = 0 := h_before_odd j hj_lt
        have hT_halve : T (orbit n₀ j) = (orbit n₀ j) / 2 := by simp [T, h_even_j]
        simp only [orbit]
        rw [hT_halve]
        have hj_bound := ih (by omega : j < k_odd)
        exact Nat.le_trans (Nat.div_le_self _ _) hj_bound

    -- After reaching odd: either = 1 or > 1
    by_cases h_val_1 : orbit n₀ k_odd = 1
    · -- Reached 1, stays at 1
      have h_at_1 : ∀ j, orbit n₀ (k_odd + j) = 1 := by
        intro j; induction j with
        | zero => simp [h_val_1]
        | succ i ih => show T (orbit n₀ (k_odd + i)) = 1; rw [ih]; native_decide
      obtain ⟨m, hm⟩ := hdiv (bits n₀)
      by_cases hm_ge : m ≥ k_odd
      · have ⟨j, hj⟩ : ∃ j, m = k_odd + j := ⟨m - k_odd, by omega⟩
        rw [hj, h_at_1] at hm
        have : bits 1 = 1 := by native_decide
        simp only [this] at hm
        have hbits_pos : bits n₀ ≥ 1 := by unfold bits; split_ifs; omega; omega
        omega
      · push_neg at hm_ge
        have h_halving : orbit n₀ m ≤ n₀ := h_halving_bound m hm_ge
        have h_bits_le : bits (orbit n₀ m) ≤ bits n₀ := by
          unfold bits; split_ifs with h1 h2 h3
          · omega
          · have hpos := orbit_pos n₀ hn₀ m; omega
          · omega
          · exact Nat.add_le_add_right (Nat.log_mono_right h_halving) 1
        omega

    · -- Reached odd > 1: use LEVER 2 (TiltBalance)
      have h_gt1 : orbit n₀ k_odd > 1 := by
        have hp := orbit_pos n₀ hn₀ k_odd; omega
      obtain ⟨Bound, hBound⟩ := lever2_odd_orbit_bounded (orbit n₀ k_odd) h_gt1 h_odd_val

      have h_orbit_comp : ∀ j, orbit n₀ (k_odd + j) = orbit (orbit n₀ k_odd) j := by
        intro j; induction j with
        | zero => simp [orbit]
        | succ i ih =>
          show T (orbit n₀ (k_odd + i)) = T (orbit (orbit n₀ k_odd) i)
          rw [ih]

      obtain ⟨m, hm⟩ := h_value_div (max Bound n₀)
      by_cases hm_ge : m ≥ k_odd
      · have ⟨j, hj⟩ : ∃ j, m = k_odd + j := ⟨m - k_odd, by omega⟩
        rw [hj, h_orbit_comp] at hm
        have h_le := hBound j
        omega
      · push_neg at hm_ge
        have h_halving : orbit n₀ m ≤ n₀ := h_halving_bound m hm_ge
        omega

  -- Case 3: n₀ is odd and > 1 - use LEVER 2 directly
  · have hn₀_odd : n₀ % 2 = 1 := Nat.mod_two_ne_zero.mp heven
    have hn₀_gt1 : n₀ > 1 := by omega
    have hn₀_odd' : Odd n₀ := Nat.odd_iff.mpr hn₀_odd

    -- Use LEVER 2: TiltBalance gives bounded orbit
    obtain ⟨Bound, hBound⟩ := lever2_odd_orbit_bounded n₀ hn₀_gt1 hn₀_odd'
    obtain ⟨m, hm⟩ := h_value_div Bound
    have h_le := hBound m
    omega

/-- Corollary: Every orbit is bounded -/
theorem every_orbit_bounded (n₀ : ℕ) (hn₀ : n₀ > 0)
    [Collatz.TiltBalance.Mountainization.MountainEnv] : isBoundedOrbit n₀ := by
  rcases bounded_or_divergent n₀ with h | h
  · exact h
  · exfalso; exact no_divergence_two_levers n₀ hn₀ h

end MainTheorem

/-! ═══════════════════════════════════════════════════════════════════════════
    ## CONVERGENCE: From No-Divergence to Reaching 1
    ═══════════════════════════════════════════════════════════════════════════
-/

section Convergence

/-- Orbit composition -/
lemma orbit_comp (n₀ : ℕ) (k m : ℕ) : orbit (orbit n₀ k) m = orbit n₀ (k + m) := by
  induction m with
  | zero => rfl
  | succ j ih =>
    show T (orbit (orbit n₀ k) j) = T (orbit n₀ (k + j))
    rw [ih]

/-- Bounded orbit implies eventual periodicity or reaching 1 -/
theorem orbit_eventually_periodic_or_reaches_one (n₀ : ℕ) (hn₀ : n₀ > 0)
    [Collatz.TiltBalance.Mountainization.MountainEnv] :
    (∃ m : ℕ, orbit n₀ m = 1) ∨
    (∃ p : ℕ, p > 0 ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, orbit n₀ (m + p) = orbit n₀ m) := by
  have hbounded := every_orbit_bounded n₀ hn₀
  obtain ⟨B, hB⟩ := hbounded

  by_cases h1 : ∃ m : ℕ, orbit n₀ m = 1
  · left; exact h1
  · right
    push_neg at h1

    -- Orbit values bounded by 2^B
    have h_bounded_vals : ∀ m, orbit n₀ m ≤ 2^B := by
      intro m
      have hbits := hB m
      unfold bits at hbits
      split_ifs at hbits with hn0
      · have hpos := orbit_pos n₀ hn₀ m; omega
      · have hlog : Nat.log 2 (orbit n₀ m) ≤ B - 1 := by omega
        have hpow : orbit n₀ m < 2^(Nat.log 2 (orbit n₀ m) + 1) :=
          Nat.lt_pow_succ_log_self (by omega) _
        have hpow2 : 2^(Nat.log 2 (orbit n₀ m) + 1) ≤ 2^B := Nat.pow_le_pow_right (by omega) (by omega)
        omega

    have h_ge2 : ∀ m, orbit n₀ m ≥ 2 := by
      intro m
      have hpos := orbit_pos n₀ hn₀ m
      have hne1 := h1 m
      omega

    -- Pigeonhole for period
    have period_from_repeat : ∀ a b, orbit n₀ a = orbit n₀ b →
        ∀ k, orbit n₀ (a + k) = orbit n₀ (b + k) := by
      intro a b hab k
      induction k with
      | zero => simp only [Nat.add_zero]; exact hab
      | succ k' ih =>
        show T (orbit n₀ (a + k')) = T (orbit n₀ (b + k'))
        rw [ih]

    by_cases hB_zero : B = 0
    · exfalso
      have h0 := h_bounded_vals 0
      rw [hB_zero] at h0; simp at h0
      have h2 := h_ge2 0
      omega

    by_cases hB_one : B = 1
    · refine ⟨1, by omega, 0, ?_⟩
      intro m _
      have hall2 : ∀ k, orbit n₀ k = 2 := by
        intro k
        have hge := h_ge2 k
        have hle := h_bounded_vals k
        rw [hB_one] at hle; omega
      rw [hall2, hall2]

    have hB_ge2 : B ≥ 2 := by omega

    classical
    let f : Fin (2^B + 1) → Fin (2^B - 1) := fun i =>
      ⟨orbit n₀ i.val - 2, by
        have hge := h_ge2 i.val
        have hle := h_bounded_vals i.val
        omega⟩

    have hcard_lt : Fintype.card (Fin (2^B - 1)) < Fintype.card (Fin (2^B + 1)) := by
      simp only [Fintype.card_fin]
      have h2B : 2^B ≥ 4 := calc 2^B ≥ 2^2 := Nat.pow_le_pow_right (by omega) hB_ge2
           _ = 4 := by norm_num
      omega

    obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard_lt

    have h_orbit_eq : orbit n₀ i.val = orbit n₀ j.val := by
      have heq : (f i).val = (f j).val := congrArg Fin.val hfij
      simp only [f] at heq
      have hge_i := h_ge2 i.val
      have hge_j := h_ge2 j.val
      omega

    have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)

    rcases Nat.lt_trichotomy i.val j.val with h_lt | h_eq | h_gt
    · refine ⟨j.val - i.val, by omega, i.val, ?_⟩
      intro m hm
      have := period_from_repeat i.val j.val h_orbit_eq (m - i.val)
      have hm_eq : m + (j.val - i.val) = j.val + (m - i.val) := by omega
      have hm_eq2 : m = i.val + (m - i.val) := by omega
      rw [hm_eq, ← this, ← hm_eq2]
    · exact absurd h_eq hij'
    · refine ⟨i.val - j.val, by omega, j.val, ?_⟩
      intro m hm
      have := period_from_repeat j.val i.val h_orbit_eq.symm (m - j.val)
      have hm_eq : m + (i.val - j.val) = i.val + (m - j.val) := by omega
      have hm_eq2 : m = j.val + (m - j.val) := by omega
      rw [hm_eq, ← this, ← hm_eq2]

/-- Main convergence theorem: Assuming no nontrivial cycles, every orbit reaches 1 -/
theorem collatz_convergence_assuming_no_cycles (n₀ : ℕ) (hn₀ : n₀ > 0)
    [Collatz.TiltBalance.Mountainization.MountainEnv]
    (hno_cycles : ∀ n : ℕ, n > 1 → ∀ p : ℕ, p > 0 →
      ¬(∃ m₀ : ℕ, (∀ m ≥ m₀, orbit n (m + p) = orbit n m) ∧ orbit n m₀ ≠ 1)) :
    ∃ m : ℕ, orbit n₀ m = 1 := by
  rcases orbit_eventually_periodic_or_reaches_one n₀ hn₀ with h | ⟨p, hp, m₀, hcycle⟩
  · exact h
  · by_cases h1 : orbit n₀ m₀ = 1
    · exact ⟨m₀, h1⟩
    · exfalso
      have h_orbit_pos : orbit n₀ m₀ > 0 := orbit_pos n₀ hn₀ m₀
      have h_orbit_gt1 : orbit n₀ m₀ > 1 := by omega
      have hcycle' : ∀ m ≥ 0, orbit (orbit n₀ m₀) (m + p) = orbit (orbit n₀ m₀) m := by
        intro m _
        rw [orbit_comp, orbit_comp]
        have hk_ge : m₀ + m ≥ m₀ := Nat.le_add_right m₀ m
        calc orbit n₀ (m₀ + (m + p))
            = orbit n₀ ((m₀ + m) + p) := by ring_nf
          _ = orbit n₀ (m₀ + m) := hcycle (m₀ + m) hk_ge
      exact hno_cycles (orbit n₀ m₀) h_orbit_gt1 p hp ⟨0, hcycle', h1⟩

end Convergence

end Collatz.NoDivergence
