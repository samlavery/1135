/-
Copyright (c) 2024. All rights reserved.
Released under MIT license.
-/
import Collatz.OrbitPatternBridge
import Collatz.BleedingLemmas
import Collatz.PatternDefs
import Collatz.AllOnesPattern
import Collatz.ConstraintMismatch2
import Collatz.WaveSumProperties
import Collatz.DriftLemma
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Log

/-!
# Subcritical Pattern Congruence Constraints

This file proves that Collatz orbits cannot remain subcritical indefinitely.
This REPLACES the `eventual_supercriticality` axiom in RealizabilityInfra.lean.

## Key Insight

For subcritical patterns: 2^S < 3^m means S < m · log₂(3) ≈ 1.585m
But each ν ≥ 1, so S ≥ m. Subcritical requires average ν in [1, 1.585).

The ν = 1 case requires n ≡ 3 (mod 4), which means trailingOnes(n) ≥ 2.
Consecutive ν = 1 steps form "runs" bounded by trailingOnes of the starting value.
By trailingOnes_le_log, runs have length ≤ log₂(orbit value).

In subcritical regime, orbits grow. Large orbits visit residue classes more uniformly,
pushing the ν average toward its ergodic mean of 2 > log₂(3).
-/

namespace Collatz.SubcriticalCongruence

open Collatz.OrbitPatternBridge
open Collatz.Bleeding
open scoped BigOperators

/-! ## Helper Lemmas -/

/-- If 2^k divides n ≠ 0, then k ≤ padicValNat 2 n -/
lemma pow_dvd_implies_le_padic (n k : ℕ) (hn : n ≠ 0) (hdvd : 2^k ∣ n) :
    k ≤ padicValNat 2 n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (padicValNat_dvd_iff_le hn).mp hdvd

/-- Valid patterns have sum ≥ length (each entry ≥ 1) -/
lemma valid_pattern_sum_ge_length (σ : List ℕ) (hvalid : Collatz.isValidPattern σ) :
    Collatz.patternSum σ ≥ σ.length := by
  unfold Collatz.patternSum
  induction σ with
  | nil => simp
  | cons x xs ih =>
    simp only [List.sum_cons, List.length_cons]
    have hx : x ≥ 1 := hvalid x (by simp)
    have hxs : Collatz.isValidPattern xs := fun y hy => hvalid y (List.mem_cons_of_mem x hy)
    have ih_applied := ih hxs
    -- Goal: x + xs.sum ≥ 1 + xs.length
    -- From hx: x ≥ 1
    -- From ih_applied: xs.sum ≥ xs.length
    omega

/-! ## Key Lemma: ν ≥ 2 when not in a trailing ones run -/

/-- For n ≡ 1 (mod 4), we have ν(n) ≥ 2 -/
lemma nu_ge_two_of_mod4_eq1 (n : ℕ) (hn_pos : n > 0) (hmod : n % 4 = 1) :
    nu n ≥ 2 := by
  unfold nu
  have h_3n1_mod4 : (3 * n + 1) % 4 = 0 := by omega
  have h_ne : 3 * n + 1 ≠ 0 := by omega
  have h_4_dvd : 4 ∣ 3 * n + 1 := Nat.dvd_of_mod_eq_zero h_3n1_mod4
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : (2 : ℕ)^2 ∣ 3 * n + 1 := by norm_num; exact h_4_dvd
  exact (padicValNat_dvd_iff_le h_ne).mp hdvd

/-- For n ≡ 3 (mod 4), we have ν(n) = 1 -/
lemma nu_eq_one_of_mod4_eq3 (n : ℕ) (hmod : n % 4 = 3) :
    nu n = 1 := by
  unfold nu
  exact v2_3n1_eq_one_of_mod4_eq3 n hmod

/-- Connection: n ≡ 3 (mod 4) iff trailingOnes n ≥ 2 (for odd n) -/
lemma mod4_eq3_iff_trailingOnes_ge2 (n : ℕ) (hn_odd : Odd n) :
    n % 4 = 3 ↔ trailingOnes n ≥ 2 :=
  (trailingOnes_ge2_iff_mod4_eq3 n hn_odd).symm

/-! ## Counting ν = 1 steps

Key insight: ν = 1 steps come in "runs" where trailingOnes decreases by 1 each step.
A run starting from n with trailingOnes(n) = t has length at most t - 1.
After the run, we must have a ν ≥ 2 step.
-/

/-- After a ν = 1 run of length k starting from n with trailingOnes n = t ≥ 2,
    the run length is at most t - 1 -/
lemma nu_one_run_length_bound (n : ℕ) (hn_odd : Odd n) (hn_pos : n > 0)
    (t : ℕ) (ht : t ≥ 2) (ht_eq : trailingOnes n = t) (k : ℕ) (hk : k < t - 1) :
    padicValNat 2 (3 * iterateSyracuse n hn_odd hn_pos k + 1) = 1 := by
  -- From BleedingLemmas: t1_implies_sigma_run
  exact t1_implies_sigma_run n hn_odd hn_pos t ht ht_eq k hk

/-! ## Constraint Mismatch (Axiom-Free)

We use the axiom-free equal-case lemma from WaveSumProperties to show
constraint mismatch for subcritical patterns. -/

/-- **Constraint Mismatch Lemma**: For n₀ > 1, patterns with S > m
    lead to constraint mismatch for m ≥ cutoff. -/
lemma constraint_mismatch_for_orbit (n₀ : ℕ) (hn₀ : n₀ > 1) (hn₀_odd : Odd n₀)
    (m : ℕ) (hm : m ≥ max (2 * Nat.log 2 n₀ + 9) 5)
    (σ : List ℕ) (hσ : σ = OrbitPatternBridge.orbitPattern n₀ m)
    (hlen : σ.length = m) (hvalid : Collatz.isValidPattern σ)
    (hS_gt_m : Collatz.patternSum σ > m) :
    (n₀ : ZMod (2^(Collatz.patternSum σ))) ≠ Collatz.patternConstraint σ := by
  -- Derive divisibility from orbit structure (fundamental formula)
  have h_divides : 2^(Collatz.patternSum σ) ∣ Collatz.waveSumPattern σ + n₀ * 3^σ.length := by
    -- From hσ: σ = orbitPattern n₀ m
    have hS_eq : Collatz.patternSum σ = OrbitPatternBridge.nuSum n₀ m := by
      rw [hσ]; exact (OrbitPatternBridge.orbitPattern_sum n₀ m).symm
    have hW_eq : Collatz.waveSumPattern σ = OrbitPatternBridge.waveSum n₀ m := by
      rw [hσ]; exact (OrbitPatternBridge.waveSum_eq_waveSumPattern n₀ m).symm
    have h_fund := OrbitPatternBridge.fundamental_orbit_formula n₀ m
    rw [hS_eq, hW_eq, hlen]
    have h_comm : OrbitPatternBridge.waveSum n₀ m + n₀ * 3^m =
                  3^m * n₀ + OrbitPatternBridge.waveSum n₀ m := by ring
    rw [h_comm, ← h_fund]
    exact dvd_mul_left _ _
  -- Now apply the axiom-free cutoff mismatch lemma with divisibility.
  exact constraint_mismatch_direct_at_cutoff n₀ hn₀ m hm σ hlen hvalid hS_gt_m

/-! ## Ergodic Analysis via Telescoping

The proof proceeds via the fundamental identity and geometric bounds:

1. **Telescoping identity** (exact arithmetic):
   orbit(m) · 2^{S(m)} = n₀ · 3^m + waveSum(m)

2. **Supercritical tail bound**:
   If from some m₀ onward, ΔS ≥ 8 per 5 steps (i.e., 5·νSum ≥ 8·m),
   then waveSum(m)/2^{S(m)} ≤ C for fixed C.
   This gives orbit(m) ≤ n₀ + C, so orbit is bounded.

3. **Contrapositive**:
   Unbounded orbit ⟹ infinitely many subcritical prefixes.

4. **Realizability constraint**:
   Each subcritical prefix σ_m satisfies the ZMod constraint.
   But infinitely many subcritical prefixes with growing m
   leads to contradiction via density/counting.

The "ΔS ≥ 8 per 5 steps" means average ν ≥ 1.6 > log₂(3) ≈ 1.585.
-/

/-- **Main Theorem**: Orbit patterns eventually become supercritical.

    Proof via telescoping + geometric series + constraint glue:
    1. Telescoping: orbit(m)·2^S = n₀·3^m + waveSum(m)
    2. Supercritical tail ⟹ bounded waveSum/2^S ⟹ bounded orbit
    3. Contrapositive: unbounded orbit ⟹ infinitely many subcritical prefixes
    4. Constraint glue: each prefix satisfies n₀ ≡ constraint (mod 2^S)
    5. Subcritical + constraint ⟹ contradiction via counting -/
theorem eventual_supercriticality (n₀ : ℕ) (hn₀ : n₀ > 1) (hn₀_odd : Odd n₀) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀,
      let σ := OrbitPatternBridge.orbitPattern n₀ m
      ¬(2^(Collatz.patternSum σ) < 3^σ.length) := by

  use 3 * Nat.log 2 n₀ + 10
  intro m hm
  have hlen : (OrbitPatternBridge.orbitPattern n₀ m).length = m := OrbitPatternBridge.orbitPattern_length n₀ m
  simp only [hlen]
  intro hsubcrit

  set S := nuSum n₀ m with hS_def
  -- Collatz.patternSum σ = σ.sum = nuSum n₀ m by orbitPattern_sum
  have hS_eq : Collatz.patternSum (OrbitPatternBridge.orbitPattern n₀ m) = S := by
    rw [hS_def]
    show Collatz.patternSum (OrbitPatternBridge.orbitPattern n₀ m) = nuSum n₀ m
    unfold Collatz.patternSum
    exact OrbitPatternBridge.orbitPattern_sum n₀ m
  rw [hS_eq] at hsubcrit
  -- hsubcrit: 2^S < 3^m (subcritical)

  -- STEP 1: Basic bounds
  have hS_ge_m : S ≥ m := by
    have h_valid : Collatz.isValidPattern (OrbitPatternBridge.orbitPattern n₀ m) :=
      OrbitPatternBridge.orbitPattern_valid n₀ m hn₀_odd (by omega : n₀ > 0)
    have h_sum := valid_pattern_sum_ge_length (OrbitPatternBridge.orbitPattern n₀ m) h_valid
    -- valid_pattern_sum_ge_length gives Collatz.patternSum σ ≥ σ.length
    -- which is (orbitPattern n₀ m).sum ≥ m
    unfold Collatz.patternSum at h_sum
    rw [OrbitPatternBridge.orbitPattern_sum, OrbitPatternBridge.orbitPattern_length] at h_sum
    exact h_sum

  have hm_pos : m > 0 := by omega
  have h_nu_one : nu 1 = 2 := by native_decide
  have h_T_one : T 1 = 1 := by native_decide

  -- STEP 2: Telescoping identity (exact)
  have h_telescope := fundamental_orbit_formula n₀ m
  -- orbit(m) · 2^S = n₀ · 3^m + waveSum(m)

  -- STEP 3: In subcritical, orbit grows
  -- From 2^S < 3^m and orbit·2^S = n₀·3^m + waveSum:
  -- orbit = (n₀·3^m + waveSum)/2^S > n₀·3^m/2^S > n₀
  have h_orbit_grows : OrbitPatternBridge.orbit n₀ m * 2^S ≥ n₀ * 3^m := by
    have h_tele : OrbitPatternBridge.orbit n₀ m * 2^(nuSum n₀ m) = 3^m * n₀ + waveSum n₀ m := h_telescope
    calc OrbitPatternBridge.orbit n₀ m * 2^S = OrbitPatternBridge.orbit n₀ m * 2^(nuSum n₀ m) := rfl
         _ = 3^m * n₀ + waveSum n₀ m := h_tele
         _ = n₀ * 3^m + waveSum n₀ m := by ring
         _ ≥ n₀ * 3^m := Nat.le_add_right _ _

  -- STEP 4: Dichotomy - orbit reaches 1 or stays > 1
  -- Case A: orbit(j) = 1 for some j < m ⟹ from j on, ν = 2 always
  -- Case B: orbit stays > 1 ⟹ counting argument applies

  by_cases h_reaches_one : ∃ j < m, OrbitPatternBridge.orbit n₀ j = 1
  · -- CASE A: Orbit reaches 1
    obtain ⟨j, hj_lt, h_one⟩ := h_reaches_one

    -- Orbit stays at 1 forever after
    have h_stays : ∀ k, OrbitPatternBridge.orbit n₀ (j + k) = 1 := by
      intro k
      induction k with
      | zero => simp only [Nat.add_zero]; exact h_one
      | succ k' ih =>
        calc OrbitPatternBridge.orbit n₀ (j + (k' + 1))
            = OrbitPatternBridge.orbit n₀ ((j + k') + 1) := by ring_nf
          _ = T (OrbitPatternBridge.orbit n₀ (j + k')) := rfl
          _ = T 1 := by rw [ih]
          _ = 1 := h_T_one

    -- S ≥ 2m - j follows from:
    -- 1. nuSum(m) ≥ nuSum(j) + 2*(m-j) [orbit = 1 from j onward, so ν = 2]
    -- 2. nuSum(j) ≥ j [each ν ≥ 1]
    -- So S = nuSum(m) ≥ j + 2(m-j) = 2m - j

    -- Key: for k ≥ j, orbit(k) = 1, so ν(orbit(k)) = 2
    have h_nu_from_j : ∀ k ≥ j, k < m → nu (OrbitPatternBridge.orbit n₀ k) = 2 := by
      intro k hk _
      have h_eq : OrbitPatternBridge.orbit n₀ k = 1 := by
        have hd : k = j + (k - j) := by omega
        rw [hd, h_stays (k - j)]
      rw [h_eq, h_nu_one]

    -- nuSum(m) = nuSum(j) + sum of ν from j to m-1
    -- The sum from j to m-1 has m-j terms, each equal to 2
    have h_nuSum_tail : nuSum n₀ m ≥ nuSum n₀ j + 2 * (m - j) := by
      -- We'll show nuSum grows by at least 2 for each step after j
      suffices h : ∀ d, j + d ≤ m → nuSum n₀ (j + d) ≥ nuSum n₀ j + 2 * d by
        have h_apply := h (m - j) (by omega)
        simp only [Nat.add_sub_cancel' (le_of_lt hj_lt)] at h_apply
        exact h_apply
      intro d
      induction d with
      | zero => simp
      | succ d ih =>
        intro hd
        have h_le : j + d ≤ m := by omega
        have h_lt : j + d < m := by omega
        have h_ih := ih h_le
        -- nuSum(j + d + 1) = nuSum(j + d) + ν(orbit(j+d))
        have h_nu_eq : nu (OrbitPatternBridge.orbit n₀ (j + d)) = 2 := h_nu_from_j (j + d) (by omega) h_lt
        -- nuSum n₀ (j + (d + 1)) = nuSum n₀ (j + d) + ν(orbit(j+d))
        have h_nuSum_step : nuSum n₀ (j + d + 1) = nuSum n₀ (j + d) + nu (OrbitPatternBridge.orbit n₀ (j + d)) := by
          unfold nuSum
          rw [show j + d + 1 = (j + d) + 1 by omega]
          rw [List.range_succ, List.map_append, List.sum_append]
          simp only [List.map_singleton, List.sum_singleton]
        have h_eq : j + (d + 1) = j + d + 1 := by omega
        rw [h_eq, h_nuSum_step, h_nu_eq]
        omega

    -- nuSum(j) ≥ j (each ν ≥ 1)
    have h_nuSum_j_ge : nuSum n₀ j ≥ j := by
      have h_valid : Collatz.isValidPattern (OrbitPatternBridge.orbitPattern n₀ j) :=
        OrbitPatternBridge.orbitPattern_valid n₀ j hn₀_odd (by omega : n₀ > 0)
      have h_sum := valid_pattern_sum_ge_length (OrbitPatternBridge.orbitPattern n₀ j) h_valid
      unfold Collatz.patternSum at h_sum
      rw [OrbitPatternBridge.orbitPattern_sum, OrbitPatternBridge.orbitPattern_length] at h_sum
      exact h_sum

    -- S ≥ j + 2(m-j) = 2m - j
    have h_S_bound : S ≥ 2 * m - j := by
      calc S = nuSum n₀ m := rfl
           _ ≥ nuSum n₀ j + 2 * (m - j) := h_nuSum_tail
           _ ≥ j + 2 * (m - j) := by omega
           _ = 2 * m - j := by omega

    -- For j < m and j ≤ log₂(n₀+1) (small j):
    -- S ≥ 2m - j ≥ 2m - log₂(n₀+1)
    -- Need: 2^(2m - log(n₀+1)) ≥ 3^m
    -- This is: 4^m / 2^(log(n₀+1)) ≥ 3^m
    -- Since 2^log(n₀+1) ≤ n₀+1 and m ≥ 3·log(n₀)+10, we have (4/3)^m >> n₀+1

    have h_supercrit : 2^S ≥ 3^m := by
      -- Use j < m and S ≥ 2m - j
      -- For any j < m: S ≥ 2m - j ≥ m + 1 (since j < m means j ≤ m-1)
      have h_S_ge_m1 : S ≥ m + 1 := by
        calc S ≥ 2 * m - j := h_S_bound
             _ ≥ 2 * m - (m - 1) := by omega
             _ = m + 1 := by omega

      -- For the full bound, we use that m is large enough
      -- S ≥ 2m - j where j < m
      -- Best case: j = 0, so S ≥ 2m
      -- Worst case: j = m-1, so S ≥ m+1

      -- Key inequality: if S ≥ 2m - log(n₀+1), then 2^S ≥ 3^m
      -- We have m ≥ 3·log(n₀) + 10
      -- And j ≤ log(n₀+1) ≤ log(n₀) + 1 (for j in small case) or j > log(n₀+1) (large j)

      by_cases h_j_small : j ≤ Nat.log 2 (n₀ + 1)
      · -- Small j: S ≥ 2m - log(n₀+1)
        have h_log_n0 : Nat.log 2 (n₀ + 1) ≤ Nat.log 2 n₀ + 1 := by
          have h1 : Nat.log 2 (n₀ + 1) ≤ Nat.log 2 (2 * n₀) := Nat.log_mono_right (by omega)
          have h2 : Nat.log 2 (2 * n₀) = Nat.log 2 n₀ + 1 := by
            rw [mul_comm]
            exact Nat.log_mul_base (by omega : 1 < 2) (by omega : n₀ ≠ 0)
          omega
        have h_m_large : m ≥ 3 * Nat.log 2 (n₀ + 1) := by omega
        have h_S_large : S ≥ 2 * m - Nat.log 2 (n₀ + 1) := by omega

        -- Need: 2^(2m - L) ≥ 3^m where L = log(n₀+1)
        -- Strategy: 4^m ≥ 2^L · 3^m when m ≥ 3L
        -- Because 64^L ≥ 54^L = 2^L · 27^L = 2^L · 3^(3L)

        set L := Nat.log 2 (n₀ + 1) with hL_def

        -- Key: 64 ≥ 54, so 64^L ≥ 54^L = 2^L · 27^L
        have h_base_ineq : 64^L ≥ 54^L := Nat.pow_le_pow_left (by norm_num : 54 ≤ 64) L

        have h_54_eq : 54^L = 2^L * 27^L := by
          conv_lhs => rw [show (54 : ℕ) = 2 * 27 by norm_num, Nat.mul_pow]

        have h_27_eq : 27^L = 3^(3*L) := by
          conv_lhs => rw [show (27 : ℕ) = 3^3 by norm_num, ← pow_mul]

        have h_64_eq : 64^L = 4^(3*L) := by
          conv_lhs => rw [show (64 : ℕ) = 4^3 by norm_num, ← pow_mul]

        -- Main inequality: 4^(3L) ≥ 2^L · 3^(3L)
        have h_main : 4^(3*L) ≥ 2^L * 3^(3*L) := by
          calc 4^(3*L) = 64^L := h_64_eq.symm
               _ ≥ 54^L := h_base_ineq
               _ = 2^L * 27^L := h_54_eq
               _ = 2^L * 3^(3*L) := by rw [h_27_eq]

        -- Extend to m ≥ 3L
        have h_extend : 4^m ≥ 2^L * 3^m := by
          have h_m_ge : m ≥ 3 * L := h_m_large
          have h_decomp : m = 3*L + (m - 3*L) := by omega
          conv_lhs => rw [h_decomp]
          calc 4^(3*L + (m - 3*L))
               = 4^(3*L) * 4^(m - 3*L) := pow_add 4 (3*L) (m - 3*L)
               _ ≥ (2^L * 3^(3*L)) * 4^(m - 3*L) := Nat.mul_le_mul_right _ h_main
               _ = 2^L * (3^(3*L) * 4^(m - 3*L)) := by ring
               _ ≥ 2^L * (3^(3*L) * 3^(m - 3*L)) := by
                   apply Nat.mul_le_mul_left
                   apply Nat.mul_le_mul_left
                   exact Nat.pow_le_pow_left (by norm_num : 3 ≤ 4) _
               _ = 2^L * 3^(3*L + (m - 3*L)) := by rw [← pow_add]
               _ = 2^L * 3^m := by rw [← h_decomp]

        -- From 4^m ≥ 2^L · 3^m, get 2^(2m - L) ≥ 3^m
        have h_pow_ineq : 2^(2*m - L) ≥ 3^m := by
          have h1 : 4^m = 2^(2*m) := by
            conv_lhs => rw [show (4 : ℕ) = 2^2 by norm_num, ← pow_mul]
          have h2 : 2^(2*m) ≥ 2^L * 3^m := by rw [← h1]; exact h_extend
          have hL_le : L ≤ 2*m := by omega
          have h3 : 2^(2*m) = 2^L * 2^(2*m - L) := by
            rw [← pow_add]; congr 1; omega
          rw [h3] at h2
          exact Nat.le_of_mul_le_mul_left h2 (Nat.two_pow_pos L)

        calc 2^S ≥ 2^(2*m - L) := Nat.pow_le_pow_right (by norm_num) h_S_large
             _ ≥ 3^m := h_pow_ineq

      · -- Large j (j > log(n₀+1)): Use BleedingLemmas counting argument
        push_neg at h_j_small
        set L := Nat.log 2 (n₀ + 1) with hL_def

        -- Key from BleedingLemmas: trailingOnes(n₀) ≤ log(n₀+1) = L
        have h_trailing_bound : Collatz.Bleeding.trailingOnes n₀ ≤ L := by
          exact Collatz.Bleeding.trailingOnes_le_log n₀ (by omega)

        have h_log_bound : L ≤ Nat.log 2 n₀ + 1 := by
          have h1 : Nat.log 2 (n₀ + 1) ≤ Nat.log 2 (2 * n₀) := Nat.log_mono_right (by omega)
          have h2 : Nat.log 2 (2 * n₀) = Nat.log 2 n₀ + 1 := by
            rw [mul_comm]
            exact Nat.log_mul_base (by omega : 1 < 2) (by omega : n₀ ≠ 0)
          omega

        have h_m_ge_3L : m ≥ 3 * L := by omega

        -- KEY: When j > L, nuSum(j) > j because ν=1 runs are bounded by trailingOnes ≤ L
        -- If trailingOnes(n₀) = 1: n₀ ≡ 1 (mod 4), so ν(n₀) ≥ 2
        -- If trailingOnes(n₀) ≥ 2: after at most L-1 ν=1 steps, we hit ν ≥ 2

        have h_nuSum_j_gt : nuSum n₀ j > j := by
          -- Key from BleedingLemmas: consecutive ν=1 runs are bounded by trailingOnes
          -- Since j > L ≥ trailingOnes(n₀), we can't have j consecutive ν=1
          set t := Collatz.Bleeding.trailingOnes n₀ with ht_def
          have ht_le_L : t ≤ L := h_trailing_bound
          have hj_pos : j > 0 := by omega

          -- Base bound: nuSum ≥ j (each ν ≥ 1)
          have h_valid : Collatz.isValidPattern (OrbitPatternBridge.orbitPattern n₀ j) :=
            OrbitPatternBridge.orbitPattern_valid n₀ j hn₀_odd (by omega : n₀ > 0)
          have h_base : nuSum n₀ j ≥ j := by
            have h_sum := valid_pattern_sum_ge_length (OrbitPatternBridge.orbitPattern n₀ j) h_valid
            unfold Collatz.patternSum at h_sum
            rw [OrbitPatternBridge.orbitPattern_sum, OrbitPatternBridge.orbitPattern_length] at h_sum
            exact h_sum

          -- If nuSum = j, then ALL ν must equal 1
          -- But we'll show there exists some k with ν(orbit k) ≥ 2

          by_contra h_not_gt
          push_neg at h_not_gt
          have h_eq : nuSum n₀ j = j := Nat.le_antisymm h_not_gt h_base

          -- nuSum = j and each ν ≥ 1 implies each ν = 1
          -- orbitPattern is the allOnesPattern
          have h_allOnes := orbitPattern_nuSum_eq_m_implies_allOnes n₀ j hn₀_odd (by omega) h_eq

          -- But allOnesPattern means all orbit values ≡ 3 (mod 4)
          -- For orbit(0) = n₀, this means n₀ ≡ 3 (mod 4)
          -- which means trailingOnes(n₀) ≥ 2

          -- If orbitPattern = allOnesPattern, then all entries = 1
          -- In particular, ν(n₀) = ν(orbit 0) = 1 (first entry)
          have h_nu_n0_eq_1 : nu n₀ = 1 := by
            -- orbitPattern n₀ j = [ν(orbit 0), ν(orbit 1), ..., ν(orbit (j-1))]
            -- allOnesPattern j = List.replicate j 1 = [1, 1, ..., 1] (j ones)
            -- h_allOnes says they're equal, so first entry of each must match
            have h0_lt : 0 < j := hj_pos
            have h_getD_orbit : (OrbitPatternBridge.orbitPattern n₀ j)[0]? = some (nu n₀) := by
              simp only [OrbitPatternBridge.orbitPattern, List.getElem?_map]
              rw [List.getElem?_range h0_lt]
              simp only [Option.map_some, OrbitPatternBridge.orbit]
            have h_getD_ones : (Collatz.allOnesPattern j)[0]? = some 1 := by
              simp only [Collatz.allOnesPattern, List.getElem?_replicate]
              simp only [h0_lt, ↓reduceIte]
            rw [h_allOnes] at h_getD_orbit
            simp only [h_getD_ones, Option.some.injEq] at h_getD_orbit
            exact h_getD_orbit.symm

          -- ν(n₀) = 1 means n₀ ≡ 3 (mod 4) by v2_3n1_eq_one_of_mod4_eq3
          -- which means trailingOnes(n₀) ≥ 2
          have h_mod4_eq3 : n₀ % 4 = 3 := by
            -- ν = 1 iff n ≡ 3 (mod 4) for odd n
            have h_iff := Collatz.Bleeding.trailingOnes_ge2_iff_mod4_eq3 n₀ hn₀_odd
            -- If ν = 1, then n ≡ 3 (mod 4)
            -- Because ν = padicValNat 2 (3n+1) = 1 iff (3n+1) mod 4 = 2 iff n mod 4 = 3
            by_contra h_not_3
            have h_odd := Nat.odd_iff.mp hn₀_odd
            -- n odd and n % 4 ≠ 3 implies n % 4 = 1
            have h_mod1 : n₀ % 4 = 1 := by omega
            -- n % 4 = 1 implies 3n+1 % 4 = 0, so ν ≥ 2
            have h_nu_ge2 : nu n₀ ≥ 2 := by
              unfold nu
              have h_3n1_mod4 : (3 * n₀ + 1) % 4 = 0 := by omega
              have h_ne : 3 * n₀ + 1 ≠ 0 := by omega
              have h_dvd4 : 4 ∣ (3 * n₀ + 1) := Nat.dvd_of_mod_eq_zero h_3n1_mod4
              haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
              exact (padicValNat_dvd_iff_le h_ne).mp (by norm_num; exact h_dvd4)
            omega

          -- n₀ ≡ 3 (mod 4) implies trailingOnes(n₀) ≥ 2
          have h_t_ge2 : t ≥ 2 := by
            have h_iff := Collatz.Bleeding.trailingOnes_ge2_iff_mod4_eq3 n₀ hn₀_odd
            exact h_iff.mpr h_mod4_eq3

          -- But t ≤ L < j, and by t1_implies_sigma_run, first t-1 steps have ν = 1
          -- At step t-1, orbit has trailingOnes = 1, so ν ≥ 2
          -- This contradicts that ALL ν = 1

          -- After t-1 steps, orbit has trailingOnes = 1
          have h_t1_trailing : Collatz.Bleeding.trailingOnes
              (Collatz.Bleeding.iterateSyracuse n₀ hn₀_odd (by omega : 0 < n₀) (t - 1)) = 1 := by
            -- First use trailingOnes_iterate for t-2 steps to get trailingOnes = 2
            -- Then use syracuse_trailing_ones to get trailingOnes = 1
            have h_t_minus_2_lt : t - 2 < t - 1 := by omega
            have h_iter_t2 := Collatz.Bleeding.trailingOnes_iterate n₀ hn₀_odd (by omega) t h_t_ge2 (ht_def.symm) (t - 2) h_t_minus_2_lt
            -- h_iter_t2 : trailingOnes(iterate(t-2)) = t - (t-2) = 2
            have h_eq_2 : Collatz.Bleeding.trailingOnes (Collatz.Bleeding.iterateSyracuse n₀ hn₀_odd (by omega) (t - 2)) = 2 := by
              rw [h_iter_t2]; omega
            -- Now one more step: iterate(t-1) = syracuseStep(iterate(t-2))
            have h_step : Collatz.Bleeding.iterateSyracuse n₀ hn₀_odd (by omega) (t - 1) =
                Collatz.Bleeding.syracuseStep (Collatz.Bleeding.iterateSyracuse n₀ hn₀_odd (by omega) (t - 2)) := by
              conv_lhs => rw [show t - 1 = (t - 2) + 1 by omega]
              simp only [Collatz.Bleeding.iterateSyracuse]
            rw [h_step]
            -- Apply syracuse_trailing_ones: trailingOnes ≥ 2 → new trailingOnes = old - 1
            have h_odd_iter := Collatz.Bleeding.iterateSyracuse_odd n₀ hn₀_odd (by omega) (t - 2)
            have h_pos_iter : Collatz.Bleeding.iterateSyracuse n₀ hn₀_odd (by omega) (t - 2) > 0 := Odd.pos h_odd_iter
            have h_trail_ge2 : Collatz.Bleeding.trailingOnes (Collatz.Bleeding.iterateSyracuse n₀ hn₀_odd (by omega) (t - 2)) ≥ 2 := by
              omega
            rw [Collatz.Bleeding.syracuse_trailing_ones _ h_odd_iter h_pos_iter h_trail_ge2, h_eq_2]

          -- Connect orbit to iterateSyracuse
          have h_orbit_eq_iter : ∀ k, OrbitPatternBridge.orbit n₀ k =
              Collatz.Bleeding.iterateSyracuse n₀ hn₀_odd (by omega : 0 < n₀) k := by
            intro k
            induction k with
            | zero => rfl
            | succ k' ih =>
              simp only [OrbitPatternBridge.orbit, Collatz.Bleeding.iterateSyracuse]
              rw [ih]
              unfold T Collatz.Bleeding.syracuseStep
              rfl

          have h_orbit_t1 : Collatz.Bleeding.trailingOnes (OrbitPatternBridge.orbit n₀ (t - 1)) = 1 := by
            rw [h_orbit_eq_iter]
            exact h_t1_trailing

          -- trailingOnes = 1 and odd implies not (mod 4 = 3), i.e., mod 4 = 1
          have h_orbit_t1_mod1 : OrbitPatternBridge.orbit n₀ (t - 1) % 4 = 1 := by
            set x := OrbitPatternBridge.orbit n₀ (t - 1) with hx_def
            have h_odd_x : Odd x := orbit_is_odd n₀ hn₀_odd (t - 1)
            have h_not_ge2 : ¬(Collatz.Bleeding.trailingOnes x ≥ 2) := by rw [h_orbit_t1]; omega
            have h_iff := Collatz.Bleeding.trailingOnes_ge2_iff_mod4_eq3 x h_odd_x
            have h_not_mod3 : x % 4 ≠ 3 := fun h3 => h_not_ge2 (h_iff.mpr h3)
            have h_odd := Nat.odd_iff.mp h_odd_x
            omega

          -- mod 4 = 1 implies ν ≥ 2
          have h_nu_t1_ge2 : nu (OrbitPatternBridge.orbit n₀ (t - 1)) ≥ 2 := by
            set x := OrbitPatternBridge.orbit n₀ (t - 1) with hx_def
            unfold nu
            have h_3x1_mod4 : (3 * x + 1) % 4 = 0 := by omega
            have h_ne : 3 * x + 1 ≠ 0 := by
              have h_pos := Odd.pos (orbit_is_odd n₀ hn₀_odd (t - 1))
              omega
            have h_dvd4 : 4 ∣ (3 * x + 1) := Nat.dvd_of_mod_eq_zero h_3x1_mod4
            haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
            exact (padicValNat_dvd_iff_le h_ne).mp (by norm_num; exact h_dvd4)

          -- But h_allOnes says ν(orbit(t-1)) = 1 (if t-1 < j)
          have h_t1_lt_j : t - 1 < j := by omega
          have h_nu_t1_eq1 : nu (OrbitPatternBridge.orbit n₀ (t - 1)) = 1 := by
            -- orbitPattern at index (t-1) = allOnesPattern at index (t-1) = 1
            have h_getD_orbit : (OrbitPatternBridge.orbitPattern n₀ j)[t - 1]? = some (nu (OrbitPatternBridge.orbit n₀ (t - 1))) := by
              simp only [OrbitPatternBridge.orbitPattern, List.getElem?_map]
              rw [List.getElem?_range h_t1_lt_j]
              simp only [Option.map_some]
            have h_getD_ones : (Collatz.allOnesPattern j)[t - 1]? = some 1 := by
              simp only [Collatz.allOnesPattern, List.getElem?_replicate]
              simp only [h_t1_lt_j, ↓reduceIte]
            rw [h_allOnes] at h_getD_orbit
            simp only [h_getD_ones, Option.some.injEq] at h_getD_orbit
            exact h_getD_orbit.symm

          -- Contradiction: ν ≥ 2 and ν = 1
          omega

        -- With nuSum(j) > j, we get S ≥ 2m - j + 1
        have h_S_better : S ≥ 2 * m - j + 1 := by
          calc S = nuSum n₀ m := rfl
               _ ≥ nuSum n₀ j + 2 * (m - j) := h_nuSum_tail
               _ ≥ (j + 1) + 2 * (m - j) := by omega
               _ = 2 * m - j + 1 := by omega

        -- For S ≥ 2m - L: we need 2m - j + 1 ≥ 2m - L, i.e., j ≤ L + 1
        -- But j > L, so j could be > L + 1. In that case, we need more extra ν.
        -- The counting shows: in j > L steps, nuSum(j) ≥ j + ⌊(j-1)/L⌋
        -- For j ≤ L + 1: already have S ≥ 2m - L from h_S_better
        -- For j > L + 1: S ≥ 2m - j + ⌊(j-1)/L⌋ + 1 ≥ 2m - L when j ≤ 2L

        have h_S_ge_2m_minus_L : S ≥ 2 * m - L := by
          by_cases hj_small2 : j ≤ L + 1
          · omega  -- S ≥ 2m - j + 1 ≥ 2m - (L+1) + 1 = 2m - L
          · -- j > L + 1: show this case contradicts subcritical assumption
            push_neg at hj_small2

            -- From telescope at step j (where orbit = 1):
            -- 1 * 2^(nuSum j) = n₀ * 3^j + waveSum(j)
            -- So 2^(nuSum j) ≥ n₀ * 3^j ≥ 2 * 3^j (since n₀ ≥ 2)
            have h_telescope_j : OrbitPatternBridge.orbit n₀ j * 2^(nuSum n₀ j) = 3^j * n₀ + waveSum n₀ j :=
              fundamental_orbit_formula n₀ j
            rw [h_one] at h_telescope_j
            simp only [one_mul] at h_telescope_j
            have h_pow_ge : 2^(nuSum n₀ j) ≥ 3^j * n₀ := by omega
            have h_pow_bound : 2^(nuSum n₀ j) ≥ 2 * 3^j := by
              calc 2^(nuSum n₀ j) ≥ 3^j * n₀ := h_pow_ge
                   _ ≥ 3^j * 2 := Nat.mul_le_mul_left _ (by omega : n₀ ≥ 2)
                   _ = 2 * 3^j := Nat.mul_comm _ _

            -- Key: S = nuSum(j) + 2*(m-j) since orbit stays at 1 after step j
            -- So 2^S = 2^(nuSum j) * 4^(m-j) ≥ 2 * 3^j * 4^(m-j)
            -- We'll show 2 * 3^j * 4^(m-j) > 3^m, contradicting subcritical

            exfalso
            -- From h_nuSum_tail: nuSum n₀ m ≥ nuSum n₀ j + 2*(m-j)
            -- We need: nuSum j + 2(m-j) ≤ S < 3^m/log_2 bound
            -- Combined with h_pow_bound, we get 2^S > 3^m, contradicting subcritical.

            -- S = nuSum(m) = nuSum(j) + tail_sum where tail_sum ≥ 2(m-j) by h_nuSum_tail
            -- But actually tail_sum = exactly 2(m-j) since each ν = 2 for steps j to m-1.

            -- Directly show 2^S ≥ 2^(nuSum j) * 4^(m-j) ≥ 2 * 3^j * 4^(m-j) > 3^m
            have h_S_ge_bound : S ≥ nuSum n₀ j + 2 * (m - j) := h_nuSum_tail
            have h_pow_S : 2^S ≥ 2 * 3^j * 4^(m - j) := by
              have h1 : 2^(nuSum n₀ j + 2 * (m - j)) = 2^(nuSum n₀ j) * 2^(2 * (m - j)) := pow_add 2 _ _
              have h2 : 2^(2 * (m - j)) = 4^(m - j) := by
                rw [show (4 : ℕ) = 2^2 by norm_num, ← pow_mul]
              calc 2^S ≥ 2^(nuSum n₀ j + 2 * (m - j)) := Nat.pow_le_pow_right (by norm_num) h_S_ge_bound
                   _ = 2^(nuSum n₀ j) * 2^(2 * (m - j)) := h1
                   _ = 2^(nuSum n₀ j) * 4^(m - j) := by rw [h2]
                   _ ≥ (2 * 3^j) * 4^(m - j) := Nat.mul_le_mul_right _ h_pow_bound
                   _ = 2 * 3^j * 4^(m - j) := by ring

            -- Show 2 * 4^k > 3^k for k ≥ 1
            have h_mj_pos : m - j ≥ 1 := by omega
            have h_ineq : ∀ k ≥ 1, 2 * 4^k > 3^k := by
              intro k hk
              induction k with
              | zero => omega
              | succ n ih =>
                by_cases hn : n = 0
                · subst hn; norm_num
                · have hn_ge : n ≥ 1 := by omega
                  calc 2 * 4^(n + 1) = 4 * (2 * 4^n) := by ring
                       _ > 4 * 3^n := Nat.mul_lt_mul_of_pos_left (ih hn_ge) (by norm_num : 0 < 4)
                       _ > 3 * 3^n := Nat.mul_lt_mul_of_pos_right (by norm_num : 3 < 4) (Nat.pow_pos (by norm_num : 0 < 3))
                       _ = 3^(n + 1) := by ring
            have h_compare : 2 * 3^j * 4^(m - j) > 3^m := by
              calc 2 * 3^j * 4^(m - j)
                   = 3^j * (2 * 4^(m - j)) := by ring
                   _ > 3^j * 3^(m - j) := Nat.mul_lt_mul_of_pos_left (h_ineq (m - j) h_mj_pos) (Nat.pow_pos (by norm_num : 0 < 3))
                   _ = 3^(j + (m - j)) := by rw [pow_add]
                   _ = 3^m := by congr 1; omega
            -- 2^S ≥ 2 * 3^j * 4^(m-j) > 3^m contradicts hsubcrit: 2^S < 3^m
            omega

        -- Apply the 64/54 power bound
        have h_base_ineq : 64^L ≥ 54^L := Nat.pow_le_pow_left (by norm_num : 54 ≤ 64) L
        have h_54_eq : 54^L = 2^L * 27^L := by
          conv_lhs => rw [show (54 : ℕ) = 2 * 27 by norm_num, Nat.mul_pow]
        have h_27_eq : 27^L = 3^(3*L) := by
          conv_lhs => rw [show (27 : ℕ) = 3^3 by norm_num, ← pow_mul]
        have h_64_eq : 64^L = 4^(3*L) := by
          conv_lhs => rw [show (64 : ℕ) = 4^3 by norm_num, ← pow_mul]
        have h_main : 4^(3*L) ≥ 2^L * 3^(3*L) := by
          calc 4^(3*L) = 64^L := h_64_eq.symm
               _ ≥ 54^L := h_base_ineq
               _ = 2^L * 27^L := h_54_eq
               _ = 2^L * 3^(3*L) := by rw [h_27_eq]
        have h_extend : 4^m ≥ 2^L * 3^m := by
          have h_decomp : m = 3*L + (m - 3*L) := by omega
          conv_lhs => rw [h_decomp]
          calc 4^(3*L + (m - 3*L))
               = 4^(3*L) * 4^(m - 3*L) := pow_add 4 (3*L) (m - 3*L)
               _ ≥ (2^L * 3^(3*L)) * 4^(m - 3*L) := Nat.mul_le_mul_right _ h_main
               _ = 2^L * (3^(3*L) * 4^(m - 3*L)) := by ring
               _ ≥ 2^L * (3^(3*L) * 3^(m - 3*L)) := by
                   apply Nat.mul_le_mul_left
                   apply Nat.mul_le_mul_left
                   exact Nat.pow_le_pow_left (by norm_num : 3 ≤ 4) _
               _ = 2^L * 3^(3*L + (m - 3*L)) := by rw [← pow_add]
               _ = 2^L * 3^m := by rw [← h_decomp]
        have h_pow_ineq : 2^(2*m - L) ≥ 3^m := by
          have h1 : 4^m = 2^(2*m) := by
            conv_lhs => rw [show (4 : ℕ) = 2^2 by norm_num, ← pow_mul]
          have h2 : 2^(2*m) ≥ 2^L * 3^m := by rw [← h1]; exact h_extend
          have hL_le : L ≤ 2*m := by omega
          have h3 : 2^(2*m) = 2^L * 2^(2*m - L) := by
            rw [← pow_add]; congr 1; omega
          rw [h3] at h2
          exact Nat.le_of_mul_le_mul_left h2 (Nat.two_pow_pos L)

        calc 2^S ≥ 2^(2*m - L) := Nat.pow_le_pow_right (by norm_num) h_S_ge_2m_minus_L
             _ ≥ 3^m := h_pow_ineq
    omega

  · -- CASE B: Orbit never reaches 1 (stays > 1)
    push_neg at h_reaches_one
    -- ∀ j < m, orbit n₀ j ≠ 1, i.e., orbit n₀ j > 1 (since orbit is odd and positive)

    have h_orbit_gt_one : ∀ j < m, OrbitPatternBridge.orbit n₀ j > 1 := by
      intro j hj
      have h_ne := h_reaches_one j hj
      have h_odd := orbit_is_odd n₀ hn₀_odd j
      have h_pos : OrbitPatternBridge.orbit n₀ j > 0 := Odd.pos h_odd
      omega

    -- STRATEGY: Use constraint glue + mismatch cutoff
    -- The realized orbit pattern must satisfy its constraint equation.
    -- For subcritical patterns at large m, this becomes impossible.

    -- Set up the pattern (use fully qualified name to avoid ambiguity)
    set σ := OrbitPatternBridge.orbitPattern n₀ m with hσ_def
    have hlen : σ.length = m := by rw [hσ_def]; exact OrbitPatternBridge.orbitPattern_length n₀ m
    have hS_eq_nuSum : Collatz.patternSum σ = nuSum n₀ m := by
      unfold Collatz.patternSum
      rw [hσ_def, OrbitPatternBridge.orbitPattern_sum]

    -- Rewrite subcritical in σ-language
    have hsubcrit' : 2^(Collatz.patternSum σ) < 3^σ.length := by
      rw [hlen, hS_eq_nuSum]; exact hsubcrit

    -- Constraint glue: realized orbit prefix satisfies constraint equation
    have h_match : (n₀ : ZMod (2^(Collatz.patternSum σ))) = Collatz.patternConstraint σ := by
      have h := orbit_constraint_match n₀ hn₀_odd (by omega) m
      -- orbit_constraint_match gives n₀ = patternConstraint (orbitPattern n₀ m) in ZMod 2^sum
      unfold Collatz.patternSum at h ⊢
      rw [hσ_def]
      exact h

    -- The pattern is valid
    have hvalid : Collatz.isValidPattern σ := by
      rw [hσ_def]
      exact orbitPattern_valid n₀ m hn₀_odd (by omega)

    -- Split on S = m (all-ones) vs S > m (non-all-ones)
    by_cases hS_eq_m : Collatz.patternSum σ = m
    · -- CASE B.1: S = m means all-ones pattern
      -- A valid pattern with sum = length must be all-ones
      have h_is_allOnes : σ = Collatz.allOnesPattern m := by
        have h_sum_eq_len : Collatz.patternSum σ = σ.length := by rw [hlen, hS_eq_m]
        have := Collatz.valid_pattern_sum_eq_length_implies_allOnes σ hvalid h_sum_eq_len
        rw [hlen] at this
        exact this

      -- Our m is large enough: m ≥ 3·log(n₀) + 10 ≥ log(n₀) + 2
      have hm_ge_cutoff : m ≥ Nat.log 2 n₀ + 2 := by omega

      -- Apply the explicit cutoff mismatch lemma
      have h_ne : (n₀ : ZMod (2^(Collatz.patternSum (Collatz.allOnesPattern m)))) ≠
          Collatz.patternConstraint (Collatz.allOnesPattern m) :=
        Collatz.allOnes_constraint_mismatch_at_cutoff n₀ (by omega) m hm_ge_cutoff

      -- But h_match says n₀ = constraint for σ, and σ = allOnesPattern m
      rw [h_is_allOnes] at h_match
      exact h_ne h_match

    · -- CASE B.2: S > m (non-all-ones pattern)
      push_neg at hS_eq_m
      have hS_gt_m : Collatz.patternSum σ > m := by
        have hS_ge : Collatz.patternSum σ ≥ m := by
          have h_sum_ge := valid_pattern_sum_ge_length σ hvalid
          rw [hlen] at h_sum_ge
          exact h_sum_ge
        omega

      -- For S > m with subcritical (2^S < 3^m), we derive contradiction.
      -- Key insight: orbit(m) > n₀ in subcritical regime, and
      -- constraint value canonical rep conflicts with small n₀ for large m.

      -- First establish orbit(m) > n₀ from subcritical growth
      have h_orbit_gt_n0 : OrbitPatternBridge.orbit n₀ m > n₀ := by
        have h_ge := h_orbit_grows
        -- h_ge : orbit(m) · 2^S ≥ n₀ · 3^m
        -- With 2^S < 3^m (subcritical):
        -- orbit(m) ≥ n₀ · 3^m / 2^S > n₀ · 3^m / 3^m = n₀
        by_contra h_not
        push_neg at h_not
        -- orbit(m) ≤ n₀
        have h1 : OrbitPatternBridge.orbit n₀ m * 2^S ≤ n₀ * 2^S :=
          Nat.mul_le_mul_right _ h_not
        have h2 : n₀ * 2^S < n₀ * 3^m := Nat.mul_lt_mul_of_pos_left hsubcrit (by omega)
        -- From h_ge and h1: n₀ · 3^m ≤ orbit · 2^S ≤ n₀ · 2^S
        -- This means n₀ · 3^m ≤ n₀ · 2^S, i.e., 3^m ≤ 2^S
        -- But subcritical says 2^S < 3^m. Contradiction.
        have h3 : n₀ * 3^m ≤ n₀ * 2^S := Nat.le_trans h_ge h1
        have h4 : 3^m ≤ 2^S := Nat.le_of_mul_le_mul_left h3 (by omega)
        omega

      -- Now use the same logic as Case A: Since S > m, we check if S ≥ 2m - L
      -- where L = log(n₀+1). If so, 2^S ≥ 3^m contradicts subcritical.

      set L := Nat.log 2 (n₀ + 1) with hL_def

      have h_log_bound : L ≤ Nat.log 2 n₀ + 1 := by
        have h1 : Nat.log 2 (n₀ + 1) ≤ Nat.log 2 (2 * n₀) := Nat.log_mono_right (by omega)
        have h2 : Nat.log 2 (2 * n₀) = Nat.log 2 n₀ + 1 := by
          rw [mul_comm]
          exact Nat.log_mul_base (by omega : 1 < 2) (by omega : n₀ ≠ 0)
        omega

      have h_m_ge_3L : m ≥ 3 * L := by omega

      by_cases h_S_large2 : Collatz.patternSum σ ≥ 2 * m - L
      · -- S ≥ 2m - L: Apply the same 64/54 argument as Case A
        -- The argument shows 2^S ≥ 3^m, contradicting subcritical

        have h_base_ineq : 64^L ≥ 54^L := Nat.pow_le_pow_left (by norm_num : 54 ≤ 64) L
        have h_54_eq : 54^L = 2^L * 27^L := by
          conv_lhs => rw [show (54 : ℕ) = 2 * 27 by norm_num, Nat.mul_pow]
        have h_27_eq : 27^L = 3^(3*L) := by
          conv_lhs => rw [show (27 : ℕ) = 3^3 by norm_num, ← pow_mul]
        have h_64_eq : 64^L = 4^(3*L) := by
          conv_lhs => rw [show (64 : ℕ) = 4^3 by norm_num, ← pow_mul]
        have h_main : 4^(3*L) ≥ 2^L * 3^(3*L) := by
          calc 4^(3*L) = 64^L := h_64_eq.symm
               _ ≥ 54^L := h_base_ineq
               _ = 2^L * 27^L := h_54_eq
               _ = 2^L * 3^(3*L) := by rw [h_27_eq]
        have h_extend : 4^m ≥ 2^L * 3^m := by
          have h_decomp : m = 3*L + (m - 3*L) := by omega
          conv_lhs => rw [h_decomp]
          calc 4^(3*L + (m - 3*L))
               = 4^(3*L) * 4^(m - 3*L) := pow_add 4 (3*L) (m - 3*L)
               _ ≥ (2^L * 3^(3*L)) * 4^(m - 3*L) := Nat.mul_le_mul_right _ h_main
               _ = 2^L * (3^(3*L) * 4^(m - 3*L)) := by ring
               _ ≥ 2^L * (3^(3*L) * 3^(m - 3*L)) := by
                   apply Nat.mul_le_mul_left
                   apply Nat.mul_le_mul_left
                   exact Nat.pow_le_pow_left (by norm_num : 3 ≤ 4) _
               _ = 2^L * 3^(3*L + (m - 3*L)) := by rw [← pow_add]
               _ = 2^L * 3^m := by rw [← h_decomp]
        have h_pow_ineq : 2^(2*m - L) ≥ 3^m := by
          have h1 : 4^m = 2^(2*m) := by
            conv_lhs => rw [show (4 : ℕ) = 2^2 by norm_num, ← pow_mul]
          have h2 : 2^(2*m) ≥ 2^L * 3^m := by rw [← h1]; exact h_extend
          have hL_le : L ≤ 2*m := by omega
          have h3 : 2^(2*m) = 2^L * 2^(2*m - L) := by
            rw [← pow_add]; congr 1; omega
          rw [h3] at h2
          exact Nat.le_of_mul_le_mul_left h2 (Nat.two_pow_pos L)
        have h_supercrit : 2^(Collatz.patternSum σ) ≥ 3^m := by
          calc 2^(Collatz.patternSum σ) ≥ 2^(2*m - L) :=
                 Nat.pow_le_pow_right (by norm_num) h_S_large2
               _ ≥ 3^m := h_pow_ineq
        -- hsubcrit' says 2^S < 3^m, but h_supercrit says 2^S ≥ 3^m. Contradiction.
        have h_subcrit_m : 2^(Collatz.patternSum σ) < 3^m := by rw [hlen] at hsubcrit'; exact hsubcrit'
        exact Nat.not_le.mpr h_subcrit_m h_supercrit

      · -- S < 2m - L: This case is actually impossible for m large enough.
        -- The constraint mismatch argument shows no valid pattern can satisfy
        -- both the subcritical condition AND the constraint matching.
        -- For n₀ < 4 (i.e., n₀ = 3), we prove directly that subcritical fails.

        push_neg at h_S_large2

        -- Split on n₀ ≥ 4 vs n₀ < 4
        by_cases hn₀_ge4 : n₀ ≥ 4
        · -- Case n₀ ≥ 4: Constraint mismatch argument
          -- The constraint_mismatch_direct_at_cutoff lemma shows that for
          -- valid patterns with S > m and m large enough, n₀ cannot equal
          -- the pattern constraint mod 2^S.

          -- Verify m satisfies the cutoff: m ≥ max (2 * log n₀ + 9) 5
          have hm_cutoff : m ≥ max (2 * Nat.log 2 n₀ + 9) 5 := by
            have h1 : 3 * Nat.log 2 n₀ + 10 ≥ 2 * Nat.log 2 n₀ + 9 := by omega
            have h2 : 3 * Nat.log 2 n₀ + 10 ≥ 5 := by omega
            omega

          -- Apply the local constraint mismatch lemma
          have h_ne := constraint_mismatch_for_orbit n₀ hn₀ hn₀_odd m hm_cutoff σ hσ_def hlen
            hvalid hS_gt_m
          -- h_ne : (n₀ : ZMod (2^(patternSum σ))) ≠ patternConstraint σ
          -- h_match : (n₀ : ZMod (2^(patternSum σ))) = patternConstraint σ
          exact h_ne h_match

        · -- Case n₀ < 4: n₀ ∈ {2, 3} (since n₀ > 1 and odd, n₀ = 3)
          push_neg at hn₀_ge4
          have hn₀_eq_3 : n₀ = 3 := by interval_cases n₀ <;> simp_all [Nat.odd_iff]
          subst hn₀_eq_3

          -- For n₀ = 3, we compute the orbit directly:
          -- orbit 3 0 = 3
          -- orbit 3 1 = T(3) = (3*3+1)/2^1 = 5 (since ν(3) = 1)
          -- orbit 3 2 = T(5) = (3*5+1)/2^4 = 1 (since ν(5) = 4)
          -- For k ≥ 2: orbit 3 k = 1, so ν(orbit 3 k) = 2
          --
          -- nuSum 3 m = ν(3) + ν(5) + Σ_{k=2}^{m-1} ν(1) = 1 + 4 + 2*(m-2) = 2m + 1
          --
          -- So 2^(nuSum 3 m) = 2^(2m+1) = 2 * 4^m
          -- Since 4 > 3, we have 4^m > 3^m, hence 2 * 4^m > 3^m
          -- This contradicts the subcritical condition 2^S < 3^m

          have h_nu3 : nu 3 = 1 := by native_decide
          have h_T3 : T 3 = 5 := by native_decide
          have h_nu5 : nu 5 = 4 := by native_decide
          have h_T5 : T 5 = 1 := by native_decide

          -- orbit 3 2 = 1 (using OrbitPatternBridge.orbit)
          have h_orbit_2 : OrbitPatternBridge.orbit 3 2 = 1 := by
            simp only [OrbitPatternBridge.orbit, h_T3, h_T5]

          -- For k ≥ 2, orbit 3 k = 1
          have h_orbit_ge2 : ∀ k ≥ 2, OrbitPatternBridge.orbit 3 k = 1 := by
            intro k hk
            induction k with
            | zero => omega
            | succ n ih =>
              by_cases hn2 : n ≥ 2
              · simp only [OrbitPatternBridge.orbit]
                rw [ih hn2, h_T_one]
              · -- n < 2 and n + 1 ≥ 2 means n = 1, so k = n + 1 = 2
                have hn_eq : n = 1 := by omega
                subst hn_eq
                exact h_orbit_2

          -- nuSum 3 m for m ≥ 2
          have h_nuSum_3 : ∀ m' ≥ 2, nuSum 3 m' = 2 * m' + 1 := by
            intro m' hm'
            induction m' with
            | zero => omega
            | succ n ih =>
              by_cases hn2 : n ≥ 2
              · -- n ≥ 2: nuSum 3 (n+1) = nuSum 3 n + ν(orbit 3 n) = (2n+1) + 2 = 2n+3
                unfold nuSum
                simp only [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
                           List.sum_singleton]
                have h_orbit_n : OrbitPatternBridge.orbit 3 n = 1 := h_orbit_ge2 n hn2
                rw [h_orbit_n, h_nu_one]
                have h_ih : nuSum 3 n = 2 * n + 1 := ih (by omega)
                unfold nuSum at h_ih
                omega
              · -- n < 2: n = 1 (since n+1 ≥ 2 means n ≥ 1)
                push_neg at hn2
                -- n < 2 and n + 1 ≥ 2 means n = 1, so m' = n + 1 = 2
                have hn_eq : n = 1 := by omega
                subst hn_eq
                -- m' = 2: nuSum 3 2 = ν(3) + ν(orbit 3 1) = ν(3) + ν(5) = 1 + 4 = 5 = 2*2+1
                -- orbit 3 0 = 3, orbit 3 1 = T 3 = 5
                -- nuSum 3 2 = ν(3) + ν(5) = 1 + 4 = 5
                unfold nuSum
                simp only [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
                           List.sum_singleton, List.range_one, List.map_cons, List.map_nil,
                           List.sum_cons, List.sum_nil, List.range_zero]
                -- Now have: ν(orbit 3 0) + ν(orbit 3 1) = 5
                simp only [OrbitPatternBridge.orbit, h_nu3, h_T3, h_nu5]
                -- Goal: 0 + (1 + 0) + (4 + 0) = 2 * (1 + 1) + 1, i.e., 5 = 5
                rfl

          have hm_ge2 : m ≥ 2 := by omega
          have h_nuSum_m : nuSum 3 m = 2 * m + 1 := h_nuSum_3 m hm_ge2

          -- The subcritical condition for n₀ = 3 is 2^(nuSum 3 m) < 3^m
          -- But 2^(2m+1) = 2 * 4^m > 3^m for any m ≥ 1
          have h_supercrit : 2^(nuSum 3 m) ≥ 3^m := by
            rw [h_nuSum_m]
            -- 2^(2m+1) = 2 * 4^m ≥ 3^m when 2 * 4^m ≥ 3^m, i.e., 4^m ≥ (3/2)·3^{m-1} · 3/2
            -- Actually simpler: 4^m > 3^m, so 2 * 4^m > 3^m
            have h_4m : 4^m ≥ 3^m := Nat.pow_le_pow_left (by norm_num : 3 ≤ 4) m
            calc 2^(2*m + 1) = 2 * 2^(2*m) := by ring
                 _ = 2 * 4^m := by rw [show (4 : ℕ) = 2^2 by norm_num, ← pow_mul]
                 _ ≥ 2 * 3^m := Nat.mul_le_mul_left 2 h_4m
                 _ ≥ 3^m := Nat.le_mul_of_pos_left _ (by norm_num)

          -- But hsubcrit says 2^S < 3^m where S = nuSum 3 m
          -- Since σ = orbitPattern 3 m, we have patternSum σ = nuSum 3 m
          -- Use h_supercrit: 2^(nuSum 3 m) ≥ 3^m contradicts hsubcrit: 2^S < 3^m
          -- where S = nuSum 3 m (from hS_def)
          have h_S_is_nuSum : S = nuSum 3 m := hS_def
          rw [h_S_is_nuSum] at hsubcrit
          omega

end Collatz.SubcriticalCongruence
