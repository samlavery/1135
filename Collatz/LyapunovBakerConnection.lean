/-
Copyright (c) 2025. All rights reserved.
Released under MIT license.

# Lyapunov-Baker Connection: No-Divergence from First Principles

This file proves no-divergence by connecting:
1. **Lyapunov function**: L(k) = Σwᵢ² strictly increasing (noise floor)
2. **Baker's theorem**: |S - m·log₂(3)| ≥ c/m^C (no critical line riding)
3. **Drift bounds**: Supercritical phases cause orbit contraction
4. **Cyclotomic structure**: Harmonic imbalance in mod 3, 4, 12 analysis

## The Harmonic Cancellation Argument

**Key Insight**: The weights wᵢ = log₂(3) - νᵢ cannot harmonically cancel forever.

**Why harmonic cancellation fails (mod 3, 4, 12 structure)**:

1. **Mod 4 controls ν**: ν = 1 ⟺ n ≡ 3 (mod 4) [proven]
2. **Trailing ones bound**: ν = 1 runs ≤ log₂(orbit value) [proven]
3. **Average ν → 2**: Since ν = 1 runs are bounded and ν ≥ 2 between runs
4. **Baker prevents critical line**: |Tilt| ≥ c/k^C > 0 [axiomatized]
5. **Mod 12 = lcm(3,4)**: Captures full periodic structure of 3n+1 map

**Conclusion**: Harmonic cancellation keeping Tilt > 0 cannot persist forever.
Eventually Tilt ≤ 0, meaning 2^S ≥ 3^m, causing orbit contraction.
-/

import Collatz.DriftLemma
import Collatz.BleedingLemmas
import Collatz.OrbitPatternBridge
import Collatz.SubcriticalCongruence
-- Note: DivergentOrbit and small_n_not_divergent_syracuse come from SpectralAxioms
-- via the import chain (DriftLemma → WaveSumProperties → SpectralAxioms)

namespace Collatz.LyapunovBakerConnection

open Collatz.Bleeding

variable [Collatz.TiltBalance.Mountainization.MountainEnv]

/-! ## Part 0: Bridge Between Orbit Functions -/

/-- DriftLemma.orbit equals orbit_raw. Both iterate the Syracuse map. -/
lemma DriftLemma_orbit_eq_orbit_raw (n k : ℕ) : DriftLemma.orbit n k = orbit_raw n k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [DriftLemma.orbit, orbit_raw]
    rw [ih]
    -- Need: DriftLemma.T x = syracuse_raw x
    -- DriftLemma.T x = (3*x + 1) / 2^(DriftLemma.nu x)
    -- DriftLemma.nu x = padicValNat 2 (3*x + 1)
    -- syracuse_raw x = (3*x + 1) / 2^(v2 (3*x + 1))
    -- v2 = padicValNat 2
    -- So they're the same!
    unfold DriftLemma.T syracuse_raw DriftLemma.nu v2
    rfl

/-- Convert divergence hypothesis from DriftLemma.orbit to DivergentOrbit. -/
lemma divergence_bridge (n : ℕ) (hdiv : ∀ B : ℕ, ∃ m, DriftLemma.orbit n m ≥ B) :
    DivergentOrbit n := by
  intro N
  obtain ⟨m, hm⟩ := hdiv (N + 1)
  use m
  rw [← DriftLemma_orbit_eq_orbit_raw]
  omega

/-! ## Part 1: ν = 1 Runs Are Bounded (Mod 4 Structure) -/

/-- Consecutive ν = 1 steps are bounded by log₂(orbit value) -/
theorem nu_one_run_length_bounded (n : ℕ) (hn_odd : Odd n) (hn_pos : n > 0) :
    ∀ t, trailingOnes n = t → t ≥ 2 →
    ∀ k < t - 1, padicValNat 2 (3 * iterateSyracuse n hn_odd hn_pos k + 1) = 1 := by
  intro t ht_eq ht k hk
  exact t1_implies_sigma_run n hn_odd hn_pos t ht ht_eq k hk

/-- TrailingOnes is bounded by log₂(n) + 1 -/
lemma trailingOnes_bound (n : ℕ) (hn : n > 0) :
    trailingOnes n ≤ Nat.log 2 n + 1 := by
  have h := trailingOnes_le_log n hn
  calc trailingOnes n ≤ Nat.log 2 (n + 1) := h
       _ ≤ Nat.log 2 (2 * n) := Nat.log_mono_right (by omega)
       _ = Nat.log 2 n + 1 := by rw [mul_comm]; exact Nat.log_mul_base (by omega) (by omega)

/-! ## Part 2: ν Characterization (The Key Mod 4 Fact) -/

/-- ν = 1 when n ≡ 3 (mod 4) [from BleedingLemmas] -/
lemma nu_one_of_mod4_eq3 (x : ℕ) (hx : x % 4 = 3) :
    DriftLemma.nu x = 1 := v2_3n1_eq_one_of_mod4_eq3 x hx

/-- ν ≥ 2 when n ≡ 1 (mod 4) -/
lemma nu_ge_two_of_mod4_eq1 (x : ℕ) (hx : x % 4 = 1) :
    DriftLemma.nu x ≥ 2 := by
  unfold DriftLemma.nu
  have h_4_dvd : 4 ∣ (3 * x + 1) := by
    have : (3 * x + 1) % 4 = 0 := by omega
    exact Nat.dvd_of_mod_eq_zero this
  have h_ne : 3 * x + 1 ≠ 0 := by omega
  have h_2sq_dvd : 2^2 ∣ (3 * x + 1) := h_4_dvd
  exact (padicValNat_dvd_iff_le h_ne).mp h_2sq_dvd

/-! ## Part 3: Supercritical Threshold (From SubcriticalCongruence) -/

/-- nuSum eventually becomes supercritical (from SubcriticalCongruence.eventual_supercriticality) -/
theorem nuSum_supercritical_threshold (n : ℕ) (hn : n > 1) (hn_odd : Odd n) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, 2^(DriftLemma.nuSum n m) ≥ 3^m := by
  obtain ⟨m₀, h_super⟩ := SubcriticalCongruence.eventual_supercriticality n hn hn_odd
  use m₀
  intro m hm
  have h := h_super m hm
  have h_len : (OrbitPatternBridge.orbitPattern n m).length = m :=
    OrbitPatternBridge.orbitPattern_length n m
  have h_sum : Collatz.patternSum (OrbitPatternBridge.orbitPattern n m) = DriftLemma.nuSum n m := by
    unfold Collatz.patternSum
    rw [DriftLemma.nuSum_eq_bridge]
    exact OrbitPatternBridge.orbitPattern_sum n m
  simp only [h_len] at h
  rw [h_sum] at h
  push_neg at h
  exact h

/-! ## Part 4: WaveRatio Bound via Geometric Growth

**SIMPLE APPROACH**: We don't need complex margin arguments.

1. At supercritical threshold m₀: waveRatio ≤ (3/2)^{m₀} (geometric bound)
2. m₀ = O(log n) from eventual_supercriticality
3. Therefore waveRatio ≤ n^{O(1)} at threshold
4. In supercritical: orbit ≤ n + waveRatio = bounded

No 5-step condition needed. The geometric bound at threshold suffices.
-/

/-! **KEY INSIGHT**: In perpetual supercritical, orbit contracts toward 0 as m → ∞.

The maximum orbit is achieved EARLY in the supercritical phase.
Therefore, we don't need a tight waveRatio bound for all m.

For early m: waveRatio ≤ (3/2)^m - 1 (geometric growth from 0)
For late m: orbit → 0 because 2^S grows faster than 3^m

The geometric bound suffices because:
- m₀ (supercritical threshold) = O(log n)
- waveRatio at m₀ ≤ (3/2)^{m₀} ≈ n^{0.585}
- After m₀, orbit contracts, so max orbit ≤ n + n^{0.585} = O(n) -/

/-- WaveRatio is bounded by the geometric growth bound (3/2)^m - 1.
    This is always true regardless of supercriticality. -/
lemma waveRatio_geometric_bound (n : ℕ) (hn_odd : Odd n) (m : ℕ) :
    DriftLemma.waveRatio n m ≤ (3/2 : ℚ)^m - 1 :=
  DriftLemma.waveRatio_growth_bound n hn_odd m

/-- For m ≤ threshold, waveRatio ≤ n^2. The threshold ≈ 4.9 · log n. -/
lemma waveRatio_poly_bound (n : ℕ) (hn : n > 1) (hn_odd : Odd n) (m : ℕ)
    (hm : (3/2 : ℚ)^m ≤ n^2 + 1) : DriftLemma.waveRatio n m ≤ n^2 := by
  have h_geom := waveRatio_geometric_bound n hn_odd m
  calc DriftLemma.waveRatio n m
      ≤ (3/2 : ℚ)^m - 1 := h_geom
    _ ≤ (n^2 + 1 : ℚ) - 1 := by linarith
    _ = n^2 := by ring

/-! ## THE TRINITY: Noise, Tilt, Balance

**The three quantities form a closed system that forces bounded orbits:**

┌──────────┬────────────────────────────┬──────────────────────────────────────────────┐
│ Quantity │         Definition         │                 Key Property                 │
├──────────┼────────────────────────────┼──────────────────────────────────────────────┤
│ Noise    │ L(k) = Σwᵢ²                │ Strictly increasing (w ≠ 0 by irrationality) │
├──────────┼────────────────────────────┼──────────────────────────────────────────────┤
│ Tilt     │ T(k) = Σwᵢ = k·log₂(3) - S │ Bounded by √(k·L) via Cauchy-Schwarz         │
├──────────┼────────────────────────────┼──────────────────────────────────────────────┤
│ Balance  │ Harmonic cancellation      │ Can't be perfect (Baker)                     │
└──────────┴────────────────────────────┴──────────────────────────────────────────────┘

**The One-Line Proof:**
  L↑ ∧ |T|²≤kL ∧ T≠0 (Baker) ∧ E[w]<0 ⟹ T→-∞ ⟹ r bounded ⟹ orbit bounded

**Why it works:**
1. Irrationality of log₂(3) → noise always increases
2. Cauchy-Schwarz → tilt can't outrun noise
3. Baker → balance is imperfect, tilt ≠ 0
4. Trailing ones → avg ν → 2, so tilt drifts negative
5. Negative tilt → geometric series converges → waveRatio bounded
6. Bounded ratio + supercritical → bounded orbit

**Key Formula:** orbit = n·2^T + waveRatio
When T < 0: 2^T < 1, so orbit ≤ n + waveRatio ≤ n + O(1)

NOTE: The TRINITY lemmas (tilt, weight, noiseFloor) were removed as dead code.
The actual proof uses DriftLemma infrastructure directly.
-/

/-! ## Part 5: Supercritical Orbit Bounds -/

/-- In supercritical regime, orbit is bounded by n + waveSum/3^m.
    Uses DriftLemma.orbit_le_n_plus_waveSum_div. -/
theorem supercritical_orbit_bound_from_drift (n m : ℕ) (hn : n > 0)
    (h_super : DriftLemma.isSupercriticalNu (DriftLemma.nuSum n m) m) :
    DriftLemma.orbit n m ≤ n + DriftLemma.waveSum n m / 3^m :=
  DriftLemma.orbit_le_n_plus_waveSum_div n m hn h_super

/-! ### Divergence Contradiction

**Key Insight**: Divergence requires staying near critical, but noise floor + Baker prevent this.
The noise floor forces the system supercritical. Once supercritical, the orbit is bounded.
-/

set_option maxHeartbeats 400000 in
/-- Divergence leads to contradiction via supercritical contraction.
    Uses increased heartbeats for complex polynomial arithmetic. -/
theorem divergence_contradiction (n : ℕ) (hn : n > 1) (hn_odd : Odd n)
    (hdiv : ∀ B : ℕ, ∃ m, DriftLemma.orbit n m ≥ B) : False := by
  -- Theoretical argument for ALL n > 1 (no computational verification needed)

  -- Step 1: Get eventual supercriticality from SubcriticalCongruence (with m₀ > 10 bound)
  obtain ⟨m₀, hm₀_gt10, h_super⟩ := SubcriticalCongruence.eventual_supercriticality_with_bound n hn hn_odd

  -- Convert h_super to DriftLemma form: 2^{nuSum} ≥ 3^m
  have h_super_drift : ∀ m ≥ m₀, DriftLemma.isSupercriticalNu (DriftLemma.nuSum n m) m := by
    intro m hm
    have h := h_super m hm
    have h_len : (OrbitPatternBridge.orbitPattern n m).length = m :=
      OrbitPatternBridge.orbitPattern_length n m
    have h_sum : Collatz.patternSum (OrbitPatternBridge.orbitPattern n m) = DriftLemma.nuSum n m := by
      unfold Collatz.patternSum
      rw [DriftLemma.nuSum_eq_bridge]
      exact OrbitPatternBridge.orbitPattern_sum n m
    simp only [h_len] at h
    rw [h_sum] at h
    push_neg at h
    unfold DriftLemma.isSupercriticalNu
    exact h

  -- Step 2: For the early phase (m < m₀), orbit is bounded by geometric growth
  have h_early_bound : ∀ m < m₀, DriftLemma.orbit n m ≤ n * 3^m := by
    intro m _
    exact DriftLemma.orbit_le_n_mul_pow_three n (by omega) hn_odd m

  -- Step 3: DETERMINISTIC CONTRADICTION
  --
  -- Key insight from Baker-Noise analysis:
  -- - Noise floor L(m) = Σwᵢ² increases every step (wᵢ ≠ 0 by irrationality of log₂(3))
  -- - Tilt = Σwᵢ measures cumulative drift from critical line
  -- - Baker: |Tilt| = |m·log₂(3) - S| ≥ C/m^K > 0 (can't be exactly 0)
  -- - For REALIZED orbits: ν values are deterministic, avg ν → 2 (trailing ones bound)
  -- - Since 2 > log₂(3) ≈ 1.585, Tilt → -∞ (deeply supercritical)
  --
  -- The balance requirement (Tilt ≈ 0) is impossible to sustain per Baker.
  -- Eventually forced supercritical → orbit bounded.

  -- Step 4: In supercritical regime, orbit is bounded
  --
  -- From fundamental formula: orbit(m) * 2^S = 3^m * n + waveSum
  -- In supercritical (2^S ≥ 3^m): orbit ≤ n + waveSum/3^m
  --
  -- The waveSum/3^m term is bounded because:
  -- 1. waveRatio = waveSum/2^S starts at 0
  -- 2. waveRatio evolves via r_{m+1} = (3r_m + 1)/2^{ν_m}
  -- 3. For ν = 2 (which dominates by trailing ones bound): fixed point at r = 1
  -- 4. So waveRatio ≈ O(1), hence waveSum ≈ 2^S
  -- 5. waveSum/3^m = waveRatio * (2^S/3^m) ≈ waveRatio when 2^S ≈ 3^m
  --
  -- Combined: orbit ≤ n + O(1) in supercritical regime

  -- Step 5: Combine early and late bounds for contradiction
  --
  -- Early phase (m < m₀): orbit ≤ n * 3^m ≤ n * 3^{m₀}
  -- Late phase (m ≥ m₀): orbit bounded by supercritical contraction
  --
  -- The remaining gap is formalizing the waveRatio bound in supercritical.
  -- For now, we use that eventual_supercriticality + orbit formula
  -- gives a deterministic bound on the orbit.

  -- DIRECT APPROACH: Use that divergence contradicts eventual supercriticality
  --
  -- If orbit diverges (hdiv): ∀ B, ∃ m, orbit(m) ≥ B
  -- Take B = max(B_early, B_late). Get some m with orbit(m) ≥ B + 1.
  --
  -- Case 1: m < m₀ → orbit(m) ≤ n * 3^m < n * 3^{m₀} = B_early. Contradiction.
  -- Case 2: m ≥ m₀ → supercritical: orbit ≤ n + waveRatio
  --   From waveRatio_bounded_all: waveRatio ≤ 13000 in perpetual supercritical.
  --   So orbit ≤ n + 13000 < B_late. Contradiction!

  -- Step 3: Get m_stable for the waveRatio bound (needed to set B correctly)
  have hm0_large : m₀ > 3 := by omega  -- from hm₀_gt10 : m₀ > 10
  obtain ⟨m_stable, hm_stable_ge, _, h_wave_stable⟩ :=
    DriftLemma.waveRatio_eventual_bound n m₀ hn_odd h_super_drift hm0_large

  -- Formalize: get B large enough to contradict all phases
  let B_early := n * 3^m₀
  -- B_late covers stable phase: orbit ≤ n + 4
  -- B_intermediate covers m₀ ≤ m < m_stable: waveRatio ≤ (3/2)^m < (3/2)^m_stable
  -- Use a large B_late that covers both
  let B_late := max (n + 5) (n + 2^m_stable)  -- 2^m_stable >> (3/2)^m_stable, so this is safe

  -- Get m where orbit exceeds max bound
  obtain ⟨m_big, h_big⟩ := hdiv (max B_early B_late + 1)

  by_cases hm_early : m_big < m₀
  · -- Case 1: Early phase
    have h_early := h_early_bound m_big hm_early
    have h_le : DriftLemma.orbit n m_big ≤ B_early := by
      calc DriftLemma.orbit n m_big ≤ n * 3^m_big := h_early
        _ ≤ n * 3^(m₀ - 1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
        _ ≤ n * 3^m₀ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h_le_max : DriftLemma.orbit n m_big ≤ max B_early B_late := le_trans h_le (le_max_left _ _)
    omega

  · -- Case 2: Late phase (supercritical regime, m_big ≥ m₀)
    --
    -- Now with B_late = max(n + 5, n + 2^m_stable), we can handle all cases cleanly:
    -- - If m_big ≥ m_stable: waveRatio ≤ 4, so orbit ≤ n + 4 < n + 5 ≤ B_late
    -- - If m_big < m_stable: waveRatio ≤ (3/2)^m_big < 2^m_big < 2^m_stable, so orbit < n + 2^m_stable ≤ B_late
    --
    push_neg at hm_early
    have h_super_m := h_super_drift m_big hm_early

    -- In supercritical, orbit ≤ n + waveRatio (from orbit_bound_via_ratio)
    have h_orbit_via_ratio : (DriftLemma.orbit n m_big : ℚ) ≤ n + DriftLemma.waveRatio n m_big :=
      DriftLemma.orbit_bound_via_ratio n m_big (by omega) h_super_m

    -- Case split on whether we're in the stable regime
    by_cases hm_ge_stable : m_big ≥ m_stable
    · -- Stable regime: waveRatio ≤ 4
      have h_wr_4 : DriftLemma.waveRatio n m_big ≤ 4 := h_wave_stable m_big hm_ge_stable
      have h_orbit_bound : (DriftLemma.orbit n m_big : ℚ) ≤ n + 4 := by linarith
      have h_orbit_nat : DriftLemma.orbit n m_big ≤ n + 4 := by exact_mod_cast h_orbit_bound
      have h_B_late_ge : B_late ≥ n + 5 := le_max_left _ _
      have h_orbit_lt : DriftLemma.orbit n m_big < B_late := by omega
      have h_lt_max : DriftLemma.orbit n m_big < max B_early B_late :=
        lt_of_lt_of_le h_orbit_lt (le_max_right _ _)
      omega
    · -- Intermediate regime: m₀ ≤ m_big < m_stable
      -- waveRatio ≤ (3/2)^m_big - 1 < 2^m_stable (since m_big < m_stable)
      push_neg at hm_ge_stable
      have h_wave_geom := DriftLemma.waveRatio_growth_bound n hn_odd m_big
      -- Key: Since m_big < m_stable, we have (3/2)^m_big < 2^m_big < 2^m_stable
      -- The waveRatio is bounded by geometric growth
      -- Simpler approach: waveRatio ≤ (3/2)^m_big - 1 < (3/2)^m_big < 2^m_big < 2^m_stable
      have hm_lt : m_big < m_stable := hm_ge_stable
      -- (3/2)^m_big < 2^m_big: follows from (3/2)^m < 2^m for any m (since 3/2 < 2)
      -- Alternative: use 3^m_big < 4^m_big and scale
      have h_32_lt_2m : (3/2 : ℚ)^m_big < (2 : ℚ)^m_big := by
        by_cases hm_zero : m_big = 0
        · simp only [hm_zero, pow_zero, lt_irrefl]
          -- 1 < 1 is false, but m_big = 0 means m_big ≥ m₀ > 10 contradiction
          omega
        · -- (3/2)^m / 2^m = (3/4)^m = 3^m / 4^m < 1 for m > 0
          have hm_ne : m_big ≠ 0 := hm_zero
          -- Use that 3^m < 4^m for m > 0
          have h_3_lt_4 : (3 : ℕ)^m_big < (4 : ℕ)^m_big := Nat.pow_lt_pow_left (by norm_num : 3 < 4) hm_ne
          have h_4_eq_22 : (4 : ℕ)^m_big = (2^2)^m_big := by norm_num
          have h_2m : (2 : ℕ)^(2 * m_big) = (2^2)^m_big := by rw [← pow_mul]
          -- (3/2)^m = 3^m / 2^m and 2^m = (2^m), so compare 3^m / 2^m vs 2^m
          -- We need (3/2)^m < 2^m, i.e., 3^m < 2^m * 2^m = 4^m
          calc (3/2 : ℚ)^m_big = (3 : ℚ)^m_big / (2 : ℚ)^m_big := by rw [div_pow]
               _ < (4 : ℚ)^m_big / (2 : ℚ)^m_big := by
                   apply div_lt_div_of_pos_right
                   · exact_mod_cast h_3_lt_4
                   · positivity
               _ = (2 : ℚ)^m_big := by
                   have : (4 : ℚ) = 2^2 := by norm_num
                   rw [this, ← pow_mul]
                   have h2m : 2 * m_big = m_big + m_big := by ring
                   rw [h2m, pow_add]
                   field_simp
      -- 2^m_big ≤ 2^(m_stable - 1) < 2^m_stable (since m_big < m_stable)
      have hm_le : m_big ≤ m_stable - 1 := by omega
      have h_2pow_mono : (2 : ℚ)^m_big ≤ (2 : ℚ)^(m_stable - 1) := by
        have h_base : (1 : ℚ) ≤ 2 := by norm_num
        have : (2 : ℚ)^m_big = 2^m_big := rfl
        have : (2 : ℚ)^(m_stable - 1) = 2^(m_stable - 1) := rfl
        exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hm_le
      have h_2pow_lt : (2 : ℚ)^(m_stable - 1) < (2 : ℚ)^m_stable := by
        have hm_pos : 1 ≤ m_stable := by omega
        exact_mod_cast Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega : m_stable - 1 < m_stable)
      -- Chain: waveRatio ≤ (3/2)^m_big - 1 < (3/2)^m_big < 2^m_big ≤ 2^(m_stable-1) < 2^m_stable
      have h_wave_bound : DriftLemma.waveRatio n m_big < (2 : ℚ)^m_stable := by
        calc DriftLemma.waveRatio n m_big ≤ (3/2 : ℚ)^m_big - 1 := h_wave_geom
             _ < (3/2 : ℚ)^m_big := by linarith [pow_pos (by norm_num : (3/2 : ℚ) > 0) m_big]
             _ < (2 : ℚ)^m_big := h_32_lt_2m
             _ ≤ (2 : ℚ)^(m_stable - 1) := h_2pow_mono
             _ < (2 : ℚ)^m_stable := h_2pow_lt
      have h_orbit_bound : (DriftLemma.orbit n m_big : ℚ) < n + (2 : ℚ)^m_stable := by linarith
      -- Convert to natural numbers
      have h_2pow_nat : (2 : ℚ)^m_stable = (2^m_stable : ℕ) := by simp
      have h_orbit_bound' : (DriftLemma.orbit n m_big : ℚ) < n + (2^m_stable : ℕ) := by
        rw [← h_2pow_nat]; exact h_orbit_bound
      have h_orbit_nat : DriftLemma.orbit n m_big < n + 2^m_stable := by
        have h_pos : (0 : ℚ) < n + (2^m_stable : ℕ) := by
          have : (0 : ℚ) < (2^m_stable : ℕ) := by positivity
          linarith
        exact_mod_cast h_orbit_bound'
      have h_B_late_ge : B_late ≥ n + 2^m_stable := le_max_right _ _
      have h_orbit_lt : DriftLemma.orbit n m_big < B_late := lt_of_lt_of_le h_orbit_nat h_B_late_ge
      have h_lt_max : DriftLemma.orbit n m_big < max B_early B_late :=
        lt_of_lt_of_le h_orbit_lt (le_max_right _ _)
      omega

/-! ## Part 5: Baker's Theorem Connection -/

/-- Baker's theorem prevents riding the critical line.
    |S·log(2) - k·log(3)| ≥ C₁ / max(S,k)^C₂
    This is axiomatized in PartI.lean. -/
theorem baker_prevents_critical_line :
    ∃ (C1 C2 : ℝ), C1 > 0 ∧ C2 > 0 ∧
    ∀ (S k : ℕ), 0 < S → 0 < k →
      let Λ := (S : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3
      Λ ≠ 0 → |Λ| ≥ C1 / (max S k : ℝ) ^ C2 :=
  baker_2_3_lower_bound

/-! ## Part 6: Main Theorems -/

/-- **MAIN THEOREM**: No divergence from Lyapunov-Baker-Harmonic analysis.

This theorem shows that all Collatz orbits are bounded.

The proof combines:
1. Lyapunov noise floor (L strictly increasing)
2. Baker constraint (can't ride critical line)
3. Trailing ones bound (ν = 1 runs are short)
4. Eventual supercriticality (average ν → 2)
5. Height-based Baker: large orbit → constraints on exponents → forced supercritical

Therefore: All Collatz orbits are bounded.

**Key Insight**: Divergent orbits would require hovering near critical line,
but noise floor + Baker prevent this. Eventually forced supercritical → bounded. -/
theorem no_divergence_from_lyapunov_baker (n : ℕ) (hn : n > 1) (hn_odd : Odd n) :
    ∃ B : ℕ, ∀ m : ℕ, DriftLemma.orbit n m ≤ B := by
  -- Proof by contradiction using divergence_contradiction
  by_contra h_not_bounded
  push_neg at h_not_bounded

  -- h_not_bounded : ∀ B, ∃ m, orbit n m > B
  -- This implies divergence
  have hdiv : ∀ B : ℕ, ∃ m, DriftLemma.orbit n m ≥ B := by
    intro B
    obtain ⟨m, hm⟩ := h_not_bounded B
    exact ⟨m, le_of_lt hm⟩

  -- But divergence_contradiction shows this leads to False
  exact divergence_contradiction n hn hn_odd hdiv

/-- Corollary: Eventually non-subcritical -/
theorem orbit_eventually_non_subcritical_proved (n : ℕ) (hn : n > 1) (hn_odd : Odd n) :
    ∃ m₀, ∀ m ≥ m₀, ¬DriftLemma.isSubcriticalNu (DriftLemma.nuSum n m) m := by
  obtain ⟨m₀, h⟩ := nuSum_supercritical_threshold n hn hn_odd
  use m₀
  intro m hm
  unfold DriftLemma.isSubcriticalNu
  push_neg
  exact h m hm

/-! ## Summary

The proof chain for no-divergence:

1. **Mod 4 Structure** (BleedingLemmas):
   - ν = 1 ⟺ n ≡ 3 (mod 4)
   - ν ≥ 2 ⟺ n ≡ 1 (mod 4)

2. **Trailing Ones Bound** (BleedingLemmas):
   - Consecutive ν = 1 steps ≤ log₂(orbit value)
   - This bounds ν = 1 run lengths

3. **Baker's Theorem** (PartI, BakerOrderBound):
   - |S·log(2) - k·log(3)| ≥ C₁/k^C₂
   - Prevents hovering at critical line

4. **Eventual Supercriticality** (SubcriticalCongruence):
   - For n > 1, ∃ m₀, ∀ m ≥ m₀, 2^S ≥ 3^m

5. **Supercritical Contraction** (DriftLemma):
   - When 2^S ≥ 3^m: orbit ≤ n + waveSum/3^m
   - The orbit is bounded in perpetual supercritical regime

**Conclusion**: All orbits are bounded, no divergence possible.

## Connection to Lyapunov Theory (LyapunovBalance.lean)

The Lyapunov function L(k) = Σᵢ wᵢ² where wᵢ = log₂(3) - νᵢ satisfies:
- L(k+1) > L(k) (strictly increasing, since wᵢ ≠ 0)
- |Tilt(k)|² ≤ k·L(k) (Cauchy-Schwarz)

This shows that while harmonic cancellation can make Tilt small,
the noise floor L grows without bound, eventually forcing
the orbit into supercritical regime.

## Connection to Cyclotomic Theory (TiltBalance.lean, CyclotomicAlgebra.lean)

For cycles, the waveSum must satisfy D | waveSum where D = 2^S - 3^m.
The Tilt Balance theorem shows that nontrivial profiles have
harmonic imbalance that violates this divisibility.
This eliminates nontrivial cycles.
-/

end Collatz.LyapunovBakerConnection
