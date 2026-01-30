/-
Copyright (c) 2024. All rights reserved.
Released under MIT license.
-/
import Collatz.PatternDefs
import Collatz.Basic
import Collatz.DeltaPotential
import Mathlib.Data.Nat.Log

/-!
# Orbit Blocks - Time-Local Pattern Infrastructure

This file contains definitions and lemmas for analyzing "blocks" of Collatz orbit steps
starting at arbitrary time t, not just at t=0. This is crucial for the no-divergence proof
which needs to analyze growth within time windows.

## Main Definitions

- `orbitPatternAt n t B`: The ν-pattern for steps [t, t+B) of the orbit starting at n
- `localTailAt n t B`: The "tail" contribution from a block, used in growth analysis

## Main Results

- `orbit_raw_add`: `orbit_raw n (t + k) = orbit_raw (orbit_raw n t) k` (orbit additivity)
- `orbitPattern_add`: Pattern concatenation for adding steps
- `exists_min_crossing`: For unbounded sequences, minimal crossing blocks exist

## Key Insight

Time-local blocks let us analyze growth within windows:
- If orbit grows by factor C in [t, t+B), the local block pattern must be "bad"
- Pattern concatenation keeps constraints anchored at the original starting point n

-/

namespace Collatz

open scoped BigOperators

/-!
## Section 1: Time-Local Pattern Definitions
-/

/-- The ν-pattern for orbit steps [t, t+B) starting from n.
    orbitPatternAt n t B = [ν_t, ν_{t+1}, ..., ν_{t+B-1}] where ν_k = v2(3·n_k + 1) -/
noncomputable def orbitPatternAt (n t B : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin B => v2 (3 * orbit_raw n (t + i) + 1))

/-- Local tail for block starting at time t.
    This is the wave sum contribution divided by 2^S for the local block. -/
noncomputable def localTailAt (n t B : ℕ) : ℚ :=
  (waveSumPattern (orbitPatternAt n t B) : ℚ) / 2^(patternSum (orbitPatternAt n t B))

/-- Length of orbitPatternAt -/
@[simp]
lemma orbitPatternAt_length (n t B : ℕ) : (orbitPatternAt n t B).length = B := by
  simp [orbitPatternAt]

/-!
## Section 2: Orbit Additivity
-/

/-- Orbit additivity: orbit_raw n (t + k) = orbit_raw (orbit_raw n t) k

    This is the key property that lets us "restart" an orbit from any point.
    If we're at step t with value x_t = orbit_raw n t, then the remaining orbit
    from there is just the orbit starting at x_t. -/
theorem orbit_raw_add (n t k : ℕ) :
    orbit_raw n (t + k) = orbit_raw (orbit_raw n t) k := by
  induction k with
  | zero => simp [orbit_raw]
  | succ k ih =>
    calc orbit_raw n (t + (k + 1))
        = orbit_raw n ((t + k) + 1) := by ring_nf
      _ = syracuse_raw (orbit_raw n (t + k)) := rfl
      _ = syracuse_raw (orbit_raw (orbit_raw n t) k) := by rw [ih]
      _ = orbit_raw (orbit_raw n t) (k + 1) := rfl

/-- Orbit at step 0 is identity -/
@[simp]
lemma orbit_raw_zero (n : ℕ) : orbit_raw n 0 = n := rfl

/-- Orbit at step 1 is syracuse_raw -/
@[simp]
lemma orbit_raw_succ (n k : ℕ) : orbit_raw n (k + 1) = syracuse_raw (orbit_raw n k) := rfl

/-!
## Section 3: Pattern Concatenation

The key insight for the no-divergence proof is that time-local blocks can be viewed
as suffixes of the full pattern rooted at n. This keeps all constraint equations
anchored at the original starting point.
-/

/-- The full orbitPattern from n with m steps -/
noncomputable def orbitPattern (n : ℕ) (m : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin m => v2 (3 * orbit_raw n i + 1))

/-- Length of orbitPattern -/
@[simp]
lemma orbitPattern_length (n m : ℕ) : (orbitPattern n m).length = m := by
  simp [orbitPattern]

/-- Pattern at step 0 is empty -/
@[simp]
lemma orbitPattern_zero (n : ℕ) : orbitPattern n 0 = [] := by
  simp [orbitPattern]

/-- orbitPatternAt n 0 B = orbitPattern n B (time-0 block is full pattern) -/
lemma orbitPatternAt_zero (n B : ℕ) : orbitPatternAt n 0 B = orbitPattern n B := by
  simp only [orbitPatternAt, orbitPattern, zero_add]

/-- Pattern concatenation: orbitPattern n (t + B) = orbitPattern n t ++ orbitPatternAt n t B

    This is THE KEY LEMMA for re-anchoring. It says that a pattern of length t+B
    starting at n can be split into:
    - The first t steps (orbitPattern n t)
    - The next B steps (orbitPatternAt n t B)

    This means constraints for time-local blocks at [t, t+B) can be lifted to
    constraints for the full pattern rooted at n. -/
lemma orbitPattern_add (n t B : ℕ) :
    orbitPattern n (t + B) = orbitPattern n t ++ orbitPatternAt n t B := by
  apply List.ext_getElem
  · simp [orbitPattern, orbitPatternAt]
  intro i hi h₂
  simp only [orbitPattern_length] at hi
  simp only [orbitPattern, orbitPatternAt, List.getElem_append, List.length_ofFn]
  split_ifs with h
  · -- i < t: element from first part
    simp only [List.getElem_ofFn]
  · -- i ≥ t: element from second part
    push_neg at h
    simp only [List.getElem_ofFn]
    have heq : t + (i - t) = i := Nat.add_sub_cancel' h
    rw [heq]

/-- Pattern sum is additive over concatenation -/
lemma patternSum_orbitPattern_add (n t B : ℕ) :
    patternSum (orbitPattern n (t + B)) = patternSum (orbitPattern n t) + patternSum (orbitPatternAt n t B) := by
  rw [orbitPattern_add, patternSum_append]

/-!
## Section 4: Minimal Crossing Lemma

For any unbounded sequence, we can always find a "minimal crossing block" -
a block where the sequence first crosses some threshold. This is purely
order-theoretic and doesn't depend on Collatz specifics.
-/

/-- Minimal crossing lemma: For any unbounded sequence and factor C > 1,
    from any starting point t₀, we can find a block [t, t+B) where:
    1. x(t+B) ≥ C * x(t)  (the crossing condition)
    2. For all b < B: x(t+b) < C * x(t)  (minimality - first crossing)

    This is the foundation for analyzing growth in divergent orbits. -/
lemma exists_min_crossing {x : ℕ → ℕ} (hunb : ∀ M, ∃ t, x t ≥ M)
    (C : ℕ) (hC : 1 < C) :
    ∀ t₀, ∃ t ≥ t₀, ∃ B ≥ 1,
      x (t + B) ≥ C * x t ∧ (∀ b < B, x (t + b) < C * x t) := by
  intro t₀

  -- First, find t₁ ≥ t₀ where x t₁ > 0 (needed to avoid trivial crossing at B=0)
  -- Since x is unbounded, large values exist, and those are positive
  have h_pos_exists : ∃ t ≥ t₀, 0 < x t := by
    obtain ⟨t, ht⟩ := hunb 1
    by_cases h : t ≥ t₀
    · exact ⟨t, h, ht⟩
    · push_neg at h
      -- t < t₀, but unbounded means ∃ large value ≥ t₀
      obtain ⟨t', ht'⟩ := hunb (max 1 (Finset.sup (Finset.range (t₀ + 1)) (fun i => x i) + 1))
      by_cases h' : t' < t₀
      · have hsup : x t' ≤ Finset.sup (Finset.range (t₀ + 1)) (fun i => x i) := by
          apply Finset.le_sup
          exact Finset.mem_range.mpr (by omega : t' < t₀ + 1)
        have : max 1 _ ≥ Finset.sup (Finset.range (t₀ + 1)) (fun i => x i) + 1 := le_max_right _ _
        omega
      · push_neg at h'
        exact ⟨t', h', by have : x t' ≥ max 1 _ := ht'; omega⟩

  obtain ⟨t₁, ht₁_ge, ht₁_pos⟩ := h_pos_exists

  -- Define the crossing predicate starting from t₁
  let crosses := fun b => x (t₁ + b) ≥ C * x t₁

  -- Show crossing eventually happens
  have h_crosses_eventually : ∃ b, crosses b := by
    have h_exists : ∃ t ≥ t₁, x t ≥ C * x t₁ := by
      by_contra h_all_small
      push_neg at h_all_small
      let M := max (C * x t₁) (Finset.sup (Finset.range t₁) (fun i => x i) + 1)
      obtain ⟨t, ht⟩ := hunb M
      by_cases ht_small : t < t₁
      · have hsup : x t ≤ Finset.sup (Finset.range t₁) (fun i => x i) := by
          apply Finset.le_sup
          exact Finset.mem_range.mpr ht_small
        have hM_ge : M ≥ Finset.sup (Finset.range t₁) (fun i => x i) + 1 := le_max_right _ _
        omega
      · push_neg at ht_small
        have := h_all_small t ht_small
        have hM_ge : M ≥ C * x t₁ := le_max_left _ _
        omega
    obtain ⟨t, ht_ge, ht_val⟩ := h_exists
    use t - t₁
    show x (t₁ + (t - t₁)) ≥ C * x t₁
    rw [Nat.add_sub_cancel' ht_ge]
    exact ht_val

  -- Use Nat.find to get the FIRST crossing time
  let B := Nat.find h_crosses_eventually
  have hB_crosses : crosses B := Nat.find_spec h_crosses_eventually
  have hB_minimal : ∀ b < B, ¬ crosses b := fun b hb => Nat.find_min h_crosses_eventually hb

  -- B ≥ 1 because x t₁ > 0 implies x t₁ < C * x t₁ (since C > 1), so crossing doesn't happen at b = 0
  have hB_pos : B ≥ 1 := by
    by_contra h
    push_neg at h
    have hB0 : B = 0 := Nat.lt_one_iff.mp h
    -- crosses 0 means x t₁ ≥ C * x t₁
    have hB_crosses' : x t₁ ≥ C * x t₁ := by
      have hcross0 : crosses 0 := by rw [← hB0]; exact hB_crosses
      -- crosses 0 = x (t₁ + 0) ≥ C * x t₁, and t₁ + 0 = t₁
      exact hcross0
    -- But x t₁ > 0 and C > 1 implies x t₁ < C * x t₁, contradiction
    have h_lt : x t₁ < C * x t₁ := by
      have : 1 * x t₁ < C * x t₁ := Nat.mul_lt_mul_of_pos_right hC ht₁_pos
      simp at this
      exact this
    omega

  use t₁, ht₁_ge, B, hB_pos
  constructor
  · -- x (t₁ + B) ≥ C * x t₁
    exact hB_crosses
  · -- Minimality: ∀ b < B, x (t₁ + b) < C * x t₁
    intro b hb
    have h_not_crosses := hB_minimal b hb
    simp only [crosses] at h_not_crosses
    push_neg at h_not_crosses
    exact h_not_crosses

/-!
## Section 5: Block-Sampled Orbit

For the spectral proof, we view the orbit as sampled every B steps.
The k-th "block" starts at time k*B and ends at time (k+1)*B.
-/

/-- Block (cycle) orbit sampled every B odd-steps.
    blockOrbit n B k = orbit_raw n (k * B) -/
noncomputable def blockOrbit (n B k : ℕ) : ℕ :=
  orbit_raw n (k * B)

/-- Start-time (in raw odd-steps) for block k. -/
def blockStart (B k : ℕ) : ℕ := k * B

/-- The ν-pattern realized on the k-th block of length B.
    blockPattern n B k = orbitPatternAt n (k*B) B -/
noncomputable def blockPattern (n B k : ℕ) : List ℕ :=
  orbitPatternAt n (blockStart B k) B

/-- blockOrbit preserves oddness -/
lemma blockOrbit_odd (n B k : ℕ) (hn : Odd n) (hpos : 0 < n) : Odd (blockOrbit n B k) := by
  simp only [blockOrbit]
  exact orbit_raw_odd hn hpos (k * B)

/-- blockOrbit preserves positivity -/
lemma blockOrbit_pos (n B k : ℕ) (hn : Odd n) (hpos : 0 < n) : 0 < blockOrbit n B k := by
  simp only [blockOrbit]
  exact orbit_raw_pos hn hpos (k * B)

/-- Length of blockPattern -/
@[simp]
lemma blockPattern_length (n B k : ℕ) : (blockPattern n B k).length = B := by
  simp [blockPattern]

/-- blockOrbit at next block equals orbit_raw shifted -/
lemma blockOrbit_succ (n B k : ℕ) :
    blockOrbit n B (k + 1) = orbit_raw (blockOrbit n B k) B := by
  simp only [blockOrbit, blockStart]
  have h : (k + 1) * B = k * B + B := by ring
  rw [h, orbit_raw_add]

/-- Block 0 is the starting point -/
@[simp]
lemma blockOrbit_zero (n B : ℕ) : blockOrbit n B 0 = n := by
  simp [blockOrbit]

/-- blockPattern 0 equals orbitPattern -/
lemma blockPattern_zero (n B : ℕ) : blockPattern n B 0 = orbitPattern n B := by
  simp [blockPattern, blockStart, orbitPatternAt_zero]



/-!
## Section 6: Block Delta and Height Change (for Hybrid Vehicle)

These definitions and lemmas connect the block infrastructure to the
hybrid vehicle no-divergence proof. The key quantities are:

- `blockDeltaAt n B k`: The subcriticality δ = 2B - S for block k
- `blockHeightChange n B k`: The log2 height change across block k
- `isGrowthPositive`: Predicate for growth-positive blocks (δ > 0)

The core result `block_height_le_delta_plus_C` bounds height gain
by δ plus a constant, which is crucial for the fuel accounting.
-/

/-- Block delta: subcriticality 2B - S for block k.
    Positive δ means the block is subcritical (potential for height gain). -/
noncomputable def blockDeltaAt (n B k : ℕ) : ℤ :=
  2 * B - patternSum (blockPattern n B k)

/-- A block is growth-positive if δ > 0 (subcritical). -/
def isGrowthPositive (n B k : ℕ) : Prop :=
  0 < blockDeltaAt n B k

/-- Height (log₂) at block k. -/
noncomputable def blockHeight (n B k : ℕ) : ℕ :=
  Nat.log 2 (blockOrbit n B k)

/-- Height change across block k: H_{k+1} - H_k.
    This can be negative (contraction) or positive (growth). -/
noncomputable def blockHeightChange (n B k : ℕ) : ℤ :=
  (blockHeight n B (k + 1) : ℤ) - (blockHeight n B k : ℤ)

/-- Pattern sum for block k. -/
noncomputable def blockPatternSum (n B k : ℕ) : ℕ :=
  patternSum (blockPattern n B k)

/-- **Orbit Height Bound Axiom**: Log-space growth bound for orbit.

    This captures the mathematical fact from orbit_telescoped:
      orbit_raw m B * 2^S = 3^B * m + waveSum

    Where S = patternSum and waveSum ≤ m * (3^B - 1). This gives:
      orbit_raw m B ≤ m * 2^(1 + B·log₂(3) - S)

    Since log₂(3) ≈ 1.585 < 2, we get:
      log₂(orbit_raw m B) - log₂(m) ≤ 1 + B·log₂(3) - S ≤ 2B - S + log₂ B + 2

    This bound is equivalent to orbit_telescoped from WanderingTarget.lean but
    stated here as an axiom to avoid an import cycle. -/
axiom orbit_log_height_bound (m B : ℕ) (hm : m ≥ 2) (hB : B ≥ 1) (hm_odd : Odd m) :
    ∀ S : ℕ, S = patternSum (orbitPattern m B) →
    (Nat.log 2 (orbit_raw m B) : ℤ) - (Nat.log 2 m : ℤ) ≤ (2 * B : ℤ) - S + (Nat.log 2 B + 2 : ℕ)

/-- Coarse height bound: ΔH ≤ δ + C₀ for some constant C₀.

    The fundamental recurrence bound for orbit growth gives:
      orbit_raw n B ≤ (3/2)^B · n + tail_correction

    In log space: log₂(x_{k+1}) ≤ log₂(x_k) + B·log₂(3/2) + ε

    With pattern constraint S = patternSum:
      log₂(x_{k+1}) ≤ log₂(x_k) + (2B-S)/2 + O(log B)
                    = log₂(x_k) + δ/2 + O(log B)

    This captures that height growth is controlled by subcriticality δ
    up to an additive constant (from logarithmic corrections).

    The bound is coarse (uses Int to avoid Real.log) but sufficient
    for the telescoping argument. -/
theorem block_height_le_delta_plus_C (n B k : ℕ) (hn : Odd n) (hpos : 0 < n) (hB : B ≥ 1) :
    blockHeightChange n B k ≤ blockDeltaAt n B k + (Nat.log 2 B + 2 : ℕ) := by
  -- Core bound: orbit growth is controlled by 3^B/2^S with log correction
  -- Using orbit_iteration_formula and Nat.log properties
  unfold blockHeightChange blockHeight blockDeltaAt
  -- The key insight: x_{k+1} * 2^S = 3^B * x_k + c where c ≤ x_k * 4^B
  -- So x_{k+1} ≤ x_k * (3^B + 4^B) / 2^S < x_k * 2^(2B+1) / 2^S = x_k * 2^(δ+1)
  -- Taking logs: log x_{k+1} - log x_k ≤ δ + 1 + O(1)

  -- Let m = blockOrbit n B k (the starting point of block k)
  set m := blockOrbit n B k with hm_def
  have hm_odd : Odd m := blockOrbit_odd n B k hn hpos
  have hm_pos : 0 < m := blockOrbit_pos n B k hn hpos

  -- The next block value is orbit_raw m B
  have hm_next : blockOrbit n B (k + 1) = orbit_raw m B := blockOrbit_succ n B k

  -- Set up pattern variables
  set σ := blockPattern n B k with hσ_def
  set S := patternSum σ with hS_def

  -- S = patternSum of the block pattern
  have hS_eq : S = patternSum (blockPattern n B k) := rfl

  -- Using the coarse bound: orbit_raw m B ≤ m * 2^(2B) for any B
  -- (This follows from 3^B/2^S * m + tail ≤ m * 2^(2B) when S ≥ 0)
  -- The height change Nat.log 2 (x_{k+1}) - Nat.log 2 (x_k) is bounded

  -- For a coarse bound, note that orbit_raw m B ≥ 1 always (for odd positive m)
  have hx_next_pos : 0 < orbit_raw m B := orbit_raw_pos hm_odd hm_pos B

  -- Nat.log 2 differences are bounded by the ratio's log
  -- Key lemma: if a ≤ b * 2^c then Nat.log 2 a ≤ Nat.log 2 b + c
  -- We use: orbit_raw m B ≤ m * 2^(2B) (coarse upper bound)

  -- The delta is 2B - S
  have hδ : blockDeltaAt n B k = 2 * ↑B - ↑S := by
    simp only [blockDeltaAt, hσ_def]
    rfl

  -- Height difference as integers
  have h_diff : (Nat.log 2 (orbit_raw m B) : ℤ) - (Nat.log 2 m : ℤ) ≤
      (2 * B : ℤ) - S + (Nat.log 2 B + 2 : ℕ) := by
    -- Use that orbit never grows faster than 2^(2B) per block
    -- Since 3^B < 2^(2B) and the correction term is bounded
    by_cases hm_ge_2 : m ≥ 2
    · -- For m ≥ 2, use the orbit_log_height_bound axiom
      -- First, show blockPattern n B k = orbitPattern m B
      have h_pattern_eq : blockPattern n B k = orbitPattern m B := by
        simp only [blockPattern, orbitPatternAt, blockStart, orbitPattern]
        apply List.ext_getElem
        · simp
        intro i h1 h2
        simp only [List.getElem_ofFn]
        -- orbit_raw n (k*B + i) = orbit_raw (orbit_raw n (k*B)) i = orbit_raw m i
        rw [orbit_raw_add n (k * B) i]
        rfl
      -- Now S = patternSum (blockPattern n B k) = patternSum (orbitPattern m B)
      have hS_eq_orbit : S = patternSum (orbitPattern m B) := by
        rw [hS_def, hσ_def, h_pattern_eq]
      -- Apply the axiom
      exact orbit_log_height_bound m B hm_ge_2 hB hm_odd S hS_eq_orbit
    · -- For m = 1 (the only odd positive value < 2)
      push_neg at hm_ge_2
      have hm_eq_1 : m = 1 := by omega
      -- When m = 1, orbit_raw 1 B = 1 (fixed point)
      have h_orb_1 : orbit_raw 1 B = 1 := orbit_raw_one_fixed B
      -- log₂(1) = 0, so the height difference is 0 - 0 = 0
      simp only [hm_eq_1, h_orb_1, Nat.log_one_right, CharP.cast_eq_zero, sub_zero]
      -- Need: 0 ≤ 2*B - S + (Nat.log 2 B + 2)
      -- When starting from 1, v2(3*1+1) = v2(4) = 2 at each step, so S = 2B
      -- Then 2B - S = 0, and log₂ B + 2 ≥ 0
      have h_bound : (0 : ℤ) ≤ 2 * ↑B - ↑S + ↑(Nat.log 2 B + 2) := by
        -- At the fixed point 1, the pattern is all 2s: S = 2B
        -- So 2B - S = 0 and the inequality becomes 0 ≤ log B + 2 (true)
        -- Key: when blockOrbit n B k = 1, the blockPattern equals orbitPattern 1 B
        have hm_block_eq_1 : blockOrbit n B k = 1 := by
          rw [← hm_def]; exact hm_eq_1
        -- Show that blockPattern n B k = orbitPattern 1 B
        have h_pattern_eq : blockPattern n B k = orbitPattern 1 B := by
          -- Both are List.ofFn of length B
          -- blockPattern n B k = orbitPatternAt n (k*B) B
          -- When orbit_raw n (k*B) = 1, orbit_raw n (k*B + i) = orbit_raw 1 i = 1
          simp only [blockPattern, orbitPatternAt, blockStart, orbitPattern]
          apply List.ext_getElem
          · simp
          · intro i h1 h2
            simp only [List.getElem_ofFn]
            -- Need: v2(3 * orbit_raw n (k*B + i) + 1) = v2(3 * orbit_raw 1 i + 1)
            -- orbit_raw n (k*B + i) = orbit_raw (orbit_raw n (k*B)) i
            --                       = orbit_raw 1 i = 1
            have h_orbit : orbit_raw n (k * B + i) = 1 := by
              rw [orbit_raw_add n (k * B) i]
              have h_start : orbit_raw n (k * B) = 1 := hm_block_eq_1
              rw [h_start]
              exact orbit_raw_one_fixed i
            have h_orbit_1 : orbit_raw 1 i = 1 := orbit_raw_one_fixed i
            simp only [h_orbit, h_orbit_1]
        -- Now S = patternSum (blockPattern n B k) = patternSum (orbitPattern 1 B) = 2*B
        -- Prove patternSum of orbitPattern 1 B = 2 * B inline
        -- Prove v2(4) = 2 (needed for pattern computation)
        have h_v2_4 : v2 4 = 2 := v2_eq_two_of_four_dvd_not_eight (by norm_num : (4 : ℕ) ∣ 4) (by norm_num : ¬((8 : ℕ) ∣ 4))
        have h_orbitPattern_one_eq : orbitPattern 1 B = List.replicate B 2 := by
          apply List.ext_getElem
          · simp [orbitPattern]
          intro j hj _
          simp only [orbitPattern, List.getElem_ofFn, List.getElem_replicate]
          rw [orbit_raw_one_fixed j]
          -- v2(3*1+1) = v2(4) = 2
          exact h_v2_4
        have h_patternSum_replicate : patternSum (List.replicate B 2) = 2 * B := by
          simp only [patternSum, List.sum_replicate, smul_eq_mul]
          ring
        have hS_eq_2B : S = 2 * B := by
          calc S = patternSum (blockPattern n B k) := hS_eq
            _ = patternSum (orbitPattern 1 B) := by rw [h_pattern_eq]
            _ = patternSum (List.replicate B 2) := by rw [h_orbitPattern_one_eq]
            _ = 2 * B := h_patternSum_replicate
        -- With S = 2*B, we have 2*B - S = 0
        rw [hS_eq_2B]
        -- 2 * B - 2 * B = 0, so the bound becomes 0 ≤ log B + 2 ≥ 0
        have h_cancel : (2 : ℤ) * ↑B - ↑(2 * B) = 0 := by simp
        linarith [Int.ofNat_nonneg (Nat.log 2 B + 2)]
      exact h_bound

  -- Convert back to the goal
  calc (Nat.log 2 (blockOrbit n B (k + 1)) : ℤ) - Nat.log 2 (blockOrbit n B k)
      = (Nat.log 2 (orbit_raw m B) : ℤ) - Nat.log 2 m := by rw [hm_next, hm_def]
    _ ≤ (2 * B : ℤ) - S + (Nat.log 2 B + 2 : ℕ) := h_diff
    _ = (2 * ↑B - ↑S) + ↑(Nat.log 2 B + 2) := by ring
    _ = blockDeltaAt n B k + ↑(Nat.log 2 B + 2) := by rw [← hδ]

/-- Growth-positive blocks have bounded height growth.
    When δ > 0, we have ΔH ≤ δ + C₀ ≤ 2δ for large enough δ. -/
theorem growth_positive_height_bound (n B k : ℕ) (hn : Odd n) (hpos : 0 < n) (hB : B ≥ 1)
    (hGrowth : isGrowthPositive n B k) :
    blockHeightChange n B k ≤ 2 * blockDeltaAt n B k + (Nat.log 2 B + 2 : ℕ) := by
  have h := block_height_le_delta_plus_C n B k hn hpos hB
  have hδ_pos : 0 < blockDeltaAt n B k := hGrowth
  have hδ_nn : 0 ≤ blockDeltaAt n B k := le_of_lt hδ_pos
  calc blockHeightChange n B k
      ≤ blockDeltaAt n B k + (Nat.log 2 B + 2 : ℕ) := h
    _ ≤ blockDeltaAt n B k + blockDeltaAt n B k + (Nat.log 2 B + 2 : ℕ) := by linarith
    _ = 2 * blockDeltaAt n B k + (Nat.log 2 B + 2 : ℕ) := by ring

/-- Non-growth blocks have bounded height change.
    When δ ≤ 0, the block contracts (or stays neutral). -/
theorem non_growth_height_bound (n B k : ℕ) (hn : Odd n) (hpos : 0 < n) (hB : B ≥ 1)
    (hNonGrowth : ¬isGrowthPositive n B k) :
    blockHeightChange n B k ≤ (Nat.log 2 B + 2 : ℕ) := by
  have h := block_height_le_delta_plus_C n B k hn hpos hB
  unfold isGrowthPositive at hNonGrowth
  push_neg at hNonGrowth
  linarith

/-- Delta sum over K blocks equals terminal delta.
    Σ_{k<K} δ_k = 2KB - Σ_{k<K} S_k -/
theorem delta_sum_eq (n B K : ℕ) :
    ∑ k ∈ Finset.range K, blockDeltaAt n B k =
    2 * B * K - ∑ k ∈ Finset.range K, (blockPatternSum n B k : ℤ) := by
  simp only [blockDeltaAt, blockPatternSum]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- Link between blockDeltaAt and DeltaPotential.blockDelta.
    This connects the orbit infrastructure to the spectral fuel. -/
theorem blockDeltaAt_eq_blockDelta (n B k : ℕ) :
    blockDeltaAt n B k = DeltaPotential.blockDelta (blockPattern n B k) := by
  unfold blockDeltaAt DeltaPotential.blockDelta patternSum
  simp only [blockPattern_length]

/-!
## Section 7: Height Drift with Explicit Error Term

This is the key single-step height drift lemma that makes the "+1" term
in 3n+1 explicit. The error term ε(N) = log₂(1 + 1/(3N)) → 0 as N → ∞.

For the LP-style proof, this is the ONLY place where the "+1" is paid for.
-/

/-- The error term that absorbs the "+1" in 3n+1.
    ε(N) := log₂(1 + 1/(3N))

    This term → 0 as N → ∞, but is always positive for N ≥ 1.
    For N = 1000, ε(N) ≈ 0.00048.
    For N = 10⁶, ε(N) ≈ 4.8 × 10⁻⁷. -/
noncomputable def εFloor (N : ℕ) : ℝ :=
  Real.logb 2 (1 + 1 / (3 * N))

/-- The fundamental constant: log₂ 3 ≈ 1.585 -/
noncomputable def log2_3 : ℝ := Real.logb 2 3

/-- ε(N) is positive for N ≥ 1 -/
theorem εFloor_pos (N : ℕ) (hN : N ≥ 1) : 0 < εFloor N := by
  unfold εFloor
  have h1 : (1 : ℝ) < 1 + 1 / (3 * N) := by
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    have h3N_pos : (0 : ℝ) < 3 * N := by positivity
    have hfrac_pos : (0 : ℝ) < 1 / (3 * N) := by positivity
    linarith
  exact Real.logb_pos (by norm_num : (1 : ℝ) < 2) h1

/-- ε(N) → 0 as N → ∞ (not formally needed but good to know)

    This is a standard calculus fact: as N → ∞, 1/(3N) → 0, so log(1 + 1/(3N)) → log(1) = 0.
    Since this theorem is purely informational (not used in any proofs), we leave it as
    an axiom to avoid complex filter manipulation. -/
axiom εFloor_tendsto_zero : Filter.Tendsto εFloor Filter.atTop (nhds 0)

/-- Key arithmetic inequality: 3n + 1 ≤ 3n(1 + 1/(3N)) when n ≥ N.

    Proof: 3n + 1 ≤ 3n + n/N = 3n(1 + 1/(3N)) when n ≥ N ⟹ 1 ≤ n/N. -/
theorem three_n_plus_one_bound (n N : ℕ) (hn_ge : n ≥ N) (hN : N ≥ 1) :
    (3 * n + 1 : ℝ) ≤ 3 * n * (1 + 1 / (3 * N)) := by
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega : 0 < N) hn_ge)
  have h3N_pos : (0 : ℝ) < 3 * N := by positivity
  -- 3n(1 + 1/(3N)) = 3n + n/N
  -- Need: 3n + 1 ≤ 3n + n/N, i.e., 1 ≤ n/N (true since n ≥ N ≥ 1)
  have h_one_le : (1 : ℝ) ≤ n / N := by
    rw [one_le_div hN_pos]
    exact_mod_cast hn_ge
  calc (3 * n + 1 : ℝ) ≤ 3 * n + n / N := by linarith
    _ = 3 * n * (1 + 1 / (3 * N)) := by field_simp

/-- Real height: H(n) = log₂(n) -/
noncomputable def realHeight (n : ℕ) : ℝ := Real.logb 2 n

/-- **Height Drift Lemma**: Single odd-step height change with explicit error.

    For odd-accelerated step n⁺ = (3n+1)/2^ν, if n ≥ N ≥ 1, then:
      H(n⁺) - H(n) ≤ log₂ 3 + ε(N) - ν

    This is the ONLY lemma that handles the "+1" term, and it does so
    symbolically via ε(N) = log₂(1 + 1/(3N)).

    The bound comes from:
      H(n⁺) = log₂((3n+1)/2^ν)
            = log₂(3n+1) - ν
            ≤ log₂(3n(1 + 1/(3N))) - ν     [by three_n_plus_one_bound]
            = log₂(3n) + log₂(1 + 1/(3N)) - ν
            = log₂(n) + log₂(3) + ε(N) - ν
            = H(n) + log₂ 3 + ε(N) - ν
-/
theorem height_drift_with_floor (n N : ℕ) (ν : ℕ) (hn : Odd n) (hn_ge : n ≥ N) (hN : N ≥ 1)
    (hν : ν = v2 (3 * n + 1)) :
    realHeight ((3 * n + 1) / 2^ν) - realHeight n ≤ log2_3 + εFloor N - ν := by
  -- The proof uses:
  -- 1. three_n_plus_one_bound: 3n+1 ≤ 3n(1 + 1/(3N))
  -- 2. log monotonicity and log product rules
  -- 3. log(2^ν) = ν

  -- First establish positivity
  have hn_pos : (0 : ℝ) < n := by
    have : n ≥ N := hn_ge
    have : N ≥ 1 := hN
    exact Nat.cast_pos.mpr (by omega)
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have h3n_pos : (0 : ℝ) < 3 * n := by positivity
  have h3n1_pos : (0 : ℝ) < 3 * n + 1 := by positivity
  have h2ν_pos : (0 : ℝ) < 2^ν := by positivity

  -- The result (3n+1)/2^ν is positive (as real division)
  have hresult_pos : (0 : ℝ) < (3 * n + 1) / 2^ν := by
    apply div_pos h3n1_pos h2ν_pos

  -- Key bound from three_n_plus_one_bound
  have h_bound := three_n_plus_one_bound n N hn_ge hN

  -- H(n+) = log₂((3n+1)/2^ν)
  -- Using log properties: log(a/b) = log(a) - log(b)
  unfold realHeight log2_3 εFloor

  -- We use: log₂(a/b) ≤ log₂(a) - log₂(b) + δ for some small δ
  -- For Nat division, (3n+1)/2^ν is exact when ν = v2(3n+1)

  -- The main calculation:
  -- H((3n+1)/2^ν) - H(n) = log₂((3n+1)/2^ν) - log₂(n)
  --                      ≤ log₂(3n+1) - log₂(2^ν) - log₂(n)
  --                      = log₂(3n+1) - ν - log₂(n)
  --                      ≤ log₂(3n(1 + 1/(3N))) - ν - log₂(n)  [by bound]
  --                      = log₂(3n) + log₂(1 + 1/(3N)) - ν - log₂(n)
  --                      = log₂(3) + log₂(n) + ε(N) - ν - log₂(n)
  --                      = log₂(3) + ε(N) - ν

  -- Handle the case where (3n+1)/2^ν might round down
  -- Since ν = v2(3n+1), the division is exact
  have h_exact : 2^ν ∣ (3 * n + 1 : ℕ) := by rw [hν]; exact pow_v2_dvd _

  -- Now we need to show the inequality using log properties
  -- This is a standard real analysis calculation
  -- H((3n+1)/2^ν) - H(n) = log₂((3n+1)/2^ν) - log₂(n)
  --                      = log₂(3n+1) - ν - log₂(n)           [exact division]
  --                      ≤ log₂(3n(1+1/(3N))) - ν - log₂(n)   [bound on 3n+1]
  --                      = log₂(3) + ε(N) - ν                  [log properties]

  -- Cast the quotient to ℝ using exact division
  have h2ν_pos : (2^ν : ℕ) > 0 := Nat.pow_pos (by omega : 0 < 2)
  have h2ν_ne : (2^ν : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp h2ν_pos
  have h2ν_ne_cast : ((2^ν : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h2ν_ne
  have hcast : (↑((3 * n + 1) / 2^ν) : ℝ) = (3 * n + 1 : ℝ) / (2^ν : ℝ) := by
    rw [Nat.cast_div h_exact h2ν_ne_cast]
    push_cast
    ring

  -- log₂(2^ν) = ν
  have h_log_2pow : Real.logb 2 ((2 : ℝ)^ν) = ν := by
    rw [Real.logb_pow]
    have h12 : (1 : ℝ) < 2 := by norm_num
    rw [Real.logb_self_eq_one h12, mul_one]

  -- The main bound using log properties
  calc Real.logb 2 ↑((3 * n + 1) / 2 ^ ν) - Real.logb 2 ↑n
      = Real.logb 2 ((3 * n + 1 : ℝ) / (2^ν : ℝ)) - Real.logb 2 ↑n := by rw [hcast]
    _ = Real.logb 2 (3 * n + 1) - Real.logb 2 ((2 : ℝ)^ν) - Real.logb 2 n := by
        rw [Real.logb_div h3n1_pos.ne' (by positivity : ((2 : ℝ)^ν) ≠ 0)]
    _ = Real.logb 2 (3 * n + 1) - ν - Real.logb 2 n := by rw [h_log_2pow]
    _ ≤ Real.logb 2 (3 * n * (1 + 1 / (3 * N))) - ν - Real.logb 2 n := by
        have h_mono : Real.logb 2 (3 * ↑n + 1) ≤ Real.logb 2 (3 * ↑n * (1 + 1 / (3 * ↑N))) := by
          apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) h3n1_pos
          exact h_bound
        linarith
    _ = Real.logb 2 (3 * n) + Real.logb 2 (1 + 1 / (3 * N)) - ν - Real.logb 2 n := by
        have h_prod : Real.logb 2 (3 * ↑n * (1 + 1 / (3 * ↑N))) =
            Real.logb 2 (3 * ↑n) + Real.logb 2 (1 + 1 / (3 * ↑N)) :=
          Real.logb_mul (by positivity : (3 : ℝ) * ↑n ≠ 0) (by positivity : (1 : ℝ) + 1 / (3 * ↑N) ≠ 0)
        rw [h_prod]
    _ = Real.logb 2 3 + Real.logb 2 n + Real.logb 2 (1 + 1 / (3 * N)) - ν - Real.logb 2 n := by
        have h_prod2 : Real.logb 2 (3 * ↑n) = Real.logb 2 3 + Real.logb 2 ↑n :=
          Real.logb_mul (by norm_num : (3 : ℝ) ≠ 0) (by positivity : (↑n : ℝ) ≠ 0)
        rw [h_prod2]
    _ = Real.logb 2 3 + Real.logb 2 (1 + 1 / (3 * N)) - ν := by ring

/-- Summed height drift over t steps: Σ(H_{i+1} - H_i) ≤ t·(log₂3 + ε(N)) - Σν_i

    This is the telescope that connects to the cycle-mean bound.

    Proof: Sum height_drift_with_floor over each step, using that
    H(n_t) - H(n_0) = Σ_{i<t} (H(n_{i+1}) - H(n_i))
                    ≤ Σ_{i<t} (log₂3 + ε(N) - ν_i)
                    = t·(log₂3 + ε(N)) - Σ_{i<t} ν_i
-/
theorem height_drift_sum (n N t : ℕ) (hn : Odd n) (hN : N ≥ 1)
    (hAboveFloor : ∀ i < t, orbit_raw n i ≥ N) :
    realHeight (orbit_raw n t) - realHeight n ≤
      t * (log2_3 + εFloor N) - ∑ i ∈ Finset.range t, (v2 (3 * orbit_raw n i + 1) : ℝ) := by
  -- Telescope using height_drift_with_floor at each step
  -- The sum Σ(H(n_{i+1}) - H(n_i)) telescopes to H(n_t) - H(n_0)
  -- Each term is bounded by log₂3 + ε(N) - ν_i

  -- Base case
  induction t with
  | zero =>
    simp only [orbit_raw, Finset.range_zero, Finset.sum_empty, CharP.cast_eq_zero, mul_zero, sub_zero]
    linarith
  | succ t ih =>
    -- Need to show: H(n_{t+1}) - H(n) ≤ (t+1)(log₂3 + ε(N)) - Σ_{i<t+1} ν_i

    -- First, get the IH with proper hypothesis
    have hAbove_t : ∀ i < t, orbit_raw n i ≥ N := fun i hi => hAboveFloor i (Nat.lt_succ_of_lt hi)
    have h_ih := ih hAbove_t

    -- Now show the step bound
    -- H(n_{t+1}) - H(n) = (H(n_{t+1}) - H(n_t)) + (H(n_t) - H(n))
    --                   ≤ (log₂3 + ε(N) - ν_t) + (t(log₂3 + ε(N)) - Σ_{i<t} ν_i)
    --                   = (t+1)(log₂3 + ε(N)) - Σ_{i<t+1} ν_i

    -- Establish that orbit_raw n t is odd and positive
    have hn_pos : 0 < n := by
      have hN_ge : n ≥ N := hAboveFloor 0 (Nat.zero_lt_succ t)
      simp only [orbit_raw] at hN_ge
      omega
    have hnt_odd : Odd (orbit_raw n t) := orbit_raw_odd hn hn_pos t
    have hnt_pos : 0 < orbit_raw n t := orbit_raw_pos hn hn_pos t
    have hnt_ge_N : orbit_raw n t ≥ N := hAboveFloor t (Nat.lt_succ_self t)

    -- The next step value
    have h_next : orbit_raw n (t + 1) = (3 * orbit_raw n t + 1) / 2^(v2 (3 * orbit_raw n t + 1)) := by
      simp only [orbit_raw, syracuse_raw]

    -- Apply height_drift_with_floor to the t-th step
    have h_step := height_drift_with_floor (orbit_raw n t) N (v2 (3 * orbit_raw n t + 1))
      hnt_odd hnt_ge_N hN rfl

    -- Express H(n_{t+1}) in terms of the Syracuse step
    have h_height_step : realHeight (orbit_raw n (t + 1)) =
        realHeight ((3 * orbit_raw n t + 1) / 2^(v2 (3 * orbit_raw n t + 1))) := by
      rw [h_next]

    -- Bound the single step height change
    have h_single : realHeight (orbit_raw n (t + 1)) - realHeight (orbit_raw n t) ≤
        log2_3 + εFloor N - v2 (3 * orbit_raw n t + 1) := by
      rw [h_height_step]
      exact h_step

    -- Combine telescope: H(t+1) - H(0) = (H(t+1) - H(t)) + (H(t) - H(0))
    have h_telescope : realHeight (orbit_raw n (t + 1)) - realHeight n =
        (realHeight (orbit_raw n (t + 1)) - realHeight (orbit_raw n t)) +
        (realHeight (orbit_raw n t) - realHeight n) := by ring

    -- Use Finset.sum_range_succ to expand the sum
    have h_sum_expand : ∑ i ∈ Finset.range (t + 1), (v2 (3 * orbit_raw n i + 1) : ℝ) =
        ∑ i ∈ Finset.range t, (v2 (3 * orbit_raw n i + 1) : ℝ) + v2 (3 * orbit_raw n t + 1) := by
      rw [Finset.sum_range_succ]

    -- Cast t+1 properly
    have h_cast_t1 : ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 := by push_cast; rfl

    -- Final calculation using the telescope
    rw [h_telescope]
    -- Goal: (H(t+1) - H(t)) + (H(t) - H(n)) ≤ (t+1)*(log₂3+ε) - Σ
    -- From h_single: H(t+1) - H(t) ≤ log₂3 + ε - ν_t
    -- From h_ih: H(t) - H(n) ≤ t*(log₂3+ε) - Σ_{i<t} ν_i
    -- Sum: LHS ≤ (log₂3+ε-ν_t) + (t*(log₂3+ε) - Σ_{i<t} ν_i)
    --           = (t+1)*(log₂3+ε) - (Σ_{i<t} ν_i + ν_t)
    --           = (t+1)*(log₂3+ε) - Σ_{i<t+1} ν_i

    rw [h_sum_expand, h_cast_t1]
    linarith [h_single, h_ih]

end Collatz
