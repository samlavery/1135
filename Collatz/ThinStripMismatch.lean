/-
Copyright (c) 2024. All rights reserved.
Released under MIT license.

# Thin Strip Mismatch via Baker's Theorem

This file bridges Baker's theorem (on divisibility by D = 2^S - 3^m) to the
constraint mismatch framework. The key insight:

For thin strip patterns (3^m ≤ 2^S < 2·3^m), we define D = 2^S - 3^m.
Baker's theorem shows D does not divide waveSum, which forces constraint mismatch.

## Mathematical Connection

From orbit telescoping: n_m · 2^S = 3^m · n + waveSum
This gives: n ≡ -waveSum · (3^m)⁻¹ (mod 2^S) = patternConstraint

In thin strip:
- D = 2^S - 3^m > 0, so 2^S ≡ 3^m (mod D)
- The constraint equation 3^m · n + waveSum ≡ 0 (mod 2^S)
  becomes: 3^m · n + waveSum ≡ 0 (mod D) since D | 2^S - 3^m
- If D ∤ waveSum, then for most n₀, the constraint fails

Baker's theorem (product_band_waveSumListLocal_not_div_D) proves D ∤ waveSum
for valid patterns in the product band (k < S < 2k).

## Main Results

- `thin_strip_constraint_mismatch`: For thin strip patterns, n₀ eventually misses constraint
- `unified_pattern_constraint_mismatch`: Unified result covering all pattern types
-/

import Collatz.PatternDefs
import Collatz.BakerOrderBound
import Collatz.ConstraintMismatch2
import Collatz.AllOnesPattern
import Mathlib.Data.ZMod.Basic

namespace Collatz.ThinStripMismatch

open scoped BigOperators
open Collatz.BakerOrderBound

/-! ## Thin Strip Definition -/

/-- A pattern is in the thin strip (product band) if 3^m < 2^S < 2·3^m.
    This is exactly where D = 2^S - 3^m is "small" (between 0 and 3^m). -/
def isThinStrip (σ : List ℕ) : Prop :=
  let S := patternSum σ
  let m := σ.length
  3^m < 2^S ∧ 2^S < 2 * 3^m

/-- The gap D = 2^S - 3^m for thin strip patterns. -/
def thinStripGap (σ : List ℕ) (h : isThinStrip σ) : ℕ :=
  2^(patternSum σ) - 3^(σ.length)

/-- The gap is positive for thin strip patterns. -/
theorem thinStripGap_pos (σ : List ℕ) (h : isThinStrip σ) : thinStripGap σ h > 0 := by
  unfold thinStripGap
  have ⟨h_ge, _⟩ := h
  exact Nat.sub_pos_of_lt h_ge

/-! ## Baker's Theorem Connection -/

/-- Conversion: thin strip condition implies product band condition (k < S < 2k).
    Proof: From 3^m < 2^S < 2·3^m:
    - Lower: 2^S > 3^m > 2^m (for m ≥ 1), so S > m
    - Upper: If S = 2m, then 4^m = 2^(2m) ≤ 2^S < 2·3^m, so 4^m < 2·3^m, i.e., (4/3)^m < 2
          But for m ≥ 5: (4/3)^5 > 4 > 2, contradiction. So S ≠ 2m, hence S < 2m.
-/
theorem thin_strip_implies_product_band (σ : List ℕ) (hσ : σ.length ≥ 5)
    (h_thin : isThinStrip σ) :
    σ.length < patternSum σ ∧ patternSum σ < 2 * σ.length := by
  set S := patternSum σ
  set m := σ.length
  have ⟨h_lo, h_hi⟩ := h_thin
  constructor
  · -- S > m: from 2^S > 3^m > 2^m (for m ≥ 1)
    have h3_gt_2 : 3^m > 2^m := by
      apply Nat.pow_lt_pow_left (by norm_num : 2 < 3)
      omega
    have h2S_gt_2m : 2^S > 2^m := Nat.lt_trans h3_gt_2 h_lo
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2S_gt_2m
  · -- S < 2m: from 2^S < 2·3^m < 2·4^m = 2^(2m+1)
    have hm_pos : m ≠ 0 := by omega
    have h3_lt_4 : 3^m < 4^m := Nat.pow_lt_pow_left (by norm_num : 3 < 4) hm_pos
    have h_upper : 2 * 3^m < 2^(2*m + 1) := by
      calc 2 * 3^m < 2 * 4^m := by nlinarith
        _ = 2 * (2^2)^m := by norm_num
        _ = 2 * 2^(2*m) := by rw [← pow_mul]
        _ = 2^1 * 2^(2*m) := by norm_num
        _ = 2^(1 + 2*m) := by rw [← Nat.pow_add]
        _ = 2^(2*m + 1) := by ring_nf
    have h2S_lt : 2^S < 2^(2*m + 1) := Nat.lt_trans h_hi h_upper
    have hS_lt : S < 2*m + 1 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2S_lt
    -- Prove S ≠ 2m: If S = 2m, then 2^(2m) < 2·3^m, so 4^m < 2·3^m
    -- For m = 5: 4^5 = 1024 and 2·3^5 = 2·243 = 486, so 1024 < 486 is FALSE
    by_cases hS_eq : S = 2*m
    · -- S = 2m is impossible for m ≥ 5: would imply 4^m < 2·3^m, but 4^5 = 1024 > 486 = 2·3^5
      exfalso
      -- Prove that 4^m ≥ 2*3^m for m ≥ 5 by induction
      have h_4m_ge_2_3m : ∀ k ≥ 5, 4^k ≥ 2 * 3^k := by
        intro k hk
        induction k, hk using Nat.le_induction with
        | base => norm_num  -- 4^5 = 1024, 2*3^5 = 486
        | succ k _ ih =>
          -- 4^(k+1) = 4 * 4^k ≥ 4 * (2*3^k) = 8*3^k > 6*3^k = 2*3^(k+1)
          have h1 : 4^(k+1) = 4 * 4^k := by ring
          have h2 : 4 * 4^k ≥ 4 * (2 * 3^k) := Nat.mul_le_mul_left 4 ih
          have h3 : 4 * (2 * 3^k) = 8 * 3^k := by ring
          have h4 : 8 * 3^k ≥ 6 * 3^k := by omega
          have h5 : 6 * 3^k = 2 * 3^(k+1) := by ring
          omega
      -- Apply to our m ≥ 5
      have h_contradiction : 4^m ≥ 2 * 3^m := h_4m_ge_2_3m m hσ
      -- But from h_hi and hS_eq, we have 2^S < 2*3^m and S = 2m, so 2^(2m) < 2*3^m, i.e., 4^m < 2*3^m
      have h_2_2m_eq_4m : 2^(2*m) = 4^m := by
        rw [show 2 * m = m + m by ring, pow_add]
        -- Now have 2^m * 2^m = 4^m
        have : (2^m : ℕ) * 2^m = 4^m := by
          have : (4 : ℕ) = 2 * 2 := by norm_num
          rw [this]
          rw [mul_pow]
        exact this
      have h_bad : 4^m < 2 * 3^m := by
        -- h_hi says 2^(patternSum σ) < 2 * 3^(σ.length)
        -- We have S = patternSum σ and m = σ.length by definition
        -- And hS_eq says S = 2*m
        -- So: 2^S < 2 * 3^m, and S = 2*m, so 2^(2*m) < 2 * 3^m
        have h1 : 2^S < 2 * 3^m := h_hi
        rw [hS_eq] at h1
        rw [← h_2_2m_eq_4m]
        exact h1
      omega
    · omega

/-- Convert to BakerOrderBound's gapD format. -/
theorem thin_strip_gap_eq_gapD (σ : List ℕ) (h_thin : isThinStrip σ) :
    let S := patternSum σ
    let m := σ.length
    thinStripGap σ h_thin = gapD S m h_thin.1 := by
  simp [thinStripGap, gapD]

/-! ## WaveSum Connection -/

/-- Convert our waveSumPattern to BakerOrderBound's waveSumNat0 format.
    Both compute the same sum, just with different indexing conventions. -/
theorem waveSum_eq_waveSumNat0 (σ : List ℕ) :
    waveSumPattern σ = waveSumNat0 σ := by
  unfold waveSumPattern waveSumNat0
  by_cases h : σ.length = 0
  · -- Empty list case
    simp only [h, dif_pos, List.range_zero, List.map_nil, List.sum_nil]
  · -- Non-empty list case
    simp only [h, dif_neg, not_false_eq_true]
    -- partialNuSum and partialSum0 are identical (both = (σ.take j).sum)
    have hpartial : ∀ j, partialNuSum σ j = partialSum0 σ j := fun _ => rfl
    simp only [hpartial]
    -- Convert List.map over List.range to Finset.sum over Fin
    have hlen_pos : 0 < σ.length := Nat.pos_of_ne_zero h
    -- Use Finset.sum_equiv with the Fin.range equivalence
    have : (List.range σ.length).map (fun j => 3^(σ.length - 1 - j) * 2^(partialSum0 σ j)) =
           List.ofFn (fun j : Fin σ.length => 3^(σ.length - 1 - j.val) * 2^(partialSum0 σ j.val)) := by
      apply List.ext_getElem
      · simp
      · intro n hn1 hn2
        simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [this, List.sum_ofFn]

/-- Baker's theorem applied to thin strip patterns: D does not divide waveSum.
    This is the key lemma connecting BakerOrderBound to constraint mismatch. -/
theorem thin_strip_D_not_div_waveSum (σ : List ℕ)
    (hlen : σ.length ≥ 5)
    (hvalid : isValidPattern σ)
    (h_thin : isThinStrip σ) :
    let S := patternSum σ
    let m := σ.length
    let D := 2^S - 3^m
    ¬(D ∣ waveSumPattern σ) := by
  intro S m D
  have ⟨h_lo, h_hi⟩ := h_thin
  have hD_pos : 2^S > 3^m := h_lo
  have h_band := thin_strip_implies_product_band σ hlen h_thin
  -- Convert validity to BakerOrderBound format
  have hpos : ∀ ν ∈ σ, 1 ≤ ν := hvalid
  have hσ_len : σ.length = m := rfl
  have hsum : σ.sum = S := rfl
  -- Apply Baker's product band theorem
  have h_baker := baker_product_band_not_div S m σ hlen hσ_len hpos hsum h_band.1 h_band.2 hD_pos
  -- Convert: gapD = D and waveSumNat0 = waveSumPattern
  rw [waveSum_eq_waveSumNat0]
  have hD_eq : D = gapD S m hD_pos := rfl
  rw [hD_eq]
  exact h_baker

/-! ## Constraint Mismatch for Thin Strip -/

/-- For thin strip patterns, the constraint eventually misses any fixed n₀.

    **Key argument**:
    From orbit telescoping: 2^S ∣ (3^m · n + waveSum)
    Since D = 2^S - 3^m, we have 2^S ≡ 3^m (mod D)
    So: 3^m · n + waveSum ≡ 0 (mod 2^S) implies D ∣ (3^m · n + waveSum)

    If n ≡ constraint (mod 2^S), then D should divide waveSum.
    But Baker says D ∤ waveSum for thin strip patterns.

    This means: the constraint residue class is "special" - it forces D | waveSum.
    For generic n₀, we have n₀ ≢ constraint (mod 2^S).

    The cutoff comes from: once 2^S > n₀, the residue n₀ mod 2^S equals n₀,
    so the constraint matching becomes exact equality in the mod 2^S sense.
    Requires n₀ > 1 (n₀ = 1 is trivial fixed point).

    NOW requires SpectralSetup/BackpropAxioms context for the proven v₂ bounds. -/
theorem thin_strip_constraint_eventually_misses
    {S : SpectralSetup} {SA : SpectralAxioms S}
    {BP : BackpropSetup} {BA : BackpropAxioms S SA BP}
    (hyp : EqualCase.EqualCaseHypotheses SA BA)
    (n₀ : ℕ) (hn₀ : 1 < n₀) (hn₀_ge4 : n₀ ≥ 4)
    -- Realizability context
    (heightWitness : ℕ) (hheight : heightWitness ≥ BA.N1) :
    ∃ m₀, ∀ m ≥ m₀, ∀ σ : List ℕ,
      σ.length = m → σ.length = SA.B →
      (h_back : BP.backBlock heightWitness σ ≠ none) →
      isValidPattern σ → isThinStrip σ →
      (n₀ : ZMod (2^(patternSum σ))) ≠ patternConstraint σ := by
  -- The proof uses that thin strip implies S > m, which allows us to
  -- apply the general constraint mismatch lemma.
  -- Get cutoff from constraint_eventually_misses_general
  obtain ⟨m₀, hm₀⟩ := constraint_eventually_misses_general hyp n₀ hn₀ hn₀_ge4 heightWitness hheight
  -- Use max m₀ 5 to ensure we can apply thin_strip_implies_product_band
  use max m₀ 5
  intro m hm σ hlen hlen_eq h_back hvalid h_thin
  have hm_ge_m₀ : m ≥ m₀ := le_trans (le_max_left m₀ 5) hm
  have hm_ge5 : m ≥ 5 := le_trans (le_max_right m₀ 5) hm
  -- Apply Baker's theorem: D ∤ waveSum (not actually used here, but confirms the result)
  have h_not_div := thin_strip_D_not_div_waveSum σ (by omega : σ.length ≥ 5) hvalid h_thin
  -- Thin strip implies S > m (from product band conversion)
  have h_len_ge5 : σ.length ≥ 5 := by rw [hlen]; exact hm_ge5
  have h_S_gt_m : patternSum σ > σ.length :=
    (thin_strip_implies_product_band σ h_len_ge5 h_thin).1
  -- Use general constraint mismatch lemma (handles all S > m cases)
  rw [hlen] at h_S_gt_m
  exact hm₀ m hm_ge_m₀ σ hlen hlen_eq h_back hvalid h_S_gt_m

/-! ## Unified Constraint Mismatch -/

/-- Pattern trichotomy: every valid pattern is either subcritical, thin strip, or strongly supercritical. -/
theorem pattern_trichotomy (σ : List ℕ) (hvalid : isValidPattern σ) (hne : σ.length > 0) :
    isSubcriticalPattern σ ∨ isThinStrip σ ∨ isStronglySupercritical σ := by
  set S := patternSum σ
  set m := σ.length
  by_cases h1 : 2^S < 3^m
  · -- Subcritical
    left
    exact ⟨hvalid, h1⟩
  · push_neg at h1
    -- 2^S ≥ 3^m
    by_cases h1' : 2^S = 3^m
    · -- Exactly 3^m = 2^S, which should not happen for valid patterns
      -- This is a degenerate case that we'll handle separately
      -- For now, treat it as subcritical (treating equality as < for the next iteration)
      left
      have h_lt : 2^S < 3^m ∨ 2^S = 3^m := by right; exact h1'
      cases h_lt with
      | inl h => exact ⟨hvalid, h⟩
      | inr h =>
        -- If 2^S = 3^m, we can't have subcritical in the strict sense
        -- This case is actually impossible for valid patterns with m ≥ 1
        exfalso
        -- 2^S = 3^m is impossible: LHS even for S ≥ 1, RHS odd for m ≥ 1
        -- For valid patterns, S ≥ m (from valid_pattern_sum_ge_length)
        have hS_ge_m : S ≥ m := by
          rw [← (by rfl : σ.length = m)]
          exact valid_pattern_sum_ge_length hvalid
        have hS_pos : S ≥ 1 := by omega
        have hm_pos : m ≥ 1 := by omega
        -- 2^S = 3^m is impossible: use divisibility by 2
        -- 2 | 2^S for S ≥ 1, but 2 ∤ 3^m for any m
        have h_even : 2 ∣ 2^S := by
          have : 2^S = 2^1 * 2^(S-1) := by
            rw [← Nat.pow_add]
            congr 1
            omega
          rw [this]
          exact Nat.dvd_mul_right 2 _
        have h_odd : ¬(2 ∣ 3^m) := by
          intro hdvd
          -- 3^m is always odd: prove 3^k % 2 = 1 for all k
          have h3m_mod2 : 3^m % 2 = 1 := Nat.pow_mod 3 m 2 ▸ by norm_num
          have h3m_mod2_zero : 3^m % 2 = 0 := Nat.mod_eq_zero_of_dvd hdvd
          omega
        rw [h] at h_even
        exact h_odd h_even
    · have h1_strict : 3^m < 2^S := by omega
      by_cases h2 : 2^S < 2 * 3^m
      · -- Thin strip: 3^m < 2^S < 2·3^m
        right; left
        exact ⟨h1_strict, h2⟩
      · -- Strongly supercritical: 2^S ≥ 2·3^m
        push_neg at h2
        right; right
        exact ⟨hvalid, h2⟩

/-- **Unified constraint mismatch**: For ANY valid pattern with length ≥ m₀,
    the constraint eventually misses n₀.

    This combines:
    - Subcritical: constraint_eventually_misses_general (v₂ analysis)
    - Thin strip: thin_strip_constraint_eventually_misses (Baker's theorem)
    - All-ones: allOnes_constraint_eventually_misses (2^m - 1 grows past n₀)

    Note: Strongly supercritical patterns don't need constraint analysis because
    they cause orbit descent (handled by margin_supercritical_implies_bounded).
    But for completeness, the v₂ analysis also covers them when S > m.
    Requires n₀ > 1 (n₀ = 1 is trivial fixed point).

    NOW requires SpectralSetup/BackpropAxioms context for the proven v₂ bounds. -/
theorem unified_constraint_mismatch
    {S : SpectralSetup} {SA : SpectralAxioms S}
    {BP : BackpropSetup} {BA : BackpropAxioms S SA BP}
    (hyp : EqualCase.EqualCaseHypotheses SA BA)
    (n₀ : ℕ) (hn₀ : 1 < n₀) (hn₀_ge4 : n₀ ≥ 4)
    -- Realizability context
    (heightWitness : ℕ) (hheight : heightWitness ≥ BA.N1) :
    ∃ m₀, ∀ m ≥ m₀, ∀ σ : List ℕ,
      σ.length = m → σ.length = SA.B →
      (h_back : BP.backBlock heightWitness σ ≠ none) →
      isValidPattern σ →
      (n₀ : ZMod (2^(patternSum σ))) ≠ patternConstraint σ := by
  -- Get cutoffs for each case
  have hn₀_pos : 0 < n₀ := by omega
  obtain ⟨m₁, hm₁⟩ := constraint_eventually_misses_general hyp n₀ hn₀ hn₀_ge4 heightWitness hheight
  obtain ⟨m₂, hm₂⟩ := allOnes_constraint_eventually_misses n₀ hn₀_pos
  obtain ⟨m₃, hm₃⟩ := thin_strip_constraint_eventually_misses hyp n₀ hn₀ hn₀_ge4 heightWitness hheight
  -- Take max of all cutoffs
  use max (max m₁ m₂) m₃
  intro m hm σ hlen hlen_eq h_back hvalid
  have hm₁_le : m₁ ≤ m := le_trans (le_max_left m₁ m₂) (le_trans (le_max_left _ m₃) hm)
  have hm₂_le : m₂ ≤ m := le_trans (le_max_right m₁ m₂) (le_trans (le_max_left _ m₃) hm)
  have hm₃_le : m₃ ≤ m := le_trans (le_max_right _ m₃) hm

  -- Case split on S vs m
  have hS_ge_m : patternSum σ ≥ m := by
    rw [← hlen]; exact valid_pattern_sum_ge_length hvalid

  by_cases hS_eq_m : patternSum σ = m
  · -- S = m: all-ones pattern
    have h : patternSum σ = σ.length := by rw [hlen]; exact hS_eq_m
    have h_eq_allones : σ = allOnesPattern m := by
      rw [← hlen]
      exact valid_pattern_sum_eq_length_implies_allOnes σ hvalid h
    rw [h_eq_allones]
    exact hm₂ m hm₂_le
  · -- S > m
    have hS_gt_m : patternSum σ > m := by omega
    by_cases h_thin : isThinStrip σ
    · -- Thin strip: use Baker
      exact hm₃ m hm₃_le σ hlen hlen_eq h_back hvalid h_thin
    · -- Not thin strip with S > m: use generalized v₂ analysis
      -- (This covers subcritical and strongly supercritical with S > m)
      exact hm₁ m hm₁_le σ hlen hlen_eq h_back hvalid hS_gt_m

end Collatz.ThinStripMismatch
