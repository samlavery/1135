/-
Copyright (c) 2024. All rights reserved.
Released under MIT license.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Digits.Lemmas
import Collatz.Basic

/-!
# DC-Mass and Bit Profile Rigidity

This file proves a key spectral-combinatorial bridge:

**High DC-mass ⟹ bit profile is almost constant**

## Main Results

- `dcMass_eq_mean_sq`: For ±1 profiles, dcMass(f) = (mean f)²
- `high_dcMass_minority_bound`: If dcMass ≥ 1-ε, minority fraction ≤ (1-√(1-ε))/2 ≤ ε/2

## Key Identity

For a profile f : Fin L → {-1, +1} with orthonormal DFT:

  dcMass(f) = |f̂(0)|² / L = (1/L² · (Σⱼ f(j))²) = (mean f)²

Equivalently: dcMass(f) = (1 - 2q)² where q is the minority fraction.

## Confidence: 99%+

This is pure algebra with no Collatz dependency.
-/

namespace Collatz

open scoped BigOperators
open Finset

/-!
## Section 1: ±1 Profiles and Mean
-/

/-- A ±1 profile on L positions. Values are exactly +1 or -1. -/
def IsPMOne {L : ℕ} (f : Fin L → ℝ) : Prop :=
  ∀ j, f j = 1 ∨ f j = -1

/-- The mean of a profile. -/
noncomputable def profileMean {L : ℕ} [NeZero L] (f : Fin L → ℝ) : ℝ :=
  (∑ j : Fin L, f j) / L

/-- For ±1 profiles, sum of squares equals L. -/
lemma pmOne_sum_sq {L : ℕ} (f : Fin L → ℝ) (hf : IsPMOne f) :
    ∑ j : Fin L, (f j)^2 = L := by
  have h : ∀ j, (f j)^2 = 1 := fun j => by
    cases hf j with
    | inl h => simp [h]
    | inr h => simp [h]
  simp_rw [h]
  simp

/-- DC-mass: fraction of spectral energy at DC.
    For ±1 profiles with Parseval giving total energy L:
    dcMass = |f̂(0)|² / L = (1/L²)(Σⱼ f(j))² -/
noncomputable def dcMassPM {L : ℕ} [NeZero L] (f : Fin L → ℝ) : ℝ :=
  (∑ j : Fin L, f j)^2 / (L : ℝ)^2

/-!
## Section 2: The Key Identity: dcMass = (mean)²
-/

/-- **KEY IDENTITY**: For any profile, dcMass equals the square of the mean.
    This is exact, no approximation. -/
theorem dcMass_eq_mean_sq {L : ℕ} [NeZero L] (f : Fin L → ℝ) :
    dcMassPM f = (profileMean f)^2 := by
  unfold dcMassPM profileMean
  have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  simp [div_eq_mul_inv, mul_pow, inv_pow, hL]

/-- Mean of a ±1 profile is bounded: |m| ≤ 1. -/
lemma mean_bound {L : ℕ} [NeZero L] (f : Fin L → ℝ) (hf : IsPMOne f) :
    |profileMean f| ≤ 1 := by
  unfold profileMean
  have hL_pos : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  have hL_ne : (L : ℝ) ≠ 0 := ne_of_gt hL_pos
  rw [abs_div, abs_of_pos hL_pos]
  have hsum_bound : |∑ j : Fin L, f j| ≤ L := by
    calc |∑ j : Fin L, f j|
        ≤ ∑ j : Fin L, |f j| := abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin L, 1 := by
          congr 1; ext j
          cases hf j with
          | inl h => simp [h]
          | inr h => simp [h]
      _ = L := by simp
  calc |∑ j : Fin L, f j| / L
      ≤ L / L := div_le_div_of_nonneg_right hsum_bound (le_of_lt hL_pos)
    _ = 1 := div_self hL_ne

/-- DC-mass of ±1 profile is in [0, 1]. -/
lemma dcMass_bounds {L : ℕ} [NeZero L] (f : Fin L → ℝ) (hf : IsPMOne f) :
    0 ≤ dcMassPM f ∧ dcMassPM f ≤ 1 := by
  rw [dcMass_eq_mean_sq]
  constructor
  · exact sq_nonneg _
  · have h := mean_bound f hf
    have h_abs_nonneg : 0 ≤ |profileMean f| := abs_nonneg _
    calc (profileMean f)^2 = |profileMean f|^2 := (sq_abs _).symm
      _ ≤ 1^2 := by
        apply sq_le_sq'
        · linarith [abs_nonneg (profileMean f)]
        · exact h
      _ = 1 := one_pow 2

/-!
## Section 3: dcMass in terms of minority fraction

Key insight: m = 2p - 1 where p is fraction of +1s.
So dcMass = m² = (2p-1)² = (1-2q)² where q = min(p, 1-p) is minority fraction.
-/

/-- Fraction of +1 entries in a ±1 profile. -/
noncomputable def plusOneFraction {L : ℕ} [NeZero L] (f : Fin L → ℝ) : ℝ :=
  (Finset.univ.filter (fun j => f j = 1)).card / L

/-- Minority fraction: the smaller of p and 1-p. -/
noncomputable def minorityFraction {L : ℕ} [NeZero L] (f : Fin L → ℝ) : ℝ :=
  min (plusOneFraction f) (1 - plusOneFraction f)

/-- For ±1 profiles, sum = (2p - 1) * L where p is the +1 fraction. -/
lemma pmOne_sum_eq {L : ℕ} [NeZero L] (f : Fin L → ℝ) (hf : IsPMOne f) :
    ∑ j : Fin L, f j = (2 * plusOneFraction f - 1) * L := by
  -- Count +1s and -1s
  set P := Finset.univ.filter (fun j : Fin L => f j = 1) with hP_def
  set M := Finset.univ.filter (fun j : Fin L => f j = -1) with hM_def
  have hPM_disjoint : Disjoint P M := by
    rw [hP_def, hM_def, Finset.disjoint_filter]
    intro x _ hx hy
    rw [hx] at hy
    norm_num at hy
  have hPM_cover : P ∪ M = Finset.univ := by
    ext x
    rw [hP_def, hM_def]
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact hf x
  have hcard : P.card + M.card = L := by
    have h := Finset.card_union_of_disjoint hPM_disjoint
    rw [hPM_cover] at h
    simp only [Finset.card_univ, Fintype.card_fin] at h
    exact h.symm
  -- Sum over P gives P.card (all +1), sum over M gives -M.card (all -1)
  have hsum_P : ∑ j ∈ P, f j = P.card := by
    rw [Finset.sum_eq_card_nsmul (s := P) (b := (1 : ℝ))]
    · rw [nsmul_eq_mul, mul_one]
    · intro x hx
      rw [hP_def, Finset.mem_filter] at hx
      exact hx.2
  have hsum_M : ∑ j ∈ M, f j = -(M.card : ℝ) := by
    rw [Finset.sum_eq_card_nsmul (s := M) (b := (-1 : ℝ))]
    · rw [nsmul_eq_mul, mul_neg, mul_one]
    · intro x hx
      rw [hM_def, Finset.mem_filter] at hx
      exact hx.2
  -- Total sum
  have hsum_total : ∑ j : Fin L, f j = P.card - M.card := by
    have huniv : ∑ j : Fin L, f j = ∑ j ∈ P ∪ M, f j := by
      conv_lhs => rw [← hPM_cover]
    rw [huniv, Finset.sum_union hPM_disjoint, hsum_P, hsum_M]
    ring
  rw [hsum_total]
  -- Now: P.card - M.card = (2 * P.card / L - 1) * L
  have hL_pos : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  have hL_ne : (L : ℝ) ≠ 0 := ne_of_gt hL_pos
  have hP_le : P.card ≤ L := by omega
  have hM_eq : (M.card : ℝ) = L - P.card := by
    have hM_nat : M.card = L - P.card := by omega
    rw [hM_nat, Nat.cast_sub hP_le]
  rw [hM_eq]
  unfold plusOneFraction
  rw [hP_def]
  field_simp
  ring

/-- For ±1 profiles, mean = 2p - 1. -/
lemma pmOne_mean_eq {L : ℕ} [NeZero L] (f : Fin L → ℝ) (hf : IsPMOne f) :
    profileMean f = 2 * plusOneFraction f - 1 := by
  unfold profileMean
  rw [pmOne_sum_eq f hf]
  have hL_pos : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  have hL_ne : (L : ℝ) ≠ 0 := ne_of_gt hL_pos
  field_simp [hL_ne]

/-- |2p - 1| = |1 - 2q| where q = min(p, 1-p). -/
lemma abs_two_p_minus_one_eq {L : ℕ} [NeZero L] (f : Fin L → ℝ) (hf : IsPMOne f)
    (hp_bound : 0 ≤ plusOneFraction f ∧ plusOneFraction f ≤ 1) :
    |2 * plusOneFraction f - 1| = 1 - 2 * minorityFraction f := by
  unfold minorityFraction
  set p := plusOneFraction f
  rcases le_or_lt p (1/2) with hp_le | hp_gt
  · -- p ≤ 1/2: minority is p, so |2p-1| = 1-2p = 1 - 2*min(p, 1-p)
    have hmin : min p (1 - p) = p := by
      apply min_eq_left
      linarith
    rw [hmin]
    have h : 2 * p - 1 ≤ 0 := by linarith
    rw [abs_of_nonpos h]
    ring
  · -- p > 1/2: minority is 1-p, so |2p-1| = 2p-1 = 1 - 2*(1-p)
    have hmin : min p (1 - p) = 1 - p := by
      apply min_eq_right
      linarith
    rw [hmin]
    have h : 0 ≤ 2 * p - 1 := by linarith
    rw [abs_of_nonneg h]
    ring

/-- plusOneFraction is in [0, 1] for ±1 profiles. -/
lemma plusOneFraction_bounds {L : ℕ} [NeZero L] (f : Fin L → ℝ) (hf : IsPMOne f) :
    0 ≤ plusOneFraction f ∧ plusOneFraction f ≤ 1 := by
  unfold plusOneFraction
  constructor
  · apply div_nonneg
    · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _
  · have hL_pos : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
    rw [div_le_one hL_pos]
    have h : (Finset.univ.filter (fun j => f j = 1)).card ≤ Finset.univ.card :=
      Finset.card_filter_le _ _
    simp only [Finset.card_univ, Fintype.card_fin] at h
    exact Nat.cast_le.mpr h

/-- **KEY IDENTITY 2**: dcMass = (1 - 2q)² where q is minority fraction.

    This is the cleaner form that makes the "high DC ⟹ low minority" obvious. -/
theorem dcMass_eq_one_minus_two_q_sq {L : ℕ} [NeZero L] (f : Fin L → ℝ) (hf : IsPMOne f) :
    dcMassPM f = (1 - 2 * minorityFraction f)^2 := by
  rw [dcMass_eq_mean_sq, pmOne_mean_eq f hf]
  have hp := plusOneFraction_bounds f hf
  have h := abs_two_p_minus_one_eq f hf hp
  -- dcMass = (2p-1)² = |2p-1|² = (1-2q)²
  calc (2 * plusOneFraction f - 1)^2
      = |2 * plusOneFraction f - 1|^2 := (sq_abs _).symm
    _ = (1 - 2 * minorityFraction f)^2 := by rw [h]

/-!
## Section 4: High DC-Mass Implies Minority Bound

MAIN THEOREM: If dcMass(f) ≥ 1 - ε, then q ≤ (1 - √(1-ε))/2 ≤ ε/2.
-/

/-- Minority fraction is in [0, 1/2]. -/
lemma minorityFraction_bounds {L : ℕ} [NeZero L] (f : Fin L → ℝ) (hf : IsPMOne f) :
    0 ≤ minorityFraction f ∧ minorityFraction f ≤ 1/2 := by
  unfold minorityFraction
  have hp := plusOneFraction_bounds f hf
  constructor
  · exact le_min (by linarith) (by linarith)
  · apply min_le_iff.mpr
    by_cases h : plusOneFraction f ≤ 1/2
    · left; exact h
    · push_neg at h
      right; linarith

/-- Minority fraction equals the smaller count divided by L. -/
lemma minorityFraction_eq_min_count_div_L {L : ℕ} [NeZero L] (f : Fin L → ℝ) (hf : IsPMOne f) :
    let numPlusOne := (Finset.univ.filter (fun j => f j = 1)).card
    let numMinusOne := (Finset.univ.filter (fun j => f j = -1)).card
    minorityFraction f = min (numPlusOne : ℝ) (numMinusOne : ℝ) / L := by
  intro numPlusOne numMinusOne
  set P := Finset.univ.filter (fun j : Fin L => f j = 1) with hP_def
  set M := Finset.univ.filter (fun j : Fin L => f j = -1) with hM_def
  have hPM_disjoint : Disjoint P M := by
    rw [hP_def, hM_def, Finset.disjoint_filter]
    intro x _ hx hy
    rw [hx] at hy
    norm_num at hy
  have hPM_cover : P ∪ M = Finset.univ := by
    ext x
    rw [hP_def, hM_def]
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact hf x
  have hcard_sum : P.card + M.card = L := by
    have h := Finset.card_union_of_disjoint hPM_disjoint
    rw [hPM_cover] at h
    simp only [Finset.card_univ, Fintype.card_fin] at h
    exact h.symm
  have hL_pos : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  have hL_ne : (L : ℝ) ≠ 0 := ne_of_gt hL_pos
  have hpof : plusOneFraction f = P.card / L := by
    unfold plusOneFraction
    rw [hP_def]
  have h1mp : 1 - plusOneFraction f = M.card / L := by
    have hPM_sum_real : (P.card : ℝ) + M.card = L := by exact_mod_cast hcard_sum
    rw [hpof]
    field_simp [hL_ne]
    linarith
  have hminf : minorityFraction f = min (P.card : ℝ) M.card / L := by
    unfold minorityFraction
    rw [h1mp, hpof, min_div_div_right (le_of_lt hL_pos)]
  have hP_eq : numPlusOne = P.card := rfl
  have hM_eq : numMinusOne = M.card := rfl
  simpa [hP_eq, hM_eq] using hminf

/-- The exact minority bound from high DC-mass.
    If dcMass ≥ 1 - ε, then minority fraction q ≤ (1 - √(1-ε))/2. -/
theorem high_dcMass_exact_minority_bound {L : ℕ} [NeZero L] (f : Fin L → ℝ) (hf : IsPMOne f)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hdcMass : dcMassPM f ≥ 1 - ε) :
    minorityFraction f ≤ (1 - Real.sqrt (1 - ε)) / 2 := by
  -- From dcMass = (1-2q)², we get (1-2q)² ≥ 1-ε
  have h_dcMass_eq := dcMass_eq_one_minus_two_q_sq f hf
  rw [h_dcMass_eq] at hdcMass
  -- So (1-2q)² ≥ 1-ε

  set q := minorityFraction f with hq_def
  have hq_bounds := minorityFraction_bounds f hf
  have hq_nonneg : 0 ≤ q := hq_bounds.1
  have hq_le_half : q ≤ 1/2 := hq_bounds.2

  -- Since 0 ≤ q ≤ 1/2, we have 1-2q ∈ [0, 1]
  have h_1_2q_nonneg : 0 ≤ 1 - 2 * q := by linarith
  have h_1_2q_le_1 : 1 - 2 * q ≤ 1 := by linarith

  -- (1-2q)² ≥ 1-ε, and 1-2q ≥ 0, so 1-2q ≥ √(1-ε)
  have h_1_eps_nonneg : 0 ≤ 1 - ε := by linarith
  have h_sq : (1 - 2 * q)^2 ≥ 1 - ε := hdcMass
  have h_sqrt : 1 - 2 * q ≥ Real.sqrt (1 - ε) := by
    have h1 : Real.sqrt ((1 - 2 * q)^2) = |1 - 2 * q| := Real.sqrt_sq_eq_abs _
    have h2 : |1 - 2 * q| = 1 - 2 * q := abs_of_nonneg h_1_2q_nonneg
    rw [← h2, ← h1]
    exact Real.sqrt_le_sqrt h_sq

  -- Hence q ≤ (1 - √(1-ε))/2
  linarith

/-- The simple minority bound: if dcMass ≥ 1 - ε, then minority fraction ≤ ε/2.
    This uses √(1-ε) ≥ 1-ε, so 1 - √(1-ε) ≤ ε. -/
theorem high_dcMass_simple_minority_bound {L : ℕ} [NeZero L] (f : Fin L → ℝ) (hf : IsPMOne f)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hdcMass : dcMassPM f ≥ 1 - ε) :
    minorityFraction f ≤ ε / 2 := by
  have h1 := high_dcMass_exact_minority_bound f hf ε hε_pos hε_lt hdcMass
  have h_sqrt_ineq : 1 - Real.sqrt (1 - ε) ≤ ε := by
    have h_1_minus_eps : 0 ≤ 1 - ε := by linarith
    -- Key: √x ≥ x for x ∈ [0,1] because √x - x = √x(1 - √x) ≥ 0
    have h_sqrt_ge : Real.sqrt (1 - ε) ≥ 1 - ε := by
      have h_sq : Real.sqrt (1 - ε) * Real.sqrt (1 - ε) = 1 - ε := Real.mul_self_sqrt h_1_minus_eps
      have h_sqrt_nonneg : 0 ≤ Real.sqrt (1 - ε) := Real.sqrt_nonneg _
      have h_sqrt_le_1 : Real.sqrt (1 - ε) ≤ 1 := by
        have : 1 - ε ≤ 1 := by linarith
        calc Real.sqrt (1 - ε) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt this
          _ = 1 := Real.sqrt_one
      -- √(1-ε) ≥ 1-ε iff √(1-ε) - (1-ε) ≥ 0 iff √(1-ε)(1 - √(1-ε)) + √(1-ε) - 1 + ε ≥ 0
      -- Simpler: √x ≥ x for x ∈ [0,1]. Since √x * √x = x and √x ≤ 1, we have √x ≥ √x * √x = x
      calc Real.sqrt (1 - ε)
          ≥ Real.sqrt (1 - ε) * Real.sqrt (1 - ε) := by
            have : Real.sqrt (1 - ε) * 1 ≥ Real.sqrt (1 - ε) * Real.sqrt (1 - ε) :=
              mul_le_mul_of_nonneg_left h_sqrt_le_1 h_sqrt_nonneg
            simp at this
            exact this
        _ = 1 - ε := h_sq
    linarith
  calc minorityFraction f
      ≤ (1 - Real.sqrt (1 - ε)) / 2 := h1
    _ ≤ ε / 2 := by linarith

/-- Corollary: High DC-mass bounds the number of minority bits.
    If dcMass(f) ≥ 1 - ε, then at most (ε/2)·L bits differ from majority. -/
theorem high_dcMass_hamming_bound {L : ℕ} [NeZero L] (f : Fin L → ℝ) (hf : IsPMOne f)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hdcMass : dcMassPM f ≥ 1 - ε) :
    let numPlusOne := (Finset.univ.filter (fun j => f j = 1)).card
    let numMinusOne := (Finset.univ.filter (fun j => f j = -1)).card
    min (numPlusOne : ℝ) (numMinusOne : ℝ) ≤ (ε / 2) * L := by
  intro numPlusOne numMinusOne
  have hL_pos : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  have hL_ne : (L : ℝ) ≠ 0 := ne_of_gt hL_pos
  have hq := high_dcMass_simple_minority_bound f hf ε hε_pos hε_lt hdcMass
  have hq' := mul_le_mul_of_nonneg_right hq (le_of_lt hL_pos)
  have hmin := minorityFraction_eq_min_count_div_L f hf
  have hmin' : minorityFraction f = min (numPlusOne : ℝ) (numMinusOne : ℝ) / L := by
    simpa [numPlusOne, numMinusOne] using hmin
  have hmin'' : minorityFraction f * L = min (numPlusOne : ℝ) (numMinusOne : ℝ) := by
    calc minorityFraction f * L
        = (min (numPlusOne : ℝ) (numMinusOne : ℝ) / L) * L := by simpa [hmin']
      _ = min (numPlusOne : ℝ) (numMinusOne : ℝ) := by
          field_simp [hL_ne]
  calc min (numPlusOne : ℝ) (numMinusOne : ℝ)
      = minorityFraction f * L := hmin''.symm
    _ ≤ (ε / 2) * L := by nlinarith

/-!
## Section 5: Application to Bit Profiles
-/

/-- Convert a bit (0 or 1) to ±1 value: 0 ↦ -1, 1 ↦ +1. -/
def bitToPM (b : ℕ) : ℝ := if b % 2 = 1 then 1 else -1

/-- The LSB profile of x: the first L bits as ±1 values. -/
def lsbProfile (L : ℕ) (x : ℕ) : Fin L → ℝ :=
  fun j => bitToPM (x / 2^j.val)

/-- LSB profile is ±1 valued. -/
lemma lsbProfile_isPMOne (L : ℕ) (x : ℕ) : IsPMOne (lsbProfile L x) := by
  intro j
  unfold lsbProfile bitToPM
  split_ifs with h
  · left; rfl
  · right; rfl

/-- For odd x, bit 0 is 1, so lsbProfile has +1 at position 0. -/
lemma lsbProfile_zero_odd (L : ℕ) [NeZero L] (x : ℕ) (hx : Odd x) :
    lsbProfile L x ⟨0, NeZero.pos L⟩ = 1 := by
  unfold lsbProfile bitToPM
  simp only [pow_zero, Nat.div_one]
  rw [Nat.odd_iff] at hx
  simp [hx]

/-!
## Section 6: Threshold for Majority Sign

For odd x with high LSB DC-mass, "mostly zeros" is impossible when L is large enough.

Key threshold: L > 2/(1 - √(1-ε)) forces majority to be +1 for odd x.
-/

/-- Threshold L value beyond which odd x with dcMass ≥ 1-ε must have majority +1s. -/
noncomputable def majorityThresholdL (ε : ℝ) : ℝ :=
  2 / (1 - Real.sqrt (1 - ε))

/-!
## Section 6: DC Orientation for LSB Profiles

To break the ± symmetry, we track the sign of the mean.
This yields a clean "majority is +1" condition without a size threshold.
-/

/-- LSB DC-pure with bias towards +1 (mean nonnegative). -/
def InCdcPlus (L : ℕ) [NeZero L] (ε : ℝ) (x : ℕ) : Prop :=
  Odd x ∧
  dcMassPM (lsbProfile L x) ≥ 1 - ε ∧
  profileMean (lsbProfile L x) ≥ 0

lemma lsb_majority_ones_of_mean_nonneg
    {L : ℕ} [NeZero L] (x : ℕ)
    (hmean : profileMean (lsbProfile L x) ≥ 0) :
    (Finset.univ.filter (fun j : Fin L => lsbProfile L x j = -1)).card
      ≤ (Finset.univ.filter (fun j : Fin L => lsbProfile L x j = 1)).card := by
  let f := lsbProfile L x
  have hf : IsPMOne f := lsbProfile_isPMOne L x
  have hmean_eq : profileMean f = 2 * plusOneFraction f - 1 := pmOne_mean_eq f hf
  have hp_ge_half : (1 / 2 : ℝ) ≤ plusOneFraction f := by
    have : 0 ≤ 2 * plusOneFraction f - 1 := by linarith [hmean, hmean_eq]
    linarith
  let numPlusOne := (Finset.univ.filter (fun j : Fin L => f j = 1)).card
  let numMinusOne := (Finset.univ.filter (fun j : Fin L => f j = -1)).card
  set P := Finset.univ.filter (fun j : Fin L => f j = 1) with hP_def
  set M := Finset.univ.filter (fun j : Fin L => f j = -1) with hM_def
  have hPM_disjoint : Disjoint P M := by
    rw [hP_def, hM_def, Finset.disjoint_filter]
    intro x _ hx hy
    rw [hx] at hy
    norm_num at hy
  have hPM_cover : P ∪ M = Finset.univ := by
    ext x
    rw [hP_def, hM_def]
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact hf x
  have hcard_sum : P.card + M.card = L := by
    have h := Finset.card_union_of_disjoint hPM_disjoint
    rw [hPM_cover] at h
    simp only [Finset.card_univ, Fintype.card_fin] at h
    exact h.symm
  have hL_pos : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  have hL_ne : (L : ℝ) ≠ 0 := ne_of_gt hL_pos
  have hP_eq : numPlusOne = P.card := rfl
  have hM_eq : numMinusOne = M.card := rfl
  have hpof : plusOneFraction f = P.card / L := by
    unfold plusOneFraction
    rw [hP_def]
  have h1mp : 1 - plusOneFraction f = M.card / L := by
    have hPM_sum_real : (P.card : ℝ) + M.card = L := by exact_mod_cast hcard_sum
    rw [hpof]
    field_simp [hL_ne]
    linarith
  have hmn_div : (numMinusOne : ℝ) / L ≤ (numPlusOne : ℝ) / L := by
    have h1 : 1 - plusOneFraction f ≤ plusOneFraction f := by linarith [hp_ge_half]
    have h1mp' : (numMinusOne : ℝ) / L = 1 - plusOneFraction f := by
      symm
      simpa [hM_eq] using h1mp
    have hpof' : (numPlusOne : ℝ) / L = plusOneFraction f := by
      symm
      simpa [hP_eq] using hpof
    linarith [h1, h1mp', hpof']
  have hmn : (numMinusOne : ℝ) ≤ (numPlusOne : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hmn_div (le_of_lt hL_pos)
    field_simp [hL_ne] at h
    exact h
  have hmn_nat : numMinusOne ≤ numPlusOne := by
    exact_mod_cast hmn
  simpa [numMinusOne, numPlusOne, f] using hmn_nat

theorem odd_high_dcMass_zero_count_bound_plus {L : ℕ} [NeZero L] (x : ℕ) (hx : Odd x)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hdcMass : dcMassPM (lsbProfile L x) ≥ 1 - ε)
    (hmean : profileMean (lsbProfile L x) ≥ 0) :
    ((Finset.univ.filter (fun j : Fin L => lsbProfile L x j = -1)).card : ℝ) ≤ (ε / 2) * L := by
  have hf : IsPMOne (lsbProfile L x) := lsbProfile_isPMOne L x
  let numPlusOne := (Finset.univ.filter (fun j : Fin L => lsbProfile L x j = 1)).card
  let numMinusOne := (Finset.univ.filter (fun j : Fin L => lsbProfile L x j = -1)).card
  have hham := high_dcMass_hamming_bound (lsbProfile L x) hf ε hε_pos hε_lt hdcMass
  have hham' :
      min (numPlusOne : ℝ) (numMinusOne : ℝ) ≤ (ε / 2) * L := by
    simpa [numPlusOne, numMinusOne] using hham
  have hmaj : numMinusOne ≤ numPlusOne := lsb_majority_ones_of_mean_nonneg x hmean
  have hmin : min (numPlusOne : ℝ) (numMinusOne : ℝ) = (numMinusOne : ℝ) := by
    apply min_eq_right
    exact_mod_cast hmaj
  simpa [numMinusOne, hmin] using hham'

/-- If the LSB mean is nonnegative, then +1s are at least as frequent as -1s. -/
theorem odd_high_dcMass_majority_ones {L : ℕ} [NeZero L] (x : ℕ)
    (hmean : profileMean (lsbProfile L x) ≥ 0) :
    (Finset.univ.filter (fun j : Fin L => lsbProfile L x j = -1)).card
      ≤ (Finset.univ.filter (fun j : Fin L => lsbProfile L x j = 1)).card := by
  exact lsb_majority_ones_of_mean_nonneg x hmean

/-- With mean bias to +1 and high LSB DC-mass, the number of 0-bits is at most (ε/2)·L. -/
theorem odd_high_dcMass_zero_count_bound {L : ℕ} [NeZero L] (x : ℕ) (hx : Odd x)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hdcMass : dcMassPM (lsbProfile L x) ≥ 1 - ε)
    (hmean : profileMean (lsbProfile L x) ≥ 0) :
    ((Finset.univ.filter (fun j : Fin L => lsbProfile L x j = -1)).card : ℝ) ≤ (ε / 2) * L := by
  exact odd_high_dcMass_zero_count_bound_plus x hx ε hε_pos hε_lt hdcMass hmean

/-!
## Section 7: Sharp v₂ Bound from Error Set

**KEY ARITHMETIC RESULT**: For R = Σ_{j∈E} 2^j with |E| = t:
  v₂(3R+2) ≤ 2t + 1

This bound is **sharp**: the extremal pattern E = {1, 3, 5, ..., 2t-1} achieves equality.

**Proof by induction on v** (the valuation we're bounding):

Base case (v=1): Trivial, bound is t ≥ 0.

Inductive step (v ≥ 2): Assume v₂(3R+2) ≥ v.
1. Look mod 4: 3R+2 ≡ -R+2 ≡ 0 (mod 4) forces R ≡ 2 (mod 4).
2. This means bit 1 is present: 1 ∈ E, and bit 0 is absent.
3. Write R = 2 + 4S where S has t-1 bits (E \ {1}, shifted).
4. Then 3R+2 = 8 + 12S = 4(2 + 3S), so v₂(3R+2) = 2 + v₂(3S+2).
5. By induction on S: t-1 ≥ ⌈(v-3)/2⌉.
6. Algebra: t ≥ 1 + ⌈(v-3)/2⌉ = ⌈(v-1)/2⌉, i.e., v ≤ 2t+1.

**Extremal pattern**: E_t = {1, 3, 5, ..., 2t-1} gives
  R_t = 2·(4^t - 1)/3, and 3R_t + 2 = 2^{2t+1}.

**Application to Collatz**: For odd x with t zeros in LSB window:
  v₂(3x+1) ≤ 2t + 2

Combined with spectral/Hamming bounds (t ≤ (ε/2)L):
  v₂(3x+1) ≤ εL + 2
-/

/-- The error set E for x with respect to L: positions j ∈ [0, L) where bit j of x is 0. -/
def errorSet (L : ℕ) (x : ℕ) : Finset (Fin L) :=
  Finset.univ.filter (fun j => x / 2^j.val % 2 = 0)

/-- The error residue R = Σ_{j ∈ E} 2^j. -/
def errorResidue (L : ℕ) (x : ℕ) : ℕ :=
  (errorSet L x).sum (fun j => 2^j.val)

/-- For odd x, position 0 is not in the error set. -/
lemma zero_not_in_errorSet (L : ℕ) [NeZero L] (x : ℕ) (hx : Odd x) :
    ⟨0, NeZero.pos L⟩ ∉ errorSet L x := by
  simp only [errorSet, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [pow_zero, Nat.div_one]
  rw [Nat.odd_iff] at hx
  omega

/-- Size of error set equals number of -1 entries in LSB profile. -/
lemma errorSet_card_eq_minusOne_count (L : ℕ) (x : ℕ) :
    (errorSet L x).card = (Finset.univ.filter (fun j : Fin L => lsbProfile L x j = -1)).card := by
  congr 1
  ext j
  simp only [errorSet, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [lsbProfile, bitToPM]
  split_ifs with h
  · -- h : x / 2^j.val % 2 = 1 → lsbProfile L x j = 1 ≠ -1
    constructor
    · intro h0; omega  -- 0 ≠ 1
    · intro h1; norm_num at h1  -- 1 ≠ -1
  · -- h : x / 2^j.val % 2 ≠ 1 → lsbProfile L x j = -1
    constructor
    · intro _; rfl
    · intro _
      have h2 : x / 2^j.val % 2 = 0 ∨ x / 2^j.val % 2 = 1 := Nat.mod_two_eq_zero_or_one _
      cases h2 with
      | inl h0 => exact h0
      | inr h1 => exact (h h1).elim

lemma errorSet_card_bound_inCdcPlus
    {L : ℕ} [NeZero L] (x : ℕ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hC : InCdcPlus L ε x) :
    ((errorSet L x).card : ℝ) ≤ (ε / 2) * L := by
  rcases hC with ⟨hx, hdcMass, hmean⟩
  have hcard :=
    odd_high_dcMass_zero_count_bound_plus x hx ε hε_pos hε_lt hdcMass hmean
  simpa [errorSet_card_eq_minusOne_count] using hcard

/-
**KEY LEMMA (SHARP)**: v_2(3R+2) <= 2t + 1 where t = |E| and R = sum of 2^j for j in E.
This bound is tight: the pattern E = {1, 3, 5, ..., 2t-1} achieves equality.
-/

/-- v₂(3R+2) ≥ 2 implies R ≡ 2 (mod 4). -/
lemma v2_ge_two_implies_R_mod_four (R : ℕ) (h : v2 (3 * R + 2) ≥ 2) : R % 4 = 2 := by
  -- v₂(3R+2) ≥ 2 means 4 | (3R+2)
  unfold v2 at h
  have h4 : 4 ∣ (3 * R + 2) := by
    have hne : 3 * R + 2 ≠ 0 := by omega
    have hdvd := (padicValNat_dvd_iff_le hne (n := 2) (p := 2)).mpr h
    simp only [pow_two] at hdvd
    exact hdvd
  -- 4 | (3R+2) means 3R+2 ≡ 0 (mod 4)
  -- 3R ≡ -R (mod 4), so 3R+2 ≡ -R+2 ≡ 0 (mod 4)
  -- Thus R ≡ 2 (mod 4)
  have : (3 * R + 2) % 4 = 0 := Nat.mod_eq_zero_of_dvd h4
  omega

/-- When R = Σ_{j∈E} 2^j and R ≡ 2 (mod 4), we have 1 ∈ E. -/
lemma one_mem_E_of_R_mod_four (E : Finset ℕ) (hR : E.sum (fun j => 2^j) % 4 = 2) : 1 ∈ E := by
  by_contra h1
  -- If 1 ∉ E, then either 0 ∈ E (making sum odd) or all j ≥ 2 (making sum ≡ 0 mod 4)
  -- Either contradicts R % 4 = 2
  by_cases h0 : 0 ∈ E
  · -- If 0 ∈ E, sum has 2^0 = 1, so it's odd
    have : E.sum (fun j => 2^j) % 2 = 1 := by
      have hsplit := Finset.sum_eq_sum_diff_singleton_add h0 (fun j => 2^j)
      simp only [pow_zero] at hsplit
      have hrest_even : (E \ {0}).sum (fun j => 2^j) % 2 = 0 := by
        refine Finset.sum_induction (fun j => 2^j) (fun x => x % 2 = 0) ?_ ?_ ?_
        · intro a b ha hb; omega
        · rfl
        · intro x hx
          simp only [Finset.mem_sdiff, Finset.mem_singleton] at hx
          have hx_pos : x ≠ 0 := hx.2
          have hx_ge1 : x ≥ 1 := Nat.one_le_iff_ne_zero.mpr hx_pos
          have : 2 ∣ 2^x := ⟨2^(x-1), by
            have : x = x - 1 + 1 := (Nat.sub_add_cancel hx_ge1).symm
            conv_lhs => rw [this, pow_succ]
            ring⟩
          exact Nat.mod_eq_zero_of_dvd this
      omega
    omega
  · -- If 0 ∉ E and 1 ∉ E, all j ≥ 2, so sum ≡ 0 (mod 4)
    have : E.sum (fun j => 2^j) % 4 = 0 := by
      refine Finset.sum_induction (fun j => 2^j) (fun x => x % 4 = 0) ?_ ?_ ?_
      · intro a b ha hb; omega
      · rfl
      · intro x hx
        have hx0 : x ≠ 0 := fun heq => h0 (heq ▸ hx)
        have hx1 : x ≠ 1 := fun heq => h1 (heq ▸ hx)
        have hx_ge2 : x ≥ 2 := by omega
        have : 4 ∣ 2^x := ⟨2^(x-2), by
          have : x = x - 2 + 2 := (Nat.sub_add_cancel hx_ge2).symm
          conv_lhs => rw [this, pow_add]
          ring⟩
        exact Nat.mod_eq_zero_of_dvd this
    omega

/-- When R = Σ_{j∈E} 2^j and R ≡ 2 (mod 4), we have 0 ∉ E. -/
lemma zero_not_mem_E_of_R_mod_four (E : Finset ℕ) (hR : E.sum (fun j => 2^j) % 4 = 2) : 0 ∉ E := by
  by_contra h0
  -- If 0 ∈ E, then R is odd (has 2^0 = 1 term), so R % 4 ∈ {1, 3}
  -- This contradicts R % 4 = 2
  have hR_odd : E.sum (fun j => 2^j) % 2 = 1 := by
    have hsplit := Finset.sum_eq_sum_diff_singleton_add h0 (fun j => 2^j)
    simp only [pow_zero] at hsplit
    have hrest_even : (E \ {0}).sum (fun j => 2^j) % 2 = 0 := by
      refine Finset.sum_induction (fun j => 2^j) (fun x => x % 2 = 0) ?_ ?_ ?_
      · intro a b ha hb; omega
      · rfl
      · intro x hx
        simp only [Finset.mem_sdiff, Finset.mem_singleton] at hx
        have hx_pos : x ≠ 0 := hx.2
        have hx_ge1 : x ≥ 1 := Nat.one_le_iff_ne_zero.mpr hx_pos
        have : 2 ∣ 2^x := ⟨2^(x-1), by
          have : x = x - 1 + 1 := (Nat.sub_add_cancel hx_ge1).symm
          conv_lhs => rw [this, pow_succ]
          ring⟩
        exact Nat.mod_eq_zero_of_dvd this
    omega
  omega

/-- The shifted set E' = {j - 2 : j ∈ E, j ≥ 2}. When E has 1 ∈ E, 0 ∉ E,
    we have |E'| = |E| - 1 and the shifted residue S satisfies R = 2 + 4S. -/
lemma shifted_set_properties (E : Finset ℕ) (h1 : 1 ∈ E) (h0 : 0 ∉ E)
    (R : ℕ) (hR : R = E.sum (fun j => 2^j)) :
    let E' := (E.filter (fun j => j ≥ 2)).image (fun j => j - 2)
    let S := E'.sum (fun k => 2^k)
    R = 2 + 4 * S ∧ E'.card = E.card - 1 := by
  intro E' S
  -- E = {1} ∪ {j ∈ E : j ≥ 2}
  have hE_split : E = insert 1 (E.filter (fun j => j ≥ 2)) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_filter]
    constructor
    · intro hx
      by_cases hx1 : x = 1
      · left; exact hx1
      · right; exact ⟨hx, by have : x ≠ 0 := fun h => h0 (h ▸ hx); omega⟩
    · intro hx
      cases hx with
      | inl h => rw [h]; exact h1
      | inr h => exact h.1
  have h1_not_in_filter : 1 ∉ E.filter (fun j => j ≥ 2) := by simp [Finset.mem_filter]
  constructor
  · -- R = 2 + 4S
    rw [hR, hE_split, Finset.sum_insert h1_not_in_filter]
    simp only [pow_one]
    have hsum_eq : (E.filter (fun j => j ≥ 2)).sum (fun j => 2^j) = 4 * S := by
      show _ = 4 * ((E.filter (fun j => j ≥ 2)).image (fun j => j - 2)).sum (fun k => 2^k)
      have hinj : ∀ x ∈ E.filter (fun j => j ≥ 2), ∀ y ∈ E.filter (fun j => j ≥ 2),
          x - 2 = y - 2 → x = y := by
        intro x hx y hy hxy
        simp only [Finset.mem_filter] at hx hy
        omega
      rw [Finset.sum_image hinj, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_filter] at hj
      have hj2 : j ≥ 2 := hj.2
      have : j = j - 2 + 2 := (Nat.sub_add_cancel hj2).symm
      conv_lhs => rw [this, pow_add]
      ring
    linarith
  · -- |E'| = |E| - 1
    show ((E.filter (fun j => j ≥ 2)).image (fun j => j - 2)).card = E.card - 1
    have hinj : Set.InjOn (fun j => j - 2) (E.filter (fun j => j ≥ 2)) := by
      intro x hx y hy hxy
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
      have hx2 : x ≥ 2 := hx.2
      have hy2 : y ≥ 2 := hy.2
      -- hxy : (fun j => j - 2) x = (fun j => j - 2) y, i.e., x - 2 = y - 2
      simp only at hxy
      -- x - 2 = y - 2 and x ≥ 2, y ≥ 2 implies x = y
      have : x - 2 + 2 = y - 2 + 2 := by rw [hxy]
      rw [Nat.sub_add_cancel hx2, Nat.sub_add_cancel hy2] at this
      exact this
    rw [Finset.card_image_of_injOn hinj]
    -- E = insert 1 (E.filter (fun j => j ≥ 2)), so |E| = 1 + |E.filter ...|
    have h_filter_card : (E.filter (fun j => j ≥ 2)).card + 1 = E.card := by
      have h1 := Finset.card_insert_of_not_mem h1_not_in_filter
      rw [← hE_split] at h1
      omega
    omega

/-- v₂(4 * (2 + 3S)) = 2 + v₂(3S + 2) for any S. -/
lemma v2_factor_four (S : ℕ) : v2 (4 * (2 + 3 * S)) = 2 + v2 (3 * S + 2) := by
  unfold v2
  have h4ne : (4 : ℕ) ≠ 0 := by omega
  have hS : 3 * S + 2 ≠ 0 := by omega
  have : 2 + 3 * S = 3 * S + 2 := by ring
  rw [this, padicValNat.mul h4ne hS]
  have h4 : padicValNat 2 4 = 2 := by
    have : (4 : ℕ) = 2^2 := by norm_num
    rw [this, padicValNat.prime_pow]
  rw [h4]

/-- The main v₂ bound statement for any t and any set E with |E| = t. -/
theorem v2_bound_from_residue_aux (t : ℕ) : ∀ E : Finset ℕ, E.card = t →
    v2 (3 * E.sum (fun j => 2^j) + 2) ≤ 2 * t + 1 := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro E hcard
    set R := E.sum (fun j => 2^j) with hR_def
    -- Handle the trivial case v₂(3R+2) ≤ 1
    by_cases h_small : v2 (3 * R + 2) ≤ 1
    · calc v2 (3 * R + 2) ≤ 1 := h_small
        _ ≤ 2 * t + 1 := by omega
    · -- v₂(3R+2) ≥ 2
      push_neg at h_small
      -- Step 1: R ≡ 2 (mod 4)
      have hRmod : R % 4 = 2 := v2_ge_two_implies_R_mod_four R h_small
      -- Step 2: 1 ∈ E and 0 ∉ E
      have h1 : 1 ∈ E := one_mem_E_of_R_mod_four E hRmod
      have h0 : 0 ∉ E := zero_not_mem_E_of_R_mod_four E hRmod
      -- E is nonempty since 1 ∈ E
      have ht_pos : t ≥ 1 := by rw [← hcard]; exact Finset.one_le_card.mpr ⟨1, h1⟩
      -- Step 3: Build E' and S
      set E' := (E.filter (fun j => j ≥ 2)).image (fun j => j - 2) with hE'_def
      set S := E'.sum (fun k => 2^k) with hS_def
      have ⟨hR_eq, hcard_eq⟩ := shifted_set_properties E h1 h0 R hR_def
      -- Step 4: v₂(3R+2) = 2 + v₂(3S+2)
      have hv2_eq : v2 (3 * R + 2) = 2 + v2 (3 * S + 2) := by
        calc v2 (3 * R + 2) = v2 (3 * (2 + 4 * S) + 2) := by rw [hR_eq]
          _ = v2 (8 + 12 * S) := by ring_nf
          _ = v2 (4 * (2 + 3 * S)) := by ring_nf
          _ = 2 + v2 (3 * S + 2) := v2_factor_four S
      -- Step 5: Apply IH to E' (cardinality t-1 < t)
      have hE'_card : E'.card = t - 1 := by rw [← hcard, hcard_eq]
      have hE'_card_lt : E'.card < t := by omega
      have hIH : v2 (3 * S + 2) ≤ 2 * (t - 1) + 1 := by
        have := ih E'.card hE'_card_lt E' rfl
        simp only [hE'_card] at this
        convert this using 2
      -- Combine
      calc v2 (3 * R + 2) = 2 + v2 (3 * S + 2) := hv2_eq
        _ ≤ 2 + (2 * (t - 1) + 1) := by linarith
        _ = 2 * t + 1 := by omega

theorem v2_bound_from_residue (E : Finset ℕ) :
    let R := E.sum (fun j => 2^j)
    let t := E.card
    v2 (3 * R + 2) ≤ 2 * t + 1 := by
  intro R t
  exact v2_bound_from_residue_aux t E rfl

/-- Express `ofDigits` as a finite sum over `getD`. -/
lemma ofDigits_eq_sum_getD (b : ℕ) (L : List ℕ) :
    Nat.ofDigits b L =
      Finset.sum (Finset.range L.length) (fun i => (L.getD i 0) * b^i) := by
  induction L with
  | nil =>
      simp
  | cons hd tl ih =>
      have hsum :
          Finset.sum (Finset.range (tl.length + 1))
              (fun i => (List.getD (hd :: tl) i 0) * b^i) =
            (List.getD (hd :: tl) 0 0) * b^0 +
              Finset.sum (Finset.range tl.length)
                (fun i => (List.getD (hd :: tl) (i + 1) 0) * b^(i+1)) := by
        simpa [add_comm] using
          (Finset.sum_range_succ' (f := fun i => (List.getD (hd :: tl) i 0) * b^i) tl.length)
      calc
        Nat.ofDigits b (hd :: tl) = hd + b * Nat.ofDigits b tl := rfl
        _ = hd + b * Finset.sum (Finset.range tl.length) (fun i => (tl.getD i 0) * b^i) := by
              simpa [ih]
        _ = hd + Finset.sum (Finset.range tl.length) (fun i => b * ((tl.getD i 0) * b^i)) := by
              simp [Finset.mul_sum]
        _ = hd + Finset.sum (Finset.range tl.length) (fun i => (tl.getD i 0) * b^(i+1)) := by
              refine congrArg (fun s => hd + s) ?_
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]
        _ = (List.getD (hd :: tl) 0 0) * b^0 +
            Finset.sum (Finset.range tl.length)
              (fun i => (List.getD (hd :: tl) (i + 1) 0) * b^(i+1)) := by
              simp
        _ = Finset.sum (Finset.range (tl.length + 1))
              (fun i => (List.getD (hd :: tl) i 0) * b^i) := by
              symm
              exact hsum

/-- For x < 2^L, the sum x + errorResidue equals 2^L - 1.
    This expresses that bits in [0,L) are partitioned into error positions and non-error.

    x contributes 2^j for bits where testBit x j = true
    errorResidue contributes 2^j for bits where testBit x j = false
    Together they sum to Σ_{j=0}^{L-1} 2^j = 2^L - 1 -/
lemma x_plus_errorResidue_eq (L : ℕ) [NeZero L] (x : ℕ) (hx_bound : x < 2^L) :
    x + errorResidue L x = 2^L - 1 := by
  unfold errorResidue errorSet
  simp only [Finset.sum_filter]
  have hL_pos : 0 < L := NeZero.pos L
  -- Key: Σ_{j : Fin L} 2^j = 2^L - 1 (geometric sum)
  have h_geom : ∑ j : Fin L, (2 : ℕ)^j.val = 2^L - 1 := by
    have hge2 : 2 ≤ 2 := le_refl 2
    have heq := Nat.geomSum_eq hge2 L
    -- (2^L - 1) / (2 - 1) = 2^L - 1
    simp only at heq
    rw [Nat.div_one] at heq
    rw [← heq, ← Fin.sum_univ_eq_sum_range (f := fun i => (2 : ℕ)^i)]
  -- Each position contributes either to x (bit=1) or errorResidue (bit=0), total = 2^j
  have h_partition : ∀ j : Fin L,
      (x / 2^j.val % 2) * 2^j.val + (if x / 2^j.val % 2 = 0 then 2^j.val else 0) = 2^j.val := by
    intro j
    by_cases hbit : x / 2^j.val % 2 = 0
    · simp [hbit]
    · have hmod : x / 2^j.val % 2 = 1 := by
        have h01 := Nat.mod_two_eq_zero_or_one (x / 2^j.val)
        cases h01 with
        | inl h0 => exact absurd h0 hbit
        | inr h1 => exact h1
      simp [hmod]
  -- Binary representation: x = Σ_{j < L} (x / 2^j % 2) * 2^j  for x < 2^L
  have h_binary : x = ∑ j : Fin L, (x / 2^j.val % 2) * 2^j.val := by
    set len := (Nat.digits 2 x).length with hlen_def
    have hb : (1 : ℕ) < 2 := by decide
    have hlen : len ≤ L := by
      have hlen' :=
        (Nat.digits_length_le_iff (b := 2) (k := L) (n := x) (hb := hb)).2 hx_bound
      simpa [hlen_def] using hlen'
    have hsum_digits :
        Nat.ofDigits 2 (Nat.digits 2 x) =
          Finset.sum (Finset.range len) (fun i => (x / 2^i % 2) * 2^i) := by
      calc
        Nat.ofDigits 2 (Nat.digits 2 x) =
            Finset.sum (Finset.range len) (fun i => (Nat.digits 2 x).getD i 0 * 2^i) := by
              simpa [hlen_def] using (ofDigits_eq_sum_getD 2 (Nat.digits 2 x))
        _ = Finset.sum (Finset.range len) (fun i => (x / 2^i % 2) * 2^i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hgi : (Nat.digits 2 x).getD i 0 = x / 2^i % 2 := by
                simpa using (Nat.getD_digits x i (b := 2) (by decide))
              rw [hgi]
    have hsum_range :
        Finset.sum (Finset.range len) (fun i => (x / 2^i % 2) * 2^i) =
          Finset.sum (Finset.range L) (fun i => (x / 2^i % 2) * 2^i) := by
      have hzero :
          Finset.sum (Finset.Ico len L) (fun i => (x / 2^i % 2) * 2^i) = 0 := by
        refine (Finset.sum_eq_zero_iff_of_nonneg ?_).2 ?_
        · intro i hi
          exact Nat.zero_le _
        · intro i hi
          have hi' : len ≤ i := (Finset.mem_Ico.mp hi).1
          have hxlt : x < 2^i := by
            exact (Nat.digits_length_le_iff (b := 2) (k := i) (n := x) (hb := hb)).1
              (by simpa [hlen_def] using hi')
          have hxdiv : x / 2^i = 0 := Nat.div_eq_of_lt hxlt
          simp [hxdiv]
      have hsplit :=
        Finset.sum_range_add_sum_Ico (f := fun i => (x / 2^i % 2) * 2^i) hlen
      have hsplit' :
          Finset.sum (Finset.range len) (fun i => (x / 2^i % 2) * 2^i) =
            Finset.sum (Finset.range L) (fun i => (x / 2^i % 2) * 2^i) := by
        simpa [hzero] using hsplit
      exact hsplit'
    have hx_digits : x = Nat.ofDigits 2 (Nat.digits 2 x) := by
      simpa using (Nat.ofDigits_digits 2 x).symm
    calc
      x = Nat.ofDigits 2 (Nat.digits 2 x) := hx_digits
      _ = Finset.sum (Finset.range len) (fun i => (x / 2^i % 2) * 2^i) := hsum_digits
      _ = Finset.sum (Finset.range L) (fun i => (x / 2^i % 2) * 2^i) := hsum_range
      _ = ∑ j : Fin L, (x / 2^j.val % 2) * 2^j.val := by
        simpa using
          (Fin.sum_univ_eq_sum_range
              (n := L) (f := fun i : ℕ => (x / 2^i % 2) * 2^i)).symm
  -- Now combine using h_partition
  have h_sum_partition : ∑ j : Fin L, 2^j.val =
      ∑ j : Fin L, ((x / 2^j.val % 2) * 2^j.val + (if x / 2^j.val % 2 = 0 then 2^j.val else 0)) := by
    apply Finset.sum_congr rfl
    intro j _
    exact (h_partition j).symm
  rw [← h_geom, h_sum_partition, Finset.sum_add_distrib]
  -- Goal: x + ∑ (if ...) = ∑ (x/2^j%2)*2^j + ∑ (if ...)
  rw [← h_binary]

/-- v₂(2^L·a - b) = v₂(b) when a is odd, v₂(b) < L, and b < 2^L·a.
    This is the ultrametric property: v(x - y) = min(v(x), v(y)) when v(x) ≠ v(y). -/
lemma v2_pow_sub_eq (L : ℕ) (a b : ℕ) (ha_odd : Odd a) (hb_pos : 0 < b)
    (hv : v2 b < L) (hlt : b < 2^L * a) :
    v2 (2^L * a - b) = v2 b := by
  unfold v2
  have hp : Nat.Prime 2 := Nat.prime_two
  haveI : Fact (Nat.Prime 2) := ⟨hp⟩
  -- 2^L * a has v₂ = L (since a is odd)
  have ha_pos : 0 < a := Odd.pos ha_odd
  have h2L_pos : 0 < 2^L := pow_pos (by omega : 0 < 2) L
  have ha_val : padicValNat 2 (2^L * a) = L := by
    rw [padicValNat.mul h2L_pos.ne' ha_pos.ne']
    rw [padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd]
    · omega
    · exact ha_odd.not_two_dvd_nat
  -- v₂(m - n) = v₂(n) when v₂(m) > v₂(n) and m > n (ultrametric)
  -- Non-zero hypotheses for padicValNat_eq_emultiplicity
  have hb_ne : b ≠ 0 := hb_pos.ne'
  have hsub_ne : 2^L * a - b ≠ 0 := Nat.sub_ne_zero_of_lt hlt
  have h2La_ne : 2^L * a ≠ 0 := (Nat.mul_pos h2L_pos ha_pos).ne'
  -- Use Nat.cast_injective to lift the goal to ℕ∞
  apply Nat.cast_injective (R := ℕ∞)
  -- Now the goal is (padicValNat 2 (2^L * a - b) : ℕ∞) = (padicValNat 2 b : ℕ∞)
  -- Convert padicValNat to emultiplicity
  rw [padicValNat_eq_emultiplicity hsub_ne, padicValNat_eq_emultiplicity hb_ne]
  -- Cast to ℤ using Int.natCast_emultiplicity
  rw [← Int.natCast_emultiplicity 2 (2^L * a - b), ← Int.natCast_emultiplicity 2 b]
  -- The subtraction in ℕ equals subtraction in ℤ since 2^L * a > b
  have h_sub_cast : ((2^L * a - b : ℕ) : ℤ) = ((2^L * a : ℕ) : ℤ) - ((b : ℕ) : ℤ) := by
    exact Int.ofNat_sub (le_of_lt hlt)
  rw [h_sub_cast]
  -- Apply ultrametric property: emultiplicity_sub_of_gt
  apply emultiplicity_sub_of_gt
  -- Need: emultiplicity ↑2 ↑b < emultiplicity ↑2 ↑(2^L * a) in ℤ
  -- First convert from ℤ back to ℕ using Int.natCast_emultiplicity
  rw [Int.natCast_emultiplicity, Int.natCast_emultiplicity]
  -- Now goal is emultiplicity 2 b < emultiplicity 2 (2^L * a) in ℕ
  -- Convert to padicValNat
  rw [← padicValNat_eq_emultiplicity hb_ne, ← padicValNat_eq_emultiplicity h2La_ne]
  rw [ha_val]
  exact_mod_cast hv

/-- For odd x with error set E, v₂(3x+1) ≤ 2|E| + 2.

    This uses the fact that for x < 2^L with error set E:
    x ≡ (2^L - 1) - R (mod 2^L) where R = Σ_{j∈E} 2^j.
    Then 3x+1 ≡ 3·2^L - (3R+2) (mod higher powers),
    and v₂(3x+1) = v₂(3R+2) as long as v₂(3R+2) < L.

    Note: The bound is 2|E| + 2 (not 2|E| + 1) due to edge cases where
    v₂(3R+2) ≥ L. E.g., L=3, x=5: error set {1}, v₂(16)=4 > 2·1+1=3.
    These edge cases only occur when t ≥ (L-1)/2 (many errors). -/
theorem v2_bound_from_errorSet (L : ℕ) [NeZero L] (x : ℕ) (hx : Odd x)
    (hx_pos : 0 < x)
    (hx_bound : x < 2^L) :
    v2 (3 * x + 1) ≤ 2 * (errorSet L x).card + 2 := by
  -- Get R = errorResidue L x
  set R := errorResidue L x with hR_def
  set t := (errorSet L x).card with ht_def
  -- From x_plus_errorResidue_eq: x + R = 2^L - 1, so x = 2^L - 1 - R
  have hxR : x = 2^L - 1 - R := by
    have h := x_plus_errorResidue_eq L x hx_bound
    omega
  -- Therefore: 3x + 1 = 3(2^L - 1 - R) + 1 = 3·2^L - 3 - 3R + 1 = 3·2^L - (3R + 2)
  have h3x1 : 3 * x + 1 = 3 * 2^L - (3 * R + 2) := by
    have hL_pos : 0 < L := NeZero.pos L
    have h2L : 2^L ≥ 1 := Nat.one_le_pow _ _ (by norm_num)
    -- Need 2^L > R to ensure 2^L - 1 - R ≥ 0
    have hR_bound : R ≤ 2^L - 1 := by
      have h := x_plus_errorResidue_eq L x hx_bound
      omega
    have hR_bound2 : R < 2^L := by omega
    -- 3·2^L > 3R + 2
    have h3 : 3 * 2^L > 3 * R + 2 := by nlinarith
    -- Expand 3 * (2^L - 1 - R) + 1 = 3*2^L - (3R + 2)
    have hcalc : 3 * (2^L - 1 - R) + 1 = 3 * 2^L - (3 * R + 2) := by
      have hpos : 2^L ≥ 1 + R := by omega
      omega
    rw [hxR, hcalc]
  -- Now use v2_bound_from_residue on R
  -- The errorResidue uses Fin L indices, need to convert to ℕ indices
  -- errorResidue L x = (errorSet L x).sum (fun j => 2^j.val)
  -- We need a Finset ℕ version for v2_bound_from_residue
  -- Map errorSet L x to a Finset ℕ
  set E_nat := (errorSet L x).image (fun j : Fin L => j.val) with hE_nat_def
  have hR_eq : R = E_nat.sum (fun j => 2^j) := by
    show errorResidue L x = ((errorSet L x).image (fun j : Fin L => j.val)).sum (fun j => 2^j)
    unfold errorResidue
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact Fin.val_injective hab
  have ht_eq : t = E_nat.card := by
    show (errorSet L x).card = ((errorSet L x).image (fun j : Fin L => j.val)).card
    rw [Finset.card_image_of_injective]
    exact Fin.val_injective
  -- From v2_bound_from_residue: v₂(3R + 2) ≤ 2t + 1
  have hv2R := v2_bound_from_residue E_nat
  simp only at hv2R
  rw [← hR_eq, ← ht_eq] at hv2R
  -- Now show v₂(3x + 1) = v₂(3R + 2) (when v₂(3R+2) < L)
  -- For simplicity, we'll show the bound directly
  by_cases hsmall : v2 (3 * R + 2) < L
  · -- Case: v₂(3R + 2) < L
    have h3R2_pos : 0 < 3 * R + 2 := by omega
    have h3_odd : Odd 3 := by decide
    -- R < 2^L so 3R + 2 < 3·2^L = 2^L · 3
    have hR_bound' : R < 2^L := by
      have h := x_plus_errorResidue_eq L x hx_bound
      omega
    have h3R2_lt : 3 * R + 2 < 2^L * 3 := by nlinarith
    -- Rewrite 3 * 2^L as 2^L * 3 for the lemma
    have h_comm : 3 * 2^L = 2^L * 3 := Nat.mul_comm _ _
    rw [h3x1, h_comm, v2_pow_sub_eq L 3 (3 * R + 2) h3_odd h3R2_pos hsmall h3R2_lt]
    -- hv2R gives ≤ 2t+1, we need ≤ 2t+2
    omega
  · -- Case: v₂(3R + 2) ≥ L
    -- Structural analysis: 2^L | (3R+2), so 3R+2 = 2^L · k for some k ≥ 1
    -- Since R < 2^L, we have 3R+2 < 3·2^L, so k ∈ {1, 2}
    -- Then 3x+1 = 3·2^L - 2^L·k = 2^L·(3-k)
    -- k=1 ⟹ v₂(3x+1) = L+1, k=2 ⟹ v₂(3x+1) = L
    -- Also: L ≤ v₂(3R+2) ≤ 2t+1, so L ≤ 2t+1
    push_neg at hsmall
    have hL_bound : L ≤ 2 * t + 1 := by omega
    -- Use structural argument: v₂(3x+1) ≤ L + 1
    have h3x1_pos : 0 < 3 * x + 1 := by omega
    have hv2_struct : v2 (3 * x + 1) ≤ L + 1 := by
      -- 3x+1 = 3·2^L - (3R+2) where 2^L | (3R+2)
      -- Let k = (3R+2) / 2^L, then 3x+1 = 2^L · (3 - k)
      -- Since R < 2^L and R ≥ 0: 2 ≤ 3R+2 ≤ 3·2^L - 1, so k ∈ {1, 2}
      -- k=1: 3x+1 = 2^(L+1), v₂ = L+1
      -- k=2: 3x+1 = 2^L, v₂ = L
      have hR_bound : R < 2^L := by
        have h := x_plus_errorResidue_eq L x hx_bound
        omega
      have h3R2_bound : 3 * R + 2 < 3 * 2^L := by omega
      have h3R2_pos : 0 < 3 * R + 2 := by omega
      -- In both cases, v₂(3x+1) ≤ L + 1
      have h_div : (2^L : ℕ) ∣ (3 * R + 2) := by
        unfold v2 at hsmall
        have h3R2_ne : 3 * R + 2 ≠ 0 := by omega
        exact (padicValNat_dvd_iff_le h3R2_ne).mpr hsmall
      obtain ⟨k, hk⟩ := h_div
      -- k < 3 since 3R+2 < 3·2^L
      have hk_bound : k < 3 := by
        have : 3 * R + 2 < 3 * 2^L := h3R2_bound
        rw [hk] at this
        have h2L_pos : 0 < 2^L := pow_pos (by omega : 0 < 2) L
        -- 2^L * k < 3 * 2^L with 0 < 2^L implies k < 3
        have : k * 2^L < 3 * 2^L := by rw [mul_comm] at this; exact this
        exact (Nat.mul_lt_mul_right h2L_pos).mp this
      have hk_pos : 0 < k := by
        by_contra hk0
        push_neg at hk0
        have h2L_pos : 0 < 2^L := pow_pos (by omega : 0 < 2) L
        have hkle : k = 0 := Nat.le_zero.mp hk0
        have : 3 * R + 2 = 0 := by rw [hk, hkle]; simp
        omega
      -- So k ∈ {1, 2}
      have hk_cases : k = 1 ∨ k = 2 := by omega
      -- In both cases, directly compute v₂(3x+1)
      cases hk_cases with
      | inl h1 =>
        -- k = 1: 3R+2 = 2^L, so 3x+1 = 3·2^L - 2^L = 2·2^L = 2^(L+1)
        subst h1
        have h3x1_val : 3 * x + 1 = 2^(L+1) := by
          rw [h3x1, hk]
          have h2L_pos : 0 < 2^L := pow_pos (by omega : 0 < 2) L
          have heq1 : 3 * 2^L - 2^L * 1 = 2 * 2^L := by omega
          have heq2 : 2 * 2^L = 2^(L+1) := by rw [pow_succ]; ring
          omega
        rw [h3x1_val]
        unfold v2
        rw [padicValNat.prime_pow]
      | inr h2 =>
        -- k = 2: 3R+2 = 2·2^L, so 3x+1 = 3·2^L - 2·2^L = 2^L
        subst h2
        have h3x1_val : 3 * x + 1 = 2^L := by
          rw [h3x1, hk]
          have h2L_pos : 0 < 2^L := pow_pos (by omega : 0 < 2) L
          omega
        rw [h3x1_val]
        unfold v2
        rw [padicValNat.prime_pow]
        omega
    -- Now combine: v₂(3x+1) ≤ L+1 and L ≤ 2t+1
    -- Therefore v₂(3x+1) ≤ L+1 ≤ 2t+2 ✓
    omega

/-- **COMBINED BOUND**: For x in InCdcPlus,
    v2(3x+1) ≤ εL + 2.

    Proof chain:
    1. dcMass ≥ 1-ε and mean ≥ 0 ⟹ number of -1s ≤ (ε/2)L
    2. v2(3x+1) ≤ 2|E| + 2
    3. Combine to get εL + 2

    Note: Bound is εL + 2 (not εL + 1) due to edge cases in v2_bound_from_errorSet. -/
theorem v2_bound_from_dcMass_plus {L : ℕ} [NeZero L] (x : ℕ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hx_pos : 0 < x) (hx_bound : x < 2^L)
    (hC : InCdcPlus L ε x) :
    (v2 (3 * x + 1) : ℝ) ≤ ε * L + 2 := by
  have h1 := v2_bound_from_errorSet L x hC.1 hx_pos hx_bound
  have h2 := errorSet_card_bound_inCdcPlus x ε hε_pos hε_lt hC
  have h1' : (v2 (3 * x + 1) : ℝ) ≤ 2 * (errorSet L x).card + 2 := by
    exact_mod_cast h1
  calc (v2 (3 * x + 1) : ℝ)
      ≤ 2 * (errorSet L x).card + 2 := h1'
    _ ≤ 2 * ((ε / 2) * L) + 2 := by linarith
    _ = ε * L + 2 := by ring

/-!
## Section 8: qMax, tMaxSharp, and nuMax
-/

/-- The sharp minority bound qMax(ε) = (1 - sqrt(1-ε)) / 2. -/
noncomputable def qMax (ε : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - ε)) / 2

/-- Exact Hamming bound using qMax. -/
theorem high_dcMass_hamming_bound_exact {L : ℕ} [NeZero L] (f : Fin L → ℝ) (hf : IsPMOne f)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hdcMass : dcMassPM f ≥ 1 - ε) :
    let numPlusOne := (Finset.univ.filter (fun j => f j = 1)).card
    let numMinusOne := (Finset.univ.filter (fun j => f j = -1)).card
    min (numPlusOne : ℝ) (numMinusOne : ℝ) ≤ qMax ε * L := by
  intro numPlusOne numMinusOne
  have hL_pos : (0 : ℝ) < L := Nat.cast_pos.mpr (NeZero.pos L)
  have hL_ne : (L : ℝ) ≠ 0 := ne_of_gt hL_pos
  have hq := high_dcMass_exact_minority_bound f hf ε hε_pos hε_lt hdcMass
  have hq' : minorityFraction f * L ≤ qMax ε * L := by
    simpa [qMax] using mul_le_mul_of_nonneg_right hq (le_of_lt hL_pos)
  have hmin := minorityFraction_eq_min_count_div_L f hf
  have hmin' : minorityFraction f = min (numPlusOne : ℝ) (numMinusOne : ℝ) / L := by
    simpa [numPlusOne, numMinusOne] using hmin
  have hmin'' : minorityFraction f * L = min (numPlusOne : ℝ) (numMinusOne : ℝ) := by
    calc minorityFraction f * L
        = (min (numPlusOne : ℝ) (numMinusOne : ℝ) / L) * L := by simpa [hmin']
      _ = min (numPlusOne : ℝ) (numMinusOne : ℝ) := by
          field_simp [hL_ne]
  calc min (numPlusOne : ℝ) (numMinusOne : ℝ)
      = minorityFraction f * L := hmin''.symm
    _ ≤ qMax ε * L := hq'

/-- Maximum zero count in L-window for dcMass ≥ 1-ε. -/
noncomputable def tMaxSharp (L : ℕ) (ε : ℝ) : ℕ :=
  Nat.floor (qMax ε * L)

/-- Maximum single-step Collatz exponent for DC-pure states. -/
noncomputable def nuMax (L : ℕ) (ε : ℝ) : ℕ :=
  2 * tMaxSharp L ε + 2

lemma errorSet_card_le_tMaxSharp
    {L : ℕ} [NeZero L] (x : ℕ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hC : InCdcPlus L ε x) :
    (errorSet L x).card ≤ tMaxSharp L ε := by
  have hf : IsPMOne (lsbProfile L x) := lsbProfile_isPMOne L x
  let numPlusOne := (Finset.univ.filter (fun j : Fin L => lsbProfile L x j = 1)).card
  let numMinusOne := (Finset.univ.filter (fun j : Fin L => lsbProfile L x j = -1)).card
  have hham :=
    high_dcMass_hamming_bound_exact (lsbProfile L x) hf ε hε_pos hε_lt hC.2.1
  have hham' :
      min (numPlusOne : ℝ) (numMinusOne : ℝ) ≤ qMax ε * L := by
    simpa [numPlusOne, numMinusOne] using hham
  have hmaj : numMinusOne ≤ numPlusOne := lsb_majority_ones_of_mean_nonneg x hC.2.2
  have hmin : min (numPlusOne : ℝ) (numMinusOne : ℝ) = (numMinusOne : ℝ) := by
    apply min_eq_right
    exact_mod_cast hmaj
  have hcard_real : (numMinusOne : ℝ) ≤ qMax ε * L := by
    simpa [hmin] using hham'
  have hcard_real' : ((errorSet L x).card : ℝ) ≤ qMax ε * L := by
    simpa [numMinusOne, errorSet_card_eq_minusOne_count] using hcard_real
  have hq_nonneg : 0 ≤ qMax ε * L := by
    have hsqrt_le : Real.sqrt (1 - ε) ≤ 1 := by
      have : 1 - ε ≤ 1 := by linarith
      simpa using (Real.sqrt_le_sqrt this)
    have hq_nonneg : 0 ≤ qMax ε := by
      unfold qMax
      linarith
    exact mul_nonneg hq_nonneg (Nat.cast_nonneg _)
  exact (Nat.le_floor_iff hq_nonneg).2 hcard_real'

theorem nu_bounded_in_CdcPlus {L : ℕ} [NeZero L] (x : ℕ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hx_pos : 0 < x) (hx_bound : x < 2^L)
    (hC : InCdcPlus L ε x) :
    v2 (3 * x + 1) ≤ nuMax L ε := by
  have h1 := v2_bound_from_errorSet L x hC.1 hx_pos hx_bound
  have hE := errorSet_card_le_tMaxSharp x ε hε_pos hε_lt hC
  have hE' : 2 * (errorSet L x).card ≤ 2 * tMaxSharp L ε := by
    exact Nat.mul_le_mul_left 2 hE
  have hE'' : 2 * (errorSet L x).card + 2 ≤ 2 * tMaxSharp L ε + 2 := by
    exact Nat.add_le_add_right hE' 2
  have hbound : v2 (3 * x + 1) ≤ 2 * tMaxSharp L ε + 2 := le_trans h1 hE''
  simpa [nuMax] using hbound

/-!
## Block-Level Finite Set S_dc(L,ε,B)

This section records the original block/orbit notions for completeness.
-/

/-- C_dc(L,ε): Odd integers with DC-pure LSB profile, mean bias to +1, and x < 2^L. -/
def InCdc (L : ℕ) [NeZero L] (ε : ℝ) (x : ℕ) : Prop :=
  InCdcPlus L ε x ∧ x < 2^L

/-- For x ∈ C_dc(L,ε), the Collatz exponent is bounded by ν_max. -/
theorem nu_bounded_in_Cdc {L : ℕ} [NeZero L] (x : ℕ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hCdc : InCdc L ε x) :
    v2 (3 * x + 1) ≤ nuMax L ε := by
  have hx_pos : 0 < x := Odd.pos hCdc.1.1
  have hx_bound : x < 2^L := hCdc.2
  exact nu_bounded_in_CdcPlus x ε hε_pos hε_lt hx_pos hx_bound hCdc.1

/-- **FINITENESS THEOREM**: The single-step exponent range for DC-pure states is finite. -/
theorem single_step_exponent_finite (L : ℕ) [NeZero L] (ε : ℝ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ∀ x, InCdc L ε x →
      v2 (3 * x + 1) ∈ Finset.range (nuMax L ε + 1) := by
  intro x hCdc
  have hbound := nu_bounded_in_Cdc x ε hε_pos hε_lt hCdc
  simp only [Finset.mem_range]
  omega

/-- A ν-block is DC-realizable if there exists an orbit in C_dc producing it. -/
def IsDcRealizableBlock (L : ℕ) [NeZero L] (ε : ℝ) (block : List ℕ) : Prop :=
  ∃ x₀ : ℕ, Odd x₀ ∧ 0 < x₀ ∧
    ∀ k (hk : k < block.length),
      let xₖ := orbit_raw x₀ k
      InCdc L ε xₖ ∧ block.get ⟨k, hk⟩ = v2 (3 * xₖ + 1)

/-- **BLOCK-LEVEL FINITENESS**: S_dc(L,ε,B) is finite. -/
theorem Sdc_finite_crude_bound (L : ℕ) [NeZero L] (ε : ℝ) (B : ℕ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ∀ block : List ℕ, block.length = B →
      IsDcRealizableBlock L ε block →
      ∀ ν ∈ block, ν ≤ nuMax L ε := by
  intro block hlen hreal ν hν_mem
  rcases hreal with ⟨x₀, hx₀_odd, hx₀_pos, hprop⟩
  rcases (List.mem_iff_getElem.mp hν_mem) with ⟨k, hk, hget⟩
  have hprop' := hprop k hk
  rcases hprop' with ⟨hCdc, hval⟩
  have hν : ν = v2 (3 * orbit_raw x₀ k + 1) := by
    simpa [hget] using hval
  have hbound := nu_bounded_in_Cdc (x := orbit_raw x₀ k) ε hε_pos hε_lt hCdc
  simpa [hν] using hbound

/-!
## MSB Profiles and Mantissa Band

High MSB DC-mass constrains the mantissa band; kept for completeness.
-/

/-- The MSB profile of x for window length L. -/
def msbProfile (L : ℕ) (x : ℕ) : Fin L → ℝ :=
  if x = 0 then fun _ => -1
  else
    let K := Nat.log2 x
    fun j => if (x / 2^(K - j.val)) % 2 = 1 then 1 else -1

/-- MSB profile is ±1 valued. -/
lemma msbProfile_isPMOne (L : ℕ) (x : ℕ) : IsPMOne (msbProfile L x) := by
  intro j
  unfold msbProfile
  by_cases hx : x = 0
  · simp only [hx, ↓reduceIte]
    right; trivial
  · simp only [hx, ↓reduceIte]
    by_cases hbit : (x / 2^(Nat.log2 x - j.val)) % 2 = 1
    · left
      simp only [hbit, ↓reduceIte]
    · right
      have h0 : (x / 2^(Nat.log2 x - j.val)) % 2 = 0 := by
        have := Nat.mod_two_eq_zero_or_one (x / 2^(Nat.log2 x - j.val))
        omega
      simp only [h0, zero_ne_one, ↓reduceIte]

/-- For x > 0, the MSB (position K = ⌊log₂ x⌋) is always 1. -/
lemma msbProfile_zero_pos (L : ℕ) [NeZero L] (x : ℕ) (hx : 0 < x) :
    msbProfile L x ⟨0, NeZero.pos L⟩ = 1 := by
  unfold msbProfile
  have hx_ne : x ≠ 0 := Nat.pos_iff_ne_zero.mp hx
  simp only [hx_ne, ↓reduceIte, Nat.sub_zero]
  have hle : 2^(Nat.log2 x) ≤ x := by
    rw [Nat.log2_eq_log_two]
    exact Nat.pow_log_le_self 2 hx_ne
  have hlt : x < 2^(Nat.log2 x + 1) := by
    rw [Nat.log2_eq_log_two, ← Nat.succ_eq_add_one]
    exact Nat.lt_pow_succ_log_self Nat.one_lt_two x
  have h : x / 2^(Nat.log2 x) = 1 := by
    apply Nat.div_eq_of_lt_le
    · calc 1 * 2^(Nat.log2 x) = 2^(Nat.log2 x) := by ring
        _ ≤ x := hle
    · calc x < 2^(Nat.log2 x + 1) := hlt
        _ = 2 * 2^(Nat.log2 x) := by ring
        _ = (1 + 1) * 2^(Nat.log2 x) := by ring
  simp only [h, Nat.one_mod, ↓reduceIte]

/-- DC-mass of MSB profile for x > 0 with high DC-mass bounds the mantissa. -/
theorem msb_high_dcMass_mantissa_band {L : ℕ} [NeZero L] (x : ℕ) (hx : 0 < x)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (hdcMass : dcMassPM (msbProfile L x) ≥ 1 - ε) :
    minorityFraction (msbProfile L x) ≤ (1 - Real.sqrt (1 - ε)) / 2 := by
  exact high_dcMass_exact_minority_bound (msbProfile L x) (msbProfile_isPMOne L x) ε hε_pos hε_lt hdcMass

/-- Combined LSB+MSB constraint creates a "tiny arithmetic slice". -/
theorem combined_lsb_msb_constraint {L : ℕ} [NeZero L] (x : ℕ) (hx : Odd x) (hx_pos : 0 < x)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (h_lsb : dcMassPM (lsbProfile L x) ≥ 1 - ε)
    (h_msb : dcMassPM (msbProfile L x) ≥ 1 - ε) :
    minorityFraction (lsbProfile L x) ≤ qMax ε ∧
    minorityFraction (msbProfile L x) ≤ qMax ε := by
  constructor
  · exact high_dcMass_exact_minority_bound (lsbProfile L x) (lsbProfile_isPMOne L x) ε hε_pos hε_lt h_lsb
  · exact high_dcMass_exact_minority_bound (msbProfile L x) (msbProfile_isPMOne L x) ε hε_pos hε_lt h_msb

/-!
## Summary

- dcMassPM f = (profileMean f)^2 = (1 - 2q)^2 for minority fraction q
- High dcMass gives q ≤ (1 - sqrt(1-ε)) / 2 and the simple q ≤ ε / 2 bound
- For InCdcPlus, -1 entries in the LSB profile are at most (ε / 2) * L
- For odd x < 2^L, v2(3x+1) ≤ 2 * |E| + 2 with E = errorSet L x
- For InCdcPlus, v2(3x+1) ≤ ε * L + 2, and also ≤ nuMax L ε
- qMax, tMaxSharp, nuMax provide a nat-sized bound without orbit/block structure
-/

end Collatz
