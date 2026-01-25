/-
Copyright (c) 2024. All rights reserved.
Released under MIT license.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Spectral Potential Infrastructure

This file provides the generic spectral layer + the "bounded δ-increase on a (sub)sequence
is impossible" helper. This is a key component of the no-divergence proof.

## Main Definitions

- `Profile L`: Real-valued profile on a length-L window
- `powSpec`: Power spectrum at frequency k
- `totalEnergy`: Total spectral energy
- `dcMass`: DC-mass (fraction of energy at k=0)

## Main Results

- `dcMass_bounds`: DC-mass is always in [0, 1]
- `bounded_strict_increase_subseq`: Bounded, strictly δ-increasing subsequence is impossible

This last lemma is the key for showing that DC-mass cannot drift by δ infinitely often
on a bounded quantity.
-/

namespace Collatz

open scoped BigOperators
open Finset

/-- A real-valued profile on a length-L window. -/
abbrev Profile (L : ℕ) := Fin L → ℝ

/-- DFT interface. The actual implementation will be plugged in via SpectralSetup.
    Here we define a placeholder for type-checking purposes. -/
noncomputable def dftPlaceholder {L : ℕ} (_f : Profile L) : Fin L → ℂ :=
  fun _k => 0

/-- Power spectrum at frequency k: |DFT(f)(k)|^2.
    Uses the placeholder DFT - actual implementation via SpectralSetup.dft -/
noncomputable def powSpecOf {L : ℕ} (dft : Profile L → Fin L → ℂ) (f : Profile L) (k : Fin L) : ℝ :=
  ‖dft f k‖ ^ (2 : ℕ)

/-- Total spectral energy: Σ_k |DFT(f)(k)|^2. -/
noncomputable def totalEnergyOf {L : ℕ} (dft : Profile L → Fin L → ℂ) (f : Profile L) : ℝ :=
  ∑ k : Fin L, powSpecOf dft f k

lemma powSpecOf_nonneg {L : ℕ} (dft : Profile L → Fin L → ℂ) (f : Profile L) (k : Fin L) :
    0 ≤ powSpecOf dft f k := by
  unfold powSpecOf
  exact pow_nonneg (norm_nonneg _) _

lemma totalEnergyOf_nonneg {L : ℕ} (dft : Profile L → Fin L → ℂ) (f : Profile L) :
    0 ≤ totalEnergyOf dft f := by
  classical
  unfold totalEnergyOf
  refine sum_nonneg ?_
  intro k _
  exact powSpecOf_nonneg dft f k

lemma powSpecOf_le_totalEnergyOf {L : ℕ} (dft : Profile L → Fin L → ℂ) (f : Profile L) (k : Fin L) :
    powSpecOf dft f k ≤ totalEnergyOf dft f := by
  classical
  unfold totalEnergyOf
  have hk : k ∈ (Finset.univ : Finset (Fin L)) := by simp
  have := single_le_sum (fun j _ => powSpecOf_nonneg dft f j) hk
  simpa using this

/-- DC-mass: fraction of spectral energy sitting at k=0.
    Defined with a safe `if` so it is total even if totalEnergy = 0. -/
noncomputable def dcMassOf {L : ℕ} [NeZero L] (dft : Profile L → Fin L → ℂ) (f : Profile L) : ℝ :=
  if h : totalEnergyOf dft f = 0 then 0
  else (powSpecOf dft f ⟨0, NeZero.pos L⟩) / (totalEnergyOf dft f)

lemma dcMassOf_bounds_of_pos {L : ℕ} [NeZero L] (dft : Profile L → Fin L → ℂ) (f : Profile L)
    (hE : 0 < totalEnergyOf dft f) :
    0 ≤ dcMassOf dft f ∧ dcMassOf dft f ≤ 1 := by
  have hE0 : totalEnergyOf dft f ≠ 0 := ne_of_gt hE
  unfold dcMassOf
  simp only [hE0, dite_false]
  constructor
  · apply div_nonneg
    · exact powSpecOf_nonneg dft f ⟨0, NeZero.pos L⟩
    · exact le_of_lt hE
  · have hle : powSpecOf dft f ⟨0, NeZero.pos L⟩ ≤ totalEnergyOf dft f :=
      powSpecOf_le_totalEnergyOf dft f ⟨0, NeZero.pos L⟩
    have hdiv : (powSpecOf dft f ⟨0, NeZero.pos L⟩) / (totalEnergyOf dft f)
            ≤ (totalEnergyOf dft f) / (totalEnergyOf dft f) :=
      div_le_div_of_nonneg_right hle (le_of_lt hE)
    simpa [div_self (ne_of_gt hE)] using hdiv

/-- Always: 0 ≤ dcMass ≤ 1 (trivial if totalEnergy=0, else use lemma above). -/
lemma dcMassOf_bounds {L : ℕ} [NeZero L] (dft : Profile L → Fin L → ℂ) (f : Profile L) :
    0 ≤ dcMassOf dft f ∧ dcMassOf dft f ≤ 1 := by
  by_cases hE : totalEnergyOf dft f = 0
  · unfold dcMassOf
    simp [hE]
  · have hEpos : 0 < totalEnergyOf dft f :=
      lt_of_le_of_ne (totalEnergyOf_nonneg dft f) (Ne.symm hE)
    exact dcMassOf_bounds_of_pos dft f hEpos

/-!
## Bounded Strict Increase Subsequence Impossibility

This is the key lemma for the spectral proof: if a bounded sequence has a strictly
monotonically increasing subsequence (by at least δ each step), we get a contradiction.

We apply this to:
  a i = dcMass(profile(blockOrbit n B (k i)))

where k is a strictly increasing subsequence of block indices.
-/

/-- Bounded, strictly-δ-increasing subsequence is impossible.

    If a : ℕ → ℝ is bounded in [0, 1] and there exists:
    - A strictly monotone subsequence k : ℕ → ℕ
    - With a(k(i+1)) ≥ a(k(i)) + δ for some δ > 0

    Then we get a contradiction (the sequence would eventually exceed 1). -/
lemma bounded_strict_increase_subseq
    {a : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (h0 : ∀ n, 0 ≤ a n) (h1 : ∀ n, a n ≤ 1)
    (k : ℕ → ℕ) (_hk_strict : StrictMono k)
    (hstep : ∀ i, a (k (i+1)) ≥ a (k i) + δ) :
    False := by
  -- linear lower bound on subsequence
  have hlin : ∀ n : ℕ, a (k n) ≥ a (k 0) + (n : ℝ) * δ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hstep_n := hstep n
      -- a(k (n+1)) ≥ a(k n) + δ ≥ (a(k0) + nδ) + δ
      calc a (k (n + 1)) ≥ a (k n) + δ := hstep_n
        _ ≥ (a (k 0) + (n : ℝ) * δ) + δ := by linarith
        _ = a (k 0) + (↑(n + 1) : ℝ) * δ := by push_cast; ring

  -- choose N so that a(k0) + N * δ > 1
  have hgt : ∃ N : ℕ, a (k 0) + (N : ℝ) * δ > 1 := by
    -- choose N > (1 - a(k0))/δ
    have hexists := exists_nat_gt ((1 - a (k 0)) / δ)
    rcases hexists with ⟨N, hN⟩
    have hN_cast : (N : ℝ) > (1 - a (k 0)) / δ := by exact_mod_cast hN
    have hmul : (N : ℝ) * δ > 1 - a (k 0) := by
      have := mul_lt_mul_of_pos_right hN_cast hδ
      simp only [div_mul_cancel₀ _ (ne_of_gt hδ)] at this
      exact this
    refine ⟨N, ?_⟩
    linarith

  rcases hgt with ⟨N, hN⟩
  have hN' : a (k N) > 1 := by
    have := hlin N
    linarith
  have hbound : a (k N) ≤ 1 := h1 _
  exact (lt_irrefl _ (lt_of_lt_of_le hN' hbound))

/-- Contrapositive form: If we have bounded, monotone values and infinitely many δ-increases,
    we get a contradiction. The monotonicity is essential - without it, the sequence could
    oscillate and have infinitely many δ-jumps while staying bounded.

    With monotonicity: each δ-jump accumulates permanently, so after 1/δ jumps we exceed 1. -/
lemma infinitely_many_increases_impossible
    {a : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (h0 : ∀ n, 0 ≤ a n) (h1 : ∀ n, a n ≤ 1)
    (h_mono : Monotone a) :
    ¬ (∀ k₀ : ℕ, ∃ k ≥ k₀, a (k + 1) ≥ a k + δ) := by
  intro hinf
  -- The key observation: if a is monotone and bounded by 1, the total increase
  -- from a(0) to any a(n) is at most 1. Each δ-jump contributes at least δ,
  -- so there can be at most ⌊1/δ⌋ + 1 such jumps.
  -- Get M such that M * δ > 1
  have hM_exists : ∃ M : ℕ, (M : ℝ) * δ > 1 := by
    have h := exists_nat_gt (1 / δ)
    obtain ⟨M, hM⟩ := h
    use M
    have hM_cast : (M : ℝ) > 1 / δ := by exact_mod_cast hM
    calc (M : ℝ) * δ > (1 / δ) * δ := mul_lt_mul_of_pos_right hM_cast hδ
      _ = 1 := by field_simp
  obtain ⟨M, hM⟩ := hM_exists
  -- Build M+1 distinct jump points using hinf
  -- Start from 0, repeatedly apply hinf
  have h_accum : ∀ m : ℕ, ∃ k : ℕ, a k ≥ m * δ := by
    intro m
    induction m with
    | zero =>
      use 0
      simp [h0]
    | succ m ih =>
      obtain ⟨k_prev, hk_prev⟩ := ih
      -- Get a jump point at or after k_prev
      obtain ⟨k_jump, hk_ge, hk_delta⟩ := hinf k_prev
      -- a(k_jump + 1) ≥ a(k_jump) + δ
      -- By monotonicity: a(k_jump) ≥ a(k_prev) ≥ m*δ
      -- So a(k_jump + 1) ≥ m*δ + δ = (m+1)*δ
      use k_jump + 1
      have h1' : a k_jump ≥ a k_prev := h_mono hk_ge
      calc a (k_jump + 1) ≥ a k_jump + δ := hk_delta
        _ ≥ a k_prev + δ := by linarith
        _ ≥ m * δ + δ := by linarith
        _ = (m + 1 : ℕ) * δ := by push_cast; ring
  -- Apply to M+1: get k such that a(k) ≥ (M+1)*δ > 1
  obtain ⟨k, hk⟩ := h_accum (M + 1)
  have hgt : a k > 1 := by
    calc a k ≥ (M + 1 : ℕ) * δ := hk
      _ = (M : ℝ) * δ + δ := by push_cast; ring
      _ > 1 + 0 := by linarith
      _ = 1 := by ring
  -- Contradiction with h1
  have hle := h1 k
  linarith

end Collatz
