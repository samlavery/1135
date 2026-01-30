/-
Copyright (c) 2024. All rights reserved.
Released under MIT license.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Finset
open scoped BigOperators

namespace Collatz.CycleLemma

/-!
## Cycle Lemma (ANT Random Walk Lemma)

This file proves the cycle lemma: for a finite integer sequence with total sum 0,
there exists a rotation whose prefix sums are all nonnegative.

This is a fundamental result in combinatorics, related to the ballot problem.

### Main Results

* `cycle_lemma_nat`: For d : ℕ → ℤ with ∑_{i < k} d i = 0, there exists j0 < k
  such that ∀ ℓ ≤ k, ∑_{i < ℓ} d ((j0 + i) % k) ≥ 0

* `cycle_lemma_fin`: The same result for d : Fin k → ℤ

* `nonneg_sum_zero_implies_all_zero`: If all elements are nonnegative and sum to 0, all are 0.
-/

section PartialSums

/-- Partial sum of d from 0 to j-1. P 0 = 0, P j = ∑ i < j, d i -/
def partialSum (d : ℕ → ℤ) (j : ℕ) : ℤ :=
  ∑ i ∈ range j, d i

lemma partialSum_zero (d : ℕ → ℤ) : partialSum d 0 = 0 := by
  simp [partialSum]

lemma partialSum_succ (d : ℕ → ℤ) (j : ℕ) :
    partialSum d (j + 1) = partialSum d j + d j := by
  simp [partialSum, sum_range_succ]

/-- Telescoping: d j = P(j+1) - P(j) -/
lemma d_eq_partialSum_diff (d : ℕ → ℤ) (j : ℕ) :
    d j = partialSum d (j + 1) - partialSum d j := by
  simp [partialSum, sum_range_succ]

/-- Partial sum difference via strong induction on the difference -/
lemma partialSum_diff_eq_sum (d : ℕ → ℤ) (a b : ℕ) (hab : a ≤ b) :
    partialSum d b - partialSum d a = ∑ i ∈ range (b - a), d (a + i) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction c with
  | zero => simp
  | succ c ih =>
    simp only [Nat.add_sub_cancel_left] at ih ⊢
    rw [Nat.add_succ, partialSum_succ]
    calc partialSum d (a + c) + d (a + c) - partialSum d a
        = (partialSum d (a + c) - partialSum d a) + d (a + c) := by ring
      _ = (∑ i ∈ range c, d (a + i)) + d (a + c) := by rw [ih]
      _ = ∑ i ∈ range (c + 1), d (a + i) := by rw [sum_range_succ]

end PartialSums

section MinimumFinding

/-- The minimum partial sum exists over range (k+1) for k > 0 -/
lemma exists_min_partialSum (d : ℕ → ℤ) (k : ℕ) (_hk : 0 < k) :
    ∃ j0 ∈ range (k + 1), ∀ m ∈ range (k + 1), partialSum d j0 ≤ partialSum d m := by
  have h_nonempty : (range (k + 1)).Nonempty := ⟨0, mem_range.mpr (Nat.succ_pos k)⟩
  exact Finset.exists_min_image (range (k + 1)) (partialSum d) h_nonempty

end MinimumFinding

section RotatedSum

/-- Rotated sum: Q_ℓ = ∑_{i < ℓ} d((j0 + i) % k) -/
def rotatedSum (d : ℕ → ℤ) (k j0 : ℕ) (ℓ : ℕ) : ℤ :=
  ∑ i ∈ range ℓ, d ((j0 + i) % k)

lemma rotatedSum_zero (d : ℕ → ℤ) (k j0 : ℕ) : rotatedSum d k j0 0 = 0 := by
  simp [rotatedSum]

lemma rotatedSum_succ (d : ℕ → ℤ) (k j0 ℓ : ℕ) :
    rotatedSum d k j0 (ℓ + 1) = rotatedSum d k j0 ℓ + d ((j0 + ℓ) % k) := by
  simp [rotatedSum, sum_range_succ]

end RotatedSum

section NoWrapCase

/-- No-wrap case: when j0 + ℓ ≤ k, the rotation is just a shift -/
lemma rotatedSum_no_wrap (d : ℕ → ℤ) (k j0 ℓ : ℕ) (_hk : 0 < k)
    (h_no_wrap : j0 + ℓ ≤ k) :
    rotatedSum d k j0 ℓ = partialSum d (j0 + ℓ) - partialSum d j0 := by
  unfold rotatedSum
  -- When j0 + i < k, (j0 + i) % k = j0 + i
  have h_reindex : ∑ i ∈ range ℓ, d ((j0 + i) % k) = ∑ i ∈ range ℓ, d (j0 + i) := by
    apply sum_congr rfl
    intro i hi
    have hi_lt : i < ℓ := mem_range.mp hi
    have h_sum_lt : j0 + i < k := by omega
    simp [Nat.mod_eq_of_lt h_sum_lt]
  rw [h_reindex]
  -- Now use partialSum_diff_eq_sum
  have h_le : j0 ≤ j0 + ℓ := Nat.le_add_right j0 ℓ
  rw [partialSum_diff_eq_sum d j0 (j0 + ℓ) h_le]
  simp only [Nat.add_sub_cancel_left]

end NoWrapCase

section WrapCase

/-- Wrap case: when j0 + ℓ > k, express in terms of partial sums -/
lemma rotatedSum_wrap (d : ℕ → ℤ) (k j0 ℓ : ℕ) (hk : 0 < k)
    (hj0 : j0 < k) (hℓ : ℓ ≤ k) (h_wrap : j0 + ℓ > k)
    (h_sum_zero : ∑ i ∈ range k, d i = 0) :
    rotatedSum d k j0 ℓ = partialSum d ((j0 + ℓ) % k) - partialSum d j0 + partialSum d k := by
  -- Key facts
  have h_Pk : partialSum d k = 0 := by simp [partialSum, h_sum_zero]
  have h_mod_val : (j0 + ℓ) % k = j0 + ℓ - k := by
    have h_ge : j0 + ℓ ≥ k := by omega
    have h_lt : j0 + ℓ < 2 * k := by omega
    rw [Nat.mod_eq_sub_mod h_ge]
    rw [Nat.mod_eq_of_lt (by omega : j0 + ℓ - k < k)]

  -- The cut point where wrapping starts
  set cut := k - j0 with h_cut_def
  have h_cut_pos : 0 < cut := by omega
  have h_cut_le : cut ≤ ℓ := by omega

  unfold rotatedSum

  -- Key insight: split the sum at the wrap point
  have h_ℓ_eq : ℓ = cut + (ℓ - cut) := by omega

  -- Rewrite the sum by splitting at cut
  calc ∑ i ∈ range ℓ, d ((j0 + i) % k)
      = ∑ i ∈ range cut, d ((j0 + i) % k) +
        ∑ i ∈ range (ℓ - cut), d ((j0 + (cut + i)) % k) := by
          conv_lhs => rw [h_ℓ_eq]
          rw [sum_range_add]
    _ = ∑ i ∈ range cut, d (j0 + i) +
        ∑ i ∈ range (ℓ - cut), d i := by
          congr 1
          · -- No wrap part: (j0 + i) % k = j0 + i for i < cut
            apply sum_congr rfl
            intro i hi
            have hi_lt : i < cut := mem_range.mp hi
            have h_no_wrap : j0 + i < k := by omega
            simp [Nat.mod_eq_of_lt h_no_wrap]
          · -- Wrap part: (j0 + cut + i) % k = i for i < ℓ - cut
            apply sum_congr rfl
            intro i hi
            have hi_lt : i < ℓ - cut := mem_range.mp hi
            -- j0 + cut + i = j0 + (k - j0) + i = k + i
            have h_idx : j0 + (cut + i) = k + i := by omega
            rw [h_idx]
            -- (k + i) % k = i since i < ℓ - cut ≤ ℓ ≤ k, so i < k
            have h_i_lt_k : i < k := by omega
            simp [Nat.mod_eq_of_lt h_i_lt_k]
    _ = (partialSum d k - partialSum d j0) + partialSum d (ℓ - cut) := by
          -- First sum: ∑ i < cut, d(j0 + i) = P(k) - P(j0)
          have h_le : j0 ≤ k := le_of_lt hj0
          have h_eq1 : ∑ i ∈ range cut, d (j0 + i) = partialSum d k - partialSum d j0 := by
            rw [partialSum_diff_eq_sum d j0 k h_le]
            -- cut = k - j0, so this is just reflexivity
          rw [h_eq1]
          -- Second part: ∑ i < (ℓ - cut), d i = partialSum d (ℓ - cut) by definition
          rfl
    _ = partialSum d ((j0 + ℓ) % k) - partialSum d j0 + partialSum d k := by
          -- ℓ - cut = ℓ - (k - j0) = j0 + ℓ - k = (j0 + ℓ) % k
          have h_eq : ℓ - cut = (j0 + ℓ) % k := by
            rw [h_mod_val]
            omega
          rw [h_eq]
          ring

end WrapCase

section MainLemma

/-- **Cycle Lemma (Nat version)**: For any sequence d : ℕ → ℤ with ∑_{i<k} d i = 0,
    there exists a starting point j0 < k such that all prefix sums of the
    rotated sequence are nonnegative. -/
theorem cycle_lemma_nat {k : ℕ} (hk : 0 < k) (d : ℕ → ℤ)
    (h_sum_zero : ∑ i ∈ range k, d i = 0) :
    ∃ j0 < k, ∀ ℓ ≤ k, 0 ≤ rotatedSum d k j0 ℓ := by
  -- Find the index j0 with minimum partial sum P(j0)
  obtain ⟨j0, hj0_mem, hj0_min⟩ := exists_min_partialSum d k hk
  have hj0_lt : j0 < k + 1 := mem_range.mp hj0_mem
  have hj0_le : j0 ≤ k := Nat.lt_succ_iff.mp hj0_lt

  -- Key facts about partial sums
  have h_P0 : partialSum d 0 = 0 := partialSum_zero d
  have h_Pk : partialSum d k = 0 := by simp [partialSum, h_sum_zero]

  -- If j0 = k, use j0 = 0 instead (since P(0) = P(k) = 0, both are minimal)
  by_cases hj0_eq_k : j0 = k
  · -- j0 = k case: use j0 = 0
    use 0
    constructor
    · exact hk
    · intro ℓ hℓ
      by_cases hℓ_eq : ℓ = 0
      · simp [hℓ_eq, rotatedSum_zero]
      · have hℓ_pos : 0 < ℓ := Nat.pos_of_ne_zero hℓ_eq
        -- For j0 = 0: rotatedSum d k 0 ℓ = P(ℓ) (since no wrap when 0 + ℓ ≤ k)
        rw [rotatedSum_no_wrap d k 0 ℓ hk (by omega : 0 + ℓ ≤ k)]
        simp only [zero_add, partialSum_zero, sub_zero]
        -- P(ℓ) ≥ P(k) = 0 by minimality
        have hℓ_mem : ℓ ∈ range (k + 1) := mem_range.mpr (by omega)
        have h_min := hj0_min ℓ hℓ_mem
        subst hj0_eq_k
        rw [h_Pk] at h_min
        exact h_min
  · -- j0 < k case
    have hj0_strict : j0 < k := by omega
    use j0
    constructor
    · exact hj0_strict
    · intro ℓ hℓ
      by_cases hℓ_eq : ℓ = 0
      · simp [hℓ_eq, rotatedSum_zero]
      · have hℓ_pos : 0 < ℓ := Nat.pos_of_ne_zero hℓ_eq
        by_cases h_no_wrap : j0 + ℓ ≤ k
        · -- No wrap case
          rw [rotatedSum_no_wrap d k j0 ℓ hk h_no_wrap]
          -- Need: P(j0 + ℓ) - P(j0) ≥ 0, i.e., P(j0 + ℓ) ≥ P(j0)
          have h_mem : j0 + ℓ ∈ range (k + 1) := mem_range.mpr (by omega)
          have h_min := hj0_min (j0 + ℓ) h_mem
          linarith
        · -- Wrap case
          have h_wrap : j0 + ℓ > k := by omega
          rw [rotatedSum_wrap d k j0 ℓ hk hj0_strict hℓ h_wrap h_sum_zero]
          rw [h_Pk, add_zero]
          -- Need: P((j0+ℓ) % k) ≥ P(j0)
          have h_mod_lt : (j0 + ℓ) % k < k := Nat.mod_lt (j0 + ℓ) hk
          have h_mem : (j0 + ℓ) % k ∈ range (k + 1) := mem_range.mpr (by omega)
          have h_min := hj0_min ((j0 + ℓ) % k) h_mem
          linarith

end MainLemma

section FinWrapper

/-- Convert Fin k → ℤ to ℕ → ℤ, extending by 0 outside [0, k) -/
def finToNat {k : ℕ} (d : Fin k → ℤ) : ℕ → ℤ :=
  fun n => if h : n < k then d ⟨n, h⟩ else 0

lemma finToNat_eq {k : ℕ} (d : Fin k → ℤ) (i : Fin k) :
    finToNat d i.val = d i := by
  simp [finToNat, i.is_lt]

lemma sum_finToNat_eq {k : ℕ} (_hk : 0 < k) (d : Fin k → ℤ) :
    ∑ i ∈ range k, finToNat d i = ∑ i : Fin k, d i := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i _
  simp [finToNat, i.is_lt]

/-- **Cycle Lemma (Fin version)**: For any d : Fin k → ℤ with ∑ d = 0,
    there exists j0 : Fin k such that all prefix sums of the rotated sequence
    are nonnegative. -/
theorem cycle_lemma_fin {k : ℕ} (hk : 0 < k) (d : Fin k → ℤ)
    (h_sum_zero : ∑ i : Fin k, d i = 0) :
    ∃ j0 : Fin k, ∀ ℓ ≤ k, 0 ≤ ∑ i ∈ range ℓ, d ⟨(j0.val + i) % k, Nat.mod_lt _ hk⟩ := by
  -- Convert to nat version
  let d' := finToNat d
  have h_sum_zero' : ∑ i ∈ range k, d' i = 0 := by
    rw [sum_finToNat_eq hk, h_sum_zero]
  -- Apply nat version
  obtain ⟨j0_nat, hj0_lt, hj0_rot⟩ := cycle_lemma_nat hk d' h_sum_zero'
  -- Package result
  use ⟨j0_nat, hj0_lt⟩
  intro ℓ hℓ
  have h_eq : ∑ i ∈ range ℓ, d ⟨(j0_nat + i) % k, Nat.mod_lt _ hk⟩ =
              rotatedSum d' k j0_nat ℓ := by
    unfold rotatedSum
    apply sum_congr rfl
    intro i _
    have h_mod_lt : (j0_nat + i) % k < k := Nat.mod_lt _ hk
    show d ⟨(j0_nat + i) % k, _⟩ = finToNat d ((j0_nat + i) % k)
    unfold finToNat
    rw [dif_pos h_mod_lt]
  rw [h_eq]
  exact hj0_rot ℓ hℓ

end FinWrapper

section RigidityLemma

/-- **Simple Rigidity**: If all elements are nonnegative and sum to 0, all are 0.

    This is the second key piece of the ANT random-walk argument:
    once we have a closed walk (sum = 0) with all steps nonnegative,
    the only possibility is that all steps are zero. -/
theorem nonneg_sum_zero_implies_all_zero {k : ℕ} (d : Fin k → ℤ)
    (h_sum_zero : ∑ i : Fin k, d i = 0)
    (h_all_nonneg : ∀ i : Fin k, d i ≥ 0) :
    ∀ i : Fin k, d i = 0 := by
  intro i
  by_contra h_not_zero
  have h_pos : d i > 0 := by
    have := h_all_nonneg i
    omega
  have h_sum_pos : ∑ j : Fin k, d j > 0 := by
    have h_split : ∑ j : Fin k, d j = d i + ∑ j ∈ (univ : Finset (Fin k)).erase i, d j := by
      have := Finset.add_sum_erase univ (fun j => d j) (Finset.mem_univ i)
      linarith
    rw [h_split]
    have h_rest_nonneg : 0 ≤ ∑ j ∈ (univ : Finset (Fin k)).erase i, d j := by
      apply Finset.sum_nonneg
      intro j _
      exact h_all_nonneg j
    linarith
  linarith

/-- **Rotation Rigidity**: For closed walks with nonnegative elements, all are 0.

    This directly applies the simple rigidity - the rotation provided by
    cycle_lemma_fin is not needed when we already know all elements are nonneg. -/
theorem rotation_rigidity {k : ℕ} (_hk : 0 < k) (d : Fin k → ℤ)
    (h_sum_zero : ∑ i : Fin k, d i = 0)
    (h_all_nonneg : ∀ i : Fin k, d i ≥ 0) :
    ∀ i : Fin k, d i = 0 :=
  nonneg_sum_zero_implies_all_zero d h_sum_zero h_all_nonneg

end RigidityLemma

end Collatz.CycleLemma
