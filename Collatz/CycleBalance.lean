/-
Copyright (c) 2024. All rights reserved.
Released under MIT license.

# Balance Analysis for Cycle Profiles

## Two Cases

**Case 1: Critical-line cycles (ν ∈ {1, 2})**
- From cycle equation: mean ν ≈ log₂(3) ≈ 1.585
- FW concentrated on residues 1 and 2 (mod q for q ≥ 3)
- balance = FW(1)·ζ + FW(2)·ζ² ≠ 0 since |FW(1)/FW(2)| ≈ 0.71 ≠ 1
- See DirectCycleVariance.lean

**Case 2: Uniform FW (hypothetical spread-out profiles)**
- If sumSqDev < 2 and q | ΣFW → FW is uniform
- Uniform FW → balance = 0

The key insight: actual cycles from the cycle equation are Case 1,
which have balance ≠ 0, violating the cyclotomic constraint.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Collatz.RootsOfUnitySum
import Collatz.CloseSpectral

namespace CycleBalance

open scoped BigOperators Real
open Finset Complex

/-! ## Definitions -/

noncomputable def ζ (q : ℕ) : ℂ := exp (2 * π * I / q)

noncomputable def balance (q : ℕ) (FW : Fin q → ℕ) : ℂ :=
  ∑ j : Fin q, (FW j : ℂ) * ζ q ^ j.val

def sumSqDev (q : ℕ) (FW : Fin q → ℕ) (μ : ℕ) : ℕ :=
  ∑ j : Fin q, (Int.natAbs ((FW j : ℤ) - μ))^2

/-! ## Step 1: Roots of Unity Sum to Zero -/

theorem roots_sum_zero (q : ℕ) (hq : q ≥ 2) : ∑ j : Fin q, ζ q ^ j.val = 0 := by
  have h : ζ q = RootsOfUnity.ζ q := rfl
  simp only [h]
  exact RootsOfUnity.roots_sum_zero q hq

/-! ## Step 2: Uniform Weights Give Zero Balance -/

theorem uniform_zero (q : ℕ) (hq : q ≥ 2) (c : ℕ) : balance q (fun _ => c) = 0 := by
  simp only [balance, mul_comm (c : ℂ), ← sum_mul, roots_sum_zero q hq, zero_mul]

/-! ## Step 3: Integer Forcing Lemma -/

/-- If sumSqDev < 2 and q | ΣFW, then all FW(j) equal the mean.

Key insight: If any FW(j) ≠ μ, the sum-zero constraint forces another
FW(k) ≠ μ, giving sumSqDev ≥ 1 + 1 = 2. -/
theorem forcing (q : ℕ) (hq : q ≥ 2) (FW : Fin q → ℕ)
    (hdiv : q ∣ ∑ j, FW j) (hvar : sumSqDev q FW ((∑ j, FW j) / q) < 2) :
    ∀ j, FW j = (∑ i, FW i) / q := by
  set W := ∑ j, FW j
  set μ := W / q

  have hWqμ : W = q * μ := Nat.eq_mul_of_div_eq_right hdiv rfl
  have hsum : ∑ j : Fin q, ((FW j : ℤ) - μ) = 0 := by
    rw [sum_sub_distrib, sum_const, card_fin, nsmul_eq_mul]
    have hWcast : (∑ j, (FW j : ℤ)) = (q : ℤ) * μ := by
      have : (W : ℤ) = (q : ℤ) * μ := by exact_mod_cast hWqμ
      convert this using 1
      exact (Nat.cast_sum _ _).symm
    rw [hWcast]; ring

  intro j
  by_contra hne

  have hj : (Int.natAbs ((FW j : ℤ) - μ))^2 ≥ 1 := by
    have hne' : (FW j : ℤ) - μ ≠ 0 := by
      intro h
      have : (FW j : ℤ) = μ := sub_eq_zero.mp h
      have : FW j = μ := Int.ofNat_inj.mp this
      exact hne this
    have hpos := Int.natAbs_pos.mpr hne'
    nlinarith

  obtain ⟨k, hkj, hk⟩ : ∃ k, k ≠ j ∧ (Int.natAbs ((FW k : ℤ) - μ))^2 ≥ 1 := by
    by_contra hall
    push_neg at hall
    have hall' : ∀ i, i ≠ j → (FW i : ℤ) - μ = 0 := fun i hi => by
      have := hall i hi
      have habs : Int.natAbs ((FW i : ℤ) - μ) = 0 := by nlinarith
      exact Int.natAbs_eq_zero.mp habs
    have heq : ∑ i : Fin q, ((FW i : ℤ) - μ) = (FW j : ℤ) - μ := by
      rw [← add_sum_erase _ _ (mem_univ j)]
      have hrest : ∑ i ∈ erase univ j, ((FW i : ℤ) - ↑μ) = 0 :=
        sum_eq_zero fun i hi => hall' i (ne_of_mem_erase hi)
      simp [hrest]
    rw [heq] at hsum
    have : FW j = μ := Int.ofNat_inj.mp (sub_eq_zero.mp hsum)
    exact hne this

  have hge2 : sumSqDev q FW μ ≥ 2 := by
    unfold sumSqDev
    let f : Fin q → ℕ := fun i => (Int.natAbs ((FW i : ℤ) - μ))^2
    have hsplit : ∑ i, f i = f j + ∑ i ∈ erase univ j, f i :=
      (add_sum_erase (univ : Finset (Fin q)) f (mem_univ j)).symm
    have hk_mem : k ∈ erase univ j := mem_erase.mpr ⟨hkj, mem_univ k⟩
    have hk_le : f k ≤ ∑ i ∈ erase univ j, f i :=
      single_le_sum (fun _ _ => Nat.zero_le _) hk_mem
    calc ∑ i, f i = f j + ∑ i ∈ erase univ j, f i := hsplit
      _ ≥ 1 + f k := Nat.add_le_add hj hk_le
      _ ≥ 1 + 1 := Nat.add_le_add_left hk 1
      _ = 2 := rfl

  exact Nat.not_lt.mpr hge2 hvar

/-! ## Balance Zero for Uniform Profiles -/

/-- If FW is uniform (all entries equal), balance = 0. -/
theorem balance_zero_of_uniform (q : ℕ) (hq : q ≥ 2) (FW : Fin q → ℕ)
    (hunif : ∀ j, FW j = FW ⟨0, by omega⟩) :
    balance q FW = 0 := by
  have h : FW = fun _ => FW ⟨0, by omega⟩ := funext hunif
  rw [h]
  exact uniform_zero q hq _

/-! ## Critical Line Balance (Non-Zero)

For critical-line cycles where FW is concentrated on residues 1 and 2,
balance = FW(1)·ζ + FW(2)·ζ² which is non-zero when |FW(1)/FW(2)| ≠ 1.

The cycle equation forces FW(1)/FW(2) ≈ 0.415/0.585 ≈ 0.71 ≠ 1,
so balance ≠ 0 for all critical-line cycles.

This is the content of DirectCycleVariance.lean. -/

end CycleBalance
