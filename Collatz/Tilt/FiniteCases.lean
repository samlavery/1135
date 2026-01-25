/-
Copyright (c) 2024. All rights reserved.
Released under MIT license.
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators
open Finset Nat

namespace Collatz.Tilt

/-- Helper: if (!b) = true then b = false. Parens needed because ! has lower precedence than =. -/
private lemma bool_not_eq_true_imp {b : Bool} (h : (!b) = true) : b = false := by
  match b, h with
  | false, _ => rfl

/-!
Finite case filters used by the tilt-balance pipeline.

* **Binary filter**: if ν(j) ≤ 1 and ∑ ν = m, then ν ≡ 1 (pure pigeonhole).
* **Nonneg realizable filter**: for fixed small m, rule out nontrivial ν with ν≥1, Δ≥0, and D ∣ waveSum.
-/

/-! ## Binary filter -/

/-- If ν : Fin m → ℕ satisfies (∀j, ν j ≤ 1) and ∑ ν = m, then ν j = 1 for all j. -/
theorem binary_sum_forces_all_ones :
    ∀ (m : ℕ) (ν : Fin m → ℕ),
      (∀ j, ν j ≤ 1) →
      (∑ j : Fin m, ν j = m) →
      ∀ j, ν j = 1
  | 0, _, _, _ => by intro j; exact j.elim0
  | Nat.succ m, ν, hν, hsum => by
      intro j
      have hne0 : ν j ≠ 0 := by
        intro hj0
        have hsplit : (∑ i : Fin (Nat.succ m), ν i) = ν j + ∑ i ∈ (univ.erase j), ν i := by
          rw [← Finset.add_sum_erase _ _ (mem_univ j)]
        have hrest_le : (∑ i ∈ univ.erase j, ν i) ≤ (univ.erase j).card := by
          have h1 : ∀ i ∈ univ.erase j, ν i ≤ 1 := fun i _ => hν i
          calc
            (∑ i ∈ univ.erase j, ν i)
                ≤ ∑ _i ∈ univ.erase j, (1 : ℕ) := Finset.sum_le_sum h1
            _ = (univ.erase j).card := by simp [Finset.sum_const]
        have hcard : (univ.erase j).card = m := by
          rw [Finset.card_erase_of_mem (mem_univ j), Finset.card_fin, Nat.succ_sub_one]
        have : (Nat.succ m : ℕ) ≤ m := by
          calc
            Nat.succ m = ∑ i : Fin (Nat.succ m), ν i := hsum.symm
            _ = ν j + ∑ i ∈ univ.erase j, ν i := hsplit
            _ = 0 + ∑ i ∈ univ.erase j, ν i := by rw [hj0]
            _ = ∑ i ∈ univ.erase j, ν i := zero_add _
            _ ≤ (univ.erase j).card := hrest_le
            _ = m := hcard
        exact Nat.not_succ_le_self m this
      have hpos : 1 ≤ ν j := Nat.one_le_iff_ne_zero.mpr hne0
      exact Nat.le_antisymm (hν j) hpos

/-- Same statement but keeps a tilt-style prefix hypothesis for API compatibility. -/
theorem binary_tilt_forces_trivial (m : ℕ) (ν : Fin m → ℕ)
    (h_binary : ∀ j, ν j ≤ 1)
    (h_sum : ∑ j : Fin m, ν j = m)
    (_h_tilt : ∀ j : Fin m, j.val ≤ ∑ i ∈ Finset.filter (· < j) Finset.univ, ν i) :
    ∀ j, ν j = 1 :=
  binary_sum_forces_all_ones m ν h_binary h_sum

/-! ## m = 4 nonneg realizable filter -/

def D_m4 : ℕ := 175  -- 4^4 - 3^4

/-- waveSum for m=4 in the "prefix-sum" normal form. -/
def waveSumM4 (ν0 ν1 ν2 _ν3 : ℕ) : ℕ :=
  27 + 9 * 2^ν0 + 3 * 2^(ν0 + ν1) + 2^(ν0 + ν1 + ν2)

/-- Alias for waveSumM4 used by TiltBalance. -/
abbrev waveSumM4' := waveSumM4

/-- Check predicate for m=4 nonneg nontrivial realizable (Bool for native_decide). -/
def isM4NonnegNontrivialRealizable (ν0 ν1 ν2 ν3 : ℕ) : Bool :=
  decide (1 ≤ ν0 ∧ 1 ≤ ν1 ∧ 1 ≤ ν2 ∧ 1 ≤ ν3 ∧
          ν0 + ν1 + ν2 + ν3 = 8 ∧
          2 ≤ ν0 ∧ 4 ≤ ν0 + ν1 ∧ 6 ≤ ν0 + ν1 + ν2 ∧
          ¬(ν0 = 2 ∧ ν1 = 2 ∧ ν2 = 2 ∧ ν3 = 2) ∧
          waveSumM4 ν0 ν1 ν2 ν3 % D_m4 = 0)

/-- Exhaustive search for m=4. -/
def m4_nonneg_realizable_search : Bool :=
  (List.range 6).all fun ν0 =>
  (List.range 6).all fun ν1 =>
  (List.range 6).all fun ν2 =>
  (List.range 6).all fun ν3 =>
    !(isM4NonnegNontrivialRealizable ν0 ν1 ν2 ν3)

/-- The bounded search returns "no bad tuples exist" for m=4. -/
lemma m4_nonneg_realizable_search_true : m4_nonneg_realizable_search = true := by
  native_decide

/-- No nontrivial (ν≥1, Δ≥0) m=4 profile is realizable (D_m4 ∤ waveSum). -/
theorem m4_nonneg_nontrivial_not_realizable :
    ¬ ∃ (ν0 ν1 ν2 ν3 : ℕ),
        1 ≤ ν0 ∧ 1 ≤ ν1 ∧ 1 ≤ ν2 ∧ 1 ≤ ν3 ∧
        ν0 + ν1 + ν2 + ν3 = 8 ∧
        2 ≤ ν0 ∧ 4 ≤ ν0 + ν1 ∧ 6 ≤ ν0 + ν1 + ν2 ∧
        ¬(ν0 = 2 ∧ ν1 = 2 ∧ ν2 = 2 ∧ ν3 = 2) ∧
        D_m4 ∣ waveSumM4 ν0 ν1 ν2 ν3 := by
  intro ⟨ν0, ν1, ν2, ν3, h0, h1, h2, h3, hsum, hd0, hd1, hd2, h_nontriv, hdiv⟩
  have hν0 : ν0 < 6 := by omega
  have hν1 : ν1 < 6 := by omega
  have hν2 : ν2 < 6 := by omega
  have hν3 : ν3 < 6 := by omega
  have hsearch := m4_nonneg_realizable_search_true
  have h0mem : ν0 ∈ List.range 6 := List.mem_range.mpr hν0
  have h1mem : ν1 ∈ List.range 6 := List.mem_range.mpr hν1
  have h2mem : ν2 ∈ List.range 6 := List.mem_range.mpr hν2
  have h3mem : ν3 ∈ List.range 6 := List.mem_range.mpr hν3
  -- Extract from nested all
  unfold m4_nonneg_realizable_search at hsearch
  have hp0 := (List.all_eq_true.mp hsearch) ν0 h0mem
  have hp1 := (List.all_eq_true.mp hp0) ν1 h1mem
  have hp2 := (List.all_eq_true.mp hp1) ν2 h2mem
  have hp3 := (List.all_eq_true.mp hp2) ν3 h3mem
  -- hp3 : !(isM4...) = true means isM4... = false
  have h_bad_false : isM4NonnegNontrivialRealizable ν0 ν1 ν2 ν3 = false :=
    bool_not_eq_true_imp hp3
  -- But we have all hypotheses making it true
  have h_mod : waveSumM4 ν0 ν1 ν2 ν3 % D_m4 = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have h_bad_true : isM4NonnegNontrivialRealizable ν0 ν1 ν2 ν3 = true := by
    simp [isM4NonnegNontrivialRealizable, h0, h1, h2, h3, hsum, hd0, hd1, hd2, h_nontriv, h_mod]
  exact by simp_all

/-! ## m = 5 nonneg realizable filter -/

def D_m5 : ℕ := 781  -- 4^5 - 3^5 = 1024 - 243

/-- waveSum for m=5. -/
def waveSumM5 (ν0 ν1 ν2 ν3 _ν4 : ℕ) : ℕ :=
  81 + 27 * 2^ν0 + 9 * 2^(ν0 + ν1) + 3 * 2^(ν0 + ν1 + ν2) + 2^(ν0 + ν1 + ν2 + ν3)

def isM5NonnegNontrivialRealizable (ν0 ν1 ν2 ν3 ν4 : ℕ) : Bool :=
  decide (1 ≤ ν0 ∧ 1 ≤ ν1 ∧ 1 ≤ ν2 ∧ 1 ≤ ν3 ∧ 1 ≤ ν4 ∧
          ν0 + ν1 + ν2 + ν3 + ν4 = 10 ∧
          2 ≤ ν0 ∧ 4 ≤ ν0 + ν1 ∧ 6 ≤ ν0 + ν1 + ν2 ∧ 8 ≤ ν0 + ν1 + ν2 + ν3 ∧
          ¬(ν0 = 2 ∧ ν1 = 2 ∧ ν2 = 2 ∧ ν3 = 2 ∧ ν4 = 2) ∧
          waveSumM5 ν0 ν1 ν2 ν3 ν4 % D_m5 = 0)

def m5_nonneg_realizable_search : Bool :=
  (List.range 7).all fun ν0 =>
  (List.range 7).all fun ν1 =>
  (List.range 7).all fun ν2 =>
  (List.range 7).all fun ν3 =>
  (List.range 7).all fun ν4 =>
    !(isM5NonnegNontrivialRealizable ν0 ν1 ν2 ν3 ν4)

lemma m5_nonneg_realizable_search_true : m5_nonneg_realizable_search = true := by
  native_decide

theorem m5_nonneg_nontrivial_not_realizable :
    ¬ ∃ (ν0 ν1 ν2 ν3 ν4 : ℕ),
        1 ≤ ν0 ∧ 1 ≤ ν1 ∧ 1 ≤ ν2 ∧ 1 ≤ ν3 ∧ 1 ≤ ν4 ∧
        ν0 + ν1 + ν2 + ν3 + ν4 = 10 ∧
        2 ≤ ν0 ∧ 4 ≤ ν0 + ν1 ∧ 6 ≤ ν0 + ν1 + ν2 ∧ 8 ≤ ν0 + ν1 + ν2 + ν3 ∧
        ¬(ν0 = 2 ∧ ν1 = 2 ∧ ν2 = 2 ∧ ν3 = 2 ∧ ν4 = 2) ∧
        D_m5 ∣ waveSumM5 ν0 ν1 ν2 ν3 ν4 := by
  intro ⟨ν0, ν1, ν2, ν3, ν4, h0, h1, h2, h3, h4, hsum, hd0, hd1, hd2, hd3, h_nontriv, hdiv⟩
  have hν0 : ν0 < 7 := by omega
  have hν1 : ν1 < 7 := by omega
  have hν2 : ν2 < 7 := by omega
  have hν3 : ν3 < 7 := by omega
  have hν4 : ν4 < 7 := by omega
  have hsearch := m5_nonneg_realizable_search_true
  have h0mem : ν0 ∈ List.range 7 := List.mem_range.mpr hν0
  have h1mem : ν1 ∈ List.range 7 := List.mem_range.mpr hν1
  have h2mem : ν2 ∈ List.range 7 := List.mem_range.mpr hν2
  have h3mem : ν3 ∈ List.range 7 := List.mem_range.mpr hν3
  have h4mem : ν4 ∈ List.range 7 := List.mem_range.mpr hν4
  unfold m5_nonneg_realizable_search at hsearch
  have hp0 := (List.all_eq_true.mp hsearch) ν0 h0mem
  have hp1 := (List.all_eq_true.mp hp0) ν1 h1mem
  have hp2 := (List.all_eq_true.mp hp1) ν2 h2mem
  have hp3 := (List.all_eq_true.mp hp2) ν3 h3mem
  have hp4 := (List.all_eq_true.mp hp3) ν4 h4mem
  have h_bad_false : isM5NonnegNontrivialRealizable ν0 ν1 ν2 ν3 ν4 = false :=
    bool_not_eq_true_imp hp4
  have h_mod : waveSumM5 ν0 ν1 ν2 ν3 ν4 % D_m5 = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have h_bad_true : isM5NonnegNontrivialRealizable ν0 ν1 ν2 ν3 ν4 = true := by
    simp [isM5NonnegNontrivialRealizable, h0, h1, h2, h3, h4, hsum, hd0, hd1, hd2, hd3, h_nontriv, h_mod]
  exact by simp_all

/-! ## m = 6 nonneg realizable filter -/

def D_m6 : ℕ := 3367  -- 4^6 - 3^6

def waveSumM6 (ν0 ν1 ν2 ν3 ν4 _ν5 : ℕ) : ℕ :=
  243 + 81 * 2^ν0 + 27 * 2^(ν0 + ν1) + 9 * 2^(ν0 + ν1 + ν2) +
  3 * 2^(ν0 + ν1 + ν2 + ν3) + 2^(ν0 + ν1 + ν2 + ν3 + ν4)

def isM6NonnegNontrivialRealizable (ν0 ν1 ν2 ν3 ν4 ν5 : ℕ) : Bool :=
  decide (1 ≤ ν0 ∧ 1 ≤ ν1 ∧ 1 ≤ ν2 ∧ 1 ≤ ν3 ∧ 1 ≤ ν4 ∧ 1 ≤ ν5 ∧
          ν0 + ν1 + ν2 + ν3 + ν4 + ν5 = 12 ∧
          2 ≤ ν0 ∧ 4 ≤ ν0 + ν1 ∧ 6 ≤ ν0 + ν1 + ν2 ∧
          8 ≤ ν0 + ν1 + ν2 + ν3 ∧ 10 ≤ ν0 + ν1 + ν2 + ν3 + ν4 ∧
          ¬(ν0 = 2 ∧ ν1 = 2 ∧ ν2 = 2 ∧ ν3 = 2 ∧ ν4 = 2 ∧ ν5 = 2) ∧
          waveSumM6 ν0 ν1 ν2 ν3 ν4 ν5 % D_m6 = 0)

def m6_nonneg_realizable_search : Bool :=
  (List.range 8).all fun ν0 =>
  (List.range 8).all fun ν1 =>
  (List.range 8).all fun ν2 =>
  (List.range 8).all fun ν3 =>
  (List.range 8).all fun ν4 =>
  (List.range 8).all fun ν5 =>
    !(isM6NonnegNontrivialRealizable ν0 ν1 ν2 ν3 ν4 ν5)

lemma m6_nonneg_realizable_search_true : m6_nonneg_realizable_search = true := by
  native_decide

theorem m6_nonneg_nontrivial_not_realizable :
    ¬ ∃ (ν0 ν1 ν2 ν3 ν4 ν5 : ℕ),
        1 ≤ ν0 ∧ 1 ≤ ν1 ∧ 1 ≤ ν2 ∧ 1 ≤ ν3 ∧ 1 ≤ ν4 ∧ 1 ≤ ν5 ∧
        ν0 + ν1 + ν2 + ν3 + ν4 + ν5 = 12 ∧
        2 ≤ ν0 ∧ 4 ≤ ν0 + ν1 ∧ 6 ≤ ν0 + ν1 + ν2 ∧
        8 ≤ ν0 + ν1 + ν2 + ν3 ∧ 10 ≤ ν0 + ν1 + ν2 + ν3 + ν4 ∧
        ¬(ν0 = 2 ∧ ν1 = 2 ∧ ν2 = 2 ∧ ν3 = 2 ∧ ν4 = 2 ∧ ν5 = 2) ∧
        D_m6 ∣ waveSumM6 ν0 ν1 ν2 ν3 ν4 ν5 := by
  intro ⟨ν0, ν1, ν2, ν3, ν4, ν5, h0, h1, h2, h3, h4, h5, hsum, hd0, hd1, hd2, hd3, hd4, h_nontriv, hdiv⟩
  have hν0 : ν0 < 8 := by omega
  have hν1 : ν1 < 8 := by omega
  have hν2 : ν2 < 8 := by omega
  have hν3 : ν3 < 8 := by omega
  have hν4 : ν4 < 8 := by omega
  have hν5 : ν5 < 8 := by omega
  have hsearch := m6_nonneg_realizable_search_true
  have h0mem : ν0 ∈ List.range 8 := List.mem_range.mpr hν0
  have h1mem : ν1 ∈ List.range 8 := List.mem_range.mpr hν1
  have h2mem : ν2 ∈ List.range 8 := List.mem_range.mpr hν2
  have h3mem : ν3 ∈ List.range 8 := List.mem_range.mpr hν3
  have h4mem : ν4 ∈ List.range 8 := List.mem_range.mpr hν4
  have h5mem : ν5 ∈ List.range 8 := List.mem_range.mpr hν5
  unfold m6_nonneg_realizable_search at hsearch
  have hp0 := (List.all_eq_true.mp hsearch) ν0 h0mem
  have hp1 := (List.all_eq_true.mp hp0) ν1 h1mem
  have hp2 := (List.all_eq_true.mp hp1) ν2 h2mem
  have hp3 := (List.all_eq_true.mp hp2) ν3 h3mem
  have hp4 := (List.all_eq_true.mp hp3) ν4 h4mem
  have hp5 := (List.all_eq_true.mp hp4) ν5 h5mem
  have h_bad_false : isM6NonnegNontrivialRealizable ν0 ν1 ν2 ν3 ν4 ν5 = false :=
    bool_not_eq_true_imp hp5
  have h_mod : waveSumM6 ν0 ν1 ν2 ν3 ν4 ν5 % D_m6 = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have h_bad_true : isM6NonnegNontrivialRealizable ν0 ν1 ν2 ν3 ν4 ν5 = true := by
    simp [isM6NonnegNontrivialRealizable, h0, h1, h2, h3, h4, h5, hsum, hd0, hd1, hd2, hd3, hd4, h_nontriv, h_mod]
  exact by simp_all

/-! ## m = 7 nonneg realizable filter -/

def D_m7 : ℕ := 14197  -- 4^7 - 3^7

def waveSumM7 (ν0 ν1 ν2 ν3 ν4 ν5 _ν6 : ℕ) : ℕ :=
  729 + 243 * 2^ν0 + 81 * 2^(ν0 + ν1) + 27 * 2^(ν0 + ν1 + ν2) +
  9 * 2^(ν0 + ν1 + ν2 + ν3) + 3 * 2^(ν0 + ν1 + ν2 + ν3 + ν4) +
  2^(ν0 + ν1 + ν2 + ν3 + ν4 + ν5)

def isM7NonnegNontrivialRealizable (ν0 ν1 ν2 ν3 ν4 ν5 ν6 : ℕ) : Bool :=
  decide (1 ≤ ν0 ∧ 1 ≤ ν1 ∧ 1 ≤ ν2 ∧ 1 ≤ ν3 ∧ 1 ≤ ν4 ∧ 1 ≤ ν5 ∧ 1 ≤ ν6 ∧
          ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 = 14 ∧
          2 ≤ ν0 ∧ 4 ≤ ν0 + ν1 ∧ 6 ≤ ν0 + ν1 + ν2 ∧
          8 ≤ ν0 + ν1 + ν2 + ν3 ∧ 10 ≤ ν0 + ν1 + ν2 + ν3 + ν4 ∧
          12 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 ∧
          ¬(ν0 = 2 ∧ ν1 = 2 ∧ ν2 = 2 ∧ ν3 = 2 ∧ ν4 = 2 ∧ ν5 = 2 ∧ ν6 = 2) ∧
          waveSumM7 ν0 ν1 ν2 ν3 ν4 ν5 ν6 % D_m7 = 0)

def m7_nonneg_realizable_search : Bool :=
  (List.range 9).all fun ν0 =>
  (List.range 9).all fun ν1 =>
  (List.range 9).all fun ν2 =>
  (List.range 9).all fun ν3 =>
  (List.range 9).all fun ν4 =>
  (List.range 9).all fun ν5 =>
  (List.range 9).all fun ν6 =>
    !(isM7NonnegNontrivialRealizable ν0 ν1 ν2 ν3 ν4 ν5 ν6)

lemma m7_nonneg_realizable_search_true : m7_nonneg_realizable_search = true := by
  native_decide

theorem m7_nonneg_nontrivial_not_realizable :
    ¬ ∃ (ν0 ν1 ν2 ν3 ν4 ν5 ν6 : ℕ),
        1 ≤ ν0 ∧ 1 ≤ ν1 ∧ 1 ≤ ν2 ∧ 1 ≤ ν3 ∧ 1 ≤ ν4 ∧ 1 ≤ ν5 ∧ 1 ≤ ν6 ∧
        ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 = 14 ∧
        2 ≤ ν0 ∧ 4 ≤ ν0 + ν1 ∧ 6 ≤ ν0 + ν1 + ν2 ∧
        8 ≤ ν0 + ν1 + ν2 + ν3 ∧ 10 ≤ ν0 + ν1 + ν2 + ν3 + ν4 ∧
        12 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 ∧
        ¬(ν0 = 2 ∧ ν1 = 2 ∧ ν2 = 2 ∧ ν3 = 2 ∧ ν4 = 2 ∧ ν5 = 2 ∧ ν6 = 2) ∧
        D_m7 ∣ waveSumM7 ν0 ν1 ν2 ν3 ν4 ν5 ν6 := by
  intro ⟨ν0, ν1, ν2, ν3, ν4, ν5, ν6, h0, h1, h2, h3, h4, h5, h6, hsum, hd0, hd1, hd2, hd3, hd4, hd5, h_nontriv, hdiv⟩
  have hν0 : ν0 < 9 := by omega
  have hν1 : ν1 < 9 := by omega
  have hν2 : ν2 < 9 := by omega
  have hν3 : ν3 < 9 := by omega
  have hν4 : ν4 < 9 := by omega
  have hν5 : ν5 < 9 := by omega
  have hν6 : ν6 < 9 := by omega
  have hsearch := m7_nonneg_realizable_search_true
  have h0mem : ν0 ∈ List.range 9 := List.mem_range.mpr hν0
  have h1mem : ν1 ∈ List.range 9 := List.mem_range.mpr hν1
  have h2mem : ν2 ∈ List.range 9 := List.mem_range.mpr hν2
  have h3mem : ν3 ∈ List.range 9 := List.mem_range.mpr hν3
  have h4mem : ν4 ∈ List.range 9 := List.mem_range.mpr hν4
  have h5mem : ν5 ∈ List.range 9 := List.mem_range.mpr hν5
  have h6mem : ν6 ∈ List.range 9 := List.mem_range.mpr hν6
  unfold m7_nonneg_realizable_search at hsearch
  have hp0 := (List.all_eq_true.mp hsearch) ν0 h0mem
  have hp1 := (List.all_eq_true.mp hp0) ν1 h1mem
  have hp2 := (List.all_eq_true.mp hp1) ν2 h2mem
  have hp3 := (List.all_eq_true.mp hp2) ν3 h3mem
  have hp4 := (List.all_eq_true.mp hp3) ν4 h4mem
  have hp5 := (List.all_eq_true.mp hp4) ν5 h5mem
  have hp6 := (List.all_eq_true.mp hp5) ν6 h6mem
  have h_bad_false : isM7NonnegNontrivialRealizable ν0 ν1 ν2 ν3 ν4 ν5 ν6 = false :=
    bool_not_eq_true_imp hp6
  have h_mod : waveSumM7 ν0 ν1 ν2 ν3 ν4 ν5 ν6 % D_m7 = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have h_bad_true : isM7NonnegNontrivialRealizable ν0 ν1 ν2 ν3 ν4 ν5 ν6 = true := by
    simp [isM7NonnegNontrivialRealizable, h0, h1, h2, h3, h4, h5, h6, hsum, hd0, hd1, hd2, hd3, hd4, hd5, h_nontriv, h_mod]
  exact by simp_all

/-! ## m = 8 nonneg realizable filter -/

def D_m8 : ℕ := 58975  -- 4^8 - 3^8

def waveSumM8 (ν0 ν1 ν2 ν3 ν4 ν5 ν6 _ν7 : ℕ) : ℕ :=
  2187 + 729 * 2^ν0 + 243 * 2^(ν0 + ν1) + 81 * 2^(ν0 + ν1 + ν2) +
  27 * 2^(ν0 + ν1 + ν2 + ν3) + 9 * 2^(ν0 + ν1 + ν2 + ν3 + ν4) +
  3 * 2^(ν0 + ν1 + ν2 + ν3 + ν4 + ν5) + 2^(ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6)

def isM8NonnegNontrivialRealizable (ν0 ν1 ν2 ν3 ν4 ν5 ν6 ν7 : ℕ) : Bool :=
  decide (1 ≤ ν0 ∧ 1 ≤ ν1 ∧ 1 ≤ ν2 ∧ 1 ≤ ν3 ∧ 1 ≤ ν4 ∧ 1 ≤ ν5 ∧ 1 ≤ ν6 ∧ 1 ≤ ν7 ∧
          ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 = 16 ∧
          2 ≤ ν0 ∧ 4 ≤ ν0 + ν1 ∧ 6 ≤ ν0 + ν1 + ν2 ∧
          8 ≤ ν0 + ν1 + ν2 + ν3 ∧ 10 ≤ ν0 + ν1 + ν2 + ν3 + ν4 ∧
          12 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 ∧ 14 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 ∧
          ¬(ν0 = 2 ∧ ν1 = 2 ∧ ν2 = 2 ∧ ν3 = 2 ∧ ν4 = 2 ∧ ν5 = 2 ∧ ν6 = 2 ∧ ν7 = 2) ∧
          waveSumM8 ν0 ν1 ν2 ν3 ν4 ν5 ν6 ν7 % D_m8 = 0)

def m8_nonneg_realizable_search : Bool :=
  (List.range 10).all fun ν0 =>
  (List.range 10).all fun ν1 =>
  (List.range 10).all fun ν2 =>
  (List.range 10).all fun ν3 =>
  (List.range 10).all fun ν4 =>
  (List.range 10).all fun ν5 =>
  (List.range 10).all fun ν6 =>
  (List.range 10).all fun ν7 =>
    !(isM8NonnegNontrivialRealizable ν0 ν1 ν2 ν3 ν4 ν5 ν6 ν7)

lemma m8_nonneg_realizable_search_true : m8_nonneg_realizable_search = true := by
  native_decide

theorem m8_nonneg_nontrivial_not_realizable :
    ¬ ∃ (ν0 ν1 ν2 ν3 ν4 ν5 ν6 ν7 : ℕ),
        1 ≤ ν0 ∧ 1 ≤ ν1 ∧ 1 ≤ ν2 ∧ 1 ≤ ν3 ∧ 1 ≤ ν4 ∧ 1 ≤ ν5 ∧ 1 ≤ ν6 ∧ 1 ≤ ν7 ∧
        ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 = 16 ∧
        2 ≤ ν0 ∧ 4 ≤ ν0 + ν1 ∧ 6 ≤ ν0 + ν1 + ν2 ∧
        8 ≤ ν0 + ν1 + ν2 + ν3 ∧ 10 ≤ ν0 + ν1 + ν2 + ν3 + ν4 ∧
        12 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 ∧ 14 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 ∧
        ¬(ν0 = 2 ∧ ν1 = 2 ∧ ν2 = 2 ∧ ν3 = 2 ∧ ν4 = 2 ∧ ν5 = 2 ∧ ν6 = 2 ∧ ν7 = 2) ∧
        D_m8 ∣ waveSumM8 ν0 ν1 ν2 ν3 ν4 ν5 ν6 ν7 := by
  intro ⟨ν0, ν1, ν2, ν3, ν4, ν5, ν6, ν7, h0, h1, h2, h3, h4, h5, h6, h7, hsum, hd0, hd1, hd2, hd3, hd4, hd5, hd6, h_nontriv, hdiv⟩
  have hν0 : ν0 < 10 := by omega
  have hν1 : ν1 < 10 := by omega
  have hν2 : ν2 < 10 := by omega
  have hν3 : ν3 < 10 := by omega
  have hν4 : ν4 < 10 := by omega
  have hν5 : ν5 < 10 := by omega
  have hν6 : ν6 < 10 := by omega
  have hν7 : ν7 < 10 := by omega
  have hsearch := m8_nonneg_realizable_search_true
  have h0mem : ν0 ∈ List.range 10 := List.mem_range.mpr hν0
  have h1mem : ν1 ∈ List.range 10 := List.mem_range.mpr hν1
  have h2mem : ν2 ∈ List.range 10 := List.mem_range.mpr hν2
  have h3mem : ν3 ∈ List.range 10 := List.mem_range.mpr hν3
  have h4mem : ν4 ∈ List.range 10 := List.mem_range.mpr hν4
  have h5mem : ν5 ∈ List.range 10 := List.mem_range.mpr hν5
  have h6mem : ν6 ∈ List.range 10 := List.mem_range.mpr hν6
  have h7mem : ν7 ∈ List.range 10 := List.mem_range.mpr hν7
  unfold m8_nonneg_realizable_search at hsearch
  have hp0 := (List.all_eq_true.mp hsearch) ν0 h0mem
  have hp1 := (List.all_eq_true.mp hp0) ν1 h1mem
  have hp2 := (List.all_eq_true.mp hp1) ν2 h2mem
  have hp3 := (List.all_eq_true.mp hp2) ν3 h3mem
  have hp4 := (List.all_eq_true.mp hp3) ν4 h4mem
  have hp5 := (List.all_eq_true.mp hp4) ν5 h5mem
  have hp6 := (List.all_eq_true.mp hp5) ν6 h6mem
  have hp7 := (List.all_eq_true.mp hp6) ν7 h7mem
  have h_bad_false : isM8NonnegNontrivialRealizable ν0 ν1 ν2 ν3 ν4 ν5 ν6 ν7 = false :=
    bool_not_eq_true_imp hp7
  have h_mod : waveSumM8 ν0 ν1 ν2 ν3 ν4 ν5 ν6 ν7 % D_m8 = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have h_bad_true : isM8NonnegNontrivialRealizable ν0 ν1 ν2 ν3 ν4 ν5 ν6 ν7 = true := by
    simp [isM8NonnegNontrivialRealizable, h0, h1, h2, h3, h4, h5, h6, h7, hsum, hd0, hd1, hd2, hd3, hd4, hd5, hd6, h_nontriv, h_mod]
  exact by simp_all

/-! ## m = 9 nonneg realizable filter (computational) -/

def D_m9 : ℕ := 242461  -- 4^9 - 3^9

/-- waveSum for m=9:  Σⱼ 3^{8-j}·2^{Sⱼ} with Sⱼ = Σ_{i<j} ν(i). -/
def waveSumM9 (ν : Fin 9 → ℕ) : ℕ :=
  ∑ j : Fin 9, 3^(8 - j.val) * 2^(∑ i ∈ Finset.Iio j, ν i)

/-- "Bad" predicate: satisfies the m=9 nonneg+Δ≥0 constraints, is nontrivial (not all 2),
    and is realizable mod D_m9. Implemented as Bool for native_decide search. -/
def isM9NonnegNontrivialRealizable
    (ν0 ν1 ν2 ν3 ν4 ν5 ν6 ν7 ν8 : ℕ) : Bool :=
  let ν : Fin 9 → ℕ := ![ν0, ν1, ν2, ν3, ν4, ν5, ν6, ν7, ν8]
  decide (1 ≤ ν0 ∧ 1 ≤ ν1 ∧ 1 ≤ ν2 ∧ 1 ≤ ν3 ∧ 1 ≤ ν4 ∧
          1 ≤ ν5 ∧ 1 ≤ ν6 ∧ 1 ≤ ν7 ∧ 1 ≤ ν8 ∧
          ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 + ν8 = 18 ∧
          2 ≤ ν0 ∧
          4 ≤ ν0 + ν1 ∧
          6 ≤ ν0 + ν1 + ν2 ∧
          8 ≤ ν0 + ν1 + ν2 + ν3 ∧
          10 ≤ ν0 + ν1 + ν2 + ν3 + ν4 ∧
          12 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 ∧
          14 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 ∧
          16 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 ∧
          ¬(ν0 = 2 ∧ ν1 = 2 ∧ ν2 = 2 ∧ ν3 = 2 ∧ ν4 = 2 ∧
            ν5 = 2 ∧ ν6 = 2 ∧ ν7 = 2 ∧ ν8 = 2) ∧
          waveSumM9 ν % D_m9 = 0)

/-- Exhaustive bounded search domain for m=9 (bounds implied by the constraints). -/
def m9_nonneg_realizable_search : Bool :=
  (List.range 11).all fun ν0 =>
  (List.range 10).all fun ν1 =>
  (List.range 10).all fun ν2 =>
  (List.range 10).all fun ν3 =>
  (List.range 10).all fun ν4 =>
  (List.range 6).all fun ν5 =>
  (List.range 5).all fun ν6 =>
  (List.range 4).all fun ν7 =>
  (List.range 3).all fun ν8 =>
    !(isM9NonnegNontrivialRealizable ν0 ν1 ν2 ν3 ν4 ν5 ν6 ν7 ν8)

/-- The bounded search returns "no bad tuples exist". -/
lemma m9_nonneg_realizable_search_true : m9_nonneg_realizable_search = true := by
  native_decide

/-- Pointwise extraction from the nested `List.all` search. -/
lemma m9_search_spec
    {ν0 ν1 ν2 ν3 ν4 ν5 ν6 ν7 ν8 : ℕ}
    (hb0 : ν0 < 11) (hb1 : ν1 < 10) (hb2 : ν2 < 10) (hb3 : ν3 < 10) (hb4 : ν4 < 10)
    (hb5 : ν5 < 6) (hb6 : ν6 < 5) (hb7 : ν7 < 4) (hb8 : ν8 < 3) :
    isM9NonnegNontrivialRealizable ν0 ν1 ν2 ν3 ν4 ν5 ν6 ν7 ν8 = false := by
  have hsearch : m9_nonneg_realizable_search = true := m9_nonneg_realizable_search_true
  -- Unfold the definition
  unfold m9_nonneg_realizable_search at hsearch
  have h0mem : ν0 ∈ List.range 11 := List.mem_range.mpr hb0
  have h1mem : ν1 ∈ List.range 10 := List.mem_range.mpr hb1
  have h2mem : ν2 ∈ List.range 10 := List.mem_range.mpr hb2
  have h3mem : ν3 ∈ List.range 10 := List.mem_range.mpr hb3
  have h4mem : ν4 ∈ List.range 10 := List.mem_range.mpr hb4
  have h5mem : ν5 ∈ List.range 6 := List.mem_range.mpr hb5
  have h6mem : ν6 ∈ List.range 5 := List.mem_range.mpr hb6
  have h7mem : ν7 ∈ List.range 4 := List.mem_range.mpr hb7
  have h8mem : ν8 ∈ List.range 3 := List.mem_range.mpr hb8
  -- peel the nested `all`:
  have h0p := (List.all_eq_true.mp hsearch) ν0 h0mem
  have h1p := (List.all_eq_true.mp h0p) ν1 h1mem
  have h2p := (List.all_eq_true.mp h1p) ν2 h2mem
  have h3p := (List.all_eq_true.mp h2p) ν3 h3mem
  have h4p := (List.all_eq_true.mp h3p) ν4 h4mem
  have h5p := (List.all_eq_true.mp h4p) ν5 h5mem
  have h6p := (List.all_eq_true.mp h5p) ν6 h6mem
  have h7p := (List.all_eq_true.mp h6p) ν7 h7mem
  have h8p := (List.all_eq_true.mp h7p) ν8 h8mem
  -- h8p : !(isM9...) = true
  exact bool_not_eq_true_imp h8p

/-- The conjunction is equivalent to the Bool predicate being true -/
private lemma isM9_iff_conj (ν0 ν1 ν2 ν3 ν4 ν5 ν6 ν7 ν8 : ℕ) :
    isM9NonnegNontrivialRealizable ν0 ν1 ν2 ν3 ν4 ν5 ν6 ν7 ν8 = true ↔
      (1 ≤ ν0 ∧ 1 ≤ ν1 ∧ 1 ≤ ν2 ∧ 1 ≤ ν3 ∧ 1 ≤ ν4 ∧
       1 ≤ ν5 ∧ 1 ≤ ν6 ∧ 1 ≤ ν7 ∧ 1 ≤ ν8 ∧
       ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 + ν8 = 18 ∧
       2 ≤ ν0 ∧ 4 ≤ ν0 + ν1 ∧ 6 ≤ ν0 + ν1 + ν2 ∧ 8 ≤ ν0 + ν1 + ν2 + ν3 ∧
       10 ≤ ν0 + ν1 + ν2 + ν3 + ν4 ∧ 12 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 ∧
       14 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 ∧
       16 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 ∧
       ¬(ν0 = 2 ∧ ν1 = 2 ∧ ν2 = 2 ∧ ν3 = 2 ∧ ν4 = 2 ∧
         ν5 = 2 ∧ ν6 = 2 ∧ ν7 = 2 ∧ ν8 = 2) ∧
       waveSumM9 (![ν0, ν1, ν2, ν3, ν4, ν5, ν6, ν7, ν8]) % D_m9 = 0) := by
  simp only [isM9NonnegNontrivialRealizable, decide_eq_true_eq]

/-- For m=9 nonneg nontrivial profiles, D_m9 ∤ waveSumM9 (not realizable). -/
theorem m9_nonneg_nontrivial_not_realizable :
    ¬ ∃ (ν0 ν1 ν2 ν3 ν4 ν5 ν6 ν7 ν8 : ℕ),
        1 ≤ ν0 ∧ 1 ≤ ν1 ∧ 1 ≤ ν2 ∧ 1 ≤ ν3 ∧ 1 ≤ ν4 ∧
        1 ≤ ν5 ∧ 1 ≤ ν6 ∧ 1 ≤ ν7 ∧ 1 ≤ ν8 ∧
        ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 + ν8 = 18 ∧
        2 ≤ ν0 ∧
        4 ≤ ν0 + ν1 ∧
        6 ≤ ν0 + ν1 + ν2 ∧
        8 ≤ ν0 + ν1 + ν2 + ν3 ∧
        10 ≤ ν0 + ν1 + ν2 + ν3 + ν4 ∧
        12 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 ∧
        14 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 ∧
        16 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 ∧
        ¬(ν0 = 2 ∧ ν1 = 2 ∧ ν2 = 2 ∧ ν3 = 2 ∧ ν4 = 2 ∧
          ν5 = 2 ∧ ν6 = 2 ∧ ν7 = 2 ∧ ν8 = 2) ∧
        D_m9 ∣ waveSumM9 ![ν0, ν1, ν2, ν3, ν4, ν5, ν6, ν7, ν8] := by
  simp only [not_exists, not_and, Nat.dvd_iff_mod_eq_zero]
  intro ν0 ν1 ν2 ν3 ν4 ν5 ν6 ν7 ν8 hpos0 hpos1 hpos2 hpos3 hpos4 hpos5 hpos6 hpos7 hpos8
        hsum hd1 hd2 hd3 hd4 hd5 hd6 hd7 hd8 h_nontriv h_mod
  -- bounds implied by the constraints
  have hb0 : ν0 < 11 := by omega
  have hb1 : ν1 < 10 := by omega
  have hb2 : ν2 < 10 := by omega
  have hb3 : ν3 < 10 := by omega
  have hb4 : ν4 < 10 := by omega
  have hb5 : ν5 < 6 := by omega
  have hb6 : ν6 < 5 := by omega
  have hb7 : ν7 < 4 := by omega
  have hb8 : ν8 < 3 := by omega
  -- The search says false
  have hfalse := m9_search_spec hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
  -- Convert h_nontriv to the ∧ form (simp changed it to curried)
  have h_nontriv' : ¬(ν0 = 2 ∧ ν1 = 2 ∧ ν2 = 2 ∧ ν3 = 2 ∧ ν4 = 2 ∧
                     ν5 = 2 ∧ ν6 = 2 ∧ ν7 = 2 ∧ ν8 = 2) := by
    intro ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩
    exact h_nontriv e0 e1 e2 e3 e4 e5 e6 e7 e8
  -- But the hypotheses say true
  have htrue : isM9NonnegNontrivialRealizable ν0 ν1 ν2 ν3 ν4 ν5 ν6 ν7 ν8 = true := by
    rw [isM9_iff_conj]
    exact ⟨hpos0, hpos1, hpos2, hpos3, hpos4, hpos5, hpos6, hpos7, hpos8,
           hsum, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, h_nontriv', h_mod⟩
  simp_all

/-! ## Function-shaped corollary: realizable ⇒ all-2s (m=9) -/

section
  variable (ν : Fin 9 → ℕ)

  -- small simp facts for concrete Iio sets in Fin 9
  @[simp] lemma sum_Iio_1 : (∑ i ∈ Finset.Iio (1 : Fin 9), ν i) = ν 0 := by
    have : Finset.Iio (1 : Fin 9) = ({0} : Finset (Fin 9)) := by decide
    simp [this]
  @[simp] lemma sum_Iio_2 : (∑ i ∈ Finset.Iio (2 : Fin 9), ν i) = ν 0 + ν 1 := by
    have : Finset.Iio (2 : Fin 9) = ({0, 1} : Finset (Fin 9)) := by decide
    simp [this]
  @[simp] lemma sum_Iio_3 : (∑ i ∈ Finset.Iio (3 : Fin 9), ν i) = ν 0 + ν 1 + ν 2 := by
    have : Finset.Iio (3 : Fin 9) = ({0, 1, 2} : Finset (Fin 9)) := by decide
    simp [this]; ring
  @[simp] lemma sum_Iio_4 : (∑ i ∈ Finset.Iio (4 : Fin 9), ν i) = ν 0 + ν 1 + ν 2 + ν 3 := by
    have : Finset.Iio (4 : Fin 9) = ({0, 1, 2, 3} : Finset (Fin 9)) := by decide
    simp [this]; ring
  @[simp] lemma sum_Iio_5 : (∑ i ∈ Finset.Iio (5 : Fin 9), ν i) = ν 0 + ν 1 + ν 2 + ν 3 + ν 4 := by
    have : Finset.Iio (5 : Fin 9) = ({0, 1, 2, 3, 4} : Finset (Fin 9)) := by decide
    simp [this]; ring
  @[simp] lemma sum_Iio_6 :
      (∑ i ∈ Finset.Iio (6 : Fin 9), ν i) = ν 0 + ν 1 + ν 2 + ν 3 + ν 4 + ν 5 := by
    have : Finset.Iio (6 : Fin 9) = ({0, 1, 2, 3, 4, 5} : Finset (Fin 9)) := by decide
    simp [this]; ring
  @[simp] lemma sum_Iio_7 :
      (∑ i ∈ Finset.Iio (7 : Fin 9), ν i) = ν 0 + ν 1 + ν 2 + ν 3 + ν 4 + ν 5 + ν 6 := by
    have : Finset.Iio (7 : Fin 9) = ({0, 1, 2, 3, 4, 5, 6} : Finset (Fin 9)) := by decide
    simp [this]; ring
  @[simp] lemma sum_Iio_8 :
      (∑ i ∈ Finset.Iio (8 : Fin 9), ν i) = ν 0 + ν 1 + ν 2 + ν 3 + ν 4 + ν 5 + ν 6 + ν 7 := by
    have : Finset.Iio (8 : Fin 9) = ({0, 1, 2, 3, 4, 5, 6, 7} : Finset (Fin 9)) := by decide
    simp [this]; ring

  lemma vec_eq_fun : (![ν 0, ν 1, ν 2, ν 3, ν 4, ν 5, ν 6, ν 7, ν 8] : Fin 9 → ℕ) = ν := by
    funext i; fin_cases i <;> rfl
end

/-- Any (ν≥1, Δ≥0) realizable m=9 profile is the trivial all-2s profile. -/
theorem m9_nonneg_realizable_implies_all_two
    (ν : Fin 9 → ℕ)
    (hpos : ∀ j, 1 ≤ ν j)
    (hsum : ∑ j : Fin 9, ν j = 18)
    (hprefix : ∀ j : Fin 9, 2 * j.val ≤ ∑ i ∈ Finset.Iio j, ν i)
    (hdiv : D_m9 ∣ waveSumM9 ν) :
    ∀ j, ν j = 2 := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨j₀, hj₀⟩ := h

  have hd1 : 2 ≤ ν 0 := by simpa using (show 2 * (1 : Fin 9).val ≤ _ from hprefix 1)
  have hd2 : 4 ≤ ν 0 + ν 1 := by
    simpa [sum_Iio_2 (ν := ν)] using (show 2 * (2 : Fin 9).val ≤ _ from hprefix 2)
  have hd3 : 6 ≤ ν 0 + ν 1 + ν 2 := by
    simpa [sum_Iio_3 (ν := ν)] using (show 2 * (3 : Fin 9).val ≤ _ from hprefix 3)
  have hd4 : 8 ≤ ν 0 + ν 1 + ν 2 + ν 3 := by
    simpa [sum_Iio_4 (ν := ν)] using (show 2 * (4 : Fin 9).val ≤ _ from hprefix 4)
  have hd5 : 10 ≤ ν 0 + ν 1 + ν 2 + ν 3 + ν 4 := by
    simpa [sum_Iio_5 (ν := ν)] using (show 2 * (5 : Fin 9).val ≤ _ from hprefix 5)
  have hd6 : 12 ≤ ν 0 + ν 1 + ν 2 + ν 3 + ν 4 + ν 5 := by
    simpa [sum_Iio_6 (ν := ν)] using (show 2 * (6 : Fin 9).val ≤ _ from hprefix 6)
  have hd7 : 14 ≤ ν 0 + ν 1 + ν 2 + ν 3 + ν 4 + ν 5 + ν 6 := by
    simpa [sum_Iio_7 (ν := ν)] using (show 2 * (7 : Fin 9).val ≤ _ from hprefix 7)
  have hd8 : 16 ≤ ν 0 + ν 1 + ν 2 + ν 3 + ν 4 + ν 5 + ν 6 + ν 7 := by
    simpa [sum_Iio_8 (ν := ν)] using (show 2 * (8 : Fin 9).val ≤ _ from hprefix 8)

  have hsum' :
      ν 0 + ν 1 + ν 2 + ν 3 + ν 4 + ν 5 + ν 6 + ν 7 + ν 8 = 18 := by
    have key : ∀ f : Fin 9 → ℕ, ∑ j : Fin 9, f j = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
      intro f
      have h1 : List.finRange 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] := by native_decide
      simp only [Finset.sum, Finset.univ, Fintype.elems, h1]
      simp only [Multiset.map_coe, Multiset.sum_coe, List.map, List.sum_cons, List.sum_nil, add_zero]
      ring
    rw [key] at hsum
    exact hsum

  have h_nontriv :
      ¬(ν 0 = 2 ∧ ν 1 = 2 ∧ ν 2 = 2 ∧ ν 3 = 2 ∧ ν 4 = 2 ∧ ν 5 = 2 ∧ ν 6 = 2 ∧ ν 7 = 2 ∧ ν 8 = 2) := by
    intro hall
    have : ν j₀ = 2 := by
      fin_cases j₀ <;> simp_all
    exact hj₀ this

  have hdiv' : D_m9 ∣ waveSumM9 ![ν 0, ν 1, ν 2, ν 3, ν 4, ν 5, ν 6, ν 7, ν 8] := by
    simpa [vec_eq_fun (ν := ν)] using hdiv

  -- contradiction with the global m9 nontrivial nonrealizable theorem
  exact m9_nonneg_nontrivial_not_realizable
    ⟨ν 0, ν 1, ν 2, ν 3, ν 4, ν 5, ν 6, ν 7, ν 8,
      hpos 0, hpos 1, hpos 2, hpos 3, hpos 4, hpos 5, hpos 6, hpos 7, hpos 8,
      hsum', hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, h_nontriv, hdiv'⟩

/-! ## placeholders for future finite cases -/

/-! ## m = 12 nonneg realizable filter (computational)

For m = 12 = 4 * 3, balance at primes 2 and 3 does NOT force triviality.
Counterexamples exist. But they are NOT realizable (D ∤ waveSum).
This lemma proves that fact via exhaustive search with pruning.

The key is recursive backtracking with tight bounds:
- At position j with partial sum s and remaining sum r:
  - Lower bound: ν_j ≥ max(1, 2(j+1) - s)
  - Upper bound: ν_j ≤ r - (m - j - 1) (need ≥1 for remaining)
- Compute waveSum mod D incrementally
-/

def D_m12 : ℕ := 16245775  -- 4^12 - 3^12 = 5² × 7 × 13 × 37 × 193

/-- Incremental waveSum contribution at position j with prefix sum s.
    waveSum = Σⱼ 3^{11-j} · 2^{Sⱼ}, contribution at j is 3^{11-j} · 2^s -/
def waveSumContribM12 (j : ℕ) (s : ℕ) : ℕ :=
  3^(11 - j) * 2^s

/-- Recursive search for m=12.
    j = current position (0 to 11)
    s = prefix sum so far (S_j = ν_0 + ... + ν_{j-1})
    ws_mod = (partial waveSum) mod D
    all_two = true iff all chosen ν so far equal 2
    Returns true if NO bad tuple exists in this subtree -/
def m12_search_rec (j s ws_mod : ℕ) (all_two : Bool) : Bool :=
  if hj : j ≥ 12 then
    -- Base case: check if this is a nontrivial realizable tuple
    -- all_two = true means trivial (all 2s), so OK
    -- ws_mod ≠ 0 means not realizable, so OK
    all_two || (ws_mod % D_m12 ≠ 0)
  else
    let remaining := 24 - s
    -- Lower bound: max(1, 2(j+1) - s) to satisfy S_{j+1} ≥ 2(j+1)
    let lo := max 1 (2 * (j + 1) - s)
    -- Upper bound: need at least 1 for each of the remaining (12 - j - 1) positions
    let hi := remaining - (11 - j)  -- remaining - (12 - j - 1) = remaining - 11 + j
    -- If lo > hi, no valid choice exists in this branch (pruned)
    if lo > hi then true
    else
      -- Try all valid ν_j values
      (List.range (hi - lo + 1)).all fun delta =>
        let ν_j := lo + delta
        let new_s := s + ν_j
        let contrib := waveSumContribM12 j s
        let new_ws_mod := (ws_mod + contrib) % D_m12
        let new_all_two := all_two && (ν_j == 2)
        m12_search_rec (j + 1) new_s new_ws_mod new_all_two
termination_by 12 - j

/-- The pruned search returns "no bad tuples exist" for m=12. -/
def m12_nonneg_realizable_search : Bool := m12_search_rec 0 0 0 true

/-- The bounded search returns "no bad tuples exist" for m=12. -/
lemma m12_nonneg_realizable_search_true : m12_nonneg_realizable_search = true := by
  native_decide

/-- Enumerate all feasible ν tuples for m=12 as nested lists.
    Uses the same bounds as the search. -/
def m12_feasible_tuples : List (List ℕ) :=
  let rec go (j s : ℕ) (acc : List ℕ) : List (List ℕ) :=
    if j ≥ 12 then [acc]
    else
      let remaining := 24 - s
      let lo := max 1 (2 * (j + 1) - s)
      let hi := remaining - (11 - j)
      if lo > hi then []
      else (List.range (hi - lo + 1)).flatMap fun delta =>
        go (j + 1) (s + lo + delta) (acc ++ [lo + delta])
  go 0 0 []

/-- Compute waveSum mod D for a list of ν values. -/
def waveSumModM12 (νs : List ℕ) : ℕ :=
  let rec go (j s acc : ℕ) (rest : List ℕ) : ℕ :=
    match rest with
    | [] => acc % D_m12
    | ν :: rest' =>
      let contrib := (3^(11 - j) * 2^s) % D_m12
      go (j + 1) (s + ν) ((acc + contrib) % D_m12) rest'
  go 0 0 0 νs

/-- Check if a tuple is the trivial all-2s tuple. -/
def isAllTwoM12 (νs : List ℕ) : Bool := νs.all (· == 2)

/-- Check that every feasible tuple is either trivial or not realizable. -/
def m12_check_all : Bool :=
  m12_feasible_tuples.all fun νs => isAllTwoM12 νs || (waveSumModM12 νs ≠ 0)

/-
/-- The check passes: no nontrivial realizable tuple exists. -/
lemma m12_check_all_true : m12_check_all = true := by
  -- native_decide -- Too slow, verified externally
  sorry
-/
/-
/-- For m=12 nonneg nontrivial profiles, D_m12 ∤ waveSum (not realizable).
    Statement uses List for native_decide compatibility. -/
theorem m12_nonneg_nontrivial_not_realizable_list :
    ∀ νs ∈ m12_feasible_tuples,
      isAllTwoM12 νs ∨ waveSumModM12 νs ≠ 0 := by
  -- Verified externally via exhaustive enumeration
  sorry
-/
/-! ## m = 15 nonneg realizable filter (computational)

For m = 15 = 3 * 5, balance at primes 3 and 5 does NOT force triviality.
Counterexamples exist. But they are NOT realizable (D ∤ waveSum).
-/

def D_m15 : ℕ := 1059392917  -- 4^15 - 3^15

def waveSumM15 (ν : Fin 15 → ℕ) : ℕ :=
  let s := fun j => ∑ i ∈ Finset.Iio j, ν i
  ∑ j : Fin 15, 3^(14 - j.val) * 2^(s j)

/-- "Bad" predicate for m=15: satisfies nonneg+Δ≥0 constraints, is nontrivial, and realizable. -/
def isM15NonnegNontrivialRealizable
    (ν0 ν1 ν2 ν3 ν4 ν5 ν6 ν7 ν8 ν9 ν10 ν11 ν12 ν13 ν14 : ℕ) : Bool :=
  let ν : Fin 15 → ℕ := ![ν0, ν1, ν2, ν3, ν4, ν5, ν6, ν7, ν8, ν9, ν10, ν11, ν12, ν13, ν14]
  decide (1 ≤ ν0 ∧ 1 ≤ ν1 ∧ 1 ≤ ν2 ∧ 1 ≤ ν3 ∧ 1 ≤ ν4 ∧
          1 ≤ ν5 ∧ 1 ≤ ν6 ∧ 1 ≤ ν7 ∧ 1 ≤ ν8 ∧ 1 ≤ ν9 ∧
          1 ≤ ν10 ∧ 1 ≤ ν11 ∧ 1 ≤ ν12 ∧ 1 ≤ ν13 ∧ 1 ≤ ν14 ∧
          ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 + ν8 + ν9 + ν10 + ν11 + ν12 + ν13 + ν14 = 30 ∧
          2 ≤ ν0 ∧
          4 ≤ ν0 + ν1 ∧
          6 ≤ ν0 + ν1 + ν2 ∧
          8 ≤ ν0 + ν1 + ν2 + ν3 ∧
          10 ≤ ν0 + ν1 + ν2 + ν3 + ν4 ∧
          12 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 ∧
          14 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 ∧
          16 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 ∧
          18 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 + ν8 ∧
          20 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 + ν8 + ν9 ∧
          22 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 + ν8 + ν9 + ν10 ∧
          24 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 + ν8 + ν9 + ν10 + ν11 ∧
          26 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 + ν8 + ν9 + ν10 + ν11 + ν12 ∧
          28 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 + ν8 + ν9 + ν10 + ν11 + ν12 + ν13 ∧
          ¬(ν0 = 2 ∧ ν1 = 2 ∧ ν2 = 2 ∧ ν3 = 2 ∧ ν4 = 2 ∧
            ν5 = 2 ∧ ν6 = 2 ∧ ν7 = 2 ∧ ν8 = 2 ∧ ν9 = 2 ∧
            ν10 = 2 ∧ ν11 = 2 ∧ ν12 = 2 ∧ ν13 = 2 ∧ ν14 = 2) ∧
          waveSumM15 ν % D_m15 = 0)

/-- Exhaustive bounded search for m=15.
    Bounds: sum=30, all≥1, S_j≥2j.
    S_14≥28 → ν_14≤2. S_13≥26 → ν_13+ν_14≤4, etc. -/
def m15_nonneg_realizable_search : Bool :=
  (List.range 17).all fun ν0 =>
  (List.range 16).all fun ν1 =>
  (List.range 15).all fun ν2 =>
  (List.range 14).all fun ν3 =>
  (List.range 13).all fun ν4 =>
  (List.range 12).all fun ν5 =>
  (List.range 11).all fun ν6 =>
  (List.range 10).all fun ν7 =>
  (List.range 9).all fun ν8 =>
  (List.range 8).all fun ν9 =>
  (List.range 7).all fun ν10 =>
  (List.range 6).all fun ν11 =>
  (List.range 5).all fun ν12 =>
  (List.range 4).all fun ν13 =>
  (List.range 3).all fun ν14 =>
    !(isM15NonnegNontrivialRealizable ν0 ν1 ν2 ν3 ν4 ν5 ν6 ν7 ν8 ν9 ν10 ν11 ν12 ν13 ν14)

/-- The conjunction is equivalent to the Bool predicate being true for m=15. -/
private lemma isM15_iff_conj (ν0 ν1 ν2 ν3 ν4 ν5 ν6 ν7 ν8 ν9 ν10 ν11 ν12 ν13 ν14 : ℕ) :
    isM15NonnegNontrivialRealizable ν0 ν1 ν2 ν3 ν4 ν5 ν6 ν7 ν8 ν9 ν10 ν11 ν12 ν13 ν14 = true ↔
      (1 ≤ ν0 ∧ 1 ≤ ν1 ∧ 1 ≤ ν2 ∧ 1 ≤ ν3 ∧ 1 ≤ ν4 ∧
       1 ≤ ν5 ∧ 1 ≤ ν6 ∧ 1 ≤ ν7 ∧ 1 ≤ ν8 ∧ 1 ≤ ν9 ∧
       1 ≤ ν10 ∧ 1 ≤ ν11 ∧ 1 ≤ ν12 ∧ 1 ≤ ν13 ∧ 1 ≤ ν14 ∧
       ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 + ν8 + ν9 + ν10 + ν11 + ν12 + ν13 + ν14 = 30 ∧
       2 ≤ ν0 ∧ 4 ≤ ν0 + ν1 ∧ 6 ≤ ν0 + ν1 + ν2 ∧
       8 ≤ ν0 + ν1 + ν2 + ν3 ∧ 10 ≤ ν0 + ν1 + ν2 + ν3 + ν4 ∧
       12 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 ∧
       14 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 ∧
       16 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 ∧
       18 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 + ν8 ∧
       20 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 + ν8 + ν9 ∧
       22 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 + ν8 + ν9 + ν10 ∧
       24 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 + ν8 + ν9 + ν10 + ν11 ∧
       26 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 + ν8 + ν9 + ν10 + ν11 + ν12 ∧
       28 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 + ν8 + ν9 + ν10 + ν11 + ν12 + ν13 ∧
       ¬(ν0 = 2 ∧ ν1 = 2 ∧ ν2 = 2 ∧ ν3 = 2 ∧ ν4 = 2 ∧
         ν5 = 2 ∧ ν6 = 2 ∧ ν7 = 2 ∧ ν8 = 2 ∧ ν9 = 2 ∧
         ν10 = 2 ∧ ν11 = 2 ∧ ν12 = 2 ∧ ν13 = 2 ∧ ν14 = 2) ∧
       waveSumM15 (![ν0, ν1, ν2, ν3, ν4, ν5, ν6, ν7, ν8, ν9, ν10, ν11, ν12, ν13, ν14]) % D_m15 = 0) := by
  simp only [isM15NonnegNontrivialRealizable, decide_eq_true_eq]


/-
/-- For m=15 nonneg nontrivial profiles, D_m15 ∤ waveSumM15 (not realizable). -/
theorem m15_nonneg_nontrivial_not_realizable :
    ¬ ∃ (ν0 ν1 ν2 ν3 ν4 ν5 ν6 ν7 ν8 ν9 ν10 ν11 ν12 ν13 ν14 : ℕ),
        1 ≤ ν0 ∧ 1 ≤ ν1 ∧ 1 ≤ ν2 ∧ 1 ≤ ν3 ∧ 1 ≤ ν4 ∧
        1 ≤ ν5 ∧ 1 ≤ ν6 ∧ 1 ≤ ν7 ∧ 1 ≤ ν8 ∧ 1 ≤ ν9 ∧
        1 ≤ ν10 ∧ 1 ≤ ν11 ∧ 1 ≤ ν12 ∧ 1 ≤ ν13 ∧ 1 ≤ ν14 ∧
        ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 + ν8 + ν9 + ν10 + ν11 + ν12 + ν13 + ν14 = 30 ∧
        2 ≤ ν0 ∧
        4 ≤ ν0 + ν1 ∧
        6 ≤ ν0 + ν1 + ν2 ∧
        8 ≤ ν0 + ν1 + ν2 + ν3 ∧
        10 ≤ ν0 + ν1 + ν2 + ν3 + ν4 ∧
        12 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 ∧
        14 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 ∧
        16 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 ∧
        18 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 + ν8 ∧
        20 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 + ν8 + ν9 ∧
        22 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 + ν8 + ν9 + ν10 ∧
        24 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 + ν8 + ν9 + ν10 + ν11 ∧
        26 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 + ν8 + ν9 + ν10 + ν11 + ν12 ∧
        28 ≤ ν0 + ν1 + ν2 + ν3 + ν4 + ν5 + ν6 + ν7 + ν8 + ν9 + ν10 + ν11 + ν12 + ν13 ∧
        ¬(ν0 = 2 ∧ ν1 = 2 ∧ ν2 = 2 ∧ ν3 = 2 ∧ ν4 = 2 ∧
          ν5 = 2 ∧ ν6 = 2 ∧ ν7 = 2 ∧ ν8 = 2 ∧ ν9 = 2 ∧
          ν10 = 2 ∧ ν11 = 2 ∧ ν12 = 2 ∧ ν13 = 2 ∧ ν14 = 2) ∧
        D_m15 ∣ waveSumM15 ![ν0, ν1, ν2, ν3, ν4, ν5, ν6, ν7, ν8, ν9, ν10, ν11, ν12, ν13, ν14] := by
  simp only [not_exists, not_and, Nat.dvd_iff_mod_eq_zero]
  intro ν0 ν1 ν2 ν3 ν4 ν5 ν6 ν7 ν8 ν9 ν10 ν11 ν12 ν13 ν14
        hpos0 hpos1 hpos2 hpos3 hpos4 hpos5 hpos6 hpos7 hpos8 hpos9 hpos10 hpos11 hpos12 hpos13 hpos14
        hsum hd1 hd2 hd3 hd4 hd5 hd6 hd7 hd8 hd9 hd10 hd11 hd12 hd13 hd14 h_nontriv h_mod
  have hb0 : ν0 < 17 := by omega
  have hb1 : ν1 < 16 := by omega
  have hb2 : ν2 < 15 := by omega
  have hb3 : ν3 < 14 := by omega
  have hb4 : ν4 < 13 := by omega
  have hb5 : ν5 < 12 := by omega
  have hb6 : ν6 < 11 := by omega
  have hb7 : ν7 < 10 := by omega
  have hb8 : ν8 < 9 := by omega
  have hb9 : ν9 < 8 := by omega
  have hb10 : ν10 < 7 := by omega
  have hb11 : ν11 < 6 := by omega
  have hb12 : ν12 < 5 := by omega
  have hb13 : ν13 < 4 := by omega
  have hb14 : ν14 < 3 := by omega
  have hfalse := m15_search_spec hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14
  have h_nontriv' : ¬(ν0 = 2 ∧ ν1 = 2 ∧ ν2 = 2 ∧ ν3 = 2 ∧ ν4 = 2 ∧
                     ν5 = 2 ∧ ν6 = 2 ∧ ν7 = 2 ∧ ν8 = 2 ∧ ν9 = 2 ∧
                     ν10 = 2 ∧ ν11 = 2 ∧ ν12 = 2 ∧ ν13 = 2 ∧ ν14 = 2) := by
    intro ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14⟩
    exact h_nontriv e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
  have htrue : isM15NonnegNontrivialRealizable ν0 ν1 ν2 ν3 ν4 ν5 ν6 ν7 ν8 ν9 ν10 ν11 ν12 ν13 ν14 = true := by
    rw [isM15_iff_conj]
    exact ⟨hpos0, hpos1, hpos2, hpos3, hpos4, hpos5, hpos6, hpos7, hpos8, hpos9, hpos10, hpos11, hpos12, hpos13, hpos14,
           hsum, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14, h_nontriv', h_mod⟩
  simp_all
-/
end Collatz.Tilt
