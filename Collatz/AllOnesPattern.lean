/-
Copyright (c) 2024. All rights reserved.
Released under MIT license.
-/
import Collatz.PatternDefs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Log

/-!
# All-Ones Pattern Analysis

This file contains the analysis of the all-ones pattern [1, 1, ..., 1] for the Collatz conjecture.
The all-ones pattern is the unique subcritical pattern with sum equal to length, and plays a key
role in the divergence argument.

## Main Results

- `allOnesPattern_subcritical`: The all-ones pattern is subcritical for m ≥ 1
- `valid_pattern_sum_eq_length_implies_allOnes`: Any valid pattern with sum = length must be all-ones
- `waveSumPattern_allOnes`: The wave sum for all-ones is 3^m - 2^m
- `patternConstraint_allOnes`: The constraint for all-ones equals 2^m - 1
- `allOnes_constraint_grows`: For large m, the all-ones constraint exceeds any fixed n₀

-/

namespace Collatz

open scoped BigOperators

/-- The all-1 pattern of length m: [1, 1, ..., 1] -/
def allOnesPattern (m : ℕ) : List ℕ := List.replicate m 1

/-- All-1 pattern has length m -/
@[simp] lemma allOnesPattern_length (m : ℕ) : (allOnesPattern m).length = m := by
  unfold allOnesPattern; simp

/-- All-1 pattern sum equals m -/
@[simp] lemma allOnesPattern_sum (m : ℕ) : patternSum (allOnesPattern m) = m := by
  unfold patternSum allOnesPattern
  simp only [List.sum_replicate, smul_eq_mul, mul_one]

/-- All-1 pattern is valid -/
lemma allOnesPattern_valid (m : ℕ) : isValidPattern (allOnesPattern m) := by
  unfold isValidPattern allOnesPattern
  intro ν hν
  simp only [List.mem_replicate] at hν
  obtain ⟨_, heq⟩ := hν
  omega

/-- All-1 pattern is subcritical for m ≥ 1 (since 2^m < 3^m for all m ≥ 1) -/
lemma allOnesPattern_subcritical {m : ℕ} (hm : 1 ≤ m) : isSubcriticalPattern (allOnesPattern m) := by
  constructor
  · exact allOnesPattern_valid m
  · simp only [allOnesPattern_length, allOnesPattern_sum]
    -- 2^m < 3^m for m ≥ 1 (standard arithmetic)
    -- Use (2/3)^m < 1, equivalently 2^m < 3^m
    have h23 : (2 : ℕ) < 3 := by omega
    exact Nat.pow_lt_pow_left h23 (by omega : m ≠ 0)

/-- If a valid pattern has sum = length, it must be the all-1 pattern.
    Proof: Each element is ≥ 1 (valid), and sum = length means average = 1, so each = 1. -/
lemma valid_pattern_sum_eq_length_implies_allOnes (σ : List ℕ) (hvalid : isValidPattern σ)
    (hsum : patternSum σ = σ.length) : σ = allOnesPattern σ.length := by
  unfold allOnesPattern
  apply List.ext_getElem
  · simp
  intro i hi _
  simp only [List.getElem_replicate]
  -- Each element is ≥ 1 (valid) and sum = length implies each = 1
  have h_ge_1 : σ[i] ≥ 1 := hvalid σ[i] (List.getElem_mem hi)
  by_contra h_ne_1
  push_neg at h_ne_1
  have h_gt_1 : σ[i] > 1 := by omega
  -- If some σ[i] > 1 and all σ[j] ≥ 1, then sum > length
  have h_sum_gt : σ.sum > σ.length := by
    -- Helper lemma: for any list where all elements ≥ 1, sum ≥ length
    have sum_ge_len_aux : ∀ (l : List ℕ), (∀ x, x ∈ l → x ≥ 1) → l.sum ≥ l.length := by
      intro l
      induction l with
      | nil => simp
      | cons x xs ih =>
        intro h_all
        simp only [List.sum_cons, List.length_cons]
        have hx : x ≥ 1 := h_all x (by simp)
        have hxs : xs.sum ≥ xs.length := ih (fun y hy => h_all y (by simp [hy]))
        omega
    have h_sum_ge_len : σ.sum ≥ σ.length := sum_ge_len_aux σ hvalid
    -- Since σ[i] > 1 and sum ≥ length, we get sum > length
    -- Split list: σ.sum = take.sum + σ[i] + drop.sum
    have h_split : σ.sum = (σ.take i).sum + σ[i] + (σ.drop (i + 1)).sum := by
      -- Split list sum via take/drop decomposition
      have h1 : σ = σ.take i ++ σ.drop i := (List.take_append_drop i σ).symm
      have hdrop : σ.drop i = σ[i] :: σ.drop (i + 1) := List.drop_eq_getElem_cons hi
      have hsum1 : σ.sum = (σ.take i).sum + (σ.drop i).sum := by
        conv_lhs => rw [h1]; rw [List.sum_append]
      have hsum2 : (σ.drop i).sum = σ[i] + (σ.drop (i + 1)).sum := by
        rw [hdrop, List.sum_cons]
      omega
    have h_take_ge : (σ.take i).sum ≥ (σ.take i).length := by
      apply sum_ge_len_aux
      intro x hx
      exact hvalid x (List.mem_of_mem_take hx)
    have h_drop_ge : (σ.drop (i + 1)).sum ≥ (σ.drop (i + 1)).length := by
      apply sum_ge_len_aux
      intro x hx
      exact hvalid x (List.mem_of_mem_drop hx)
    have h_take_len : (σ.take i).length = i := List.length_take_of_le (by omega : i ≤ σ.length)
    have h_drop_len : (σ.drop (i + 1)).length = σ.length - (i + 1) := by simp [List.length_drop]
    calc σ.sum = (σ.take i).sum + σ[i] + (σ.drop (i + 1)).sum := h_split
      _ ≥ (σ.take i).length + σ[i] + (σ.drop (i + 1)).length := by omega
      _ = i + σ[i] + (σ.length - (i + 1)) := by rw [h_take_len, h_drop_len]
      _ ≥ i + 2 + (σ.length - (i + 1)) := by omega
      _ = σ.length + 1 := by omega
      _ > σ.length := by omega
  unfold patternSum at hsum
  omega

/-- Partial ν-sum for all-1 pattern equals j (capped at m) -/
lemma partialNuSum_allOnes (m j : ℕ) : partialNuSum (allOnesPattern m) j = min j m := by
  unfold partialNuSum allOnesPattern
  simp only [List.take_replicate, List.sum_replicate, smul_eq_mul, mul_one]

/-- Geometric series identity: Σⱼ₌₀^{m-1} 3^{m-1-j} · 2^j = 3^m - 2^m
    Proved by induction: Base empty sum = 0 = 1-1. Step uses 3·(3^n - 2^n) + 2^n = 3^{n+1} - 2^{n+1}. -/
lemma geom_series_3_2 (m : ℕ) :
    ((List.range m).map (fun j => 3^(m - 1 - j) * 2^j)).sum = 3^m - 2^m := by
  induction m with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.map_singleton, List.sum_append,
               List.sum_singleton, Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
    -- The earlier terms: 3^{n-j} = 3 * 3^{n-1-j} for j < n
    have hearly : ((List.range n).map (fun j => 3^(n - j) * 2^j)).sum =
                  3 * ((List.range n).map (fun j => 3^(n - 1 - j) * 2^j)).sum := by
      have hmapeq : (List.range n).map (fun j => 3^(n - j) * 2^j) =
                    (List.range n).map (fun j => 3 * (3^(n - 1 - j) * 2^j)) := by
        apply List.map_congr_left
        intro j hj
        simp only [List.mem_range] at hj
        have h1 : n - j = (n - 1 - j) + 1 := by omega
        rw [h1, pow_succ']
        ring
      rw [hmapeq]
      simp only [List.sum_map_mul_left]
    rw [hearly, ih]
    -- Now: 3 * (3^n - 2^n) + 2^n = 3^{n+1} - 2^{n+1}
    have h3 : 3^n ≥ 2^n := Nat.pow_le_pow_left (by omega : 2 ≤ 3) n
    have h4 : 3^(n+1) ≥ 2^(n+1) := Nat.pow_le_pow_left (by omega : 2 ≤ 3) (n+1)
    omega

/-- For all-1 pattern, partialNuSum at position j equals j (when j ≤ m) -/
lemma partialNuSum_allOnes_eq (m j : ℕ) (hj : j ≤ m) : partialNuSum (allOnesPattern m) j = j := by
  simp [partialNuSum, allOnesPattern, List.take_replicate, List.sum_replicate, smul_eq_mul, mul_one,
        min_eq_left hj]

/-- Wave sum for all-1 pattern: c = Σⱼ 3^{m-1-j} · 2^j = 3^m - 2^m -/
lemma waveSumPattern_allOnes (m : ℕ) : waveSumPattern (allOnesPattern m) = 3^m - 2^m := by
  unfold waveSumPattern
  simp only [allOnesPattern_length]
  -- Show the summand equals the geometric series term
  have hmap : (List.range m).map (fun j => 3 ^ (m - 1 - j) * 2 ^ partialNuSum (allOnesPattern m) j) =
              (List.range m).map (fun j => 3^(m - 1 - j) * 2^j) := by
    apply List.map_congr_left
    intro j hj
    simp only [List.mem_range] at hj
    rw [partialNuSum_allOnes_eq m j (Nat.le_of_lt hj)]
  rw [hmap, geom_series_3_2]

/-- The constraint for all-1 pattern equals 2^m - 1 mod 2^m

    Proof sketch: The wave sum is 3^m - 2^m. The constraint is
    -(3^m - 2^m) · (3^m)^{-1} mod 2^m = -1 mod 2^m = 2^m - 1.
    This uses that 2^m ≡ 0 (mod 2^m) and 3^m is invertible mod 2^m. -/
lemma patternConstraint_allOnes (m : ℕ) (hm : 1 ≤ m) :
    (patternConstraint (allOnesPattern m)).val = 2^m - 1 := by
  have hsum : patternSum (allOnesPattern m) = m := allOnesPattern_sum m
  have hlen : (allOnesPattern m).length = m := allOnesPattern_length m
  have hwave : waveSumPattern (allOnesPattern m) = 3^m - 2^m := waveSumPattern_allOnes m
  have h3m_ge_2m : 3^m ≥ 2^m := Nat.pow_le_pow_left (by omega : 2 ≤ 3) m
  have h2m_zero : ((2^m : ℕ) : ZMod (2^m)) = 0 := ZMod.natCast_self (2^m)
  have hcast : ((3^m - 2^m : ℕ) : ZMod (2^m)) = ((3^m : ℕ) : ZMod (2^m)) := by
    rw [Nat.cast_sub h3m_ge_2m]; simp only [h2m_zero, sub_zero]
  have h_neg_one_val : ((-1 : ZMod (2^m))).val = 2^m - 1 := by
    have h2m_pos : 0 < 2^m := Nat.two_pow_pos m
    have h2m_succ : 2^m = (2^m - 1).succ := Nat.succ_pred_eq_of_pos h2m_pos |>.symm
    conv_lhs => rw [h2m_succ]; exact ZMod.val_neg_one (2^m - 1)
  have h_coprime : Nat.Coprime (3^m) (2^m) := Nat.Coprime.pow m m (by decide : Nat.Coprime 3 2)
  have h_inv : ((3^m : ℕ) : ZMod (2^m)) * ((3^m : ℕ) : ZMod (2^m))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ (ZMod.unitOfCoprime (3^m) h_coprime).isUnit
  -- Prove the result directly
  unfold patternConstraint
  simp only [hlen]
  -- The key step: convert goal to use m instead of patternSum (allOnesPattern m)
  conv_lhs => rw [hsum]
  -- Now goal is in ZMod (2^m)
  -- Goal is: (-↑(waveSumPattern (allOnesPattern m)) * (↑(3^m))⁻¹).val = 2^m - 1
  simp only [hwave]
  -- Now: (-↑(3^m - 2^m) * (↑(3^m))⁻¹).val = 2^m - 1
  -- Rewrite under the negation: ↑(3^m - 2^m) = ↑(3^m)
  conv_lhs => arg 1; arg 1; rw [hcast]
  -- Now: (-↑(3^m) * (↑(3^m))⁻¹).val = 2^m - 1
  rw [neg_mul, h_inv, h_neg_one_val]

/-- Key lemma: For large m, the all-1 pattern constraint exceeds n₀ -/
lemma allOnes_constraint_grows {n₀ : ℕ} (hn₀ : 0 < n₀) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, 1 ≤ m → (patternConstraint (allOnesPattern m)).val > n₀ := by
  use Nat.log 2 n₀ + 2
  intro m hm hm_pos
  rw [patternConstraint_allOnes m hm_pos]
  have hm_ge : m ≥ Nat.log 2 n₀ + 2 := hm
  have h_log : n₀ < 2^(Nat.log 2 n₀ + 1) := Nat.lt_pow_succ_log_self (by omega) n₀
  have h1 : n₀ < 2^(m - 1) := Nat.lt_of_lt_of_le h_log (Nat.pow_le_pow_right (by omega) (by omega))
  have h2m_pos : 0 < 2^m := Nat.two_pow_pos m
  have h_m1_lt : 2^(m-1) ≤ 2^m - 1 := by
    have h2pow : 2^m = 2 * 2^(m-1) := by
      have hm1 : m = m - 1 + 1 := by omega
      calc 2^m = 2^(m - 1 + 1) := by rw [← hm1]
           _ = 2^(m-1) * 2 := Nat.pow_succ _ _
           _ = 2 * 2^(m-1) := by ring
    omega
  omega

/-- The all-1 pattern constraint eventually misses any fixed n₀.
    For m > log₂(n₀) + 1, the constraint is 2^m - 1 > n₀, so n₀ ≠ constraint in ZMod. -/
lemma allOnes_constraint_eventually_misses (n₀ : ℕ) (hn₀ : 0 < n₀) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, (n₀ : ZMod (2^(patternSum (allOnesPattern m)))) ≠
      patternConstraint (allOnesPattern m) := by
  -- Use m₀ = log₂(n₀) + 2
  use Nat.log 2 n₀ + 2
  intro m hm
  -- patternSum (allOnesPattern m) = m, so we're working in ZMod (2^m)
  have hsum : patternSum (allOnesPattern m) = m := allOnesPattern_sum m
  have hm_pos : 1 ≤ m := by omega
  -- The constraint value is 2^m - 1
  have h_constraint_val : (patternConstraint (allOnesPattern m)).val = 2^m - 1 :=
    patternConstraint_allOnes m hm_pos
  -- n₀ < 2^m for our choice of m₀
  have h_n0_lt_2m : n₀ < 2^m := by
    have h_log : n₀ < 2^(Nat.log 2 n₀ + 1) := Nat.lt_pow_succ_log_self (by omega) n₀
    calc n₀ < 2^(Nat.log 2 n₀ + 1) := h_log
         _ ≤ 2^m := Nat.pow_le_pow_right (by omega) (by omega)
  -- n₀ < 2^m - 1
  have h_2m_minus_1 : n₀ < 2^m - 1 := by
    have h1 : n₀ < 2^(m - 1) := by
      have h_log : n₀ < 2^(Nat.log 2 n₀ + 1) := Nat.lt_pow_succ_log_self (by omega) n₀
      calc n₀ < 2^(Nat.log 2 n₀ + 1) := h_log
           _ ≤ 2^(m - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2pow : 2^m = 2 * 2^(m-1) := by
      have hm1 : m = m - 1 + 1 := by omega
      calc 2^m = 2^(m - 1 + 1) := by rw [← hm1]
           _ = 2^(m-1) * 2 := Nat.pow_succ _ _
           _ = 2 * 2^(m-1) := by ring
    omega
  -- Now prove inequality by showing values differ
  intro heq
  -- Cast both sides to their canonical representatives
  have h_n0_val : (n₀ : ZMod (2^(patternSum (allOnesPattern m)))).val = n₀ := by
    rw [hsum]
    exact ZMod.val_natCast_of_lt h_n0_lt_2m
  have h_constraint_val' : (patternConstraint (allOnesPattern m)).val = 2^m - 1 := h_constraint_val
  -- If they're equal, their vals are equal
  have h_vals_eq : (n₀ : ZMod (2^(patternSum (allOnesPattern m)))).val =
                   (patternConstraint (allOnesPattern m)).val := by rw [heq]
  -- Simplify the goal using our equality facts
  rw [h_n0_val, h_constraint_val'] at h_vals_eq
  -- Now h_vals_eq : n₀ = 2^m - 1 contradicts h_2m_minus_1 : n₀ < 2^m - 1
  linarith

/-- Universal version of allOnes_constraint_eventually_misses at explicit cutoff.
    For m ≥ log n₀ + 2, the all-ones pattern constraint misses n₀. -/
lemma allOnes_constraint_mismatch_at_cutoff (n₀ : ℕ) (hn₀ : 0 < n₀)
    (m : ℕ) (hm : m ≥ Nat.log 2 n₀ + 2) :
    (n₀ : ZMod (2^(patternSum (allOnesPattern m)))) ≠ patternConstraint (allOnesPattern m) := by
  -- patternSum (allOnesPattern m) = m
  have hsum : patternSum (allOnesPattern m) = m := allOnesPattern_sum m
  have hm_pos : 1 ≤ m := by omega
  -- The constraint value is 2^m - 1
  have h_constraint_val : (patternConstraint (allOnesPattern m)).val = 2^m - 1 :=
    patternConstraint_allOnes m hm_pos
  -- n₀ < 2^m for our choice of cutoff
  have h_n0_lt_2m : n₀ < 2^m := by
    have h_log : n₀ < 2^(Nat.log 2 n₀ + 1) := Nat.lt_pow_succ_log_self (by omega) n₀
    calc n₀ < 2^(Nat.log 2 n₀ + 1) := h_log
         _ ≤ 2^m := Nat.pow_le_pow_right (by omega) (by omega)
  -- n₀ < 2^m - 1
  have h_2m_minus_1 : n₀ < 2^m - 1 := by
    have h1 : n₀ < 2^(m - 1) := by
      have h_log : n₀ < 2^(Nat.log 2 n₀ + 1) := Nat.lt_pow_succ_log_self (by omega) n₀
      calc n₀ < 2^(Nat.log 2 n₀ + 1) := h_log
           _ ≤ 2^(m - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2pow : 2^m = 2 * 2^(m-1) := by
      have hm1 : m = m - 1 + 1 := by omega
      calc 2^m = 2^(m - 1 + 1) := by rw [← hm1]
           _ = 2^(m-1) * 2 := Nat.pow_succ _ _
           _ = 2 * 2^(m-1) := by ring
    omega
  -- Prove inequality
  intro heq
  have h_n0_val : (n₀ : ZMod (2^(patternSum (allOnesPattern m)))).val = n₀ := by
    rw [hsum]
    exact ZMod.val_natCast_of_lt h_n0_lt_2m
  have h_vals_eq : (n₀ : ZMod (2^(patternSum (allOnesPattern m)))).val =
                   (patternConstraint (allOnesPattern m)).val := by rw [heq]
  rw [h_n0_val, h_constraint_val] at h_vals_eq
  linarith

end Collatz
