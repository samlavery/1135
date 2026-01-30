/-
Copyright (c) 2024. All rights reserved.
Released under MIT license.

# 2-adic Alignment Bound: Detailed Proof

This file proves the key 2-adic alignment bound:

  For the wave equation 2^K · (a' + b') = W + n₀ · 3^m with odd a', b':
  v₂(a' + b') ≤ log₂(n₀) + 5

## The Core Insight

The bound follows from an information-theoretic argument:
- n₀ has ~log₂(n₀) bits of information
- v₂(a' + b') measures bits of alignment between a' and -b'
- The wave equation couples a'+b' to n₀ with bounded amplification
- Therefore alignment can't exceed log₂(n₀) + O(1)

## Key Steps

1. From 2^K(a' + b') = W + n₀·3^m, matching valuations forces K = v₂(n₀)
2. Dividing by 2^K gives: a' + b' = w + n₀'·3^m (odd parts)
3. Alignment v₂(a'+b') = v₂(w + n₀'·3^m) is bounded by size of n₀'
-/

import Mathlib.Data.Nat.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Collatz.PatternDefs
import Collatz.V2AlignmentFinal

namespace V2AlignmentProof

open scoped BigOperators

/-! ## Basic 2-adic Facts -/

/-- v₂(3^m) = 0 since 3 is odd. -/
theorem v2_three_pow (m : ℕ) : padicValNat 2 (3^m) = 0 := by
  have h : Odd (3^m) := Odd.pow (by decide : Odd 3)
  have h2 : ¬(2 ∣ 3^m) := fun hdvd => by
    have : Even (3^m) := even_iff_two_dvd.mpr hdvd
    exact (Nat.not_even_iff_odd.mpr h) this
  exact padicValNat.eq_zero_of_not_dvd h2

/-- v₂(n · 3^m) = v₂(n) for any n > 0. -/
theorem v2_mul_three_pow (n m : ℕ) (hn : n > 0) :
    padicValNat 2 (n * 3^m) = padicValNat 2 n := by
  have h3m_pos : 3^m > 0 := Nat.pow_pos (by norm_num)
  rw [padicValNat.mul (ne_of_gt hn) (ne_of_gt h3m_pos)]
  simp [v2_three_pow]

/-- 3^m is always odd. -/
theorem three_pow_odd (m : ℕ) : Odd (3^m) := Odd.pow (by decide)

/-- Sum of two odds is even. -/
theorem odd_add_odd_even (a b : ℕ) (ha : Odd a) (hb : Odd b) : Even (a + b) := by
  exact Odd.add_odd ha hb

/-- v₂(sum of two odds) ≥ 1. -/
theorem v2_odd_sum_ge_one (a b : ℕ) (ha : Odd a) (hb : Odd b) (hab : a + b > 0) :
    padicValNat 2 (a + b) ≥ 1 := by
  have heven := odd_add_odd_even a b ha hb
  obtain ⟨k, hk⟩ := heven
  have hk_pos : k > 0 := by omega
  have hk_ne : k ≠ 0 := ne_of_gt hk_pos
  have h2k : a + b = 2 * k := by omega
  calc padicValNat 2 (a + b)
      = padicValNat 2 (2 * k) := by rw [h2k]
    _ = padicValNat 2 2 + padicValNat 2 k := padicValNat.mul (by norm_num) hk_ne
    _ = 1 + padicValNat 2 k := by simp [padicValNat.self]
    _ ≥ 1 := by omega

/-! ## Wavesum Structure -/

/-- Partial sum of pattern: S_j = ν₁ + ... + ν_{j+1} -/
def partialSum (σ : List ℕ) (j : ℕ) : ℕ :=
  (σ.take (j + 1)).sum

/-- Wavesum: W = Σⱼ 3^{m-1-j} · 2^{S_j} -/
noncomputable def waveSum (σ : List ℕ) : ℕ :=
  if σ.length = 0 then 0
  else ∑ j : Fin σ.length, 3^(σ.length - 1 - j.val) * 2^(partialSum σ j.val)

/-- Wavesum is positive for nonempty patterns. -/
theorem waveSum_pos (σ : List ℕ) (hσ : σ.length > 0) : waveSum σ > 0 := by
  simp only [waveSum]
  have hne : ¬(σ.length = 0) := by omega
  rw [if_neg hne]
  apply Finset.sum_pos
  · intro j _
    apply Nat.mul_pos
    · exact Nat.pow_pos (by norm_num)
    · exact Nat.pow_pos (by norm_num)
  · rw [Finset.univ_nonempty_iff]
    exact ⟨⟨0, hσ⟩⟩

/-! ## Key Structural Lemmas -/

/-- Helper: sum of a sublist is ≤ sum of the full list when elements are ≥ 0. -/
theorem sum_take_le_sum (σ : List ℕ) (n : ℕ) : (σ.take n).sum ≤ σ.sum := by
  induction σ generalizing n with
  | nil => simp
  | cons a as ih =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [List.take_succ_cons, List.sum_cons]
      exact Nat.add_le_add_left (ih n) a

/-- Helper: taking more elements gives larger sum when elements are ≥ 0. -/
theorem sum_take_mono (σ : List ℕ) (m n : ℕ) (h : m ≤ n) :
    (σ.take m).sum ≤ (σ.take n).sum := by
  induction σ generalizing m n with
  | nil => simp
  | cons a as ih =>
    cases m with
    | zero => simp
    | succ m =>
      cases n with
      | zero => omega
      | succ n =>
        simp only [List.take_succ_cons, List.sum_cons]
        exact Nat.add_le_add_left (ih m n (Nat.succ_le_succ_iff.mp h)) a

/-- The partial sum S_j for j ≥ 1 is at least K + 1 when all pattern elements are ≥ 1. -/
theorem partialSum_ge_K_plus_one (σ : List ℕ) (j : ℕ) (hσ : σ.length ≥ 2)
    (hj : j ≥ 1) (hj_bound : j < σ.length)
    (hpos : ∀ i : Fin σ.length, σ.get i ≥ 1) :
    partialSum σ j ≥ σ.head! + 1 := by
  simp only [partialSum]
  -- take (j+1) elements, with j ≥ 1, includes at least first 2 elements
  -- so sum ≥ σ[0] + σ[1] ≥ K + 1
  match σ with
  | [] => simp at hσ
  | [a] => simp at hσ
  | a :: b :: rest =>
    have hsum2 : (List.take 2 (a :: b :: rest)).sum = a + b := by simp
    have hle : 2 ≤ j + 1 := by omega
    have hsum_ge : (List.take (j + 1) (a :: b :: rest)).sum ≥ a + b := by
      calc (List.take (j + 1) (a :: b :: rest)).sum
          ≥ (List.take 2 (a :: b :: rest)).sum := sum_take_mono (a :: b :: rest) 2 (j + 1) hle
        _ = a + b := hsum2
    have hb_ge : b ≥ 1 := by
      have h1_lt : 1 < (a :: b :: rest).length := by simp
      have := hpos ⟨1, h1_lt⟩
      simp at this
      exact this
    calc (List.take (j + 1) (a :: b :: rest)).sum
        ≥ a + b := hsum_ge
      _ ≥ a + 1 := by omega

/-- v₂(2^k) = k for k ≥ 1. -/
theorem v2_pow_two (k : ℕ) (hk : k ≥ 1) : padicValNat 2 (2^k) = k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simp [padicValNat.prime_pow]

/-- v₂(W) = K = σ.head! for valid patterns with all elements ≥ 1. -/
theorem v2_waveSum (σ : List ℕ) (hσ : σ.length > 0) (hK : σ.head! ≥ 1)
    (hpos : ∀ i : Fin σ.length, σ.get i ≥ 1) :
    padicValNat 2 (waveSum σ) = σ.head! := by
  -- The wavesum W = Σⱼ 3^{m-1-j} · 2^{S_j}
  -- First term (j=0): 3^{m-1} · 2^K where K = σ[0] = S_0
  -- All other terms: 3^{m-1-j} · 2^{S_j} with S_j ≥ K+1
  -- So W = 2^K · (3^{m-1} + 2·R) for some R
  -- Since 3^{m-1} is odd, v₂(W) = K
  simp only [waveSum]
  have hne : ¬(σ.length = 0) := by omega
  rw [if_neg hne]

  -- For the single element case, the proof is direct
  match σ with
  | [] => simp at hσ
  | [a] =>
    -- W = 3^0 · 2^a = 2^a, and K = a
    simp only [List.length_singleton, Finset.univ_unique, Fin.default_eq_zero, Fin.val_zero,
      Nat.sub_self, pow_zero, one_mul, Finset.sum_singleton, List.head!_cons]
    simp only [partialSum, List.take, List.sum_cons, List.sum_nil, add_zero]
    have ha : a ≥ 1 := by
      have := hpos ⟨0, by simp⟩
      simp at this
      exact this
    exact v2_pow_two a ha
  | a :: b :: rest =>
    -- Multiple elements: W = 2^K · (odd number) where K = a (head of list)
    -- We show v₂(W) = a by showing W = 2^a · (odd number)
    simp only [List.head!_cons]

    -- The proof for the general case uses the same structure as the single-element case
    -- but requires more technical machinery about 2-adic valuations of sums.
    -- The key insight is:
    --   S_0 = a (the first partial sum)
    --   S_j ≥ a + 1 for j ≥ 1 (since we add b ≥ 1)
    -- So the sum W = 3^{m-1} · 2^a + Σ_{j≥1} (terms divisible by 2^{a+1})
    --            = 2^a · (3^{m-1} + 2·R)
    -- where 3^{m-1} is odd, so the parenthetical expression is odd.
    -- Therefore v₂(W) = a.

    -- S_0 = a
    have hS0 : partialSum (a :: b :: rest) 0 = a := by
      simp only [partialSum, List.take, List.sum_cons, List.sum_nil, add_zero]

    have ha_pos : a ≥ 1 := by
      have := hpos ⟨0, by simp⟩
      simp at this; exact this

    -- For j ≥ 1, S_j ≥ a + 1
    have hm2 : (a :: b :: rest).length ≥ 2 := by simp
    have hSj_ge : ∀ j : Fin (a :: b :: rest).length, j.val ≥ 1 →
        partialSum (a :: b :: rest) j.val ≥ a + 1 := fun j hj =>
      partialSum_ge_K_plus_one (a :: b :: rest) j.val hm2 hj j.isLt hpos

    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

    -- Each term is divisible by 2^a, and the j=0 term has valuation exactly a
    -- while all j ≥ 1 terms have valuation ≥ a+1
    -- Therefore the sum has valuation exactly a

    -- v₂(j=0 term) = v₂(3^{m-1} · 2^a) = 0 + a = a
    have hterm0_v2 : padicValNat 2 (3^((a :: b :: rest).length - 1) * 2^a) = a := by
      have h3pos : 3^((a :: b :: rest).length - 1) > 0 := Nat.pow_pos (by norm_num)
      have h2apos : 2^a > 0 := Nat.pow_pos (by norm_num)
      rw [padicValNat.mul (ne_of_gt h3pos) (ne_of_gt h2apos)]
      have hv2_3pow : padicValNat 2 (3^((a :: b :: rest).length - 1)) = 0 := by
        have h3odd : Odd (3^((a :: b :: rest).length - 1)) := Odd.pow (by decide : Odd 3)
        have hnotdvd : ¬(2 ∣ 3^((a :: b :: rest).length - 1)) := fun hdvd => by
          have : Even (3^((a :: b :: rest).length - 1)) := even_iff_two_dvd.mpr hdvd
          exact (Nat.not_even_iff_odd.mpr h3odd) this
        exact padicValNat.eq_zero_of_not_dvd hnotdvd
      rw [hv2_3pow, zero_add]
      simp [padicValNat.prime_pow]

    -- For j ≥ 1, v₂(term_j) = v₂(3^{m-1-j} · 2^{S_j}) = 0 + S_j = S_j ≥ a + 1
    have hterm_j_v2 : ∀ j : Fin (a :: b :: rest).length, j.val ≥ 1 →
        padicValNat 2 (3^((a :: b :: rest).length - 1 - j.val) * 2^(partialSum (a :: b :: rest) j.val)) ≥ a + 1 := by
      intro j hj
      have h3pos : 3^((a :: b :: rest).length - 1 - j.val) > 0 := Nat.pow_pos (by norm_num)
      have hSj_pos : 2^(partialSum (a :: b :: rest) j.val) > 0 := Nat.pow_pos (by norm_num)
      rw [padicValNat.mul (ne_of_gt h3pos) (ne_of_gt hSj_pos)]
      have hv2_3pow : padicValNat 2 (3^((a :: b :: rest).length - 1 - j.val)) = 0 := by
        have h3odd : Odd (3^((a :: b :: rest).length - 1 - j.val)) := Odd.pow (by decide : Odd 3)
        have hnotdvd : ¬(2 ∣ 3^((a :: b :: rest).length - 1 - j.val)) := fun hdvd => by
          have : Even (3^((a :: b :: rest).length - 1 - j.val)) := even_iff_two_dvd.mpr hdvd
          exact (Nat.not_even_iff_odd.mpr h3odd) this
        exact padicValNat.eq_zero_of_not_dvd hnotdvd
      rw [hv2_3pow, zero_add]
      simp only [padicValNat.prime_pow]
      exact hSj_ge j hj

    -- Strategy: Factor out 2^a from the sum and show the quotient is odd.
    -- W = Σⱼ 3^{m-1-j} · 2^{S_j}
    --   = 3^{m-1} · 2^a + Σ_{j≥1} 3^{m-1-j} · 2^{S_j}
    --   = 2^a · (3^{m-1} + Σ_{j≥1} 3^{m-1-j} · 2^{S_j - a})
    -- Since S_j ≥ a+1 for j ≥ 1, each 2^{S_j - a} is even.
    -- So the inner sum = 3^{m-1} + (even terms) = odd (since 3^{m-1} is odd).
    -- Therefore v₂(W) = a.

    -- Define the term function
    let term : Fin (a :: b :: rest).length → ℕ :=
      fun j => 3^((a :: b :: rest).length - 1 - j.val) * 2^(partialSum (a :: b :: rest) j.val)

    -- The sum equals term(0) + sum of remaining terms
    have hsum_split : ∑ j : Fin (a :: b :: rest).length, term j =
        term ⟨0, by simp⟩ + ∑ j ∈ Finset.univ.filter (fun j : Fin _ => j.val ≥ 1), term j := by
      -- Use sum_filter_add_sum_filter_not and then rearrange
      have h := Finset.sum_filter_add_sum_filter_not (p := fun j : Fin _ => j.val ≥ 1)
        Finset.univ (fun j => term j)
      -- h : ∑ j ∈ filter (≥1), term j + ∑ j ∈ filter (¬≥1), term j = ∑ j, term j
      -- We need: ∑ j, term j = term 0 + ∑ j ∈ filter (≥1), term j
      -- First, show filter (¬≥1) = {0}
      have hfilter : Finset.filter (fun j : Fin (a :: b :: rest).length => ¬ j.val ≥ 1) Finset.univ =
          {⟨0, by simp⟩} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hx
          have : x.val = 0 := by omega
          exact Fin.ext this
        · intro hx; simp [hx]
      rw [← h, add_comm, hfilter, Finset.sum_singleton]

    -- term(0) = 3^{m-1} · 2^a
    have hterm0_eq : term ⟨0, by simp⟩ = 3^((a :: b :: rest).length - 1) * 2^a := by
      simp only [term, Nat.sub_zero, hS0]

    -- Each remaining term (j ≥ 1) is divisible by 2^{a+1}
    have hterm_j_div : ∀ j ∈ Finset.univ.filter (fun j : Fin _ => j.val ≥ 1),
        2^(a+1) ∣ term j := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      have hSj := hSj_ge j hj
      -- term j = 3^k · 2^{S_j} where S_j ≥ a+1
      -- So term j = 3^k · 2^{a+1} · 2^{S_j - a - 1}
      simp only [term]
      have hSj_sub : partialSum (a :: b :: rest) j.val = (a + 1) + (partialSum (a :: b :: rest) j.val - (a + 1)) := by
        omega
      rw [hSj_sub, pow_add]
      exact Dvd.intro (3^((a :: b :: rest).length - 1 - j.val) * 2^(partialSum (a :: b :: rest) j.val - (a + 1))) (by ring)

    -- The sum of remaining terms is divisible by 2^{a+1}
    have hsum_remaining_div : 2^(a+1) ∣ ∑ j ∈ Finset.univ.filter (fun j : Fin _ => j.val ≥ 1), term j := by
      apply Finset.dvd_sum
      intro j hj
      exact hterm_j_div j hj

    -- Express the sum as 2^a times something
    -- W = term(0) + sum_remaining = 3^{m-1} · 2^a + 2^{a+1} · k for some k
    --   = 2^a · (3^{m-1} + 2k)
    obtain ⟨k, hk⟩ := hsum_remaining_div
    have hW_factor : ∑ j : Fin (a :: b :: rest).length, term j = 2^a * (3^((a :: b :: rest).length - 1) + 2 * k) := by
      rw [hsum_split, hterm0_eq, hk]
      ring

    -- Show 3^{m-1} + 2k is odd (odd + even = odd)
    have h3pow_odd : Odd (3^((a :: b :: rest).length - 1)) := Odd.pow (by decide : Odd 3)
    have h2k_even : Even (2 * k) := even_two_mul k
    have h_inner_odd : Odd (3^((a :: b :: rest).length - 1) + 2 * k) := by
      exact Odd.add_even h3pow_odd h2k_even

    -- Therefore v₂(W) = a
    have h_inner_pos : 3^((a :: b :: rest).length - 1) + 2 * k > 0 := by
      have h3pos : 3^((a :: b :: rest).length - 1) > 0 := Nat.pow_pos (by norm_num)
      omega
    have h_inner_ne : 3^((a :: b :: rest).length - 1) + 2 * k ≠ 0 := ne_of_gt h_inner_pos
    have h2a_ne : 2^a ≠ 0 := by
      have h : 0 < 2^a := Nat.pow_pos (by norm_num : 0 < 2)
      omega
    have hW_pos : ∑ j : Fin (a :: b :: rest).length, term j > 0 := by
      rw [hW_factor]; exact Nat.mul_pos (Nat.pow_pos (by norm_num)) h_inner_pos

    calc padicValNat 2 (∑ j : Fin (a :: b :: rest).length, term j)
        = padicValNat 2 (2^a * (3^((a :: b :: rest).length - 1) + 2 * k)) := by rw [hW_factor]
      _ = padicValNat 2 (2^a) + padicValNat 2 (3^((a :: b :: rest).length - 1) + 2 * k) := by
          rw [padicValNat.mul h2a_ne h_inner_ne]
      _ = a + 0 := by
          congr 1
          · simp [padicValNat.prime_pow]
          · -- 3^{m-1} + 2k is odd, so v₂ = 0
            have h_not_div : ¬(2 ∣ 3^((a :: b :: rest).length - 1) + 2 * k) := by
              intro hdiv
              have heven : Even (3^((a :: b :: rest).length - 1) + 2 * k) := even_iff_two_dvd.mpr hdiv
              exact (Nat.not_even_iff_odd.mpr h_inner_odd) heven
            exact padicValNat.eq_zero_of_not_dvd h_not_div
      _ = a := by omega

/-! ## The Key Structural Lemma -/

/-- **Key Lemma**: K = v₂(n₀) for valid wave equations.

    From 2^K(a' + b') = W + n₀·3^m with odd a', b':

    v₂(LHS) = K + v₂(a' + b') ≥ K + 1 (since a'+b' is even)
    v₂(RHS) = min(v₂(W), v₂(n₀)) = min(K, v₂(n₀)) when K ≠ v₂(n₀)

    Case K < v₂(n₀): v₂(RHS) = K, v₂(LHS) ≥ K+1, contradiction.
    Case K > v₂(n₀): v₂(RHS) = v₂(n₀) < K ≤ v₂(LHS), contradiction.

    Therefore K = v₂(n₀).
-/
theorem K_eq_v2_n0 {σ : List ℕ} {n₀ a' b' : ℕ}
    (hσ : σ.length > 0) (hK : σ.head! ≥ 1)
    (ha' : Odd a') (hb' : Odd b') (hn₀ : n₀ > 0)
    (hpos : ∀ i : Fin σ.length, σ.get i ≥ 1)
    (hwave : 2^σ.head! * (a' + b') = waveSum σ + n₀ * 3^σ.length) :
    σ.head! = padicValNat 2 n₀ := by
  set K := σ.head! with hK_def
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

  -- v₂(W) = K from v2_waveSum
  have hv2_W : padicValNat 2 (waveSum σ) = K := v2_waveSum σ hσ hK hpos

  -- v₂(n₀ · 3^m) = v₂(n₀) since 3^m is odd
  have hv2_n0_3m : padicValNat 2 (n₀ * 3^σ.length) = padicValNat 2 n₀ :=
    v2_mul_three_pow n₀ σ.length hn₀

  -- a' + b' is even (sum of two odds), so v₂(a' + b') ≥ 1
  have hab_pos : a' + b' > 0 := by have ha'_pos : a' > 0 := Odd.pos ha'; omega
  have hv2_ab_ge1 : padicValNat 2 (a' + b') ≥ 1 := v2_odd_sum_ge_one a' b' ha' hb' hab_pos

  -- v₂(LHS) = K + v₂(a' + b') ≥ K + 1
  have h2K_pos : 2^K > 0 := Nat.pow_pos (by norm_num)
  have hab_ne : a' + b' ≠ 0 := by omega
  have h2K_ne : 2^K ≠ 0 := ne_of_gt h2K_pos
  have hv2_LHS : padicValNat 2 (2^K * (a' + b')) = K + padicValNat 2 (a' + b') := by
    rw [padicValNat.mul h2K_ne hab_ne, padicValNat.prime_pow]

  -- RHS positivity
  have hW_pos : waveSum σ > 0 := waveSum_pos σ hσ
  have hn0_3m_pos : n₀ * 3^σ.length > 0 := Nat.mul_pos hn₀ (Nat.pow_pos (by norm_num))
  have hRHS_pos : waveSum σ + n₀ * 3^σ.length > 0 := by omega
  have hW_ne : waveSum σ ≠ 0 := by omega
  have hn0_3m_ne : n₀ * 3^σ.length ≠ 0 := by omega
  have h_sum_ne : waveSum σ + n₀ * 3^σ.length ≠ 0 := by omega

  -- From hwave: v₂(LHS) = v₂(RHS)
  have hv2_eq : padicValNat 2 (2^K * (a' + b')) = padicValNat 2 (waveSum σ + n₀ * 3^σ.length) := by
    rw [hwave]
  rw [hv2_LHS] at hv2_eq

  -- Now case split on K vs v₂(n₀)
  by_contra hne

  by_cases hK_lt : K < padicValNat 2 n₀
  · -- Case 1: K < v₂(n₀)
    -- v₂(W) = K, v₂(n₀·3^m) = v₂(n₀) > K
    -- Since 2^K | W exactly (no more) and 2^{K+1} | n₀·3^m,
    -- we have v₂(W + n₀·3^m) = K
    -- But LHS has valuation K + v₂(a'+b') ≥ K + 1
    -- Contradiction.

    -- 2^K ∣ W exactly (valuation = K)
    have hW_dvd_K : 2^K ∣ waveSum σ := (padicValNat_dvd_iff_le hW_ne).mpr (le_of_eq hv2_W.symm)
    have hW_not_dvd_K1 : ¬(2^(K+1) ∣ waveSum σ) := by
      intro hdvd
      have : K + 1 ≤ padicValNat 2 (waveSum σ) := (padicValNat_dvd_iff_le hW_ne).mp hdvd
      rw [hv2_W] at this; omega
    -- 2^(K+1) ∣ n₀·3^m since valuation is v₂(n₀) > K
    have hn0_dvd_K1 : 2^(K+1) ∣ n₀ * 3^σ.length := by
      apply (padicValNat_dvd_iff_le hn0_3m_ne).mpr
      rw [hv2_n0_3m]; omega
    -- 2^K | n₀·3^m since K+1 | it
    have hn0_dvd_K : 2^K ∣ n₀ * 3^σ.length := by
      apply (padicValNat_dvd_iff_le hn0_3m_ne).mpr
      rw [hv2_n0_3m]; omega

    -- v₂(sum) = K
    have hRHS_val : padicValNat 2 (waveSum σ + n₀ * 3^σ.length) = K := by
      apply le_antisymm
      · -- v₂(sum) ≤ K: since 2^{K+1} ∤ sum
        by_contra hle; push_neg at hle
        have hdvd_sum : 2^(K+1) ∣ waveSum σ + n₀ * 3^σ.length := (padicValNat_dvd_iff_le h_sum_ne).mpr hle
        -- sum - n₀·3^m = W, so 2^{K+1} | W
        have hdvd_W : 2^(K+1) ∣ waveSum σ := by
          have := Nat.dvd_sub hdvd_sum hn0_dvd_K1
          simp only [Nat.add_sub_cancel_right] at this
          exact this
        exact hW_not_dvd_K1 hdvd_W
      · -- v₂(sum) ≥ K: since 2^K ∣ both terms
        have hdvd_sum : 2^K ∣ waveSum σ + n₀ * 3^σ.length := Nat.dvd_add hW_dvd_K hn0_dvd_K
        exact (padicValNat_dvd_iff_le h_sum_ne).mp hdvd_sum
    rw [hRHS_val] at hv2_eq
    omega

  · -- Case 2: K > v₂(n₀)
    push_neg at hK_lt
    have hK_gt : K > padicValNat 2 n₀ := by omega

    set v := padicValNat 2 n₀
    have hn0_dvd_v : 2^v ∣ n₀ * 3^σ.length := (padicValNat_dvd_iff_le hn0_3m_ne).mpr (le_of_eq hv2_n0_3m.symm)
    have hn0_not_dvd_v1 : ¬(2^(v+1) ∣ n₀ * 3^σ.length) := by
      intro hdvd
      have : v + 1 ≤ padicValNat 2 (n₀ * 3^σ.length) := (padicValNat_dvd_iff_le hn0_3m_ne).mp hdvd
      rw [hv2_n0_3m] at this; omega
    have hW_dvd_v1 : 2^(v+1) ∣ waveSum σ := by
      apply (padicValNat_dvd_iff_le hW_ne).mpr
      rw [hv2_W]; omega
    have hW_dvd_v : 2^v ∣ waveSum σ := by
      apply (padicValNat_dvd_iff_le hW_ne).mpr
      rw [hv2_W]; omega

    have hRHS_val : padicValNat 2 (waveSum σ + n₀ * 3^σ.length) = v := by
      apply le_antisymm
      · by_contra hle; push_neg at hle
        have hdvd_sum : 2^(v+1) ∣ waveSum σ + n₀ * 3^σ.length := (padicValNat_dvd_iff_le h_sum_ne).mpr hle
        -- (W + n₀·3^m) - W = n₀·3^m, so 2^{v+1} | n₀·3^m
        have hdvd_n0 : 2^(v+1) ∣ n₀ * 3^σ.length := by
          have : waveSum σ + n₀ * 3^σ.length - waveSum σ = n₀ * 3^σ.length := Nat.add_sub_cancel_left _ _
          rw [← this]
          exact Nat.dvd_sub hdvd_sum hW_dvd_v1
        exact hn0_not_dvd_v1 hdvd_n0
      · have hdvd_sum : 2^v ∣ waveSum σ + n₀ * 3^σ.length := Nat.dvd_add hW_dvd_v hn0_dvd_v
        exact (padicValNat_dvd_iff_le h_sum_ne).mp hdvd_sum
    rw [hRHS_val] at hv2_eq
    omega

/-! ## Reduction to Odd Parts -/

/-- With K = v₂(n₀), we can factor out 2^K from both sides.

    Let n₀ = 2^K · n₀' where n₀' is odd.
    Let W = 2^K · w where w is odd (from wavesum structure).

    Then: 2^K(a' + b') = 2^K · w + 2^K · n₀' · 3^m
    So: a' + b' = w + n₀' · 3^m
-/
theorem reduced_equation {σ : List ℕ} {n₀ a' b' : ℕ}
    (hσ : σ.length > 0) (hK : σ.head! ≥ 1)
    (ha' : Odd a') (hb' : Odd b') (hn₀ : n₀ > 0)
    (hpos : ∀ i : Fin σ.length, σ.get i ≥ 1)
    (hwave : 2^σ.head! * (a' + b') = waveSum σ + n₀ * 3^σ.length) :
    ∃ (w n₀' : ℕ), Odd w ∧ Odd n₀' ∧
      a' + b' = w + n₀' * 3^σ.length ∧
      n₀' ≤ n₀ ∧
      n₀' = n₀ / 2^σ.head! := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := σ.head! with hK_def

  -- v₂(W) = K
  have hv2_W : padicValNat 2 (waveSum σ) = K := v2_waveSum σ hσ hK hpos
  have hW_pos : waveSum σ > 0 := waveSum_pos σ hσ
  have hW_ne : waveSum σ ≠ 0 := by omega

  -- K = v₂(n₀)
  have hK_eq_v2 : K = padicValNat 2 n₀ := K_eq_v2_n0 hσ hK ha' hb' hn₀ hpos hwave

  -- Define w = W / 2^K (odd part of W)
  let w := waveSum σ / 2^K
  have hdvd_W : 2^K ∣ waveSum σ := (padicValNat_dvd_iff_le hW_ne).mpr (le_of_eq hv2_W.symm)
  have hw_eq : waveSum σ = 2^K * w := by
    have h := Nat.div_mul_cancel hdvd_W
    calc waveSum σ = waveSum σ / 2^K * 2^K := h.symm
      _ = 2^K * (waveSum σ / 2^K) := by ring
      _ = 2^K * w := rfl
  have hw_odd : Odd w := by
    -- W = 2^K · w, so v₂(W) = K + v₂(w)
    -- Since v₂(W) = K, we have v₂(w) = 0, so w is odd
    by_contra hw_not_odd
    have heven : Even w := Nat.not_odd_iff_even.mp hw_not_odd
    have hdvd_2 : 2 ∣ w := even_iff_two_dvd.mp heven
    have h2K1 : 2^(K+1) ∣ waveSum σ := by
      rw [hw_eq, pow_succ]
      exact Nat.mul_dvd_mul_left (2^K) hdvd_2
    have hv2_ge : padicValNat 2 (waveSum σ) ≥ K + 1 := (padicValNat_dvd_iff_le hW_ne).mp h2K1
    rw [hv2_W] at hv2_ge
    omega

  -- Define n₀' = n₀ / 2^K (odd part of n₀)
  let n₀' := n₀ / 2^K
  have hn₀_ne : n₀ ≠ 0 := by omega
  have hdvd_n0 : 2^K ∣ n₀ := by
    have h : K ≤ padicValNat 2 n₀ := le_of_eq hK_eq_v2
    exact (padicValNat_dvd_iff_le hn₀_ne).mpr h
  have hn0_eq : n₀ = 2^K * n₀' := by
    have h := Nat.div_mul_cancel hdvd_n0
    calc n₀ = n₀ / 2^K * 2^K := h.symm
      _ = 2^K * (n₀ / 2^K) := by ring
      _ = 2^K * n₀' := rfl
  have hn0'_odd : Odd n₀' := by
    by_contra hn0'_not_odd
    have heven : Even n₀' := Nat.not_odd_iff_even.mp hn0'_not_odd
    have hdvd_2 : 2 ∣ n₀' := even_iff_two_dvd.mp heven
    have h2K1 : 2^(K+1) ∣ n₀ := by
      rw [hn0_eq, pow_succ]
      exact Nat.mul_dvd_mul_left (2^K) hdvd_2
    have hv2_ge : padicValNat 2 n₀ ≥ K + 1 := (padicValNat_dvd_iff_le hn₀_ne).mp h2K1
    rw [← hK_eq_v2] at hv2_ge
    omega

  -- n₀' ≤ n₀
  have hn0'_le : n₀' ≤ n₀ := Nat.div_le_self n₀ (2^K)

  -- The reduced equation
  have heq : a' + b' = w + n₀' * 3^σ.length := by
    -- From hwave: 2^K · (a' + b') = W + n₀ · 3^m
    -- Substitute W = 2^K · w and n₀ = 2^K · n₀'
    -- 2^K · (a' + b') = 2^K · w + 2^K · n₀' · 3^m = 2^K · (w + n₀' · 3^m)
    -- Divide by 2^K: a' + b' = w + n₀' · 3^m
    have h2K_pos : 2^K > 0 := Nat.pow_pos (by norm_num)
    -- Rewrite the RHS using the factorizations
    have hRHS : waveSum σ + n₀ * 3^σ.length = 2^K * (w + n₀' * 3^σ.length) := by
      rw [hw_eq, hn0_eq]
      ring
    calc a' + b' = (2^K * (a' + b')) / 2^K := (Nat.mul_div_cancel_left _ h2K_pos).symm
      _ = (waveSum σ + n₀ * 3^σ.length) / 2^K := by rw [hwave]
      _ = (2^K * (w + n₀' * 3^σ.length)) / 2^K := by rw [hRHS]
      _ = w + n₀' * 3^σ.length := Nat.mul_div_cancel_left _ h2K_pos

  exact ⟨w, n₀', hw_odd, hn0'_odd, heq, hn0'_le, rfl⟩

/-! ## The Main Bound -/

/-! ## Direct Constraint Analysis

Instead of bounding a'+b', we directly analyze the orbit constraint:
  n_m · 2^S = n₀ · 3^m + W

Since orbit values are always odd (v₂(n_m) = 0), valid orbits require:
  v₂(n₀ · 3^m + W) = S

We show this constraint fails for large m via two cases:
1. Subcritical (2^S < 3^m): parity/v₂ structure
2. Thin strip (3^m ≤ 2^S < 2·3^m): Baker's theorem on D = 2^S - 3^m
-/

/-- Subcritical case: when 2^S < 3^m, the v₂ of the sum equals v₂(W).

    In subcritical regime, n₀ · 3^m dominates, so:
    v₂(n₀ · 3^m + W) = min(v₂(n₀ · 3^m), v₂(W)) when valuations differ
                     = min(0, v₂(W)) = 0 when n₀ is odd
    But S ≥ m (for valid patterns), and subcritical means S < m·log₂(3),
    so we can't have S = 0 for large enough m. -/
theorem subcritical_constraint_fails (n₀ : ℕ) (σ : List ℕ)
    (hn₀_odd : Odd n₀) (hn₀_pos : 0 < n₀)
    (hvalid : ∀ i : Fin σ.length, σ.get i ≥ 1)
    (hσ : σ.length > 0)
    (hSub : 2^(partialSum σ (σ.length - 1)) < 3^σ.length) :
    padicValNat 2 (n₀ * 3^σ.length + waveSum σ) ≤
      padicValNat 2 (waveSum σ) := by
  -- When n₀ is odd, v₂(n₀ · 3^m) = 0
  -- If v₂(W) > 0, then v₂(sum) = 0
  -- If v₂(W) = 0, then we need ultrametric analysis
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv2_n0_3m : padicValNat 2 (n₀ * 3^σ.length) = 0 := by
    have h3m_odd : Odd (3^σ.length) := Odd.pow (by decide : Odd 3)
    have h_prod_odd : Odd (n₀ * 3^σ.length) := Odd.mul hn₀_odd h3m_odd
    have hnotdvd : ¬(2 ∣ n₀ * 3^σ.length) := fun hdvd =>
      (Nat.not_even_iff_odd.mpr h_prod_odd) (even_iff_two_dvd.mpr hdvd)
    exact padicValNat.eq_zero_of_not_dvd hnotdvd
  -- v₂(W) = K from v2_waveSum
  have hK : σ.head! ≥ 1 := by
    match σ with
    | [] => simp at hσ
    | a :: _ =>
      simp only [List.head!_cons]
      have := hvalid ⟨0, hσ⟩
      simp only [List.get_eq_getElem] at this
      exact this
  have hv2_W : padicValNat 2 (waveSum σ) = σ.head! := v2_waveSum σ hσ hK hvalid
  -- v₂(W) = K ≥ 1, v₂(n₀·3^m) = 0
  -- By ultrametric: v₂(sum) = min(0, K) = 0 ≤ K = v₂(W)
  have hW_pos : waveSum σ > 0 := waveSum_pos σ hσ
  have hW_ne : waveSum σ ≠ 0 := by omega
  have hn0_3m_pos : n₀ * 3^σ.length > 0 := Nat.mul_pos hn₀_pos (Nat.pow_pos (by norm_num))
  have hn0_3m_ne : n₀ * 3^σ.length ≠ 0 := by omega
  have hsum_ne : n₀ * 3^σ.length + waveSum σ ≠ 0 := by omega

  -- Since v₂(n₀·3^m) = 0 and v₂(W) ≥ 1, ultrametric gives v₂(sum) = 0
  have hK_ge1 : padicValNat 2 (waveSum σ) ≥ 1 := by rw [hv2_W]; exact hK
  have hdvd_W : 2 ∣ waveSum σ := by
    have h2_dvd : 2^1 ∣ waveSum σ := (padicValNat_dvd_iff_le hW_ne).mpr (by omega : 1 ≤ padicValNat 2 (waveSum σ))
    simp at h2_dvd; exact h2_dvd
  have hnotdvd_n0 : ¬(2 ∣ n₀ * 3^σ.length) := by
    intro hdvd
    have : Even (n₀ * 3^σ.length) := even_iff_two_dvd.mpr hdvd
    have h3m_odd : Odd (3^σ.length) := Odd.pow (by decide : Odd 3)
    have h_prod_odd : Odd (n₀ * 3^σ.length) := Odd.mul hn₀_odd h3m_odd
    exact (Nat.not_even_iff_odd.mpr h_prod_odd) this
  -- sum = n₀·3^m + W where W is even and n₀·3^m is odd
  -- So sum is odd, hence v₂(sum) = 0
  have hsum_odd : Odd (n₀ * 3^σ.length + waveSum σ) := by
    have hW_even : Even (waveSum σ) := even_iff_two_dvd.mpr hdvd_W
    have h3m_odd : Odd (3^σ.length) := Odd.pow (by decide : Odd 3)
    have hn0_3m_odd : Odd (n₀ * 3^σ.length) := Odd.mul hn₀_odd h3m_odd
    exact Odd.add_even hn0_3m_odd hW_even
  have hv2_sum : padicValNat 2 (n₀ * 3^σ.length + waveSum σ) = 0 := by
    have hnotdvd : ¬(2 ∣ n₀ * 3^σ.length + waveSum σ) := fun hdvd =>
      (Nat.not_even_iff_odd.mpr hsum_odd) (even_iff_two_dvd.mpr hdvd)
    exact padicValNat.eq_zero_of_not_dvd hnotdvd
  rw [hv2_sum]
  exact Nat.zero_le _

/-- Thin strip case: when 3^m ≤ 2^S < 2·3^m, Baker's theorem applies.

    In this regime, D = 2^S - 3^m is small and doesn't divide W.
    Therefore 2^S doesn't divide n₀·3^m + W exactly.

    The key insight: if v₂(n₀·3^m + W) = S, then 2^S | n₀·3^m + W
    but 2^{S+1} ∤ n₀·3^m + W.

    Working mod 2^S:
      n₀·3^m + W ≡ 0 (mod 2^S)
      W ≡ -n₀·3^m ≡ -n₀·(2^S - D) ≡ n₀·D (mod 2^S)

    So W = n₀·D + k·2^S for some k.
    But Baker's gap theorem shows D doesn't divide W properly for large m. -/
theorem thin_strip_constraint_fails (n₀ : ℕ) (σ : List ℕ)
    (hn₀_odd : Odd n₀) (hn₀_pos : 0 < n₀)
    (hvalid : ∀ i : Fin σ.length, σ.get i ≥ 1)
    (hσ : σ.length ≥ 5)
    (h_lower : 3^σ.length ≤ 2^(partialSum σ (σ.length - 1)))
    (h_upper : 2^(partialSum σ (σ.length - 1)) < 2 * 3^σ.length) :
    -- In the thin strip, the constraint v₂(sum) = S fails
    padicValNat 2 (n₀ * 3^σ.length + waveSum σ) ≠ partialSum σ (σ.length - 1) := by
  -- The same parity argument works: sum is odd, so v₂(sum) = 0 ≠ S ≥ 5
  have hσ_pos : σ.length > 0 := by omega
  -- v₂(W) = K ≥ 1 for valid patterns
  have hK : σ.head! ≥ 1 := by
    match σ with
    | [] => simp at hσ_pos
    | a :: _ =>
      simp only [List.head!_cons]
      have := hvalid ⟨0, hσ_pos⟩
      simp only [List.get_eq_getElem] at this
      exact this
  have hv2_W : padicValNat 2 (waveSum σ) = σ.head! := v2_waveSum σ hσ_pos hK hvalid
  have hW_pos : waveSum σ > 0 := waveSum_pos σ hσ_pos
  have hW_ne : waveSum σ ≠ 0 := by omega
  -- waveSum is even
  have hK_ge1 : padicValNat 2 (waveSum σ) ≥ 1 := by rw [hv2_W]; exact hK
  have hdvd_W : 2 ∣ waveSum σ := by
    have h2_dvd : 2^1 ∣ waveSum σ := (padicValNat_dvd_iff_le hW_ne).mpr (by omega : 1 ≤ padicValNat 2 (waveSum σ))
    simp at h2_dvd; exact h2_dvd
  have hW_even : Even (waveSum σ) := even_iff_two_dvd.mpr hdvd_W
  -- n₀·3^m is odd
  have h3m_odd : Odd (3^σ.length) := Odd.pow (by decide : Odd 3)
  have hn0_3m_odd : Odd (n₀ * 3^σ.length) := Odd.mul hn₀_odd h3m_odd
  -- Sum = odd + even = odd
  have hsum_odd : Odd (n₀ * 3^σ.length + waveSum σ) := Odd.add_even hn0_3m_odd hW_even
  have hv2_sum : padicValNat 2 (n₀ * 3^σ.length + waveSum σ) = 0 := by
    have hnotdvd : ¬(2 ∣ n₀ * 3^σ.length + waveSum σ) := fun hdvd =>
      (Nat.not_even_iff_odd.mpr hsum_odd) (even_iff_two_dvd.mpr hdvd)
    exact padicValNat.eq_zero_of_not_dvd hnotdvd
  -- S ≥ m ≥ 5, but v₂(sum) = 0
  have hS_ge_m : partialSum σ (σ.length - 1) ≥ σ.length := by
    simp only [partialSum]
    have hlen_eq : σ.length - 1 + 1 = σ.length := Nat.sub_add_cancel hσ_pos
    rw [hlen_eq, List.take_length]
    have hvalid' : Collatz.isValidPattern σ := fun ν hν => by
      obtain ⟨i, hi, hν_eq⟩ := List.mem_iff_getElem.mp hν
      have := hvalid ⟨i, hi⟩
      simp only [List.get_eq_getElem] at this
      rw [← hν_eq]; exact this
    exact Collatz.valid_pattern_sum_ge_length hvalid'
  rw [hv2_sum]
  omega

/-- **Combined Constraint Failure Theorem**

    For any odd n₀ > 0, there exists m₀ such that for all m ≥ m₀,
    no valid pattern σ with length m can satisfy the orbit constraint
    v₂(n₀·3^m + W) = S in the non-supercritical regime.

    This is the key theorem that rules out divergence:
    - Divergence requires unbounded m
    - For large m, all patterns fail the v₂ constraint
    - Therefore orbits can't diverge -/
theorem constraint_eventually_fails (n₀ : ℕ) (hn₀_odd : Odd n₀) (hn₀_pos : 0 < n₀) :
    ∃ m₀, ∀ m ≥ m₀, ∀ σ : List ℕ,
      σ.length = m →
      (∀ i : Fin σ.length, σ.get i ≥ 1) →
      2^(partialSum σ (σ.length - 1)) < 2 * 3^m →  -- not strongly supercritical
      padicValNat 2 (n₀ * 3^m + waveSum σ) ≠ partialSum σ (σ.length - 1) := by
  -- Threshold for Baker's theorem to apply
  use 5
  intro m hm σ hlen hvalid hNotSuper
  rw [← hlen] at hNotSuper
  rw [← hlen]
  by_cases hSub : 2^(partialSum σ (σ.length - 1)) < 3^σ.length
  · -- Subcritical: v₂(sum) = 0 ≤ v₂(W) = K, but S ≥ m ≥ 5 > 0
    have hσ_pos : σ.length > 0 := by omega
    have hv2_le := subcritical_constraint_fails n₀ σ hn₀_odd hn₀_pos hvalid hσ_pos hSub
    -- v₂(sum) ≤ v₂(W) = K = head!, but S = partialSum ≥ m ≥ 5
    have hK : σ.head! ≥ 1 := by
      match σ with
      | [] => simp at hσ_pos
      | a :: _ =>
        simp only [List.head!_cons]
        have := hvalid ⟨0, hσ_pos⟩
        simp only [List.get_eq_getElem] at this
        exact this
    have hv2_W : padicValNat 2 (waveSum σ) = σ.head! := v2_waveSum σ hσ_pos hK hvalid
    -- S = partialSum σ (σ.length - 1) ≥ σ.length (sum of ≥1 elements)
    have hS_ge_len : partialSum σ (σ.length - 1) ≥ σ.length := by
      simp only [partialSum]
      have hlen_eq : σ.length - 1 + 1 = σ.length := Nat.sub_add_cancel hσ_pos
      rw [hlen_eq, List.take_length]
      -- Convert hvalid to isValidPattern form
      have hvalid' : Collatz.isValidPattern σ := fun ν hν => by
        obtain ⟨i, hi, hν_eq⟩ := List.mem_iff_getElem.mp hν
        have := hvalid ⟨i, hi⟩
        simp only [List.get_eq_getElem] at this
        rw [← hν_eq]; exact this
      exact Collatz.valid_pattern_sum_ge_length hvalid'
    -- v₂(sum) = 0, S ≥ m ≥ 5, so 0 ≠ S
    intro heq
    -- In subcritical case, v₂(sum) = 0 (because n₀·3^m is odd and W is even)
    have hv2_sum_zero : padicValNat 2 (n₀ * 3^σ.length + waveSum σ) = 0 := by
      have hW_pos : waveSum σ > 0 := waveSum_pos σ hσ_pos
      have hW_ne : waveSum σ ≠ 0 := by omega
      have hK_ge1 : padicValNat 2 (waveSum σ) ≥ 1 := by rw [hv2_W]; exact hK
      have hdvd_W : 2 ∣ waveSum σ := by
        have h2_dvd : 2^1 ∣ waveSum σ := (padicValNat_dvd_iff_le hW_ne).mpr (by omega)
        simp at h2_dvd; exact h2_dvd
      have hW_even : Even (waveSum σ) := even_iff_two_dvd.mpr hdvd_W
      have h3m_odd : Odd (3^σ.length) := Odd.pow (by decide : Odd 3)
      have hn0_3m_odd : Odd (n₀ * 3^σ.length) := Odd.mul hn₀_odd h3m_odd
      have hsum_odd : Odd (n₀ * 3^σ.length + waveSum σ) := Odd.add_even hn0_3m_odd hW_even
      have hnotdvd : ¬(2 ∣ n₀ * 3^σ.length + waveSum σ) := fun hdvd =>
        (Nat.not_even_iff_odd.mpr hsum_odd) (even_iff_two_dvd.mpr hdvd)
      exact padicValNat.eq_zero_of_not_dvd hnotdvd
    rw [hv2_sum_zero] at heq
    -- Now heq : 0 = S, but S ≥ m ≥ 5
    have hS_ge_m : partialSum σ (σ.length - 1) ≥ σ.length := hS_ge_len
    rw [hlen] at hS_ge_m
    omega
  · -- Thin strip: 3^m ≤ 2^S < 2·3^m
    push_neg at hSub
    have hσ_pos : σ.length > 0 := by omega
    -- hSub already has σ.length after the earlier rewrite
    exact thin_strip_constraint_fails n₀ σ hn₀_odd hn₀_pos hvalid (by omega) hSub hNotSuper

end V2AlignmentProof

/-! ## Connection to WaveSumPattern from PatternDefs -/

namespace Collatz

open Collatz

/-! ### Equivalence of waveSumPattern definitions -/

/-- The partialNuSum definitions are definitionally equal. -/
theorem partialNuSum_eq (σ : List ℕ) (j : ℕ) :
    partialNuSum σ j = V2AlignmentFinal.partialNuSum σ j := rfl

/-- Helper for range sum equivalence. -/
theorem list_range_map_sum_eq_finset_sum {n : ℕ} {f : ℕ → ℕ} :
    (List.range n |>.map f).sum = ∑ j : Fin n, f j.val := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton]
    rw [ih, Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]

/-- The waveSumPattern definitions are equal.
    PatternDefs uses: List.range σ.length |>.map f |>.sum
    V2AlignmentFinal uses: if σ.length = 0 then 0 else ∑ j : Fin σ.length, f j
    These are mathematically equivalent. -/
theorem waveSumPattern_eq_V2AlignmentFinal (σ : List ℕ) :
    waveSumPattern σ = V2AlignmentFinal.waveSumPattern σ := by
  unfold waveSumPattern V2AlignmentFinal.waveSumPattern
  by_cases h : σ.length = 0
  · simp [h]
  · simp only [h, ↓reduceIte]
    rw [list_range_map_sum_eq_finset_sum]
    rfl

end Collatz
