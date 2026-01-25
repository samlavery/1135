/-
Copyright (c) 2024. All rights reserved.
Released under MIT license.
-/
import Collatz.Basic
import Collatz.WaveSumProperties

/-!
# Wave Decomposition Lemmas

Structural lemmas about wave sum decomposition used in ConstraintMismatch.lean.
-/

namespace Collatz

/-- Helper: partialNuSum at j+1 is at least the first element -/
private lemma partialNuSum_ge_head {σ : List ℕ} (hlen1 : σ.length ≥ 1) (j : ℕ) :
    partialNuSum σ (j + 1) ≥ σ.head! := by
  unfold partialNuSum
  obtain ⟨fst, rest, hσ_eq⟩ := List.length_pos_iff_exists_cons.mp hlen1
  subst hσ_eq
  simp only [List.head!_cons, List.take_succ_cons, List.sum_cons]
  omega

/-- Helper: 2^{pns(j+1)} = 2^K * 2^{pns(j+1) - K} -/
private lemma twoPow_partialNuSum_split
    {σ : List ℕ} {K : ℕ} (hlen1 : σ.length ≥ 1)
    (hK : K = σ.head!) (j : ℕ) :
    2 ^ (partialNuSum σ (j + 1)) = 2 ^ K * 2 ^ (partialNuSum σ (j + 1) - K) := by
  have hle : K ≤ partialNuSum σ (j + 1) := by
    have hge : partialNuSum σ (j + 1) ≥ σ.head! := partialNuSum_ge_head hlen1 j
    omega
  calc 2 ^ (partialNuSum σ (j + 1))
      = 2 ^ (K + (partialNuSum σ (j + 1) - K)) := by rw [Nat.add_sub_of_le hle]
    _ = 2 ^ K * 2 ^ (partialNuSum σ (j + 1) - K) := by rw [pow_add]

/-- Factor 2^K out of waveSumEvenPart -/
private lemma waveSumEvenPart_factor_twoPow
    {σ : List ℕ} {K m : ℕ}
    (hlen : σ.length = m) (hm_ge_1 : m ≥ 1) (hK : K = σ.head!) :
    waveSumEvenPart σ =
      2 ^ K * ((List.range (m - 1)).map (fun j =>
        3 ^ (m - 2 - j) * 2 ^ (partialNuSum σ (j + 1) - K))).sum := by
  have hlen1 : σ.length ≥ 1 := by omega
  unfold waveSumEvenPart
  simp only [hlen]
  -- Show term-by-term equality and use induction
  have heq : ∀ j, 3 ^ (m - 2 - j) * 2 ^ (partialNuSum σ (j + 1)) =
      2 ^ K * (3 ^ (m - 2 - j) * 2 ^ (partialNuSum σ (j + 1) - K)) := by
    intro j
    rw [twoPow_partialNuSum_split hlen1 hK j]
    ring
  induction (List.range (m - 1)) with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [heq a, ih, Nat.mul_add]

/-- Wave decomposition lemma: Y = j1 + (j≥2 sum) -/
lemma wave_decomp_Y_eq_j1_plus_rest
    {σ : List ℕ} {K ν₁ m : ℕ}
    (hlen : σ.length = m) (hm_ge_4 : m ≥ 4)
    (hvalid : isValidPattern σ)
    (hK_def : K = σ.head!) (hν₁_def : ν₁ = σ.tail.head!)
    (hpns1 : partialNuSum σ 1 = K)
    (h_pns2 : partialNuSum σ 2 = K + ν₁)
    (B : ℕ) (hB_def : B = waveSumEvenPart σ)
    (Y : ℕ) (hY_def : Y = B / 2^K - 3^(m-2)) :
    Y = 3^(m-3) * 2^ν₁ +
        (Finset.Ico 2 (m-1)).sum (fun j => 3^(m-2-j) * 2^(partialNuSum σ (j+1) - K)) := by
  have h2K_pos : 0 < 2^K := Nat.pow_pos (by norm_num)
  have hm_ge_1 : m ≥ 1 := by omega

  -- Factor 2^K out of B and divide
  have hBfac := waveSumEvenPart_factor_twoPow hlen hm_ge_1 hK_def
  have hdiv : B / 2^K = ((List.range (m - 1)).map (fun j =>
      3 ^ (m - 2 - j) * 2 ^ (partialNuSum σ (j + 1) - K))).sum := by
    rw [hB_def, hBfac, Nat.mul_div_cancel_left _ h2K_pos]

  -- Split range (m-1) into j=0, j=1, and j≥2
  have hsplit : ((List.range (m - 1)).map (fun j =>
      3 ^ (m - 2 - j) * 2 ^ (partialNuSum σ (j + 1) - K))).sum =
      3^(m-2) + 3^(m-3) * 2^ν₁ +
      (Finset.Ico 2 (m-1)).sum (fun j => 3^(m-2-j) * 2^(partialNuSum σ (j+1) - K)) := by
    -- range (m-1) = [0, 1, 2, ..., m-2]
    -- Split into first two elements and the rest
    have hm1_ge2 : m - 1 ≥ 2 := by omega
    have hrange_eq : List.range (m - 1) = [0, 1] ++ List.range' 2 (m - 3) := by
      have hlen : (m - 1) = 2 + (m - 3) := by omega
      rw [hlen, List.range_add, List.range_succ, List.range_one]
      simp only [List.cons_append, List.nil_append]
      congr 1
      rw [List.range'_eq_map_range]
    rw [hrange_eq, List.map_append, List.sum_append]
    -- Simplify [0, 1] part
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    -- j=0: 3^{m-2} * 2^{pns(1)-K} = 3^{m-2}
    have hj0 : 3^(m - 2 - 0) * 2^(partialNuSum σ (0 + 1) - K) = 3^(m-2) := by
      simp only [Nat.sub_zero, Nat.zero_add, hpns1, Nat.sub_self, pow_zero, mul_one]
    -- j=1: 3^{m-3} * 2^{pns(2)-K} = 3^{m-3} * 2^{ν₁}
    have hj1 : 3^(m - 2 - 1) * 2^(partialNuSum σ (1 + 1) - K) = 3^(m-3) * 2^ν₁ := by
      have hsub : m - 2 - 1 = m - 3 := by omega
      simp only [hsub, h_pns2]
      have hexp : K + ν₁ - K = ν₁ := by omega
      rw [hexp]
    rw [hj0, hj1]
    -- Convert List.range' sum to Finset.Ico sum
    -- congr 1 solves this because the sums are definitionally equal
    congr 1

  -- Combine
  rw [hY_def, hdiv, hsplit]
  omega

end Collatz
