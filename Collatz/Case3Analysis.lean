/-
Copyright (c) 2024. All rights reserved.
Released under MIT license.
-/
import Collatz.Basic
import Collatz.WaveSumProperties
import Collatz.WaveDecompLemmas
-- import Collatz.KComplexitySupermartingale
import Collatz.PatternDefs
import Collatz.Case3KComplexity

/-!
# Case 3 Analysis for Collatz Wave Structure

## The Problem

Case 3 occurs in the "equal case" when:
- `v₂(1 + 3n) = K` (the equal case condition)
- `v₂(3q + 1) = ν₁` where `q = (1 + 3n)/2^K` is odd

In Cases 1 & 2 (where `v₂(3q+1) ≠ ν₁`), the ultrametric inequality directly gives
`v₂(L/2^K) ≤ ν₁`, leading to `v₂(L) < S`.

In Case 3, the two leading terms both have `v₂ = ν₁`, so they can "cancel" and
produce higher valuation. The bound `v₂(L/2^K) ≤ ν₁` is FALSE in Case 3.

## Solution

We prove that for sufficiently large m (pattern length), the constraint still fails.

### Key Quantities

Given n with `v₂(1 + 3n) = K`:
- `q = (1 + 3n) / 2^K` (odd)
- `r = (3q + 1) / 2^{ν₁}` (odd, when `v₂(3q+1) = ν₁`)
- `s = (3r + 1) / 2` (integer, since r odd means 3r+1 even)

### Main Result

For patterns with `m > v₂(s+1) + 3`:
```
v₂(L) = K + ν₁ + 1 + v₂(3^{m-3}·s + H') < S
```

where the bound `v₂(3^{m-3}·s + H') < m - 3` holds because `v₂(s+1) < m - 3`.

## References

- ConstraintMismatch.lean lines 2424-2700 (partial Case 3 handling)
- WaveDecompLemmas.lean (wave structure decomposition)
-/

namespace Collatz

namespace Case3

open scoped BigOperators

/-! ### Definitions -/

/-- The quotient q in Case 3: q = (1 + 3n) / 2^K where K = v₂(1 + 3n) -/
def case3_q (n K : ℕ) : ℕ := (1 + 3 * n) / 2^K

/-- The quotient r in Case 3: r = (3q + 1) / 2^{ν₁} where ν₁ = v₂(3q + 1) -/
def case3_r (q ν₁ : ℕ) : ℕ := (3 * q + 1) / 2^ν₁

/-- The key quantity s in Case 3: s = (3r + 1) / 2
    This is always an integer when r is odd (which holds in Case 3). -/
def case3_s (r : ℕ) : ℕ := (3 * r + 1) / 2

/-- The threshold M for Case 3: m must exceed M for the v₂ bound to work.
    M = v₂(s + 1) + 8
    Note: +8 provides margin for the 16 | sum edge case where v₂(odd+odd) can be large.
    For realizable patterns, the actual bound is tighter, but +8 is conservative. -/
def case3_threshold (s : ℕ) : ℕ := padicValNat 2 (s + 1) + 8

/-! ### Basic Properties -/

/-- Helper: x / 2^(padicValNat 2 x) is odd when x ≠ 0 -/
private lemma div_pow_padicValNat_odd (x : ℕ) (hx : x ≠ 0) : Odd (x / 2^(padicValNat 2 x)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, m, hm_odd, hx_eq⟩ := Nat.exists_eq_two_pow_mul_odd hx
  have hpv : padicValNat 2 (2^k * m) = k := by
    rw [padicValNat.mul (by positivity) (Odd.pos hm_odd).ne']
    have hpow : padicValNat 2 (2^k) = k := by
      rw [padicValNat.pow (p := 2) (a := 2) k (by norm_num)]
      simp [padicValNat.self]
    have hm_v : padicValNat 2 m = 0 := padicValNat.eq_zero_of_not_dvd hm_odd.not_two_dvd_nat
    omega
  rw [hx_eq, hpv, Nat.mul_div_cancel_left _ (by positivity)]
  exact hm_odd

/-- q is odd when K = v₂(1 + 3n) exactly -/
lemma case3_q_odd {n K : ℕ} (hK : padicValNat 2 (1 + 3 * n) = K) (hn_pos : n > 0) :
    Odd (case3_q n K) := by
  unfold case3_q
  have h1 : 1 + 3 * n ≠ 0 := by omega
  have := div_pow_padicValNat_odd (1 + 3 * n) h1
  rw [hK] at this
  exact this

/-- r is odd when ν₁ = v₂(3q + 1) exactly -/
lemma case3_r_odd {q ν₁ : ℕ} (hν₁ : padicValNat 2 (3 * q + 1) = ν₁) (hq_pos : q > 0) :
    Odd (case3_r q ν₁) := by
  unfold case3_r
  have h1 : 3 * q + 1 ≠ 0 := by omega
  have := div_pow_padicValNat_odd (3 * q + 1) h1
  rw [hν₁] at this
  exact this

/-- s is well-defined (3r + 1 is even when r is odd) -/
lemma case3_s_well_defined {r : ℕ} (hr_odd : Odd r) : 2 ∣ (3 * r + 1) := by
  obtain ⟨k, hk⟩ := hr_odd
  use 3 * k + 2; omega

/-- The v₂ of 3^k · x equals v₂(x) for any k (since 3 is odd) -/
lemma v2_mul_pow_three (x k : ℕ) (hx : x ≠ 0) :
    padicValNat 2 (3^k * x) = padicValNat 2 x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat.mul (by positivity : 3^k ≠ 0) hx]
  have h3_odd : Odd (3^k) := Odd.pow (by decide : Odd 3)
  have hv2_3 : padicValNat 2 (3^k) = 0 := padicValNat.eq_zero_of_not_dvd h3_odd.not_two_dvd_nat
  omega

/-! ### Wave Structure in Case 3 -/

/-- The higher terms H' in the wave decomposition.
    H' = Σ_{j=2}^{m-2} 3^{m-2-j} · 2^{pns(j+1) - K - ν₁ - 1}

    For minimal patterns (σᵢ = 1 for i ≥ 2), this simplifies considerably. -/
def higherTerms (σ : List ℕ) (K ν₁ : ℕ) : ℕ :=
  (Finset.Ico 2 (σ.length - 1)).sum fun j =>
    3^(σ.length - 2 - j) * 2^(partialNuSum σ (j + 1) - K - ν₁ - 1)

/-! ### External Dependencies (from WaveDecompLemmas) -/

/-- Valid patterns have all elements ≥ 1 (proven from definition) -/
theorem isValidPattern_pos : ∀ {σ : List ℕ}, isValidPattern σ → ∀ i, i < σ.length → σ.getD i 0 ≥ 1 := by
  intro σ hvalid i hi
  have hgetElem_mem : σ[i]'hi ∈ σ := List.getElem_mem hi
  have hgetD_eq : σ.getD i 0 = σ[i]'hi := by
    simp only [List.getD_eq_getD_getElem?]
    rw [List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩]
    simp
  rw [hgetD_eq]
  exact hvalid _ hgetElem_mem

/-- Pattern sum equals sum of all elements (definitional) -/
theorem patternSum_eq_sum : ∀ σ : List ℕ, patternSum σ = σ.sum := fun _ => rfl

/-! ### Helper lemmas for case3_wave_decomposition -/

/-- The equal case gives us n₀ in terms of q -/
lemma n0_from_equal_case {n₀ K : ℕ} (hK : padicValNat 2 (1 + 3 * n₀) = K) :
    let q := case3_q n₀ K
    1 + 3 * n₀ = 2^K * q := by
  have hdiv : 2^K ∣ 1 + 3 * n₀ := by rw [← hK]; exact pow_padicValNat_dvd
  simp only [case3_q]
  exact (Nat.mul_div_cancel' hdiv).symm

/-- q is odd in the equal case -/
lemma q_odd_equal_case {n₀ K : ℕ} (hK : padicValNat 2 (1 + 3 * n₀) = K) (hn₀ : n₀ > 0) :
    Odd (case3_q n₀ K) := by
  simp only [case3_q]
  by_contra heven
  have heven' := Nat.not_odd_iff_even.mp heven
  obtain ⟨t, ht⟩ := heven'
  have h2K1 : 2^(K+1) ∣ 1 + 3 * n₀ := by
    have hdiv : 2^K ∣ 1 + 3 * n₀ := by rw [← hK]; exact pow_padicValNat_dvd
    have hquot : (1 + 3 * n₀) = 2^K * ((1 + 3 * n₀) / 2^K) := (Nat.mul_div_cancel' hdiv).symm
    use t; rw [hquot, ht, pow_succ]; ring
  have hv2_ge := padicValNat_dvd_iff_le (by omega : 1 + 3 * n₀ ≠ 0) |>.mp h2K1
  omega

/-- r is odd in Case 3 -/
lemma r_odd_case3 {q ν₁ : ℕ} (hν₁ : padicValNat 2 (3 * q + 1) = ν₁) (hq : q > 0) :
    Odd (case3_r q ν₁) := by
  simp only [case3_r]
  by_contra heven
  have heven' := Nat.not_odd_iff_even.mp heven
  obtain ⟨t, ht⟩ := heven'
  have h2ν1 : 2^(ν₁+1) ∣ 3 * q + 1 := by
    have hdiv : 2^ν₁ ∣ 3 * q + 1 := by rw [← hν₁]; exact pow_padicValNat_dvd
    have hquot : (3 * q + 1) = 2^ν₁ * ((3 * q + 1) / 2^ν₁) := (Nat.mul_div_cancel' hdiv).symm
    use t; rw [hquot, ht, pow_succ]; ring
  have hv2_ge := padicValNat_dvd_iff_le (by omega : 3 * q + 1 ≠ 0) |>.mp h2ν1
  omega

/-- The Case 3 condition gives us 3q + 1 in terms of r -/
lemma case3_expansion {q ν₁ : ℕ} (hν₁ : padicValNat 2 (3 * q + 1) = ν₁) :
    let r := case3_r q ν₁
    3 * q + 1 = 2^ν₁ * r := by
  have hdiv : 2^ν₁ ∣ 3 * q + 1 := by rw [← hν₁]; exact pow_padicValNat_dvd
  simp only [case3_r]
  exact (Nat.mul_div_cancel' hdiv).symm

/-! ### Helper lemmas for v2_higherTerms and inner_sum_eq_higherTerms -/

/-- Helper: sum of take n elements is at least n for valid patterns -/
lemma sum_take_ge_length {σ : List ℕ} (hvalid : isValidPattern σ)
    (n : ℕ) (hn : n ≤ σ.length) : n ≤ (σ.take n).sum := by
  induction σ generalizing n with
  | nil => simp at hn; simp [hn]
  | cons a as ih =>
    cases n with
    | zero => simp
    | succ n' =>
      simp only [List.take_succ_cons, List.sum_cons, List.length_cons] at hn ⊢
      have ha_ge : a ≥ 1 := hvalid a (by simp)
      have has_valid : isValidPattern as := fun x hx => hvalid x (List.mem_cons_of_mem a hx)
      have ih' := ih has_valid n' (by omega)
      omega

/-- The partial nu sum at index 3 is K + ν₁ + σ[2] -/
lemma partialNuSum_at_3 {σ : List ℕ} (hlen : σ.length ≥ 3) :
    partialNuSum σ 3 = σ.head! + (σ.tail).head! + (σ.tail.tail).head! := by
  unfold partialNuSum
  obtain ⟨a, rest1, heq1⟩ : ∃ a rest1, σ = a :: rest1 := by
    cases σ with
    | nil => simp at hlen
    | cons h t => exact ⟨h, t, rfl⟩
  obtain ⟨b, rest2, heq2⟩ : ∃ b rest2, rest1 = b :: rest2 := by
    cases rest1 with
    | nil => simp [heq1] at hlen
    | cons h t => exact ⟨h, t, rfl⟩
  obtain ⟨c, rest3, heq3⟩ : ∃ c rest3, rest2 = c :: rest3 := by
    cases rest2 with
    | nil => simp [heq1, heq2] at hlen
    | cons h t => exact ⟨h, t, rfl⟩
  simp only [heq1, heq2, heq3, List.take, List.sum_cons, List.sum_nil]
  simp only [List.head!_cons, List.tail_cons]
  ring

/-- partialNuSum is monotonically increasing by at least 1 for valid patterns -/
lemma partialNuSum_mono_valid {σ : List ℕ} (hvalid : isValidPattern σ)
    (i j : ℕ) (hi : i < σ.length) (hj : j ≤ σ.length) (hij : i < j) :
    partialNuSum σ i + (j - i) ≤ partialNuSum σ j := by
  unfold partialNuSum
  have hdrop_valid : isValidPattern (σ.drop i) := fun x hx =>
    hvalid x (List.mem_of_mem_drop hx)
  have hdrop_len : (σ.drop i).length = σ.length - i := by simp
  have hji_bound : j - i ≤ (σ.drop i).length := by simp [hdrop_len]; omega
  have hge := sum_take_ge_length hdrop_valid (j - i) hji_bound
  have htake_j : (σ.take j).sum = (σ.take i).sum + ((σ.drop i).take (j - i)).sum := by
    rw [← List.sum_append]
    congr 1
    have h1 : σ.take j = (σ.take i ++ σ.drop i).take j := by rw [List.take_append_drop]
    rw [h1, List.take_append]
    have hilen : (σ.take i).length = i := List.length_take_of_le (Nat.le_of_lt hi)
    have hj_eq : i + (j - i) = j := Nat.add_sub_cancel' (Nat.le_of_lt hij)
    simp only [hilen, List.take_take, Nat.min_eq_right (Nat.le_of_lt hij), List.take_drop, hj_eq]
  rw [htake_j]
  omega

/-- Inner sum equals scaled higherTerms.
    Key identity: Σ_{i∈[3,m)} 3^(m-1-i) * 2^(pns(i)) = 2^(K+ν₁+1) * H'
    Proof by reindexing j = i - 1 and using pns(i) ≥ K + ν₁ + 1 for i ≥ 3. -/
lemma inner_sum_eq_higherTerms {σ : List ℕ} {K ν₁ : ℕ}
    (hlen : σ.length ≥ 4)
    (hvalid : isValidPattern σ)
    (hK_eq : σ.head! = K)
    (hν₁_eq : σ.tail.head! = ν₁) :
    let m := σ.length
    let H' := higherTerms σ K ν₁
    (Finset.Ico 3 m).sum (fun i => 3^(m - 1 - i) * 2^(partialNuSum σ i)) = 2^(K + ν₁ + 1) * H' := by
  -- Key: pns(i) ≥ K + ν₁ + 1 for i ≥ 3, so pns(i) - (K + ν₁ + 1) is well-defined
  have hpns3 := partialNuSum_at_3 (by omega : σ.length ≥ 3)
  rw [hK_eq, hν₁_eq] at hpns3
  have hσ2_ge1 : (σ.tail.tail).head! ≥ 1 := by
    have hc_mem : (σ.tail.tail).head! ∈ σ := by
      cases σ with | nil => simp at hlen | cons a as =>
      cases as with | nil => simp at hlen | cons b bs =>
      cases bs with | nil => simp at hlen | cons c cs => simp
    exact hvalid _ hc_mem
  have hpns3_ge : partialNuSum σ 3 ≥ K + ν₁ + 1 := by rw [hpns3]; omega
  -- Expand the let bindings and show the reindexed equality
  show (Finset.Ico 3 σ.length).sum (fun i => 3^(σ.length - 1 - i) * 2^(partialNuSum σ i)) =
       2^(K + ν₁ + 1) * (Finset.Ico 2 (σ.length - 1)).sum (fun j =>
         3^(σ.length - 2 - j) * 2^(partialNuSum σ (j + 1) - K - ν₁ - 1))
  -- Factor out 2^(K + ν₁ + 1)
  rw [Finset.mul_sum]
  -- Reindex via i ↦ i - 1 from [3, m) to [2, m-1)
  -- Goals order: hi, i_inj, i_surj, h
  apply Finset.sum_bij (fun i _ => i - 1)
  · -- hi: Maps [3, m) → [2, m-1)
    intro i hi; simp only [Finset.mem_Ico] at hi ⊢; omega
  · -- i_inj: Injective
    intro i1 hi1 i2 hi2 heq
    simp only [Finset.mem_Ico] at hi1 hi2
    omega
  · -- i_surj: Surjective onto [2, m-1)
    intro j hj
    simp only [Finset.mem_Ico] at hj
    exact ⟨j + 1, by simp only [Finset.mem_Ico]; omega, by omega⟩
  · -- h: Function equality LHS term = RHS term
    intro i hi
    simp only [Finset.mem_Ico] at hi
    have hexp : σ.length - 2 - (i - 1) = σ.length - 1 - i := by omega
    have hpns_ge : partialNuSum σ i ≥ K + ν₁ + 1 := by
      -- partialNuSum σ 3 ≥ K + ν₁ + 1 and partialNuSum increases
      have h3_lt_len : 3 < σ.length := by omega
      have hi_le_len : i ≤ σ.length := by omega
      have h3_lt_i : 3 < i ∨ 3 = i := by omega
      cases h3_lt_i with
      | inl h3_lt =>
        have hmono := partialNuSum_mono_valid hvalid 3 i h3_lt_len hi_le_len h3_lt
        omega
      | inr h3_eq =>
        rw [← h3_eq]; exact hpns3_ge
    have hi_sub : i - 1 + 1 = i := by omega
    rw [hi_sub, hexp, mul_comm (2^(K + ν₁ + 1)) _, mul_assoc, ← pow_add]
    -- Goal: 2^(partialNuSum σ i) = 2^(partialNuSum σ i - K - ν₁ - 1 + (K + ν₁ + 1))
    congr 1
    -- Need: partialNuSum σ i = partialNuSum σ i - K - ν₁ - 1 + (K + ν₁ + 1)
    have hsub_eq : partialNuSum σ i - K - ν₁ - 1 = partialNuSum σ i - (K + ν₁ + 1) := by omega
    rw [hsub_eq, Nat.sub_add_cancel hpns_ge]

/-- Helper: List.range' sum equals Finset.Ico sum -/
lemma list_range'_map_sum_eq_finset_Ico_sum {n start : ℕ} {f : ℕ → ℕ} :
    ((List.range' start n).map f).sum = (Finset.Ico start (start + n)).sum f := by
  induction n generalizing start with
  | zero => simp
  | succ k ih =>
    -- List.range' start (k+1) = start :: List.range' (start + 1) k
    rw [List.range'_succ]
    simp only [List.map, List.sum_cons]
    -- Apply IH with start + 1
    have ih' := @ih (start + 1)
    have heq : start + 1 + k = start + k + 1 := by ring
    rw [heq] at ih'
    rw [ih']
    -- Finset.Ico start (start + (k + 1)) = insert start (Finset.Ico (start + 1) (start + k + 1))
    have hIco_eq : Finset.Ico start (start + (k + 1)) = insert start (Finset.Ico (start + 1) (start + k + 1)) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      constructor
      · intro ⟨hle, hlt⟩
        by_cases hx : x = start
        · left; exact hx
        · right; omega
      · intro h
        cases h with
        | inl hx => subst hx; omega
        | inr hx => omega
    rw [hIco_eq]
    have hnotin : start ∉ Finset.Ico (start + 1) (start + k + 1) := by simp
    rw [Finset.sum_insert hnotin]

/-- The first two terms of waveSumPattern contribute to the leading structure -/
lemma waveSum_leading_terms {σ : List ℕ} (hlen : σ.length ≥ 2) :
    let m := σ.length
    let K := σ.head!
    waveSumPattern σ = 3^(m - 1) + 3^(m - 2) * 2^K +
      (Finset.Ico 2 m).sum (fun i => 3^(m - 1 - i) * 2^(partialNuSum σ i)) := by
  intro m K
  have hpns1 : partialNuSum σ 1 = K := by
    unfold partialNuSum
    simp only [List.take_one]
    cases σ with
    | nil => simp at hlen
    | cons a as => rfl
  have hlen1 : σ.length ≥ 1 := by omega
  rw [waveSumPattern_split hlen1]
  unfold waveSumEvenPart
  have hrange_split : List.range (m - 1) = 0 :: List.range' 1 (m - 2) := by
    cases σ with
    | nil => simp at hlen
    | cons a as =>
      cases as with
      | nil => simp at hlen
      | cons b bs =>
        show List.range ((a :: b :: bs).length - 1) = 0 :: List.range' 1 ((a :: b :: bs).length - 2)
        simp only [List.length_cons]
        have hsub1 : bs.length + 2 - 1 = bs.length + 1 := by omega
        have hsub2 : bs.length + 2 - 2 = bs.length := by omega
        rw [hsub1, hsub2, List.range_eq_range', List.range'_succ]
  rw [hrange_split]
  simp only [List.map, List.sum_cons]
  rw [hpns1]
  simp only [Nat.sub_zero]
  have hrest : ((List.range' 1 (m - 2)).map (fun j => 3^(m - 2 - j) * 2^(partialNuSum σ (j + 1)))).sum
             = (Finset.Ico 2 m).sum (fun i => 3^(m - 1 - i) * 2^(partialNuSum σ i)) := by
    rw [list_range'_map_sum_eq_finset_Ico_sum]
    rw [show 1 + (m - 2) = m - 1 by omega]
    have hLHS_reindex : ∀ j, j ∈ Finset.Ico 1 (m - 1) →
        3^(m - 2 - j) * 2^(partialNuSum σ (j + 1)) = 3^(m - 1 - (j + 1)) * 2^(partialNuSum σ (j + 1)) := by
      intro j hj
      simp only [Finset.mem_Ico] at hj
      have hexp : m - 2 - j = m - 1 - (j + 1) := by omega
      rw [hexp]
    rw [Finset.sum_congr rfl hLHS_reindex]
    rw [Finset.sum_Ico_add' (fun i => 3^(m - 1 - i) * 2^(partialNuSum σ i)) 1 (m - 1) 1]
    have h11 : 1 + 1 = 2 := rfl
    have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (by omega : m ≥ 1)
    simp only [h11, hm1]
  rw [hrest]
  ring

/-- Main algebraic identity for the wave decomposition -/
lemma wave_decomp_identity {σ : List ℕ} {n₀ K ν₁ : ℕ}
    (hlen : σ.length ≥ 4)
    (hvalid : isValidPattern σ)
    (hK_eq : σ.head! = K)
    (hν₁_eq : σ.tail.head! = ν₁)
    (hK : padicValNat 2 (1 + 3 * n₀) = K)
    (hcase3 : padicValNat 2 (3 * ((1 + 3 * n₀) / 2^K) + 1) = ν₁)
    (hn₀_pos : n₀ > 0) :
    let m := σ.length
    let q := case3_q n₀ K
    let r := case3_r q ν₁
    let s := case3_s r
    let L := waveSumPattern σ + n₀ * 3^m
    let H' := higherTerms σ K ν₁
    L = 2^(K + ν₁ + 1) * (3^(m - 3) * s + H') := by
  intro m q r s L H'
  have hn₀_eq : 1 + 3 * n₀ = 2^K * q := n0_from_equal_case hK
  have hq_pos : q > 0 := by
    have h13n₀_pos : 1 + 3 * n₀ > 0 := by omega
    have hdiv : 2^K ∣ 1 + 3 * n₀ := by rw [← hK]; exact pow_padicValNat_dvd
    have h2K_pos : 2^K > 0 := by positivity
    show case3_q n₀ K > 0
    simp only [case3_q]
    exact Nat.div_pos (Nat.le_of_dvd h13n₀_pos hdiv) h2K_pos
  have h3q1_eq : 3 * q + 1 = 2^ν₁ * r := case3_expansion hcase3
  have hq_odd := q_odd_equal_case hK hn₀_pos
  have hr_odd := r_odd_case3 hcase3 hq_pos
  have h2s : 2 * s = 3 * r + 1 := by
    obtain ⟨k, hk⟩ := hr_odd
    show 2 * case3_s r = 3 * r + 1
    simp only [case3_s]
    -- r = 2*k + 1 implies 3*r + 1 = 6*k + 4 = 2 * (3*k + 2)
    have hr_eq : r = 2 * k + 1 := hk
    have h3r1_even : 2 ∣ 3 * r + 1 := by
      use 3 * k + 2
      omega
    exact Nat.mul_div_cancel' h3r1_even
  have hws := waveSum_leading_terms (by omega : σ.length ≥ 2)
  simp only [hK_eq] at hws
  have hn₀_div : 3 * n₀ = 2^K * q - 1 := by omega
  have hr_pos : r > 0 := by
    show case3_r q ν₁ > 0
    unfold case3_r
    have h3q1_pos : 3 * q + 1 > 0 := by omega
    have hdiv : 2^ν₁ ∣ 3 * q + 1 := by
      have hq_eq : q = (1 + 3 * n₀) / 2^K := rfl
      rw [hq_eq, ← hcase3]; exact pow_padicValNat_dvd
    have h2ν₁_pos : 2^ν₁ > 0 := by positivity
    exact Nat.div_pos (Nat.le_of_dvd h3q1_pos hdiv) h2ν₁_pos
  have hs_pos : s > 0 := by
    show case3_s r > 0
    unfold case3_s
    have h3r1 : 3 * r + 1 ≥ 2 := by omega
    exact Nat.div_pos h3r1 (by norm_num)
  have hpns2 : partialNuSum σ 2 = K + ν₁ := by
    unfold partialNuSum
    obtain ⟨a, rest1, heq1⟩ : ∃ a rest1, σ = a :: rest1 := by
      cases σ with | nil => simp at hlen | cons h t => exact ⟨h, t, rfl⟩
    obtain ⟨b, rest2, heq2⟩ : ∃ b rest2, rest1 = b :: rest2 := by
      cases rest1 with | nil => simp [heq1] at hlen | cons h t => exact ⟨h, t, rfl⟩
    simp only [heq1, heq2, List.take, List.sum_cons, List.sum_nil]
    simp only [heq1, heq2, List.head!_cons, List.tail_cons] at hK_eq hν₁_eq
    omega
  have hsum_split : (Finset.Ico 2 m).sum (fun i => 3^(m - 1 - i) * 2^(partialNuSum σ i)) =
      3^(m - 3) * 2^(K + ν₁) + (Finset.Ico 3 m).sum (fun i => 3^(m - 1 - i) * 2^(partialNuSum σ i)) := by
    have h23 : Finset.Ico 2 m = {2} ∪ Finset.Ico 3 m := by
      ext x; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico]; omega
    rw [h23, Finset.sum_union (by simp)]
    simp only [Finset.sum_singleton, hpns2]
    have hexp : m - 1 - 2 = m - 3 := by omega
    rw [hexp]
  have hL_exp : L = 3^(m - 1) + 3^(m - 2) * 2^K +
      (3^(m - 3) * 2^(K + ν₁) + (Finset.Ico 3 m).sum (fun i => 3^(m - 1 - i) * 2^(partialNuSum σ i))) +
      n₀ * 3^m := by
    show waveSumPattern σ + n₀ * 3^m = _
    rw [hws, hsum_split]
  have hn₀_3m : n₀ * 3^m = (2^K * q - 1) * 3^(m - 1) := by
    have h3n₀ : 3 * n₀ = 2^K * q - 1 := hn₀_div
    calc n₀ * 3^m = n₀ * (3 * 3^(m - 1)) := by
           conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ']
      _ = (n₀ * 3) * 3^(m - 1) := by ring
      _ = (3 * n₀) * 3^(m - 1) := by ring
      _ = (2^K * q - 1) * 3^(m - 1) := by rw [h3n₀]
  have hcomb : 3^(m - 1) + 3^(m - 2) * 2^K + 3^(m - 3) * 2^(K + ν₁) + (2^K * q - 1) * 3^(m - 1) =
      2^(K + ν₁) * 3^(m - 3) * (3 * r + 1) := by
    have h1_3q : 1 + 3 * q = 2^ν₁ * r := by omega
    have h3m1_eq : 3^(m - 1) = 3 * 3^(m - 2) := by
      conv_lhs => rw [show m - 1 = (m - 2) + 1 by omega, pow_succ']
    have h3m2_eq : 3^(m - 2) = 3 * 3^(m - 3) := by
      conv_lhs => rw [show m - 2 = (m - 3) + 1 by omega, pow_succ']
    have h2K_ge1 : 2^K ≥ 1 := Nat.one_le_pow K 2 (by norm_num)
    have h2Kq_ge1 : 2^K * q ≥ 1 := Nat.mul_pos h2K_ge1 hq_pos
    have hcomb1 : (2^K * q - 1) * 3^(m - 1) + 3^(m - 1) = 2^K * q * 3^(m - 1) := by
      have h2Kq_pos : 2^K * q > 0 := Nat.mul_pos (Nat.pow_pos (by norm_num : 0 < 2)) hq_pos
      rw [Nat.sub_one_mul, Nat.sub_add_cancel]
      exact Nat.le_mul_of_pos_left (3^(m - 1)) h2Kq_pos
    calc 3^(m - 1) + 3^(m - 2) * 2^K + 3^(m - 3) * 2^(K + ν₁) + (2^K * q - 1) * 3^(m - 1)
        = (2^K * q - 1) * 3^(m - 1) + 3^(m - 1) + 3^(m - 2) * 2^K + 3^(m - 3) * 2^(K + ν₁) := by ring
      _ = 2^K * q * 3^(m - 1) + 3^(m - 2) * 2^K + 3^(m - 3) * 2^(K + ν₁) := by rw [hcomb1]
      _ = 2^K * (q * 3^(m - 1) + 3^(m - 2)) + 3^(m - 3) * 2^(K + ν₁) := by ring
      _ = 2^K * (q * (3 * 3^(m - 2)) + 3^(m - 2)) + 3^(m - 3) * 2^(K + ν₁) := by rw [h3m1_eq]
      _ = 2^K * 3^(m - 2) * (3*q + 1) + 3^(m - 3) * 2^(K + ν₁) := by ring
      _ = 2^K * 3^(m - 2) * (2^ν₁ * r) + 3^(m - 3) * 2^(K + ν₁) := by rw [h3q1_eq]
      _ = 2^(K + ν₁) * 3^(m - 2) * r + 2^(K + ν₁) * 3^(m - 3) := by rw [pow_add]; ring
      _ = 2^(K + ν₁) * (3^(m - 2) * r + 3^(m - 3)) := by ring
      _ = 2^(K + ν₁) * ((3 * 3^(m - 3)) * r + 3^(m - 3)) := by rw [h3m2_eq]
      _ = 2^(K + ν₁) * 3^(m - 3) * (3 * r + 1) := by ring
  have h3r1_eq_2s : 3 * r + 1 = 2 * s := h2s.symm
  have hsum_eq_H' : (Finset.Ico 3 m).sum (fun i => 3^(m - 1 - i) * 2^(partialNuSum σ i)) =
      2^(K + ν₁ + 1) * H' := inner_sum_eq_higherTerms hlen hvalid hK_eq hν₁_eq
  calc L = 3^(m - 1) + 3^(m - 2) * 2^K +
             (3^(m - 3) * 2^(K + ν₁) + (Finset.Ico 3 m).sum (fun i => 3^(m - 1 - i) * 2^(partialNuSum σ i))) +
             n₀ * 3^m := hL_exp
    _ = (3^(m - 1) + 3^(m - 2) * 2^K + 3^(m - 3) * 2^(K + ν₁) + (2^K * q - 1) * 3^(m - 1)) +
        (Finset.Ico 3 m).sum (fun i => 3^(m - 1 - i) * 2^(partialNuSum σ i)) := by rw [hn₀_3m]; ring
    _ = 2^(K + ν₁) * 3^(m - 3) * (3 * r + 1) +
        (Finset.Ico 3 m).sum (fun i => 3^(m - 1 - i) * 2^(partialNuSum σ i)) := by rw [hcomb]
    _ = 2^(K + ν₁) * 3^(m - 3) * (2 * s) +
        (Finset.Ico 3 m).sum (fun i => 3^(m - 1 - i) * 2^(partialNuSum σ i)) := by rw [h3r1_eq_2s]
    _ = 2^(K + ν₁ + 1) * 3^(m - 3) * s +
        (Finset.Ico 3 m).sum (fun i => 3^(m - 1 - i) * 2^(partialNuSum σ i)) := by rw [pow_succ]; ring
    _ = 2^(K + ν₁ + 1) * 3^(m - 3) * s + 2^(K + ν₁ + 1) * H' := by rw [hsum_eq_H']
    _ = 2^(K + ν₁ + 1) * (3^(m - 3) * s + H') := by ring

/-- Wave decomposition algebraic structure for Case 3.
    Proves: L = 2^{K+ν₁+1} · (3^{m-3}·s + H')
    Therefore: v₂(L) = K + ν₁ + 1 + v₂(3^{m-3}·s + H')

    Note: H' is odd iff σ[2] = 1. See v2_case3_inner_bound for general case. -/
theorem case3_wave_decomposition
    {σ : List ℕ} {n₀ K ν₁ : ℕ}
    (hlen : σ.length ≥ 4)
    (hvalid : isValidPattern σ)
    (hK_eq : σ.head! = K)
    (hν₁_eq : σ.tail.head! = ν₁)
    (hK : padicValNat 2 (1 + 3 * n₀) = K)
    (hcase3 : padicValNat 2 (3 * ((1 + 3 * n₀) / 2^K) + 1) = ν₁)
    (hn₀_pos : n₀ > 0) :
    let q := case3_q n₀ K
    let r := case3_r q ν₁
    let s := case3_s r
    let m := σ.length
    let L := waveSumPattern σ + n₀ * 3^m
    let H' := higherTerms σ K ν₁
    padicValNat 2 L = K + ν₁ + 1 + padicValNat 2 (3^(m - 3) * s + H') := by
  intro q r s m L H'
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- Key identities
  have hn₀_eq : 1 + 3 * n₀ = 2^K * q := n0_from_equal_case hK
  have hq_pos : q > 0 := by
    have h13n₀_pos : 1 + 3 * n₀ > 0 := by omega
    have hdiv : 2^K ∣ 1 + 3 * n₀ := by rw [← hK]; exact pow_padicValNat_dvd
    have h2K_pos : 2^K > 0 := by positivity
    show case3_q n₀ K > 0
    simp only [case3_q]
    exact Nat.div_pos (Nat.le_of_dvd h13n₀_pos hdiv) h2K_pos
  have h3q1_eq : 3 * q + 1 = 2^ν₁ * r := case3_expansion hcase3
  have hq_odd := q_odd_equal_case hK hn₀_pos
  have hr_odd := r_odd_case3 hcase3 hq_pos
  -- s = (3*r + 1) / 2, and since r is odd, 2*s = 3*r + 1
  have h2s : 2 * s = 3 * r + 1 := by
    obtain ⟨k, hk⟩ := hr_odd
    show 2 * case3_s r = 3 * r + 1
    simp only [case3_s]
    have hr_eq : r = 2 * k + 1 := hk
    have h3r1_even : 2 ∣ 3 * r + 1 := ⟨3 * k + 2, by omega⟩
    exact Nat.mul_div_cancel' h3r1_even
  -- The inner term 3^(m-3)*s + H' is positive
  have hinner_pos : 3^(m - 3) * s + H' > 0 := by
    have h3pow_pos : 3^(m - 3) > 0 := by positivity
    have hs_pos : s > 0 := by
      show case3_s r > 0
      simp only [case3_s]
      have hr_pos : r > 0 := by
        show case3_r q ν₁ > 0
        unfold case3_r
        have h3q1_pos : 3 * q + 1 > 0 := by omega
        have hdiv : 2^ν₁ ∣ 3 * q + 1 := by rw [← hcase3]; exact pow_padicValNat_dvd
        have h2ν₁_pos : 2^ν₁ > 0 := by positivity
        exact Nat.div_pos (Nat.le_of_dvd h3q1_pos hdiv) h2ν₁_pos
      have h3r1 : 3 * r + 1 ≥ 2 := by omega
      exact Nat.div_pos h3r1 (by norm_num)
    exact Nat.add_pos_left (Nat.mul_pos h3pow_pos hs_pos) _
  -- The algebraic identity: L = 2^(K + ν₁ + 1) * (3^(m-3) * s + H')
  -- This is the core wave decomposition result
  -- For the full proof, we use the verified identity from wave_decomp_identity
  -- which combines leading terms and factors out 2^(K+ν₁+1)
  have h2pow_pos : 2^(K + ν₁ + 1) > 0 := by positivity
  -- The v₂ calculation follows from the factorization
  have hL_factor : L = 2^(K + ν₁ + 1) * (3^(m - 3) * s + H') :=
    wave_decomp_identity hlen hvalid hK_eq hν₁_eq hK hcase3 hn₀_pos
  rw [hL_factor]
  rw [padicValNat.mul (by positivity : 2^(K + ν₁ + 1) ≠ 0) (by omega : 3^(m - 3) * s + H' ≠ 0)]
  rw [padicValNat.prime_pow]

/-- H' is odd when σ[2] = 1 (proven from structure of higherTerms) -/
theorem higherTerms_odd_minimal :
    ∀ {σ : List ℕ} {K ν₁ : ℕ},
      σ.length ≥ 4 →
      isValidPattern σ →
      σ.head! = K →
      σ.tail.head! = ν₁ →
      (σ.tail.tail).head! = 1 →
      Odd (higherTerms σ K ν₁) := by
  intro σ K ν₁ hlen hvalid hK hν₁ hσ2
  unfold higherTerms
  set m := σ.length
  -- Key: partialNuSum σ 3 = K + ν₁ + 1 when first three elements are K, ν₁, 1
  have h_pns3 : partialNuSum σ 3 = K + ν₁ + 1 := by
    unfold partialNuSum
    have hlen3 : σ.length ≥ 3 := by omega
    have htake3 : σ.take 3 = [σ.head!, σ.tail.head!, (σ.tail.tail).head!] := by
      match σ, hlen3 with
      | a :: b :: c :: _, _ => simp
    rw [htake3, List.sum_cons, List.sum_cons, List.sum_singleton, hK, hν₁, hσ2]
    ring
  -- Check if the sum is empty or nonempty
  by_cases hIco_empty : (Finset.Ico 2 (m - 1)).Nonempty
  · -- Nonempty: split at j=2
    have h2_mem : 2 ∈ Finset.Ico 2 (m - 1) := by simp [Finset.mem_Ico]; omega
    rw [← Finset.add_sum_erase _ _ h2_mem]
    -- j=2 term: exponent is pns(3) - K - ν₁ - 1 = 0
    have hfirst_exp : partialNuSum σ (2 + 1) - K - ν₁ - 1 = 0 := by rw [h_pns3]; omega
    have hfirst : 3^(m - 2 - 2) * 2^(partialNuSum σ (2 + 1) - K - ν₁ - 1) = 3^(m - 4) := by
      rw [hfirst_exp]
      have hexp_eq : m - 2 - 2 = m - 4 := by omega
      simp [hexp_eq]
    rw [hfirst]
    have h3pow_odd : Odd (3^(m - 4)) := Odd.pow (by decide : Odd 3)
    -- Rest is even (each term has 2^(≥1) factor)
    have hrest_even : Even (((Finset.Ico 2 (m - 1)).erase 2).sum (fun j =>
        3^(m - 2 - j) * 2^(partialNuSum σ (j + 1) - K - ν₁ - 1))) := by
      apply Finset.even_sum
      intro j hj
      have hj_mem := Finset.mem_erase.mp hj
      have hj_ne2 : j ≠ 2 := hj_mem.1
      have hj_range : j ∈ Finset.Ico 2 (m - 1) := hj_mem.2
      simp only [Finset.mem_Ico] at hj_range
      have hj_ge3 : j ≥ 3 := by omega
      -- partialNuSum σ (j+1) ≥ K + ν₁ + 2 since σ[i] ≥ 1 for all i
      have h_pns_ge : partialNuSum σ (j + 1) ≥ K + ν₁ + 2 := by
        -- partialNuSum is sum of first j+1 elements
        -- For j ≥ 3, this includes at least 4 elements: K, ν₁, 1, and at least one more
        -- Each element is ≥ 1 (valid pattern), so sum ≥ K + ν₁ + 1 + 1 = K + ν₁ + 2
        unfold partialNuSum
        have hlen4 : σ.length ≥ 4 := hlen
        have hsum_ge : (σ.take (j + 1)).sum ≥ (σ.take 4).sum := by
          have hprefix : (σ.take 4).IsPrefix (σ.take (j + 1)) := by
            rw [List.take_isPrefix_take]
            left; omega
          have hsublist : (σ.take 4).Sublist (σ.take (j + 1)) := hprefix.sublist
          have hnn : ∀ a ∈ σ.take (j + 1), 0 ≤ a := fun _ _ => Nat.zero_le _
          exact hsublist.sum_le_sum hnn
        have h4sum : (σ.take 4).sum ≥ K + ν₁ + 2 := by
          have htake4 : σ.take 4 = [σ.head!, σ.tail.head!, (σ.tail.tail).head!, (σ.tail.tail.tail).head!] := by
            match σ, hlen4 with
            | a :: b :: c :: d :: _, _ => simp
          rw [htake4, List.sum_cons, List.sum_cons, List.sum_cons, List.sum_singleton, hK, hν₁, hσ2]
          have h4th_ge1 : (σ.tail.tail.tail).head! ≥ 1 := by
            have hmem : (σ.tail.tail.tail).head! ∈ σ := by
              match σ, hlen4 with
              | a :: b :: c :: d :: _, _ => simp
            exact hvalid _ hmem
          omega
        omega
      -- Exponent of 2 is ≥ 1
      have hexp_ge1 : partialNuSum σ (j + 1) - K - ν₁ - 1 ≥ 1 := by omega
      have h2pow_even : Even (2^(partialNuSum σ (j + 1) - K - ν₁ - 1)) := by
        have hk : partialNuSum σ (j + 1) - K - ν₁ - 1 = (partialNuSum σ (j + 1) - K - ν₁ - 2) + 1 := by omega
        rw [hk, pow_succ']
        exact even_two_mul _
      exact Even.mul_left h2pow_even _
    exact Odd.add_even h3pow_odd hrest_even
  · -- Empty sum: m - 1 ≤ 2, so m ≤ 3, contradicting m ≥ 4
    simp only [Finset.not_nonempty_iff_eq_empty, Finset.Ico_eq_empty_iff] at hIco_empty
    omega

/-- Lower bound on waveSum for nonempty patterns (discharged from WaveSumProperties) -/
theorem waveSumPattern_lower_bound' : ∀ {σ : List ℕ}, σ.length ≥ 1 → waveSumPattern σ > 0 := by
  intro σ hlen
  have h := Collatz.waveSumPattern_lower_bound hlen
  calc waveSumPattern σ ≥ 3^(σ.length - 1) := h
    _ ≥ 1 := Nat.one_le_pow _ _ (by omega)
    _ > 0 := by omega

/-- For minimal patterns, H' is odd -/
lemma higherTerms_odd_minimal' {m : ℕ} (hm : m ≥ 4) :
    let σ := List.replicate m 1
    let K := 1
    let ν₁ := 1
    Odd (higherTerms σ K ν₁) := by
  -- For σ = List.replicate m 1:
  -- - partialNuSum σ (j+1) = j + 1 (sum of j+1 ones)
  -- - higherTerms = Σ_{j=2}^{m-2} 3^(m-2-j) * 2^(j-2)
  -- - For j=2: 3^(m-4) * 2^0 = 3^(m-4) (odd)
  -- - For j≥3: 3^(m-2-j) * 2^(j-2) is even (factor of 2)
  -- - Sum = odd + even = odd
  simp only
  unfold higherTerms
  have hlen : (List.replicate m 1).length = m := List.length_replicate ..
  simp only [hlen]
  -- partialNuSum of replicate equals j
  have h_pns : ∀ j ≤ m, partialNuSum (List.replicate m 1) j = j := by
    intro j hj
    unfold partialNuSum
    simp only [List.take_replicate, List.sum_replicate, smul_eq_mul, mul_one, min_eq_left hj]
  by_cases hm4 : m = 4
  · -- m = 4: Ico 2 3 = {2}, only one term which is odd
    subst hm4
    have hIco : Finset.Ico 2 (4 - 1) = {2} := by decide
    rw [hIco, Finset.sum_singleton]
    have hpns3 : partialNuSum (List.replicate 4 1) 3 = 3 := h_pns 3 (by omega)
    simp only [hpns3]
    norm_num
  · -- m > 4: split into j=2 and j≥3
    have hm_gt4 : m > 4 := by omega
    have hIco_eq : Finset.Ico 2 (m - 1) = {2} ∪ Finset.Ico 3 (m - 1) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton]; omega
    have hdisj : Disjoint {2} (Finset.Ico 3 (m - 1)) := by
      simp only [Finset.disjoint_singleton_left, Finset.mem_Ico, not_and, not_lt]; omega
    rw [hIco_eq, Finset.sum_union hdisj, Finset.sum_singleton]
    -- First term: 3^(m-4) * 2^0 = 3^(m-4) (odd)
    have hpns3 : partialNuSum (List.replicate m 1) 3 = 3 := h_pns 3 (by omega)
    have hexp_sub : m - 2 - 2 = m - 4 := by omega
    have hfirst : 3^(m - 2 - 2) * 2^(partialNuSum (List.replicate m 1) (2 + 1) - 1 - 1 - 1) =
        3^(m - 4) := by simp only [hpns3, hexp_sub]; ring
    rw [hfirst]
    have h3pow_odd : Odd (3^(m - 4)) := Odd.pow (by decide : Odd 3)
    -- Second sum is even (each term has factor 2^(j-2) ≥ 2^1 for j ≥ 3)
    have hsecond_even : Even ((Finset.Ico 3 (m - 1)).sum fun j =>
        3^(m - 2 - j) * 2^(partialNuSum (List.replicate m 1) (j + 1) - 1 - 1 - 1)) := by
      apply Finset.even_sum
      intro j hj
      simp only [Finset.mem_Ico] at hj
      have hpnsj : partialNuSum (List.replicate m 1) (j + 1) = j + 1 := h_pns (j + 1) (by omega)
      simp only [hpnsj]
      have hexp_eq : j + 1 - 1 - 1 - 1 = j - 2 := by omega
      rw [hexp_eq]
      have hj_ge3 : j ≥ 3 := hj.1
      have hexp_ge1 : j - 2 ≥ 1 := by omega
      have h2pow_even : Even (2^(j - 2)) := by
        have hsplit : j - 2 = 1 + (j - 3) := by omega
        rw [hsplit, pow_add, pow_one]
        exact Even.mul_right (by decide : Even 2) _
      exact Even.mul_left h2pow_even _
    exact Odd.add_even h3pow_odd hsecond_even

/-! ### Auxiliary lemmas for valuation analysis -/

/-- When x is odd, x + 1 is even and we can analyze v₂(x + 1) -/
lemma odd_add_one_even {x : ℕ} (hx : Odd x) : Even (x + 1) := by
  obtain ⟨k, hk⟩ := hx
  use k + 1; omega

/-- v₂(2x) = 1 + v₂(x) for x > 0 -/
lemma v2_double {x : ℕ} (hx : x ≠ 0) : padicValNat 2 (2 * x) = 1 + padicValNat 2 x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat.mul (by norm_num : (2 : ℕ) ≠ 0) hx]
  simp [padicValNat.self]

/-- For odd a, b: v₂(a + b) = 1 + v₂((a + b) / 2) -/
lemma v2_odd_sum {a b : ℕ} (ha : Odd a) (hb : Odd b) (hab_pos : a + b > 0) :
    padicValNat 2 (a + b) = 1 + padicValNat 2 ((a + b) / 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- odd + odd = even
  have hab_even : Even (a + b) := Odd.add_odd ha hb
  obtain ⟨k, hk⟩ := hab_even
  have hk_pos : k ≠ 0 := by omega
  have h2k : a + b = 2 * k := by omega
  rw [h2k, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  rw [padicValNat.mul (by norm_num) hk_pos]
  simp [padicValNat.self]

/-- Ultrametric property: when valuations differ, sum has minimum valuation -/
lemma padicValNat_add_eq_min' {p a b : ℕ} [hp : Fact (Nat.Prime p)]
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) (hdiff : padicValNat p a ≠ padicValNat p b) :
    padicValNat p (a + b) = min (padicValNat p a) (padicValNat p b) := by
  rcases lt_trichotomy (padicValNat p a) (padicValNat p b) with hlt | heq | hgt
  · -- Case: v_p(a) < v_p(b)
    rw [min_eq_left (le_of_lt hlt)]
    apply le_antisymm
    · -- Show: v_p(a+b) ≤ v_p(a) by contradiction
      by_contra hle
      push_neg at hle
      have hdvd_ab : p ^ (padicValNat p a + 1) ∣ a + b :=
        padicValNat_dvd_iff_le hab |>.mpr hle
      have hdvd_b : p ^ (padicValNat p a + 1) ∣ b :=
        padicValNat_dvd_iff_le hb |>.mpr (by omega)
      have hdvd_a : p ^ (padicValNat p a + 1) ∣ a := by
        have h1 := Nat.dvd_sub hdvd_ab hdvd_b
        simp only [Nat.add_sub_cancel_right] at h1
        exact h1
      have hle_a := padicValNat_dvd_iff_le ha |>.mp hdvd_a
      omega
    · -- Show: v_p(a) ≤ v_p(a+b)
      apply padicValNat_dvd_iff_le hab |>.mp
      have hdvd_a : p ^ padicValNat p a ∣ a := padicValNat_dvd_iff_le ha |>.mpr le_rfl
      have hdvd_b : p ^ padicValNat p a ∣ b := padicValNat_dvd_iff_le hb |>.mpr (by omega)
      exact Nat.dvd_add hdvd_a hdvd_b
  · exact (hdiff heq).elim
  · -- Case: v_p(a) > v_p(b) - symmetric
    rw [min_eq_right (le_of_lt hgt)]
    apply le_antisymm
    · by_contra hle
      push_neg at hle
      have hdvd_ab : p ^ (padicValNat p b + 1) ∣ a + b :=
        padicValNat_dvd_iff_le hab |>.mpr hle
      have hdvd_a : p ^ (padicValNat p b + 1) ∣ a :=
        padicValNat_dvd_iff_le ha |>.mpr (by omega)
      have hdvd_b : p ^ (padicValNat p b + 1) ∣ b := by
        have h1 := Nat.dvd_sub hdvd_ab hdvd_a
        simp only [Nat.add_sub_cancel_left] at h1
        exact h1
      have hle_b := padicValNat_dvd_iff_le hb |>.mp hdvd_b
      omega
    · apply padicValNat_dvd_iff_le hab |>.mp
      have hdvd_a : p ^ padicValNat p b ∣ a := padicValNat_dvd_iff_le ha |>.mpr (by omega)
      have hdvd_b : p ^ padicValNat p b ∣ b := padicValNat_dvd_iff_le hb |>.mpr le_rfl
      exact Nat.dvd_add hdvd_a hdvd_b

/-- Ultrametric inequality for 2-adic valuation (disjunctive form) -/
lemma v2_ultrametric {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    padicValNat 2 (x + y) ≥ min (padicValNat 2 x) (padicValNat 2 y) ∨
    padicValNat 2 (x + y) = min (padicValNat 2 x) (padicValNat 2 y) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hdiff : padicValNat 2 x = padicValNat 2 y
  · -- Equal valuations: sum valuation is ≥ min
    left
    rw [hdiff, min_self]
    -- 2^v divides both, so divides sum
    have hdvd_x : 2 ^ padicValNat 2 y ∣ x := padicValNat_dvd_iff_le hx |>.mpr (by omega)
    have hdvd_y : 2 ^ padicValNat 2 y ∣ y := padicValNat_dvd_iff_le hy |>.mpr le_rfl
    have hdvd_sum : 2 ^ padicValNat 2 y ∣ x + y := Nat.dvd_add hdvd_x hdvd_y
    exact padicValNat_dvd_iff_le hxy |>.mp hdvd_sum
  · -- Different valuations: sum valuation equals min
    right
    exact padicValNat_add_eq_min' hx hy hxy hdiff

/-- When v₂(x) < v₂(y), we have v₂(x + y) = v₂(x) -/
lemma v2_add_of_lt {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0)
    (hlt : padicValNat 2 x < padicValNat 2 y) :
    padicValNat 2 (x + y) = padicValNat 2 x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdiff : padicValNat 2 x ≠ padicValNat 2 y := Nat.ne_of_lt hlt
  rw [padicValNat_add_eq_min' hx hy hxy hdiff]
  exact Nat.min_eq_left (Nat.le_of_lt hlt)

/-- v₂(H') = σ[2] - 1 when σ[2] ≥ 1

    Proof: H' = Σ_{j≥2} 3^{m-2-j} · 2^{pns(j+1) - K - ν₁ - 1}
    The j=2 term has exponent pns(3) - K - ν₁ - 1 = σ[2] - 1
    All j ≥ 3 terms have larger exponents (≥ σ[2] + σ[3] - 1 > σ[2] - 1)
    By ultrametric, v₂(H') = σ[2] - 1 -/
lemma v2_higherTerms {σ : List ℕ} {K ν₁ : ℕ}
    (hlen : σ.length ≥ 4)
    (hvalid : isValidPattern σ)
    (hK_eq : σ.head! = K)
    (hν₁_eq : σ.tail.head! = ν₁) :
    let σ2 := (σ.tail.tail).head!
    padicValNat 2 (higherTerms σ K ν₁) = σ2 - 1 := by
  intro σ2
  have hpns3 := partialNuSum_at_3 (by omega : σ.length ≥ 3)
  rw [hK_eq, hν₁_eq] at hpns3
  have hexp_j2 : partialNuSum σ 3 - K - ν₁ - 1 = σ2 - 1 := by rw [hpns3]; omega
  have hσ2_ge1 : σ2 ≥ 1 := by
    have hc_mem : (σ.tail.tail).head! ∈ σ := by
      cases σ with | nil => simp at hlen | cons a as =>
      cases as with | nil => simp at hlen | cons b bs =>
      cases bs with | nil => simp at hlen | cons c cs => simp
    exact hvalid (σ.tail.tail).head! hc_mem
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let m := σ.length
  have h23 : Finset.Ico 2 (m - 1) = {2} ∪ Finset.Ico 3 (m - 1) := by
    ext x; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico]; omega
  have hterm2 : 3^(m - 2 - 2) * 2^(partialNuSum σ (2 + 1) - K - ν₁ - 1) = 3^(m - 4) * 2^(σ2 - 1) := by
    rw [show m - 2 - 2 = m - 4 by omega, hexp_j2]
  have h_v2_j2 : padicValNat 2 (3^(m - 4) * 2^(σ2 - 1)) = σ2 - 1 := by
    rw [padicValNat.mul (by positivity) (by positivity)]
    have h3_odd : Odd (3^(m - 4)) := Odd.pow ⟨1, rfl⟩
    have hv2_3 : padicValNat 2 (3^(m - 4)) = 0 :=
      padicValNat.eq_zero_of_not_dvd h3_odd.not_two_dvd_nat
    rw [hv2_3, zero_add, padicValNat.prime_pow]
  have h_rest_exp : ∀ j ∈ Finset.Ico 3 (m - 1),
      partialNuSum σ (j + 1) - K - ν₁ - 1 ≥ σ2 := by
    intro j hj
    simp only [Finset.mem_Ico] at hj
    have hmono := partialNuSum_mono_valid hvalid 3 (j + 1) (by omega) (by omega) (by omega)
    rw [hpns3] at hmono; omega
  by_cases hempty : (Finset.Ico 3 (m - 1)).card = 0
  · have hm4 : σ.length = 4 := by
      simp only [Finset.card_eq_zero, Finset.Ico_eq_empty_iff] at hempty
      omega
    unfold higherTerms
    simp only [hm4, show Finset.Ico 2 3 = {2} by decide]
    rw [Finset.sum_singleton]
    have h_exp : partialNuSum σ (2 + 1) - K - ν₁ - 1 = σ2 - 1 := hexp_j2
    simp only [show (4 : ℕ) - 2 - 2 = 0 by norm_num, pow_zero, one_mul, h_exp]
    exact padicValNat.prime_pow (σ2 - 1)
  · have hrest_v2_ge : ∀ j ∈ Finset.Ico 3 (m - 1),
        padicValNat 2 (3^(m - 2 - j) * 2^(partialNuSum σ (j + 1) - K - ν₁ - 1)) ≥ σ2 := by
      intro j hj
      rw [padicValNat.mul (by positivity) (by positivity)]
      have h3_odd : Odd (3^(m - 2 - j)) := Odd.pow ⟨1, rfl⟩
      have hv2_3 : padicValNat 2 (3^(m - 2 - j)) = 0 :=
        padicValNat.eq_zero_of_not_dvd h3_odd.not_two_dvd_nat
      rw [hv2_3, zero_add, padicValNat.prime_pow]
      exact h_rest_exp j hj
    unfold higherTerms
    rw [h23, Finset.sum_union (by simp), Finset.sum_singleton, hterm2]
    have hj2_pos : 3^(m - 4) * 2^(σ2 - 1) > 0 := by positivity
    have hj2_ne : 3^(m - 4) * 2^(σ2 - 1) ≠ 0 := by positivity
    by_cases hrest_zero : (Finset.Ico 3 (m - 1)).sum (fun j =>
        3^(m - 2 - j) * 2^(partialNuSum σ (j + 1) - K - ν₁ - 1)) = 0
    · rw [hrest_zero, add_zero, h_v2_j2]
    · have hrest_pos : (Finset.Ico 3 (m - 1)).sum (fun j =>
          3^(m - 2 - j) * 2^(partialNuSum σ (j + 1) - K - ν₁ - 1)) > 0 := by
        apply Nat.pos_of_ne_zero hrest_zero
      have hsum_ne : 3^(m - 4) * 2^(σ2 - 1) +
          (Finset.Ico 3 (m - 1)).sum (fun j =>
            3^(m - 2 - j) * 2^(partialNuSum σ (j + 1) - K - ν₁ - 1)) ≠ 0 := by omega
      have hrest_v2_min : padicValNat 2 ((Finset.Ico 3 (m - 1)).sum (fun j =>
          3^(m - 2 - j) * 2^(partialNuSum σ (j + 1) - K - ν₁ - 1))) ≥ σ2 := by
        have hdiv_all : ∀ j ∈ Finset.Ico 3 (m - 1),
            2^σ2 ∣ 3^(m - 2 - j) * 2^(partialNuSum σ (j + 1) - K - ν₁ - 1) := by
          intro j hj
          have hexp := h_rest_exp j hj
          have : 2^σ2 ∣ 2^(partialNuSum σ (j + 1) - K - ν₁ - 1) :=
            pow_dvd_pow 2 hexp
          exact Dvd.dvd.mul_left this _
        have hdiv_sum : 2^σ2 ∣ (Finset.Ico 3 (m - 1)).sum (fun j =>
            3^(m - 2 - j) * 2^(partialNuSum σ (j + 1) - K - ν₁ - 1)) :=
          Finset.dvd_sum hdiv_all
        exact padicValNat_dvd_iff_le hrest_zero |>.mp hdiv_sum
      have hv2_diff : padicValNat 2 (3^(m - 4) * 2^(σ2 - 1)) ≠
          padicValNat 2 ((Finset.Ico 3 (m - 1)).sum (fun j =>
            3^(m - 2 - j) * 2^(partialNuSum σ (j + 1) - K - ν₁ - 1))) := by
        rw [h_v2_j2]
        omega
      rw [padicValNat_add_eq_min' hj2_ne hrest_zero hsum_ne hv2_diff, h_v2_j2]
      apply Nat.min_eq_left
      omega


end Case3

end Collatz
