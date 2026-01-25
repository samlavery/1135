/-
# OrbitPatternBridge.lean - Bridge lemmas for forward reference resolution

This file provides lemmas that connect orbit patterns to constraints,
enabling their use in earlier proofs in DriftLemma.lean.

The key lemmas here are proven independently using only:
- Basic.lean definitions (T, v2, etc.)
- PatternDefs.lean (patternSum, patternConstraint, allOnesPattern)
- AllOnesPattern.lean (constraint properties)

These lemmas enable the no_infinite_patterns_implies_bounded proof.
-/

import Collatz.Basic
import Collatz.PatternDefs
import Collatz.AllOnesPattern
import Mathlib

namespace Collatz.OrbitPatternBridge

open scoped BigOperators

noncomputable section

/-! ## Core definitions duplicated from DriftLemma (to avoid circular import) -/

/-- 2-adic valuation of 3x+1 -/
def nu (x : ℕ) : ℕ := padicValNat 2 (3 * x + 1)

/-- Syracuse function: T(x) = (3x+1)/2^ν where ν = v₂(3x+1) -/
def T (x : ℕ) : ℕ := (3 * x + 1) / 2^(nu x)

/-- Syracuse orbit: iterating T starting from n -/
def orbit (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => T (orbit n k)

/-- Cumulative ν-sum: S_m = Σ_{i<m} ν_i -/
def nuSum (n : ℕ) (t : ℕ) : ℕ := ((List.range t).map (fun i => nu (orbit n i))).sum

/-- Wave sum: c_m = 3·c_{m-1} + 2^{S_{m-1}} with c_0 = 0 -/
def waveSum (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => 3 * waveSum n m + 2^(nuSum n m)

/-- The orbit pattern: list of ν values for first m steps -/
def orbitPattern (n m : ℕ) : List ℕ :=
  (List.range m).map (fun i => nu (orbit n i))

/-! ## Basic properties -/

lemma orbitPattern_length (n m : ℕ) : (orbitPattern n m).length = m := by
  simp [orbitPattern]

lemma orbitPattern_sum (n m : ℕ) : (orbitPattern n m).sum = nuSum n m := rfl

/-- nu ≥ 1 for odd inputs -/
lemma nu_ge_one_of_odd (x : ℕ) (hx : Odd x) : nu x ≥ 1 := by
  unfold nu
  have h_even : 2 ∣ 3 * x + 1 := by
    obtain ⟨k, hk⟩ := hx
    use 3 * k + 2
    omega
  have h_ne_zero : 3 * x + 1 ≠ 0 := by omega
  exact one_le_padicValNat_of_dvd h_ne_zero h_even

/-- Orbit stays odd if initial value is odd -/
lemma orbit_is_odd (n : ℕ) (hn : Odd n) (k : ℕ) : Odd (orbit n k) := by
  induction k with
  | zero => simp [orbit]; exact hn
  | succ j ih =>
    simp only [orbit]
    unfold T
    set x := orbit n j with hx
    -- T(x) = (3x+1) / 2^{v_2(3x+1)} is odd: we divide out all factors of 2
    have h_ne : 3 * x + 1 ≠ 0 := by omega
    have h_dvd := pow_padicValNat_dvd (p := 2) (n := 3 * x + 1)
    -- After dividing by 2^{v_2(n)}, the result is not divisible by 2
    have h_not_dvd : ¬(2 ∣ (3 * x + 1) / 2^(padicValNat 2 (3 * x + 1))) := by
      intro h_two_dvd
      have h_pow_succ : 2^(padicValNat 2 (3 * x + 1) + 1) ∣ 3 * x + 1 := by
        rw [pow_succ]
        exact Nat.mul_dvd_of_dvd_div h_dvd h_two_dvd
      exact pow_succ_padicValNat_not_dvd h_ne h_pow_succ
    -- ¬(2 ∣ y) → Odd y
    rw [Nat.two_dvd_ne_zero] at h_not_dvd
    exact Nat.odd_iff.mpr h_not_dvd

/-- orbitPattern is always valid (each entry ≥ 1) for odd n > 0 -/
lemma orbitPattern_valid (n m : ℕ) (hn : Odd n) (hpos : n > 0) :
    Collatz.isValidPattern (orbitPattern n m) := by
  intro ν hν
  simp only [orbitPattern, List.mem_map, List.mem_range] at hν
  obtain ⟨i, _, rfl⟩ := hν
  exact nu_ge_one_of_odd (orbit n i) (orbit_is_odd n hn i)

/-- Partial sum of orbitPattern equals nuSum -/
lemma partialNuSum_orbitPattern_eq_nuSum (n m j : ℕ) (hj : j ≤ m) :
    Collatz.partialNuSum (orbitPattern n m) j = nuSum n j := by
  simp only [Collatz.partialNuSum, orbitPattern]
  rw [← List.map_take]
  have h_take : (List.range m).take j = List.range j := by
    rw [List.take_range]
    simp only [Nat.min_eq_left hj]
  rw [h_take]
  rfl

/-! ## Key bridge lemmas -/

/-- If orbitPattern has sum = length (nuSum = m), then it equals allOnesPattern -/
lemma orbitPattern_nuSum_eq_m_implies_allOnes (n m : ℕ) (hn : Odd n) (hpos : n > 0)
    (h_nusum : nuSum n m = m) :
    orbitPattern n m = Collatz.allOnesPattern m := by
  have h_valid := orbitPattern_valid n m hn hpos
  have h_sum : Collatz.patternSum (orbitPattern n m) = (orbitPattern n m).length := by
    simp only [Collatz.patternSum, orbitPattern_sum, orbitPattern_length, h_nusum]
  have h_eq := Collatz.valid_pattern_sum_eq_length_implies_allOnes (orbitPattern n m) h_valid h_sum
  simp only [orbitPattern_length] at h_eq
  exact h_eq

/-- Fundamental orbit formula: orbit(n,m) * 2^{nuSum(n,m)} = 3^m * n + waveSum(n,m) -/
lemma fundamental_orbit_formula (n m : ℕ) :
    orbit n m * 2^(nuSum n m) = 3^m * n + waveSum n m := by
  induction m with
  | zero =>
    simp only [orbit, nuSum, List.range_zero, List.map_nil, List.sum_nil, pow_zero, mul_one,
               pow_zero, one_mul, waveSum, add_zero]
  | succ k ih =>
    -- orbit(k+1) = T(orbit(k)) = (3·orbit(k) + 1) / 2^{ν_k}
    -- nuSum(k+1) = nuSum(k) + ν_k
    -- waveSum(k+1) = 3·waveSum(k) + 2^{nuSum(k)}
    simp only [orbit, T]
    have h_nu := nu (orbit n k)
    -- orbit(k+1) * 2^{nuSum(k+1)} = T(orbit(k)) * 2^{nuSum(k) + ν_k}
    --   = ((3·orbit(k) + 1) / 2^{ν_k}) * 2^{nuSum(k) + ν_k}
    --   = (3·orbit(k) + 1) * 2^{nuSum(k)}
    --   = 3·orbit(k)·2^{nuSum(k)} + 2^{nuSum(k)}
    -- By IH: orbit(k)·2^{nuSum(k)} = 3^k·n + waveSum(k)
    --   = 3·(3^k·n + waveSum(k)) + 2^{nuSum(k)}
    --   = 3^{k+1}·n + 3·waveSum(k) + 2^{nuSum(k)}
    --   = 3^{k+1}·n + waveSum(k+1) ✓

    -- nuSum_succ
    have h_nusum_succ : nuSum n (k + 1) = nuSum n k + nu (orbit n k) := by
      simp only [nuSum, List.range_succ, List.map_append, List.map_cons, List.map_nil,
                 List.sum_append, List.sum_cons, List.sum_nil, add_zero]

    -- The division property
    have h_div : 2^(nu (orbit n k)) ∣ 3 * orbit n k + 1 := pow_padicValNat_dvd
    have h_pos : 0 < 2^(nu (orbit n k)) := Nat.two_pow_pos _

    -- T(orbit n k) * 2^(nu (orbit n k)) = 3 * orbit n k + 1
    have h_T_expand : T (orbit n k) * 2^(nu (orbit n k)) = 3 * orbit n k + 1 := by
      unfold T
      exact Nat.div_mul_cancel h_div

    -- Main calculation
    calc orbit n (k + 1) * 2^(nuSum n (k + 1))
        = T (orbit n k) * 2^(nuSum n (k + 1)) := rfl
      _ = T (orbit n k) * 2^(nuSum n k + nu (orbit n k)) := by rw [h_nusum_succ]
      _ = T (orbit n k) * (2^(nuSum n k) * 2^(nu (orbit n k))) := by rw [pow_add]
      _ = T (orbit n k) * 2^(nu (orbit n k)) * 2^(nuSum n k) := by ring
      _ = (3 * orbit n k + 1) * 2^(nuSum n k) := by rw [h_T_expand]
      _ = 3 * orbit n k * 2^(nuSum n k) + 2^(nuSum n k) := by ring
      _ = 3 * (orbit n k * 2^(nuSum n k)) + 2^(nuSum n k) := by ring
      _ = 3 * (3^k * n + waveSum n k) + 2^(nuSum n k) := by rw [ih]
      _ = 3^(k + 1) * n + (3 * waveSum n k + 2^(nuSum n k)) := by ring
      _ = 3^(k + 1) * n + waveSum n (k + 1) := by simp only [waveSum]

/-- waveSum equals waveSumPattern of orbitPattern -/
lemma waveSum_eq_waveSumPattern (n m : ℕ) :
    waveSum n m = Collatz.waveSumPattern (orbitPattern n m) := by
  induction m with
  | zero =>
    simp only [waveSum, Collatz.waveSumPattern, orbitPattern_length,
               List.range_zero, List.map_nil, List.sum_nil]
  | succ k ih =>
    rw [waveSum]
    unfold Collatz.waveSumPattern
    simp only [orbitPattern_length]
    rw [List.range_succ, List.map_append, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    -- Last term
    have h_last : 3^((k + 1) - 1 - k) * 2^(Collatz.partialNuSum (orbitPattern n (k + 1)) k) =
                  2^(nuSum n k) := by
      have h_exp : (k + 1) - 1 - k = 0 := by omega
      rw [h_exp, pow_zero, one_mul]
      rw [partialNuSum_orbitPattern_eq_nuSum n (k + 1) k (by omega)]
    rw [h_last]
    -- Factor the earlier terms
    have h_factor : (List.range k).map (fun j => 3^((k + 1) - 1 - j) *
                     2^(Collatz.partialNuSum (orbitPattern n (k + 1)) j)) =
                   (List.range k).map (fun j => 3 * (3^(k - 1 - j) *
                     2^(Collatz.partialNuSum (orbitPattern n k) j))) := by
      apply List.map_congr_left
      intro j hj
      have hj_lt : j < k := List.mem_range.mp hj
      have h_exp : (k + 1) - 1 - j = k - j := by omega
      rw [h_exp]
      have h_exp2 : k - j = (k - 1 - j) + 1 := by omega
      rw [h_exp2, pow_succ]
      ring_nf
      have h1 : Collatz.partialNuSum (orbitPattern n (1 + k)) j = nuSum n j :=
        partialNuSum_orbitPattern_eq_nuSum n (1 + k) j (by omega)
      have h2 : Collatz.partialNuSum (orbitPattern n k) j = nuSum n j :=
        partialNuSum_orbitPattern_eq_nuSum n k j (by omega)
      rw [h1, h2]
    rw [h_factor]
    rw [List.sum_map_mul_left]
    -- Now connect to ih: waveSum n k = waveSumPattern (orbitPattern n k)
    unfold Collatz.waveSumPattern at ih
    simp only [orbitPattern_length] at ih
    omega

/-- Orbit constraint match: the orbit pattern constraint matches n in the appropriate ZMod -/
lemma orbit_constraint_match (n : ℕ) (hn : Odd n) (hpos : 0 < n) (m : ℕ) :
    let σ := orbitPattern n m
    let S := Collatz.patternSum σ
    (n : ZMod (2^S)) = Collatz.patternConstraint σ := by
  let σ := orbitPattern n m
  let S := Collatz.patternSum σ
  have hS_eq : S = nuSum n m := orbitPattern_sum n m
  have hLen_eq : σ.length = m := orbitPattern_length n m

  have h_fund := fundamental_orbit_formula n m
  have h_waveSum_bridge := waveSum_eq_waveSumPattern n m

  rw [Collatz.constraint_eq_iff_waveSum]
  conv_lhs => rw [← h_waveSum_bridge]
  conv_rhs => rw [hLen_eq]

  -- Now show: waveSum n m = -n * 3^m in ZMod(2^S)
  have h_eq : (3^m * n + waveSum n m : ℕ) = orbit n m * 2^(nuSum n m) := h_fund.symm
  have h_div : 2^S ∣ 3^m * n + waveSum n m := by
    rw [h_eq, hS_eq]
    exact dvd_mul_left _ _

  have h_zero : (3^m * n + waveSum n m : ZMod (2^S)) = 0 := by
    have := (ZMod.natCast_eq_zero_iff (3^m * n + waveSum n m) (2^S)).mpr h_div
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at this
    exact this

  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add] at h_zero ⊢
  have h_solve : (waveSum n m : ZMod (2^S)) = -(3^m * (n : ZMod (2^S))) := by
    calc (waveSum n m : ZMod (2^S))
        = (3^m * (n : ZMod (2^S)) + (waveSum n m : ZMod (2^S))) - 3^m * (n : ZMod (2^S)) := by ring
      _ = 0 - 3^m * (n : ZMod (2^S)) := by rw [h_zero]
      _ = -(3^m * (n : ZMod (2^S))) := by ring
  rw [h_solve]
  ring

end

end Collatz.OrbitPatternBridge
