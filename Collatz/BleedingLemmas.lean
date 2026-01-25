/-
  BleedingLemmas.lean - Trailing ones analysis for Collatz orbits

  Provides the interface required by ConstraintMismatch.lean:
  - trailingOnes
  - iterateSyracuse
  - max_trailing_ones_bound
  - t1_implies_sigma_run

  ALL lemmas are fully proven - no axioms.
-/

import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Ring.Parity
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

namespace Collatz.Bleeding

/-! ## Definitions -/

/-- Count trailing ones in binary representation -/
def trailingOnes : ℕ → ℕ
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 0 then 0 else 1 + trailingOnes ((n + 1) / 2)

/-- Syracuse step -/
def syracuseStep (n : ℕ) : ℕ :=
  (3 * n + 1) / 2^(padicValNat 2 (3 * n + 1))

/-- Iterate Syracuse -/
def iterateSyracuse (n₀ : ℕ) (_hn : Odd n₀) (_hpos : 0 < n₀) : ℕ → ℕ
  | 0 => n₀
  | k + 1 => syracuseStep (iterateSyracuse n₀ _hn _hpos k)

/-! ## Core Lemmas -/

/-- trailingOnes of even positive number is 0 -/
lemma trailingOnes_even {n : ℕ} (hn : n > 0) (heven : n % 2 = 0) : trailingOnes n = 0 := by
  match n with
  | 0 => omega
  | n' + 1 => simp only [trailingOnes, heven, ↓reduceIte]

/-- trailingOnes of odd number is 1 + trailingOnes (n/2) -/
lemma trailingOnes_odd {n : ℕ} (hn : n > 0) (hodd : n % 2 = 1) :
    trailingOnes n = 1 + trailingOnes (n / 2) := by
  match n with
  | 0 => omega
  | n' + 1 =>
    simp only [trailingOnes, hodd]
    rfl

/-- Trailing ones is bounded by log of n+1. -/
theorem trailingOnes_le_log (n : ℕ) (hn : n > 0) : trailingOnes n ≤ Nat.log 2 (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ =>
    rename_i n ih
    match n with
    | 0 => omega
    | 1 => native_decide
    | n' + 2 =>
      by_cases heven : (n' + 2) % 2 = 0
      · rw [trailingOnes_even (by omega) heven]; exact Nat.zero_le _
      · have hodd : (n' + 2) % 2 = 1 := by omega
        rw [trailingOnes_odd (by omega) hodd]
        have hdiv_lt : (n' + 2) / 2 < n' + 2 := Nat.div_lt_self (by omega) (by omega)
        have hdiv_pos : (n' + 2) / 2 > 0 := by omega
        have h_ih := ih _ hdiv_lt hdiv_pos
        -- Key: log 2 (n+1) = log 2 ((n+1)/2) + 1 when n+1 ≥ 2
        have hlog_div : Nat.log 2 (n' + 3) = Nat.log 2 ((n' + 3) / 2) + 1 :=
          Nat.log_of_one_lt_of_le (by omega : 1 < 2) (by omega : 2 ≤ n' + 3)
        rw [hlog_div, Nat.add_comm]
        apply Nat.add_le_add_right
        calc trailingOnes ((n' + 2) / 2)
          ≤ Nat.log 2 ((n' + 2) / 2 + 1) := h_ih
          _ ≤ Nat.log 2 ((n' + 3) / 2) := by
            apply Nat.log_mono_right
            have : (n' + 2) / 2 + 1 ≤ (n' + 3) / 2 + 1 := by omega
            have h1 : (n' + 2) / 2 ≤ (n' + 3) / 2 := by omega
            omega

/-- n has ≥2 trailing ones iff n ≡ 3 (mod 4). -/
theorem trailingOnes_ge2_iff_mod4_eq3 (n : ℕ) (hn : Odd n) :
    trailingOnes n ≥ 2 ↔ n % 4 = 3 := by
  obtain ⟨k, hk⟩ := hn
  subst hk
  have hodd : (2 * k + 1) % 2 = 1 := by omega
  rw [trailingOnes_odd (by omega) hodd]
  have hdiv : (2 * k + 1) / 2 = k := by omega
  rw [hdiv]
  have h_mod : (2 * k + 1) % 4 = 3 ↔ k % 2 = 1 := by omega
  rw [h_mod]
  match k with
  | 0 => simp [trailingOnes]
  | k' + 1 =>
    by_cases hk'_even : (k' + 1) % 2 = 0
    · rw [trailingOnes_even (by omega) hk'_even]
      constructor <;> omega
    · have hk'_odd : (k' + 1) % 2 = 1 := by omega
      rw [trailingOnes_odd (by omega) hk'_odd]
      constructor <;> omega

/-! ## Key v₂ Lemmas -/

/-- If n ≡ 3 (mod 4), then v₂(3n+1) = 1. -/
theorem v2_3n1_eq_one_of_mod4_eq3 (n : ℕ) (hn : n % 4 = 3) :
    padicValNat 2 (3 * n + 1) = 1 := by
  have h_mod4 : (3 * n + 1) % 4 = 2 := by omega
  have h_ne : 3 * n + 1 ≠ 0 := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_dvd_2 : 2 ∣ (3 * n + 1) := by omega
  have h_not_dvd_4 : ¬(4 ∣ (3 * n + 1)) := by omega
  have h_ge_1 : padicValNat 2 (3 * n + 1) ≥ 1 :=
    padicValNat_dvd_iff_le h_ne |>.mp h_dvd_2
  have h_le_1 : padicValNat 2 (3 * n + 1) ≤ 1 := by
    by_contra hle
    push_neg at hle
    have h_ge_2 : padicValNat 2 (3 * n + 1) ≥ 2 := hle
    have h_dvd_4 : 4 ∣ (3 * n + 1) := by
      have hdvd : (2 : ℕ)^2 ∣ (3 * n + 1) := padicValNat_dvd_iff_le h_ne |>.mpr h_ge_2
      norm_num at hdvd
      exact hdvd
    exact h_not_dvd_4 h_dvd_4
  omega

/-- Key lemma: If n has t ≥ 2 trailing ones, then v₂(3n+1) = 1. -/
theorem trailing_ones_gives_v2_one (n : ℕ) (hn : Odd n) (ht : trailingOnes n ≥ 2) :
    padicValNat 2 (3 * n + 1) = 1 := by
  have h_mod4 := (trailingOnes_ge2_iff_mod4_eq3 n hn).mp ht
  exact v2_3n1_eq_one_of_mod4_eq3 n h_mod4

/-! ## Syracuse Properties -/

/-- Syracuse step of odd n divides out all factors of 2, so result is odd -/
theorem syracuseStep_odd (n : ℕ) (hn : Odd n) : Odd (syracuseStep n) := by
  unfold syracuseStep
  have h3n1_pos : 3 * n + 1 > 0 := by have := Odd.pos hn; omega
  have h3n1_ne : 3 * n + 1 ≠ 0 := by omega
  set v := padicValNat 2 (3 * n + 1) with hv_def
  have h_pow_dvd : 2^v ∣ 3 * n + 1 := pow_padicValNat_dvd
  have h_pow_pos : (2 : ℕ)^v > 0 := by positivity
  have h_div_pos : (3 * n + 1) / 2^v > 0 :=
    Nat.div_pos (Nat.le_of_dvd h3n1_pos h_pow_dvd) h_pow_pos
  have h_div_ne : (3 * n + 1) / 2^v ≠ 0 := by omega
  have h_v2_zero : padicValNat 2 ((3 * n + 1) / 2^v) = 0 := by
    have h := padicValNat.div_pow h_pow_dvd
    omega
  rw [Nat.odd_iff]
  by_contra heven
  push_neg at heven
  have heven' : (3 * n + 1) / 2^v % 2 = 0 := by omega
  have h_2_dvd : 2 ∣ (3 * n + 1) / 2^v := Nat.dvd_of_mod_eq_zero heven'
  have h_v2_ge1 : padicValNat 2 ((3 * n + 1) / 2^v) ≥ 1 :=
    (padicValNat_dvd_iff_le h_div_ne).mp h_2_dvd
  omega

/-- Syracuse iterates are always odd -/
lemma iterateSyracuse_odd (n₀ : ℕ) (hn : Odd n₀) (hpos : 0 < n₀) (k : ℕ) :
    Odd (iterateSyracuse n₀ hn hpos k) := by
  induction k with
  | zero => exact hn
  | succ j ih => exact syracuseStep_odd _ ih

/-- Syracuse step of n with ≥2 trailing ones: (3n+1)/2 since v₂ = 1 -/
lemma syracuseStep_of_trailing_ge2 (n : ℕ) (hn : Odd n) (ht : trailingOnes n ≥ 2) :
    syracuseStep n = (3 * n + 1) / 2 := by
  unfold syracuseStep
  rw [trailing_ones_gives_v2_one n hn ht]
  simp

/-- Identity: trailingOnes(3m+2) = trailingOnes(m) for all m -/
lemma trailingOnes_3m2_eq (m : ℕ) : trailingOnes (3 * m + 2) = trailingOnes m := by
  induction m using Nat.strong_induction_on with
  | _ =>
    rename_i m ih
    match m with
    | 0 => native_decide
    | 1 => native_decide
    | m' + 2 =>
      by_cases hm'_even : (m' + 2) % 2 = 0
      · have h3m2_even : (3 * (m' + 2) + 2) % 2 = 0 := by omega
        rw [trailingOnes_even (by omega) h3m2_even]
        rw [trailingOnes_even (by omega) hm'_even]
      · have hm_odd : (m' + 2) % 2 = 1 := by omega
        have h3m2_odd : (3 * (m' + 2) + 2) % 2 = 1 := by omega
        rw [trailingOnes_odd (by omega) h3m2_odd]
        rw [trailingOnes_odd (by omega) hm_odd]
        set q := (m' + 2) / 2 with hq_def
        have hq_lt : q < m' + 2 := Nat.div_lt_self (by omega) (by omega)
        have h_eq1 : (3 * (m' + 2) + 2) / 2 = 3 * q + 2 := by omega
        simp only [h_eq1]
        exact congrArg (1 + ·) (ih q hq_lt)

/-- Syracuse step reduces trailing ones by 1 when t ≥ 2. -/
theorem syracuse_trailing_ones (n : ℕ) (hn : Odd n) (hpos : n > 0) (ht : trailingOnes n ≥ 2) :
    trailingOnes (syracuseStep n) = trailingOnes n - 1 := by
  rw [syracuseStep_of_trailing_ge2 n hn ht]
  obtain ⟨k, hk⟩ := hn
  subst hk
  have hodd : (2 * k + 1) % 2 = 1 := by omega
  have hdiv_k : (2 * k + 1) / 2 = k := by omega
  have h1 : trailingOnes (2 * k + 1) = 1 + trailingOnes k := by
    rw [trailingOnes_odd (by omega) hodd, hdiv_k]
  rw [h1]
  have hdiv : (3 * (2 * k + 1) + 1) / 2 = 3 * k + 2 := by omega
  rw [hdiv]
  have ht_k : trailingOnes k ≥ 1 := by omega
  have hk_pos : k > 0 := by
    by_contra h; push_neg at h; simp only [Nat.le_zero] at h; subst h
    simp only [trailingOnes, ge_iff_le, Nat.le_zero, Nat.one_ne_zero] at ht_k
  have hk_odd : k % 2 = 1 := by
    by_contra heven
    push_neg at heven
    have : k % 2 = 0 := by omega
    rw [trailingOnes_even hk_pos this] at ht_k
    omega
  -- k = 2j + 1 for some j
  have ⟨j, hj⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
  subst hj
  -- 3k + 2 = 3(2j+1) + 2 = 6j + 5
  -- trailingOnes(6j+5) should equal trailingOnes(2j+1) - 1
  have h3k2_odd : (3 * (2 * j + 1) + 2) % 2 = 1 := by omega
  have hdiv3 : (3 * (2 * j + 1) + 2) / 2 = 3 * j + 2 := by omega
  have h2j1_odd : (2 * j + 1) % 2 = 1 := by omega
  have hdiv_j : (2 * j + 1) / 2 = j := by omega
  have h2 : trailingOnes (2 * j + 1) = 1 + trailingOnes j := by
    rw [trailingOnes_odd (by omega) h2j1_odd, hdiv_j]
  rw [trailingOnes_odd (by omega) h3k2_odd, hdiv3]
  rw [h2]
  rw [trailingOnes_3m2_eq j]
  omega

/-! ## Main Theorems -/

/-- TrailingOnes decreases along Syracuse iteration -/
lemma trailingOnes_iterate (n₀ : ℕ) (hn : Odd n₀) (hpos : 0 < n₀) (L : ℕ) (hL : L ≥ 2)
    (ht1 : trailingOnes n₀ = L) (i : ℕ) (hi : i < L - 1) :
    trailingOnes (iterateSyracuse n₀ hn hpos i) = L - i := by
  induction i with
  | zero => simp only [iterateSyracuse]; exact ht1
  | succ j ih =>
    have hj_lt : j < L - 1 := Nat.lt_of_succ_lt hi
    have ihj := ih hj_lt
    simp only [iterateSyracuse]
    have h_odd_j := iterateSyracuse_odd n₀ hn hpos j
    have h_pos_j : iterateSyracuse n₀ hn hpos j > 0 := Odd.pos h_odd_j
    have htrail_j_ge : trailingOnes (iterateSyracuse n₀ hn hpos j) ≥ 2 := by
      rw [ihj]; omega
    rw [syracuse_trailing_ones _ h_odd_j h_pos_j htrail_j_ge, ihj]
    omega

/-- Trailing ones bound for cycle orbits -/
theorem max_trailing_ones_bound (n₀ : ℕ) (hn₀ : Odd n₀) (hpos₀ : 0 < n₀) (t : ℕ)
    (hOrbitAll : ∀ s, Nat.log 2 (iterateSyracuse n₀ hn₀ hpos₀ s + 1) ≤ 2 * Nat.log 2 n₀ + 8) :
    trailingOnes (iterateSyracuse n₀ hn₀ hpos₀ t) ≤ 2 * Nat.log 2 n₀ + 11 := by
  set n_t := iterateSyracuse n₀ hn₀ hpos₀ t
  by_cases hn_t : n_t = 0
  · simp only [trailingOnes, hn_t]; exact Nat.zero_le _
  · have hn_t_pos : n_t > 0 := Nat.pos_of_ne_zero hn_t
    calc trailingOnes n_t
      ≤ Nat.log 2 (n_t + 1) := trailingOnes_le_log n_t hn_t_pos
      _ ≤ 2 * Nat.log 2 n₀ + 8 := hOrbitAll t
      _ ≤ 2 * Nat.log 2 n₀ + 11 := by omega

/-- High trailing ones implies ν=1 run -/
theorem t1_implies_sigma_run (n₀ : ℕ) (hn : Odd n₀) (hpos : 0 < n₀) (L : ℕ) (hL : L ≥ 2)
    (ht1 : trailingOnes n₀ = L) :
    ∀ i < L - 1, padicValNat 2 (3 * iterateSyracuse n₀ hn hpos i + 1) = 1 := by
  intro i hi
  have ht_i : trailingOnes (iterateSyracuse n₀ hn hpos i) ≥ 2 := by
    rw [trailingOnes_iterate n₀ hn hpos L hL ht1 i hi]
    omega
  exact trailing_ones_gives_v2_one _ (iterateSyracuse_odd n₀ hn hpos i) ht_i

end Collatz.Bleeding
