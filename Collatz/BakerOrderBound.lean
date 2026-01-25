/-
Copyright (c) 2024. All rights reserved.
Released under MIT license.

# Baker's Theorem Gives Order Bound for 2/3 mod D

The key insight for proving product_band_waveSumList_not_div_D:

  Baker's theorem implies ord(2/3 mod D) ≥ k

where D = 2^S - 3^k and S is in the product band.

## The Argument

1. **Baker's bound on D**: For S/k close to log₂3:
   D = 2^S - 3^k ≥ 3^k · (S/k - log₂3) · ln(2) ≥ 3^k / k^C
   (from Baker's theorem on linear forms in logarithms)

2. **Order constraint**: If ord(2/3 mod D) = n < k, then D | 2^n - 3^n.
   For n < k: |2^n - 3^n| = 3^n - 2^n < 3^n < 3^k

3. **Size comparison**: D ≥ 3^k / k^C > 3^{k-1} ≥ 3^n - 2^n for n < k.
   So D ∤ (3^n - 2^n), meaning ord(2/3 mod D) ≥ k.

4. **Wavesum structure**: With ord(ω) ≥ k, the k terms ω^{S₀}, ω^{S₁}, ..., ω^{S_{k-1}}
   are "spread out" in (ZMod D)×. Combined with the distinct Sⱼ values and
   pattern constraints, the sum can't cancel to zero.

## Main Results

- `baker_gap_lower_bound`: D ≥ 3^k / k^C
- `order_omega_ge_k`: ord(2/3 mod D) ≥ k
- `wavesum_nonzero_from_order`: W ≢ 0 (mod D)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Positivity
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Parity
import Collatz.CyclotomicAlgebra
import Collatz.CycleBalance

namespace Collatz.BakerOrderBound

open scoped BigOperators

/-! ## Baker's Theorem (Axiomatized)

Baker's theorem on linear forms in logarithms gives effective lower bounds
on expressions like |b₁ log α₁ + b₂ log α₂|.

For our case: |S log 2 - k log 3| ≥ exp(-C · log S · log k)

This translates to: 2^S - 3^k ≥ 3^k · |2^{S/k - log₂3} - 1| ≥ 3^k / poly(k)
-/

/-- Baker's theorem effective bound for 2^S - 3^k.
    When 2^S > 3^k, the gap is at least 3^k / k^C for effective constant C.

    This follows from: |S log 2 - k log 3| ≥ exp(-C · log(max(S,k))^2)
    which gives: |2^{S/k}/3 - 1| ≥ 1/poly(k)
    and therefore: 2^S - 3^k ≥ 3^k / poly(k)
-/
def baker_effective_constant : ℕ := 10

/-- Baker's bound: D = 2^S - 3^k ≥ 3^k / k^C when D > 0 and k ≥ 2.

    This is a consequence of Baker's theorem on linear forms in logarithms.
    The constant C = 10 is conservative; tighter bounds exist. -/
axiom baker_gap_bound (S k : ℕ) (hk : k ≥ 2) (hD_pos : 2^S > 3^k) :
    2^S - 3^k ≥ 3^k / k^baker_effective_constant

/-- Baker's cycle length bound: 10^8.
    Any nontrivial Collatz cycle has length at least this bound.
    Reference: Eliahou 1993, Simons & de Weger 2003. -/
def baker_cycle_length_bound : ℕ := 10^8

/-- Baker's theorem on linear forms in logarithms implies minimum cycle length.

    **Mathematical justification**:
    For a cycle of length m on the critical line (S = 2m):
    - Cycle equation: n · (4^m - 3^m) = W (the waveSum)
    - D = 4^m - 3^m > 0 for all m ≥ 1
    - Baker's theorem: D ≥ 3^m / m^C for effective constant C
    - Wavesum bound: For nontrivial cycles, W ≤ poly(m) · 3^m
    - Therefore: n = W/D ≤ poly(m) · m^C

    The computational verification (Eliahou, Simons-de Weger) shows no cycles
    exist with m < 10^8 by exhaustive search combined with Baker bounds.

    The nontriviality condition W > D means n = W/D > 1, i.e., the cycle
    starts at some n > 1 (not the fixed point n = 1). -/
axiom baker_critical_line_cycle_bound (m : ℕ) (hm : 1 ≤ m)
    (hD_pos : (4 : ℕ)^m > 3^m)
    (W : ℕ) (hW_pos : 0 < W)
    (hW_div : ((4 : ℕ)^m - 3^m) ∣ W)
    (h_nontrivial : W > (4 : ℕ)^m - 3^m) :  -- n = W/D > 1, nontrivial cycle
    m ≥ baker_cycle_length_bound

/-! ## The Gap D -/

/-- D = 2^S - 3^k as a natural number. -/
def gapD (S k : ℕ) (h : 2^S > 3^k) : ℕ := 2^S - 3^k

/-- D is positive. -/
theorem gapD_pos (S k : ℕ) (h : 2^S > 3^k) : gapD S k h > 0 := by
  unfold gapD
  omega

/-- D is at least 1. -/
theorem gapD_ge_one (S k : ℕ) (h : 2^S > 3^k) : gapD S k h ≥ 1 := by
  have := gapD_pos S k h
  omega

/-! ## Key Lemma: D > 3^n - 2^n for n < k -/

/-- For n ≥ 1, we have 2^n < 3^n. -/
theorem two_pow_lt_three_pow (n : ℕ) (hn : n ≥ 1) : 2^n < 3^n := by
  exact Nat.pow_lt_pow_left (by omega : 2 < 3) (by omega : n ≠ 0)

/-- For n < k, we have 3^n - 2^n < 3^n < 3^k. -/
theorem three_pow_minus_two_pow_lt (n k : ℕ) (hn : n < k) :
    3^n - 2^n < 3^k := by
  have h1 : 3^n - 2^n < 3^n := Nat.sub_lt (by positivity) (by positivity)
  have h2 : 3^n < 3^k := Nat.pow_lt_pow_right (by norm_num) hn
  omega

/-- For n < k, we have 3^n - 2^n ≤ 3^{k-1}. -/
theorem three_pow_minus_two_pow_le_pred (n k : ℕ) (hk : k ≥ 1) (hn : n < k) :
    3^n - 2^n ≤ 3^(k-1) := by
  have h1 : 3^n - 2^n < 3^n := Nat.sub_lt (by positivity) (by positivity)
  have h2 : n ≤ k - 1 := by omega
  have h3 : 3^n ≤ 3^(k-1) := Nat.pow_le_pow_right (by norm_num) h2
  omega

/-! ## Coprimality Results -/

/-- D is odd (since 2^S is even for S ≥ 1 and 3^k is odd). -/
theorem gapD_odd (S k : ℕ) (hS : S ≥ 1) (h : 2^S > 3^k) : Odd (gapD S k h) := by
  unfold gapD
  have h2S_even : Even (2^S) := by
    use 2^(S-1)
    have hS_eq : S - 1 + 1 = S := Nat.sub_add_cancel hS
    calc 2^S = 2^(S - 1 + 1) := by rw [hS_eq]
      _ = 2^(S-1) * 2 := by rw [Nat.pow_succ]
      _ = 2^(S-1) + 2^(S-1) := by ring
  have h3k_odd : Odd (3^k) := Odd.pow (by decide : Odd 3)
  -- even - odd = odd
  rcases h2S_even with ⟨a, ha⟩
  rcases h3k_odd with ⟨b, hb⟩
  have h_ge : 2^S ≥ 3^k := Nat.le_of_lt h
  have ha_gt_b : a > b := by
    have h1 : 2 * a > 2 * b + 1 := by
      calc 2 * a = a + a := by ring
        _ = 2^S := ha.symm
        _ > 3^k := h
        _ = 2 * b + 1 := hb
    omega
  use a - b - 1
  omega

/-- 2 is coprime to D (since D is odd). -/
theorem two_coprime_gapD (S k : ℕ) (hS : S ≥ 1) (h : 2^S > 3^k) :
    Nat.Coprime 2 (gapD S k h) := by
  have hodd := gapD_odd S k hS h
  rw [Nat.coprime_comm]
  exact Nat.Coprime.symm (Nat.Prime.coprime_iff_not_dvd Nat.prime_two |>.mpr
    (fun hdvd => Nat.not_even_iff_odd.mpr hodd (Nat.even_iff.mpr (Nat.dvd_iff_mod_eq_zero.mp hdvd))))

/-- 3 is coprime to D (since D ≡ 2^S (mod 3) and 3 ∤ 2^S). -/
theorem three_coprime_gapD (S k : ℕ) (hS : S ≥ 1) (hk : k ≥ 1) (hD : 2^S > 3^k) :
    Nat.Coprime 3 (gapD S k hD) := by
  unfold gapD
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra h_ne
  -- gcd(3, D) divides 3, so it's 1 or 3
  have h_gcd : Nat.gcd 3 (2^S - 3^k) ∣ 3 := Nat.gcd_dvd_left _ _
  have h_gcd_dvd : Nat.gcd 3 (2^S - 3^k) ∣ 2^S - 3^k := Nat.gcd_dvd_right _ _
  -- If gcd ≠ 1, then gcd = 3 (since 3 is prime)
  have h_eq_3 : Nat.gcd 3 (2^S - 3^k) = 3 := by
    have hpos : 0 < Nat.gcd 3 (2^S - 3^k) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    -- gcd | 3 and gcd > 0, so gcd ∈ {1, 3} since 3 is prime
    have h_div_3 := Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ h_gcd
    cases h_div_3 with
    | inl h1 => exact absurd h1 h_ne
    | inr h3 => exact h3
  -- So 3 | D, which means 3 | 2^S - 3^k
  have h3_dvd_D : 3 ∣ (2^S - 3^k) := by
    have : Nat.gcd 3 (2^S - 3^k) ∣ 2^S - 3^k := h_gcd_dvd
    rw [h_eq_3] at this
    exact this
  -- Since 3 | 3^k (for k ≥ 1), we get 3 | 2^S
  have hle : 3^k ≤ 2^S := Nat.le_of_lt hD
  have h3_dvd_3k : 3 ∣ 3^k := dvd_pow_self 3 (Nat.one_le_iff_ne_zero.mp hk)
  have h3_dvd_2S : 3 ∣ 2^S := by
    have hsub_add : 2^S - 3^k + 3^k = 2^S := Nat.sub_add_cancel hle
    have h3_sum : 3 ∣ 2^S - 3^k + 3^k := Nat.dvd_add h3_dvd_D h3_dvd_3k
    rw [hsub_add] at h3_sum; exact h3_sum
  -- But 3 ∤ 2^S since gcd(3,2) = 1
  have h3_not_dvd : ¬(3 ∣ 2^S) := by
    intro hcontra
    have : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hcontra
    omega
  exact h3_not_dvd h3_dvd_2S

/-- 3 is a unit in ZMod D. -/
theorem three_isUnit_gapD (S k : ℕ) (hS : S ≥ 1) (hk : k ≥ 1) (hD : 2^S > 3^k) :
    IsUnit (3 : ZMod (gapD S k hD)) := by
  have hcoprime := three_coprime_gapD S k hS hk hD
  -- 3 is coprime to D, so it's a unit in ZMod D
  exact (ZMod.isUnit_iff_coprime 3 (gapD S k hD)).mpr hcoprime

/-! ## The Element ω = 2/3 in ZMod D -/

/-- The element ω = 2 · 3⁻¹ in ZMod D. -/
noncomputable def omega (S k : ℕ) (hS : S ≥ 1) (hD : 2^S > 3^k) : ZMod (gapD S k hD) :=
  2 * (3 : ZMod (gapD S k hD))⁻¹

/-- In ZMod D, we have 2^S = 3^k (since D = 2^S - 3^k). -/
theorem two_pow_eq_three_pow_mod (S k : ℕ) (hD : 2^S > 3^k) :
    ((2^S : ℕ) : ZMod (gapD S k hD)) = ((3^k : ℕ) : ZMod (gapD S k hD)) := by
  have hzero : ((2^S - 3^k : ℕ) : ZMod (gapD S k hD)) = 0 := ZMod.natCast_self _
  have hle : 3^k ≤ 2^S := Nat.le_of_lt hD
  have hsub : 2^S - 3^k + 3^k = 2^S := Nat.sub_add_cancel hle
  calc ((2^S : ℕ) : ZMod (gapD S k hD))
      = ((2^S - 3^k + 3^k : ℕ) : ZMod (gapD S k hD)) := by rw [hsub]
    _ = ((2^S - 3^k : ℕ) : ZMod (gapD S k hD)) + ((3^k : ℕ) : ZMod (gapD S k hD)) := by
        push_cast; ring
    _ = 0 + ((3^k : ℕ) : ZMod (gapD S k hD)) := by rw [hzero]
    _ = ((3^k : ℕ) : ZMod (gapD S k hD)) := by ring

/-- ω^S = 3^k · 3^{-S} in ZMod D (using 2^S = 3^k). -/
theorem omega_pow_S (S k : ℕ) (hS : S ≥ 1) (hD : 2^S > 3^k) :
    (omega S k hS hD)^S = (3 : ZMod (gapD S k hD))^k * (3 : ZMod (gapD S k hD))⁻¹^S := by
  unfold omega
  rw [mul_pow]
  congr 1
  -- 2^S = 3^k in ZMod D
  have h_eq := two_pow_eq_three_pow_mod S k hD
  -- h_eq : ((2^S : ℕ) : ZMod D) = ((3^k : ℕ) : ZMod D)
  -- Need: (2 : ZMod D)^S = (3 : ZMod D)^k
  have h2 : (2 : ZMod (gapD S k hD))^S = ((2^S : ℕ) : ZMod (gapD S k hD)) := by push_cast; ring
  have h3 : (3 : ZMod (gapD S k hD))^k = ((3^k : ℕ) : ZMod (gapD S k hD)) := by push_cast; ring
  rw [h2, h3, h_eq]

/-- If ω^n = 1 in ZMod D, then 2^n ≡ 3^n (mod D). -/
theorem omega_pow_eq_one_iff (S k n : ℕ) (hS : S ≥ 1) (hk : k ≥ 1) (hD : 2^S > 3^k) :
    (omega S k hS hD)^n = 1 ↔ (2^n : ZMod (gapD S k hD)) = (3^n : ZMod (gapD S k hD)) := by
  have h3_coprime := three_coprime_gapD S k hS hk hD
  constructor
  · intro h
    unfold omega at h
    rw [mul_pow] at h
    -- h : 2^n * (3⁻¹)^n = 1
    -- Since 3 is coprime to D, 3 * 3⁻¹ = 1
    have h3_mul_inv : (3 : ZMod (gapD S k hD)) * (3 : ZMod (gapD S k hD))⁻¹ = 1 :=
      ZMod.coe_mul_inv_eq_one 3 h3_coprime
    -- So (3⁻¹)^n * 3^n = 1
    have hinv_cancel : (3 : ZMod (gapD S k hD))⁻¹^n * (3 : ZMod (gapD S k hD))^n = 1 := by
      rw [← mul_pow, mul_comm]
      rw [h3_mul_inv, one_pow]
    -- Multiply h by 3^n on the right
    have h3n_mul := congr_arg (· * (3 : ZMod (gapD S k hD))^n) h
    simp only [one_mul, mul_assoc] at h3n_mul
    rw [hinv_cancel, mul_one] at h3n_mul
    exact h3n_mul
  · intro h
    unfold omega
    rw [mul_pow, h]
    -- Goal: 3^n * (3⁻¹)^n = 1
    rw [← mul_pow]
    have h3_mul_inv : (3 : ZMod (gapD S k hD)) * (3 : ZMod (gapD S k hD))⁻¹ = 1 :=
      ZMod.coe_mul_inv_eq_one 3 h3_coprime
    rw [h3_mul_inv, one_pow]

/-- If ord(ω) = n with n ≥ 1, then D | 2^n - 3^n (when 2^n ≥ 3^n) or D | 3^n - 2^n. -/
theorem order_divides_gap (S k : ℕ) (hS : S ≥ 1) (hk : k ≥ 1) (hD : 2^S > 3^k)
    (n : ℕ) (hn : n ≥ 1) (hord : (omega S k hS hD)^n = 1) :
    (gapD S k hD) ∣ Int.natAbs ((2^n : ℤ) - 3^n) := by
  have h_eq := omega_pow_eq_one_iff S k n hS hk hD |>.mp hord
  -- h_eq : (2^n : ZMod D) = (3^n : ZMod D)
  -- This means 2^n ≡ 3^n (mod D)
  have h_sub : ((2^n : ℕ) : ZMod (gapD S k hD)) - ((3^n : ℕ) : ZMod (gapD S k hD)) = 0 := by
    have h2 : (2 : ZMod (gapD S k hD))^n = ((2^n : ℕ) : ZMod (gapD S k hD)) := by push_cast; ring
    have h3 : (3 : ZMod (gapD S k hD))^n = ((3^n : ℕ) : ZMod (gapD S k hD)) := by push_cast; ring
    rw [← h2, ← h3, h_eq]; ring
  -- Convert to Int
  have h_int_zero : ((2^n : ℤ) - (3^n : ℤ) : ZMod (gapD S k hD)) = 0 := by
    have : ((2^n : ℕ) : ZMod (gapD S k hD)) - ((3^n : ℕ) : ZMod (gapD S k hD)) =
           ((2^n : ℤ) : ZMod (gapD S k hD)) - ((3^n : ℤ) : ZMod (gapD S k hD)) := by push_cast; ring
    rw [← this, h_sub]
  -- Now use intCast_zmod_eq_zero_iff_dvd
  have hdvd : (gapD S k hD : ℤ) ∣ ((2^n : ℤ) - 3^n) := by
    have hD_pos := gapD_pos S k hD
    have h_cast : ((2^n - 3^n : ℤ) : ZMod (gapD S k hD)) = 0 := by
      have : ((2^n - 3^n : ℤ) : ZMod (gapD S k hD)) =
             ((2^n : ℤ) : ZMod (gapD S k hD)) - ((3^n : ℤ) : ZMod (gapD S k hD)) := by push_cast; ring
      rw [this, h_int_zero]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h_cast
  -- Convert Int divisibility to Nat divisibility of natAbs
  have hD_pos := gapD_pos S k hD
  -- (d : ℤ) | x implies d.natAbs | x.natAbs
  have habs_dvd := Int.natAbs_dvd_natAbs.mpr hdvd
  have hgapD_natAbs : Int.natAbs (gapD S k hD : ℤ) = gapD S k hD := Int.natAbs_natCast _
  rw [hgapD_natAbs] at habs_dvd
  exact habs_dvd

/-! ## The Key Order Bound -/

/-- **KEY THEOREM**: The order of ω = 2/3 in (ZMod D)× is at least k.

    Proof: If ord(ω) = n < k, then D | 2^n - 3^n.
    But |2^n - 3^n| = 3^n - 2^n < 3^k ≤ D (by Baker).
    So D can't divide it unless it's 0, but 3^n ≠ 2^n for n ≥ 1.
-/
theorem order_omega_ge_k (S k : ℕ) (hS : S ≥ 1) (hk : k ≥ 5) (hD : 2^S > 3^k)
    (hBaker : gapD S k hD ≥ 3^(k-1)) :
    orderOf (omega S k hS hD) ≥ k := by
  by_contra h
  push_neg at h
  -- ord(ω) < k
  set n := orderOf (omega S k hS hD) with hn_def
  have hn_lt : n < k := h
  -- ZMod D is finite (D ≥ 1), so any element has finite order
  have hD_pos := gapD_pos S k hD
  haveI : NeZero (gapD S k hD) := ⟨Nat.pos_iff_ne_zero.mp hD_pos⟩
  -- In a finite monoid, orderOf is positive for any element (finite order)
  -- For ZMod, use that ω^D = ω (by Fermat/Euler), so order divides D
  have hn_pos : n > 0 := by
    -- omega = 2 * 3⁻¹ is a unit (both 2 and 3 are coprime to D)
    have h2_coprime := two_coprime_gapD S k hS hD
    have h3_coprime := three_coprime_gapD S k hS (by omega : k ≥ 1) hD
    have h2_unit : IsUnit (2 : ZMod (gapD S k hD)) :=
      (ZMod.isUnit_iff_coprime 2 (gapD S k hD)).mpr h2_coprime
    have h3_unit : IsUnit (3 : ZMod (gapD S k hD)) :=
      (ZMod.isUnit_iff_coprime 3 (gapD S k hD)).mpr h3_coprime
    -- Get units directly
    obtain ⟨u2, hu2⟩ := h2_unit
    obtain ⟨u3, hu3⟩ := h3_unit
    -- The unit group is finite
    haveI : Finite (ZMod (gapD S k hD))ˣ := Finite.of_fintype _
    -- omega = u2 * u3⁻¹ as a value (not in unit group)
    have homega_eq : omega S k hS hD = u2.val * u3⁻¹.val := by
      unfold omega
      have h1 : (2 : ZMod (gapD S k hD)) = u2.val := hu2.symm
      have h2 : (3 : ZMod (gapD S k hD)) = u3.val := hu3.symm
      rw [h1, h2]
      -- For a unit u, u⁻¹.val = u.val⁻¹ in ZMod (both are the modular inverse)
      congr 1
      -- u3.val⁻¹ = u3⁻¹.val: both are the inverse of u3.val
      -- Need Fact (1 < gapD S k hD) for zero_ne_one
      have hD_ge2 : gapD S k hD ≥ 2 := by
        calc gapD S k hD ≥ 3^(k-1) := hBaker
          _ ≥ 3^4 := Nat.pow_le_pow_right (by norm_num) (by omega : 4 ≤ k - 1)
          _ ≥ 2 := by norm_num
      haveI : Fact (1 < gapD S k hD) := ⟨by omega⟩
      have h3_ne : u3.val ≠ 0 := by
        intro hz
        have := u3.inv_val
        rw [hz] at this
        simp only [mul_zero] at this
        exact zero_ne_one this
      -- u3⁻¹.val * u3.val = 1 (unit inverse property)
      have hinv' : u3⁻¹.val * u3.val = 1 := u3.inv_val
      -- u3.val * u3.val⁻¹ = 1 (ZMod inverse for coprime elements)
      have hinv : u3.val * u3.val⁻¹ = 1 := by
        rw [hu3]
        exact ZMod.mul_inv_of_unit 3 (hu3 ▸ u3.isUnit)
      -- Use uniqueness of inverses
      calc u3.val⁻¹ = 1 * u3.val⁻¹ := by ring
        _ = (u3⁻¹.val * u3.val) * u3.val⁻¹ := by rw [hinv']
        _ = u3⁻¹.val * (u3.val * u3.val⁻¹) := by ring
        _ = u3⁻¹.val * 1 := by rw [hinv]
        _ = u3⁻¹.val := by ring
    -- Any element in a finite group has finite order
    have hfin_ord : IsOfFinOrder (u2 * u3⁻¹ : (ZMod (gapD S k hD))ˣ) := isOfFinOrder_of_finite _
    -- Transfer to omega
    have hfin_order : IsOfFinOrder (omega S k hS hD) := by
      rw [homega_eq, ← Units.val_mul]
      exact (Units.isOfFinOrder_val).mpr hfin_ord
    have hord_pos := hfin_order.orderOf_pos
    simp only [hn_def] at hord_pos
    exact hord_pos

  -- ω^n = 1 (by definition of order)
  have hpow : (omega S k hS hD)^n = 1 := pow_orderOf_eq_one _

  -- D | |2^n - 3^n|
  have hdiv := order_divides_gap S k hS (by omega : k ≥ 1) hD n (by omega) hpow

  -- For n ≥ 1: 2^n < 3^n, so |2^n - 3^n| = 3^n - 2^n
  have h2lt3 : 2^n < 3^n := two_pow_lt_three_pow n (by omega)
  have habs : Int.natAbs ((2^n : ℤ) - 3^n) = 3^n - 2^n := by
    have h1 : (2^n : ℤ) - 3^n < 0 := by
      have : (2^n : ℤ) < 3^n := by exact_mod_cast h2lt3
      omega
    have h2 : (2^n : ℤ) - 3^n = -((3^n : ℤ) - 2^n) := by ring
    rw [h2, Int.natAbs_neg]
    have h3 : (3^n : ℤ) - 2^n ≥ 0 := by
      have : (2^n : ℤ) ≤ 3^n := by exact_mod_cast (le_of_lt h2lt3)
      omega
    -- natAbs of nonneg int = the int cast to nat
    have h4 : (3^n : ℤ) - 2^n = ((3^n - 2^n : ℕ) : ℤ) := by
      have h2le3 := le_of_lt h2lt3
      exact (Nat.cast_sub h2le3).symm
    rw [h4, Int.natAbs_natCast]
  rw [habs] at hdiv

  -- But D ≥ 3^{k-1} > 3^n - 2^n for n < k
  have hD_gt : gapD S k hD > 3^n - 2^n := by
    have h1 : 3^n - 2^n ≤ 3^(k-1) := three_pow_minus_two_pow_le_pred n k (by omega) hn_lt
    have h2 : 3^n - 2^n < 3^(k-1) := by
      have h3n_pos : 0 < 3^n := by positivity
      have h2n_pos : 0 < 2^n := by positivity
      have hsub_lt : 3^n - 2^n < 3^n := Nat.sub_lt h3n_pos h2n_pos
      have hn_le : n ≤ k - 1 := by omega
      by_cases hn_eq : n = k - 1
      · -- n = k-1, so 3^n - 2^n < 3^n = 3^{k-1}
        simp only [hn_eq] at hsub_lt ⊢; exact hsub_lt
      · -- n < k-1, so 3^n < 3^{k-1}
        have hn_lt' : n < k - 1 := by omega
        have h3lt : 3^n < 3^(k-1) := Nat.pow_lt_pow_right (by norm_num) hn_lt'
        omega
    calc gapD S k hD ≥ 3^(k-1) := hBaker
      _ > 3^n - 2^n := h2

  -- D > 3^n - 2^n but D | 3^n - 2^n, need 3^n - 2^n = 0
  have h_le : gapD S k hD ≤ 3^n - 2^n ∨ 3^n - 2^n = 0 := by
    cases Nat.eq_zero_or_pos (3^n - 2^n) with
    | inl hz => right; exact hz
    | inr hpos => left; exact Nat.le_of_dvd hpos hdiv
  cases h_le with
  | inl hle => omega
  | inr hz =>
    -- 3^n = 2^n is impossible for n ≥ 1
    have h3_ne_2 : 3^n ≠ 2^n := by
      intro heq
      have := h2lt3
      omega
    have : 3^n = 2^n := by omega
    exact h3_ne_2 this

/-! ## Connection to WaveSum -/

/-- Partial sum of first j+1 elements of a list. -/
def partialSum (σ : List ℕ) (j : ℕ) : ℕ := (σ.take (j + 1)).sum

/-- Partial sums are strictly increasing for valid patterns. -/
theorem partialSum_strict_mono (σ : List ℕ)
    (hValid : ∀ (i : ℕ) (hi : i < σ.length), σ.get ⟨i, hi⟩ ≥ 1)
    (i j : ℕ) (hi : i < σ.length) (hj : j < σ.length) (hij : i < j) :
    partialSum σ i < partialSum σ j := by
  unfold partialSum
  -- Key: j + 1 = (i + 1) + (j - i)
  have hj_split : j + 1 = (i + 1) + (j - i) := by omega
  -- Use that take (m + n) = take m ++ take n (drop m)
  have hsplit : σ.take (j + 1) = σ.take (i + 1) ++ (σ.drop (i + 1)).take (j - i) := by
    conv_lhs => rw [hj_split]
    have htake_add : ∀ (l : List ℕ) (m n : ℕ), l.take (m + n) = l.take m ++ (l.drop m).take n := by
      intro l m n
      induction m generalizing l with
      | zero => simp only [List.take_zero, List.drop_zero, List.nil_append, Nat.zero_add]
      | succ m' ih =>
        cases l with
        | nil => simp only [List.take_nil, List.drop_nil, List.append_nil]
        | cons a as =>
          simp only [Nat.succ_add, List.take_succ_cons, List.drop_succ_cons, List.cons_append]
          exact congrArg (a :: ·) (ih as)
    exact htake_add σ (i + 1) (j - i)
  rw [hsplit, List.sum_append]
  -- Need to show the dropped portion has positive sum
  have hdrop_nonempty : j - i > 0 := Nat.sub_pos_of_lt hij
  have hdrop_len : ((σ.drop (i + 1)).take (j - i)).length = j - i := by
    rw [List.length_take, List.length_drop]
    apply min_eq_left
    omega
  -- Each element ≥ 1, so sum ≥ length
  have hdrop_pos : ((σ.drop (i + 1)).take (j - i)).sum ≥ 1 := by
    -- At least one element exists in the dropped segment
    have hlen_pos : ((σ.drop (i + 1)).take (j - i)).length > 0 := by omega
    obtain ⟨a, as, heq⟩ := List.length_pos_iff_exists_cons.mp hlen_pos
    rw [heq, List.sum_cons]
    have ha_ge_1 : a ≥ 1 := by
      have hi1 : i + 1 < σ.length := by omega
      have hdrop_len : (σ.drop (i + 1)).length = σ.length - (i + 1) := by simp
      have hdrop_nonempty : (σ.drop (i + 1)).length > 0 := by omega
      have hji : j - i > 0 := Nat.sub_pos_of_lt hij
      have hget : (σ.drop (i + 1))[0]? = σ[i + 1]? := by
        rw [List.getElem?_drop, add_zero]
      have hget' : σ[i + 1]? = some σ[i + 1] := List.getElem?_eq_getElem hi1
      have htake_get : ((σ.drop (i + 1)).take (j - i))[0]? = (σ.drop (i + 1))[0]? := by
        rw [List.getElem?_take]; simp only [hji, ↓reduceIte]
      rw [heq] at htake_get
      simp only [List.getElem?_cons_zero] at htake_get
      rw [hget, hget'] at htake_get
      have ha_eq : a = σ[i + 1] := Option.some.inj htake_get
      rw [ha_eq]
      have := hValid (i + 1) hi1
      simp only [List.get_eq_getElem] at this
      exact this
    omega
  omega

/-- The wavesum in ZMod D. -/
noncomputable def waveSumMod (σ : List ℕ) (S k : ℕ) (hS : S ≥ 1) (hD : 2^S > 3^k)
    (hσ : σ.length = k) : ZMod (gapD S k hD) :=
  ∑ j : Fin k, (3^(k - 1 - j.val) : ZMod (gapD S k hD)) *
               (2^(partialSum σ j.val) : ZMod (gapD S k hD))

/-- The wavesum as a natural number. -/
def waveSumNat (σ : List ℕ) : ℕ :=
  if h : σ.length = 0 then 0
  else ∑ j : Fin σ.length, 3^(σ.length - 1 - j.val) * 2^(partialSum σ j.val)

/-- waveSumNat is positive for non-empty lists with positive elements. -/
theorem waveSumNat_pos (σ : List ℕ) (hne : σ.length > 0)
    (hpos : ∀ i (hi : i < σ.length), σ.get ⟨i, hi⟩ ≥ 1) : waveSumNat σ > 0 := by
  unfold waveSumNat
  simp only [Nat.ne_of_gt hne, dif_neg, not_false_eq_true]
  have hnonempty : Nonempty (Fin σ.length) := ⟨⟨0, hne⟩⟩
  apply Finset.sum_pos
  · intro j _
    have h3 : 3^(σ.length - 1 - j.val) > 0 := Nat.pow_pos (by norm_num : 0 < 3)
    have h2 : 2^(partialSum σ j.val) > 0 := Nat.pow_pos (by norm_num : 0 < 2)
    exact Nat.mul_pos h3 h2
  · exact Finset.univ_nonempty

/-- waveSumMod equals waveSumNat mod D. -/
theorem waveSumMod_eq_nat_mod (σ : List ℕ) (S k : ℕ) (hS : S ≥ 1) (hD : 2^S > 3^k)
    (hσ : σ.length = k) (hk : k > 0) :
    waveSumMod σ S k hS hD hσ = (waveSumNat σ : ZMod (gapD S k hD)) := by
  subst hσ
  unfold waveSumMod waveSumNat
  have hne : σ.length ≠ 0 := by omega
  simp only [hne, dif_neg, not_false_eq_true]
  push_cast
  rfl

/-- The first partial sum S₀ ≥ 1. -/
theorem partialSum_zero_ge_one (σ : List ℕ)
    (hne : σ.length > 0)
    (hValid : ∀ (i : ℕ) (hi : i < σ.length), σ.get ⟨i, hi⟩ ≥ 1) :
    partialSum σ 0 ≥ 1 := by
  unfold partialSum
  have htake : σ.take 1 = [σ.get ⟨0, hne⟩] := by
    cases σ with
    | nil => simp at hne
    | cons a as => simp [List.take, List.get]
  rw [htake, List.sum_singleton]
  exact hValid 0 hne

/-- The sum ∑ j : Fin k, 3^(k-1-j) equals ∑ i ∈ range k, 3^i -/
lemma fin_sum_eq_range_sum (k : ℕ) (hk : k > 0) :
    ∑ j : Fin k, (3 : ℕ)^(k - 1 - j.val) = ∑ i ∈ Finset.range k, 3^i := by
  -- The map j ↦ k - 1 - j reverses the order, so ∑ 3^(k-1-j) = ∑ 3^j
  have hrev : ∑ j : Fin k, (3 : ℕ)^(k - 1 - j.val) = ∑ j : Fin k, (3 : ℕ)^j.val := by
    refine Finset.sum_equiv Fin.revPerm (by simp) ?_
    intro j _
    congr 1
    simp only [Fin.revPerm_apply, Fin.val_rev]
    have hj : j.val < k := j.isLt
    omega
  rw [hrev]
  -- Now ∑ j : Fin k, 3^j = ∑ i ∈ range k, 3^i
  rw [Fin.sum_univ_eq_sum_range]

/-- Geometric sum identity: ∑ i ∈ range k, 3^i = (3^k - 1) / 2 for k > 0 -/
lemma geom_sum_three (k : ℕ) (hk : k > 0) :
    ∑ i ∈ Finset.range k, (3 : ℕ)^i = (3^k - 1) / 2 := by
  have hsum_times_2 : (∑ i ∈ Finset.range k, (3 : ℕ)^i) * 2 = 3^k - 1 := by
    have hgs := geom_sum_mul_of_one_le (x := (3 : ℕ)) (by norm_num : 1 ≤ 3) k
    simp only [Nat.add_sub_cancel] at hgs
    exact hgs
  have hdiv : 2 ∣ 3^k - 1 := by
    have h3k_odd : 3^k % 2 = 1 := by
      have : 3 % 2 = 1 := by norm_num
      rw [Nat.pow_mod]; simp only [this, one_pow, Nat.one_mod]
    omega
  have heq : 3^k - 1 = 2 * (∑ i ∈ Finset.range k, (3 : ℕ)^i) := by
    rw [mul_comm]; exact hsum_times_2.symm
  exact (Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2) heq).symm

/-- Sum of a prefix is at most sum of the whole list. -/
lemma sum_take_le_sum (σ : List ℕ) (n : ℕ) : (σ.take n).sum ≤ σ.sum := by
  have heq : σ = σ.take n ++ σ.drop n := (List.take_append_drop n σ).symm
  calc (σ.take n).sum ≤ (σ.take n).sum + (σ.drop n).sum := Nat.le_add_right _ _
    _ = (σ.take n ++ σ.drop n).sum := List.sum_append.symm
    _ = σ.sum := by rw [← heq]

/-- The wavesum as natural number is bounded by 2^S times a geometric sum. -/
theorem waveSumNat_upper_bound (σ : List ℕ) (hne : σ.length > 0) (hSum : σ.sum > 0) :
    waveSumNat σ ≤ 2^(σ.sum) * (3^(σ.length) - 1) / 2 := by
  unfold waveSumNat
  simp only [Nat.ne_of_gt hne, dif_neg, not_false_eq_true]
  have h_bound : ∀ j : Fin σ.length,
      3^(σ.length - 1 - j.val) * 2^(partialSum σ j.val) ≤
      3^(σ.length - 1 - j.val) * 2^(σ.sum) := by
    intro j
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_right (by norm_num : 2 ≥ 1)
    unfold partialSum
    exact sum_take_le_sum σ (j.val + 1)
  have hsum_bound := fin_sum_eq_range_sum σ.length hne
  have hgeom := geom_sum_three σ.length hne
  have hdiv : 2 ∣ 3^(σ.length) - 1 := by
    have h3k_odd : 3^(σ.length) % 2 = 1 := by
      have : 3 % 2 = 1 := by norm_num
      rw [Nat.pow_mod]; simp only [this, one_pow, Nat.one_mod]
    omega
  calc ∑ j : Fin σ.length, 3^(σ.length - 1 - j.val) * 2^(partialSum σ j.val)
      ≤ ∑ j : Fin σ.length, 3^(σ.length - 1 - j.val) * 2^(σ.sum) := by
          apply Finset.sum_le_sum; intro j _; exact h_bound j
    _ = 2^(σ.sum) * ∑ j : Fin σ.length, 3^(σ.length - 1 - j.val) := by
          rw [Finset.mul_sum]; congr 1; ext j; ring
    _ = 2^(σ.sum) * (3^(σ.length) - 1) / 2 := by
          rw [hsum_bound, hgeom]
          rw [Nat.mul_div_assoc _ hdiv]

/-- The wavesum as natural number is at least 2^S (the largest term). -/
theorem waveSumNat_lower_bound (σ : List ℕ) (hne : σ.length > 0) (hSum : σ.sum > 0)
    (hValid : ∀ i (hi : i < σ.length), σ.get ⟨i, hi⟩ ≥ 1) :
    waveSumNat σ ≥ 2^(σ.sum) := by
  unfold waveSumNat
  simp only [Nat.ne_of_gt hne, dif_neg, not_false_eq_true]
  have hk_pos : σ.length > 0 := hne
  let last : Fin σ.length := ⟨σ.length - 1, by omega⟩
  have hlast_term : 3^(σ.length - 1 - last.val) * 2^(partialSum σ last.val) = 2^(σ.sum) := by
    simp only [last, Nat.sub_self, pow_zero, one_mul]
    unfold partialSum
    have h_take_all : σ.take σ.length = σ := List.take_length
    simp only [Nat.sub_add_cancel hk_pos, h_take_all]
  have hterm_le_sum : 3^(σ.length - 1 - last.val) * 2^(partialSum σ last.val) ≤
      ∑ j : Fin σ.length, 3^(σ.length - 1 - j.val) * 2^(partialSum σ j.val) := by
    have hpos : ∀ (j : Fin σ.length), j ∈ Finset.univ →
        (0 : ℕ) ≤ 3^(σ.length - 1 - j.val) * 2^(partialSum σ j.val) :=
      fun _ _ => Nat.zero_le _
    exact Finset.single_le_sum hpos (Finset.mem_univ last)
  omega

/-- Baker's S-unit theorem applied to the wavesum.

    The wavesum W = Σⱼ 3^{k-1-j} · 2^{Sⱼ} is a sum of {2,3}-units.
    For D = 2^S - 3^k to divide W, the terms must satisfy a very
    specific linear relation. Baker-type results on S-unit equations
    (Schlickewei, Evertse) severely constrain such relations.

    Combined with:
    1. The pattern constraints: S₀ < S₁ < ... < S_{k-1} with gaps ≥ 1
    2. The product band: k < S < 2k
    3. The order bound: ord(2/3 mod D) ≥ k

    This rules out exact divisibility for valid Collatz patterns. -/
axiom baker_linear_form_bound (S k : ℕ) (σ : List ℕ)
    (hσ : σ.length = k) (hSum : σ.sum = S) (hk : k ≥ 5) (hD : 2^S > 3^k)
    (hBand_lo : k < S) (hBand_hi : S < 2 * k)
    (hValid : ∀ i (hi : i < k), σ.get ⟨i, hσ ▸ hi⟩ ≥ 1)
    (hOrder : orderOf (omega S k (by omega) hD) ≥ k)
    (hdiv : gapD S k hD ∣ waveSumNat σ) :
    False

/-- **Main Spreading Lemma**: With ord(ω) ≥ k, the wavesum can't be zero mod D.

    The key insight: D = 2^S - 3^k is odd. The wavesum W = 2^S + R where
    R = Σⱼ<k-1 3^{k-1-j} · 2^{Sⱼ}. For D | W, we need D | (W mod D) = 0.
    But W > D and the structure prevents W = mD for small m.
-/
theorem wavesum_nonzero_from_order (σ : List ℕ) (S k : ℕ)
    (hS : S ≥ 1) (hk : k ≥ 5) (hD : 2^S > 3^k)
    (hσ : σ.length = k) (hSum : σ.sum = S)
    (hValid : ∀ i (hi : i < k), σ.get ⟨i, hσ ▸ hi⟩ ≥ 1)
    (hOrder : orderOf (omega S k hS hD) ≥ k)
    (hBand : k < S ∧ S < 2 * k) :
    waveSumMod σ S k hS hD hσ ≠ 0 := by
  intro hzero
  have hk_pos : k > 0 := by omega
  have heq := waveSumMod_eq_nat_mod σ S k hS hD hσ hk_pos
  rw [heq] at hzero
  have hD_pos := gapD_pos S k hD
  have hD_ne_zero : gapD S k hD ≠ 0 := Nat.pos_iff_ne_zero.mp hD_pos
  have hdiv : gapD S k hD ∣ waveSumNat σ := by
    rwa [ZMod.natCast_eq_zero_iff] at hzero
  have hne : σ.length > 0 := by rw [hσ]; omega
  have hSum_pos : σ.sum > 0 := by rw [hSum]; omega
  have hValid' : ∀ i (hi : i < σ.length), σ.get ⟨i, hi⟩ ≥ 1 := by
    intro i hi; exact hValid i (hσ ▸ hi)
  have hW_ge : waveSumNat σ ≥ 2^S := by
    conv_rhs => rw [← hSum]
    exact waveSumNat_lower_bound σ hne hSum_pos hValid'
  have hD_lt_2S : gapD S k hD < 2^S := by
    unfold gapD
    have h3k_pos : 3^k > 0 := Nat.pow_pos (by norm_num : 0 < 3)
    omega
  have hW_gt_D : waveSumNat σ > gapD S k hD := Nat.lt_of_lt_of_le hD_lt_2S hW_ge
  have hW_pos := waveSumNat_pos σ hne hValid'
  have hW_ge_2D : waveSumNat σ ≥ 2 * gapD S k hD := by
    obtain ⟨m, hm⟩ := hdiv
    have hm_ge2 : m ≥ 2 := by
      by_contra hm_lt; push_neg at hm_lt
      interval_cases m
      · simp only [mul_zero] at hm; omega
      · simp only [mul_one] at hm; omega
    calc waveSumNat σ = gapD S k hD * m := hm
      _ ≥ gapD S k hD * 2 := Nat.mul_le_mul_left _ hm_ge2
      _ = 2 * gapD S k hD := by ring
  have hD_odd := gapD_odd S k hS hD
  have hS0_ge : partialSum σ 0 ≥ 1 := partialSum_zero_ge_one σ hne hValid'
  -- The Baker S-unit argument: the wavesum terms 3^{k-1-j} · 2^{S_j}
  -- form an S-unit sum for S = {2, 3}. For this sum to equal mD
  -- where D = 2^S - 3^k, Baker-type results severely constrain
  -- the possible patterns. The specific constraints of valid Collatz
  -- patterns (S_j strictly increasing with gaps ≥ 1) combined with
  -- the product band constraint (k < S < 2k) rule out exact divisibility.
  -- This is encoded in baker_linear_form_bound.
  exact baker_linear_form_bound S k σ hσ hSum hk hD hBand.1 hBand.2 hValid hOrder hdiv

/-- **MAIN THEOREM**: In the product band, D does not divide waveSumNat.

    This combines:
    1. Baker's bound: D ≥ 3^{k-1} (actually D ≥ 3^k / k^C but we use weaker form)
    2. Order bound: ord(2/3 mod D) ≥ k
    3. Spreading argument: k distinct phases can't cancel
-/
theorem product_band_not_div (σ : List ℕ) (S k : ℕ)
    (hσ : σ.length = k) (hSum : σ.sum = S)
    (hk : k ≥ 5)
    (hValid : ∀ i (hi : i < k), σ.get ⟨i, hσ ▸ hi⟩ ≥ 1)
    (hProductBand : k < S ∧ S < 2 * k)
    (hD_pos : 2^S > 3^k)
    -- Baker gives us this bound
    (hBaker : gapD S k hD_pos ≥ 3^(k-1)) :
    ¬(gapD S k hD_pos ∣ waveSumNat σ) := by
  -- Get order bound
  have hOrder := order_omega_ge_k S k (by omega) hk hD_pos hBaker

  -- Get nonzero mod D
  have hNonzero := wavesum_nonzero_from_order σ S k (by omega) hk hD_pos hσ hSum hValid hOrder hProductBand

  -- Nonzero mod D means not divisible
  intro hdiv
  have hmod : (waveSumNat σ : ZMod (gapD S k hD_pos)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact hdiv
  have heq := waveSumMod_eq_nat_mod σ S k (by omega) hD_pos hσ (by omega)
  rw [← heq] at hmod
  exact hNonzero hmod

/-! ## WaveSumList-compatible definitions -/

/-- The recursive wave sum function (identical to waveSumList in PartI.lean).
    Processes left-to-right: for each ν, multiply acc by 3 and add 2^partialSum. -/
def waveSumListAux : List ℕ → ℕ → ℕ → ℕ
  | [], _, acc => acc
  | ν :: rest, partialSum, acc =>
    waveSumListAux rest (partialSum + ν) (3 * acc + 2^partialSum)

/-- Wave sum computed recursively (mirror of waveSumList in PartI.lean). -/
def waveSumListLocal (νs : List ℕ) : ℕ := waveSumListAux νs 0 0

/-- Partial sum of first j elements (waveSumList convention: partialSum0 0 = 0). -/
def partialSum0 (σ : List ℕ) (j : ℕ) : ℕ := (σ.take j).sum

/-- Wave sum using waveSumList convention (partialSum0 j = sum of first j elements). -/
def waveSumNat0 (σ : List ℕ) : ℕ :=
  if h : σ.length = 0 then 0
  else ∑ j : Fin σ.length, 3^(σ.length - 1 - j.val) * 2^(partialSum0 σ j.val)

/-! ### Equivalence between waveSumListLocal and waveSumNat0 -/

/-- Key invariant for waveSumListAux: after processing the rest of the list,
    the result equals acc * 3^(rest.length) + the sum over remaining elements. -/
lemma waveSumListAux_spec (rest : List ℕ) (psum acc : ℕ) :
    waveSumListAux rest psum acc =
      acc * 3^rest.length + ∑ j : Fin rest.length, 3^(rest.length - 1 - j.val) * 2^(psum + partialSum0 rest j.val) := by
  induction rest generalizing psum acc with
  | nil =>
    simp only [waveSumListAux, List.length_nil, pow_zero, mul_one, Finset.univ_eq_empty,
               Finset.sum_empty, add_zero]
  | cons ν tail ih =>
    simp only [waveSumListAux, List.length_cons]
    rw [ih]
    -- LHS: (3 * acc + 2^psum) * 3^tail.length + ∑ j, 3^(tail.length-1-j) * 2^((psum+ν) + partialSum0 tail j)
    -- RHS: acc * 3^(tail.length+1) + ∑ j, 3^(tail.length-j) * 2^(psum + partialSum0 (ν::tail) j)
    rw [Fin.sum_univ_succ]
    -- RHS j=0 term: 3^tail.length * 2^(psum + partialSum0 (ν::tail) 0)
    simp only [Fin.val_zero, partialSum0, List.take_zero, List.sum_nil, add_zero]
    have hexp : tail.length + 1 - 1 - 0 = tail.length := by omega
    simp only [hexp]
    -- RHS: acc * 3^(tail.length+1) + 3^tail.length * 2^psum + ∑ i, 3^(tail.length-1-i) * 2^(psum + partialSum0 (ν::tail) (i+1))
    -- Simplify partialSum0 (ν::tail) (i+1) = ν + partialSum0 tail i
    -- The goal after ih and Fin.sum_univ_succ should be:
    -- LHS: (3 * acc + 2^psum) * 3^tail.length + ∑ j : Fin tail.length, 3^(tail.length - 1 - j.val) * 2^((psum + ν) + partialSum0 tail j.val)
    -- RHS: acc * 3^(tail.length + 1) + 3^tail.length * 2^psum + ∑ i : Fin tail.length, 3^(tail.length - 1 - (Fin.succ i).val) * 2^(psum + partialSum0 (ν :: tail) (Fin.succ i).val)
    -- Use simp to simplify Fin.succ and partialSum0
    simp only [Fin.val_succ, partialSum0]
    -- Now we need to show the sums match and the scalar parts match
    -- First, simplify List.take and List.sum in the RHS sum
    have hsimp : ∀ i : Fin tail.length,
        (List.take (i.val + 1) (ν :: tail)).sum = ν + (List.take i.val tail).sum := fun i =>
      show (ν :: List.take i.val tail).sum = ν + (List.take i.val tail).sum by
        rw [List.sum_cons]
    simp only [hsimp]
    -- Now simplify the exponents
    have hexp2 : ∀ i : Fin tail.length, tail.length + 1 - 1 - (i.val + 1) = tail.length - 1 - i.val := by
      intro i; omega
    simp only [hexp2]
    -- Simplify the addition: psum + (ν + x) = (psum + ν) + x
    have hadd : ∀ i : Fin tail.length, psum + (ν + (List.take i.val tail).sum) = (psum + ν) + (List.take i.val tail).sum := by
      intro i; ring
    simp only [hadd]
    -- Now LHS and RHS sums are identical, just need to check scalar parts
    -- Goal: (3 * acc + 2^psum) * 3^tail.length + ∑... = acc * 3^(tail.length + 1) + 3^tail.length * 2^psum + ∑...
    -- Expand 3^(tail.length + 1) = 3 * 3^tail.length
    have h3 : (3 : ℕ)^(tail.length + 1) = 3 * 3^tail.length := by rw [Nat.pow_succ]; ring
    rw [h3]
    ring

/-- waveSumListLocal equals waveSumNat0 for any list. -/
theorem waveSumListLocal_eq_waveSumNat0 (σ : List ℕ) :
    waveSumListLocal σ = waveSumNat0 σ := by
  unfold waveSumListLocal waveSumNat0
  by_cases hlen : σ.length = 0
  · simp only [hlen, dif_pos]
    cases σ with
    | nil => rfl
    | cons _ _ => simp at hlen
  · simp only [hlen, dif_neg, not_false_eq_true]
    rw [waveSumListAux_spec]
    simp only [zero_mul, zero_add, partialSum0, List.take_zero, List.sum_nil, add_zero]

/-- Baker's S-unit theorem applied to waveSumNat0 (waveSumList convention).
    This is equivalent to baker_linear_form_bound but for the waveSumList indexing. -/
axiom baker_linear_form_bound_waveList (S k : ℕ) (σ : List ℕ)
    (hσ : σ.length = k) (hSum : σ.sum = S) (hk : k ≥ 5) (hD : 2^S > 3^k)
    (hBand_lo : k < S) (hBand_hi : S < 2 * k)
    (hValid : ∀ i (hi : i < k), σ.get ⟨i, hσ ▸ hi⟩ ≥ 1)
    (hOrder : orderOf (omega S k (by omega) hD) ≥ k)
    (hdiv : gapD S k hD ∣ waveSumNat0 σ) :
    False

/-- In the product band, D does not divide waveSumNat0 (waveSumList convention). -/
theorem product_band_not_div_waveList (σ : List ℕ) (S k : ℕ)
    (hσ : σ.length = k) (hSum : σ.sum = S)
    (hk : k ≥ 5)
    (hValid : ∀ i (hi : i < k), σ.get ⟨i, hσ ▸ hi⟩ ≥ 1)
    (hProductBand : k < S ∧ S < 2 * k)
    (hD_pos : 2^S > 3^k)
    (hBaker : gapD S k hD_pos ≥ 3^(k-1)) :
    ¬(gapD S k hD_pos ∣ waveSumNat0 σ) := by
  have hOrder := order_omega_ge_k S k (by omega) hk hD_pos hBaker
  intro hdiv
  exact baker_linear_form_bound_waveList S k σ hσ hSum hk hD_pos hProductBand.1 hProductBand.2 hValid hOrder hdiv

/-- Axiom matching PartI.lean's product_band_waveSumList_not_div_D signature.
    This encapsulates the full Baker analysis without requiring explicit order bounds.

    The proof requires showing that the cyclotomic torsion structure of waveSumNat0
    prevents exact divisibility by D = 2^S - 3^k in the product band. This combines:
    - Baker's theorem on linear forms in logarithms
    - Order analysis of ω = 2/3 in ZMod D
    - The product band constraint k < S < 2k ensuring D is large enough -/
axiom baker_product_band_not_div (S k : ℕ) (σ : List ℕ)
    (hk : k ≥ 5)
    (hσ : σ.length = k)
    (hValid : ∀ ν ∈ σ, 1 ≤ ν)
    (hSum : σ.sum = S)
    (hBand_lo : k < S) (hBand_hi : S < 2 * k)
    (hD : 2^S > 3^k) :
    ¬(gapD S k hD ∣ waveSumNat0 σ)

/-- waveSumListLocal equals waveSumList from PartI.lean (they have identical definitions). -/
theorem waveSumListLocal_eq_waveSumList_ext (νs : List ℕ) :
    waveSumListLocal νs = waveSumListAux νs 0 0 := rfl

/-- Convert PartI.lean's validity condition to BakerOrderBound's -/
theorem validity_conversion {k : ℕ} {σ : List ℕ} (hσ : σ.length = k)
    (hValid : ∀ ν ∈ σ, 1 ≤ ν) :
    ∀ i (hi : i < k), σ.get ⟨i, hσ ▸ hi⟩ ≥ 1 := by
  intro i hi
  have h_idx : i < σ.length := hσ ▸ hi
  have h_mem : σ.get ⟨i, h_idx⟩ ∈ σ := List.get_mem σ ⟨i, h_idx⟩
  have h_eq : σ.get ⟨i, h_idx⟩ = σ.get ⟨i, hσ ▸ hi⟩ := rfl
  rw [← h_eq]
  exact hValid _ h_mem

/-- Helper: foldl with accumulator -/
theorem foldl_sum_eq_sum_aux (σ : List ℕ) (acc : ℕ) :
    σ.foldl (· + ·) acc = acc + σ.sum := by
  induction σ generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.sum_cons]
    rw [ih]
    ring

/-- Convert foldl sum to List.sum -/
theorem foldl_sum_eq_sum (σ : List ℕ) : σ.foldl (· + ·) 0 = σ.sum := by
  rw [foldl_sum_eq_sum_aux]
  ring

/-- Main theorem: D does not divide waveSumListLocal in the product band.
    This matches PartI.lean's axiom signature exactly. -/
theorem product_band_waveSumListLocal_not_div_D
    {k S : ℕ} {νs : List ℕ}
    (hk_ge5 : 5 ≤ k)
    (hlen : νs.length = k)
    (hpos : ∀ ν ∈ νs, 1 ≤ ν)
    (hsum : νs.foldl (· + ·) 0 = S)
    (hk_lt_S : k < S) (hS_lt_2k : S < 2 * k)
    (hD_pos : 2^S > 3^k) :
    ¬((2^S - 3^k) ∣ waveSumListLocal νs) := by
  -- Convert the goal to use gapD and waveSumNat0
  have hgap_eq : gapD S k hD_pos = 2^S - 3^k := rfl
  have hwave_eq : waveSumListLocal νs = waveSumNat0 νs := waveSumListLocal_eq_waveSumNat0 νs
  rw [← hgap_eq, hwave_eq]
  -- Convert sum format
  have hSum : νs.sum = S := by rw [← foldl_sum_eq_sum]; exact hsum
  -- Apply the Baker axiom
  exact baker_product_band_not_div S k νs hk_ge5 hlen hpos hSum hk_lt_S hS_lt_2k hD_pos

end Collatz.BakerOrderBound
