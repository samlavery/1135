/-
Copyright (c) 2024. All rights reserved.
Released under MIT license.

# Roots of Unity Sum to Zero

Standard result: For q ≥ 2, ∑_{j=0}^{q-1} ζ^j = 0 where ζ = e^{2πi/q}
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic

namespace RootsOfUnity

open scoped BigOperators
open Finset Complex

noncomputable def ζ (q : ℕ) : ℂ := exp (2 * Real.pi * I / q)

/-! ## Basic Properties of ζ -/

theorem zeta_pow_q (q : ℕ) (hq : q ≥ 1) : ζ q ^ q = 1 := by
  unfold ζ
  rw [← exp_nat_mul]
  have hq_ne : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have : (q : ℂ) * (2 * ↑Real.pi * I / ↑q) = 2 * Real.pi * I := by field_simp
  rw [this]
  exact exp_two_pi_mul_I

theorem zeta_ne_one (q : ℕ) (hq : q ≥ 2) : ζ q ≠ 1 := by
  -- exp(2πi/q) = 1 iff 2πi/q = 2πik for some k ∈ ℤ, i.e., 1/q = k
  -- But 1/q is not an integer for q ≥ 2
  unfold ζ
  intro h
  rw [exp_eq_one_iff] at h
  obtain ⟨k, hk⟩ := h
  have hq_ne : (q : ℂ) ≠ 0 := by simp; omega
  have htwopi_ne : (2 : ℂ) * Real.pi * I ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  -- From hk: 2πi/q = k * 2πi, so q * k = 1
  have h1 : (q : ℂ) * k = 1 := by
    have := congrArg (· * q / (2 * Real.pi * I)) hk
    field_simp [htwopi_ne, hq_ne] at this
    exact this.symm
  -- q * k = 1 in ℂ with q ≥ 2 natural and k integer is impossible
  -- Taking real parts: q * k = 1 as reals, then as integers
  have hqk : (q : ℤ) * k = 1 := by
    have hre := congrArg Complex.re h1
    simp only [mul_re, natCast_re, natCast_im, one_re] at hre
    simp at hre
    exact_mod_cast hre
  -- q * k = 1 in ℤ with q ≥ 2 is impossible (units of ℤ are ±1)
  have hq1 : q = 1 := by
    have hdvd : (q : ℤ) ∣ 1 := ⟨k, hqk.symm⟩
    have habs := Int.natAbs_dvd_natAbs.mpr hdvd
    simp at habs
    exact habs
  omega

/-! ## Geometric Series -/

/-- Geometric series formula: (x - 1) * ∑_{j=0}^{n-1} x^j = x^n - 1 -/
theorem geom_sum_mul (x : ℂ) (n : ℕ) :
    (x - 1) * ∑ j : Fin n, x ^ j.val = x ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [mul_add, ih]
    ring

/-- Alternative: ∑_{j=0}^{n-1} x^j = (x^n - 1) / (x - 1) for x ≠ 1 -/
theorem geom_sum (x : ℂ) (n : ℕ) (hx : x ≠ 1) :
    ∑ j : Fin n, x ^ j.val = (x ^ n - 1) / (x - 1) := by
  have h := geom_sum_mul x n
  have hne : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  rw [eq_div_iff hne, mul_comm]
  exact h

/-! ## Main Theorem -/

/-- **Theorem**: Sum of q-th roots of unity is zero for q ≥ 2. -/
theorem roots_sum_zero (q : ℕ) (hq : q ≥ 2) : ∑ j : Fin q, ζ q ^ j.val = 0 := by
  have hζ_ne_1 : ζ q ≠ 1 := zeta_ne_one q hq
  have hζ_pow : ζ q ^ q = 1 := zeta_pow_q q (by omega)
  
  rw [geom_sum (ζ q) q hζ_ne_1]
  rw [hζ_pow]
  simp

/-! ## Corollary for Sums with Coefficients -/

/-- Constant coefficients give zero sum. -/
theorem const_coeff_sum_zero (q : ℕ) (hq : q ≥ 2) (c : ℂ) :
    ∑ j : Fin q, c * ζ q ^ j.val = 0 := by
  rw [← mul_sum]
  simp [roots_sum_zero q hq]

/-- Balance with uniform weights is zero. -/
theorem uniform_balance_zero (q : ℕ) (hq : q ≥ 2) (c : ℕ) :
    ∑ j : Fin q, (c : ℂ) * ζ q ^ j.val = 0 := 
  const_coeff_sum_zero q hq c

end RootsOfUnity
