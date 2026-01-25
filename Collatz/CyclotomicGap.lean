/-
Copyright (c) 2024. All rights reserved.
Released under MIT license.

# Cyclotomic Gap Condition for Collatz Conjecture

This file proves the gap condition using cyclotomic field theory.
Based on Aristotle output (uuid: 97e99a31-bb8c-43cc-af5a-4a4cfa46a758).

## Main Results

- `dft_parseval`: Parseval's identity for the DFT
- `dft_non_dc_energy`: Non-DC energy equals q times variance
- `dft_am_gm_bound`: AM-GM bound on product of DFT components
- `norm_balance_upper_bound`: Upper bound on |Norm(balance)| via variance
- `gap_condition_from_variance`: Gap fires when variance < 6

## Mathematical Context

For prime q ≥ 5, if the folded weights FW : Fin q → ℕ have variance V,
then:
  |Algebra.norm ℚ (balance)| ≤ (q · V / (q-1))^{(q-1)/2}

where balance = Σ FW_r · ζ_q^r in the cyclotomic field Q(ζ_q).

When V < 6, this is less than Φ_q(4,3) = 4^q - 3^q, establishing the gap.

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.Sqrt

namespace Collatz.CyclotomicGap

open scoped BigOperators
open Finset Complex Polynomial

/-! ## Part 1: Cyclotomic Field Setup -/

variable (q : ℕ) [hq_fact : Fact (Nat.Prime q)]

/-- Primitive q-th root of unity -/
noncomputable def ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)

/-- ζ is a primitive q-th root of unity -/
lemma zeta_isPrimitiveRoot : IsPrimitiveRoot (ζ q) q := by
  have hq_pos : 0 < q := Nat.Prime.pos hq_fact.out
  have hq_ne : q ≠ 0 := by omega
  exact Complex.isPrimitiveRoot_exp q hq_ne

/-- Sum of q-th roots of unity is 0 for q ≥ 2 -/
lemma roots_sum_zero (hq_ge2 : q ≥ 2) : ∑ j : Fin q, (ζ q) ^ j.val = 0 := by
  have hζ := zeta_isPrimitiveRoot q
  rw [Fin.sum_univ_eq_sum_range]
  exact hζ.geom_sum_eq_zero hq_ge2

/-! ## Part 2: Balance Sum Definition -/

/-- The balance sum: weighted sum over roots of unity -/
noncomputable def balanceSum (FW : Fin q → ℕ) : ℂ :=
  ∑ r : Fin q, (FW r : ℂ) * (ζ q) ^ r.val

/-- Mean of folded weights -/
noncomputable def foldedMean (FW : Fin q → ℕ) : ℝ :=
  (∑ r : Fin q, (FW r : ℝ)) / q

/-- Variance of folded weights -/
noncomputable def foldedVariance (FW : Fin q → ℕ) : ℝ :=
  let μ := foldedMean q FW
  ∑ r : Fin q, ((FW r : ℝ) - μ) ^ 2

/-- Variance is nonnegative (sum of squares). -/
lemma foldedVariance_nonneg (FW : Fin q → ℕ) : 0 ≤ foldedVariance q FW := by
  unfold foldedVariance
  apply Finset.sum_nonneg
  intro r _
  apply sq_nonneg

/-! ## Bridge: ℚ variance → ℝ variance

The CyclotomicAlgebra module defines foldedVariance over ℚ.
We show that if the ℚ version is < 6, then the ℝ version is also < 6. -/

/-- The ℚ-valued foldedMean equals the ℝ-valued one under coercion. -/
lemma foldedMean_rat_eq_real (FW : Fin q → ℕ) :
    ((∑ r : Fin q, (FW r : ℚ)) / q : ℝ) = foldedMean q FW := by
  unfold foldedMean
  simp only [Rat.cast_sum, Rat.cast_natCast, Rat.cast_div, Rat.cast_natCast]

/-- The ℚ-valued foldedVariance equals the ℝ-valued one under coercion.
    This bridges CyclotomicAlgebra.foldedVariance to CyclotomicGap.foldedVariance. -/
lemma foldedVariance_rat_eq_real (FW : Fin q → ℕ) :
    (((∑ r : Fin q, ((FW r : ℚ) - (∑ s : Fin q, (FW s : ℚ)) / q) ^ 2) : ℚ) : ℝ) =
    foldedVariance q FW := by
  unfold foldedVariance foldedMean
  simp only [Rat.cast_sum, Rat.cast_pow, Rat.cast_sub, Rat.cast_natCast, Rat.cast_div]

/-- If variance (computed over ℚ) is less than 6, then the ℝ version is also < 6. -/
lemma variance_lt_of_rat_lt (FW : Fin q → ℕ)
    (hV : (∑ r : Fin q, ((FW r : ℚ) - (∑ s : Fin q, (FW s : ℚ)) / q) ^ 2) < 6) :
    foldedVariance q FW < 6 := by
  have h := foldedVariance_rat_eq_real q FW
  rw [← h]
  exact_mod_cast hV

/-! ## Part 3: Norm Bounds -/

/-- The bivariate cyclotomic polynomial Φ_q(4,3) = 4^q - 3^q for prime q -/
def cyclotomicBivar43 : ℤ := (4 : ℤ)^q - 3^q

/-- Φ_q(4,3) > 0 for all q ≥ 1 -/
lemma cyclotomicBivar43_pos : cyclotomicBivar43 q > 0 := by
  unfold cyclotomicBivar43
  have hq_pos : 0 < q := Nat.Prime.pos hq_fact.out
  have h : (4 : ℕ)^q > 3^q := Nat.pow_lt_pow_left (by norm_num : 3 < 4) (by omega)
  have h' : (4 : ℤ)^q > 3^q := by exact_mod_cast h
  linarith

/-- For q ≥ 5: Φ_q(4,3) ≥ 4^{q-1} -/
lemma cyclotomicBivar43_lower_bound (hq_ge5 : q ≥ 5) :
    cyclotomicBivar43 q ≥ 4^(q-1) := by
  unfold cyclotomicBivar43
  -- 4^q - 3^q ≥ 4^{q-1} ⟺ 4^q - 4^{q-1} ≥ 3^q ⟺ 3·4^{q-1} ≥ 3^q ⟺ 4^{q-1} ≥ 3^{q-1}
  have hq_pos : q ≥ 1 := by omega
  have h1 : (4 : ℤ)^q = 4 * 4^(q-1) := by
    have heq : q = (q - 1) + 1 := by omega
    calc (4 : ℤ)^q = 4^((q-1) + 1) := by rw [Nat.sub_add_cancel hq_pos]
      _ = 4^(q-1) * 4 := by rw [pow_succ]
      _ = 4 * 4^(q-1) := by ring
  have h2 : (4 : ℤ)^q - 4^(q-1) = 3 * 4^(q-1) := by linarith
  have h3 : (4 : ℕ)^(q-1) ≥ 3^(q-1) := Nat.pow_le_pow_left (by norm_num) (q-1)
  have h4 : (3 : ℤ) * 4^(q-1) ≥ 3 * 3^(q-1) := by
    have : (4 : ℤ)^(q-1) ≥ 3^(q-1) := by exact_mod_cast h3
    linarith
  have h5 : (3 : ℤ) * 3^(q-1) = 3^q := by
    calc (3 : ℤ) * 3^(q-1) = 3^(q-1) * 3 := by ring
      _ = 3^((q-1) + 1) := by rw [pow_succ]
      _ = 3^q := by rw [Nat.sub_add_cancel hq_pos]
  linarith

/-! ## Part 4: DFT Components and Parseval -/

/-- The k-th DFT component of the weights -/
noncomputable def dft_component (FW : Fin q → ℕ) (k : Fin q) : ℂ :=
  Finset.sum Finset.univ (fun r : Fin q => (FW r : ℂ) * (ζ q) ^ (k.val * r.val))

/-- The 0-th DFT component is the sum of weights -/
lemma dft_zero_eq_sum (FW : Fin q → ℕ) :
    dft_component q FW 0 = Finset.sum Finset.univ (fun r : Fin q => (FW r : ℂ)) := by
  convert Finset.sum_congr rfl fun i _ => ?_
  simp [dft_component]

/-- The 1-st DFT component is the balance sum -/
lemma dft_one_eq_balance (FW : Fin q → ℕ) :
    dft_component q FW 1 = balanceSum q FW := by
  apply Finset.sum_congr rfl
  intro r _
  simp [dft_component, balanceSum]
  rcases q with (_ | _ | q) <;> simp

/-- Parseval's identity for the DFT -/
lemma dft_parseval (FW : Fin q → ℕ) :
    ∑ k : Fin q, Complex.normSq (dft_component q FW k) = q * ∑ r : Fin q, ((FW r : ℝ) ^ 2) := by
  -- Expand the LHS using the definition of the DFT
  have lhs_expansion : ∑ k : Fin q, Complex.normSq (∑ r : Fin q, (FW r : ℂ) * (ζ q) ^ (k.val * r.val)) =
      ∑ k : Fin q, ∑ r : Fin q, ∑ s : Fin q, (FW r : ℂ) * (FW s : ℂ) * (ζ q) ^ (k.val * (r.val - s.val : ℤ)) := by
    simp +decide [Complex.normSq_eq_norm_sq, Complex.norm_exp]
    have h_norm_sq : ∀ k : Fin q, ‖∑ r : Fin q, (FW r : ℂ) * (ζ q) ^ (k.val * r.val)‖ ^ 2 =
        ∑ r : Fin q, ∑ s : Fin q, (FW r : ℂ) * (FW s : ℂ) * (ζ q) ^ (k.val * (r.val - s.val : ℤ)) := by
      have h_norm_sq : ∀ k : Fin q, ‖∑ r : Fin q, (FW r : ℂ) * (ζ q) ^ (k.val * r.val)‖ ^ 2 =
          (∑ r : Fin q, (FW r : ℂ) * (ζ q) ^ (k.val * r.val)) *
          (∑ s : Fin q, (FW s : ℂ) * (ζ q) ^ (-k.val * s.val : ℤ)) := by
        intro k
        have h_norm_sq : ‖∑ r : Fin q, (FW r : ℂ) * (ζ q) ^ (k.val * r.val)‖ ^ 2 =
            (∑ r : Fin q, (FW r : ℂ) * (ζ q) ^ (k.val * r.val)) *
            starRingEnd ℂ (∑ r : Fin q, (FW r : ℂ) * (ζ q) ^ (k.val * r.val)) := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
        convert h_norm_sq using 2
        simp +decide [Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def]
        norm_num [Complex.normSq_eq_norm_sq, Complex.norm_exp, Complex.exp_re, Complex.exp_im, zpow_mul]
        norm_num [pow_mul, Complex.exp_re, Complex.exp_im, Complex.normSq_eq_norm_sq, Complex.norm_exp, zeta_isPrimitiveRoot]
        norm_num [ζ, Complex.exp_re, Complex.exp_im, Complex.normSq_eq_norm_sq, Complex.norm_exp]
        norm_num [← Complex.exp_nat_mul, ← Complex.exp_conj, Complex.exp_re, Complex.exp_im]
        norm_num [neg_div, mul_neg]
      simp_all +decide [mul_assoc, mul_sub, zpow_sub₀, zpow_mul, mul_comm, Finset.mul_sum _ _ _, Finset.sum_mul]
      intro k
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      norm_num [zpow_sub₀, show ζ q ≠ 0 from Complex.exp_ne_zero _, mul_assoc, mul_left_comm, mul_comm]
      ring
      norm_cast
      norm_num
    simp_all +decide [← mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, ← zpow_mul]
  -- The inner sum Σ_{k=0}^{q-1} ζ^{k(r-s)} is q if r=s and 0 if r ≠ s
  have inner_sum : ∀ r s : Fin q, ∑ k : Fin q, (ζ q) ^ (k.val * (r.val - s.val : ℤ)) = if r = s then q else 0 := by
    intro r s
    split_ifs <;> simp_all +decide [zeta_isPrimitiveRoot]
    -- Since r ≠ s, we have ζ^{r-s} ≠ 1, and thus the sum is geometric with sum zero
    have h_geo_series : ∑ k ∈ Finset.range q, (ζ q) ^ (k * (r.val - s.val : ℤ)) = 0 := by
      have h_geo_series : ∑ k ∈ Finset.range q, (ζ q ^ (r.val - s.val : ℤ)) ^ k = 0 := by
        rw [geom_sum_eq] <;> norm_num
        · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
          rw [show ζ q ^ q = 1 from by
            rw [show ζ q = Complex.exp (2 * Real.pi * Complex.I / q) from rfl]
            rw [← Complex.exp_nat_mul, mul_comm]
            norm_num [show q ≠ 0 from Nat.Prime.ne_zero Fact.out]]
          norm_num
        · have h_ne_one : ¬(ζ q) ^ (r.val - s.val : ℤ) = 1 := by
            have h_order : ∀ k : ℤ, (ζ q) ^ k = 1 → q ∣ Int.natAbs k := by
              intros k hk
              have := zeta_isPrimitiveRoot q
              simp_all +decide [IsPrimitiveRoot.iff_def]
              rcases k with (_ | k) <;> simp_all +decide [← Complex.exp_int_mul, mul_div_cancel₀]
            intro h
            specialize h_order (r - s) h
            simp_all +decide [← Int.natCast_dvd_natCast, Fin.ext_iff]
            exact ‹¬(r : ℕ) = s› (by
              obtain ⟨k, hk⟩ := h_order
              nlinarith [show k = 0 by nlinarith [Fin.is_lt r, Fin.is_lt s]])
          convert h_ne_one using 1
      exact Eq.trans (Finset.sum_congr rfl fun _ _ => by group) h_geo_series
    simpa only [Finset.sum_range] using h_geo_series
  convert lhs_expansion using 1
  unfold dft_component
  norm_cast
  simp +decide [← mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, inner_sum]
  simp +decide [← Finset.mul_sum _ _ _, ← Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, Int.subNatNat_eq_coe]
  norm_num [← Finset.mul_sum _ _ _, ← Finset.sum_mul, ← Finset.sum_comm, inner_sum]
  ring
  simp +decide [mul_comm, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, sq]
  norm_num [← Complex.ofReal_inj, Complex.ofReal_sum]

/-- The sum of squared norms of non-DC DFT components equals q times the variance -/
lemma dft_non_dc_energy (FW : Fin q → ℕ) :
    ∑ k ∈ Finset.univ.erase 0, Complex.normSq (dft_component q FW k) = q * foldedVariance q FW := by
  have h_simp : ∑ k ∈ Finset.univ.erase 0, Complex.normSq (dft_component q FW k) =
      q * (∑ r : Fin q, (FW r : ℝ) ^ 2) - Complex.normSq (dft_component q FW 0) := by
    convert congr_arg (fun x : ℝ => x - Complex.normSq (dft_component q FW 0)) (dft_parseval q FW) using 1
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  convert h_simp using 1
  unfold dft_component foldedVariance
  norm_num [Complex.normSq, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _]
  ring
  norm_num [Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, foldedMean]
  ring
  simp +decide [← Finset.mul_sum _ _ _, ← Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, sq,
    ne_of_gt (Nat.Prime.pos Fact.out)]
  ring

/-- AM-GM bound: product of squared norms bounded by variance term raised to q-1 -/
lemma dft_am_gm_bound (FW : Fin q → ℕ) :
    ∏ k ∈ Finset.univ.erase 0, Complex.normSq (dft_component q FW k) ≤
    ((q * foldedVariance q FW) / (q - 1)) ^ (q - 1) := by
  have h_am_gm : (∏ k ∈ Finset.univ.erase 0, Complex.normSq (dft_component q FW k)) ≤
      ((∑ k ∈ Finset.univ.erase 0, Complex.normSq (dft_component q FW k)) / (q - 1)) ^ (q - 1) := by
    have := @Real.geom_mean_le_arith_mean
    specialize this (Finset.univ.erase 0) (fun _i => 1) (fun _i => Complex.normSq (dft_component q FW _i))
    rcases q with (_ | _ | q) <;> simp_all +decide
    exact le_trans (by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Finset.prod_nonneg fun _ _ => Complex.normSq_nonneg _),
        Nat.cast_add_one, inv_mul_cancel₀ (by linarith), Real.rpow_one])
      (pow_le_pow_left₀ (Real.rpow_nonneg (Finset.prod_nonneg fun _ _ => Complex.normSq_nonneg _) _)
        (this (by linarith) fun _ _ => Complex.normSq_nonneg _) _)
  convert h_am_gm using 3
  rw [dft_non_dc_energy]

/-! ## Part 5: Balance Polynomial -/

/-- Balance as an element of the cyclotomic field -/
noncomputable def balance_alg (FW : Fin q → ℕ) : CyclotomicField q ℚ :=
  ∑ r : Fin q, (FW r : ℚ) * (IsCyclotomicExtension.zeta q ℚ (CyclotomicField q ℚ)) ^ r.val

/-- The balance polynomial Σ FW_r X^r -/
noncomputable def balance_poly (FW : Fin q → ℕ) : Polynomial ℚ :=
  ∑ r : Fin q, Polynomial.C (FW r : ℚ) * Polynomial.X ^ r.val

/-- balance_alg is the evaluation of balance_poly at ζ -/
lemma balance_alg_eq_aeval (FW : Fin q → ℕ) :
    balance_alg q FW = Polynomial.aeval (IsCyclotomicExtension.zeta q ℚ (CyclotomicField q ℚ)) (balance_poly q FW) := by
  unfold balance_alg balance_poly
  simp +decide [Polynomial.aeval_def]

/-- dft_component k is the evaluation of balance_poly at ζ^k -/
lemma dft_eq_eval (FW : Fin q → ℕ) (k : Fin q) :
    dft_component q FW k = (Polynomial.map (algebraMap ℚ ℂ) (balance_poly q FW)).eval ((ζ q) ^ k.val) := by
  unfold dft_component balance_poly
  simp +decide [Polynomial.eval_finset_sum]
  ring
  ac_rfl

/-- A power of ζ is a primitive root iff the exponent is non-zero (mod q) -/
lemma isPrimitiveRoot_zeta_pow_iff (k : Fin q) :
    IsPrimitiveRoot ((ζ q) ^ k.val) q ↔ k.val ≠ 0 := by
  constructor
  · intro hk h
    simp_all +decide [IsPrimitiveRoot.iff_def, ← pow_mul]
    exact absurd (hk 1) (Nat.Prime.not_dvd_one Fact.out)
  · intro hk_ne_zero
    have h_coprime : Nat.gcd k.val q = 1 := by
      exact Nat.Coprime.symm ((Fact.out : Nat.Prime q) |> fun h =>
        h.coprime_iff_not_dvd.mpr <| Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk_ne_zero) k.2)
    convert IsPrimitiveRoot.pow_of_coprime _ _ _
    · convert zeta_isPrimitiveRoot q
    · exact h_coprime

/-! ## Part 6: Main Theorems -/

/-- Upper bound on |balance|² using variance.

For balance = Σ FW_r · ζ^r, by AM-GM on the (q-1) non-DC DFT components:
  |Norm(balance)|² ≤ ∏_{k≠0} |b_k|² ≤ (q·V/(q-1))^{q-1}

So: |Norm(balance)| ≤ (q·V/(q-1))^{(q-1)/2} -/
theorem norm_balance_upper_bound (FW : Fin q → ℕ) :
    let V := foldedVariance q FW
    -- The product of squared norms (related to norm squared) is bounded
    ∏ k ∈ Finset.univ.erase 0, Complex.normSq (dft_component q FW k) ≤ ((q * V) / (q - 1)) ^ (q - 1) :=
  dft_am_gm_bound q FW

/-- The gap condition: for small enough variance, the norm bound fires.

If V < 6 and q ≥ 5, then (q·V/(q-1))^{(q-1)/2} < 4^{q-1} ≤ Φ_q(4,3)

For q = 5: (5·6/4)^2 = 56.25 < 256 = 4^4
For q = 7: (7·6/6)^3 = 343 < 4096 = 4^6 -/
theorem gap_condition_from_variance (hq_ge5 : q ≥ 5) (FW : Fin q → ℕ)
    (hV : foldedVariance q FW < 6) :
    ((q * foldedVariance q FW) / (q - 1)) ^ (q - 1) < (4 : ℝ) ^ (2 * (q - 1)) := by
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast Nat.Prime.pos hq_fact.out
  have hq_ge5_real : (q : ℝ) ≥ 5 := by exact_mod_cast hq_ge5
  have hq_sub_pos : (0 : ℝ) < q - 1 := by linarith
  -- (q * V) / (q-1) < q * 6 / (q-1) ≤ 7.5 for q ≥ 5
  have h1 : (q * foldedVariance q FW) / (q - 1) < (q * 6) / (q - 1) := by
    apply div_lt_div_of_pos_right _ hq_sub_pos
    exact mul_lt_mul_of_pos_left hV hq_pos
  -- For q ≥ 5: q * 6 / (q-1) ≤ 30/4 = 7.5
  have h2 : (q * (6 : ℝ)) / (q - 1) ≤ 7.5 := by
    have heq : (q : ℝ) * 6 / (q - 1) = 6 + 6 / (q - 1) := by field_simp; ring
    rw [heq]
    have hle : (6 : ℝ) / (q - 1) ≤ 6 / 4 := by
      apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 6)
      · linarith
      · linarith
    linarith
  have h3 : ((q * foldedVariance q FW) / (q - 1)) ^ (q - 1) < (7.5 : ℝ) ^ (q - 1) := by
    have hnn : 0 ≤ (q * foldedVariance q FW) / (q - 1) := by
      apply div_nonneg
      · apply mul_nonneg (le_of_lt hq_pos)
        unfold foldedVariance
        apply Finset.sum_nonneg
        intro r _
        apply sq_nonneg
      · linarith
    have hlt : (q * foldedVariance q FW) / (q - 1) < 7.5 := lt_of_lt_of_le h1 h2
    have hq_sub_pos' : q - 1 > 0 := by omega
    gcongr
  -- 7.5^{q-1} < 16^{q-1} = 4^{2(q-1)} for q ≥ 2
  have h4 : (7.5 : ℝ) ^ (q - 1) < (16 : ℝ) ^ (q - 1) := by
    have hq_sub_pos' : q - 1 > 0 := by omega
    gcongr
    norm_num
  have h5 : (16 : ℝ) ^ (q - 1) = (4 : ℝ) ^ (2 * (q - 1)) := by
    have : (16 : ℝ) = 4^2 := by norm_num
    rw [this, ← pow_mul]
  linarith

/-- Combined theorem: For q ≥ 5 prime with variance < 6, the gap condition holds.

This implies balance = 0 by the integrality argument:
1. (4-3ζ) | balance in Z[ζ] (from cyclotomic divisibility chain)
2. If balance ≠ 0, |Norm(balance)| ≥ Φ_q(4,3)
3. But gap condition says |Norm(balance)| < Φ_q(4,3)
4. Contradiction, so balance = 0 -/
theorem gap_implies_norm_lt_cyclotomic (hq_ge5 : q ≥ 5) (FW : Fin q → ℕ)
    (hV : foldedVariance q FW < 6) :
    ∏ k ∈ Finset.univ.erase 0, Complex.normSq (dft_component q FW k) < ((4 : ℝ) ^ (q - 1)) ^ 2 := by
  have h1 := norm_balance_upper_bound q FW
  have h2 := gap_condition_from_variance q hq_ge5 FW hV
  have h3 : ((4 : ℝ) ^ (q - 1)) ^ 2 = (4 : ℝ) ^ (2 * (q - 1)) := by rw [← pow_mul]; ring_nf
  rw [h3]
  exact lt_of_le_of_lt h1 h2

end Collatz.CyclotomicGap
