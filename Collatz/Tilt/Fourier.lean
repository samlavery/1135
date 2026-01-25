/-
Copyright (c) 2024. All rights reserved.
Released under MIT license.
-/
import Collatz.CyclotomicAlgebra
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic

/-!
# Fourier Analysis for Tilt-Balance

This file contains Fourier lemmas for the tilt-balance proof.
The main result establishes that nonnegative integer coefficients whose sum
against a primitive root vanishes must all be equal.

## Main Results

* `nonneg_coeffs_primitive_root_zero_eq_constant`: The core Fourier rigidity lemma (ℕ over ℂ)
* `foldedWeights_equal_from_balance`: Application to natural number weights

## Key Insight

The Fourier rigidity is provided by `primitive_root_nonneg_coeffs_eq` from
CyclotomicAlgebra.lean, which proves that for prime q and nonnegative integer
coefficients, Σ a_r ζ^r = 0 implies all a_r are equal.

This file provides a clean interface for the tilt-balance subsystem.
-/

open scoped BigOperators
open Finset

namespace Collatz.Fourier

/-! ## Primitive Root Properties -/

/-- For a primitive q-th root of unity, the sum 1 + ζ + ζ² + ... + ζ^{q-1} = 0. -/
lemma sum_primitive_root_powers {K : Type*} [CommRing K] [IsDomain K]
    {q : ℕ} (hq : 1 < q) (ζ : K) (hζ : IsPrimitiveRoot ζ q) :
    ∑ i : Fin q, ζ ^ i.val = 0 := by
  have h := hζ.geom_sum_eq_zero hq
  -- Convert sum over Fin q to sum over range q
  rw [← h, Finset.sum_range]

/-- Alternative form: Σᵢ ζⁱ = 0 for primitive root when q > 1. -/
lemma geom_sum_primitive_root_eq_zero {K : Type*} [CommRing K] [IsDomain K]
    {q : ℕ} (hq : 1 < q) (ζ : K) (hζ : IsPrimitiveRoot ζ q) :
    ∑ i ∈ range q, ζ ^ i = 0 :=
  hζ.geom_sum_eq_zero hq

/-! ## Core Fourier Rigidity Lemma (ℕ-coefficients over ℂ) -/

/-- **Main Fourier Rigidity Lemma (ℕ-coefficients over ℂ)**

    For a prime `q`, a primitive `q`-th root of unity `ζ : ℂ`, and a family
    of nonnegative integer coefficients `a : Fin q → ℕ`, if

      ∑ r, (a r : ℂ) * ζ^r = 0,

    then all coefficients `a r` are equal (in fact equal to `a 0`).

    This is a thin wrapper around `primitive_root_nonneg_coeffs_eq` from
    CyclotomicAlgebra.lean.
-/
lemma nonneg_coeffs_primitive_root_zero_eq_constant
    (q : ℕ) (hq_prime : Nat.Prime q)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ q)
    (a : Fin q → ℕ)
    (h_sum_zero : ∑ r : Fin q, (a r : ℂ) * ζ^(r : ℕ) = 0) :
    ∀ r : Fin q, a r = a ⟨0, hq_prime.pos⟩ := by
  classical
  -- `primitive_root_nonneg_coeffs_eq` already proves all coefficients are equal
  have h_all_eq : ∀ r s : Fin q, a r = a s :=
    Collatz.CyclotomicAlgebra.primitive_root_nonneg_coeffs_eq q hq_prime ζ hζ a h_sum_zero
  -- Specialize with `s = 0`
  intro r
  exact h_all_eq r ⟨0, hq_prime.pos⟩

/-- Variant: all coefficients equal to each other. -/
lemma nonneg_coeffs_primitive_root_all_eq
    (q : ℕ) (hq_prime : Nat.Prime q)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ q)
    (a : Fin q → ℕ)
    (h_sum_zero : ∑ r : Fin q, (a r : ℂ) * ζ^(r : ℕ) = 0) :
    ∀ r s : Fin q, a r = a s :=
  Collatz.CyclotomicAlgebra.primitive_root_nonneg_coeffs_eq q hq_prime ζ hζ a h_sum_zero

/-! ## Consequence: Equal Folded Weights from Balance -/

/-- From balance at prime q (sum against primitive root = 0), folded weights are equal.
    This connects the Fourier lemma back to the tilt structure. -/
theorem foldedWeights_equal_from_balance
    {q : ℕ} (hq_prime : Nat.Prime q)
    (W : Fin q → ℕ)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ q)
    (h_balance : ∑ r : Fin q, (W r : ℂ) * ζ^(r : ℕ) = 0) :
    ∃ c : ℕ, ∀ r, W r = c := by
  have h_const := nonneg_coeffs_primitive_root_zero_eq_constant q hq_prime ζ hζ W h_balance
  exact ⟨W ⟨0, hq_prime.pos⟩, h_const⟩

/-- Corollary: Equal folded weights expressed as pairwise equality. -/
theorem foldedWeights_pairwise_equal_from_balance
    {q : ℕ} (hq_prime : Nat.Prime q)
    (W : Fin q → ℕ)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ q)
    (h_balance : ∑ r : Fin q, (W r : ℂ) * ζ^(r : ℕ) = 0) :
    ∀ r s : Fin q, W r = W s :=
  nonneg_coeffs_primitive_root_all_eq q hq_prime ζ hζ W h_balance

end Collatz.Fourier
