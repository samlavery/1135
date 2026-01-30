/-
Copyright (c) 2024. All rights reserved.
Released under MIT license.

# Integrality Bridge for Cyclotomic Fields

This file provides the key bridge between integer divisibility and cyclotomic
field arithmetic for the Collatz ANT argument. It isolates ALL the algebraic
number theory (ζ, adjoin ℤ{ζ}, norms, integrality) into one module.

## Architecture

**For CyclotomicAlgebra.lean**:
- Input: Integer divisibility `Φ_q(4,3) | waveSumPoly(4)`
- Output: Factorization `balanceSumK FW = (4-3ζ) * T` with `T` integral

**For TiltBalance.lean** (via `local_tilt_obstruction`):
- Input: Integer divisibility + bounds on folded weights
- Output: Pure arithmetic conclusion (no ζ visible!)

## Main Results

* `integral_of_mem_adjoin_zeta`: Elements of ℤ[ζ] are integral over ℤ
* `T_isIntegral_from_poly`: T is integral when given as a polynomial in ζ
* `bridge_norm_divides`: Norm(4-3ζ) | Norm(balanceSumK) in ℤ
* `local_tilt_obstruction`: **Key theorem for TiltBalance** - arithmetic corollary

## Strategy

The bridge does NOT require proving that "quotients are integral" in general.
Instead, we use:
1. T is explicitly constructed from polynomial operations, hence T ∈ ℤ[ζ]
2. Elements of ℤ[ζ] are integral (adjoin_le_integralClosure)
3. NumberField.norm is multiplicative and ℤ-valued
4. Therefore Norm(4-3ζ) | Norm(balanceSumK) in ℤ
-/

import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Tactic

open scoped NumberField
open Algebra Polynomial

namespace Collatz.IntegralityBridge

variable {q : ℕ} [hq_fact : Fact (Nat.Prime q)]

/-!
## Basic Definitions
-/

/-- The cyclotomic field K = ℚ(ζ_q) for prime q. -/
abbrev K (q : ℕ) [Fact (Nat.Prime q)] : Type := CyclotomicField q ℚ

/-- The canonical primitive q-th root of unity in K. -/
noncomputable def zeta : K q :=
  IsCyclotomicExtension.zeta q ℚ (K q)

/-- The balance sum Σ FW_r ζ^r. -/
noncomputable def balanceSumK (FW : Fin q → ℕ) : K q :=
  ∑ r : Fin q, (FW r : K q) * zeta ^ (r : ℕ)

/-- The element 4 - 3ζ (evaluation of Φ_q(4,3) structure). -/
noncomputable def fourSubThreeZeta : K q :=
  (4 : K q) - 3 * zeta

/-!
## Primitive Root Properties
-/

/-- ζ is a primitive q-th root of unity. -/
lemma zeta_is_primitive_root :
    IsPrimitiveRoot (zeta (q := q)) q :=
  IsCyclotomicExtension.zeta_spec q ℚ (K q)

/-- ζ is integral over ℤ. -/
lemma zeta_isIntegral : IsIntegral ℤ (zeta (q := q)) := by
  have hq_pos : 0 < q := Nat.Prime.pos hq_fact.out
  exact zeta_is_primitive_root.isIntegral hq_pos

/-!
## Membership in adjoin ℤ {ζ}
-/

/-- Elements in adjoin ℤ {ζ} are integral over ℤ. -/
lemma integral_of_mem_adjoin_zeta (x : K q)
    (hx : x ∈ adjoin ℤ ({zeta (q := q)} : Set (K q))) :
    IsIntegral ℤ x := by
  have h_le : adjoin ℤ ({zeta (q := q)} : Set (K q)) ≤
      integralClosure ℤ (K q) := by
    apply adjoin_le_integralClosure
    have hq_pos : 0 < q := Nat.Prime.pos hq_fact.out
    exact zeta_is_primitive_root.isIntegral hq_pos
  exact h_le hx

/-- 4 - 3ζ is in adjoin ℤ {ζ}. -/
lemma fourSubThreeZeta_mem_adjoin :
    fourSubThreeZeta (q := q) ∈
      adjoin ℤ ({zeta (q := q)} : Set (K q)) := by
  unfold fourSubThreeZeta
  apply Subalgebra.sub_mem
  · exact Subalgebra.algebraMap_mem _ 4
  · apply Subalgebra.mul_mem
    · exact Subalgebra.algebraMap_mem _ 3
    · exact Algebra.subset_adjoin (Set.mem_singleton _)

/-- 4 - 3ζ is integral over ℤ. -/
lemma fourSubThreeZeta_isIntegral :
    IsIntegral ℤ (fourSubThreeZeta (q := q)) :=
  integral_of_mem_adjoin_zeta _ fourSubThreeZeta_mem_adjoin

/-- The balance sum is in adjoin ℤ {ζ}. -/
lemma balanceSumK_mem_adjoin (FW : Fin q → ℕ) :
    balanceSumK (q := q) FW ∈
      adjoin ℤ ({zeta (q := q)} : Set (K q)) := by
  unfold balanceSumK
  apply Subalgebra.sum_mem
  intro r _
  apply Subalgebra.mul_mem
  · exact Subalgebra.algebraMap_mem _ (FW r : ℤ)
  · apply Subalgebra.pow_mem
    exact Algebra.subset_adjoin (Set.mem_singleton _)

/-- The balance sum is integral. -/
lemma balanceSumK_isIntegral (FW : Fin q → ℕ) :
    IsIntegral ℤ (balanceSumK (q := q) FW) :=
  integral_of_mem_adjoin_zeta _ (balanceSumK_mem_adjoin FW)

/-!
## Nonzero Property
-/

/-- 4 - 3ζ is nonzero in the cyclotomic field.

    Proof: If 4 - 3ζ = 0, then ζ = 4/3. But ζ^q = 1 implies (4/3)^q = 1,
    meaning 4^q = 3^q, contradicting 4 ≠ 3. -/
lemma fourSubThreeZeta_ne_zero : fourSubThreeZeta (q := q) ≠ 0 := by
  unfold fourSubThreeZeta
  intro h_eq
  have hq_prime := hq_fact.out
  have hq_pos : 0 < q := Nat.Prime.pos hq_prime
  -- If 4 - 3ζ = 0, then 3ζ = 4
  have h_3zeta_eq_4 : (3 : K q) * zeta = 4 := by
    have h1 : (4 : K q) - 3 * zeta = 0 := h_eq
    exact (sub_eq_zero.mp h1).symm
  -- But ζ^q = 1
  have hζ := zeta_is_primitive_root (q := q)
  have h_pow_one : (zeta (q := q)) ^ q = 1 := hζ.pow_eq_one
  -- So (3ζ)^q = 3^q and also = 4^q
  have h_pow_eq : (4 : K q) ^ q = 3 ^ q := by
    calc (4 : K q) ^ q
        = (3 * zeta) ^ q := by rw [h_3zeta_eq_4]
      _ = 3 ^ q * zeta ^ q := by ring
      _ = 3 ^ q * 1 := by rw [h_pow_one]
      _ = 3 ^ q := by ring
  -- But 4^q ≠ 3^q in ℕ
  have h_nat_ineq : (4 : ℕ) ^ q ≠ 3 ^ q := by
    have h1 : (4 : ℕ) ^ q > 3 ^ q := Nat.pow_lt_pow_left (by omega : 3 < 4) (by omega : q ≠ 0)
    omega
  -- Lift to the field
  have h_field_ineq : (4 : K q) ^ q ≠ 3 ^ q := by
    intro heq
    have h4 : (4 : K q) ^ q = ((4 : ℕ) ^ q : ℕ) := by norm_cast
    have h3 : (3 : K q) ^ q = ((3 : ℕ) ^ q : ℕ) := by norm_cast
    rw [h4, h3] at heq
    have hinj : Function.Injective (Nat.cast (R := K q)) := Nat.cast_injective
    exact h_nat_ineq (hinj heq)
  exact h_field_ineq h_pow_eq

/-!
## T Integrality from Polynomial Expression

The key insight: T is integral because it's EXPLICITLY given as a polynomial in ζ
with integer coefficients. We don't need any abstract "quotient integrality" lemma.
-/

/-- A ℤ-linear combination of powers of ζ is in adjoin ℤ {ζ}. -/
lemma poly_in_zeta_mem_adjoin (coeffs : Fin q → ℤ) :
    (∑ r : Fin q, (coeffs r : K q) * zeta ^ (r : ℕ)) ∈
      adjoin ℤ ({zeta (q := q)} : Set (K q)) := by
  apply Subalgebra.sum_mem
  intro r _
  apply Subalgebra.mul_mem
  · exact Subalgebra.algebraMap_mem _ _
  · apply Subalgebra.pow_mem
    exact Algebra.subset_adjoin (Set.mem_singleton _)

/-- T is integral when explicitly given as a polynomial in ζ with ℤ coefficients. -/
theorem T_isIntegral_from_poly
    (T : K q)
    (hT_poly : ∃ coeffs : Fin q → ℤ,
        T = ∑ r : Fin q, (coeffs r : K q) * zeta ^ (r : ℕ)) :
    IsIntegral ℤ T := by
  obtain ⟨coeffs, hcoeffs⟩ := hT_poly
  rw [hcoeffs]
  exact integral_of_mem_adjoin_zeta _ (poly_in_zeta_mem_adjoin coeffs)

/-- T is in adjoin ℤ {ζ} when explicitly given as a polynomial in ζ. -/
theorem T_mem_adjoin_from_poly
    (T : K q)
    (hT_poly : ∃ coeffs : Fin q → ℤ,
        T = ∑ r : Fin q, (coeffs r : K q) * zeta ^ (r : ℕ)) :
    T ∈ adjoin ℤ ({zeta (q := q)} : Set (K q)) := by
  obtain ⟨coeffs, hcoeffs⟩ := hT_poly
  rw [hcoeffs]
  exact poly_in_zeta_mem_adjoin coeffs

/-!
## Alternative: Working with Algebra.norm ℚ

For some applications over ℚ instead of ℤ. This is well-defined since
K q IS finite-dimensional over ℚ (dimension = φ(q) = q-1 for prime q).
-/

/-- Alternative bridge using Algebra.norm over ℚ.

    Note: Unlike the ℤ case, Algebra.norm ℚ on K q IS well-defined since
    K q is finite-dimensional over ℚ. However, this gives divisibility
    in ℚ, not ℤ, which is less useful for the integer arithmetic we need. -/
theorem bridge_norm_divides_rat
    (FW : Fin q → ℕ)
    (T : K q)
    (_hT_poly : ∃ coeffs : Fin q → ℤ,
        T = ∑ r : Fin q, (coeffs r : K q) * zeta ^ (r : ℕ))
    (hT_eq : balanceSumK (q := q) FW = fourSubThreeZeta (q := q) * T) :
    (Algebra.norm ℚ (fourSubThreeZeta (q := q))) ∣
      (Algebra.norm ℚ (balanceSumK (q := q) FW)) := by
  have h_norm_mul :
      Algebra.norm ℚ (fourSubThreeZeta (q := q) * T) =
        Algebra.norm ℚ (fourSubThreeZeta (q := q)) *
          Algebra.norm ℚ T :=
    map_mul (Algebra.norm ℚ) _ _
  have h_norm :
      Algebra.norm ℚ (balanceSumK (q := q) FW) =
        Algebra.norm ℚ (fourSubThreeZeta (q := q)) *
          Algebra.norm ℚ T := by
    rw [hT_eq]
    exact h_norm_mul
  exact ⟨Algebra.norm ℚ T, h_norm⟩

/-!
## Section: Pure Arithmetic Interface for TiltBalance

These theorems provide the clean arithmetic interface that TiltBalance needs.
No ζ, no adjoin, no integrality proofs visible - just arithmetic conclusions
derived from the ANT machinery.
-/

/-- The element of 𝓞(K q) corresponding to balanceSumK FW.
    This lifts the integral element from K q to the ring of integers. -/
noncomputable def balanceSumK_integral (FW : Fin q → ℕ) : 𝓞 (K q) :=
  IsIntegralClosure.mk' (𝓞 (K q)) (balanceSumK FW) (balanceSumK_isIntegral FW)

/-- The norm of `balanceSumK FW` in ℤ (as an integer).
    This is computed on 𝓞(K q) to ensure we get a meaningful norm
    (since K q is not finite over ℤ, Algebra.norm ℤ on K q would be 1). -/
noncomputable def normBalanceSumK (FW : Fin q → ℕ) : ℤ :=
  Algebra.norm ℤ (balanceSumK_integral (q := q) FW)

/-- The element of 𝓞(K q) corresponding to fourSubThreeZeta. -/
noncomputable def fourSubThreeZeta_integral : 𝓞 (K q) :=
  IsIntegralClosure.mk' (𝓞 (K q)) (fourSubThreeZeta (q := q)) (fourSubThreeZeta_isIntegral (q := q))

/-- The norm of `4 - 3ζ` equals Φ_q(4,3).
    This is the key fact connecting cyclotomic norms to bivariate cyclotomic polynomials. -/
noncomputable def normFourSubThreeZeta : ℤ :=
  Algebra.norm ℤ (fourSubThreeZeta_integral (q := q))

/-!
## Norm Divisibility Bridge

This is the core bridge lemma. We use:
1. NumberField.norm is multiplicative on the ring of integers 𝓞 (K q)
2. Algebra.norm ℤ : 𝓞 (K q) → ℤ is well-defined (𝓞 K is finite over ℤ)
3. From B = u * T in 𝓞 (K q) we get Norm(B) = Norm(u) * Norm(T)
4. Hence Norm(u) | Norm(B) in ℤ

**Important**: We work on 𝓞 (K q), NOT on K q directly, because K q is not
finite over ℤ (only over ℚ), so Algebra.norm ℤ on K q would be meaningless.
-/

/-- Norm divisibility: If balanceSumK = fourSubThreeZeta * T with T integral, then
    Norm(fourSubThreeZeta) | Norm(balanceSumK) in ℤ.

    This version correctly works on 𝓞 (K q) where Algebra.norm ℤ is well-defined. -/
lemma norm_fourSubThreeZeta_dvd_norm_balanceSumK
    (FW : Fin q → ℕ)
    (T : K q)
    (hT_int : IsIntegral ℤ T)
    (hT_eq : balanceSumK (q := q) FW = fourSubThreeZeta (q := q) * T) :
    normFourSubThreeZeta (q := q) ∣ normBalanceSumK (q := q) FW := by
  -- Lift T to 𝓞 (K q)
  let T_int : 𝓞 (K q) := IsIntegralClosure.mk' (𝓞 (K q)) T hT_int
  have hT_coerce : (T_int : K q) = T := IsIntegralClosure.algebraMap_mk' _ _ _

  -- The factorization lifts to 𝓞 (K q) since the coercion is injective
  have h_factor_int : balanceSumK_integral FW = fourSubThreeZeta_integral (q := q) * T_int := by
    apply IsFractionRing.injective (𝓞 (K q)) (K q)
    simp only [map_mul]
    -- Unfold definitions to expose IsIntegralClosure.mk' structure
    simp only [balanceSumK_integral, fourSubThreeZeta_integral]
    rw [IsIntegralClosure.algebraMap_mk', IsIntegralClosure.algebraMap_mk',
        IsIntegralClosure.algebraMap_mk']
    exact hT_eq

  -- Use multiplicativity of norm on 𝓞 (K q)
  unfold normFourSubThreeZeta normBalanceSumK
  rw [h_factor_int, map_mul]
  exact dvd_mul_right _ _

/-- **Main Bridge Theorem**: If balanceSumK = (4-3ζ) * T with T explicitly a polynomial
    in ζ with ℤ coefficients, then Norm(4-3ζ) | Norm(balanceSumK) in ℤ.

    This is the key result connecting the cyclotomic field arithmetic to
    divisibility in ℤ, which then combines with analytic bounds to give
    the global obstruction.

    This version correctly uses norms on 𝓞 (K q). -/
theorem bridge_norm_divides
    (FW : Fin q → ℕ)
    (T : K q)
    (hT_poly : ∃ coeffs : Fin q → ℤ,
        T = ∑ r : Fin q, (coeffs r : K q) * zeta ^ (r : ℕ))
    (hT_eq : balanceSumK (q := q) FW = fourSubThreeZeta (q := q) * T) :
    normFourSubThreeZeta (q := q) ∣ normBalanceSumK (q := q) FW := by
  -- T is integral since it's explicitly in ℤ[ζ]
  have hT_int : IsIntegral ℤ T := T_isIntegral_from_poly T hT_poly
  exact norm_fourSubThreeZeta_dvd_norm_balanceSumK FW T hT_int hT_eq

/-- Norm bound for balance sum: |N(Σ FW_r ζ^r)| ≤ (Σ FW_r)^{q-1}.

    This follows from:
    - N(α) = ∏_{σ} σ(α) over all embeddings σ : K → ℂ
    - |σ(Σ FW_r ζ^r)| = |Σ FW_r σ(ζ)^r| ≤ Σ FW_r (triangle inequality, |σ(ζ)| = 1)
    - |N(α)| ≤ (Σ FW_r)^{[K:ℚ]} = (Σ FW_r)^{q-1} -/
lemma norm_balanceSumK_bound (FW : Fin q → ℕ) :
    (normBalanceSumK FW).natAbs ≤ (∑ r : Fin q, FW r) ^ (q - 1) := by
  have hq_pos : 0 < q := Nat.Prime.pos hq_fact.out
  have hq_gt : 1 < q := Nat.Prime.one_lt hq_fact.out
  haveI : NumberField (K q) := inferInstance

  let α : K q := balanceSumK (q := q) FW
  let S := ∑ r : Fin q, (FW r : ℝ)

  -- Step 1: Per-place bound using triangle inequality
  have h_place_bound : ∀ w : NumberField.InfinitePlace (K q), w α ≤ S := by
    intro w
    let φ := NumberField.InfinitePlace.embedding w
    -- w α = ‖φ α‖ = ‖Σ FW_r · φ(ζ)^r‖
    have h_wα : w α = ‖φ (balanceSumK (q := q) FW)‖ :=
      (NumberField.InfinitePlace.norm_embedding_eq w (balanceSumK (q := q) FW)).symm
    rw [h_wα]
    -- φ(balanceSumK FW) = Σ FW_r · φ(ζ)^r
    have h_φα : φ (balanceSumK (q := q) FW) = ∑ r : Fin q, (FW r : ℂ) * (φ (zeta (q := q)))^(r : ℕ) := by
      unfold balanceSumK
      simp only [map_sum, map_mul, map_pow, map_natCast]
    rw [h_φα]
    -- Triangle inequality: ‖Σ a_r‖ ≤ Σ ‖a_r‖
    have h_tri := norm_sum_le (s := Finset.univ) (fun r => (FW r : ℂ) * (φ (zeta (q := q)))^(r : ℕ))
    refine h_tri.trans ?_
    -- Each term: ‖FW_r · φ(ζ)^r‖ = FW_r · ‖φ(ζ)‖^r = FW_r (since ‖φ(ζ)‖ = 1)
    have h_terms : ∀ r : Fin q, ‖(FW r : ℂ) * (φ (zeta (q := q)))^(r : ℕ)‖ = FW r := by
      intro r
      rw [norm_mul, norm_pow]
      have hζ := zeta_is_primitive_root (q := q)
      have h_φζ_root : (φ (zeta (q := q)))^q = 1 := by
        rw [← map_pow, IsPrimitiveRoot.pow_eq_one hζ, map_one]
      have h_norm_φζ : ‖φ (zeta (q := q))‖ = 1 := by
        exact Complex.norm_eq_one_of_pow_eq_one h_φζ_root (Nat.Prime.ne_zero hq_fact.out)
      rw [h_norm_φζ, one_pow, mul_one]
      simp only [Complex.norm_natCast]
    simp_rw [h_terms]
    rfl

  -- Step 2: Use product formula |N_ℚ(α)| = ∏_w w(α)^{mult(w)}
  have h_prod_formula := NumberField.InfinitePlace.prod_eq_abs_norm α

  -- Step 3: Bound the product using per-place bounds
  have h_prod_bound : ∏ w : NumberField.InfinitePlace (K q),
      (w α)^(NumberField.InfinitePlace.mult w) ≤ S ^ (q - 1) := by
    have h_sum_mult : ∑ w : NumberField.InfinitePlace (K q),
        NumberField.InfinitePlace.mult w = Module.finrank ℚ (K q) :=
      NumberField.InfinitePlace.sum_mult_eq
    have h_deg : Module.finrank ℚ (K q) = q - 1 := by
      have hirr : Irreducible (Polynomial.cyclotomic q ℚ) :=
        Polynomial.cyclotomic.irreducible_rat hq_pos
      have h_totient := IsCyclotomicExtension.finrank (K q) hirr
      -- For prime q, totient q = q - 1
      have h_prime := hq_fact.out
      rw [Nat.totient_prime h_prime] at h_totient
      exact h_totient
    have h_factor_bound : ∀ w : NumberField.InfinitePlace (K q),
        (w α)^(NumberField.InfinitePlace.mult w) ≤ S^(NumberField.InfinitePlace.mult w) := by
      intro w
      by_cases hS : S = 0
      · have h_all_zero : ∀ r, FW r = 0 := by
          intro r
          have h_nonneg : ∀ i ∈ Finset.univ, (0 : ℝ) ≤ (FW i : ℝ) := fun i _ => by positivity
          have h := Finset.sum_eq_zero_iff_of_nonneg h_nonneg
          have h2 := h.mp hS r (Finset.mem_univ r)
          simp only [Nat.cast_eq_zero] at h2
          exact h2
        have hα_zero : α = 0 := by
          simp only [α, balanceSumK]
          simp_rw [h_all_zero]
          simp
        simp [hα_zero, hS]
      · exact (pow_le_pow_left₀ (apply_nonneg w α) (h_place_bound w)) _
    calc ∏ w, (w α)^(NumberField.InfinitePlace.mult w)
        ≤ ∏ w, S^(NumberField.InfinitePlace.mult w) :=
          Finset.prod_le_prod (fun w _ => pow_nonneg (apply_nonneg w α) _) (fun w _ => h_factor_bound w)
      _ = S ^ (∑ w, NumberField.InfinitePlace.mult w) := by
          rw [← Finset.prod_pow_eq_pow_sum]
      _ = S ^ (q - 1) := by rw [h_sum_mult, h_deg]

  -- Step 4: Get |N_ℚ(α)| ≤ S^{q-1}
  have h_abs_bound : |Algebra.norm ℚ α| ≤ S ^ (q - 1) := by
    rw [← h_prod_formula]
    exact h_prod_bound

  -- Step 5: Convert to final inequality
  -- Key fact: (Algebra.norm ℤ x : ℚ) = Algebra.norm ℚ (x : K) for x in ring of integers
  have h_norm_eq_cast : ((normBalanceSumK FW : ℤ) : ℚ) = Algebra.norm ℚ α := by
    simp only [normBalanceSumK, α]
    -- balanceSumK_integral FW : 𝓞 (K q) coerces to balanceSumK FW : K q
    have h_coerce : (balanceSumK_integral FW : K q) = balanceSumK FW :=
      IsIntegralClosure.algebraMap_mk' _ _ _
    rw [← h_coerce]
    -- Now apply Algebra.coe_norm_int: (norm ℤ x : ℚ) = norm ℚ (x : K) for x : 𝓞 K
    exact Algebra.coe_norm_int (balanceSumK_integral FW)

  have h_natAbs_le : (normBalanceSumK FW).natAbs ≤ (∑ r : Fin q, FW r) ^ (q - 1) := by
    have h1 : |((normBalanceSumK FW : ℤ) : ℚ)| = ((normBalanceSumK FW).natAbs : ℚ) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]
      simp only [Int.cast_natCast]
    have h2 : |Algebra.norm ℚ α| ≤ ((∑ r : Fin q, FW r) ^ (q - 1) : ℕ) := by
      -- The bound h_abs_bound is in ℝ: ↑|(Algebra.norm ℚ) α| ≤ S ^ (q - 1)
      -- We need |(Algebra.norm ℚ) α| ≤ (∑ FW r) ^ (q-1) in ℚ
      -- Use Rat.cast_abs: ↑|q| = |↑q| for q : ℚ and cast to ℝ
      have h_cast_eq : (↑|(Algebra.norm ℚ) α| : ℝ) = |((Algebra.norm ℚ) α : ℝ)| :=
        Rat.cast_abs (Algebra.norm ℚ α)
      have h_bound_real : |((Algebra.norm ℚ) α : ℝ)| ≤ ((∑ r : Fin q, FW r) ^ (q - 1) : ℕ) := by
        rw [← h_cast_eq]
        calc (↑|(Algebra.norm ℚ) α| : ℝ)
            ≤ S ^ (q - 1) := h_abs_bound
          _ = (∑ r : Fin q, (FW r : ℝ)) ^ (q - 1) := by rfl
          _ = (((∑ r : Fin q, FW r) ^ (q - 1) : ℕ) : ℝ) := by norm_cast
      exact_mod_cast h_bound_real
    have h3 : ((normBalanceSumK FW).natAbs : ℚ) ≤ ((∑ r : Fin q, FW r) ^ (q - 1) : ℕ) := by
      rw [← h1, h_norm_eq_cast]
      exact_mod_cast h2
    exact_mod_cast h3

  exact h_natAbs_le

/-- Helper: embedding K q into ℂ maps zeta to a primitive q-th root. -/
lemma embedding_zeta_isPrimitiveRoot (σ : K q →+* ℂ) :
    IsPrimitiveRoot (σ (zeta (q := q))) q := by
  have hζ := zeta_is_primitive_root (q := q)
  exact hζ.map_of_injective σ.injective

/-- **Key lemma**: For a primitive q-th root ζ (q prime) and non-negative integers a_k,
    if Σ a_k ζ^k = 0 then all a_k are equal.

    **Proof sketch**:
    1. The minimal polynomial of ζ over ℚ is Φ_q(x) = 1 + x + ... + x^{q-1}
    2. If A(x) = Σ a_k x^k satisfies A(ζ) = 0, then minpoly | A
    3. Since deg A ≤ q-1 = deg Φ_q and Φ_q is irreducible, A = c · Φ_q for some c
    4. Comparing coefficients: all a_k = c

    This is the core algebraic fact underlying the "no non-trivial cycles" argument. -/
lemma zero_sum_nonneg_coeffs_primitive_root_const
    {K : Type*} [Field K] [CharZero K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ q)
    (a : Fin q → ℕ)
    (h_sum : ∑ k : Fin q, (a k : K) * ζ^(k : ℕ) = 0) :
    ∃ c : ℕ, ∀ k, a k = c := by
  have hq_pos : 0 < q := Nat.Prime.pos hq_fact.out
  have hq_gt : 1 < q := Nat.Prime.one_lt hq_fact.out

  -- Σ ζ^i = 0 for primitive q-th root (q prime, q > 1)
  have h_geom_zero : ∑ i ∈ Finset.range q, ζ^i = 0 := hζ.geom_sum_eq_zero hq_gt

  -- Convert Fin sum to range sum
  have h_fin_eq_range : ∑ k : Fin q, ζ^(k : ℕ) = ∑ i ∈ Finset.range q, ζ^i := by
    rw [Fin.sum_univ_eq_sum_range]

  -- The proof uses that all coefficients must be equal.
  -- Choose c = a 0 and show all a k = a 0.
  use a 0
  intro k

  -- Key: the kernel of φ : ℤ^q → K, φ(c) = Σ c_k ζ^k, has dimension 1
  -- and is generated by (1,1,...,1) (the cyclotomic relation).
  -- If Σ c_k ζ^k = 0 and c_0 = 0, then c = 0·(1,...,1) = 0.

  -- We show: if Σ (a_k - a_0) ζ^k = 0 and (a_0 - a_0) = 0, then a_k - a_0 = 0 for all k.

  -- Step 1: Σ (a_k - a_0) ζ^k = Σ a_k ζ^k - a_0 · Σ ζ^k = 0 - 0 = 0
  have h_diff_zero : ∑ j : Fin q, ((a j : K) - (a 0 : K)) * ζ^(j : ℕ) = 0 := by
    have h1 : ∑ j : Fin q, ((a j : K) - (a 0 : K)) * ζ^(j : ℕ) =
        ∑ j : Fin q, (a j : K) * ζ^(j : ℕ) - (a 0 : K) * ∑ j : Fin q, ζ^(j : ℕ) := by
      rw [Finset.mul_sum]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [h1, h_sum, h_fin_eq_range, h_geom_zero]
    ring

  -- Step 2: b_k := a_k - a_0 satisfies Σ b_k ζ^k = 0 and b_0 = 0
  let b : Fin q → ℤ := fun j => (a j : ℤ) - (a 0 : ℤ)
  have hb0 : b 0 = 0 := by simp [b]
  have hb_sum : ∑ j : Fin q, (b j : K) * ζ^(j : ℕ) = 0 := by
    convert h_diff_zero using 2 with j
    simp only [b, Int.cast_sub, Int.cast_natCast]

  -- Step 3: All b_k must be zero via minpoly/degree argument
  -- Strategy:
  --   1. Define B(X) = ∑ b_j X^j ∈ ℚ[X]
  --   2. B(ζ) = 0, so minpoly ℚ ζ | B
  --   3. minpoly ℚ ζ = cyclotomic q ℚ, degree q-1
  --   4. Constant term of B is 0 (since b_0 = 0), so X | B
  --   5. cyclotomic q and X are coprime (cyclotomic has nonzero constant term)
  --   6. If B ≠ 0: both minpoly | B and X | B, with gcd = 1, so deg B ≥ q
  --      But deg B ≤ q-1, contradiction
  --   7. So B = 0, hence all b_j = 0

  suffices h_bk_zero : b k = 0 by
    simp only [b, sub_eq_zero] at h_bk_zero
    exact Int.ofNat_inj.mp h_bk_zero

  -- All b j = 0
  have h_b_all_zero : ∀ j : Fin q, b j = 0 := by
    -- Define polynomial B(X) = ∑ b_j X^j ∈ ℚ[X]
    let B : Polynomial ℚ := ∑ j : Fin q, Polynomial.C (b j : ℚ) * Polynomial.X^(j : ℕ)

    -- 1. B(ζ) = 0
    have hB_aeval : Polynomial.aeval ζ B = 0 := by
      simp only [B, map_sum, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
      have h_eq : ∑ x : Fin q, (algebraMap ℚ K) (b x : ℚ) * ζ^(x : ℕ) =
                  ∑ j : Fin q, (b j : K) * ζ^(j : ℕ) := by
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        exact Rat.cast_intCast (b j)
      rw [h_eq, hb_sum]

    -- 2. minpoly divides B
    have h_int : IsIntegral ℚ ζ := (hζ.isIntegral hq_pos).tower_top
    have h_dvd : minpoly ℚ ζ ∣ B := minpoly.dvd ℚ ζ hB_aeval

    -- 3. Identify minpoly with cyclotomic q ℚ
    have hq_prime := hq_fact.out
    have h_minpoly : minpoly ℚ ζ = Polynomial.cyclotomic q ℚ :=
      (IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible hζ
        (Polynomial.cyclotomic.irreducible_rat hq_pos)).symm

    -- 4. Degree of minpoly = q-1
    have h_deg_minpoly : (minpoly ℚ ζ).natDegree = q - 1 := by
      rw [h_minpoly, Polynomial.natDegree_cyclotomic]
      exact Nat.totient_prime hq_prime

    -- 5. Constant term of B is 0 (since b 0 = 0)
    have h_const_B : B.coeff 0 = 0 := by
      simp only [B, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
      -- Only the j = 0 term contributes (when 0 = j : ℕ)
      have h_only_zero : ∀ x : Fin q, (if (0 : ℕ) = (x : ℕ) then (b x : ℚ) else 0) =
                         (if x = 0 then (b x : ℚ) else 0) := by
        intro x
        by_cases hx : x = 0
        · simp [hx]
        · have hne : (0 : ℕ) ≠ (x : ℕ) := by
            simp only [ne_eq]
            intro h
            exact hx (Fin.ext h.symm)
          simp [hx, hne]
      simp only [h_only_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      simp [hb0]

    -- 6. natDegree B ≤ q - 1
    have h_deg_B_le : B.natDegree ≤ q - 1 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro j _
      by_cases hbj : (b j : ℚ) = 0
      · simp [hbj]
      · rw [Polynomial.natDegree_C_mul_X_pow _ _ hbj]
        have : (j : ℕ) < q := j.isLt
        omega

    -- 7. Show B = 0 via degree argument
    have hB_zero : B = 0 := by
      by_contra hB_ne
      -- From constant term = 0: X | B
      have h_X_dvd : Polynomial.X ∣ B := by
        rw [Polynomial.X_dvd_iff]
        exact h_const_B

      -- Cyclotomic q has nonzero constant term (= ±1 for prime q)
      have h_cyc_const_ne : (Polynomial.cyclotomic q ℚ).coeff 0 ≠ 0 := by
        rw [Polynomial.cyclotomic_coeff_zero ℚ hq_gt]
        exact one_ne_zero

      -- X and cyclotomic q are coprime (X doesn't divide cyclotomic since constant term ≠ 0)
      have h_X_not_dvd : ¬(Polynomial.X ∣ Polynomial.cyclotomic q ℚ) := by
        intro hdvd
        rw [Polynomial.X_dvd_iff] at hdvd
        exact h_cyc_const_ne hdvd

      have h_coprime : IsCoprime Polynomial.X (Polynomial.cyclotomic q ℚ) := by
        exact (Polynomial.irreducible_X).coprime_iff_not_dvd.mpr h_X_not_dvd

      -- From minpoly | B and X | B with gcd = 1, their product | B
      -- So deg B ≥ deg X + deg minpoly = 1 + (q-1) = q
      rw [h_minpoly] at h_dvd
      have h_prod_dvd : Polynomial.X * Polynomial.cyclotomic q ℚ ∣ B :=
        h_coprime.mul_dvd h_X_dvd h_dvd

      have h_deg_prod : (Polynomial.X * Polynomial.cyclotomic q ℚ).natDegree = q := by
        rw [Polynomial.natDegree_mul (Polynomial.X_ne_zero) (Polynomial.cyclotomic_ne_zero q ℚ)]
        rw [Polynomial.natDegree_X, Polynomial.natDegree_cyclotomic, Nat.totient_prime hq_prime]
        omega

      have h_deg_le : (Polynomial.X * Polynomial.cyclotomic q ℚ).natDegree ≤ B.natDegree :=
        Polynomial.natDegree_le_of_dvd h_prod_dvd hB_ne

      -- Now q ≤ B.natDegree ≤ q-1, contradiction
      omega

    -- 8. Extract coefficients: B = 0 ⇒ all b j = 0
    intro j
    have hcoeff : B.coeff (j : ℕ) = 0 := by simp [hB_zero]
    simp only [B, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow] at hcoeff
    -- The coefficient sum simplifies to (b j : ℚ) since only x = j contributes
    -- hcoeff is: ∑ x, if (j : ℕ) = (x : ℕ) then (b x : ℚ) else 0 = 0
    have h_eq_swap : ∀ x : Fin q, (if (j : ℕ) = (x : ℕ) then (b x : ℚ) else 0) =
                     (if x = j then (b x : ℚ) else 0) := by
      intro x
      by_cases hxj : x = j
      · simp [hxj]
      · simp only [hxj, ↓reduceIte]
        have hne : (j : ℕ) ≠ (x : ℕ) := fun h => hxj (Fin.ext h.symm)
        simp [hne]
    simp only [h_eq_swap, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hcoeff
    exact Int.cast_injective hcoeff

  exact h_b_all_zero k

/-- Key characterization: if balance sum vanishes and FW non-negative,
    then FW is constant.

    Proof: For ζ a primitive q-th root and c_r ≥ 0:
    - Σ c_r ζ^r = 0 with all c_r ≥ 0 implies c_r constant
    - Embed into ℂ and use the real-part analysis -/
theorem balance_zero_implies_FW_const
    (FW : Fin q → ℕ)
    (h_zero : balanceSumK (q := q) FW = 0) :
    ∀ r s : Fin q, FW r = FW s := by
  have hq_pos : 0 < q := Nat.Prime.pos hq_fact.out
  have hq_gt : 1 < q := Nat.Prime.one_lt hq_fact.out
  have hq_prime := hq_fact.out
  have hζ := zeta_is_primitive_root (q := q)
  intro r s

  -- Embed into ℂ (number fields have embeddings into ℂ)
  -- K q = CyclotomicField q ℚ is a NumberField
  haveI : NumberField (K q) := inferInstance
  obtain ⟨σ⟩ : Nonempty ((K q) →+* ℂ) := inferInstance
  have hσζ : IsPrimitiveRoot (σ (zeta (q := q))) q := embedding_zeta_isPrimitiveRoot σ

  -- The sum is zero in ℂ too
  have h_zero_C : ∑ k : Fin q, (FW k : ℂ) * (σ (zeta (q := q)))^(k : ℕ) = 0 := by
    have h_σ : σ (balanceSumK (q := q) FW) = 0 := by rw [h_zero]; simp
    unfold balanceSumK at h_σ
    simp only [map_sum, map_mul, map_pow, map_natCast] at h_σ
    exact h_σ

  -- Sum of roots of unity = 0
  have h_sum_roots : ∑ k : Fin q, (σ (zeta (q := q)))^(k : ℕ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range]
    exact hσζ.geom_sum_eq_zero hq_gt

  -- If all FW = c (constant), we're done
  by_cases h_const : ∀ k : Fin q, FW k = FW r
  · -- h_const s : FW s = FW r, so (h_const s).symm : FW r = FW s
    exact (h_const s).symm

  -- Otherwise derive contradiction
  push_neg at h_const
  obtain ⟨t, ht⟩ := h_const

  -- Let c = min value, define deviation d_k = FW_k - c ≥ 0
  let c : ℕ := Finset.min' (Finset.image FW Finset.univ)
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

  have hc_le : ∀ k : Fin q, c ≤ FW k := by
    intro k
    exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))

  have hc_attained : ∃ k₀ : Fin q, FW k₀ = c := by
    have h_mem := Finset.min'_mem (Finset.image FW Finset.univ)
        (Finset.image_nonempty.mpr Finset.univ_nonempty)
    rw [Finset.mem_image] at h_mem
    obtain ⟨k₀, _, hk₀⟩ := h_mem
    -- hk₀ : FW k₀ = c (the min value)
    exact ⟨k₀, hk₀⟩

  obtain ⟨k₀, hk₀⟩ := hc_attained

  -- Define d_k = FW_k - c ≥ 0
  have h_dev_sum : ∑ k : Fin q, ((FW k - c : ℕ) : ℂ) * (σ (zeta (q := q)))^(k : ℕ) = 0 := by
    -- First show: Σ c * ζ^k = c * (Σ ζ^k) = c * 0 = 0
    have h_c_sum : ∑ k : Fin q, (c : ℂ) * (σ (zeta (q := q)))^(k : ℕ) = 0 := by
      have h_factor : ∑ k : Fin q, (c : ℂ) * (σ (zeta (q := q)))^(k : ℕ) =
          (c : ℂ) * ∑ k : Fin q, (σ (zeta (q := q)))^(k : ℕ) := by
        rw [Finset.mul_sum]
      rw [h_factor, h_sum_roots, mul_zero]
    -- Then: Σ FW_k * ζ^k - Σ c * ζ^k = 0 - 0 = 0
    have h1 : ∑ k : Fin q, ((FW k : ℂ) - (c : ℂ)) * (σ (zeta (q := q)))^(k : ℕ) = 0 := by
      have h2 : ∑ k : Fin q, (FW k : ℂ) * (σ (zeta (q := q)))^(k : ℕ) -
                ∑ k : Fin q, (c : ℂ) * (σ (zeta (q := q)))^(k : ℕ) = 0 := by
        rw [h_zero_C, h_c_sum, sub_zero]
      convert h2 using 1
      rw [← Finset.sum_sub_distrib]
      congr 1
      ext k
      ring
    -- Finally convert (FW k - c : ℕ) to (FW k : ℂ) - (c : ℂ)
    convert h1 using 2 with k
    have hck : c ≤ FW k := hc_le k
    simp only [Nat.cast_sub hck]

  -- d_{k₀} = 0 and not all d_k = 0 (since FW not constant)
  have h_dk0_zero : FW k₀ - c = 0 := by omega

  -- There exists k with d_k > 0 (since FW not constant but sum = 0)
  have h_exists_pos : ∃ k : Fin q, FW k - c > 0 := by
    by_contra h_all_zero
    push_neg at h_all_zero
    -- If all d_k ≤ 0 (for ℕ, this means = 0), then all FW_k = c
    have h_all_c : ∀ k : Fin q, FW k = c := by
      intro k
      have h1 : FW k - c ≤ 0 := h_all_zero k
      have h2 : c ≤ FW k := hc_le k
      omega
    -- Then FW t = FW r (both equal c), contradicting ht
    have h_eq : FW t = FW r := (h_all_c t).trans (h_all_c r).symm
    exact ht h_eq

  -- Now we have: Σ d_k ζ^k = 0 with d_k ≥ 0, some d_k = 0, some d_k > 0
  -- This is impossible for primitive roots!

  obtain ⟨k₁, hk₁⟩ := h_exists_pos

  -- Apply the key lemma: all deviations must be equal
  have h_all_equal_dev : ∃ d0 : ℕ, ∀ k : Fin q, FW k - c = d0 :=
    zero_sum_nonneg_coeffs_primitive_root_const
      (hζ := hσζ)
      (a := fun k => FW k - c)
      (h_sum := h_dev_sum)

  -- Extract the constant d0
  obtain ⟨d0, hd0⟩ := h_all_equal_dev

  -- But FW k₀ - c = 0, so d0 = 0
  have hd0_zero : d0 = 0 := by
    have h1 := hd0 k₀
    rw [h_dk0_zero] at h1
    exact h1.symm

  -- And FW k₁ - c > 0, so d0 > 0
  have hd0_pos : d0 > 0 := by
    have h1 := hd0 k₁
    rw [← h1]
    exact hk₁

  -- Contradiction: d0 = 0 and d0 > 0
  omega

/-- **LOCAL TILT OBSTRUCTION** (Key theorem for TiltBalance):

    Given:
    1. Integer divisibility: `Φ_q(4,3) | waveSumValue` (from cyclotomic structure)
    2. Folded weight bound: `∀ r, FW r ≤ B` (from tilt/growth constraints)
    3. Gap condition: `Φ_q(4,3) > (B * q)^{q-1}` (exponential growth dominates)

    Conclude: All folded weights are equal.

    **This is the PURE ARITHMETIC interface for TiltBalance**.
    No ζ, no cyclotomic fields, no integrality - just:
    "Under these numeric constraints, FW must be constant."

    The proof uses:
    - Factorization `balanceSumK = (4-3ζ) * T` (from integer divisibility)
    - Norm multiplicativity: `N(balanceSumK) = N(4-3ζ) * N(T)`
    - Gap condition forces `balanceSumK = 0` or `T = 0`
    - `balanceSumK = 0` with FW ∈ ℕ^q and ζ primitive implies FW constant
-/
theorem local_tilt_obstruction
    (FW : Fin q → ℕ)
    (B : ℕ)
    (h_bound : ∀ r : Fin q, FW r ≤ B)
    (h_factor : ∃ T : K q, IsIntegral ℤ T ∧
        balanceSumK (q := q) FW = fourSubThreeZeta (q := q) * T)
    (Φ_q : ℤ)
    (h_Φ_pos : Φ_q > 0)
    (h_norm_eq : normFourSubThreeZeta (q := q) = Φ_q ∨
                 normFourSubThreeZeta (q := q) = -Φ_q)
    (h_gap : Φ_q > (B * q : ℕ) ^ (q - 1)) :
    ∀ r s : Fin q, FW r = FW s := by
  -- Step 1: Get the factorization (in K q)
  obtain ⟨T, hT_int, hT_factor⟩ := h_factor

  -- Lift T to 𝓞 (K q)
  let T_int : 𝓞 (K q) := IsIntegralClosure.mk' (𝓞 (K q)) T hT_int
  have hT_coerce : (T_int : K q) = T := IsIntegralClosure.algebraMap_mk' _ _ _

  -- The factorization lifts to 𝓞 (K q) since 𝓞 K → K is injective
  have h_factor_int : balanceSumK_integral FW = fourSubThreeZeta_integral (q := q) * T_int := by
    -- Show the coercions to K q are equal
    have h_coerce_bal : (balanceSumK_integral FW : K q) = balanceSumK FW :=
      IsIntegralClosure.algebraMap_mk' _ _ _
    have h_coerce_four : (fourSubThreeZeta_integral (q := q) : K q) = fourSubThreeZeta :=
      IsIntegralClosure.algebraMap_mk' _ _ _
    -- Use injectivity of algebraMap : 𝓞 K → K (𝓞 K is a domain in K)
    apply IsFractionRing.injective (𝓞 (K q)) (K q)
    simp only [map_mul, h_coerce_bal, h_coerce_four, hT_coerce, hT_factor]

  -- Step 2: Compute norm of balanceSumK via multiplicativity in 𝓞 (K q)
  have h_norm_mul : Algebra.norm ℤ (balanceSumK_integral FW) =
      Algebra.norm ℤ (fourSubThreeZeta_integral (q := q)) * Algebra.norm ℤ T_int := by
    rw [h_factor_int, map_mul]

  -- Step 3: Bound on |N(balanceSumK)|
  have h_sum_bound : ∑ r : Fin q, FW r ≤ B * q := by
    calc ∑ r : Fin q, FW r
        ≤ ∑ _r : Fin q, B := Finset.sum_le_sum (fun r _ => h_bound r)
      _ = B * q := by simp [mul_comm]

  have h_norm_bound : (normBalanceSumK FW).natAbs ≤ (B * q) ^ (q - 1) := by
    calc (normBalanceSumK FW).natAbs
        ≤ (∑ r : Fin q, FW r) ^ (q - 1) := norm_balanceSumK_bound FW
      _ ≤ (B * q) ^ (q - 1) := Nat.pow_le_pow_left h_sum_bound (q - 1)

  -- Step 4: Gap argument
  -- |N(4-3ζ)| = Φ_q > (B*q)^{q-1} ≥ |N(balanceSumK)|
  -- From N(balanceSumK) = N(4-3ζ) * N(T), if N(T) ≠ 0 then
  -- |N(4-3ζ)| ≤ |N(balanceSumK)|, contradiction with gap
  -- So N(T) = 0, meaning T = 0, meaning balanceSumK = 0

  have h_balance_zero : balanceSumK (q := q) FW = 0 := by
    by_contra h_ne_zero
    -- From factorization: N(4-3ζ) | N(balanceSumK)
    have h_dvd : normFourSubThreeZeta (q := q) ∣ normBalanceSumK FW := by
      unfold normFourSubThreeZeta normBalanceSumK
      exact ⟨Algebra.norm ℤ T_int, h_norm_mul⟩
    -- |N(4-3ζ)| ≤ |N(balanceSumK)| since divisibility with nonzero quotient
    -- If balanceSumK ≠ 0, then N(balanceSumK) ≠ 0
    have h_Φ_le : Φ_q ≤ (normBalanceSumK FW).natAbs := by
      -- Abbreviations for clarity
      set a : ℤ := normFourSubThreeZeta (q := q) with ha_def
      set b : ℤ := normBalanceSumK FW with hb_def

      -- a ≠ 0 using norm = ± Φ_q and Φ_q > 0
      have ha_ne_zero : a ≠ 0 := by
        cases h_norm_eq with
        | inl h => rw [h]; exact ne_of_gt h_Φ_pos
        | inr h => rw [h]; exact neg_ne_zero.mpr (ne_of_gt h_Φ_pos)

      -- b ≠ 0: If b = 0, then balanceSumK = 0, contradicting h_ne_zero
      -- For 𝓞 K over ℤ: Algebra.norm ℤ x = 0 ↔ x = 0
      have hb_ne_zero : b ≠ 0 := by
        simp only [hb_def, normBalanceSumK]
        intro hb_zero
        apply h_ne_zero
        -- norm_eq_zero_iff: for x : 𝓞 K, Algebra.norm ℤ x = 0 ↔ x = 0
        have h_int_zero : balanceSumK_integral FW = 0 := Algebra.norm_eq_zero_iff.mp hb_zero
        -- Coerce to K q
        have h_coerce : (balanceSumK_integral FW : K q) = balanceSumK FW :=
          IsIntegralClosure.algebraMap_mk' _ _ _
        rw [← h_coerce, h_int_zero]
        rfl

      -- Unpack divisibility: b = a * c
      obtain ⟨c, hc_eq⟩ := h_dvd

      -- c ≠ 0 from a ≠ 0 and b ≠ 0
      have hc_ne_zero : c ≠ 0 := by
        intro hc0
        rw [hc0, mul_zero] at hc_eq
        exact hb_ne_zero hc_eq

      -- |b| = |a| * |c| via natAbs_mul
      have h_natAbs_mul : b.natAbs = a.natAbs * c.natAbs := by
        rw [hc_eq, Int.natAbs_mul]

      -- c ≠ 0 implies |c| ≥ 1
      have hc_ge_one : 1 ≤ c.natAbs := Int.natAbs_pos.mpr hc_ne_zero

      -- |a| ≤ |a| * |c| = |b|
      have h_abs_le : a.natAbs ≤ b.natAbs := by
        calc a.natAbs = a.natAbs * 1 := by ring
          _ ≤ a.natAbs * c.natAbs := Nat.mul_le_mul_left a.natAbs hc_ge_one
          _ = b.natAbs := h_natAbs_mul.symm

      -- |a| = Φ_q from h_norm_eq and Φ_q > 0
      have h_a_natAbs_eq : a.natAbs = Φ_q.natAbs := by
        cases h_norm_eq with
        | inl h => rw [h]
        | inr h => rw [h]; simp [Int.natAbs_neg]

      have h_Φ_natAbs : Φ_q.natAbs = Φ_q := Int.natAbs_of_nonneg (le_of_lt h_Φ_pos)

      -- Final: Φ_q = |a| ≤ |b| = (normBalanceSumK FW).natAbs
      calc (Φ_q : ℤ) = (Φ_q.natAbs : ℤ) := by rw [h_Φ_natAbs]
        _ = (a.natAbs : ℤ) := by rw [h_a_natAbs_eq]
        _ ≤ (b.natAbs : ℤ) := by exact_mod_cast h_abs_le
        _ = (normBalanceSumK FW).natAbs := by simp only [hb_def]
    -- But Φ_q > (B*q)^{q-1} ≥ |N(balanceSumK)|, contradiction
    have h_Φ_gt : Φ_q > (normBalanceSumK FW).natAbs := by
      have h_bound_int : (normBalanceSumK FW).natAbs ≤ (B * q) ^ (q - 1) := h_norm_bound
      calc (Φ_q : ℤ) > (B * q : ℕ) ^ (q - 1) := h_gap
        _ = ((B * q : ℕ) ^ (q - 1) : ℕ) := by norm_cast
        _ ≥ (normBalanceSumK FW).natAbs := by exact_mod_cast h_bound_int
    omega

  -- Step 5: balanceSumK = 0 with FW ∈ ℕ^q implies all FW equal
  -- Use the balance_zero_implies_FW_const characterization
  exact balance_zero_implies_FW_const FW h_balance_zero

end Collatz.IntegralityBridge
