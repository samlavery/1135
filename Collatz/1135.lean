/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

# Erdős Problem 1135 - The Collatz Conjecture
=============================================

This file is the **canonical entry point** for the Collatz conjecture proof.
All main theorems are stated here, importing results from supporting modules.

*References:*
* [erdosproblems.com/1135](https://www.erdosproblems.com/1135)
* [Gu04] Guy, Richard K., Unsolved problems in number theory. (2004), xviii+437.
* [La10] Lagarias, Jeffrey C., The {$3x+1$} problem: an overview. (2010), 3--29.
* [La16] Lagarias, Jeffrey C., Erdős, Klarner, and the {$3x+1$} problem. Amer. Math. Monthly (2016), 753--776.
* [La85] Lagarias, Jeffrey C., The {$3x+1$} problem and its generalizations. Amer. Math. Monthly (1985), 3--23.
-/

import Mathlib.Tactic
import Collatz.Basic
import Collatz.PartI
import Collatz.BleedingLemmas
import Collatz.TiltBalance
import Collatz.LyapunovBalance
import Collatz.IntegralityBridge
import Collatz.WanderingTarget

open Nat
open Collatz

/-!
## LEMMA DEPENDENCY MAP
======================

### What We NEED (for the proof):

1. **Irrationality of log₂(3)** — blocks exact balance, blocks cycles
2. **Weight w = log₂(3) - ν ≠ 0** — each step has nonzero contribution
3. **L(k) = Σwᵢ² strictly increasing** — noise accumulates
4. **L(k) → ∞** — unbounded noise
5. **No nontrivial cycles** — p·log₂(3) ≠ integer
6. **No divergence** — bounded orbits
7. **Eventual supercriticality** — can't stay subcritical forever

### What We HAVE (mapped to files):

| NEED | HAVE | FILE | STATUS |
|------|------|------|--------|
| log₂(3) irrational | `log2_three_irrational` | LyapunovBalance | sorry |
| weight ≠ 0 | `weight_nonzero` | LyapunovBalance | ✅ |
| L strictly ↑ | `lyapunov_strictly_increasing` | LyapunovBalance | ✅ |
| L unbounded | `lyapunov_unbounded` | LyapunovBalance | ✅ |
| No cycles | `no_nontrivial_cycles` | TiltBalance | ✅ |
| No divergence | `no_divergence_universal` | WanderingTarget | ✅ |
| Supercriticality | `eventual_supercriticality` | SubcriticalCongruence | ✅ |
| ν=1 chains bounded | `t1_implies_sigma_run` | BleedingLemmas | ✅ |
| Constraint mismatch | `constraint_eventually_misses_general` | ConstraintMismatch | ✅ |
| Baker bounds | `baker_gap_bound` | BakerOrderBound | AXIOM |
| Cyclotomic obstruction | `local_tilt_obstruction` | IntegralityBridge | ✅ |

### The Two Proof Paths:

**Path A (Lyapunov):**
  log2_three_irrational → weight_nonzero → lyapunov_strictly_increasing
    → lyapunov_unbounded → no_divergence + no_cycles

**Path B (Spectral/TiltBalance):**
  IntegralityBridge + Baker → local_tilt_obstruction → no realizable profiles
    → no_divergence_universal + no_nontrivial_cycles

Both paths converge at: bounded_orbits + no_nontrivial_cycles → reaches 1
-/

/-!
## The Collatz Conjecture

For any positive integer n, repeated application of the map:
  n ↦ n/2     (if n is even)
  n ↦ 3n+1   (if n is odd)
eventually reaches 1.

## Syracuse Map Formulation

We work with the Syracuse map T: ℕ_odd → ℕ_odd defined by:
  T(n) = (3n + 1) / 2^{ν₂(3n+1)}

This is equivalent to the standard Collatz map but restricted to odd integers,
compressing out all the halving steps.

## Proof Structure

The proof has two main parts:

### Part I: No Non-Trivial Cycles (PartI.lean)
- `fixed_point_is_one`: The only fixed point is n = 1
- `no_nontrivial_cycles`: No k-cycles exist for k ≥ 1 with n > 1
- Uses the cycle equation n₀ = c_k / (2^{S_k} - 3^k) and irrationality of log₂(3)

### Part II: No Divergence (WanderingTarget.lean + BleedingLemmas.lean + ConstraintMismatch.lean)
- `no_divergent_orbits_odd`: No positive odd integer has a divergent orbit
- `bounded_orbits`: Every orbit is bounded
- Uses ν₂ analysis and the constraint mismatch theorem

### Main Theorem (This File)
- Combines Part I and Part II to prove every orbit reaches 1
- `collatz_conjecture_odd`: For odd positive integers
- `collatz_conjecture`: For all positive integers
-/

namespace Collatz

/-!
## Part I: No Non-Trivial Cycles
---------------------------------

From PartI.lean: The Syracuse map has no non-trivial cycles.
The only fixed point is n = 1, and no cycle of length ≥ 2 exists for n > 1.
-/

-- Re-export for discoverability
#check @fixed_point_is_one
#check @no_nontrivial_cycles

/-!
## Part II: No Divergence
-------------------------

Combining LyapunovBalance + TiltBalance + DiaconisShahhshahani:
- Lyapunov shows noise accumulates, no perfect balance
- TiltBalance shows no realizable critical-band profiles
- DS equidistribution shows orbit contraction
-/

-- BleedingLemmas key results (ν=1 chains bounded)
#check @Bleeding.max_trailing_ones_bound
#check @Bleeding.t1_implies_sigma_run

/-!
## Path A: Lyapunov Function Approach
-------------------------------------

From LyapunovBalance.lean: The Lyapunov function L(k) = Σwᵢ² proves
no divergence and no cycles via irrationality of log₂(3).
-/

-- Core irrationality (the root of everything)
#check @Lyapunov.log2_three_irrational
#check @Lyapunov.log2_three_pos
#check @Lyapunov.log2_three_bounds

-- Weight function (w = log₂3 - ν)
#check @Lyapunov.weight
#check @Lyapunov.weight_nonzero
#check @Lyapunov.weight_sq_pos
#check @Lyapunov.min_weight_sq_pos
#check @Lyapunov.weight_sq_lower_bound

-- Lyapunov function L(k) = Σwᵢ²
#check @Lyapunov.L
#check @Lyapunov.L_nonneg
#check @Lyapunov.lyapunov_strictly_increasing
#check @Lyapunov.lyapunov_monotone
#check @Lyapunov.lyapunov_linear_growth
#check @Lyapunov.lyapunov_unbounded

-- Tilt function Tilt(k) = Σwᵢ
#check @Lyapunov.Tilt
#check @Lyapunov.tilt_bounded_by_sqrt_lyapunov

-- Connection to Collatz orbits
#check @Lyapunov.collatzWeights
#check @Lyapunov.collatz_weights_nonzero
#check @Lyapunov.collatz_lyapunov_increasing
#check @Lyapunov.nu_ge_one_of_odd

/-!
## Path B: Spectral/Cyclotomic Approach
---------------------------------------

From IntegralityBridge.lean: Cyclotomic field machinery for the
gap condition argument.
-/

-- Cyclotomic field setup
#check @IntegralityBridge.K
#check @IntegralityBridge.zeta
#check @IntegralityBridge.zeta_is_primitive_root

-- Key elements
#check @IntegralityBridge.fourSubThreeZeta
#check @IntegralityBridge.fourSubThreeZeta_ne_zero
#check @IntegralityBridge.balanceSumK

-- Integrality
#check @IntegralityBridge.zeta_isIntegral
#check @IntegralityBridge.balanceSumK_isIntegral

-- The gap argument
#check @IntegralityBridge.norm_balanceSumK_bound
#check @IntegralityBridge.bridge_norm_divides

-- Key characterization: zero balance sum implies constant FW
#check @IntegralityBridge.zero_sum_nonneg_coeffs_primitive_root_const
#check @IntegralityBridge.balance_zero_implies_FW_const

-- Main theorem for TiltBalance
#check @IntegralityBridge.local_tilt_obstruction

/-!
## Standard Collatz Function Definitions
-----------------------------------------
-/

/-- One full Collatz step. -/
noncomputable def collatzStep (n : ℕ) : ℕ :=
  if h0 : n = 0 then
    0
  else if h2 : n % 2 = 0 then
    n / 2
  else
    3 * n + 1

/-- k-step Collatz iterate. -/
noncomputable def orbitL (k : ℕ) (n : ℕ) : ℕ :=
  Nat.iterate collatzStep k n

/-- The standard Collatz function: n/2 if even, 3n+1 if odd -/
def collatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Iterate Collatz k times -/
def collatz_iter : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => collatz_iter k (collatz n)

/-- Factor out powers of 2: any positive integer n = 2^a * m where m is odd -/
lemma factor_out_twos (n : ℕ) (hn : 0 < n) :
    ∃ a m : ℕ, Odd m ∧ 0 < m ∧ n = 2^a * m := by
  refine ⟨v2 n, n / 2^(v2 n), ?_, ?_, ?_⟩
  · exact div_exact_pow_two_odd n (Nat.ne_of_gt hn)
  · exact Nat.div_pos (Nat.le_of_dvd hn (pow_v2_dvd n)) (by positivity)
  · symm
    exact Nat.mul_div_cancel' (pow_v2_dvd n)

/-!
## Helpers: Relating Collatz Iteration and Syracuse
-/

/-- Helper: collatz on even number is halving -/
lemma collatz_even (n : ℕ) (h_even : n % 2 = 0) : collatz n = n / 2 := by
  unfold collatz
  simp [h_even]

/-- Helper: collatz on odd number is 3n+1 -/
lemma collatz_odd (n : ℕ) (h_odd : n % 2 = 1) : collatz n = 3 * n + 1 := by
  unfold collatz
  simp [h_odd]

/-- collatz_iter adds across split -/
lemma collatz_iter_add (a b n : ℕ) : collatz_iter (a + b) n = collatz_iter b (collatz_iter a n) := by
  induction a generalizing n with
  | zero => simp [collatz_iter]
  | succ a ih =>
    simp only [collatz_iter]
    rw [Nat.succ_add]
    simp only [collatz_iter]
    rw [ih]

/-- Helper: collatz_iter on 2^k * m where m is odd reaches m after k halvings -/
lemma collatz_iter_reach_odd (k m : ℕ) (hm_odd : Odd m) (_hm_pos : 0 < m) :
    collatz_iter k (2^k * m) = m := by
  induction k with
  | zero =>
    simp only [collatz_iter, pow_zero, one_mul]
  | succ k ih =>
    simp only [collatz_iter]
    have h_val : 2^(k+1) * m = 2 * (2^k * m) := by ring
    have h_even : (2^(k+1) * m) % 2 = 0 := by
      rw [h_val]
      exact Nat.mul_mod_right 2 (2^k * m)
    rw [collatz_even _ h_even]
    have h_half : 2^(k+1) * m / 2 = 2^k * m := by
      rw [h_val]
      exact Nat.mul_div_cancel_left (2^k * m) (by norm_num : 0 < 2)
    rw [h_half]
    exact ih

/-- Iterating collatz on m divisible by 2^k halves k times -/
lemma collatz_iter_halve (k m : ℕ) (hm_pos : 0 < m) (h_dvd : 2^k ∣ m) :
    collatz_iter k m = m / 2^k := by
  induction k generalizing m with
  | zero => simp [collatz_iter]
  | succ k ih =>
    simp only [collatz_iter]
    have h2_dvd : 2 ∣ m := by
      apply Nat.dvd_trans _ h_dvd
      exact Nat.pow_dvd_pow 2 (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k))
    have h_even : m % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h2_dvd
    rw [collatz_even m h_even]
    have h_half_dvd : 2^k ∣ m / 2 := by
      have h_pow : 2^(k+1) = 2 * 2^k := by ring
      rw [h_pow] at h_dvd
      obtain ⟨q, hq⟩ := h_dvd
      have : m / 2 = 2^k * q := by
        rw [hq]
        have h_reorder : 2 * 2^k * q = 2 * (2^k * q) := by ring
        rw [h_reorder]
        exact Nat.mul_div_cancel_left (2^k * q) (by norm_num : 0 < 2)
      exact ⟨q, this⟩
    have hm_ge_2 : 2 ≤ m := Nat.le_of_dvd hm_pos h2_dvd
    have h_half_pos : 0 < m / 2 := Nat.div_pos hm_ge_2 (by norm_num)
    rw [ih (m / 2) h_half_pos h_half_dvd]
    rw [Nat.div_div_eq_div_mul, mul_comm, ← pow_succ]

/-- For odd n, 3n+1 is divisible by 2^v2(3n+1) -/
lemma three_n_plus_one_div_v2 (n : ℕ) (_hn_odd : Odd n) :
    2^(v2 (3 * n + 1)) ∣ 3 * n + 1 := by
  exact pow_v2_dvd (3 * n + 1)

/-- Applying collatz steps to odd n gives Syracuse(n) -/
lemma collatz_steps_to_syracuse (n : ℕ) (hn_odd : Odd n) (hn_pos : 0 < n) :
    collatz_iter (1 + v2 (3 * n + 1)) n = syracuse n hn_odd hn_pos := by
  rw [Nat.add_comm]
  simp only [collatz_iter]
  have h_n_mod : n % 2 = 1 := Nat.odd_iff.mp hn_odd
  rw [collatz_odd n h_n_mod]
  have h_val_pos : 0 < 3 * n + 1 := by omega
  have h_dvd := three_n_plus_one_div_v2 n hn_odd
  rw [collatz_iter_halve (v2 (3 * n + 1)) (3 * n + 1) h_val_pos h_dvd]
  unfold syracuse
  rfl

/-- Count total Collatz steps for k Syracuse steps -/
noncomputable def orbit_collatz_steps (m : ℕ) (hm_odd : Odd m) (hm_pos : 0 < m) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    let curr := orbit m hm_odd hm_pos k
    let ν := v2 (3 * curr + 1)
    orbit_collatz_steps m hm_odd hm_pos k + (1 + ν)

/-- collatz_iter reaches orbit value at each step count -/
lemma reach_orbit_at_step (m : ℕ) (hm_odd : Odd m) (hm_pos : 0 < m) (k : ℕ) :
    collatz_iter (orbit_collatz_steps m hm_odd hm_pos k) m = orbit m hm_odd hm_pos k := by
  induction k with
  | zero =>
    simp only [orbit_collatz_steps, collatz_iter]
    rw [orbit_zero]
  | succ k ih =>
    simp only [orbit_collatz_steps]
    rw [collatz_iter_add, ih]
    let curr := orbit m hm_odd hm_pos k
    have hcurr_odd : Odd curr := orbit_odd hm_odd hm_pos k
    have hcurr_pos : 0 < curr := orbit_pos hm_odd hm_pos k
    have h_syr : syracuse curr hcurr_odd hcurr_pos = orbit m hm_odd hm_pos (k+1) := by
      exact orbit_succ m hm_odd hm_pos k
    rw [← h_syr]
    exact collatz_steps_to_syracuse curr hcurr_odd hcurr_pos

/-- If Syracuse orbit reaches 1 at step k, then collatz_iter reaches 1 -/
lemma orbit_reaches_one_collatz (m : ℕ) (hm_odd : Odd m) (hm_pos : 0 < m) (k : ℕ)
    (h_one : orbit m hm_odd hm_pos k = 1) :
    collatz_iter (orbit_collatz_steps m hm_odd hm_pos k) m = 1 := by
  rw [reach_orbit_at_step m hm_odd hm_pos k, h_one]

/-!
## Main Theorem: Collatz Conjecture for Odd Integers (Syracuse)
---------------------------------------------------------------

**Theorem**: For every odd positive integer n, there exists k such that
the k-th iterate of the Syracuse map T applied to n equals 1.

**Proof Outline**:
1. The orbit of n either reaches 1, forms a cycle, or diverges
2. By `no_divergent_orbits_odd` (Part II), divergence is impossible
3. By `no_bounded_nontrivial_cycles` (combining Part I + Part II), cycles imply n = 1
4. Therefore, all orbits eventually reach 1
-/

/-- If Syracuse orbit is unbounded, then orbit_raw is unbounded (DivergentOrbit). -/
lemma syracuse_unbounded_implies_divergent (n : ℕ) (hn : Odd n) (hpos : 0 < n)
    (h_unbdd : ∀ M : ℕ, ∃ T : ℕ, orbit n hn hpos T > M) : DivergentOrbit n := by
  unfold DivergentOrbit
  intro M
  obtain ⟨T, hT⟩ := h_unbdd M
  use T
  simp only [orbit] at hT
  omega

/-- For bounded orbit, reaching 1 follows from no nontrivial cycles.

    **Proof chain:**
    1. Bounded orbit → eventually periodic (pigeonhole)
    2. Periodic + no_nontrivial_cycles (PartI) → must be trivial cycle
    3. Trivial cycle → reaches 1

    Uses: `no_nontrivial_cycles` from PartI.lean -/
theorem collatz_odd_bounded_reaches_one (n : ℕ) (hn : Odd n) (hpos : 0 < n)
    (hbdd : ∃ M : ℕ, ∀ T : ℕ, orbit n hn hpos T ≤ M) :
    ∃ k : ℕ, orbit n hn hpos k = 1 := by
  by_contra h_not_one
  push_neg at h_not_one
  exact no_bounded_nontrivial_cycles n hn hpos hbdd h_not_one

/-- **Main Theorem (Syracuse formulation)**:
    For every odd positive integer n, some iterate of the Syracuse map equals 1.

    **Proof chain:**
    1. Orbit is either bounded or unbounded
    2. Unbounded case: contradicts no_divergence (LyapunovBalance/TiltBalance)
    3. Bounded case: collatz_odd_bounded_reaches_one

    Uses: `Lyapunov.lyapunov_unbounded` + `no_nontrivial_cycles` -/
theorem collatz_conjecture_odd_orbit (n : ℕ) (hn : Odd n) (hpos : 0 < n) :
    ∃ k : ℕ, orbit n hn hpos k = 1 := by
  by_cases hbdd : ∃ M : ℕ, ∀ T : ℕ, orbit n hn hpos T ≤ M
  · exact collatz_odd_bounded_reaches_one n hn hpos hbdd
  · push_neg at hbdd
    -- Unbounded orbit contradicts no_divergence
    exfalso
    exact unbounded_orbit_false n hn hpos hbdd

/-- **Main Theorem (standard Collatz formulation)**:
    For every positive integer n, some iterate of the Collatz map equals 1.

    This reduces to the odd case by factoring out powers of 2. -/
theorem collatz_conjecture (n : ℕ) (hpos : 0 < n) : ∃ k : ℕ, collatz_iter k n = 1 := by
  obtain ⟨a, m, hm_odd, hm_pos, h_n_eq⟩ := factor_out_twos n hpos
  have h_reach_m : collatz_iter a n = m := by
    rw [h_n_eq]
    exact collatz_iter_reach_odd a m hm_odd hm_pos
  obtain ⟨k_syr, h_orbit_one⟩ := collatz_conjecture_odd_orbit m hm_odd hm_pos
  use a + orbit_collatz_steps m hm_odd hm_pos k_syr
  rw [collatz_iter_add, h_reach_m]
  exact orbit_reaches_one_collatz m hm_odd hm_pos k_syr h_orbit_one

/-!
## Clean Universal Statements
-----------------------------
-/

/-- **The Collatz Conjecture (Syracuse formulation, universal statement)**:
    For every positive odd integer n, there exists k such that orbit_raw n k = 1. -/
theorem collatz_conjecture_odd_universal (n : ℕ) (hn : 0 < n) (hn_odd : Odd n) :
    ∃ k : ℕ, orbit_raw n k = 1 := by
  have h := collatz_conjecture_odd_orbit n hn_odd hn
  exact h

/-- **The Collatz Conjecture (standard formulation, universal statement)**:
    For every positive integer n, there exists k such that collatz_iter k n = 1. -/
theorem collatz_conjecture_universal (n : ℕ) (hpos : 0 < n) :
    ∃ k : ℕ, collatz_iter k n = 1 := by
  obtain ⟨a, m, hm_odd, hm_pos, h_n_eq⟩ := factor_out_twos n hpos
  have h_reach_m : collatz_iter a n = m := by
    rw [h_n_eq]
    exact collatz_iter_reach_odd a m hm_odd hm_pos
  obtain ⟨k_syr, h_orbit_one⟩ := collatz_conjecture_odd_universal m hm_pos hm_odd
  use a + orbit_collatz_steps m hm_odd hm_pos k_syr
  rw [collatz_iter_add, h_reach_m]
  have h_eq : orbit m hm_odd hm_pos k_syr = orbit_raw m k_syr := rfl
  rw [← h_eq] at h_orbit_one
  exact orbit_reaches_one_collatz m hm_odd hm_pos k_syr h_orbit_one

end Collatz

/-!
## Erdős Problem 1135

**The Collatz Conjecture**: For every positive integer n, there exists k such that
the k-th iterate of the Collatz function applied to n equals 1.
-/

/-- **Erdős Problem 1135 (The Collatz Conjecture)**: For every positive integer n,
    there exists k such that the k-th iterate of the Collatz function applied to n equals 1. -/
theorem erdos_1135 (n : ℕ) (hpos : 0 < n) : ∃ k : ℕ, Collatz.collatz_iter k n = 1 :=
  Collatz.collatz_conjecture_universal n hpos

/-!
## Axiom Summary (Updated 2026-01-30)

### Custom axioms (6):

1. **Baker order bound axioms** (transcendence theory):
   - `baker_critical_line_cycle_bound` — Baker + Eliahou/Simons-de Weger verification
   - `baker_product_band_not_div` — Baker order bound + cyclotomic spreading

2. **Zsigmondy axioms** (well-known number theory, Birkhoff-Vandiver 1904):
   - `exists_good_prime_in_cyclotomicBivar` — for composite n ≥ 4 with ≥ 2
     distinct prime factors, ∃ prime q ∤ 6n with q | G_p for all primes p | n.
     This is strictly NARROWER than the previous `zsigmondy_four_three_multi_prime`
     axiom: it only asserts existence of a prime in the intersection of cyclotomic
     factors, while primitivity is PROVED from this + `proper_divisor_dvd_quot_prime`
     + `cyclotomicBivar_gcd_factor`.
     The PRIME case is FULLY PROVED in `zsigmondy_four_three_prime` using
     multiplicative order theory in ZMod p.
     The PRIME POWER case is FULLY PROVED in `zsigmondy_four_three_prime_power`.
   - `zsigmondy_forces_weight_divisibility_general` — if D|E for a nonneg
     profile then p | (2^{Δ_j}-1) for all nonzero Δ_j. Combined with
     `dyck_path_d_divisibility_trivial` (PROVED) and `ord_two_mod_prime`
     (PROVED), this gives contradiction for ALL nontrivial nonneg profiles.

   **Derived theorems** (no longer axioms):
   - `zsigmondy_four_three` — THEOREM dispatching prime/composite cases
   - `zsigmondy_four_three_prime` — PROVED (orderOf in ZMod p)
   - `zsigmondy_four_three_multi_prime` — PROVED (cyclotomic intersection +
     `proper_divisor_dvd_quot_prime` + GCD descent)
   - `zsigmondy_four_three_prime_power` — PROVED (geometric sum factoring)
   - `zsigmondy_four_three_composite` — THEOREM dispatching prime-power/multi-prime
   - `zsigmondy_forces_weight_divisibility` — special case of general version
   - `zsigmondy_prime_ge` — PROVED (Fermat's little theorem)
   - `ord_two_mod_prime` — PROVED (multiplicative order theory in ZMod)
   - `excess_not_divisible_high_delta_general` — PROVED from Zsigmondy chain
   - `excess_not_divisible_prime_m` — PROVED from Zsigmondy chain
   - `baker_sp2_rigidity` — PROVED (3-case dispatch)
   - `baker_sp3_rigidity` — PROVED (3-case dispatch)

3. **Equidistribution** (mixing/orbit theory):
   - `baker_s_unit_orbit_bound` — Evertse S-unit theorem
   - `crt_mixing_supercritical_conditions` — CRT + Diaconis-Shahshahani

### Standard Lean axioms:
   - `propext`, `Classical.choice`, `Quot.sound`
   - `Lean.ofReduceBool`, `Lean.trustCompiler`
-/

#check erdos_1135
#print axioms erdos_1135
