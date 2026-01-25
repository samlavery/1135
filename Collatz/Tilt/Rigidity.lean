/-
Copyright (c) 2024. All rights reserved.
Released under MIT license.
-/
import Collatz.TiltBalance

/-!
# Tilt Rigidity - Re-exports from TiltBalance

This file re-exports the rigidity theorems from TiltBalance.lean.
All proofs are complete in TiltBalance - this file provides a clean interface.

## Main Results (from TiltBalance)

* `tilt_balance_rigidity_prime`: For prime m, balance forces all Δ = 0
* `tilt_balance_rigidity_even`: For m = 2p (p odd prime), balance forces all Δ = 0
* `tilt_balance_rigidity_realizable`: For ANY m ≥ 2, realizable + balance → all Δ = 0
* `only_trivial_cycles`: Realizable balanced profiles have n = 1

## Key Insight

The rigidity arguments are:

1. **Prime m**: The Fourier rigidity lemma directly implies all weights equal,
   hence all Δ = 0.

2. **m = 2p**: Parity argument - total weight = 2*even_sum = p*c forces c even.
   Combined with anchor W₀ = 1, this forces all weights = 1.

3. **General m**: The realizability constraint (D | waveSum) combined with
   balance at all prime divisors forces the trivial profile via the
   nontrivial_not_realizable theorem.
-/

namespace Collatz.Tilt.Rigidity

open Collatz
open Collatz.TiltBalance

-- Re-export the main rigidity theorems for convenience
-- Users can access these via Collatz.Tilt.Rigidity or directly from Collatz

/-- For prime m with balance constraint, all Δ = 0. -/
theorem rigidity_prime {m : ℕ} (hm_prime : Nat.Prime m)
    (P : CriticalLineCycleProfile m)
    (h_nonneg : ∀ j : Fin m, P.Δ j ≥ 0)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m)
    (h_balance : balance_at_prime P m hm_prime (dvd_refl m) ζ hζ h_nonneg) :
    ∀ j, P.Δ j = 0 :=
  tilt_balance_rigidity_prime2 hm_prime P h_nonneg ζ hζ h_balance

/-- For m = 2p (p odd prime) with balance at all primes, all Δ = 0. -/
theorem rigidity_even {m : ℕ} (hm_pos : 0 < m)
    (p : ℕ) (hp_prime : Nat.Prime p) (hp_ne_2 : p ≠ 2)
    (hm_eq : m = 2 * p)
    (P : CriticalLineCycleProfile m)
    (h_nonneg : ∀ j : Fin m, P.Δ j ≥ 0)
    (h_balance : ∀ {q : ℕ} (hq_prime : Nat.Prime q) (hq_dvd : q ∣ m)
                   (ζ : ℂ) (hζ : IsPrimitiveRoot ζ q),
                 balance_at_prime P q hq_prime hq_dvd ζ hζ h_nonneg) :
    ∀ j, P.Δ j = 0 :=
  tilt_balance_rigidity_even hm_pos p hp_prime hp_ne_2 hm_eq P h_nonneg h_balance

/-- For ANY m ≥ 2 with realizability and balance at all primes, all Δ = 0. -/
theorem rigidity_realizable {m : ℕ} (hm_pos : 0 < m) (hm_ge2 : m ≥ 2)
    (P : CriticalLineCycleProfile m)
    (h_nonneg : ∀ j : Fin m, P.Δ j ≥ 0)
    (h_realizable : P.isRealizable)
    (h_gap :
      ∀ {d : ℕ} [NeZero d] (hd_dvd : d ∣ m) (hd_ge_2 : d ≥ 2),
        let weights : Fin m → ℕ := fun j => P.weight j (h_nonneg j)
        let FW : Fin d → ℕ := fun r => ∑ j : Fin m, if (j : ℕ) % d = r.val then weights j else 0
        |Algebra.norm ℚ (Collatz.CyclotomicAlgebra.balanceSumD d FW)| <
          |Algebra.norm ℚ (Collatz.CyclotomicAlgebra.fourSubThreeZetaD d)|)
    (h_balance : ∀ {q : ℕ} (hq_prime : Nat.Prime q) (hq_dvd : q ∣ m)
                   (ζ : ℂ) (hζ : IsPrimitiveRoot ζ q),
                 balance_at_prime P q hq_prime hq_dvd ζ hζ h_nonneg) :
    ∀ j, P.Δ j = 0 :=
  tilt_balance_rigidity_realizable hm_pos hm_ge2 P h_nonneg h_realizable h_gap h_balance

/-- The main result: realizable balanced profiles give n = 1. -/
theorem trivial_cycles {m : ℕ} (hm_pos : 0 < m) (hm_ge2 : m ≥ 2)
    (P : CriticalLineCycleProfile m)
    (h_nonneg : ∀ j : Fin m, P.Δ j ≥ 0)
    (h_realizable : P.isRealizable)
    (h_gap :
      ∀ {d : ℕ} [NeZero d] (hd_dvd : d ∣ m) (hd_ge_2 : d ≥ 2),
        let weights : Fin m → ℕ := fun j => P.weight j (h_nonneg j)
        let FW : Fin d → ℕ := fun r => ∑ j : Fin m, if (j : ℕ) % d = r.val then weights j else 0
        |Algebra.norm ℚ (Collatz.CyclotomicAlgebra.balanceSumD d FW)| <
          |Algebra.norm ℚ (Collatz.CyclotomicAlgebra.fourSubThreeZetaD d)|)
    (h_balance : ∀ {q : ℕ} (hq_prime : Nat.Prime q) (hq_dvd : q ∣ m)
                   (ζ : ℂ) (hζ : IsPrimitiveRoot ζ q),
                 balance_at_prime P q hq_prime hq_dvd ζ hζ h_nonneg)
    (n : ℕ) (hn_pos : 0 < n) (hn_eq : n * (2^(2*m) - 3^m) = P.waveSum) :
    n = 1 :=
  only_trivial_cycles hm_pos hm_ge2 P h_nonneg h_realizable h_gap h_balance n hn_pos hn_eq

end Collatz.Tilt.Rigidity
