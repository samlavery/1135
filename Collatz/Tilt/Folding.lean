/-
Copyright (c) 2024. All rights reserved.
Released under MIT license.
-/
import Collatz.Tilt.Core

/-!
# Tilt Folding - Re-exports from TiltBalance

This file re-exports folding-related definitions from TiltBalance.lean via Core.lean.
All definitions are accessed through the Profile alias.

## Main Definitions (from TiltBalance via Profile)

* `Profile.foldedWeight`: The q-folded weight W_r^{(q)} = Σ_{j ≡ r mod q} 2^{Δⱼ}
* `balance_at_prime`: The spectral condition Σᵣ W_r · ζʳ = 0
* `balance_at_all_primes`: Balance at all prime divisors of m

These definitions all come from `CriticalLineCycleProfile` in TiltBalance.lean.
The `Profile` type is an alias for `CriticalLineCycleProfile`.
-/

namespace Collatz.Tilt

-- All folding definitions are already available via Profile (= CriticalLineCycleProfile)
-- from TiltBalance.lean through the Core.lean import.

-- Users can access:
-- - Profile.foldedWeight
-- - balance_at_prime
-- - balance_at_all_primes

-- The foldedWeightsEqual predicate can be defined here if needed:

/-- When all folded weights at prime q are equal. -/
def Profile.foldedWeightsEqual {m : ℕ} (P : Profile m)
    (q : ℕ) (hq_dvd : q ∣ m) (hq_pos : 0 < q)
    (h_nonneg : ∀ j : Fin m, 0 ≤ P.Δ j) : Prop :=
  ∃ c : ℕ, ∀ r : Fin q, P.foldedWeight q hq_dvd hq_pos r h_nonneg = c

end Collatz.Tilt
