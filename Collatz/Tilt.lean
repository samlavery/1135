/-
Copyright (c) 2024. All rights reserved.
Released under MIT license.
-/
import Collatz.TiltBalance
import Collatz.Tilt.Core
import Collatz.Tilt.Folding
import Collatz.Tilt.Fourier
import Collatz.Tilt.Rigidity
import Collatz.Tilt.FiniteCases

/-!
# Tilt-Balance Subsystem

This module provides access to the tilt-balance rigidity machinery for the
Collatz conjecture. The main results are imported from TiltBalance.lean.

## Main Results

* `CriticalLineCycleProfile`: Division counts ν with νⱼ ≥ 1 and Σνⱼ = 2m
* `CriticalLineCycleProfile.Δ`: Deviations Δⱼ = Σᵢ<j (νᵢ - 2)
* `CriticalLineCycleProfile.weight`: Weights Wⱼ = 2^{Δⱼ}
* `CriticalLineCycleProfile.foldedWeight`: Folded weights W_r^{(q)} = Σ_{j≡r mod q} Wⱼ
* `balance_at_prime`: The spectral condition Σᵣ W_r · ζʳ = 0
* `tilt_balance_rigidity_prime`: For prime m, balance forces all Δ = 0
* `tilt_balance_rigidity_even`: For m = 2p (p odd prime), balance forces all Δ = 0
* `tilt_balance_rigidity_realizable`: For ANY m ≥ 2, realizable + balance → all Δ = 0
* `only_trivial_cycles`: The main result - realizable balanced profiles have n = 1

## Finite Case Verification

From FiniteCases.lean:
* `m3_binary_nontrivial_impossible`: No nontrivial binary profile for m=3
* `m4_binary_nontrivial_impossible`: No nontrivial binary profile for m=4
* `m5_binary_nontrivial_impossible`: No nontrivial binary profile for m=5
* `m6_binary_nontrivial_impossible`: No nontrivial binary profile for m=6
* `binary_tilt_forces_trivial`: General binary tilt lemma

## Fourier Rigidity

From Fourier.lean:
* `foldedWeights_equal_from_balance`: Balance at prime q → all folded weights equal

## Usage

```lean
import Collatz.Tilt

open Collatz

-- Access CriticalLineCycleProfile, Δ, weight, foldedWeight, balance_at_prime
-- Access tilt_balance_rigidity_prime, tilt_balance_rigidity_realizable
-- Access only_trivial_cycles
```
-/

namespace Collatz.Tilt

-- Re-export key definitions from TiltBalance for convenience
export CriticalLineCycleProfile (Δ weight foldedWeight increment waveSum isRealizable)

-- Re-export key rigidity theorems
-- Note: These are accessed via Collatz namespace directly after import

-- Re-export Fourier lemmas
export Fourier (foldedWeights_equal_from_balance foldedWeights_pairwise_equal_from_balance)

end Collatz.Tilt
