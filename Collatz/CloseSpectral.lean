/-
Copyright (c) 2024. All rights reserved.
Released under MIT license.

# Spectral Definitions for Cycle Analysis

## Key Insight

For cycles with mean ν ≈ log₂(3) ≈ 1.585 (from cycle equation):
- Almost all ν ∈ {1, 2}
- FW is concentrated on residues 1 and 2 (mod q for q ≥ 3)
- balance = FW(1)·ζ + FW(2)·ζ² ≠ 0 (since |FW(1)/FW(2)| ≈ 0.71 ≠ 1)

This means critical-line cycles violate the cyclotomic balance constraint.
See DirectCycleVariance.lean for the full argument.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace CloseSpectral

open scoped BigOperators
open Finset

/-- Sum of squared deviations from the mean. -/
def sumSqDev (q : ℕ) (FW : Fin q → ℕ) (μ : ℕ) : ℕ :=
  ∑ j : Fin q, (Int.natAbs ((FW j : ℤ) - μ))^2

end CloseSpectral
