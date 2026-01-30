/-
Copyright (c) 2025. All rights reserved.
Released under MIT license.

# Collatz No-Divergence via Baker/LZ Complexity

This file documents the information-theoretic approach to Collatz no-divergence.

## The Approach (Sketch)

The argument proceeds by:
1. K_lz complexity is bounded along orbits (DPI axiom)
2. Bounded K implies bounded bits (incompressibility)
3. Bounded bits implies bounded orbit values
4. Therefore: no divergence

## Status

**REMOVED**: The orbit boundedness theorems were removed because proving
K_lz boundedness on orbits is EQUIVALENT to proving orbits don't diverge.
This makes the argument circular.

The DPI argument sketched above is heuristically sound but closing the
gap requires proving the core conjecture directly.

## What Remains

BakerNoDivergence.lean contains:
- Bit dynamics analysis (bits_increase_on_nu1, bits_decrease_on_nu_ge2)
- Complexity drift bounds (complexity_bounded_by_bits)
- The DPI axiom for orbit complexity (K_lz_orbit_DPI)

These are useful building blocks but do not close the proof.
-/

import Collatz.LZComplexity

namespace Collatz.Baker

/-!
## The Baker No-Divergence Proof Structure (Incomplete)

The intended proof structure:

```
K_lz_bounded_on_orbit(n₀)     divergence_requires_unbounded_complexity
           ↓                              ↓
    K bounded along orbit       bits → ∞ ⟹ K → ∞
           ↓                              ↓
    Contrapositive: bounded K ⟹ bounded bits
                    ↓
              bits bounded
                    ↓
        orbit n₀ m < 2^B for all m
                    ↓
             NO DIVERGENCE
```

**GAP**: Proving K_lz boundedness on orbits is equivalent to the conjecture.
-/

end Collatz.Baker
