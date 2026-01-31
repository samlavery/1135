/-
Copyright (c) 2024. All rights reserved.
Released under MIT license.
-/

import Collatz.Basic
import Collatz.PartI
import Collatz.TiltBalance
import Collatz.IntegralityBridge
import Collatz.GapConditionTheorem
import Collatz.«1135»
import Collatz.DiaconisShahhshahani
import Hammer
#check @Collatz.collatz_conjecture_odd_universal

example : True := by
  hammer

/-! ## Diaconis-Shahshahani No-Divergence Bridge

  The DS file (`Collatz.DiaconisShahhshahani`) proves `no_collatz_divergence`
  using its own `orbit_ds` definition. These definitions are identical to
  `Collatz.orbit_raw` / `Collatz.DriftLemma.orbit`:

    orbit_ds n₀ k = orbit_raw n₀ k    (both iterate T(n) = (3n+1)/2^ν)

  The bridge below connects the DS result to `¬DivergentOrbit n₀`. -/

/-- orbit_ds agrees with orbit_raw (both are (3n+1)/2^{v₂(3n+1)}). -/
private lemma orbit_ds_eq_orbit_raw (n₀ : ℕ) (k : ℕ) :
    orbit_ds n₀ k = Collatz.orbit_raw n₀ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [orbit_ds, Collatz.orbit_raw]
    show T_ds (orbit_ds n₀ k) = Collatz.syracuse_raw (Collatz.orbit_raw n₀ k)
    rw [ih]
    rfl

/-- **No Collatz orbit diverges** (orbit_raw version).

    Bridge from the Diaconis-Shahshahani argument to the project's
    `DivergentOrbit` definition. -/
theorem no_divergence_ds (n₀ : ℕ) (hn₀ : n₀ > 1) (hn₀_odd : Odd n₀) :
    ¬Collatz.DivergentOrbit n₀ := by
  intro hdiv
  -- Convert DivergentOrbit (orbit_raw > N) to orbit_ds ≥ B
  have h_div_ds : ∀ B : ℕ, ∃ m, orbit_ds n₀ m ≥ B := by
    intro B
    obtain ⟨t, ht⟩ := hdiv B
    exact ⟨t, by rw [orbit_ds_eq_orbit_raw]; omega⟩
  exact no_collatz_divergence n₀ hn₀ hn₀_odd h_div_ds
