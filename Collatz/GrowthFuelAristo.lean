/-
Proven Growth-Fuel theorems from Aristotle (uuid: 0f4b3a0c-66fa-4f11-8d08-638eb22d9ad5)

Key results from the GrowthFuel module:
- fundamental_orbit_formula: orbit n t * 2^(nuSum n t) = 3^t * n + waveSum n t
- supercritical_inequality: 5*S >= 8*t implies 2^S > 3^t
- odd_orbit: orbits of odd n stay odd
-/
import Collatz.Case3KComplexity

namespace Collatz.Case3K.GrowthFuel

open scoped BigOperators

/-! ## Wave Sum Definition -/

/-- Wave sum recurrence: c_0 = 0, c_{t+1} = 3*c_t + 2^{S_t} -/
def waveSum (n₀ : ℕ) : ℕ → ℕ
| 0 => 0
| t + 1 => 3 * waveSum n₀ t + 2^(νSum n₀ t)

/-! ## Fundamental Orbit Formula

This is the key algebraic identity: orbit(n, t) * 2^S_t = 3^t * n + c_t
Proven by Aristotle via induction on t.
-/

/-- The Fundamental Orbit Formula: orbit(n, t) * 2^{νSum(n, t)} = 3^t * n + waveSum(n, t).
    Proven by Aristotle (uuid: 0f4b3a0c-66fa-4f11-8d08-638eb22d9ad5).
    Key insight: T(x) * 2^ν = 3*x + 1, so induction gives the full formula. -/
theorem fundamental_orbit_formula (n₀ : ℕ) (t : ℕ) (hn₀ : n₀ % 2 = 1) :
    orbit n₀ t * 2^(νSum n₀ t) = 3^t * n₀ + waveSum n₀ t := by
  induction t with
  | zero =>
    simp only [orbit, νSum, waveSum, Finset.range_zero, Finset.sum_empty, pow_zero, mul_one,
      one_mul, add_zero]
  | succ t ih =>
    have h_orbit_odd : (orbit n₀ t) % 2 = 1 := orbit_odd n₀ t hn₀
    have h_T_def : T (orbit n₀ t) * 2^(ν (orbit n₀ t)) = 3 * (orbit n₀ t) + 1 := by
      simp only [T, if_neg (by omega : ¬ (orbit n₀ t) % 2 = 0)]
      have h_dvd : 2^(ν (orbit n₀ t)) ∣ 3 * (orbit n₀ t) + 1 := by
        simp only [ν, if_neg (by omega : ¬ (orbit n₀ t) % 2 = 0)]
        exact pow_padicValNat_dvd
      exact Nat.div_mul_cancel h_dvd
    have h_νSum_succ : νSum n₀ (t + 1) = νSum n₀ t + ν (orbit n₀ t) := by
      simp only [νSum, Finset.range_add_one, Finset.sum_insert Finset.notMem_range_self]
      ring
    have h_waveSum_succ : waveSum n₀ (t + 1) = 3 * waveSum n₀ t + 2^(νSum n₀ t) := rfl
    calc orbit n₀ (t + 1) * 2^(νSum n₀ (t + 1))
        = T (orbit n₀ t) * 2^(νSum n₀ t + ν (orbit n₀ t)) := by simp [orbit, h_νSum_succ]
      _ = T (orbit n₀ t) * (2^(νSum n₀ t) * 2^(ν (orbit n₀ t))) := by rw [pow_add]
      _ = T (orbit n₀ t) * 2^(ν (orbit n₀ t)) * 2^(νSum n₀ t) := by ring
      _ = (3 * (orbit n₀ t) + 1) * 2^(νSum n₀ t) := by rw [h_T_def]
      _ = 3 * (orbit n₀ t * 2^(νSum n₀ t)) + 2^(νSum n₀ t) := by ring
      _ = 3 * (3^t * n₀ + waveSum n₀ t) + 2^(νSum n₀ t) := by rw [ih]
      _ = 3^(t + 1) * n₀ + (3 * waveSum n₀ t + 2^(νSum n₀ t)) := by ring
      _ = 3^(t + 1) * n₀ + waveSum n₀ (t + 1) := by rw [h_waveSum_succ]

/-! ## Supercritical Inequality -/

/-- Helper: 2^8 > 3^5 -/
private lemma two_pow_8_gt_three_pow_5 : (2 : ℕ)^8 > 3^5 := by native_decide

/-- Supercritical inequality: 5*S >= 8*t implies 2^S > 3^t (for t >= 1).
    This is the key exponential bound showing that supercritical orbits contract. -/
theorem supercritical_inequality (n₀ t : ℕ) (h_sup : 5 * νSum n₀ t ≥ 8 * t) (ht : t ≥ 1) :
    2^(νSum n₀ t) > 3^t := by
  by_contra h_not
  push_neg at h_not
  have h1 : (2 : ℕ)^(5 * νSum n₀ t) ≤ 3^(5 * t) := by
    calc 2^(5 * νSum n₀ t) = (2^(νSum n₀ t))^5 := by rw [mul_comm, pow_mul]
      _ ≤ (3^t)^5 := Nat.pow_le_pow_left h_not 5
      _ = 3^(5 * t) := by rw [mul_comm, pow_mul]
  have h2 : (2 : ℕ)^(8 * t) > 3^(5 * t) := by
    have eq1 : (2 : ℕ)^(8 * t) = (2^8)^t := Nat.pow_mul 2 8 t
    have eq2 : (3 : ℕ)^(5 * t) = (3^5)^t := Nat.pow_mul 3 5 t
    rw [eq1, eq2]
    exact Nat.pow_lt_pow_left two_pow_8_gt_three_pow_5 (by omega : t ≠ 0)
  have h3 : (2 : ℕ)^(5 * νSum n₀ t) ≥ 2^(8 * t) := Nat.pow_le_pow_right (by omega) h_sup
  omega

/-! ## Orbit Division Form -/

/-- From fundamental formula: orbit = (3^t * n + waveSum) / 2^S -/
theorem orbit_eq_div (n₀ t : ℕ) (hn₀ : n₀ % 2 = 1) :
    orbit n₀ t = (3^t * n₀ + waveSum n₀ t) / 2^(νSum n₀ t) := by
  have h := fundamental_orbit_formula n₀ t hn₀
  have h_pos : 0 < 2^(νSum n₀ t) := Nat.two_pow_pos _
  rw [← h]
  exact (Nat.mul_div_cancel _ h_pos).symm

/-! ## WaveSum Bound -/

/-- The gap function: gap(t) = (n+1) * 2^S - (waveSum + 3^t * n).
    For the waveSum bound to hold, we need gap(t) ≥ 0 for all t. -/
def waveSumGap (n₀ : ℕ) (t : ℕ) : ℤ :=
  (n₀ + 1) * 2^(νSum n₀ t) - (waveSum n₀ t + 3^t * n₀)

/-- The gap at t=0 equals 1. -/
lemma waveSumGap_zero (n₀ : ℕ) : waveSumGap n₀ 0 = 1 := by
  simp only [waveSumGap, νSum, waveSum, Finset.range_zero, Finset.sum_empty, pow_zero,
    mul_one, one_mul]
  ring

-- DELETED: waveSum_bound_supercritical, supercritical_orbit_bound_formula
-- These depended on sorry-based supercritical_orbit_bound_t_ge3 from Case3KComplexity.lean.
-- The main proof path uses no_divergence_via_supercriticality instead.

end Collatz.Case3K.GrowthFuel
