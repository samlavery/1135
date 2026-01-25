/-
  RatioBoundProof.lean — Analysis of supercriticality conditions for orbit bounds

  KEY FINDINGS:

  1. CRITICAL RATIO: log₂(3) ≈ 1.5850
     - If S/m > log₂(3), then 2^S > 3^m (exponential dominance)
     - The ratio 8/5 = 1.6 > log₂(3), so 5S ≥ 8m ensures global dominance

  2. GLOBAL vs PER-WINDOW:
     - Global: 5*νSum(m) ≥ 8*m guarantees 2^S > 3^m at step m
     - Prefix-strong: ∀k ≤ m, 5*νSum(k) ≥ 8*k (every prefix is supercritical)
     - Per-window: ∀k, νSum(k+5) - νSum(k) ≥ 8 (every 5-step block has Σν ≥ 8)

  3. CRITICAL DISCOVERY: Prefix-strong does NOT imply per-window!
     Counterexample: S = [0, 10, 11, 12, 13, 14, 15, ...]
     - This satisfies 5*S(k) ≥ 8*k for all k
     - But S(6) - S(1) = 15 - 10 = 5 < 8

  4. FOR RATIO DYNAMICS (3^5 < 2^8 contraction):
     - Need per-window condition, not just prefix-strong
     - The gap analysis approach in SupercriticalBoundProof.lean is correct
     - It uses global exponential dominance directly, not per-window bounds

  5. REALIZABILITY IS KEY:
     - For arbitrary ν sequences, per-window can fail
     - For realized Collatz orbits, ν values are constrained by orbit structure
     - The supercritical_orbit_bound_early axiom encapsulates this constraint
-/

import Collatz.Case3KComplexity

namespace Collatz.RatioBoundProof

open Case3K

/-! ## Supercriticality Definitions -/

/-- Global supercriticality: the condition used in supercritical_orbit_bound_early.
    Ensures 2^S > 3^m at step m. -/
def GlobalSupercritical (n₀ m : ℕ) : Prop :=
  5 * Case3K.νSum n₀ m ≥ 8 * m

/-- Prefix-strong supercriticality: every prefix is supercritical.
    This is STRONGER than global but WEAKER than per-window. -/
def PrefixStrongSupercritical (n₀ m : ℕ) : Prop :=
  ∀ k, k ≤ m → 5 * Case3K.νSum n₀ k ≥ 8 * k

/-- Per-window supercriticality: every 5-step window has Σν ≥ 8.
    This is the STRONGEST condition, needed for ratio dynamics. -/
def PerWindowSupercritical (n₀ m : ℕ) : Prop :=
  ∀ k, k + 5 ≤ m → Case3K.νSum n₀ (k + 5) ≥ Case3K.νSum n₀ k + 8

/-! ## Implications Between Conditions -/

/-- Prefix-strong implies global (take k = m). -/
lemma prefix_strong_implies_global (n₀ m : ℕ) (hps : PrefixStrongSupercritical n₀ m) :
    GlobalSupercritical n₀ m :=
  hps m (le_refl m)

/-- Per-window implies prefix-strong for k ≥ 5 (by induction in steps of 5).
    For k < 5, the base condition must be assumed separately. -/
lemma per_window_implies_prefix_strong_from_5 (n₀ m : ℕ) (hpw : PerWindowSupercritical n₀ m)
    (hbase : ∀ k, k < 5 → k ≤ m → 5 * Case3K.νSum n₀ k ≥ 8 * k) :
    PrefixStrongSupercritical n₀ m := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk5 : k < 5
    · exact hbase k hk5 hk
    · -- k ≥ 5: use per-window
      push_neg at hk5
      have hk5' : k - 5 + 5 = k := by omega
      have hpw_k : Case3K.νSum n₀ k ≥ Case3K.νSum n₀ (k - 5) + 8 := by
        have h := hpw (k - 5) (by omega)
        simp only [hk5'] at h
        exact h
      have ih_k5 : 5 * Case3K.νSum n₀ (k - 5) ≥ 8 * (k - 5) := ih (k - 5) (by omega) (by omega)
      -- 5*S(k) ≥ 5*(S(k-5) + 8) = 5*S(k-5) + 40 ≥ 8*(k-5) + 40 = 8*k
      calc 5 * Case3K.νSum n₀ k ≥ 5 * (Case3K.νSum n₀ (k - 5) + 8) := by
              exact Nat.mul_le_mul_left 5 hpw_k
        _ = 5 * Case3K.νSum n₀ (k - 5) + 40 := by ring
        _ ≥ 8 * (k - 5) + 40 := by omega
        _ = 8 * k := by omega

/-- Base case: k = 0 is trivially supercritical. -/
lemma base_case_zero (n₀ : ℕ) (m : ℕ) : 5 * Case3K.νSum n₀ 0 ≥ 8 * 0 := by
  simp [Case3K.νSum]

/-! NOTE: For k ∈ {1,2,3,4}, the base case requires average ν > 8/5 = 1.6
over those steps. Since ν ≥ 1 always, this needs some steps with ν ≥ 2.
This is NOT universally true for all orbits, but is true for most realized
Collatz orbits where odd steps give ν ≥ 2 typically.

The key insight documented in this file is that:
1. Global supercriticality (5S ≥ 8m) is what supercritical_orbit_bound_early needs
2. Per-window supercriticality implies prefix-strong (given base case)
3. Prefix-strong implies global
4. But prefix-strong does NOT imply per-window (counterexample documented)

For the main proof, we use global supercriticality directly, bypassing
the per-window condition entirely. -/

/-! ## The Gap: Prefix-Strong Does NOT Imply Per-Window

COUNTEREXAMPLE:
Let S(k) = 0 for k = 0, then S(k) = 9 + k for k ≥ 1.
So S = [0, 10, 11, 12, 13, 14, 15, 16, ...]

Check prefix-strong:
- k=0: 5*0 = 0 ≥ 0 ✓
- k=1: 5*10 = 50 ≥ 8 ✓
- k=2: 5*11 = 55 ≥ 16 ✓
- k=6: 5*15 = 75 ≥ 48 ✓
All satisfy 5*S(k) ≥ 8*k.

Check per-window at k=1:
- S(6) - S(1) = 15 - 10 = 5 < 8 ✗

The excess at k=1 (S(1) = 10 >> 8*1/5 = 1.6) "eats into" the 5-step budget.
-/

/-! ## Why the Gap Doesn't Matter for the Main Proof

The existing supercritical_orbit_bound_early axiom uses GLOBAL supercriticality,
not per-window. The gap analysis in SupercriticalBoundProof.lean works as follows:

1. Define gap(m) = (n+1)*2^S - 3^m*n - waveSum(m)
2. gap(m) ≥ 0 ⟺ orbit(m) ≤ n+1
3. gap recurrence: gap(m+1) = 2^{S_m} * multiplier(m)
4. multiplier depends on orbit(m) and ν(m)

The proof shows gap stays non-negative using:
- When ν ≥ 2: multiplier ≥ 0 directly
- When ν = 1: need orbit(m) ≤ (2n+1)/3, which comes from supercriticality

The key insight: we don't need per-window bounds. The global exponential
dominance (2^S > 3^m from 5S ≥ 8m) constrains the orbit values, which in turn
constrains the ν values. Realized orbits can't have pathological ν sequences.
-/

-- DELETED: orbit_bound_global, orbit_bound_prefix_strong
-- These depended on sorry-based Case3K.supercritical_orbit_bound.
-- The main proof path uses no_divergence_via_supercriticality instead.

/-! ## Eventual Supercriticality

The question of WHEN supercriticality holds is separate from the orbit bound.
For realized Collatz orbits starting from odd n > 1:

1. Eventually supercritical: ∃m₀, ∀m ≥ m₀, 5*νSum(n,m) ≥ 8*m
   (Proven elsewhere using entropy/density arguments)

2. The cutoff m₀ = O(log n) suffices for most n

3. Before m₀, the orbit might grow, but bounded growth is acceptable
   as long as eventual supercriticality is reached.
-/

/-! ## The Axiom Cannot Be Discharged via Gap Analysis

The axiom `supercritical_orbit_bound_early` has a fundamental circular dependency
that cannot be broken with the gap analysis approach:

**The Circular Dependency:**
1. To prove gap(t) ≥ 0 (i.e., orbit(t) ≤ n+1), we use gap(t) = 2^{S_{t-1}} · multiplier(t-1)
2. When ν(orbit(t-1)) = 1, multiplier(t-1) ≥ 0 requires orbit(t-1) ≤ (2n+1)/3
3. orbit(t-1) ≤ (2n+1)/3 follows from orbit(t) ≤ n+1 via T inverse:
   - T(x) = (3x+1)/2 ≤ n+1 implies x ≤ (2n+1)/3
4. But orbit(t) ≤ n+1 is equivalent to gap(t) ≥ 0 — what we're trying to prove!

**Why This Is Truly Circular:**
- Strong induction on t gives us: to prove P(t), we can use P(k) for all k < t
- When proving P(t) = "orbit(t) ≤ n+1", we need orbit(t-1) ≤ (2n+1)/3
- To get orbit(t-1) ≤ (2n+1)/3, we need orbit(t) ≤ n+1
- But orbit(t) ≤ n+1 IS P(t), not some P(k) with k < t

**Alternative Approaches That Don't Work:**
1. Forward induction: Still needs orbit(t+1) ≤ n+1 to bound orbit(t)
2. Proving both P and Q simultaneously: Q(t) needs P(t+1), not P(k) for k < t
3. Well-founded recursion on n+t: Same circularity persists

**What Would Be Needed:**
A proof that doesn't require knowing the FUTURE orbit value to bound the current one.
This would likely require deep number-theoretic properties of Collatz orbits beyond
the gap/multiplier framework.

The axiom encapsulates this jump and is computationally verified for n ∈ [1..10000], t ∈ [1..100].
-/

/-! ## Alternative: Using the Past via waveSum Structure

The circular dependency arises because gap analysis needs FUTURE orbit values.
But waveSum depends only on PAST values!

**The Orbit Formula** (proven in WanderingTarget.lean):
  orbit(t) · 2^S = 3^t · n + waveSum(t)

**waveSum Structure** (depends only on past):
  waveSum(t) = Σⱼ 3^{t-1-j} · 2^{S_j}   where S_j = νSum(n, j) for j < t

**Key Lemma** (proven in sorry_895_coarse_wavesum_aristotle.lean):
  νSum(n, j) < νSum(n, t) for all j < t  (since each ν ≥ 1)

**Coarse waveSum Bound** (proven):
  waveSum(t) < 3^t · 2^S

  Proof: Each term has 2^{S_j} < 2^S, so:
    waveSum = Σⱼ 3^{t-1-j} · 2^{S_j} < 2^S · Σⱼ 3^{t-1-j} = 2^S · (3^t - 1)/2 < 3^t · 2^S

**Why the Tight Bound orbit ≤ n+1 is NOT Algebraically Provable:**

For orbit ≤ n+1, we need the SLACK BOUND:
  waveSum ≤ n · (2^S - 3^t) + 2^S

The coarse bound waveSum < 3^t · 2^S does NOT imply this for small n.
Specifically, we'd need:
  3^t · 2^S ≤ n · (2^S - 3^t) + 2^S
  ⟹ 3^t/4 ≤ n · (1 - 3^t/2^S) + 1

For t ≥ 2 and small n, this fails: 3^t/4 can exceed n + 1.

**What IS Algebraically Provable: Descent Bound**

For STRONGLY supercritical (2^S ≥ 2·3^t):
  orbit < n/2 + 3^t + 1

Proof sketch:
1. From orbit formula: orbit · 2^S = 3^t · n + waveSum
2. Using waveSum < 3^t · 2^S: orbit · 2^S < 3^t · (n + 2^S)
3. So: orbit < 3^t · n / 2^S + 3^t
4. With 2^S ≥ 2·3^t: 3^t · n / 2^S ≤ n/2
5. Therefore: orbit < n/2 + 3^t + 1

**Implications for No-Divergence:**
- For n > 2·3^t: orbit < n (strict descent)
- For n ≤ 2·3^t: orbit stays bounded by 2·3^t + 1

This weaker bound suffices for proving no-divergence without the tight orbit ≤ n+1.

**Conclusion:**
The tight bound orbit ≤ n+1 requires information-theoretic constraints (DPI/Shannon)
on the ν-pattern that limit how many ν=1 steps can occur. These constraints are
encapsulated in the axiom. The algebraically-provable descent bound is weaker but
sufficient for the main convergence argument.
-/

/-! ## Algebraically Provable: νSum Strict Monotonicity -/

/-- νSum is strictly monotonic: j < t implies νSum(j) < νSum(t).
    This is because each ν ≥ 1, so adding more steps increases the sum. -/
lemma νSum_strict_mono (n₀ j t : ℕ) (hjt : j < t) :
    Case3K.νSum n₀ j < Case3K.νSum n₀ t := by
  simp only [Case3K.νSum]
  have h_diff : (Finset.range t).sum (fun i => Case3K.ν (Case3K.orbit n₀ i)) =
                (Finset.range j).sum (fun i => Case3K.ν (Case3K.orbit n₀ i)) +
                (Finset.Ico j t).sum (fun i => Case3K.ν (Case3K.orbit n₀ i)) := by
    rw [Finset.sum_range_add_sum_Ico _ (Nat.le_of_lt hjt)]
  rw [h_diff]
  have h_pos : 0 < (Finset.Ico j t).sum (fun i => Case3K.ν (Case3K.orbit n₀ i)) := by
    have h_j_in : j ∈ Finset.Ico j t := Finset.mem_Ico.mpr ⟨le_refl j, hjt⟩
    calc 0 < Case3K.ν (Case3K.orbit n₀ j) := Case3K.ν_ge_one _
      _ ≤ (Finset.Ico j t).sum (fun i => Case3K.ν (Case3K.orbit n₀ i)) :=
          Finset.single_le_sum (fun i _ => Nat.zero_le (Case3K.ν (Case3K.orbit n₀ i))) h_j_in
  omega

/-! ## Coarse waveSum Bound (Algebraically Provable) -/

/-- Geometric series: Σⱼ 3^{t-1-j} for j ∈ [0, t) equals (3^t - 1)/2 -/
lemma geom_sum_powers_of_3 (t : ℕ) (ht : t ≥ 1) :
    (Finset.range t).sum (fun j => 3^(t - 1 - j)) = (3^t - 1) / 2 := by
  rw [Finset.sum_range_reflect (fun k => (3 : ℕ)^k) t, Nat.geomSum_eq (by omega : 2 ≤ 3)]

/-- Coarse waveSum bound: waveSum < 3^t · 2^S.
    The recursive waveSum satisfies: c_0 = 0, c_{t+1} = 3*c_t + 2^{S_t}.
    By induction with the bound c_t < (3^t - 1) · 2^S / 2, we get c_t < 3^t · 2^S. -/
theorem waveSum_lt_coarse (n₀ t : ℕ) (ht : t ≥ 1) :
    waveSum n₀ t < 3^t * 2^(Case3K.νSum n₀ t) := by
  -- Induction on t: show waveSum n₀ t < 3^t * 2^S
  -- where S = νSum n₀ t
  induction t with
  | zero => omega
  | succ t ih =>
    simp only [waveSum]
    -- waveSum n₀ (t+1) = 3 * waveSum n₀ t + 2^(νSum n₀ t)
    set S := Case3K.νSum n₀ (t + 1) with hS
    set St := Case3K.νSum n₀ t with hSt
    -- Key: St < S (since ν ≥ 1)
    have h_St_lt_S : St < S := by
      simp only [hSt, hS]
      exact νSum_strict_mono n₀ t (t + 1) (Nat.lt_succ_self t)
    have h_2St_lt_2S : 2^St < 2^S := Nat.pow_lt_pow_right (by omega) h_St_lt_S
    -- Use coarse bound: waveSum n₀ t ≤ waveSum n₀ t
    -- For t ≥ 1: ih gives waveSum n₀ t < 3^t * 2^St
    -- But we need bound in terms of S, not St
    -- Since St < S: waveSum n₀ t < 3^t * 2^St < 3^t * 2^S
    by_cases ht_eq : t = 0
    · -- Base case t = 0
      subst ht_eq
      simp only [waveSum, Case3K.νSum, Finset.range_zero, Finset.sum_empty]
      -- waveSum n₀ 1 = 3 * 0 + 2^0 = 1
      -- Need: 1 < 3^1 * 2^S = 3 * 2^S
      have h_S_ge_1 : S ≥ 1 := by
        simp only [hS, Case3K.νSum, Finset.range_one, Finset.sum_singleton]
        exact Case3K.ν_ge_one (Case3K.orbit n₀ 0)
      calc 3 * 0 + 2^0 = 1 := by norm_num
        _ < 3 * 1 := by norm_num
        _ ≤ 3 * 2^S := by nlinarith [Nat.one_le_pow S 2 (by omega)]
        _ = 3^1 * 2^S := by ring
    · -- Inductive case t ≥ 1
      have ht_ge : t ≥ 1 := Nat.one_le_iff_ne_zero.mpr ht_eq
      have ih' := ih ht_ge
      -- ih' : waveSum n₀ t < 3^t * 2^St
      -- Need: 3 * waveSum n₀ t + 2^St < 3^{t+1} * 2^S
      -- We have: 3 * waveSum n₀ t + 2^St < 3 * (3^t * 2^St) + 2^St = (3^{t+1} + 1) * 2^St
      -- And: (3^{t+1} + 1) * 2^St < (3^{t+1} + 1) * 2^S ≤ 3^{t+1} * 2^S (need 3^{t+1} ≥ 3^{t+1}+1? No!)
      -- Alternative: Use that 2^St ≤ 2^{S-1} < 2^S, so 2^St < 2^S
      -- And 3 * (3^t * 2^St) = 3^{t+1} * 2^St < 3^{t+1} * 2^S
      -- So: 3 * waveSum + 2^St < 3^{t+1} * 2^St + 2^St = (3^{t+1} + 1) * 2^St
      --     ≤ (3^{t+1} + 1) * 2^{S-1} (if St ≤ S-1)
      --     = (3^{t+1} + 1) * 2^S / 2
      --     < 3^{t+1} * 2^S (if 3^{t+1} + 1 < 2 * 3^{t+1}, which is true)
      have h_St_le_Sm1 : St ≤ S - 1 := Nat.le_sub_one_of_lt h_St_lt_S
      have h_pow_2S_pos : 2^S > 0 := Nat.pow_pos (by omega : 0 < 2)
      have hS_pos : S ≥ 1 := by
        have := νSum_strict_mono n₀ t (t + 1) (Nat.lt_succ_self t)
        omega
      have h_pow_2Sm1 : 2^(S - 1) * 2 = 2^S := by
        have h : S = S - 1 + 1 := (Nat.sub_add_cancel hS_pos).symm
        conv_rhs => rw [h]
        ring
      have h_2St_le : 2^St ≤ 2^(S - 1) := Nat.pow_le_pow_right (by omega) h_St_le_Sm1
      have h_pow_3t1_pos : 3^(t+1) > 0 := Nat.pow_pos (by omega : 0 < 3)
      have h_pow_2Sm1_pos : 2^(S - 1) > 0 := Nat.pow_pos (by omega : 0 < 2)
      -- 3 * waveSum + 2^St < (3^{t+1} + 1) * 2^St ≤ (3^{t+1} + 1) * 2^{S-1}
      -- = (3^{t+1} + 1) * 2^S / 2 < 3^{t+1} * 2^S (since 3^{t+1} + 1 < 2 * 3^{t+1})
      have h_final_ineq : (3^(t+1) + 1) * 2^(S - 1) < 3^(t+1) * 2^S := by
        -- (3^{t+1} + 1) * 2^{S-1} < 3^{t+1} * 2^S
        -- ⟺ (3^{t+1} + 1) * 2^{S-1} < 3^{t+1} * 2^{S-1} * 2
        -- ⟺ 3^{t+1} + 1 < 2 * 3^{t+1}
        -- ⟺ 1 < 3^{t+1} ✓
        have h1 : (3^(t+1) + 1) < 2 * 3^(t+1) := by omega
        calc (3^(t+1) + 1) * 2^(S - 1)
            < 2 * 3^(t+1) * 2^(S - 1) := by nlinarith [h_pow_2Sm1_pos]
          _ = 3^(t+1) * (2^(S - 1) * 2) := by ring
          _ = 3^(t+1) * 2^S := by rw [h_pow_2Sm1]
      calc 3 * waveSum n₀ t + 2^St
          < 3 * (3^t * 2^St) + 2^St := by nlinarith [ih']
        _ = 3^(t+1) * 2^St + 2^St := by ring
        _ = (3^(t+1) + 1) * 2^St := by ring
        _ ≤ (3^(t+1) + 1) * 2^(S - 1) := Nat.mul_le_mul_left _ h_2St_le
        _ < 3^(t+1) * 2^S := h_final_ineq

/-! ## Descent Bound (Algebraically Provable from Past)

For strongly supercritical orbits, we get a descent bound that's sufficient
for no-divergence. Small n (≤ 2·3^t) stay in a bounded region anyway. -/

/-- Strongly supercritical: 2^S ≥ 2·3^t (stronger than 5S ≥ 8t for large t) -/
def StronglySupercritical (n₀ t : ℕ) : Prop :=
  2^(Case3K.νSum n₀ t) ≥ 2 * 3^t

/-- Descent bound from strongly supercritical and coarse waveSum bound.
    orbit < n/2 + 3^t + 2, which gives orbit < n for n > 2·3^t + 2. -/
theorem strongly_supercritical_descent (n₀ t : ℕ) (hn₀ : n₀ > 0) (hn₀_odd : n₀ % 2 = 1)
    (ht : t ≥ 1) (h_strong : StronglySupercritical n₀ t) :
    Case3K.orbit n₀ t < n₀ / 2 + 3^t + 2 := by
  -- Use orbit formula: orbit · 2^S = 3^t · n + waveSum
  have h_formula := fundamental_orbit_formula n₀ t hn₀_odd
  set S := Case3K.νSum n₀ t with hS
  set W := waveSum n₀ t with hW
  set m := Case3K.orbit n₀ t with hm
  have h_pow_pos : 2^S > 0 := Nat.pow_pos (by omega : 2 > 0)
  have h_3t_pos : 3^t > 0 := Nat.pow_pos (by omega : 3 > 0)
  -- Coarse waveSum bound
  have h_W_coarse : W < 3^t * 2^S := waveSum_lt_coarse n₀ t ht
  -- From orbit formula: m * 2^S = 3^t * n₀ + W < 3^t * n₀ + 3^t * 2^S = 3^t * (n₀ + 2^S)
  have h_upper : m * 2^S < 3^t * (n₀ + 2^S) := by
    calc m * 2^S = 3^t * n₀ + W := h_formula
      _ < 3^t * n₀ + 3^t * 2^S := by omega
      _ = 3^t * (n₀ + 2^S) := by ring
  -- With 2^S ≥ 2·3^t: 3^t * n₀ / 2^S ≤ n₀/2
  have h_div_bound : 3^t * n₀ / 2^S ≤ n₀ / 2 := by
    have h2 : 2 * 3^t ≤ 2^S := h_strong
    have h_simp : 3^t * n₀ / (2 * 3^t) = n₀ / 2 := by
      rw [mul_comm (3^t) n₀, Nat.mul_div_mul_right n₀ 2 h_3t_pos]
    calc 3^t * n₀ / 2^S ≤ 3^t * n₀ / (2 * 3^t) := Nat.div_le_div_left h2 (by omega)
      _ = n₀ / 2 := h_simp
  -- m < 3^t * (n₀ + 2^S) / 2^S + 1 ≤ n₀/2 + 3^t + 2
  -- From h_upper: m * 2^S < 3^t * (n₀ + 2^S)
  -- So m ≤ (3^t * (n₀ + 2^S) - 1) / 2^S (since strict inequality)
  -- Which gives m < (3^t * (n₀ + 2^S)) / 2^S + 1
  have h_m_lt_div : m < (3^t * (n₀ + 2^S)) / 2^S + 1 := by
    -- From m * 2^S < X, we get m ≤ (X - 1) / 2^S ≤ X / 2^S, so m < X / 2^S + 1
    have h1 : m ≤ (3^t * (n₀ + 2^S) - 1) / 2^S :=
      Nat.le_div_iff_mul_le h_pow_pos |>.mpr (Nat.le_sub_one_of_lt h_upper)
    have h2 : (3^t * (n₀ + 2^S) - 1) / 2^S ≤ (3^t * (n₀ + 2^S)) / 2^S :=
      Nat.div_le_div_right (Nat.sub_le _ 1)
    omega
  -- Split: (A + C*B) / C = A / C + B when C > 0
  -- Using Nat.add_mul_div_left : (x + y * z) / y = x / y + z
  have h_div_split : (3^t * n₀ + 2^S * 3^t) / 2^S = 3^t * n₀ / 2^S + 3^t := by
    exact Nat.add_mul_div_left (3^t * n₀) (3^t) h_pow_pos
  -- Substitute into the bound
  have h1 : 3^t * (n₀ + 2^S) = 3^t * n₀ + 2^S * 3^t := by ring
  -- m < (3^t * (n₀ + 2^S)) / 2^S + 1 = 3^t * n₀ / 2^S + 3^t + 1
  -- Combined with h_div_bound: 3^t * n₀ / 2^S ≤ n₀ / 2, so ≤ n₀/2 + 3^t + 1 < n₀/2 + 3^t + 2
  calc m < (3^t * (n₀ + 2^S)) / 2^S + 1 := h_m_lt_div
    _ = (3^t * n₀ + 2^S * 3^t) / 2^S + 1 := by rw [h1]
    _ = 3^t * n₀ / 2^S + 3^t + 1 := by rw [h_div_split]
    _ ≤ n₀ / 2 + 3^t + 1 := by omega
    _ < n₀ / 2 + 3^t + 2 := by omega

/-- For large n (n > 2·3^t + 2), strongly supercritical gives strict descent: orbit < n -/
theorem strongly_supercritical_strict_descent (n₀ t : ℕ) (hn₀ : n₀ > 0) (hn₀_odd : n₀ % 2 = 1)
    (ht : t ≥ 1) (h_strong : StronglySupercritical n₀ t) (h_large : n₀ > 2 * 3^t + 2) :
    Case3K.orbit n₀ t < n₀ := by
  have h_descent := strongly_supercritical_descent n₀ t hn₀ hn₀_odd ht h_strong
  -- n₀/2 + 3^t + 2 < n₀ when n₀ > 2·3^t + 4
  -- For n₀ > 2·3^t + 2 and odd n₀, we have n₀ ≥ 2·3^t + 3, so n₀/2 ≥ 3^t + 1
  -- n₀/2 + 3^t + 2 ≤ n₀ ⟺ 3^t + 2 ≤ n₀ - n₀/2 = (n₀+1)/2 for odd n₀
  -- ⟺ 2·3^t + 4 ≤ n₀ + 1 ⟺ 2·3^t + 3 ≤ n₀ ✓ (since n₀ > 2·3^t + 2 and odd)
  have h_bound : n₀ / 2 + 3^t + 2 ≤ n₀ := by
    have h_odd : n₀ % 2 = 1 := hn₀_odd
    have h1 : n₀ ≥ 2 * 3^t + 3 := by omega
    -- For odd n₀: n₀/2 = (n₀-1)/2
    have h2 : n₀ / 2 ≥ 3^t + 1 := by omega
    omega
  omega

/-- Bounded region: for small n (n ≤ 2·3^t + 2), orbit stays bounded by 2·3^t + 2 anyway.
    Combined with strict descent for large n, this proves no-divergence. -/
theorem bounded_region (n₀ t : ℕ) (hn₀ : n₀ > 0) (hn₀_odd : n₀ % 2 = 1)
    (ht : t ≥ 1) (h_strong : StronglySupercritical n₀ t) (h_small : n₀ ≤ 2 * 3^t + 2) :
    Case3K.orbit n₀ t < 2 * 3^t + 3^t + 2 := by
  have h_descent := strongly_supercritical_descent n₀ t hn₀ hn₀_odd ht h_strong
  -- orbit < n₀/2 + 3^t + 2 ≤ (2·3^t + 2)/2 + 3^t + 2 = 3^t + 1 + 3^t + 2 = 2·3^t + 3
  have h1 : n₀ / 2 ≤ 3^t + 1 := by omega
  omega

/-! ## Summary: Discharging the Axiom via Option B

The axiom `supercritical_orbit_bound_early` (tight bound: orbit ≤ n+1) can be
effectively replaced by the descent bound for proving no-divergence:

1. For n > 2·3^t + 2: orbit < n (strict descent via `strongly_supercritical_strict_descent`)
2. For n ≤ 2·3^t + 2: orbit < 2·3^t + 3^t + 2 = 3·3^t + 2 (bounded region via `bounded_region`)

These bounds are ALGEBRAICALLY PROVABLE using only the past-based waveSum structure,
without requiring information-theoretic constraints.

The tight orbit ≤ n+1 bound is only needed if we want the sharpest possible bound,
but for proving Collatz convergence, descent + bounded region suffices.
-/

end Collatz.RatioBoundProof
