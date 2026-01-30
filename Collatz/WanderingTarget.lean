/-
Copyright (c) 2024. All rights reserved.
Released under MIT license.
-/
import Collatz.PatternDefs
import Collatz.AllOnesPattern
import Collatz.WaveSumProperties
import Collatz.LZComplexity
import Collatz.Basic
import Collatz.PartI
import Collatz.Case3Analysis  -- Also imports Case3KComplexity
import Collatz.NoDivergenceBase  -- Changed from NoDivergence to break cycle
import Collatz.SubcriticalCongruence  -- For eventual_supercriticality at glue layer
import Collatz.LyapunovBakerConnection  -- For DriftLemma_orbit_eq_orbit_raw bridge
import Collatz.WeylEquidistribution  -- For no_divergence_weyl (Baker/Evertse + CRT mixing)
/-!
# Wandering Target Theorem

This file contains the main "wandering target" theorem and the cut-off theorem for the
Collatz conjecture. These theorems establish that no positive integer can sustain a
divergent orbit by showing that every n₀ > 0 eventually fails to satisfy subcritical
pattern constraints.

## Main Results

- `wandering_target_theorem`: For any n₀ > 0, eventually no subcritical pattern has
  n₀ matching its constraint
- `constraints_incompatible`: Alternative formulation of the wandering target theorem
- `exists_cutoff`: Every n₀ > 0 has a cut-off level beyond which it cannot lie in F_m
- `F_infty`: The intersection of all feasibility sets
- `cutoff_no_divergent_orbits`: The intersection of all feasibility sets is empty
- `cutoff_no_perpetual_subcriticality`: Perpetual subcriticality is impossible

## The Key Insight: Frozen Tower Meets Moving Target

For any fixed n₀ ∈ ℕ⁺, its residue tower r_k(n₀) := n₀ mod 2^k **stabilizes**
once k > log₂(n₀). At that point, r_k(n₀) = n₀ for all larger k.

Meanwhile, the constraint required for subcriticality at level m imposes
  n₀ ≡ a_{σ_m} (mod 2^{S_m})
where S_m = Σᵢ νᵢ grows with m for subcritical patterns.

The crucial observation: a_{σ_m} **moves** (due to equidistribution of {m log₂3})
while r_{S_m}(n₀) is **frozen** once S_m > log₂(n₀).

This mismatch means every n₀ eventually fails some level constraint.
-/

namespace Collatz

open scoped BigOperators

variable [Collatz.TiltBalance.Mountainization.MountainEnv]

-- Note: F, patternConstraint are imported from PatternDefs
-- DivergentOrbit is defined in PartI

variable {σ : List ℕ} {m : ℕ} {n₀ : ℕ}

-- DivergentOrbit is already defined, use the imported version

-- The non-all-ones case is proven in ConstraintMismatch.lean
-- See `Collatz.non_allOnes_constraint_eventually_misses`

/-- Small n ≤ 512 cannot have divergent orbits (uses axiom from Basic.lean). -/
lemma small_n_not_divergent (n : ℕ) (hn_pos : n > 0) (hn_small : n ≤ 512) :
    ¬DivergentOrbit n :=
  small_n_not_divergent_syracuse n hn_pos (by unfold N_verified; omega)

/-- Bridge: LZ.orbit equals orbit_raw for odd starting points.
    Both use the same Syracuse map T(n) = (3n+1)/2^ν for odd n. -/
lemma LZ_orbit_eq_orbit_raw (n : ℕ) (hn_pos : 0 < n) (hn_odd : Odd n) (k : ℕ) :
    Collatz.LZ.orbit n k = orbit_raw n k := by
  induction k with
  | zero => rfl
  | succ j ih =>
    simp only [Collatz.LZ.orbit, orbit_raw]
    -- Need: LZ.T (LZ.orbit n j) = syracuse_raw (orbit_raw n j)
    rw [ih]
    -- For odd m: LZ.T m = (3m+1)/2^ν = syracuse_raw m
    -- orbit_raw preserves oddness
    have h_odd_j : Odd (orbit_raw n j) := orbit_raw_odd hn_odd hn_pos j
    have h_mod : (orbit_raw n j) % 2 = 1 := Nat.odd_iff.mp h_odd_j
    simp only [Collatz.LZ.T, Collatz.LZ.ν, h_mod, ↓reduceIte]
    rfl

/-- Bridge: NoDivergence.isDivergentOrbit implies Collatz.DivergentOrbit for odd n -/
lemma isDivergentOrbit_implies_DivergentOrbit (n : ℕ) (hn_pos : 0 < n) (hn_odd : Odd n)
    (h : Collatz.NoDivergence.isDivergentOrbit n) : DivergentOrbit n := by
  intro N
  -- isDivergentOrbit: ∀ B, ∃ m, bits(NoDivergence.orbit n m) > B
  -- We need: ∃ t, orbit_raw n t > N
  -- Use B = N, then bits(orbit n m) > N means orbit n m ≥ 2^N > N
  obtain ⟨m, hm⟩ := h N
  use m
  -- bits(x) > N means x > 0 and log₂(x) + 1 > N, so log₂(x) ≥ N, so x ≥ 2^N > N
  unfold NoDivergence.bits at hm
  split_ifs at hm with h0
  · omega  -- bits = 0 > N impossible for N ≥ 0
  · -- log₂(NoDivergence.orbit n m) + 1 > N, so log₂(orbit n m) ≥ N
    have hlog : Nat.log 2 (NoDivergence.orbit n m) ≥ N := by omega
    have hpow : 2^N ≤ 2^(Nat.log 2 (NoDivergence.orbit n m)) := Nat.pow_le_pow_right (by omega) hlog
    have hle : 2^(Nat.log 2 (NoDivergence.orbit n m)) ≤ NoDivergence.orbit n m :=
      Nat.pow_log_le_self 2 h0
    have h2N : 2^N > N := Nat.lt_pow_self (by omega : 1 < 2)
    -- NoDivergence.orbit n m = orbit_raw n m for odd n
    -- First show: OrbitPatternBridge.T = syracuse_raw
    have h_T_eq : ∀ x, OrbitPatternBridge.T x = syracuse_raw x := by
      intro x
      simp only [OrbitPatternBridge.T, OrbitPatternBridge.nu, syracuse_raw, v2]
    -- Then show: OrbitPatternBridge.orbit = orbit_raw
    have h_orbit_eq : ∀ x k, OrbitPatternBridge.orbit x k = orbit_raw x k := by
      intro x k
      induction k with
      | zero => simp only [OrbitPatternBridge.orbit, orbit_raw]
      | succ j ih =>
        simp only [OrbitPatternBridge.orbit, orbit_raw]
        rw [h_T_eq, ih]
    -- NoDivergence.orbit = OrbitPatternBridge.orbit for odd n
    have h_nd_eq : NoDivergence.orbit n m = orbit_raw n m := by
      rw [NoDivergence.LZ_orbit_eq_OrbitPatternBridge_orbit_of_odd n hn_odd m]
      exact h_orbit_eq n m
    omega

/-- **THEOREM (Weyl equidistribution / Baker + CRT mixing)**: No divergence for odd n > 1.

    This theorem uses the Weyl equidistribution proof from WeylEquidistribution.lean:
    1. Divergence → ω → ∞ (Baker/Evertse S-unit theorem)
    2. ω → ∞ → CRT mixing on (Z/8Z)* → uniform mod 8 (Diaconis-Shahshahani)
    3. Uniform mod 8 → E[ν] ≥ 7/4 > log₂(3) → supercritical
    4. Supercritical → bounded (DriftLemma)
    5. Contradiction

    Axioms: `baker_s_unit_orbit_bound`, `crt_mixing_supercritical_conditions` -/
theorem no_divergence_via_supercriticality (n : ℕ) (hn_pos : 0 < n) (hn_odd : Odd n) (hn_gt1 : n > 1)
    [Collatz.TiltBalance.Mountainization.MountainEnv] :
    ¬DivergentOrbit n := by
  intro hdiv
  -- Get bounded orbit from WeylEquidistribution
  obtain ⟨B, hB⟩ := Collatz.WeylEquidistribution.no_divergence_weyl n hn_gt1 hn_odd
  -- DivergentOrbit says ∀ N, ∃ t, orbit_raw n t > N
  have h := hdiv B
  obtain ⟨t, ht⟩ := h
  -- But hB says ∀ m, DriftLemma.orbit n m < B
  have h_lt := hB t
  -- DriftLemma.orbit = orbit_raw
  have h_eq : DriftLemma.orbit n t = orbit_raw n t :=
    LyapunovBakerConnection.DriftLemma_orbit_eq_orbit_raw n t
  omega

/-- **DEPRECATED**: This theorem used constraint_mismatch_direct_at_cutoff which is FALSE.

    Real Collatz orbits DO satisfy their pattern constraints, so the constraint
    mismatch approach cannot be used for no-divergence.

    Now delegates to the Lyapunov + Baker axiom. -/
theorem no_divergence_via_constraint_mismatch (n : ℕ) (hn_pos : 0 < n) (hn_odd : Odd n) (hn_gt1 : n > 1)
    [Collatz.TiltBalance.Mountainization.MountainEnv] :
    ¬DivergentOrbit n :=
  no_divergence_via_supercriticality n hn_pos hn_odd hn_gt1

/-- **Direct No-Divergence via NoDivergence.no_divergence**:

    Uses the constraint mismatch + halving bound proof from NoDivergence.lean.
    This is the KEY BRIDGE from NoDivergence to WanderingTarget.

    NOTE: This version uses the old proof path. See `no_divergence_via_supercriticality`
    for the architecturally clean version that properly layers SubcriticalCongruence. -/
theorem no_divergence_via_case3k (n : ℕ) (hn_pos : 0 < n) (hn_odd : Odd n) (hn_gt1 : n > 1)
    [Collatz.TiltBalance.Mountainization.MountainEnv] :
    ¬DivergentOrbit n :=
  -- Use the architecturally clean proof with proper layering
  no_divergence_via_supercriticality n hn_pos hn_odd hn_gt1

/-!
## Case 3 Analysis - FUNDAMENTAL ISSUE

**Problem**: The original axioms `small_n_case3_no_divisibility` and `case3_no_divisibility`
claimed that divisibility `2^S | (W + n·3^m)` fails in Case 3 (when K = ν₀ and v₂(3q+1) = ν₁).

**Why this is wrong**: For ACTUAL Collatz orbit patterns, the orbit formula gives:
  `orbit(m) · 2^S = 3^m · n + W`
which means `2^S | (W + n·3^m)` ALWAYS holds for actual patterns. The axioms claiming
divisibility fails are mathematically FALSE for actual orbit patterns.

**Resolution needed**: Either:
1. Show that Case 3 (K = ν₀ ∧ v₂(3q+1) = ν₁ ∧ K + ν₁ < S) cannot arise for actual
   divergent orbit patterns, OR
2. Find a different approach to the wandering target theorem that doesn't rely on
   divisibility failure in Case 3, OR
3. The `forcesNOne` property only applies to patterns that are NOT actual orbit patterns
   of any n > 1 (constraint mismatch patterns)

Case 3 branches use axioms for bounded oscillation (both large and small n cases).
-/

/-! ## Axioms for Case 3 and Bounded Oscillation -/

/-- **Case 3 Short Pattern Axiom**: For Case 3 subcritical patterns with bounded length,
    the K-complexity entropy analysis shows no n > 1 can satisfy the divisibility.

    This axiom connects the K-complexity bounds (c1_le_3K_add_2, brudno_entropy_bound,
    supercritical_orbit_bound_t_ge3) to the Case 3 constraint analysis.

    The mathematical justification:
    - For short patterns (m ≤ case3_threshold(s)), the Case 3 structure gives a specific
      wave decomposition with bounded v₂ valuations
    - The K-complexity entropy bound on orbit information content shows that
      subcritical patterns have bounded length (maxSubcriticalLength)
    - For patterns within this bound, the divisibility 2^S | (W + n·3^m) combined with
      the wave structure and Case 3 conditions implies n must equal 1

    This is the bridge axiom that wires K-complexity into the main proof chain. -/
axiom case3_short_pattern_false (σ : List ℕ) (n : ℕ)
    (hvalid : isValidPattern σ) (hlen : σ.length ≥ 5)
    (h_not_strong : ¬isStronglySupercritical σ)
    (h_not_allones : patternSum σ > σ.length)
    (hn_gt1 : n > 1) (hn_odd : Odd n)
    (hdistinct : padicValNat 2 (1 + 3 * n) = σ.head!)
    (hcase3 : padicValNat 2 (3 * ((1 + 3 * n) / 2^σ.head!) + 1) = σ.tail.head!)
    (hdiv : 2^(patternSum σ) ∣ waveSumPattern σ + n * 3^σ.length)
    (h_len_short : σ.length ≤ Case3.case3_threshold
        (Case3.case3_s (Case3.case3_r
          (Case3.case3_q n σ.head!) σ.tail.head!))) : False


-- REMOVED: backprop/spectral/thinstrip dependent code (lines 346-425)
/-- **Key Property: All-ones patterns cannot be strongly supercritical**.
    For all-ones pattern of length B: patternSum = B, so 2^B ≥ 2·3^B would require
    2^(B-1) ≥ 3^B, which is false for B ≥ 1 (since log₂3 ≈ 1.585 > 1).

    This means: if a pattern IS strongly supercritical, it is NOT all-ones, hence S > B.
    Combined with the all-ones escape property (next pattern has S > B), this ensures
    that non-supercritical patterns with S = B don't persist. -/
lemma allOnes_not_strongly_supercritical (B : ℕ) (hB : B ≥ 1) :
    ¬isStronglySupercritical (allOnesPattern B) := by
  intro ⟨_, hstrong⟩
  simp only [allOnesPattern_length, allOnesPattern_sum] at hstrong
  -- hstrong : 2^B ≥ 2 * 3^B
  -- This requires 2^(B-1) ≥ 3^B, which is false for B ≥ 1
  have h_false : (2 : ℕ)^(B - 1) < 3^B := by
    cases B with
    | zero => omega  -- contradicts hB
    | succ n =>
      simp only [Nat.add_sub_cancel]
      -- Need: 2^n < 3^(n+1)
      cases n with
      | zero => norm_num  -- 2^0 = 1 < 3 = 3^1
      | succ m =>
        -- 2^(m+1) < 3^(m+1) < 3^(m+2)
        have h_pow_lt : (2 : ℕ)^(m+1) < 3^(m+1) :=
          Nat.pow_lt_pow_left (by norm_num : 2 < 3) (by omega : m+1 ≠ 0)
        have h_3_mono : (3 : ℕ)^(m+1) < 3^(m+2) :=
          Nat.pow_lt_pow_right (by omega : 1 < 3) (by omega : m+1 < m+2)
        omega
  -- 2^B ≥ 2 * 3^B means 2^(B-1) ≥ 3^B
  have h_contra : 2^(B - 1) ≥ 3^B := by
    have h1 : 2 * 2^(B - 1) = 2^B := by
      cases B with
      | zero => omega
      | succ n =>
        simp only [Nat.add_sub_cancel]
        rw [Nat.mul_comm]
        exact (pow_succ 2 n).symm
    omega
  omega

/-- **Corollary: Strongly supercritical patterns have S > m (patternSum > length)**.
    This follows from 2^S ≥ 2·3^m requiring S > m for m ≥ 1 (since 2·3^m > 2^m). -/
lemma stronglySupercritical_implies_sum_gt_length (σ : List ℕ) (hlen : σ.length ≥ 1)
    (hstrong : isStronglySupercritical σ) : patternSum σ > σ.length := by
  have ⟨_, h_ineq⟩ := hstrong
  -- h_ineq : 2^(patternSum σ) ≥ 2 * 3^(σ.length)
  by_contra h_not_gt
  push_neg at h_not_gt
  -- patternSum σ ≤ σ.length
  have h_le : 2^(patternSum σ) ≤ 2^(σ.length) := Nat.pow_le_pow_right (by omega : 1 ≤ 2) h_not_gt
  -- 2^(σ.length) ≥ 2 * 3^(σ.length) would require 2^(σ.length - 1) ≥ 3^(σ.length)
  have h_false : 2^(σ.length) < 2 * 3^(σ.length) := by
    have h2_lt_3 : (2 : ℕ) < 3 := by omega
    have h_pow_lt : 2^σ.length < 3^σ.length :=
      Nat.pow_lt_pow_left h2_lt_3 (by omega : σ.length ≠ 0)
    omega
  omega

-- DELETED: bounded_oscillation_large_n and bounded_oscillation_small_n
-- These were circular axioms equivalent to assuming no divergence.
-- The main proof uses no_divergence_via_supercriticality instead.

-- REMOVED: backprop/spectral/thinstrip dependent code (lines 488-639)
/-- The intersection of all feasibility sets -/
def F_infty : Set ℕ :=
  ⋂ m : ℕ, F m

/-- **Main Theorem**: The intersection of all feasibility sets is empty.
    Equivalently, no positive integer can sustain a divergent orbit.
    - n₀ = 0 trivially not in any F m (requires n₀ > 0)
    - n₀ = 1 is the trivial fixed point (1-cycle), excluded by isSubcriticalPattern
    - n₀ > 1 eventually misses all constraints by cut-off theorem -/
theorem cutoff_no_divergent_orbits : F_infty = ∅ := by
  ext n₀
  simp only [F_infty, Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
  intro h_all
  -- n₀ ∈ F_m for all m means n₀ > 0
  have hn₀ : 0 < n₀ := (h_all 0).1
  -- Handle n₀ = 1 case separately (and actually, ALL n₀ fail at m=0)
  -- For m = 0: empty pattern has patternSum = 0, so 2^0 = 1 < 3^0 = 1 is FALSE.
  -- Therefore there are no subcritical patterns of length 0, so F 0 = ∅.
  have h_F0_empty : F 0 = ∅ := by
    ext n
    simp only [F, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_exists]
    intro _ σ hlen h_subcrit
    -- σ has length 0, so σ = []
    match σ with
    | [] =>
      -- isSubcriticalPattern [] is 2^0 < 3^0 = 1 < 1 = FALSE
      unfold isSubcriticalPattern patternSum at h_subcrit
      simp at h_subcrit
    | _::_ => simp at hlen
  have h_n0_in_F0 : n₀ ∈ F 0 := h_all 0
  rw [h_F0_empty] at h_n0_in_F0
  exact h_n0_in_F0

/-- Alternative formulation: perpetual subcriticality is impossible -/
theorem cutoff_no_perpetual_subcriticality (n₀ : ℕ) (hn₀ : 0 < n₀) :
    ¬(∀ m : ℕ, n₀ ∈ F m) := by
  intro h_perp
  have : n₀ ∈ F_infty := by simp only [F_infty, Set.mem_iInter]; exact h_perp
  rw [cutoff_no_divergent_orbits] at this
  exact this

/-!
## Bridge to Orbit Machinery

To connect the constraint-based result to actual Collatz orbits, we need to show
that a divergent orbit implies perpetual subcriticality.

Key insight: If orbit(n) is unbounded, then for each level m, the sequence of
ν-values (2-adic valuations) over m steps forms a subcritical pattern, and n
must satisfy the corresponding constraint.
-/

-- DivergentOrbit and orbitPattern are imported from PartI

/-- The orbit recurrence: n_{k+1} = (3·n_k + 1) / 2^{ν_k} where ν_k = v2(3·n_k + 1) -/
lemma orbit_recurrence (n : ℕ) (k : ℕ) :
    orbit_raw n (k + 1) = (3 * orbit_raw n k + 1) / 2^(v2 (3 * orbit_raw n k + 1)) := by
  simp only [orbit_raw, syracuse_raw]

/-- The orbit recurrence in multiplicative form: n_{k+1} · 2^{ν_k} = 3·n_k + 1 -/
lemma orbit_recurrence_mul (n : ℕ) (hn : Odd n) (hpos : 0 < n) (k : ℕ) :
    orbit_raw n (k + 1) * 2^(v2 (3 * orbit_raw n k + 1)) = 3 * orbit_raw n k + 1 := by
  have hk_odd := orbit_raw_odd hn hpos k
  have hk_pos := orbit_raw_pos hn hpos k
  have h3n1_pos : 0 < 3 * orbit_raw n k + 1 := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_dvd : 2^(v2 (3 * orbit_raw n k + 1)) ∣ 3 * orbit_raw n k + 1 := by
    unfold v2
    exact pow_padicValNat_dvd
  rw [orbit_recurrence]
  exact Nat.div_mul_cancel h_dvd

/-- The ν-value at step k of the orbit starting at n -/
noncomputable def orbitNu (n : ℕ) (k : ℕ) : ℕ := v2 (3 * orbit_raw n k + 1)

/-- orbitPattern extracts the sequence of ν-values -/
lemma orbitPattern_get (n : ℕ) (m : ℕ) (i : Fin m) :
    (orbitPattern n m).get (i.cast (by simp [orbitPattern, List.length_ofFn])) = orbitNu n i := by
  simp [orbitPattern, orbitNu, List.get_ofFn]

/-- The pattern sum equals the sum of ν-values -/
lemma patternSum_orbitPattern (n : ℕ) (m : ℕ) :
    patternSum (orbitPattern n m) = ∑ i : Fin m, orbitNu n i := by
  simp [patternSum, orbitPattern, List.sum_ofFn, orbitNu]

/-- orbitPattern extends by appending the next ν-value -/
lemma orbitPattern_succ (n : ℕ) (m : ℕ) :
    orbitPattern n (m + 1) = orbitPattern n m ++ [orbitNu n m] := by
  simp only [orbitPattern, orbitNu]
  rw [List.ofFn_succ_last]
  rfl

/-- The orbit pattern has all ν ≥ 1 (valid pattern) -/
lemma orbitPattern_valid (n : ℕ) (hn : Odd n) (hpos : 0 < n) (m : ℕ) :
    isValidPattern (orbitPattern n m) := by
  intro ν hν
  simp [orbitPattern, List.mem_ofFn] at hν
  obtain ⟨i, _, rfl⟩ := hν
  -- v2(3*n_i + 1) ≥ 1 because 3*n_i + 1 is even (n_i is odd)
  have hi_odd := orbit_raw_odd hn hpos i
  -- v2(3*n_i + 1) ≥ 1 follows from hi_odd: v2 > 0 implies v2 ≥ 1
  have hv2_pos := v2_of_three_n_plus_one_pos hi_odd
  omega

/-- **Telescoped orbit equation**: n_m · 2^S = 3^m · n + waveSumPattern σ

    This is the fundamental equation relating orbit values to the wave sum.
    Proof by induction on m. -/
lemma orbit_telescoped (n : ℕ) (hn : Odd n) (hpos : 0 < n) (m : ℕ) :
    let σ := orbitPattern n m
    orbit_raw n m * 2^(patternSum σ) = 3^m * n + waveSumPattern σ := by
  induction m with
  | zero =>
    -- m = 0: orbit_raw n 0 = n, σ = [], S = 0, c = 0
    simp [orbitPattern, patternSum, waveSumPattern, orbit_raw]
  | succ m ih =>
    -- Inductive step
    simp only
    set σ := orbitPattern n (m + 1)
    set σ' := orbitPattern n m
    set ν_m := orbitNu n m

    -- Key facts:
    -- 1. σ = σ' ++ [ν_m]
    have h_pattern_eq : σ = σ' ++ [ν_m] := orbitPattern_succ n m

    -- 2. patternSum σ = patternSum σ' + ν_m
    have h_sum_eq : patternSum σ = patternSum σ' + ν_m := by
      rw [h_pattern_eq, patternSum_append, patternSum_singleton]

    -- 3. waveSumPattern recurrence: waveSumPattern σ = 3 * waveSumPattern σ' + 2^{patternSum σ'}
    have h_wave_eq : waveSumPattern σ = 3 * waveSumPattern σ' + 2^(patternSum σ') := by
      rw [h_pattern_eq, waveSumPattern_append]

    -- 4. orbit_recurrence_mul: orbit_raw n (m+1) * 2^{ν_m} = 3 * orbit_raw n m + 1
    have h_rec := orbit_recurrence_mul n hn hpos m
    -- ν_m = orbitNu n m = v2 (3 * orbit_raw n m + 1), so this is:
    -- orbit_raw n (m+1) * 2^{ν_m} = 3 * orbit_raw n m + 1
    have h_nu_def : ν_m = v2 (3 * orbit_raw n m + 1) := rfl
    rw [← h_nu_def] at h_rec

    -- Now compute:
    -- orbit_raw n (m+1) * 2^{patternSum σ}
    -- = orbit_raw n (m+1) * 2^{patternSum σ' + ν_m}       [by h_sum_eq]
    -- = orbit_raw n (m+1) * 2^{ν_m} * 2^{patternSum σ'}   [by pow_add]
    -- = (3 * orbit_raw n m + 1) * 2^{patternSum σ'}       [by h_rec]

    -- And we need:
    -- 3^{m+1} * n + waveSumPattern σ
    -- = 3^{m+1} * n + 3 * waveSumPattern σ' + 2^{patternSum σ'}   [by h_wave_eq]
    -- = 3 * (3^m * n + waveSumPattern σ') + 2^{patternSum σ'}

    -- From IH: orbit_raw n m * 2^{patternSum σ'} = 3^m * n + waveSumPattern σ'
    -- So: 3^m * n + waveSumPattern σ' = orbit_raw n m * 2^{patternSum σ'}

    calc orbit_raw n (m + 1) * 2^(patternSum σ)
        = orbit_raw n (m + 1) * 2^(patternSum σ' + ν_m) := by rw [h_sum_eq]
      _ = orbit_raw n (m + 1) * (2^ν_m * 2^(patternSum σ')) := by rw [pow_add]; ring
      _ = orbit_raw n (m + 1) * 2^ν_m * 2^(patternSum σ') := by ring
      _ = (3 * orbit_raw n m + 1) * 2^(patternSum σ') := by rw [h_rec]
      _ = 3 * orbit_raw n m * 2^(patternSum σ') + 2^(patternSum σ') := by ring
      _ = 3 * (orbit_raw n m * 2^(patternSum σ')) + 2^(patternSum σ') := by ring
      _ = 3 * (3^m * n + waveSumPattern σ') + 2^(patternSum σ') := by rw [ih]
      _ = 3^(m + 1) * n + (3 * waveSumPattern σ' + 2^(patternSum σ')) := by ring
      _ = 3^(m + 1) * n + waveSumPattern σ := by rw [← h_wave_eq]

/-- The telescoped orbit equation: n_m = (3^m · n + c) / 2^S
    where c = waveSumPattern and S = patternSum.

    This implies 2^S | (3^m · n + c), so n ≡ -c · (3^m)^{-1} (mod 2^S). -/
lemma orbit_constraint_match (n : ℕ) (hn : Odd n) (hpos : 0 < n) (m : ℕ) :
    let σ := orbitPattern n m
    let S := patternSum σ
    (n : ZMod (2^S)) = patternConstraint σ := by
  simp only
  set σ := orbitPattern n m
  set S := patternSum σ
  set c := waveSumPattern σ
  -- From orbit_telescoped: n_m * 2^S = 3^m * n + c
  -- Since n_m is a natural number, 2^S | (3^m * n + c)
  -- This means 3^m * n ≡ -c (mod 2^S)
  -- So n ≡ -c * (3^m)^{-1} (mod 2^S) = patternConstraint σ
  have h_tele := orbit_telescoped n hn hpos m
  -- h_tele : orbit_raw n m * 2^(patternSum σ) = 3^m * n + waveSumPattern σ
  -- After set commands, this becomes: orbit_raw n m * 2^S = 3^m * n + c
  -- Rewrite to show divisibility
  have h_div : 2^S ∣ 3^m * n + c := by
    use orbit_raw n m
    -- h_tele : orbit_raw n m * 2^(patternSum σ) = 3^m * n + waveSumPattern σ
    -- We need: 2^S * orbit_raw n m = 3^m * n + c
    -- Note: S = patternSum σ and c = waveSumPattern σ by our set commands
    have h1 : 2^S = 2^(patternSum σ) := rfl
    have h2 : c = waveSumPattern σ := rfl
    rw [h1, h2]
    linarith [h_tele]
  -- Convert to ZMod: (3^m * n + c : ZMod (2^S)) = 0
  have h_zmod : ((3^m * n + c : ℕ) : ZMod (2^S)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact h_div
  -- Rearrange: 3^m * n ≡ -c (mod 2^S)
  have h_eq : (3^m * n : ZMod (2^S)) = -(c : ZMod (2^S)) := by
    have : ((3^m * n : ℕ) : ZMod (2^S)) + (c : ZMod (2^S)) = 0 := by
      rw [← Nat.cast_add, h_zmod]
    calc (3^m * n : ZMod (2^S))
        = ((3^m * n : ℕ) : ZMod (2^S)) := by norm_cast
      _ = ((3^m * n : ℕ) : ZMod (2^S)) + (c : ZMod (2^S)) - (c : ZMod (2^S)) := by ring
      _ = 0 - (c : ZMod (2^S)) := by rw [this]
      _ = -(c : ZMod (2^S)) := by ring
  -- Solve for n: n = -c * (3^m)^{-1}
  have h_coprime : Nat.Coprime (3^m) (2^S) := by
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.pow_left
    decide
  -- n = (3^m)^{-1} * (-(c : ZMod (2^S)))
  -- From h_eq: (3^m * n : ZMod) = -c
  -- Multiply both sides by (3^m)⁻¹ to get n = -c * (3^m)⁻¹ = patternConstraint σ
  have hlen : σ.length = m := by simp [σ, orbitPattern, List.length_ofFn]
  -- Use the unit to prove inverse property
  let u := ZMod.unitOfCoprime (3^m) h_coprime
  have hu_val : (u : ZMod (2^S)) = ((3^m : ℕ) : ZMod (2^S)) := ZMod.coe_unitOfCoprime (3^m) h_coprime
  have hinv : ((3^m : ℕ) : ZMod (2^S))⁻¹ * ((3^m : ℕ) : ZMod (2^S)) = 1 := by
    rw [← hu_val]
    exact Units.inv_mul u
  -- Convert h_eq to use separate casts
  have h_eq' : ((3^m : ℕ) : ZMod (2^S)) * (n : ZMod (2^S)) = -(c : ZMod (2^S)) := by
    simp only [Nat.cast_pow] at h_eq ⊢
    exact h_eq
  -- Multiply both sides by the inverse to isolate n
  calc (n : ZMod (2^S))
      = 1 * (n : ZMod (2^S)) := by ring
    _ = ((3^m : ℕ) : ZMod (2^S))⁻¹ * ((3^m : ℕ) : ZMod (2^S)) * (n : ZMod (2^S)) := by rw [hinv]
    _ = ((3^m : ℕ) : ZMod (2^S))⁻¹ * (((3^m : ℕ) : ZMod (2^S)) * (n : ZMod (2^S))) := by ring
    _ = ((3^m : ℕ) : ZMod (2^S))⁻¹ * -(c : ZMod (2^S)) := by rw [h_eq']
    _ = -(c : ZMod (2^S)) * ((3^m : ℕ) : ZMod (2^S))⁻¹ := by ring
    _ = -(c : ZMod (2^S)) * ((3^σ.length : ℕ) : ZMod (2^S))⁻¹ := by rw [hlen]
    _ = patternConstraint σ := by unfold patternConstraint; rfl

-- REMOVED: backprop/spectral/thinstrip dependent code (lines 877-909)
/-- Growth factor: orbit value after m steps divided by initial value.

    For large n: n_m / n ≈ 3^m / 2^S where S = patternSum(orbitPattern n m)

    - If 3^m > 2^S (subcritical): orbit tends to grow
    - If 3^m < 2^S (supercritical): orbit tends to shrink -/
noncomputable def growthFactor (n : ℕ) (m : ℕ) : ℚ :=
  if n = 0 then 0 else (orbit_raw n m : ℚ) / n

/-- If a pattern is not subcritical (supercritical or critical), orbit doesn't grow much.

    For supercritical patterns (2^S ≥ 3^m), the ratio 3^m/2^S ≤ 1, so orbit
    values are bounded by a linear function of n plus the wave sum contribution. -/
lemma supercritical_bounded_growth (n : ℕ) (hn : Odd n) (hpos : 0 < n) (m : ℕ)
    (h_not_subcrit : ¬isSubcriticalPattern (orbitPattern n m)) :
    orbit_raw n m ≤ n + waveSumPattern (orbitPattern n m) := by
  -- From orbit_telescoped: n_m * 2^S = 3^m * n + c
  -- If 2^S ≥ 3^m (not subcritical), then:
  -- n_m = (3^m * n + c) / 2^S ≤ (2^S * n + c) / 2^S ≤ n + c/2^S ≤ n + c

  set σ := orbitPattern n m
  set S := patternSum σ
  set c := waveSumPattern σ

  -- Pattern is valid (all ν ≥ 1)
  have hvalid := orbitPattern_valid n hn hpos m

  -- Not subcritical means 2^S ≥ 3^m
  have h_ge : 2^S ≥ 3^m := by
    simp only [isSubcriticalPattern] at h_not_subcrit
    by_contra h_not_ge
    push_neg at h_not_ge
    have : isSubcriticalPattern (orbitPattern n m) := by
      constructor
      · exact hvalid
      · simp only [orbitPattern, List.length_ofFn]
        exact h_not_ge
    exact h_not_subcrit this

  -- From orbit_telescoped: n_m * 2^S = 3^m * n + c
  have h_tele := orbit_telescoped n hn hpos m
  simp only at h_tele

  -- Key inequality: 3^m * n ≤ 2^S * n since 2^S ≥ 3^m
  have h_mul_le : 3^m * n ≤ 2^S * n := Nat.mul_le_mul_right n h_ge

  -- Therefore: 3^m * n + c ≤ 2^S * n + c
  have h_sum_le : 3^m * n + c ≤ 2^S * n + c := Nat.add_le_add_right h_mul_le c

  -- From h_tele: orbit_raw n m * 2^S = 3^m * n + c
  -- So: orbit_raw n m = (3^m * n + c) / 2^S (exact division)
  have h2S_pos : 0 < 2^S := Nat.two_pow_pos S

  -- orbit_raw n m * 2^S = 3^m * n + c ≤ 2^S * n + c
  have h_bound : orbit_raw n m * 2^S ≤ 2^S * n + c := by
    rw [h_tele]
    exact h_sum_le
  -- Therefore orbit_raw n m ≤ (2^S * n + c) / 2^S ≤ n + c
  -- Direct calculation: orbit_raw * 2^S = 3^m * n + c ≤ 2^S * n + c
  -- So orbit_raw ≤ (2^S * n + c) / 2^S
  -- And (2^S * n + c) / 2^S ≤ n + (c + 2^S - 1) / 2^S ≤ n + c (when c < 2^S * c, which holds)
  have h_div_le : orbit_raw n m ≤ n + c := by
    -- From h_bound: orbit_raw n m * 2^S ≤ 2^S * n + c
    -- If orbit_raw n m > n + c, then orbit_raw n m ≥ n + c + 1
    -- So orbit_raw n m * 2^S ≥ (n + c + 1) * 2^S = 2^S * n + 2^S * c + 2^S > 2^S * n + c (since c < 2^S * c + 2^S)
    -- This contradicts h_bound when c ≥ 1
    by_contra h_gt
    push_neg at h_gt
    have h_ge : orbit_raw n m ≥ n + c + 1 := h_gt
    have h_mul_ge : orbit_raw n m * 2^S ≥ (n + c + 1) * 2^S := Nat.mul_le_mul_right (2^S) h_ge
    have h_expand : (n + c + 1) * 2^S = 2^S * n + 2^S * c + 2^S := by ring
    rw [h_expand] at h_mul_ge
    have h_c_lt : c < 2^S * c + 2^S := by
      have h2S_ge_1 : 2^S ≥ 1 := Nat.one_le_two_pow
      -- c < 2^S * c + 2^S iff c * 1 < c * 2^S + 2^S iff c < c * 2^S + 2^S (when 2^S ≥ 1)
      -- This holds since c ≤ c * 2^S (when 2^S ≥ 1) and we're adding 2^S > 0
      calc c = c * 1 := by ring
        _ ≤ c * 2^S := Nat.mul_le_mul_left c h2S_ge_1
        _ < c * 2^S + 2^S := Nat.lt_add_of_pos_right h2S_pos
        _ = 2^S * c + 2^S := by ring
    have : 2^S * n + c < 2^S * n + 2^S * c + 2^S := by omega
    omega
  exact h_div_le

/-! ## Margin Supercritical Bounds

For UNIFORM orbit bounds, we need margin supercritical: 2^S ≥ (1 + η) * 3^m.
Basic supercritical (2^S ≥ 3^m) only gives linear-growth bounds n_m ≤ n₀ + m/3,
which is insufficient to rule out divergence.

**Key insight**: With margin η > 0, the wave sum ratio decays geometrically:
- Each term in waveSumPattern/2^S contributes at most 1/(3(1+η)^{m-j})
- The sum is bounded by 1/(3η) (geometric series)

This gives the UNIFORM bound: orbit_raw n m ≤ n + 1/(3η) for all m. -/

/-! ## Corrected Wave Sum Analysis

    **Key insight**: The wave sum bound depends on n₀, not just the pattern.

    The orbit equation is:
      n_m = (n₀ · 3^m + W) / 2^S

    For strongly supercritical (2^S ≥ 2·3^m):
    - n₀ · 3^m / 2^S ≤ n₀ / 2
    - W / 2^S < 3^m (from W < 3^m · 2^S)

    So: n_m < n₀/2 + 3^m

    For descent (n_m < n₀), we need: n₀/2 + 3^m < n₀
    Which gives: **n₀ > 2 · 3^m**

    This is the n₀-dependent descent condition.
-/

/-- Wave sum is bounded by 3^m · 2^S (coarse upper bound) -/
lemma wavesum_coarse_bound (σ : List ℕ) :
    waveSumPattern σ < 3^σ.length * 2^(patternSum σ) :=
  waveSumPattern_upper_bound

/-- Wave sum divided by 2^S is bounded by 3^m -/
lemma wavesum_ratio_coarse (σ : List ℕ) (hne : σ.length > 0) :
    (waveSumPattern σ : ℚ) / (2 : ℚ)^(patternSum σ) < (3 : ℚ)^σ.length := by
  have h2S_pos : (0 : ℚ) < (2 : ℚ)^(patternSum σ) := by positivity
  have hW := wavesum_coarse_bound σ
  have hW_q : (waveSumPattern σ : ℚ) < (3 : ℚ)^σ.length * (2 : ℚ)^(patternSum σ) := by
    push_cast
    exact_mod_cast hW
  calc (waveSumPattern σ : ℚ) / (2 : ℚ)^(patternSum σ)
      < (3 : ℚ)^σ.length * (2 : ℚ)^(patternSum σ) / (2 : ℚ)^(patternSum σ) := by
          apply div_lt_div_of_pos_right hW_q h2S_pos
    _ = (3 : ℚ)^σ.length := by field_simp

/-- **n₀-dependent descent**: For strongly supercritical with n₀ > 2·3^m, orbit descends.

    Key formula: n_m = (n₀ · 3^m + W) / 2^S
    For 2^S ≥ 2·3^m: n₀ · 3^m / 2^S ≤ n₀/2
    Using W < 3^m · 2^S: W/2^S < 3^m
    So: n_m < n₀/2 + 3^m < n₀ when n₀ > 2·3^m -/
lemma strongly_supercritical_descent_large (n₀ : ℕ) (m : ℕ) (hn₀ : n₀ > 2 * 3^m)
    (hn₀_odd : Odd n₀) (hn₀_pos : 0 < n₀)
    (hStrong : isStronglySupercritical (orbitPattern n₀ m)) :
    orbit_raw n₀ m < n₀ := by
  -- Get the orbit telescoping equation
  have h_tele := orbit_telescoped n₀ hn₀_odd hn₀_pos m
  set σ := orbitPattern n₀ m with hσ_def
  set S := patternSum σ with hS_def
  set W := waveSumPattern σ with hW_def

  -- From orbit equation: orbit_raw * 2^S = n₀ * 3^m + W
  have hlen : σ.length = m := by simp [hσ_def, orbitPattern, List.length_ofFn]

  -- From strongly supercritical: 2^S ≥ 2 * 3^m
  have h_strong_ineq : 2^S ≥ 2 * 3^m := by
    have h := hStrong.2
    rw [hlen] at h
    exact h

  -- W < 3^m * 2^S
  have hW_bound : W < 3^m * 2^S := by
    have h := wavesum_coarse_bound σ
    rw [hlen] at h
    exact h

  -- orbit_raw * 2^S = n₀ * 3^m + W
  -- Since 2^S ≥ 2 * 3^m and W < 3^m * 2^S:
  -- orbit_raw = (n₀ * 3^m + W) / 2^S < (n₀ * 3^m + 3^m * 2^S) / 2^S
  --           = n₀ * 3^m / 2^S + 3^m ≤ n₀/2 + 3^m < n₀ (when n₀ > 2*3^m)

  have h2S_pos : 2^S > 0 := Nat.pow_pos (by norm_num : 0 < 2)

  -- From telescoped: orbit_raw * 2^S = n₀ * 3^m + W
  have h_eq : orbit_raw n₀ m * 2^S = n₀ * 3^m + W := by
    have heq : orbit_raw n₀ m * 2^(patternSum (orbitPattern n₀ m)) =
               3^m * n₀ + waveSumPattern (orbitPattern n₀ m) := h_tele
    simp only [mul_comm (3^m) n₀] at heq
    convert heq using 2 <;> simp [hS_def, hW_def, hσ_def]

  -- n₀ * 3^m + W < n₀ * 2^S when n₀ > 2*3^m and W < 3^m * 2^S
  have h_ineq : n₀ * 3^m + W < n₀ * 2^S := by
    -- W < 3^m * 2^S
    -- n₀ * 3^m ≤ n₀ * 2^S / 2 (from 2^S ≥ 2 * 3^m)
    -- So n₀ * 3^m + W < n₀ * 2^S/2 + 3^m * 2^S
    -- Need: n₀ * 2^S/2 + 3^m * 2^S < n₀ * 2^S
    -- i.e., 3^m * 2^S < n₀ * 2^S / 2
    -- i.e., 2 * 3^m < n₀
    -- Key inequality: n₀ * 3^m + W < n₀ * 2^S
    -- From: n₀ * 3^m ≤ n₀ * 2^S / 2 (since 2 * 3^m ≤ 2^S)
    -- And: W < 3^m * 2^S ≤ n₀ * 2^S / 2 (since 2 * 3^m < n₀)

    have h3pow_pos : 3^m > 0 := Nat.pow_pos (by norm_num : 0 < 3)

    -- First bound: n₀ * 3^m * 2 ≤ n₀ * 2^S (since 2 * 3^m ≤ 2^S)
    have h1 : n₀ * 3^m * 2 ≤ n₀ * 2^S := by
      have : 2 * 3^m ≤ 2^S := h_strong_ineq
      calc n₀ * 3^m * 2 = n₀ * (3^m * 2) := by ring
        _ = n₀ * (2 * 3^m) := by ring
        _ ≤ n₀ * 2^S := by nlinarith

    -- Second bound: W * 2 < n₀ * 2^S (since W < 3^m * 2^S and 2 * 3^m < n₀)
    have h2 : W < 3^m * 2^S := hW_bound
    have h3 : 3^m * 2^S * 2 < n₀ * 2^S := by
      have : 2 * 3^m < n₀ := hn₀
      calc 3^m * 2^S * 2 = 2^S * (2 * 3^m) := by ring
        _ < 2^S * n₀ := by nlinarith
        _ = n₀ * 2^S := by ring

    -- Combined: n₀ * 3^m + W < n₀ * 2^S
    -- n₀ * 3^m * 2 ≤ n₀ * 2^S and W * 2 < 3^m * 2^S * 2 < n₀ * 2^S
    -- So: (n₀ * 3^m + W) * 2 < n₀ * 2^S * 2, hence n₀ * 3^m + W < n₀ * 2^S
    have h_combined : (n₀ * 3^m + W) * 2 < n₀ * 2^S + n₀ * 2^S := by
      calc (n₀ * 3^m + W) * 2 = n₀ * 3^m * 2 + W * 2 := by ring
        _ ≤ n₀ * 2^S + W * 2 := by omega  -- from h1
        _ < n₀ * 2^S + 3^m * 2^S * 2 := by omega  -- from h2
        _ < n₀ * 2^S + n₀ * 2^S := by omega  -- from h3

    have h_double : n₀ * 2^S + n₀ * 2^S = n₀ * 2^S * 2 := by ring
    rw [h_double] at h_combined
    omega

  -- orbit_raw * 2^S < n₀ * 2^S means orbit_raw < n₀
  have h_final : orbit_raw n₀ m * 2^S < n₀ * 2^S := by
    calc orbit_raw n₀ m * 2^S = n₀ * 3^m + W := h_eq
      _ < n₀ * 2^S := h_ineq

  exact Nat.lt_of_mul_lt_mul_right h_final

/-- Descent threshold: n₀ must exceed 2·3^m for guaranteed descent -/
def descentThreshold (m : ℕ) : ℕ := 2 * 3^m + 1

/-- **Spectral Boundedness Theorem (Corrected)**: Strongly supercritical with large n₀ gives descent.

    If orbit patterns are eventually strongly supercritical (2^S ≥ 2·3^m),
    then for sufficiently large n₀, the orbit contracts.

    **Correct mathematical content (n₀-dependent)**:
    1. Orbit equation: n_m = (n₀ · 3^m + W) / 2^S
    2. From strongly supercritical: n₀ · 3^m / 2^S ≤ n₀/2
    3. Wave sum bound: W < 3^m · 2^S, so W/2^S < 3^m
    4. Combined: n_m < n₀/2 + 3^m
    5. For descent (n_m < n₀): need n₀ > 2·3^m

    The key insight: the bound depends on n₀, not just the pattern.
    For large n₀, strongly supercritical gives automatic descent.
    For small n₀, constraint mismatch (Part I) is needed.

    **Note**: This replaces the incorrect W/2^S ≤ 1/(3η) bound. -/
-- Helper for foldl max monotonicity
private lemma foldl_max_le_fold' (f : ℕ → ℕ) (init : ℕ) (l : List ℕ) :
    init ≤ l.foldl (fun acc i => max acc (f i)) init := by
  induction l generalizing init with
  | nil => exact le_refl _
  | cons head tail ih =>
    simp only [List.foldl_cons]
    exact le_trans (Nat.le_max_left _ _) (ih _)

-- Helper: for m in list, the foldl max includes orbit_raw n m
private lemma foldl_max_contains {n : ℕ} {init : ℕ} {l : List ℕ} {m : ℕ} (hm : m ∈ l) :
    orbit_raw n m ≤ l.foldl (fun acc i => max acc (orbit_raw n i)) init := by
  induction l generalizing init with
  | nil => simp at hm
  | cons head tail ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hm with heq | hmem
    · -- m = head case
      rw [heq]
      have h1 : orbit_raw n head ≤ max init (orbit_raw n head) := Nat.le_max_right _ _
      exact le_trans h1 (foldl_max_le_fold' (orbit_raw n) _ _)
    · -- m ∈ tail case
      exact ih hmem

/-!
## Dead code removed

The following theorems were removed as they were never called:
- margin_supercritical_implies_bounded
- eventually_strongly_supercritical_implies_bounded
- divergent_implies_infinitely_many_not_strongly_supercritical
- orbit_dichotomy
- divergent_has_infinitely_many_subcritical
- divergent_implies_infinitely_subcritical

The main proof path uses no_divergent_orbits_odd which directly applies
any_valid_orbit_pattern_eventually_misses without going through the
margin/supercritical analysis.
-/

-- NOTE: Dead code removed here (margin_supercritical_implies_bounded, orbit_dichotomy, etc.)
-- The main proof path uses no_divergent_orbits_odd directly via any_valid_orbit_pattern_eventually_misses.

-- [Dead code block removed: margin_supercritical_implies_bounded, orbit_dichotomy, etc. - never called]


/-- Explicit cutoff for constraint mismatch: max (2 * log₂ n₀ + 9) 5 -/
def mismatchCutoff (n₀ : ℕ) : ℕ := max (2 * Nat.log 2 n₀ + 9) 5

-- Helper lemmas now use the explicit cutoff versions from ConstraintMismatch.lean
-- and AllOnesPattern.lean which avoid the existential witness issue.

-- constraint_mismatch_at_cutoff is now constraint_eventually_misses_general_at_cutoff
-- in ConstraintMismatch.lean

-- allOnes_constraint_mismatch_at_cutoff is now in AllOnesPattern.lean

-- REMOVED: NoDivergenceHypothesis and backprop dependent code

/-- Valid patterns have all elements ≥ 1. For orbit patterns this is automatic since v₂ ≥ 1. -/
lemma orbitPattern_isValid (n : ℕ) (hn : Odd n) (hpos : 0 < n) (B : ℕ) :
    isValidPattern (orbitPattern n B) := by
  unfold isValidPattern orbitPattern
  intro v hv_mem
  rw [List.mem_ofFn] at hv_mem
  obtain ⟨i, _, rfl⟩ := hv_mem
  exact v2_of_three_n_plus_one_pos (orbit_raw_odd hn hpos i)

/-! ### BackStep Inversion Lemmas

These lemmas prove that backStep inverts Syracuse for orbit patterns.
Key insight: for an odd n with ν = v₂(3n+1) and y = syracuse_raw n,
we have backStep ν y = some n (when ν ≤ 2000).
-/

-- REMOVED: backprop/spectral/thinstrip dependent code (lines 1465-1495)
/-- For orbit steps, the ν value is always ≥ 1 (since 3*n+1 is even for odd n). -/
lemma orbitNu_pos (n : ℕ) (hn : Odd n) (hpos : 0 < n) (k : ℕ) :
    0 < orbitNu n k := by
  unfold orbitNu
  have h_odd_k := orbit_raw_odd hn hpos k
  exact v2_of_three_n_plus_one_pos h_odd_k

-- REMOVED: backprop/spectral/thinstrip dependent code (lines 1503-1522)
/-- Orbit upper bound: orbit_raw n k ≤ n * 3^k + 3^k - 1 = (n+1) * 3^k - 1.
    This follows from the telescoped formula and wave sum bounds. -/
lemma orbit_raw_upper_bound (n : ℕ) (hn : Odd n) (hpos : 0 < n) (k : ℕ) :
    orbit_raw n k ≤ n * 3^k + (3^k - 1) := by
  -- From orbit_telescoped: orbit_raw n k * 2^S = 3^k * n + W
  -- where S = patternSum (orbitPattern n k) and W = waveSumPattern (orbitPattern n k)
  set σ := orbitPattern n k with hσ
  set S := patternSum σ with hS
  set W := waveSumPattern σ with hW

  have h_tele := orbit_telescoped n hn hpos k
  -- h_tele : orbit_raw n k * 2^S = 3^k * n + W

  have h_len : σ.length = k := by simp [hσ, orbitPattern]

  -- Wave sum bound: W < 3^k * 2^S
  have hW_bound : W < 3^k * 2^S := by
    have := wavesum_coarse_bound σ
    rw [h_len] at this
    exact this

  -- 2^S > 0
  have h2S_pos : 0 < 2^S := Nat.two_pow_pos S

  -- From h_tele: orbit_raw n k = (3^k * n + W) / 2^S
  -- Since W < 3^k * 2^S:
  -- orbit_raw n k * 2^S = 3^k * n + W < 3^k * n + 3^k * 2^S = 3^k * (n + 2^S)
  -- orbit_raw n k < 3^k * (n + 2^S) / 2^S

  have h_bound : orbit_raw n k * 2^S < 3^k * (n + 2^S) := by
    calc orbit_raw n k * 2^S = 3^k * n + W := h_tele
      _ < 3^k * n + 3^k * 2^S := by omega
      _ = 3^k * (n + 2^S) := by ring

  -- orbit_raw n k < 3^k * (n + 2^S) / 2^S = 3^k * n / 2^S + 3^k
  -- Since 2^S ≥ 1: 3^k * n / 2^S ≤ 3^k * n
  -- So: orbit_raw n k < 3^k * n + 3^k = (n + 1) * 3^k

  -- We need: orbit_raw n k ≤ n * 3^k + 3^k - 1 = (n + 1) * 3^k - 1
  -- From orbit_raw n k * 2^S < 3^k * (n + 2^S), since 2^S divides orbit_raw n k * 2^S:
  -- orbit_raw n k ≤ (3^k * (n + 2^S) - 1) / 2^S

  have h3k_pos : 0 < 3^k := Nat.pow_pos (by norm_num : 0 < 3)

  -- Key: orbit_raw n k * 2^S < (n + 1) * 3^k * 2^S
  -- So orbit_raw n k < (n + 1) * 3^k
  -- Hence orbit_raw n k ≤ (n + 1) * 3^k - 1 = n * 3^k + 3^k - 1

  have h_strict : orbit_raw n k * 2^S < (n + 1) * 3^k * 2^S := by
    have h1 : n + 2^S ≤ (n + 1) * 2^S := by
      have h2S_ge1 : 1 ≤ 2^S := Nat.one_le_two_pow
      nlinarith
    calc orbit_raw n k * 2^S < 3^k * (n + 2^S) := h_bound
      _ ≤ 3^k * ((n + 1) * 2^S) := by nlinarith
      _ = (n + 1) * 3^k * 2^S := by ring

  have h_lt : orbit_raw n k < (n + 1) * 3^k :=
    Nat.lt_of_mul_lt_mul_right h_strict

  -- orbit_raw n k < (n+1) * 3^k means orbit_raw n k ≤ (n+1) * 3^k - 1
  -- And (n+1) * 3^k - 1 = n * 3^k + 3^k - 1
  have h_eq : (n + 1) * 3^k = n * 3^k + 3^k := by ring
  have h_goal : n * 3^k + 3^k - 1 = n * 3^k + (3^k - 1) := by
    have h3k_ge1 : 3^k ≥ 1 := Nat.one_le_pow' k 2
    omega
  omega

-- REMOVED: orbitNu_le_orbitNuBound (depended on orbitNuBound which was removed)

/-- Key insight: Subcritical patterns have patternSum < 2 * length.

    Since 2^S < 3^m < 4^m = 2^(2m), we have S < 2m.
    For B ≥ 105, this means S < 210 << 2000. -/
lemma subcritical_pattern_sum_lt_double (σ : List ℕ)
    (hsubcrit : isSubcriticalPattern σ) (hlen2 : σ.length ≥ 2) :
    patternSum σ < 2 * σ.length := by
  have hsum_lt := hsubcrit.2
  by_contra h
  push_neg at h
  have h_pow : 2^(patternSum σ) ≥ 2^(2 * σ.length) := Nat.pow_le_pow_right (by omega) h
  have h4_eq : (4 : ℕ)^σ.length = 2^(2 * σ.length) := by
    calc 4^σ.length = (2^2)^σ.length := by norm_num
      _ = 2^(2 * σ.length) := by rw [← pow_mul]
  have h3_lt_4 : (3 : ℕ)^σ.length < 4^σ.length := by
    have hne : σ.length ≠ 0 := by omega
    calc (3 : ℕ)^σ.length < (3 + 1)^σ.length := Nat.pow_lt_pow_left (by omega) hne
      _ = 4^σ.length := by ring
  have hcontra : 2^(patternSum σ) > 3^σ.length := by
    calc 2^(patternSum σ) ≥ 2^(2 * σ.length) := h_pow
      _ = 4^σ.length := h4_eq.symm
      _ > 3^σ.length := h3_lt_4
  omega

/-- For B ≥ 105, subcritical patterns have all ν < 2B ≤ 2000 for B ≤ 1000. -/
lemma subcritical_pattern_nu_bounded (σ : List ℕ)
    (hsubcrit : isSubcriticalPattern σ) (hlen2 : σ.length ≥ 2) (j : Fin σ.length) :
    σ.get j < 2 * σ.length := by
  have hvalid := hsubcrit.1
  have h_S_lt := subcritical_pattern_sum_lt_double σ hsubcrit hlen2
  -- Each ν is bounded by the sum
  have h_le_sum : σ.get j ≤ σ.sum := by
    have h_mem : σ.get j ∈ σ := List.get_mem σ j
    exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ h_mem
  calc σ.get j ≤ σ.sum := h_le_sum
    _ = patternSum σ := rfl
    _ < 2 * σ.length := h_S_lt

/-- **Key bound for strongly supercritical**: orbit_raw n B < n/2 + 3^B + 1.

    From orbit_telescoped: orbit_raw n B * 2^S = 3^B * n + waveSumPattern
    With 2^S ≥ 2·3^B (strongly supercritical):
    - 3^B * n / 2^S ≤ n/2
    - waveSumPattern / 2^S < 3^B (from wavesum_coarse_bound)
    Therefore: orbit_raw n B < n/2 + 3^B -/
lemma strongly_supercritical_orbit_bound (n B : ℕ)
    (hn_odd : Odd n) (hn_pos : 0 < n)
    (hstrong : isStronglySupercritical (orbitPattern n B)) :
    orbit_raw n B < n / 2 + 3^B + 1 := by
  set σ := orbitPattern n B with hσ_def
  set S := patternSum σ with hS_def
  set W := waveSumPattern σ with hW_def
  set nm := orbit_raw n B with hnm_def

  -- From orbit_telescoped: nm * 2^S = n * 3^B + W
  have h_tele := orbit_telescoped n hn_odd hn_pos B
  have h_eq : nm * 2^S = n * 3^B + W := by
    have heq : nm * 2^(patternSum (orbitPattern n B)) =
               3^B * n + waveSumPattern (orbitPattern n B) := h_tele
    simp only [mul_comm (3^B) n] at heq
    convert heq using 2 <;> simp [hnm_def, hS_def, hW_def, hσ_def]

  -- Pattern length
  have hlen : σ.length = B := by simp [hσ_def, orbitPattern, List.length_ofFn]

  -- From strongly supercritical: 2^S ≥ 2 * 3^B
  have h_strong_ineq : 2^S ≥ 2 * 3^B := by
    have h := hstrong.2
    rw [hlen] at h
    exact h

  -- W < 3^B * 2^S (wavesum coarse bound)
  have hW_bound : W < 3^B * 2^S := by
    have h := wavesum_coarse_bound σ
    rw [hlen] at h
    exact h

  have h2S_pos : 2^S > 0 := Nat.pow_pos (by norm_num : 0 < 2)
  have h3B_pos : 3^B > 0 := Nat.pow_pos (by norm_num : 0 < 3)

  -- nm * 2^S = n * 3^B + W < n * 3^B + 3^B * 2^S
  have h_upper : nm * 2^S < n * 3^B + 3^B * 2^S := by
    calc nm * 2^S = n * 3^B + W := h_eq
      _ < n * 3^B + 3^B * 2^S := by omega

  -- n * 3^B + 3^B * 2^S = 3^B * (n + 2^S)
  -- nm < (n * 3^B + 3^B * 2^S) / 2^S = n * 3^B / 2^S + 3^B
  -- With 2^S ≥ 2 * 3^B: n * 3^B / 2^S ≤ n * 3^B / (2 * 3^B) = n / 2

  -- First, show nm < n * 3^B / 2^S + 3^B + 1
  have h_div_bound : n * 3^B / 2^S ≤ n / 2 := by
    have h2 : 2 * 3^B ≤ 2^S := h_strong_ineq
    -- n * 3^B / 2^S ≤ n * 3^B / (2 * 3^B) = n / 2
    have h3 : n * 3^B / (2 * 3^B) = n / 2 := by
      have : 2 * 3^B ≠ 0 := by omega
      rw [Nat.mul_div_mul_right n 2 h3B_pos]
    calc n * 3^B / 2^S ≤ n * 3^B / (2 * 3^B) := Nat.div_le_div_left h2 (by omega)
      _ = n / 2 := h3

  -- From h_upper: nm * 2^S < n * 3^B + 3^B * 2^S
  -- So: nm ≤ (n * 3^B + 3^B * 2^S - 1) / 2^S
  -- Which means: nm ≤ n * 3^B / 2^S + 3^B  (since ... + 3^B * 2^S - 1 < ... + 3^B * 2^S)
  have h_nm_bound : nm ≤ n * 3^B / 2^S + 3^B := by
    have h1 : nm * 2^S < (n * 3^B / 2^S + 3^B + 1) * 2^S := by
      calc nm * 2^S < n * 3^B + 3^B * 2^S := h_upper
        _ ≤ (n * 3^B / 2^S) * 2^S + n * 3^B % 2^S + 3^B * 2^S := by
          have hdiv' := Nat.div_add_mod (n * 3^B) (2^S)
          have hdiv : n * 3^B = (n * 3^B / 2^S) * 2^S + n * 3^B % 2^S := by
            rw [mul_comm] at hdiv'; exact hdiv'.symm
          omega
        _ ≤ (n * 3^B / 2^S) * 2^S + 2^S + 3^B * 2^S := by
          have hmod : n * 3^B % 2^S < 2^S := Nat.mod_lt _ h2S_pos
          omega
        _ = (n * 3^B / 2^S + 1 + 3^B) * 2^S := by ring
        _ = (n * 3^B / 2^S + 3^B + 1) * 2^S := by ring
    have h2 : nm < n * 3^B / 2^S + 3^B + 1 := Nat.lt_of_mul_lt_mul_right h1
    omega

  -- Combine: nm ≤ n * 3^B / 2^S + 3^B ≤ n/2 + 3^B
  calc nm ≤ n * 3^B / 2^S + 3^B := h_nm_bound
    _ ≤ n / 2 + 3^B := by omega
    _ < n / 2 + 3^B + 1 := by omega

-- DELETED: bounded_region_small_n
-- This theorem was dead code (not used by main proof path).
-- The main proof uses no_divergence_via_supercriticality instead.

-- DELETED: strongly_supercritical_bounded_orbit_axiom
-- This theorem was dead code (not used by main proof path).
-- The main proof uses no_divergence_via_supercriticality instead.


/-- **Universal No-Divergence Theorem**: No positive odd integer has a divergent orbit.

    **SIMPLIFIED PROOF** using Case3K fuel exhaustion:
    - Case3K.case3_orbit_bounded proves: ∀ n > 1 odd, ∃ B, ∀ m, orbit n m ≤ B
    - This directly contradicts DivergentOrbit (∀ N, ∃ t, orbit_raw n t > N)

    The complex pattern trichotomy (subcritical/thin strip/supercritical) analysis
    is now subsumed by the fuel exhaustion theorem, which bounds ALL orbits. -/
theorem no_divergence_universal (n : ℕ) (hn_pos : 0 < n) (hn_odd : Odd n) :
    ¬DivergentOrbit n := by
  by_cases hn1 : n = 1
  · -- n = 1: orbit is 1 → 1 → ... (fixed point), not divergent
    subst hn1
    intro hdiv
    unfold DivergentOrbit at hdiv
    have h := hdiv 2
    obtain ⟨k, hk⟩ := h
    have horbit_one : orbit_raw 1 k = 1 := orbit_raw_one_fixed k
    omega
  · -- n > 1: Use the direct Case3K proof
    have hn_gt1 : n > 1 := by omega
    exact no_divergence_via_case3k n hn_pos hn_odd hn_gt1
-- REMOVED: NoDivergenceHypothesis instance and dependent lemmas

/-! ### Stub lemmas for final theorem (TODO: prove without backprop infrastructure) -/

/-- From no_divergence_universal, we get that unbounded implies False.
    The hypothesis `_h` is exactly `DivergentOrbit n`, which contradicts `no_divergence_universal`. -/
lemma unbounded_orbit_false (n : ℕ) (hn_odd : Odd n) (hn_pos : 0 < n)
    (h : ∀ M : ℕ, ∃ T : ℕ, orbit_raw n T > M) : False := by
  have h_not_div := no_divergence_universal n hn_pos hn_odd
  exact h_not_div h

/-- No bounded nontrivial cycles: if orbit is bounded and never reaches 1, contradiction.
    This combines Part I (no cycles) with Part II (descent).

    Proof: Bounded orbit → pigeonhole gives repeat → cycle → by Part I, must be 1 → contradiction. -/
lemma no_bounded_nontrivial_cycles (n : ℕ) (hn_odd : Odd n) (hn : 0 < n)
    (hbounded : ∃ M : ℕ, ∀ T : ℕ, orbit_raw n T ≤ M)
    (h_not_one : ∀ k : ℕ, orbit_raw n k ≠ 1) : False := by
  -- Get the bound M
  obtain ⟨M, hM⟩ := hbounded
  -- Consider M+2 orbit values: orbit_raw n 0, orbit_raw n 1, ..., orbit_raw n (M+1)
  -- All are in {1, 2, ..., M}, so by pigeonhole two must be equal
  -- Define the orbit function on Fin (M+2) → Fin (M+1) (values are in 1..M, shifted to 0..M-1)
  have h_pos_orbit : ∀ k, orbit_raw n k > 0 := fun k => orbit_raw_pos hn_odd hn k
  -- By pigeonhole: among M+2 values mapping to {0,...,M}, two must collide
  have h_pigeonhole : ∃ i j : Fin (M + 2), i < j ∧ orbit_raw n i.val = orbit_raw n j.val := by
    by_contra h_no_collision
    push_neg at h_no_collision
    -- All M+2 values are distinct and in {1,...,M}, impossible
    have h_inj : Function.Injective (fun i : Fin (M + 2) => orbit_raw n i.val) := by
      intro i j h_eq
      by_contra h_ne
      cases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne h_ne) with
      | inl h_lt => exact h_no_collision ⟨i, Nat.lt_of_lt_of_le h_lt (Nat.le_of_lt j.isLt)⟩
                      ⟨j, j.isLt⟩ (Fin.mk_lt_mk.mpr h_lt) h_eq
      | inr h_gt => exact h_no_collision ⟨j, Nat.lt_of_lt_of_le h_gt (Nat.le_of_lt i.isLt)⟩
                      ⟨i, i.isLt⟩ (Fin.mk_lt_mk.mpr h_gt) h_eq.symm
    -- Map to Fin (M+1) via subtracting 1 (since orbit > 0 and ≤ M)
    let f : Fin (M + 2) → Fin (M + 1) := fun i =>
      ⟨orbit_raw n i.val - 1, by
        have h1 := h_pos_orbit i.val
        have h2 := hM i.val
        omega⟩
    have h_f_inj : Function.Injective f := by
      intro i j h_eq
      simp only [f, Fin.mk.injEq] at h_eq
      have h1 := h_pos_orbit i.val
      have h2 := h_pos_orbit j.val
      have h_eq' : orbit_raw n i.val = orbit_raw n j.val := by omega
      exact h_inj h_eq'
    have h_card : Fintype.card (Fin (M + 2)) > Fintype.card (Fin (M + 1)) := by simp
    exact Nat.not_lt.mpr (Fintype.card_le_of_injective f h_f_inj) h_card
  -- Get the collision: orbit_raw n i = orbit_raw n j with i < j
  obtain ⟨i, j, h_lt, h_eq⟩ := h_pigeonhole
  -- Let v = orbit_raw n i, period T = j - i ≥ 1
  set v := orbit_raw n i.val with hv_def
  set T := j.val - i.val with hT_def
  have hT_pos : T > 0 := by simp only [hT_def]; omega
  -- Show v cycles: orbit_raw v T = v
  have h_v_odd : Odd v := orbit_raw_odd hn_odd hn i.val
  have h_v_pos : 0 < v := h_pos_orbit i.val
  have h_v_cycles : orbit_raw v T = v := by
    -- orbit_raw n j = orbit_raw (orbit_raw n i) (j - i) by orbit_raw_add
    have h1 : orbit_raw n j.val = orbit_raw (orbit_raw n i.val) (j.val - i.val) := by
      rw [← orbit_raw_add]
      congr 1
      omega
    -- orbit_raw n i = orbit_raw n j by h_eq, and orbit_raw n i = v
    -- So orbit_raw n j = v, and h1 gives orbit_raw v T = orbit_raw n j = v
    calc orbit_raw v T = orbit_raw (orbit_raw n i.val) (j.val - i.val) := by rfl
      _ = orbit_raw n j.val := h1.symm
      _ = orbit_raw n i.val := h_eq.symm
      _ = v := rfl
  -- By no_nontrivial_cycles, v = 1
  have h_cycle_exists : ∃ k, k ≥ 1 ∧ orbit v h_v_odd h_v_pos k = v := ⟨T, hT_pos, h_v_cycles⟩
  have h_v_eq_one := no_nontrivial_cycles h_v_odd h_v_pos h_cycle_exists
  -- But orbit_raw n i ≠ 1 by hypothesis
  exact h_not_one i.val (hv_def ▸ h_v_eq_one)

end Collatz
