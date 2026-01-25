/-
Copyright (c) 2024. All rights reserved.
Released under MIT license.
-/
import Collatz.Basic
import Collatz.PartI
/- import Collatz.PartII -/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Collatz Conjecture - Core Pattern Definitions

This file contains the core definitions for Collatz patterns used in the
divergence impossibility proof (Part IIb).

## Main Definitions

- `residueTower`: The residue tower n₀ mod 2^k
- `residueTower_stabilizes`: Tower stabilizes once k > log₂(n₀)
- `patternSum`: Sum of ν-values in a pattern
- `isValidPattern`: Valid patterns have all ν ≥ 1
- `isSubcriticalPattern`: Subcritical patterns satisfy 2^S < 3^m
- `partialNuSum`: Partial sum of ν-values
- `waveSumPattern`: Wave sum c_σ = Σⱼ 3^{m-1-j} · 2^{S_j}
- `patternConstraint`: Constraint value a_σ ∈ ZMod(2^S)
- `F`: Set of n₀ that can produce m-step subcritical orbits

## Key Results

- `valid_pattern_sum_ge_length`: Sum of valid pattern ≥ length
- `subcritical_sum_grows`: For large m, subcritical patterns have large S
- `constraint_match_iff`: Characterization of constraint matching
-/

namespace Collatz

open scoped BigOperators

/-!
## Section 1: The Residue Tower

For a fixed n₀ ∈ ℕ⁺, define its residue tower:
  r_k(n₀) := n₀ mod 2^k

Key property: the tower **stabilizes** at k₀ = ⌊log₂(n₀)⌋ + 1.
For k ≥ k₀, we have r_k(n₀) = n₀.
-/

/-- The residue tower: n₀ viewed modulo 2^k -/
def residueTower (n₀ : ℕ) (k : ℕ) : ZMod (2^k) := n₀

/-- The stabilization depth: smallest k such that 2^k > n₀ -/
noncomputable def stabilizationDepth (n₀ : ℕ) : ℕ :=
  if n₀ = 0 then 0 else Nat.log 2 n₀ + 1

/-- Once k exceeds stabilization depth, the residue equals n₀ -/
lemma residueTower_stabilizes {n₀ : ℕ} (hn₀ : 0 < n₀) (k : ℕ)
    (hk : stabilizationDepth n₀ ≤ k) :
    (residueTower n₀ k).val = n₀ := by
  unfold residueTower stabilizationDepth at *
  simp only [hn₀.ne', ↓reduceIte] at hk
  have h2k : 2^k > n₀ := by
    have hlog : n₀ < 2^(Nat.log 2 n₀ + 1) := Nat.lt_pow_succ_log_self (by omega) n₀
    calc n₀ < 2^(Nat.log 2 n₀ + 1) := hlog
         _ ≤ 2^k := Nat.pow_le_pow_right (by omega) hk
  simp only [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt h2k

/-!
## Section 2: Pattern Definitions
-/

/-- The ν-sum for a pattern: total bits consumed -/
def patternSum (σ : List ℕ) : ℕ := σ.sum

/-- A valid Collatz pattern: each ν ≥ 1 (since 3n+1 is always even for odd n) -/
def isValidPattern (σ : List ℕ) : Prop :=
  ∀ ν ∈ σ, ν ≥ 1

/-- Sum of a valid pattern is at least its length -/
lemma valid_pattern_sum_ge_length {σ : List ℕ} : isValidPattern σ → patternSum σ ≥ σ.length := by
  induction σ with
  | nil => simp [patternSum]
  | cons ν rest ih =>
    intro h
    simp only [patternSum, List.sum_cons, List.length_cons]
    rw [isValidPattern, List.forall_mem_cons] at h
    obtain ⟨hν, hrest⟩ := h
    have ih' : rest.sum ≥ rest.length := ih hrest
    have hν' : ν ≥ 1 := hν
    linarith

/-- A pattern σ of length m is subcritical if S < m · log₂3.
    We use the integer condition: 3^m > 2^S (equivalently 2^S < 3^m) -/
def isSubcriticalPattern (σ : List ℕ) : Prop :=
  isValidPattern σ ∧ 2^(patternSum σ) < 3^(σ.length)

/-- A pattern σ is supercritical if 2^S ≥ 3^m (the complement of subcritical for valid patterns) -/
def isSupercritical (σ : List ℕ) : Prop :=
  isValidPattern σ ∧ 2^(patternSum σ) ≥ 3^(σ.length)

/-- A pattern is all-ones if it is valid and every element equals 1.
    Equivalently, valid with sum = length (proven in AllOnesPattern.lean). -/
def isAllOnesPattern (σ : List ℕ) : Prop :=
  isValidPattern σ ∧ σ.all (· = 1)

/-- BadBlockS: A "bad" ν-block that must eventually be forbidden.
    Parameterized by Sset (spectral bad patterns).

    A block is bad if it is:
    - Subcritical with S > m (proper subcritical), OR
    - All-ones (special subcritical case S = m), OR
    - In the spectral bad set Sset

    All three cases are eventually forbidden by ZMod/constraint arguments. -/
def BadBlockS (Sset : List ℕ → Prop) (σ : List ℕ) : Prop :=
  (isSubcriticalPattern σ ∧ patternSum σ > σ.length) ∨
  isAllOnesPattern σ ∨
  Sset σ

/-- η-margin supercritical: 2^S ≥ (1 + η) * 3^m for rational η > 0.
    This gives UNIFORM orbit bounds, unlike basic supercritical which only gives
    linear-growth bounds. The margin creates geometric decay in wave sum terms. -/
def isMarginSupercritical (σ : List ℕ) (η : ℚ) : Prop :=
  isValidPattern σ ∧ (2 : ℚ)^(patternSum σ) ≥ (1 + η) * (3 : ℚ)^(σ.length)

/-- Integer version: strongly supercritical means 2^S ≥ 2 * 3^m
    This is isMarginSupercritical with η = 1, but using integer arithmetic. -/
def isStronglySupercritical (σ : List ℕ) : Prop :=
  isValidPattern σ ∧ 2^(patternSum σ) ≥ 2 * 3^(σ.length)

/-- Strongly supercritical implies margin supercritical with η = 1 -/
lemma stronglySupercritical_implies_margin (σ : List ℕ) :
    isStronglySupercritical σ → isMarginSupercritical σ 1 := by
  intro ⟨hvalid, hstrong⟩
  constructor
  · exact hvalid
  · simp only [one_add_one_eq_two]
    -- hstrong: 2^S ≥ 2 * 3^m (in ℕ)
    -- goal: (2:ℚ)^S ≥ 2 * (3:ℚ)^m
    have hnat : 2^(patternSum σ) ≥ 2 * 3^(σ.length) := hstrong
    -- Cast to ℚ and use monotonicity
    calc (2 : ℚ)^(patternSum σ) = ((2 : ℕ)^(patternSum σ) : ℚ) := by norm_cast
      _ ≥ ((2 * 3^(σ.length) : ℕ) : ℚ) := by exact_mod_cast hnat
      _ = 2 * (3 : ℚ)^(σ.length) := by norm_cast

/-- Partial sum of ν-values up to position j (exclusive) -/
def partialNuSum (σ : List ℕ) (j : ℕ) : ℕ :=
  (σ.take j).sum

/-- Partial ν-sum at position 0 equals 0 -/
@[simp]
lemma partialNuSum_zero (σ : List ℕ) : partialNuSum σ 0 = 0 := by
  simp [partialNuSum]

/-- Wave sum c_σ = Σⱼ 3^{m-1-j} · 2^{S_j} for a ν-pattern σ of length m.
    This is the "path constant" from the orbit equation n_m = (3^m · n₀ + c_σ) / 2^{S_m}. -/
def waveSumPattern (σ : List ℕ) : ℕ :=
  List.range σ.length |>.map (fun j => 3^(σ.length - 1 - j) * 2^(partialNuSum σ j)) |>.sum

/-- The constraint value a_σ ∈ ZMod(2^{S_m}) for a pattern σ.
    From the orbit equation: n_m = (3^m · n₀ + c_σ) / 2^{S_m}
    For integrality: 3^m · n₀ ≡ -c_σ (mod 2^{S_m})
    So: n₀ ≡ -c_σ · (3^m)^{-1} (mod 2^{S_m})

    Since gcd(3, 2) = 1, the inverse exists. -/
noncomputable def patternConstraint (σ : List ℕ) : ZMod (2^(patternSum σ)) :=
  let m := σ.length
  let S := patternSum σ
  let c := waveSumPattern σ
  let three_pow_m : ZMod (2^S) := (3^m : ℕ)
  let neg_c : ZMod (2^S) := -(c : ZMod (2^S))
  neg_c * three_pow_m⁻¹

/-- Algebraic bridge: equality of `patternConstraint` with an integer `n₀`
    is equivalent to a congruence on the wave sum.

    This lemma bridges between:
    - The constraint form: n₀ = patternConstraint σ (in ZMod)
    - The wave sum form: waveSumPattern σ ≡ -n₀ * 3^m (mod 2^S)

    The equivalence comes from multiplying by 3^m (which has an inverse since gcd(3,2)=1). -/
lemma constraint_eq_iff_waveSum (n₀ : ℕ) (σ : List ℕ) :
    (n₀ : ZMod (2^(patternSum σ))) = patternConstraint σ ↔
    (waveSumPattern σ : ZMod (2^(patternSum σ))) =
      -(n₀ : ZMod (2^(patternSum σ))) * ((3^σ.length : ℕ) : ZMod (2^(patternSum σ))) := by
  -- Abbreviate types for clarity
  set S := patternSum σ
  set m := σ.length
  set c := waveSumPattern σ
  set pow3m : ZMod (2^S) := ((3^m : ℕ) : ZMod (2^S))

  -- 3^m is a unit in ZMod(2^S) since gcd(3,2) = 1
  have h3_coprime : Nat.Coprime (3^m) (2^S) := by
    exact Nat.Coprime.pow_left m (Nat.Coprime.pow_right S (by decide : Nat.Coprime 3 2))
  have h_unit : IsUnit pow3m := by
    rw [ZMod.isUnit_iff_coprime]
    exact h3_coprime

  -- Key inverse properties
  have hinv_l : pow3m⁻¹ * pow3m = 1 := ZMod.inv_mul_of_unit pow3m h_unit
  have hinv_r : pow3m * pow3m⁻¹ = 1 := ZMod.mul_inv_of_unit pow3m h_unit

  unfold patternConstraint
  simp only []
  constructor
  · intro h
    -- n₀ = -c * (3^m)⁻¹ in ZMod
    -- Multiply both sides by 3^m: n₀ * 3^m = -c
    -- So c = -n₀ * 3^m
    have h' := congrArg (· * pow3m) h
    simp only at h'
    -- h' : ↑n₀ * pow3m = -↑c * pow3m⁻¹ * pow3m
    have key : (c : ZMod (2^S)) = -(n₀ : ZMod (2^S)) * pow3m := by
      have step1 : -(c : ZMod (2^S)) * pow3m⁻¹ * pow3m = -(c : ZMod (2^S)) := by
        calc -(c : ZMod (2^S)) * pow3m⁻¹ * pow3m
            = -(c : ZMod (2^S)) * (pow3m⁻¹ * pow3m) := by ring
          _ = -(c : ZMod (2^S)) * 1 := by rw [hinv_l]
          _ = -(c : ZMod (2^S)) := by ring
      have step2 : (n₀ : ZMod (2^S)) * pow3m = -(c : ZMod (2^S)) := by
        calc (n₀ : ZMod (2^S)) * pow3m = -(c : ZMod (2^S)) * pow3m⁻¹ * pow3m := h'
          _ = -(c : ZMod (2^S)) := step1
      calc (c : ZMod (2^S)) = -(-((c : ZMod (2^S)))) := by ring
        _ = -((n₀ : ZMod (2^S)) * pow3m) := by rw [← step2]
        _ = -(n₀ : ZMod (2^S)) * pow3m := by ring
    exact key
  · intro h
    -- c = -n₀ * 3^m in ZMod
    -- Multiply both sides by (3^m)⁻¹: c * (3^m)⁻¹ = -n₀
    -- So n₀ = -c * (3^m)⁻¹ = patternConstraint σ
    have h' := congrArg (· * pow3m⁻¹) h
    simp only at h'
    -- h' : ↑c * pow3m⁻¹ = -↑n₀ * pow3m * pow3m⁻¹
    have key : (n₀ : ZMod (2^S)) = -(c : ZMod (2^S)) * pow3m⁻¹ := by
      have step1 : -(n₀ : ZMod (2^S)) * pow3m * pow3m⁻¹ = -(n₀ : ZMod (2^S)) := by
        calc -(n₀ : ZMod (2^S)) * pow3m * pow3m⁻¹
            = -(n₀ : ZMod (2^S)) * (pow3m * pow3m⁻¹) := by ring
          _ = -(n₀ : ZMod (2^S)) * 1 := by rw [hinv_r]
          _ = -(n₀ : ZMod (2^S)) := by ring
      have step2 : (c : ZMod (2^S)) * pow3m⁻¹ = -(n₀ : ZMod (2^S)) := by
        calc (c : ZMod (2^S)) * pow3m⁻¹ = -(n₀ : ZMod (2^S)) * pow3m * pow3m⁻¹ := h'
          _ = -(n₀ : ZMod (2^S)) := step1
      calc (n₀ : ZMod (2^S)) = -(-(n₀ : ZMod (2^S))) := by ring
        _ = -((c : ZMod (2^S)) * pow3m⁻¹) := by rw [← step2]
        _ = -(c : ZMod (2^S)) * pow3m⁻¹ := by ring
    exact key

/-- F_m: the set of n₀ ∈ ℕ⁺ that can produce an m-step subcritical orbit -/
def F (m : ℕ) : Set ℕ :=
  {n₀ | 0 < n₀ ∧ ∃ (σ : List ℕ),
    σ.length = m ∧
    isSubcriticalPattern σ ∧
    (n₀ : ZMod (2^(patternSum σ))) = patternConstraint σ}

/-!
## Section 3: Key Properties
-/

/-- Key lemma: For any n₀ > 0, large m forces the pattern sum S to exceed log₂(n₀) -/
lemma subcritical_sum_grows {n₀ : ℕ} (_hn₀ : 0 < n₀) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ σ : List ℕ,
      σ.length = m → isSubcriticalPattern σ → patternSum σ > Nat.log 2 n₀ := by
  use Nat.log 2 n₀ + 1
  intro m hm σ hlen ⟨hvalid, _⟩
  have hS_ge_m : patternSum σ ≥ m := by
    rw [← hlen]
    exact valid_pattern_sum_ge_length hvalid
  omega

/-- Partial sum at position j+1 equals partial sum at j plus σ[j] -/
lemma partialNuSum_succ {σ : List ℕ} {j : ℕ} (hj : j < σ.length) :
    partialNuSum σ (j + 1) = partialNuSum σ j + σ[j] := by
  unfold partialNuSum
  rw [List.take_add_one]
  simp only [List.getElem?_eq_getElem hj, Option.toList_some, List.sum_append, List.sum_singleton]

/-- Partial sum at length equals pattern sum -/
@[simp]
lemma partialNuSum_length (σ : List ℕ) : partialNuSum σ σ.length = patternSum σ := by
  unfold partialNuSum patternSum
  rw [List.take_length]

/-- Pattern sum of concatenation -/
lemma patternSum_append (σ₁ σ₂ : List ℕ) :
    patternSum (σ₁ ++ σ₂) = patternSum σ₁ + patternSum σ₂ := by
  simp [patternSum]

/-- Pattern sum of singleton -/
@[simp]
lemma patternSum_singleton (ν : ℕ) : patternSum [ν] = ν := by simp [patternSum]

/-- Partial sum for extended pattern (for indices within original) -/
lemma partialNuSum_append_left {σ : List ℕ} {ν : ℕ} {j : ℕ} (hj : j ≤ σ.length) :
    partialNuSum (σ ++ [ν]) j = partialNuSum σ j := by
  unfold partialNuSum
  rw [List.take_append_of_le_length hj]

/-- Wave sum recurrence: waveSumPattern(σ ++ [ν]) = 3 * waveSumPattern(σ) + 2^{patternSum σ}

    This is the key recurrence for telescoping.
    For σ of length m with sum S, appending ν gives length m+1:
      c_{σ++[ν]} = ∑_{j=0}^{m} 3^{m-j} · 2^{S'_j}
    where S'_j = partialNuSum(σ++[ν], j) = partialNuSum(σ, j) for j ≤ m.

    Split: = (∑_{j=0}^{m-1} 3^{m-j} · 2^{S_j}) + 3^0 · 2^{S_m}
           = 3 · (∑_{j=0}^{m-1} 3^{m-1-j} · 2^{S_j}) + 2^S
           = 3 · c_σ + 2^S -/
lemma waveSumPattern_append (σ : List ℕ) (ν : ℕ) :
    waveSumPattern (σ ++ [ν]) = 3 * waveSumPattern σ + 2^(patternSum σ) := by
  unfold waveSumPattern
  simp only [List.length_append, List.length_singleton]
  set m := σ.length
  -- The range is [0, 1, ..., m] which we split into [0, ..., m-1] and [m]
  rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]

  -- The last term: 3^{m-m} · 2^{partialNuSum (σ++[ν]) m} = 1 · 2^{patternSum σ}
  have h_last : 3^(m + 1 - 1 - m) * 2^(partialNuSum (σ ++ [ν]) m) = 2^(patternSum σ) := by
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
    rw [partialNuSum_append_left (le_refl m), partialNuSum_length]

  -- The first sum: each term is 3 times the corresponding term in waveSumPattern σ
  have h_first : ((List.range m).map fun j => 3^(m + 1 - 1 - j) * 2^(partialNuSum (σ ++ [ν]) j)).sum
                 = 3 * ((List.range m).map fun j => 3^(m - 1 - j) * 2^(partialNuSum σ j)).sum := by
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro j hj
    simp only [List.mem_range] at hj
    -- 3^{m-j} = 3 * 3^{m-1-j}
    have h_exp : 3^(m + 1 - 1 - j) = 3 * 3^(m - 1 - j) := by
      have h : m + 1 - 1 - j = (m - 1 - j) + 1 := by omega
      rw [h, pow_succ]; ring
    -- partialNuSum is the same for j ≤ m
    have h_partial : partialNuSum (σ ++ [ν]) j = partialNuSum σ j :=
      partialNuSum_append_left (by omega)
    rw [h_exp, h_partial]; ring

  rw [h_first, h_last]

/-- Helper: for n₀ to match a pattern constraint, the wave sum must satisfy
    waveSumPattern σ ≡ -n₀ · 3^m (mod 2^S) -/
lemma constraint_match_iff {σ : List ℕ} {n₀ : ℕ} :
    (n₀ : ZMod (2^(patternSum σ))) = patternConstraint σ ↔
    (waveSumPattern σ : ZMod (2^(patternSum σ))) =
      -(n₀ : ZMod (2^(patternSum σ))) * (3^σ.length : ℕ) := by
  unfold patternConstraint
  simp only
  set S := patternSum σ
  set m := σ.length
  set c := waveSumPattern σ
  -- Key: 3^m is coprime to 2^S, so invertible
  have h_coprime : Nat.Coprime (3^m) (2^S) := by
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.pow_left
    decide
  have h_isunit : IsUnit ((3^m : ℕ) : ZMod (2^S)) := (ZMod.unitOfCoprime (3^m) h_coprime).isUnit
  have h_inv_mul : ((3^m : ℕ) : ZMod (2^S))⁻¹ * ((3^m : ℕ) : ZMod (2^S)) = 1 :=
    ZMod.inv_mul_of_unit _ h_isunit
  have h_mul_inv : ((3^m : ℕ) : ZMod (2^S)) * ((3^m : ℕ) : ZMod (2^S))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ h_isunit
  constructor
  · -- Forward: If n₀ = -c · (3^m)^{-1}, then c = -n₀ · 3^m
    intro h
    -- Multiply both sides by 3^m
    have h1 : (n₀ : ZMod (2^S)) * (3^m : ℕ) = -(c : ZMod (2^S)) * ((3^m : ℕ) : ZMod (2^S))⁻¹ * (3^m : ℕ) := by
      rw [h]
    -- (3^m)^{-1} * 3^m = 1
    rw [mul_assoc, h_inv_mul, mul_one] at h1
    -- h1 now says: n₀ * 3^m = -c
    -- Goal: c = -n₀ * 3^m, i.e., c = -(n₀ * 3^m)
    -- From h1: n₀ * 3^m = -c, so -(n₀ * 3^m) = --c = c
    have h2 : (c : ZMod (2^S)) = -((n₀ : ZMod (2^S)) * (3^m : ℕ)) := by
      rw [h1]; ring
    rw [h2]; ring
  · -- Backward: If c = -n₀ · 3^m, then n₀ = -c · (3^m)^{-1}
    intro h
    -- From c = -n₀ · 3^m, multiply by (3^m)^{-1}
    have h1 : (c : ZMod (2^S)) * ((3^m : ℕ) : ZMod (2^S))⁻¹ =
              -(n₀ : ZMod (2^S)) * (3^m : ℕ) * ((3^m : ℕ) : ZMod (2^S))⁻¹ := by
      rw [h]
    rw [mul_assoc, h_mul_inv, mul_one] at h1
    -- h1 now says: c * (3^m)⁻¹ = -n₀
    -- Goal: n₀ = -c · (3^m)^{-1}
    have h2 : (n₀ : ZMod (2^S)) = -((c : ZMod (2^S)) * ((3^m : ℕ) : ZMod (2^S))⁻¹) := by
      rw [h1]; ring
    rw [h2]; ring

end Collatz
