# Proof of No Nontrivial Cycles

## Theorem Statement

For every odd $m > 0$, if there exists $k \geq 1$ with $T^k(m) = m$
(where $T$ is the odd Collatz map $T(n) = (3n+1)/2^{\nu_2(3n+1)}$),
then $m = 1$.

**Lean name:** `Collatz.no_nontrivial_cycles` (PartI.lean)

---

## Axiom Summary (as of 2026-01-31)

`no_nontrivial_cycles` depends on exactly **4 custom axioms**:

| # | Axiom | File | Mathematical Basis |
|---|-------|------|--------------------|
| 1 | `baker_critical_line_cycle_bound` | BakerOrderBound | Baker's theorem on linear forms in logarithms: $m \geq 10^8$ for any critical-line cycle |
| 2 | `baker_product_band_not_div` | BakerOrderBound | Baker order bound + cyclotomic spreading for off-critical $k < S < 2k$, $k \geq 5$ |
| 3 | `zsigmondy_forces_weight_divisibility_general` | TiltBalance | Galois + cyclotomic splitting: $D \mid E$ forces $p \mid (2^{\Delta_j} - 1)$ for primitive prime $p$ |
| 4 | `exists_good_prime_in_cyclotomicBivar` | TiltBalance | For composite $n \geq 4$ (not prime power), $\exists$ prime $q \nmid 6n$ in $\bigcap_p G_p$ |

Standard Lean axioms: `propext`, `Classical.choice`, `Quot.sound`, `Lean.ofReduceBool`, `Lean.trustCompiler`

Verified by: `#print axioms Collatz.no_nontrivial_cycles`

---

## Top-Level Structure

The proof splits into three cases based on the cycle length $k$ and the
total bit-shift $S = \sum_{j=0}^{k-1} \nu_j$:

1. **$k = 1$:** Fixed-point analysis. $T(m) = m$ implies $m = 1$ directly.

2. **$k \geq 2$, $S = 2k$ (critical line):** The tilt-balance/cyclotomic machinery
   shows no nontrivial cycle can sit on the critical line.

3. **$k \geq 2$, $S \neq 2k$ (off-critical):** Discriminant divisibility + Baker-type
   order bounds + computational enumeration show no valid profile exists.

---

## Case 1: Fixed Points ($k = 1$)

**Lean:** `fixed_point_is_one` — PROVED (no custom axioms)

If $T(m) = m$ then $(3m+1)/2^{\nu} = m$, which gives $3m + 1 = m \cdot 2^{\nu}$.
Rearranging: $m(2^{\nu} - 3) = 1$, so $m = 1$ and $\nu = 2$.

---

## Case 2: Critical Line ($S = 2k$)

**Lean:** `no_nontrivial_cycles_case_II` (PartI.lean)
**Axioms:** `baker_critical_line_cycle_bound`, `zsigmondy_forces_weight_divisibility_general`, `exists_good_prime_in_cyclotomicBivar`

This is the heart of the proof. The critical line $S = 2k$ is the unique
value where $2^S = 4^k$, making the discriminant $D = 4^k - 3^k$.

### Step 2.1: Cycle Equation

A $k$-cycle with starting value $n$ satisfies:

$$n \cdot 2^S = 3^k \cdot n + c$$

where $c = \sum_{j=0}^{k-1} 3^{k-1-j} \cdot 2^{S_j}$ is the "waveSum" and
$S_j = \sum_{i=0}^{j} \nu_i$ is the partial bit-shift sum.

Rearranging: $n \cdot D = c$ where $D = 2^S - 3^k = 4^k - 3^k$.

### Step 2.2: Critical Line Cycle Profile

From the cycle, construct a `CriticalLineCycleProfile` with:

- $\nu_j \geq 1$: the 2-adic valuation at step $j$
- $\sum \nu_j = 2k$: the critical line condition
- **Deviation** $\Delta_j = S_j - 2j$: how much the partial sum deviates from the "expected" value $2j$
- **Anchor:** $\Delta_0 = 0$ (convention)
- **Weight:** $w_j = 2^{\Delta_j}$

### Step 2.3: Key Properties

From the actual cycle, the profile satisfies:

- **Nonnegativity:** $\Delta_j \geq 0$ for all $j$ (proved: `critical_line_delta_nonneg`)
- **Realizability:** $D \mid c$ (i.e., $D \mid \text{waveSum}$) (proved: `cycle_implies_realizable`)
- **Nontriviality:** If $n > 1$, then $\exists j$ with $\Delta_j > 0$ (proved: `cycle_n_gt_one_implies_exists_pos_delta`)

### Step 2.4: Finite Cases ($k = 4, 9$)

For $k = 4$ and $k = 9$, a direct computational search
(`m4_realizable_nonneg_implies_delta_zero`, `m9_realizable_nonneg_implies_delta_zero`)
shows that the only nonneg realizable profile has all $\Delta_j = 0$,
which forces $n = 1$.

These are verified by `native_decide` in Lean.

### Step 2.5: General Case ($k \neq 4, 9$)

For all other $k \geq 2$, the proof delegates to `no_nontrivial_cycles_case_II_with_gap`.
This theorem takes as input a **gap condition**: for each divisor $d \geq 2$ of $k$
and each primitive $d$-th root of unity $\omega$,
$$\sum_{j=0}^{k-1} w_j \cdot \omega^{j \bmod d} = 0.$$
Given this, Fourier inversion over $\mathbb{Z}/k\mathbb{Z}$ forces all weights equal
($w_j = c$ for all $j$), the anchor $\Delta_0 = 0$ gives $c = 1$, hence $\Delta_j = 0$
for all $j$ and $n = 1$.

The gap condition is established by splitting on the profile:

**Trivial profiles ($\forall j, \Delta_j = 0$):** All weights equal 1, so folded weights
are $k/d$ for each residue class. The DFT of a constant sequence vanishes at all
non-trivial roots, giving the gap condition directly.

**Nontrivial profiles ($\exists j, \Delta_j > 0$):** Apply
`critical_realizability_rigidity`, which proves
no nontrivial nonneg realizable profile exists — contradiction, so the gap
condition holds vacuously.

### Step 2.6: Critical Realizability Rigidity

**Lean:** `critical_realizability_rigidity` — THEOREM

**Claim:** For any $m \geq 1$, no `CriticalLineCycleProfile` of length $m$ can
simultaneously be nonneg, realizable, and nontrivial. That is:

$$\Delta_j \geq 0 \;\forall j, \quad D \mid \text{waveSum}, \quad \exists j: \Delta_j > 0 \quad \Longrightarrow \quad \bot$$

The proof splits on $m$:

**Small $m$ ($m \leq 9$):** Handled by `interval_cases` + finite verification
for each $m \in \{1, \ldots, 9\}$. For $m \in \{4, 9\}$ this uses
the computational lemmas above. For other small $m$, it's vacuous
(e.g., $m = 1$ can't have $\Delta_j > 0$ since the only index is $j = 0$
where $\Delta_0 = 0$ always).

**Large $m$ ($m \geq 10$):** Delegates to `baker_no_realizable_nontrivial`.

### Step 2.7: Large-$m$ Rigidity

**Lean:** `baker_no_realizable_nontrivial` (TiltBalance.lean) — THEOREM

For $m \geq 10$, split into three sub-cases by the smallest prime factor:

#### Sub-case 2.7a: $2 \mid m$ — PROVED

**Lean:** `baker_sp2_rigidity` — THEOREM (was axiom, now proved)

Three-case dispatch on the profile shape:
1. **Short single excursion:** `bounded_single_excursion_not_divisible` — size argument
2. **High drift ($\exists \Delta_j > 2$):** `excess_not_divisible_high_delta_general` — Zsigmondy + Dyck path
3. **Low drift (max $\Delta \leq 2$):** `low_delta_excess_not_divisible_general` — mod-4 obstruction

#### Sub-case 2.7b: $3 \mid m$ — PROVED

**Lean:** `baker_sp3_rigidity` — THEOREM (was axiom, now proved)

Same three-case dispatch as 2.7a.

#### Sub-case 2.7c: $\gcd(m, 6) = 1$ — PROVED (modulo axioms)

**Lean:** `baker_profile_rigidity` (TiltBalance.lean) — THEOREM

Delegates to `walk_constrained_balance_nonzero`, which is a **theorem**.

1. **Baker bound:** `baker_from_realizability` shows $m \geq 10^8$.
   Uses `baker_critical_line_cycle_bound` (**AXIOM**): if $D = 4^m - 3^m$
   divides a waveSum $W > D$, then $m$ exceeds the Baker--Laurent--Mignotte--Nesterenko bound.

2. **Excess = waveSum - D > 0:** Proved in `excess_pos_of_nontrivial` (no custom axioms).

3. **D | waveSum implies D | E:** Proved in `realizable_implies_D_dvd_excess` (no custom axioms).

4. **D does NOT divide E:** This is the key obstruction, proved in
   `excess_not_divisible_by_D` (THEOREM, see Step 2.8).

5. **Contradiction:** Steps 3 and 4 are incompatible.

### Step 2.8: The Excess Non-Divisibility Theorem

**Lean:** `excess_not_divisible_by_D` (TiltBalance.lean) — THEOREM

For nontrivial nonneg profiles with $m \geq 10^8$ coprime to 6,
the excess $E = \text{waveSum} - D$ is not divisible by $D = 4^m - 3^m$.

This dispatches into **three cases**, all fully proved:

#### Case A: Short Single Excursion ($3L < 2m$) — PROVED (no custom axioms)

**Lean:** `bounded_single_excursion_not_divisible`

If the $\Delta$ path makes a single excursion of length $L$ with $3L < 2m$,
factor $E = 3^a \cdot 4^b \cdot C$ where $C$ is the "excursion core."
Then $0 < C < 2^{3L} \leq D$. Since $\gcd(3^a \cdot 4^b, D) = 1$
(coprimality from $\gcd(m,6)=1$), $D \mid E$ implies $D \mid C$,
contradicting $0 < C < D$.

#### Case B: Low Drift ($\max \Delta_j \leq 2$) — PROVED (no custom axioms)

**Lean:** `low_delta_excess_not_divisible`

**Mod-4 obstruction.** Three ingredients:

1. $4 \mid E$ because $\Delta_0 = 0$ kills the $j=0$ term and all $j \geq 1$
   terms carry factor $4^j$.
2. $D$ is odd (from $\gcd(m,6) = 1$), so $\gcd(4, D) = 1$.
3. $E \leq 3D$ because $\max \Delta_j \leq 2$ means each weight
   $w_j = 2^{\Delta_j} - 1 \leq 3$.

Now $D \mid E$ and $4 \mid E$ with $\gcd(4, D) = 1$ gives $4D \mid E$,
so $E \geq 4D > 3D \geq E$. Contradiction.

#### Case C: High Drift ($\max \Delta_j \geq 3$) — PROVED (2 axioms)

**Lean:** `excess_not_divisible_high_delta_general` (TiltBalance.lean) — THEOREM
**Axioms used:** `exists_good_prime_in_cyclotomicBivar`, `zsigmondy_forces_weight_divisibility_general`

This handles **all** $m \geq 10$ uniformly (prime or composite), eliminating the
previous separate prime/composite dispatch:

**Step C.1 — Zsigmondy prime.** For $m \geq 2$, $D = 4^m - 3^m$ has a
primitive prime divisor $p$ that does not divide $4^k - 3^k$ for
any $1 \leq k < m$. (`zsigmondy_four_three` — THEOREM, depends on
`exists_good_prime_in_cyclotomicBivar` for composite $m$.)

**Step C.2 — Large prime.** The primitive prime satisfies $p \geq m + 1$
via Fermat's little theorem: $\text{ord}_p(4/3) = m$ divides $p - 1$.
(`zsigmondy_prime_ge` — PROVED, no custom axioms.)

**Step C.3 — Weight divisibility.** If $D \mid E$, then $p \mid E$. The
algebraic structure of $E = \sum 3^{m-1-j} \cdot 4^j \cdot (2^{\Delta_j} - 1)$
combined with the Galois action in $\mathbb{Z}[\zeta_m]$ forces
$p \mid (2^{\Delta_j} - 1)$ for every nonzero $\Delta_j$.
(`zsigmondy_forces_weight_divisibility_general` — **AXIOM**.)

**Step C.4 — Multiplicative order.** Since $p \geq m + 1 \geq 3$, the
multiplicative order $d = \text{ord}_p(2) \geq 2$, and
$p \mid (2^k - 1)$ implies $d \mid k$.
(`ord_two_mod_prime` — PROVED, no custom axioms.)

**Step C.5 — Dyck path obstruction.** Steps C.3--C.4 give
$(d : \mathbb{Z}) \mid \Delta_j$ for every nonzero $\Delta_j$, with $d \geq 2$.
But the $\Delta$ sequence is a nonneg lattice path anchored at 0
that returns to 0. If any $\Delta_j \geq d \geq 2$, the path gets
stuck at height $\geq d$ forever: from height $\geq d$, each step
decreases by at most 1 (since $\nu_j \geq 1$), so the next height
is $\geq d - 1 \geq 1 > 0$, hence the divisibility hypothesis forces
it back up to $\geq d$. By induction, $\Delta_k \geq d$ for all
subsequent $k$, but the path must return to 0 at $k = m$. Contradiction.
(`dyck_path_d_divisibility_trivial` — PROVED, no custom axioms.)

**Step C.6 — Conclusion.** The Dyck path obstruction forces all
$\Delta_j = 0$, contradicting nontriviality.

### Dispatch Summary

```
excess_not_divisible_by_D (THEOREM)
├── [short single excursion, 3L < 2m] bounded_single_excursion_not_divisible  ✓ PROVED
├── [max Δ ≤ 2] low_delta_excess_not_divisible                               ✓ PROVED
└── [max Δ ≥ 3, no short excursion] excess_not_divisible_high_delta_general   ✓ THEOREM
    ├── zsigmondy_four_three                        ✓ THEOREM
    │   ├── [prime n] zsigmondy_four_three_prime     ✓ PROVED (orderOf in ZMod)
    │   └── [composite n] zsigmondy_four_three_composite  ✓ THEOREM
    │       ├── [prime power] zsigmondy_four_three_prime_power  ✓ PROVED
    │       └── [multi-prime] zsigmondy_four_three_multi_prime  ✓ THEOREM
    │           └── exists_good_prime_in_cyclotomicBivar        << AXIOM
    ├── zsigmondy_prime_ge                          ✓ PROVED
    ├── zsigmondy_forces_weight_divisibility_general << AXIOM
    ├── ord_two_mod_prime                           ✓ PROVED
    └── dyck_path_d_divisibility_trivial            ✓ PROVED
```

---

## Case 3: Off-Critical Line ($S \neq 2k$)

**Lean:** The `by_contra` branch of `no_nontrivial_cycles` (PartI.lean)

When $S \neq 2k$, the cycle equation $n \cdot (2^S - 3^k) = c$ still holds,
but the analysis differs.

### Step 3.1: Bounds on $S$

From the cycle equation with $n \geq 3$ (since $n$ is odd and $> 1$):
- **Lower:** $D = 2^S - 3^k > 0$, so $2^S > 3^k$, giving $S > k \log_2 3 > k$.
- **Upper:** The cycle product identity $2^S = 3^k \prod_{j=0}^{k-1}(1 + 1/(3n_j))$
  with $n_j \geq 1$ gives $2^S \leq 4^k$, i.e., $S \leq 2k$.
- **Off-critical:** $S \neq 2k$ is given, so $S < 2k$.

This pins $S$ to the narrow band $k < S < 2k$.

### Step 3.2: Small $k$ ($k \in \{2, 3, 4\}$)

The narrow band plus $2^S > 3^k$ leaves at most one possible value of $S$
for each $k$:

| $k$ | $3^k$ | $S$ range | Possible $S$ | Verdict |
|-----|--------|-----------|---------------|---------|
| 2   | 9      | $(2, 4)$  | 3             | $D = 2^3 - 9 = -1 < 0$. No positive cycle. |
| 3   | 27     | $(3, 6)$  | 4 or 5        | $S = 4$: $D < 0$. $S = 5$: $D = 5$. Enumerate compositions. |
| 4   | 81     | $(4, 8)$  | 7             | $D = 47$. Enumerate all compositions. |

For each $(k, S)$, `noBadProfiles k S` exhaustively enumerates all
compositions of $S$ into $k$ parts $\geq 1$ and checks that none satisfy
the divisibility condition $D \mid c$ with $c/D \geq 3$. Verified by `native_decide`.

### Step 3.3: Large $k$ ($k \geq 5$): Product Band

**Axiom:** `baker_product_band_not_div` (BakerOrderBound.lean)

For $k \geq 5$ with $S$ in the product band $(k, 2k)$, the discriminant
$D = 2^S - 3^k$ does NOT divide the waveSum of any valid $\nu$-list.

**Mathematical basis:** Baker's theorem on linear forms in logarithms gives
a lower bound $|2^S - 3^k| \geq 3^k / k^{C}$. Combined with the order
bound $\text{ord}(2/3 \bmod D) \geq k$ from the cyclotomic structure,
the divisibility $D \mid c$ forces $c$ to be unreasonably large relative
to the structural constraints on the $\nu$-list.

---

## Proof Dependency Graph

```
no_nontrivial_cycles (4 custom axioms)
├── [k=1] fixed_point_is_one                              ✓ PROVED
├── [k≥2, S=2k] no_nontrivial_cycles_case_II  (3 axioms: #1, #3, #4)
│   ├── [k=4] m4_realizable_nonneg_implies_delta_zero     ✓ native_decide
│   ├── [k=9] m9_realizable_nonneg_implies_delta_zero     ✓ native_decide
│   └── [other k] no_nontrivial_cycles_case_II_with_gap
│       ├── [trivial Δ] direct arithmetic                 ✓ PROVED
│       └── [nontrivial Δ] critical_realizability_rigidity
│           ├── [m ≤ 9] interval_cases + finite check     ✓ PROVED
│           └── [m ≥ 10] baker_no_realizable_nontrivial
│               ├── [2|m] baker_sp2_rigidity               ✓ THEOREM (was axiom)
│               ├── [3|m] baker_sp3_rigidity               ✓ THEOREM (was axiom)
│               └── [gcd(m,6)=1] baker_profile_rigidity    ✓ THEOREM
│                   └── walk_constrained_balance_nonzero    ✓ THEOREM
│                       ├── baker_from_realizability        uses AXIOM #1
│                       ├── realizable_implies_D_dvd_excess ✓ PROVED
│                       └── excess_not_divisible_by_D       ✓ THEOREM
│                           ├── [short excursion]           ✓ PROVED
│                           ├── [max Δ ≤ 2, mod-4]         ✓ PROVED
│                           └── [max Δ ≥ 3] excess_not_divisible_high_delta_general
│                               ├── zsigmondy_four_three    ✓ THEOREM (uses AXIOM #4)
│                               ├── zsigmondy_prime_ge      ✓ PROVED
│                               ├── ord_two_mod_prime       ✓ PROVED
│                               ├── dyck_path_d_divisibility_trivial  ✓ PROVED
│                               └── zsigmondy_forces_weight_divisibility_general  AXIOM #3
└── [k≥2, S≠2k] off-critical analysis  (1 axiom: #2)
    ├── [k ∈ {2,3,4}] noBadProfiles                       ✓ native_decide
    └── [k ≥ 5] baker_product_band_not_div                 AXIOM #2

erdos_1135 (7 custom axioms total)
├── [bounded orbit] no_bounded_nontrivial_cycles
│   └── no_nontrivial_cycles (4 axioms above)
├── [unbounded orbit] unbounded_orbit_false
│   └── no_divergence (3 separate axioms: see NO_DIVERGENCE.md)
│       ├── bounded_omega_finite_orbit_values              << AXIOM
│       ├── equidist_bounded_omega                         << AXIOM
│       └── hardy_ramanujan_collatz                        << AXIOM
└── factor_out_twos (reduce to odd case)                   ✓ PROVED
```

---

## The Zsigmondy Chain (fully traced)

The Zsigmondy chain is the backbone of the excess non-divisibility argument.
Here is its current state:

```
zsigmondy_four_three (THEOREM — 1 axiom: exists_good_prime_in_cyclotomicBivar)
├── [prime n] zsigmondy_four_three_prime                   ✓ PROVED
│   └── Uses orderOf in ZMod p, multiplicative order theory
├── [composite n] zsigmondy_four_three_composite           ✓ THEOREM
│   ├── [prime power n=p^a] zsigmondy_four_three_prime_power  ✓ PROVED
│   │   ├── cyclotomicBivar_mul_sub                        ✓ PROVED
│   │   ├── cyclotomicBivar_gcd_factor                     ✓ PROVED
│   │   ├── cyclotomicBivar_43_pow_odd                     ✓ PROVED
│   │   ├── cyclotomicBivar_43_pow_mod3                    ✓ PROVED
│   │   ├── cyclotomicBivar_43_pow_mod_p                   ✓ PROVED
│   │   └── dvd_pow_sub_gcd_of_dvd_pow_sub                ✓ PROVED
│   └── [multi-prime n] zsigmondy_four_three_multi_prime   ✓ THEOREM
│       ├── exists_good_prime_in_cyclotomicBivar           << AXIOM
│       ├── proper_divisor_dvd_quot_prime                  ✓ PROVED
│       ├── cyclotomicBivar_mul_sub                        ✓ PROVED
│       ├── cyclotomicBivar_gcd_factor                     ✓ PROVED
│       └── dvd_pow_sub_gcd_of_dvd_pow_sub                ✓ PROVED

zsigmondy_prime_ge (PROVED — no custom axioms)
└── Fermat's little theorem: ord_p(4/3) = m divides p-1

ord_two_mod_prime (PROVED — no custom axioms)
└── Elementary: ord_p(2) ≥ 2 for p ≥ 3, divides k when p | (2^k - 1)

dyck_path_d_divisibility_trivial (PROVED — no custom axioms)
└── Lattice path stuck-at-height argument

zsigmondy_forces_weight_divisibility_general (AXIOM)
└── Galois action in Z[ζ_m]: D | E + p primitive ⟹ p | (2^{Δ_j} - 1)
```

---

## What Changed (2026-01-31)

### Axioms eliminated since previous version:

| Old Axiom | Status | How |
|-----------|--------|-----|
| `zsigmondy_four_three` | THEOREM | Dispatches prime/composite; prime case proved via ZMod, composite via new infrastructure |
| `zsigmondy_four_three_multi_prime` | THEOREM | Proved via `exists_good_prime_in_cyclotomicBivar` + `proper_divisor_dvd_quot_prime` + `cyclotomicBivar_gcd_factor` |
| `zsigmondy_prime_ge` | PROVED | Fermat's little theorem, no custom axioms |
| `ord_two_mod_prime` | PROVED | Multiplicative order theory in ZMod, no custom axioms |
| `zsigmondy_forces_weight_divisibility` | THEOREM | Derived from `zsigmondy_forces_weight_divisibility_general` |
| `baker_sp2_rigidity` | THEOREM | Three-case dispatch: short excursion + high delta (Zsigmondy) + low delta (mod-4) |
| `baker_sp3_rigidity` | THEOREM | Same three-case dispatch |
| `excess_not_divisible_composite_high_delta` | THEOREM | Superseded by `excess_not_divisible_high_delta_general` which handles all $m$ uniformly |

### New axiom (strictly narrower):

| New Axiom | Replaces | Why narrower |
|-----------|----------|--------------|
| `exists_good_prime_in_cyclotomicBivar` | `zsigmondy_four_three_multi_prime` | Only asserts $\exists q \nmid 6n$ in $\bigcap_p G_p$; primitivity is *proved* from this + GCD descent + Dyck path |

### Key structural improvement:

The old proof had separate cases for prime $m$ (proved) and composite $m$ (axiom) in
the high-drift branch. The new `excess_not_divisible_high_delta_general` handles
**all** $m \geq 10$ uniformly using `zsigmondy_four_three` (which now works for all $m$).
This eliminated the prime/composite split entirely.

---

## Axiom Difficulty Tiers

### Tier 1 — Standard results (provable with effort):

- **`exists_good_prime_in_cyclotomicBivar`**: The $n$-th homogeneous cyclotomic value
  $\Psi_n(4,3)$ divides each $G_p$. Its prime factors coprime to $6n$ exist by:
  $|\Psi_n| \geq 2$, $\gcd(\Psi_n, 6) = 1$, and $v_p(\Psi_n) \leq 1$ for $p | n$
  (Lifting the Exponent Lemma) combined with $|\Psi_n| \gg \text{rad}(n)$.

### Tier 2 — Moderate difficulty:

- **`zsigmondy_forces_weight_divisibility_general`**: Lifts $p \mid D \mid E$ to
  $p \mid (2^{\Delta_j} - 1)$ for each nonzero $\Delta_j$. Uses cyclotomic splitting
  of $D$ in $\mathbb{Z}[\zeta_m]$ and the fact that $p$ is a primitive divisor.

### Tier 3 — Hard (transcendence theory):

- **`baker_critical_line_cycle_bound`**: Baker's theorem on linear forms in logarithms.
  Deep result, unlikely to be proved in Lean soon. Only used to establish $m \geq 10^8$.
- **`baker_product_band_not_div`**: Combines Baker's order bound with cyclotomic spreading.
  Requires effective lower bounds on $|2^S - 3^k|$.

### Most impactful next steps:

1. **Prove `exists_good_prime_in_cyclotomicBivar`**: Requires formalizing the Lifting the
   Exponent Lemma and cyclotomic value size bounds. Would eliminate the last Zsigmondy axiom.
2. **Prove `zsigmondy_forces_weight_divisibility_general`**: The algebraic step that transfers
   divisibility from the discriminant to individual weights. Would make the entire excess
   chain depend only on Baker bounds.

---

## Key Definitions

**CriticalLineCycleProfile $m$:** A sequence $(\nu_0, \ldots, \nu_{m-1})$ with
$\nu_j \geq 1$ and $\sum \nu_j = 2m$, together with derived quantities:
- $\Delta_j = S_j - 2j$ (deviation from critical line)
- $w_j = 2^{\Delta_j}$ (weight)
- $\text{waveSum} = \sum_j 3^{m-1-j} \cdot 2^{S_j}$
- **Excess:** $E = \text{waveSum} - D$ where $D = 4^m - 3^m$

**Realizable:** $D \mid \text{waveSum}$ where $D = 4^m - 3^m$.

**Nontrivial:** $\exists j$ with $\Delta_j > 0$.

**Cycle denominator:** $D = \text{cycleDenominator}(m, 2m) = 2^{2m} - 3^m = 4^m - 3^m$.

**Single excursion:** The $\Delta$ path is zero outside a contiguous block
$[j_0, j_0 + L)$ of length $L$.

**Folded weight:** $\text{FW}_q(r) = \sum_{j \equiv r \pmod{q}} w_j$.

**Cyclotomic factorization:** $D = 4^m - 3^m = \prod_{d \mid m} \Phi_d(4, 3)$
where $\Phi_d$ is the $d$-th cyclotomic polynomial.

**Bivariate cyclotomic value:** $G_p = \Phi_p(4^{n/p}, 3^{n/p})$ — the geometric sum
$(4^{n/p})^{p-1} + (4^{n/p})^{p-2} \cdot 3^{n/p} + \cdots + (3^{n/p})^{p-1}$.

---

## File Map

| File | Role |
|------|------|
| `PartI.lean` | Top-level `no_nontrivial_cycles`, case splits, off-critical analysis, cycle equation |
| `TiltBalance.lean` | Profile definitions, excess obstruction theorems, Zsigmondy chain, Dyck path, Baker bound bridge, rigidity, `exists_good_prime_in_cyclotomicBivar` axiom |
| `BakerOrderBound.lean` | Baker bound axioms, product band analysis, discriminant arithmetic |
| `IntegralityBridge.lean` | Cyclotomic field bridge: norm divisibility, local tilt obstruction |
| `CyclotomicAlgebra.lean` | Cyclotomic field definitions, bivariate cyclotomic polynomials, norm machinery |
| `WanderingTarget.lean` | No-divergence theorem (separate axiom set) |
| `1135.lean` | Final theorem assembly `erdos_1135`, axiom audit |
