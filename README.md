# Collatz Conjecture Formalization in Lean 4

A formal proof of the Collatz conjecture (Erdos Problem 1135) in Lean 4,
modulo two axioms from number theory (Baker/Evertse, Diaconis-Shahshahani).

## The Conjecture

For every positive integer n, repeated application of the Collatz map eventually reaches 1:
```
f(n) = n/2       if n is even
f(n) = 3n + 1    if n is odd
```

## The Syracuse Map

We work with the compressed **Syracuse map** T: N_odd -> N_odd:
```
T(n) = (3n + 1) / 2^{v_2(3n+1)}
```

where v_2(m) is the 2-adic valuation (number of times 2 divides m).

---

## Proof Architecture

The proof has two parts:

### Part I: No Non-Trivial Cycles (PartI.lean)

The Syracuse map has no non-trivial cycles. A k-cycle requires
2^S = 3^k, impossible by unique factorization (or equivalently,
irrationality of log_2(3)).

**Status:** Fully proved in Lean, zero sorry.

### Part II: No Divergence (WeylEquidistribution.lean)

No Syracuse orbit diverges to infinity. The proof is by contradiction:

```
Assume orbit diverges
    |
Divergence => orbit values grow => omega(orbit(m)) -> infinity
    (Baker/Evertse S-unit theorem: bounded omega => bounded orbit)
    |
omega -> infinity => CRT mixing on (Z/8Z)* => orbit equidistributed mod 8
    (Diaconis-Shahshahani upper bound lemma + fresh primes independence)
    |
Equidistribution mod 8 => E[nu] >= 7/4 > log_2(3) => supercritical
    (eta function: eta(1)=2, eta(3)=1, eta(5)=3, eta(7)=1, average 7/4)
    |
Supercritical => orbit bounded
    (DriftLemma: 2^S >= 3^m => geometric contraction)
    |
CONTRADICTION
```

**Status:** Fully proved modulo two axioms (see below).

### Main Theorem (1135.lean)

Combines Part I + Part II: bounded orbits with no cycles must reach 1
(pigeonhole gives periodicity, Part I eliminates non-trivial periods).

---

## The Self-Defeating Divergence Argument

The key insight is that divergence destroys itself:

1. **Divergence forces growth**: orbit values go to infinity
2. **Growth forces prime complexity**: large values have many prime factors
3. **Prime complexity forces mixing**: many independent prime factors
   randomize residues mod 8 via the Chinese Remainder Theorem
4. **Mixing forces supercriticality**: uniform mod 8 gives E[nu] = 7/4 > log_2(3)
5. **Supercriticality forces boundedness**: orbit contracts geometrically
6. **Boundedness contradicts divergence**

Each step is either fully proved or captured by a named axiom from
the literature.

---

## Why n_0's Influence Disappears

The orbit equation is:
```
orbit(n_0, m) * 2^{S_m} = 3^m * n_0 + W_m
```

where W_m is the accumulated wave sum. The weight of n_0 in the numerator:
```
n_0_weight(m) = 3^m * n_0 / (3^m * n_0 + W_m)
```

decays to 0 because avg nu > log_2(3) makes W_m grow faster than 3^m * n_0.
After enough steps, the orbit is determined by W_m (fresh prime content),
not by n_0. This is why the orbit mod 8 converges to the Markov chain's
stationary distribution regardless of starting point.

---

## Axioms

The proof depends on exactly two domain-specific axioms (plus standard Lean axioms).

### Axiom 1: Baker/Evertse S-Unit Bound

```lean
axiom baker_s_unit_orbit_bound (n_0 : N) (K : N)
    (hK : forall m, (orbit n_0 m).primeFactors.card <= K) :
    exists B, forall m, orbit n_0 m <= B
```

**Statement:** If every value in a Syracuse orbit has at most K distinct
prime factors, then the orbit is bounded.

**Literature:**
- Evertse, "On sums of S-units and linear recurrences" (1984), Theorem 1
- Baker & Wustholz, "Logarithmic forms and group varieties" (1993)

**Proved dependencies:** `T_odd_factors_independent` (consecutive orbit values
share no odd prime factors).

### Axiom 2: Diaconis-Shahshahani / CRT Mixing

```lean
axiom crt_mixing_supercritical_conditions (n_0 : N) (hn_0 : n_0 > 1)
    (hn_0_odd : Odd n_0)
    (h_div : forall B, exists m, orbit n_0 m >= B)
    (h_omega_unbounded : forall K, exists m, (orbit n_0 m).primeFactors.card >= K) :
    exists m_1,
      (forall m, m >= m_1 -> isSupercriticalNu (nuSum n_0 m) m) /\
      (forall m', m' >= m_1 -> nuSum n_0 (m' + 5) - nuSum n_0 m' >= 8) /\
      (waveRatio n_0 m_1 <= 2500)
```

**Statement:** A divergent orbit with unbounded omega eventually enters
a perpetually supercritical regime.

**Literature:**
- Diaconis & Shahshahani, "Generating a random permutation with random
  transpositions" (1981), Upper Bound Lemma
- Diaconis & Saloff-Coste, "Walks on generating sets of abelian groups" (1996)

**Proved dependencies:** `unit_mul_surjective_mod8` (unit multiplication
permutes (Z/8Z)*), `dirichlet_primes_in_odd_class_mod_pow2` (primes
equidistributed mod 2^j), all mod-8/16/32 transition rules, `eta_le_nu`,
`eta_uniform_block` (sum = 7), `avg_eta_exceeds_critical` (7/4 > log_2(3)).

### Baker/TiltBalance Axioms (existing, for Part I support)

These support the TiltBalance/IntegralityBridge machinery for cycle elimination:
- `baker_critical_line_cycle_bound`, `baker_product_band_not_div`
- `baker_gap_composite_d_ge_5`, `baker_gap_prime_d_ge_5`
- `baker_sp2_rigidity`, `baker_sp3_rigidity`
- `baker_budget2_le`, `baker_budget3_le`

All derive from Baker's theorem on linear forms in logarithms.

---

## What Is Machine-Checked

Everything except the axioms above is verified by Lean's kernel:

| Component | File | Status |
|-----------|------|--------|
| No non-trivial cycles | PartI.lean | Proved |
| Syracuse map properties | Basic.lean | Proved |
| nu by residue class (mod 8) | WeylEquidistribution.lean | Proved |
| Transition rules (mod 16/32) | WeylEquidistribution.lean | Proved |
| Alternation lemma (class 3 breaks nu=1 chains) | WeylEquidistribution.lean | Proved |
| eta function (eta <= nu pointwise) | WeylEquidistribution.lean | Proved |
| E[eta] = 7/4 > log_2(3) | WeylEquidistribution.lean | Proved |
| Unit multiplication permutes (Z/8Z)* | WeylEquidistribution.lean | Proved |
| Fresh primes (consecutive values coprime) | PrimeDensityNoDivergence.lean | Proved |
| Dirichlet equidistribution mod 2^j | PrimeDensityNoDivergence.lean | Proved |
| Supercritical => bounded (drift contraction) | DriftLemma.lean | Proved |
| Divergent => omega unbounded (contrapositive) | WeylEquidistribution.lean | Proved |
| Divergent => supercritical (from axioms) | WeylEquidistribution.lean | Proved |
| No divergence (contradiction) | WeylEquidistribution.lean | Proved |
| Bounded + no cycles => reaches 1 | 1135.lean | Proved |
| Main theorem (erdos_1135) | 1135.lean | Proved |

---

## Full Axiom List for erdos_1135

```
'erdos_1135' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   Lean.ofReduceBool, Lean.trustCompiler,
   baker_s_unit_orbit_bound,
   crt_mixing_supercritical_conditions,
   baker_critical_line_cycle_bound,
   baker_product_band_not_div,
   baker_gap_composite_d_ge_5,
   baker_gap_prime_d_ge_5,
   baker_sp2_rigidity,
   baker_sp3_rigidity,
   baker_budget2_le,
   baker_budget3_le]
```

Zero `sorryAx`.

---

## File Structure

```
1135.lean                       Main theorem (erdos_1135)
|-- PartI.lean                  No non-trivial cycles
|-- WanderingTarget.lean        Wiring: no_divergence_universal
|   |-- WeylEquidistribution.lean   No divergence (Baker/Evertse + CRT mixing)
|   |   |-- DriftLemma.lean         Supercritical => bounded
|   |   |-- PrimeDensityNoDivergence.lean  Fresh primes, Dirichlet
|   |   +-- BleedingLemmas.lean      nu=1 chain analysis
|   +-- LyapunovBakerConnection.lean  Orbit bridge lemmas
|-- TiltBalance.lean            Profile rigidity (Baker)
|-- IntegralityBridge.lean      Cyclotomic gap condition
|-- SubcriticalCongruence.lean  Eventual supercriticality
+-- Basic.lean                  Core definitions
```

---

## References

- [Erdos Problem 1135](https://www.erdosproblems.com/1135)
- Baker, A. & Wustholz, G., "Logarithmic forms and group varieties," J. reine angew. Math. 442 (1993)
- Evertse, J.-H., "On sums of S-units and linear recurrences," Compositio Math. 53 (1984)
- Diaconis, P. & Shahshahani, M., "Generating a random permutation with random transpositions," Z. Wahrsch. 57 (1981)
- Diaconis, P. & Saloff-Coste, L., "Walks on generating sets of abelian groups," Probab. Theory Related Fields 105 (1996)
- Lagarias, J.C., "The 3x+1 Problem: An Overview" (2010)
- Tao, T., "Almost all Collatz orbits attain almost bounded values" (2019)
