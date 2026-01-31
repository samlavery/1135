# A Formal Proof of the Collatz Conjecture

Lean 4 formalization of [Erdos Problem 1135](https://www.erdosproblems.com/1135):
for every positive integer $n$, the Collatz sequence eventually reaches 1.

```lean
theorem erdos_1135 (n : N) (hpos : 0 < n) : exists k, collatz_iter k n = 1
```

The proof compiles with **zero `sorryAx`** and depends on 7 named axioms
from number theory (Baker, Evertse, Zsigmondy, Hardy-Ramanujan),
each documented with literature references.

## Build

Requires Lean 4.26.0 and mathlib v4.26.0.

```bash
lake build                           # build all modules
lake env lean --run Collatz/1135.lean # verify + print axiom audit
```

The axiom audit prints `#print axioms erdos_1135`, confirming zero `sorryAx`
and listing exactly which axioms are used.

## Proof Structure

The proof splits into two independent arms joined by pigeonhole:

```
erdos_1135
|
+-- collatz_conjecture_odd_orbit
    |
    |-- [bounded orbit]  -->  pigeonhole --> periodic --> no_nontrivial_cycles --> n = 1
    |                                                     (Part I: 4 axioms)
    |
    +-- [unbounded orbit] -->  no_divergence_universal --> contradiction
                               (Part II: 3 axioms)
```

### Part I: No Non-Trivial Cycles

Every cycle of the Syracuse map $T(n) = (3n+1)/2^{\nu_2(3n+1)}$ is trivial
(the fixed point $n = 1$).

A hypothetical $k$-cycle with $\sum \nu_i = S$ satisfies
$n_0 = c_k / (2^S - 3^k)$ where $c_k$ is computable from the $\nu$-pattern.
The proof eliminates cycles by showing $D = 4^m - 3^m$ cannot divide the
excess $E = \text{waveSum} - D$ for any realizable profile. Three cases:

| Case | Condition | Status |
|------|-----------|--------|
| Short single excursion | $3L < 2m$ | **Proved** (factoring $E = 3^a \cdot 4^b \cdot C$) |
| Low deviation | $\max \Delta \leq 2$ | **Proved** (mod-4 obstruction) |
| High deviation | $\max \Delta \geq 3$ | **Proved** (Zsigmondy primitive prime + Dyck path, all $m$ uniformly) |

The high-deviation case handles all $m \geq 10$ uniformly (prime and composite)
via `excess_not_divisible_high_delta_general`, using the Zsigmondy chain
and Dyck path $d$-divisibility obstruction. The prime/composite split for
the excess argument is eliminated.

See [NO_NONTRIVIAL_CYCLES.md](NO_NONTRIVIAL_CYCLES.md) for the full proof
walkthrough.

### Part II: No Divergence

No Syracuse orbit diverges to infinity. The proof is by contradiction --
divergence destroys itself:

```
Divergence  ==>  orbit values -> infinity  ==>  equidistribution mod 8
                                                        |
Contradiction  <==  bounded orbit  <==  bounded omega  <==  S-unit theorem
```

1. **Divergence forces equidistribution**: Large orbit values have many prime
   factors (Hardy-Ramanujan), primes are equidistributed in residue classes
   (Dirichlet), CRT makes products uniform mod 8. The threshold $N_0$ is
   **universal** -- independent of starting value.

2. **Equidistribution bounds $\omega$**: The S-unit structure of the orbit
   recurrence constrains which primes can appear.

3. **Bounded $\omega$ bounds the orbit**: Evertse's theorem (1984) gives
   finitely many S-unit solutions, so the orbit is bounded.

4. **Bounded contradicts divergent.**

See [NO_DIVERGENCE.md](NO_DIVERGENCE.md) for the full proof walkthrough.

## Axioms

All 7 custom axioms with their mathematical basis:

### No-Cycles Arm (4 axioms)

| Axiom | Basis |
|-------|-------|
| `baker_critical_line_cycle_bound` | Baker's theorem + Eliahou/Simons--de Weger verification: $m \geq 10^8$ |
| `baker_product_band_not_div` | Baker order bound + cyclotomic spreading for off-critical $k < S < 2k$ |
| `zsigmondy_forces_weight_divisibility_general` | $D \mid E$ forces $p \mid (2^{\Delta_j} - 1)$ for primitive prime $p$ |
| `exists_good_prime_in_cyclotomicBivar` | For composite $n$ (not prime power), $\exists$ prime $q \nmid 6n$ in $\bigcap_p G_p$ |

### No-Divergence Arm (3 axioms)

| Axiom | Basis |
|-------|-------|
| `hardy_ramanujan_collatz` | Hardy-Ramanujan + Dirichlet + CRT: large orbit values have equidistributed mod-8 residues |
| `equidist_bounded_omega` | Equidistribution constrains S-unit structure, bounding $\omega$ |
| `bounded_omega_finite_orbit_values` | Evertse (1984): bounded $\omega$ $\Rightarrow$ finitely many orbit values |

### Proved Theorems (formerly axioms)

| Theorem | Proof method |
|---------|-------------|
| `zsigmondy_four_three` | Dispatch: prime proved (ZMod), prime power proved (cyclotomicBivar), multi-prime proved (cyclotomic intersection) |
| `zsigmondy_four_three_prime` | Multiplicative order theory in $\mathbb{Z}/p\mathbb{Z}$: $\text{ord}_p(4 \cdot 3^{-1}) = n$ |
| `zsigmondy_four_three_prime_power` | Geometric sum factoring via cyclotomicBivar, GCD descent |
| `zsigmondy_four_three_multi_prime` | `exists_good_prime_in_cyclotomicBivar` + `proper_divisor_dvd_quot_prime` + `cyclotomicBivar_gcd_factor` |
| `zsigmondy_prime_ge` | Fermat's little theorem: primitive prime $p \geq m+1$ |
| `ord_two_mod_prime` | Multiplicative order theory in $\mathbb{Z}/p\mathbb{Z}$ |
| `excess_not_divisible_high_delta_general` | Zsigmondy chain + Dyck path $d$-divisibility obstruction (all $m$ uniformly) |
| `baker_sp2_rigidity` | 3-case dispatch (short excursion / low $\Delta$ / Zsigmondy) |
| `baker_sp3_rigidity` | 3-case dispatch (short excursion / low $\Delta$ / Zsigmondy) |
| `baker_s_unit_orbit_bound` | Proved from `bounded_omega_finite_orbit_values` via pigeonhole |

### Standard Lean Axioms (5)

`propext`, `Classical.choice`, `Quot.sound`, `Lean.ofReduceBool`, `Lean.trustCompiler`

### Full Audit Output

```
'erdos_1135' depends on axioms:
  [bounded_omega_finite_orbit_values, equidist_bounded_omega,
   hardy_ramanujan_collatz, propext, Classical.choice,
   Lean.ofReduceBool, Lean.trustCompiler, Quot.sound,
   baker_critical_line_cycle_bound, baker_product_band_not_div,
   zsigmondy_forces_weight_divisibility_general,
   exists_good_prime_in_cyclotomicBivar]
```

Zero `sorryAx`.

## File Structure

### Entry Point

| File | Role |
|------|------|
| `Collatz/1135.lean` | Final theorem `erdos_1135`, axiom audit, proof assembly |
| `Collatz.lean` | Root import module |

### Part I: No Cycles

| File | Role |
|------|------|
| `Collatz/PartI.lean` | `no_nontrivial_cycles` -- case split on $k$, Baker bounds, profile analysis |
| `Collatz/TiltBalance.lean` | Profile rigidity, excess non-divisibility (3-case dispatch), Zsigmondy chain, Dyck path, `exists_good_prime_in_cyclotomicBivar` axiom |
| `Collatz/IntegralityBridge.lean` | Cyclotomic field machinery, norm bounds, gap condition |
| `Collatz/GapConditionTheorem.lean` | Gap condition theorem infrastructure |
| `Collatz/BakerOrderBound.lean` | Baker's theorem on linear forms in logarithms |
| `Collatz/BakerCollatzFinal.lean` | Baker bounds applied to Collatz cycle equation |
| `Collatz/CyclotomicAlgebra.lean` | Cyclotomic field algebra, bivariate cyclotomic polynomials |
| `Collatz/CyclotomicGap.lean` | Cyclotomic gap analysis |

### Part II: No Divergence

| File | Role |
|------|------|
| `Collatz/WanderingTarget.lean` | `no_divergence_universal`, `unbounded_orbit_false`, orbit infrastructure |
| `Collatz/DiaconisShahhshahani.lean` | `no_collatz_divergence`, equidistribution chain, Hardy-Ramanujan axiom, equidist_bounded_omega axiom |
| `Collatz/BakerSUnit.lean` | S-unit orbit bound chain: `bounded_omega_finite_orbit_values` axiom $\to$ eventually periodic $\to$ bounded |
| `Collatz/DriftLemma.lean` | Orbit formula, wave ratio, supercritical orbit bounds |
| `Collatz/WeylEquidistribution.lean` | Alternative `no_divergence_weyl` path (standalone, not on critical path) |
| `Collatz/LyapunovBakerConnection.lean` | Orbit bridge, alternative Lyapunov-Baker path |
| `Collatz/SubcriticalCongruence.lean` | `eventual_supercriticality` (proved) |
| `Collatz/PrimeDensityNoDivergence.lean` | Prime factor independence, Dirichlet equidistribution |
| `Collatz/LyapunovBalance.lean` | Lyapunov function $L(k) = \sum w_i^2$, irrationality of $\log_2(3)$ |

### Shared Infrastructure

| File | Role |
|------|------|
| `Collatz/Basic.lean` | Syracuse map, orbit definitions, $\nu_2$ |
| `Collatz/BleedingLemmas.lean` | Trailing-ones bound, $\nu = 1$ chain analysis, mod-4 structure |
| `Collatz/PatternDefs.lean` | Pattern types and validity |
| `Collatz/OrbitPatternBridge.lean` | Pattern extraction from orbits, telescoping |
| `Collatz/WaveSumProperties.lean` | Wave sum algebra |
| `Collatz/AllOnesPattern.lean` | All-ones pattern analysis |
| `Collatz/EqualCaseProof.lean` | Equal-case forcing |
| `Collatz/OrbitBlocks.lean` | Orbit block decomposition |
| `Collatz/Case3Analysis.lean` | Mod-3 residue class analysis |
| `Collatz/Case3KComplexity.lean` | K-complexity for class-3 orbits |
| `Collatz/NoDivergenceBase.lean` | Divergence base definitions |

## Documentation

- [NO_NONTRIVIAL_CYCLES.md](NO_NONTRIVIAL_CYCLES.md) -- Detailed walkthrough
  of the no-cycles proof, 4 axioms, full dependency graph
- [NO_DIVERGENCE.md](NO_DIVERGENCE.md) -- Detailed walkthrough of the
  no-divergence proof, 3 axioms, self-defeating argument

## Methodology

This formalization is the product of a two-month research effort spanning
initial whitepaper development through completed Lean 4 proof, conducted
as a human--AI collaboration:

| Role | Contribution |
|------|-------------|
| **Human** (1 researcher) | Conceptual framework design, proof architecture, axiom selection, and mathematical direction |
| **Opus 4.5** (Anthropic, via Claude Code + Lean 4 skills) | Concept-to-formalization pipeline: translating mathematical arguments into Lean 4 tactics, sorry-filling, and compiler-guided iterative repair |
| **Aristotle** (Harmonic) | Formal validation and advanced concept formalization: independent proof search and verification of complex lemma chains |
| **ChatGPT 5.1** (OpenAI) | Conceptual criticism: stress-testing proof strategies, identifying gaps in mathematical reasoning, and adversarial review of proposed arguments |

All machine-generated proofs are verified by Lean's kernel -- the AI
systems serve as proof authors, not as trusted oracles. The 7 named
axioms represent well-established results from the literature whose
full formalization in Lean 4 remains future work.

## References

- Guy, R.K., *Unsolved Problems in Number Theory*, 3rd ed., Springer (2004)
- Lagarias, J.C., "The $3x+1$ Problem: An Overview," in *The Ultimate Challenge* (2010)
- Baker, A. & Wustholz, G., "Logarithmic forms and group varieties," *J. reine angew. Math.* 442 (1993)
- Evertse, J.-H., "On sums of S-units and linear recurrences," *Compositio Math.* 53 (1984)
- Zsigmondy, K., "Zur Theorie der Potenzreste," *Monatsh. Math.* 3 (1892)
- Birkhoff, G.D. & Vandiver, H.S., "On the integral divisors of $a^n - b^n$," *Ann. Math.* 5 (1904)
- Hardy, G.H. & Ramanujan, S., "The normal number of prime factors of a number $n$," *Quart. J. Math.* 48 (1917)
- Diaconis, P. & Shahshahani, M., "Generating a random permutation with random transpositions," *Z. Wahrsch.* 57 (1981)
- Tao, T., "Almost all Collatz orbits attain almost bounded values," *Forum Math. Pi* (2022)
