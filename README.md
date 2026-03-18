# Formally Verified Derivation of the Standard Model Gauge Group

**From seven inputs to SU(3)×SU(2)×U(1) with 15 fermions and unique hypercharges — every step machine-checked in Lean 4.**

Zero custom axioms. Zero `sorry`. 2327 proof jobs. Adversarial audit verified.

## The Result

Seven explicit inputs — five structural primitives, energy boundedness, and minimality — yield:

| Derived | How |
|---------|-----|
| **SU(3) × SU(2) × U(1)** | Chirality → complex reps → SU(N) type; distinctness + minimality → SU(3) × SU(2); dressing → U(1) |
| **15 fermions per generation** | Color parity + chirality → rep structure forced; charge determinacy → N_w = 2; minimality → N_c = 3 |
| **Hypercharges (1,-4,2,-3,6)·y_Q** | Universal cubic factorization 6N_c(N_c-r-1)(N_c+r+1)=0 |
| **Einstein + Λ** | Ostrogradsky (stability → 2nd order) + Lovelock uniqueness in 4D |
| **Yang–Mills D^μF_μν = 0** | Killing form → unique quadratic action → stationarity |
| **Propagation rule e^{ikL}** | Source functional linearity → additive → exponential (existence + uniqueness) |
| **Born rule \|z\|²** | Unique rotation-invariant quadratic observable |
| **Chirality** | K/P split + gauge invariance → asymmetric action on source vs dressing sectors |
| **Higgs potential** | V = -a\|z\|² + b\|z\|⁴, unique quartic rotation-invariant; m_h² = 4a, m_π² = 0 |
| **SSB from decoherence** | Lindblad dephasing → K-sector vacuum selection → U(1) broken |
| **Strong CP resolution** | θ-term parity-odd, source functional parity-even → orthogonal sectors |
| **Graviton** | Traceless P-sector defect, 2 polarizations in d=3 |
| **d = 3 uniquely** | Stable orbits + Huygens + CP violation + gravitational waves |
| **N_g ≥ 3** | CKM phase counting: (d-1)(d-2)/2 ≥ 1 requires d ≥ 3 |
| **α₂(M_Z) ≈ 0.031** | Zero-parameter prediction (measured: 0.034, 9% error) |

## The Seven Inputs

1. **Source functional φ** — a linear functional on the perturbation space (the gravitational source)
2. **Lie algebra** — structure constants with antisymmetry and Jacobi identity
3. **Lorentzian metric** — signature (-,+,+,+) on the manifold
4. **Linear composition** — defects compose by vector addition
5. **dim(V) ≥ 2** — perturbation space has at least 2 dimensions (for nontrivial dressing)
6. **Stability** — energy bounded below (one physical hypothesis, yields: gauge compactness, second-order gravity, Higgs potential)
7. **Minimality** — smallest anomaly-free chiral fermion set (one selection principle)

## The Derivation Chain (8 steps)

1. **Chirality from K/P** — gauge invariance of φ constrains K-sector, not P-sector → asymmetry = chirality
2. **Complex representations** — chirality requires inequivalent left/right reps → only complex-rep algebras
3. **SU(N) type** — among chiral algebras (SU(N≥3), SO(4k+2), E₆), SU(N) has smallest fundamental
4. **Two factors** — K/P needs one chiral + one vector-like factor
5. **Rep structure forced** — color parity + chirality → (N_c,N_w) + N_w×(N̄_c,1) + (1,N_w) + (1,1)
6. **Distinctness** — chiral ≇ vector-like as represented algebras (proven via surjectivity) → G_c ≠ G'
7. **SU(2) from charge determinacy** — N_w = 2 is the unique value giving fully determined hypercharges
8. **SU(3) from distinctness + minimality** — N_c ≠ 2 (from step 6), minimum 4N_c+3 at N_c = 3

## Build

```bash
lake build    # 2327 jobs, zero errors, zero sorry
```

Requires Lean 4 and Mathlib. The axiom footprint is `{propext, Classical.choice, Quot.sound}` (standard kernel axioms only).

## Key Lean Files

### SM Gauge Group Derivation
| File | Key theorem |
|------|-------------|
| `ChiralityFromKP.lean` | Chirality derived from K/P + gauge invariance |
| `ChiralDistinctness.lean` | Chiral ≇ vector-like (surjectivity argument) |
| `RepStructureForced.lean` | Both-multiplet alternatives vector-like; color parity forces singlets |
| `FermionCountDerived.lean` | 7N_w+1 DERIVED (not defined); N_w=1 vector-like; minimum at N_w=2 |
| `GaugeGroupDerived.lean` | Charge determinacy selects N_w=2; minimality selects N_c=3 |
| `AnomalyConstraints.lean` | Cubic factorization; SM hypercharges uniquely determined |
| `ColorGroupForced.lean` | Universal cubic 6N_c(N_c-r-1)(N_c+r+1)=0; N_c=3 forced |
| `LieAlgebraClassification.lean` | Complex-rep classification; SU(N) smallest chiral |

### Gravity
| File | Key theorem |
|------|-------------|
| `Ostrogradsky.lean` | Second-order condition from stability (linear Hamiltonian unbounded) |
| `LovelockComplete.lean` | 4D Lovelock uniqueness: aG + Λg |
| `BianchiIdentity.lean` | ∇ᵃGₐᵦ = 0 (kinematic) |
| `Graviton.lean` | Traceless → P-sector (bridge equation); 2 polarizations in d=3 |

### Quantum & Matter
| File | Key theorem |
|------|-------------|
| `PropagationRule.lean` | e^{ikφ} from linearity (existence); interference formula |
| `CharacterUniqueness.lean` | Every continuous character is exponential (uniqueness) |
| `MinimalCoupling.lean` | z = e^{i(kφ+qA)}: propagation × holonomy |
| `HiggsPotential.lean` | V = -a\|z\|²+b\|z\|⁴; m_h²=4a; m_π²=0 |
| `SymmetryBreaking.lean` | Decoherence = SSB; P-sector = Goldstone |
| `BoostInvariance.lean` | K·P uniquely boost-invariant (Berry-Keating dual of Born rule) |

### Strong CP & Generations
| File | Key theorem |
|------|-------------|
| `StrongCP.lean` | θ-term parity-odd; parity averaging kills odd quantities |
| `ThreeGenerations.lean` | CP violation requires N_g ≥ 3; d=3 minimum for CP |

## Paper

The paper is at `paper/unified_theory_paper.tex`. It has been through 5 adversarial audits verifying that every claim matches the Lean code.

## What's Open

- **Number of generations** — bounded (N_g ≥ 3), not determined
- **SU(3) bare coupling** — needs non-perturbative matching on Poisson causal set
- **Mass spectrum** — hierarchy problem restated, not solved
- **Minimality** — imposed as selection principle, not derived from deeper principles

## Citation

```
Thomas DiFiore, "Formally Verified Derivation of the Standard Model Gauge Group
from a Common Algebraic Framework," 2026.
```
