# Time is a Partial Order

**One postulate. Two identifications. Zero free parameters. Machine-checked in Lean 4.**

From the axiom that time is a locally finite partial order, we derive the Standard Model of particle physics, the Higgs mass, the electroweak scale, and the quark mass hierarchy. Every algebraic step is formally verified in Lean 4 with zero `sorry` and zero custom axioms. The interpretive layer is exactly two lines thick.

**Paper:** [`paper/time_is_a_partial_order.pdf`](paper/time_is_a_partial_order.pdf)

## What Is Derived

**From one postulate** (spacetime is a locally finite partial order), **two identifications** (λ_H = γ₄²/2 and v = M_P exp(-c/g²)), and **one scale** (M_P):

### Structure (Layer 1 — unconditional algebra)

| Result | Status | Key File |
|--------|--------|----------|
| Spacetime dimension d = 3+1 | Lean ✓ | `DimensionDerived.lean` |
| d_spatial = 3 (independent confirmation) | Lean ✓ | `AntichainOverlap.lean` |
| Gauge group SU(3) × SU(2) × U(1) | Lean ✓ | `GaugeGroupDerived.lean` |
| sin²θ_W = 3/8 | Lean ✓ | `WeinbergAngle.lean` |
| 15 Weyl fermions per generation | Lean ✓ | `FermionCountFromAnomaly.lean` |
| 3 generations | Lean ✓ | `ThreeGenerations.lean` |
| All electric charges | Lean ✓ | `AnomalyConstraints.lean` |
| θ_QCD = 0 (strong CP solved) | Lean ✓ | `StrongCP.lean` |
| Proton stability | Lean ✓ | `ProtonStability.lean` |
| Spectral gap γ₄ = ln(5/3) | Lean ✓ | `FeshbachJ4.lean` |
| Feshbach discriminant Δ = 7 (prime, unique to d=4) | Lean ✓ | `ChamberPolynomialTheory.lean` |
| Char poly (5λ−3)(150λ²−50λ+3) = 0 | Lean ✓ | `FeshbachJ4.lean` |

### Quantum Mechanics (derived, not postulated)

| Result | Status | Key File |
|--------|--------|----------|
| Complex amplitudes from K/P | Lean ✓ | `ComplexFromDressing.lean` |
| Born rule \|z\|² unique | Lean ✓ | `BornRuleUnique.lean` |
| Bell violation CHSH² = 8 > 4 | Lean ✓ | `BellTheorem.lean` |
| No spooky action at a distance | Lean ✓ | `NoSpookyAction.lean` |
| Decoherence → classical | Lean ✓ | `Decoherence.lean` |
| Poset growth = Born rule | Lean ✓ | `PosetGrowthIsQuantum.lean` |
| QM is a theorem | Lean ✓ | `QuantumMechanicsIsATheorem.lean` |

### Parameters (Layer 3 — conditional on two identifications)

| Observable | Predicted | Measured | Agreement |
|-----------|-----------|---------|-----------|
| Higgs mass m_H | ln(5/3) · v = 125.78 GeV | 125.10 ± 0.14 GeV | 0.54% |
| Higgs quartic λ_H | [ln(5/3)]²/2 = 0.1305 | ~0.13 | ~1% |
| Electroweak scale v | 240.6 GeV | 246 GeV | 2.3% |
| Mass hierarchy shape | ln(5−√7)/ln(5+√7) = 0.421 | 0.436 | 3.5% |
| Cabibbo angle (Fritzsch) | 0.224 | 0.225 | 0.5% |
| Proton mass (with Λ_QCD) | 941 MeV | 938 MeV | 0.3% |

### Resolved Foundational Debates

| Debate | Resolution | Key File |
|--------|-----------|----------|
| Information paradox | Finite → invertible → unitary | `InformationParadox.lean` |
| Hierarchy problem | γ₄ = ln(5/3) is O(1), scale-invariant | `HierarchyProblem.lean` |
| Problem of time | Partial order IS time | `ProblemOfTime.lean` |
| Why something? | Flat grid beats empty set | `WhySomething.lean` |
| Continuous time | Emergent from discrete chains | `ContinuousTimeEmergent.lean` |
| Big Bang | Poset minimum | `BigBangIsPosetMinimum.lean` |
| Anti-gravity | Impossible (3 routes) | `AntiGravityImpossible.lean` |

### Four Falsifiable Predictions

| Prediction | Test | Key File |
|-----------|------|----------|
| No axion at any mass | ADMX, CAST, ALPS II | `FalsifiablePredictions.lean` |
| P-sector DM at ~126 GeV | HL-LHC invisible Higgs | `FalsifiablePredictions.lean` |
| BH remnants at 6 M_P | Hawking evaporation endpoint | `FalsifiablePredictions.lean` |
| Normal ν ordering, m₁ ≈ 5 μeV | JUNO, CMB-S4, Euclid | `FalsifiablePredictions.lean` |

## Three Layers, Three Risk Profiles

**Layer 1 (unconditional).** Theorems of finite mathematics. Do not depend on the Hauptvermutung or any physical identification. Proved in `HauptvermutungIndependence.lean`.

**Layer 2 (conditional on Hauptvermutung).** Einstein's equation, holographic bound, cosmological constant. Require the causal set to be manifold-like.

**Layer 3 (conditional on two identifications).** Higgs mass, electroweak scale, mass hierarchy. Require Layer 1 plus:
- `IdentificationChain.lean`: λ_H = γ₄²/2
- `VEVIdentificationChain.lean`: v = M_P exp(−c/g²) with g² = 2

## What Is Not Derived

- **α ≈ 1/137** — requires non-perturbative Monte Carlo
- **CKM/PMNS mixing matrices** — one-loop Feshbach effect
- **Dark matter abundance** — thermal freeze-out dynamics
- **Λ_QCD** — non-perturbative lattice computation

These are dynamical quantities at the algebra/dynamics boundary.

## Lean Formalization

**430+ files. 1,800+ theorems. Zero sorry. Zero custom axioms.**

```bash
lake build          # builds everything
```

### Capstone Files

| File | Assembles |
|------|-----------|
| `ConditionalEinstein.lean` | RG + null + K/P + Lovelock → Einstein |
| `Capstone.lean` | Metric + connection → gravity + gauge + quantum |
| `MasterCapstone.lean` | `standard_model_is_a_theorem` (21 results) |
| `PhysicsFromCounting.lean` | `physics_is_counting` (23 results) |

### Companion Repository

The algebraic/combinatorial foundations: [causal-algebraic-geometry-lean](https://github.com/tomdif/causal-algebraic-geometry-lean)

Combined: 430+ files, 1,800+ theorems, zero sorry, zero custom axioms across both repos.

## Citation

```bibtex
@article{difiore2026time,
  title={Time is a Partial Order: The Standard Model, the Higgs Mass,
         and the Electroweak Scale from a Single Ontological Postulate},
  author={DiFiore, Thomas},
  year={2026},
  note={Lean 4 formalization: 430+ files, 1800+ theorems,
        zero sorry, zero custom axioms}
}
```

## License

Apache 2.0
