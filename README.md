# Unified Theory

**Machine-checked derivation: metric + Lie algebra → gravity + gauge + matter + quantum + classical.**

**Zero custom axioms. Zero sorrys. Complete 4D Lovelock uniqueness. Quantum structure uniqueness.**

Every theorem depends only on the three standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`). The entire chain is exact — no linearized-regime or perturbative approximation anywhere.

## What's new (Session 58)

Major upgrades across all sectors:

| Sector | Before | After |
|--------|--------|-------|
| **Gravity** | div(G) = 0 (kinematic identity) | Complete 4D Lovelock: a·G + Λ·g is the **unique** field equation (tensorial, second-order natural class) |
| **Matter** | Charge additivity stipulated | Charge additivity **derived** from linearity (`map_add`) |
| **Quantum** | obs := \|z\|² (definition) | Born rule **uniqueness**: the only rotation-invariant quadratic observable |
| **Decoherence** | Trig identity | Density matrix dephasing: γ=0 is the **unique** classical limit |
| **Primitives** | 3 (metric + Lie algebra + connection) | **2 structural + 2 dynamical** (connection is a field, not a primitive) |
| **Parameters** | Uncounted | **1 free parameter** (ρ = discreteness density) |

## Capstone theorem

`complete_metric_connection` ([Capstone.lean](UnifiedTheory/Capstone.lean)): from two structural primitives — a `LorentzianMetric` and `StructureConstants` for a Lie algebra — the following are all derived:

| Branch | Result | Theorem | How derived |
|--------|--------|---------|-------------|
| **Gravity** | div(G) = 0 | `einstein_div_free_from_metric` | Bianchi identity (kinematic) |
| **Gravity** | G + Λ·g = 0 is the unique field eq. | `complete_lovelock_4d` | Lovelock uniqueness (dynamic) |
| **Gravity** | Null cone determines conformal class | `null_cone_determines_conformal_1plus1` | Linear algebra |
| **Gauge** | Curvature F = dA + [A,A] antisymmetric | `curvature_antisym` | Lie bracket antisymmetry |
| **Gauge** | Stress-energy traceless in d=4 (uniquely) | `gauge_traceless_4d` | Trace formula derivation |
| **Matter** | Charge additivity Q(h₁+h₂) = Q(h₁)+Q(h₂) | `charge_additive` | Linearity (`map_add`) |
| **Matter** | Annihilation Q(h+(-h)) = 0 | `annihilation_charge` | Linearity (`add_neg_cancel`) |
| **Quantum** | Born rule is unique | `complex_observable_unique` | Rotation invariance forces a(Q²+P²) |
| **Quantum** | Decoherence → classical | `decoherence_dynamical` | Dephasing γ=0 uniquely recovers additivity |

## Gravity: from kinematics to dynamics

The gravity sector now has a complete derivation chain:

```
g → R → Bianchi → ∇ᵃGₐᵦ = 0 → complete 4D Lovelock uniqueness → a·G + Λ·g
```

| Layer | What | File | Status |
|-------|------|------|--------|
| **Kinematic** | div(G) = 0 for ALL metrics | BianchiIdentity | PROVEN |
| **Contraction** | Ric is the only rank-2 δ-contraction of Riemann | VariationalEinstein | PROVEN |
| **Bianchi constraint** | div-free forces d = -c/2 → a·G + Λ·g | LovelockEinstein | PROVEN |
| **Gauss-Bonnet** | H_{ab} ≡ 0 in d=4 (rank-5 delta vanishes by pigeonhole) | GaussBonnet4D | PROVEN |
| **Higher Lovelock** | All p≥2 Lovelock tensors vanish in d=4 | GaussBonnet4D | PROVEN |
| **ε-exclusion** | ε·ε = δ, tensor parity excludes pseudotensors | LovelockComplete | PROVEN |
| **Variational** | Stationarity + non-degeneracy → field equation | VariationalEinstein | PROVEN |
| **Assembly** | `complete_lovelock_4d` | LovelockComplete | PROVEN |

**Scope**: Complete 4D Lovelock uniqueness within the tensorial, second-order natural class. Higher derivatives restricted by hypothesis (Ostrogradsky stability).

## Primitive reduction

The framework has **2 structural primitives** and **2 dynamical fields**:

| | Gravity | Gauge |
|---|---|---|
| **Structural primitive** | Manifold (dim n) | Lie algebra (dim g) |
| **Dynamical field** | Metric g | Connection A |
| **Curvature** | R_{abcd} | F_{μν}^a |
| **Field equation** | G + Λ·g = 0 (Lovelock) | ∂^μ F_μν = 0 (Yang-Mills) |
| **Derivation** | Variational | Variational |

The connection is NOT an independent primitive — it is a dynamical field on the Lie algebra, selected by the Yang-Mills equation. See [`GaugeDerived.lean`](UnifiedTheory/LayerA/GaugeDerived.lean).

## Quantum uniqueness

Every step in the quantum derivation is a **uniqueness** theorem:

| Step | What's unique | Theorem |
|------|---------------|---------|
| K/P split | The only rank-1 source-capturing projection | `sourceProj_unique` |
| Algebra | ℂ is the only 2D real division algebra | `complexification_unique` |
| Observable | a·(Q²+P²) is the only rotation-invariant quadratic obs | `complex_observable_unique` |
| Composition | Sum-then-square is the only faithful nonlinear rule | `amplitude_rule_unique` |
| Classical limit | γ=0 is the only fully decohered state | `classical_limit_unique` |

See [`QuantumUniqueness.lean`](UnifiedTheory/LayerB/QuantumUniqueness.lean) and [`AmplitudeUniqueness.lean`](UnifiedTheory/LayerB/AmplitudeUniqueness.lean).

## Matter: charge algebra derived from linearity

Charge additivity is **derived**, not stipulated:

```
compose = vector addition  →  charge_linear ∘ perturbation is linear  →  map_add  →  Q(h₁+h₂) = Q(h₁) + Q(h₂)
```

The `ComposableDefectBlock` structure exposes the linear primitives (`perturbation`, `charge_linear`, `compose_is_add`), and charge algebra follows from `map_add`, `map_neg`, `add_neg_cancel`.

**Dynamical stability** ([`DynamicalStability.lean`](UnifiedTheory/LayerB/DynamicalStability.lean)): the kernel of any linear field equation operator is a valid stability predicate. Charge algebra holds on the physical (on-shell) subspace.

## Parameter budget

The framework has exactly **1 continuous free parameter** (the discreteness density ρ):

| Constant | Status | How determined |
|----------|--------|----------------|
| ρ (density) | **FREE** | The one free parameter |
| n (dimension) | Discrete | Structural choice (n=4) |
| g_dim (gauge) | Discrete | Structural choice |
| α (scaling) | Derived | α = n-2 from dimension |
| κ (coupling) | Derived | κ = 8π from Einstein |
| a (Born coeff) | Derived | Normalization (a=1) |

Volume ratios are parameter-free (ρ cancels). See [`NormalizationTheorem.lean`](UnifiedTheory/LayerA/NormalizationTheorem.lean).

## Substrate bridge

A Poisson point process on a Lorentzian manifold automatically satisfies all conditions assumed by the causal reconstruction chain. See [`SubstrateBridge.lean`](UnifiedTheory/LayerA/SubstrateBridge.lean).

## Project structure

```
UnifiedTheory/
  Capstone.lean                 -- complete_metric_connection (capstone theorem)
  Basic.lean                    -- Theorem inventory + audit + primitive justification
  ConditionalEinstein.lean      -- Layer A assembly (legacy)
  LayerA/                       -- Geometric backbone
    VariationalEinstein.lean    -- Ricci/scalar/Einstein tensors, variational principle
    GaussBonnet4D.lean          -- Gauss-Bonnet vanishing in 4D (pigeonhole)
    LovelockComplete.lean       -- Complete 4D Lovelock (ε·ε=δ, parity, assembly)
    GaugeDerived.lean           -- Connection as dynamical field, primitive reduction
    SubstrateBridge.lean        -- Poisson substrate satisfies causal conditions
    NormalizationTheorem.lean   -- 1 free parameter (ρ), parameter budget
    DerivedUnification.lean     -- LorentzianMetric → 4 branches
    ExactRegime.lean            -- Exact kinematic + dynamic chain
    LinearizedFieldEqs.lean     -- Linearity of curvature
    GaugeConnection.lean        -- F = dA + [A,A], Killing form
    MetricGaugeCoupling.lean    -- Gauge trace theorem, d=4 uniqueness
    MetricToRiemann.lean        -- Riemann + Bianchi from metric
    BianchiIdentity.lean        -- Contracted Bianchi identity
    LovelockEinstein.lean       -- Bianchi constraint step
    NullConeGeneral.lean        -- Null-cone theorem (general n+1)
    NullConeTensor.lean         -- Null-cone tensor lemma (1+1)
    RenormRigidity.lean         -- alpha = 2 fixed point
    PrimitiveReduction.lean     -- 5→3 reduction
    DerivedBFSplit.lean         -- K/P split from source functional
    SinglePrimitive.lean        -- Dressing from dimension
    SourceFromMetric.lean       -- Source functional from operator
    CausalFoundation.lean       -- Causal set, dimension, conformal+volume
    CausalBridge.lean           -- Null-link equivalence + Poisson
    VolumeFromCounting.lean     -- Volume ratios from counting
    DiscreteMalament.lean       -- Causal order → conformal metric
    MetricDecomposition.lean    -- Metric = conformal + volume
    BFSourceDressing.lean       -- K/P interface (legacy)
    SparseSum.lean              -- Sparse Finset sum helpers
  LayerB/                       -- Matter + quantum sector
    QuantumUniqueness.lean      -- K/P universal property + quantum inevitability
    AmplitudeUniqueness.lean    -- Sum-then-square is unique amplitude rule
    DensityMatrix.lean          -- Density matrix dephasing decoherence
    DynamicalStability.lean     -- Stability from field equations (ker(L))
    MetricDefects.lean          -- Full chain: metric → charge → quantum
    DefectComposition.lean      -- Charge algebra (derived from linearity)
    LinearDefects.lean          -- LinearDefectBlock → ComposableDefectBlock
    SignedSource.lean           -- Signed charge algebra Q ∈ ℝ
    SourceFocusing.lean         -- Q sign controls focusing
    FocusingBridge.lean         -- Ricci/null focusing from metric
    FocusingCoupling.lean       -- GR coupling κ = 8π
    HistoryAmplitudes.lean      -- Sum-over-histories interference
    ComplexificationUniqueness.lean -- ℂ unique 2D division algebra
    EnvironmentDecoherence.lean -- Phase-averaging decoherence
    ComplexFromDressing.lean    -- z = Q+iP from K/P split
    ComplexUniqueness.lean      -- Born rule uniqueness (SO(2))
    Decoherence.lean            -- Fourier decomposition + phase averaging
    QuantumDefects.lean         -- Interference, Born rule, phase invariance
    DefectSector.lean           -- Defect data structures
    DefectEquivalence.lean      -- Defect classification
    ChargeSectors.lean          -- Sector decomposition + bound states
    MultiParticle.lean          -- Many-body conservation
    FarField.lean               -- Far-field reduction + screening
    StructuralTheorems.lean     -- Enclosure, interaction signs
    ParentU.lean                -- Parent structure (legacy)
    UnifiedBranch.lean          -- ParentU → Einstein branch (legacy)
    DefectBridge.lean           -- Source-focusing bridge
    MatterBranch.lean           -- Einstein + matter assembly
    RiemannAction.lean          -- Riemann action functional
    NonCommutative.lean         -- Matrix non-commutativity
  LayerC/                       -- Concrete realizations
    ConcreteModel.lean          -- Lean-certified U_star
    ConcreteMultiBody.lean      -- Many-body instance
    ModelB/                     -- Python benchmarks
  paper/
    unified_theory_paper.tex    -- LaTeX paper
```

## Building

Requires Lean 4 (v4.28.0) and Mathlib.

```bash
lake build
```

To verify key theorem axiom footprints:
```bash
echo 'import UnifiedTheory.Capstone
import UnifiedTheory.LayerA.LovelockComplete
import UnifiedTheory.LayerB.QuantumUniqueness
#print axioms UnifiedTheory.Capstone.complete_metric_connection
#print axioms UnifiedTheory.LayerA.LovelockComplete.complete_lovelock_4d
#print axioms UnifiedTheory.LayerB.QuantumUniqueness.quantum_structure_inevitable' | lake env lean --stdin
```

Output: `[propext, Classical.choice, Quot.sound]` for all three.

## Trusted base

Every theorem depends only on:
- `propext` (propositional extensionality)
- `Classical.choice` (classical logic)
- `Quot.sound` (quotient soundness)

These are the three standard axioms of Lean 4. Zero custom axioms. Zero sorrys.

## License

MIT
