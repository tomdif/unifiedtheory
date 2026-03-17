# Unified Theory

**Machine-checked formalization: metric + Lie algebra → gravity + gauge + matter + quantum + classical.**

**Zero custom axioms. Zero sorrys. 4D Lovelock uniqueness (within tensorial second-order natural class). Quantum observable uniqueness (within rotation-invariant quadratic class).**

Every theorem depends only on the three standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`). The entire chain is exact — no linearized-regime or perturbative approximation anywhere.

## What's new (Session 58)

Major upgrades across all sectors:

| Sector | Before | After |
|--------|--------|-------|
| **Gravity** | div(G) = 0 (kinematic identity) | 4D Lovelock: a·G + Λ·g is the unique field eq. within tensorial, second-order, δ-contraction natural class |
| **Matter** | Charge additivity stipulated as structure field | Charge additivity follows from modeling choice: composition = addition + linear charge functional |
| **Quantum** | obs := \|z\|² (definition) | Born rule uniqueness: the only rotation-invariant quadratic observable (within that class) |
| **Decoherence** | Trig identity | Density matrix dephasing model: γ=0 is the unique fully decohered state |
| **Primitives** | 3 (metric + Lie algebra + connection) | **2 structural + 2 dynamical** (connection is a field, not a primitive) |
| **Parameters** | Uncounted | **1 free parameter** (ρ = discreteness density) |

## Capstone theorem

`complete_metric_connection` ([Capstone.lean](UnifiedTheory/Capstone.lean)): from two structural primitives — a `LorentzianMetric` and `StructureConstants` for a Lie algebra — the following are all derived:

| Branch | Result | Theorem | How derived | Scope |
|--------|--------|---------|-------------|-------|
| **Gravity** | div(G) = 0 | `einstein_div_free_from_metric` | Bianchi identity | Kinematic identity, all metrics |
| **Gravity** | Null cone → conformal class | `null_cone_determines_conformal_1plus1` | Linear algebra | 1+1 dimensions |
| **Gauge** | F = dA + [A,A] antisymmetric | `curvature_antisym` | Lie bracket antisymmetry | From StructureConstants |
| **Gauge** | Stress-energy traceless in d=4 | `gauge_traceless_4d` | Trace formula | Uniquely d=4 |
| **Matter** | Charge additivity | `charge_additive` | `map_add` on `charge_linear` | Given compose = addition |
| **Matter** | Annihilation Q(h+(-h)) = 0 | `annihilation_charge` | `add_neg_cancel` | Given conjugate = negation |
| **Quantum** | Born rule uniqueness | `complex_observable_unique` | SO(2) invariance | Within quadratic class |
| **Quantum** | Discrete decoherence | `discrete_decoherence_sum` | Phase flip cancellation | 2-point averaging |

**Not in the capstone theorem** (separate files):

| Result | Theorem | File | Scope |
|--------|---------|------|-------|
| Lovelock uniqueness in 4D | `complete_lovelock_4d` | LovelockComplete | Within tensorial, second-order, δ-contraction class |
| Gauss-Bonnet vanishing | `gaussBonnet_vanishes_4d` | GaussBonnet4D | Rank-5 delta, pigeonhole |
| Density matrix decoherence | `decoherence_dynamical` | DensityMatrix | Dephasing model |
| Amplitude rule uniqueness | `amplitude_rule_unique` | AmplitudeUniqueness | Given linearity + rotation inv. |
| K/P split uniqueness | `sourceProj_unique` | QuantumUniqueness | Given rank-1 + source-capturing |

## Gravity: from kinematics to dynamics

The gravity sector has a layered derivation chain:

```
g → R → Bianchi → ∇ᵃGₐᵦ = 0  (kinematic, all metrics)
                 → Lovelock → a·G + Λ·g  (within restricted class)
```

| Layer | What | File | Status | Scope |
|-------|------|------|--------|-------|
| **Kinematic** | div(G) = 0 for ALL metrics | BianchiIdentity | PROVEN | Unconditional identity |
| **Contraction** | Ric is only rank-2 δ-contraction of Riemann | VariationalEinstein | PROVEN | Within δ-contractions |
| **Bianchi constraint** | div-free within {c·Ric+d·R·g+e·g} forces a·G+Λ·g | LovelockEinstein | PROVEN | Within parametric family |
| **Gauss-Bonnet** | H_{ab} ≡ 0 in d=4 | GaussBonnet4D | PROVEN | Pigeonhole on rank-5 delta |
| **Higher Lovelock** | All p≥2 tensors vanish in d=4 | GaussBonnet4D | PROVEN | Same mechanism |
| **ε-exclusion** | ε·ε = δ converts ε-pairs to δ-contractions | LovelockComplete | PROVEN | Even ε-count only |
| **Parity** | Odd ε-count → pseudotensor → excluded | LovelockComplete | PROVEN | For true tensors |
| **Variational** | Stationarity + non-degeneracy → E-L tensor = 0 | VariationalEinstein | PROVEN | Local action density |

**Scope**: 4D Lovelock uniqueness within the tensorial, second-order, δ-contraction natural class. Higher derivatives restricted by hypothesis. The action is formalized as a local density (not a manifold integral). The Gauss-Bonnet tensor is defined via the generalized Kronecker delta formalism. The standard-form quantities (|Riem|², |Ric|², R², and the Euler density G₄ = |Riem|² - 4|Ric|² + R²) are also defined in `GaussBonnet4D.lean`. The algebraic identity between the Kronecker and standard forms is documented but the 24-term expansion is not yet formalized.

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

## Quantum uniqueness (within stated classes)

Each step in the quantum layer is a uniqueness theorem within an explicit class:

| Step | What's unique | Theorem | Assumed class |
|------|---------------|---------|---------------|
| K/P split | Only rank-1 source-capturing projection | `sourceProj_unique` | Given: range ⊆ span{v₀}, φ∘π = φ |
| Algebra | Only 2D real commutative division algebra | `complexification_unique` | Given: 2D, commutative, α < 0 |
| Observable | Only rotation-invariant quadratic observable | `complex_observable_unique` | Given: quadratic, SO(2)-invariant, a > 0 |
| Composition | Equal-weight sum is the only symmetric linear rule | `additive_rule_unique` | Given: linear, permutation-symmetric |
| Classical limit | γ=0 is the only value killing all coherence | `classical_limit_unique` | Given: dephasing model γ·c |

**Honest scope**: These are uniqueness theorems WITHIN explicitly stated classes. The assumptions (quadratic, rotation-invariant, linear, etc.) are conditions, not derived from deeper principles. A Hardy/CDP-style derivation of these conditions from operational axioms is not formalized.

See [`QuantumUniqueness.lean`](UnifiedTheory/LayerB/QuantumUniqueness.lean) and [`AmplitudeUniqueness.lean`](UnifiedTheory/LayerB/AmplitudeUniqueness.lean).

## Matter: charge algebra from linear structure

Charge additivity follows from two modeling choices:
1. **Composition = vector addition** (`compose_is_add` — a primitive, not derived)
2. **Charge = linear functional** (`charge_linear : V →ₗ[ℝ] ℝ` — a primitive, not derived)

Given these choices, additivity is a `map_add` consequence:
```
Q(h₁ ⊕ h₂) = charge_linear(perturbation(h₁) + perturbation(h₂))
            = charge_linear(perturbation(h₁)) + charge_linear(perturbation(h₂))
            = Q(h₁) + Q(h₂)
```

**What's primitive**: composition = addition, charge = linear functional.
**What follows**: additivity, conjugation, annihilation (from `map_add`, `map_neg`, `add_neg_cancel`).
**What's NOT derived**: why composition should be addition, or why charge should be linear.

**Dynamical stability**: Two versions are available:
- `metricLinearDefectBlock`: uses `Stable := True` (algebraic, all perturbations)
- `metricDynamicalDefectBlock L`: uses `Stable := ker(L)` for any linear operator L (physical, on-shell only)

Both give valid charge algebras. The dynamical version ([`MetricDefects.lean`](UnifiedTheory/LayerB/MetricDefects.lean), `on_shell_charge_algebra`) proves additivity, annihilation, and zero-stability hold on-shell.

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

## Honest scope assessment

| Claim | Actual status | Qualification |
|-------|---------------|---------------|
| "Complete 4D Lovelock" | PROVEN within class | Within tensorial, second-order, δ-contraction natural class. Gauss-Bonnet tensor defined via generalized Kronecker delta, not standard textbook form. |
| "Charge derived from linearity" | FOLLOWS from primitives | Composition = addition and charge = linear functional are primitives. Additivity follows trivially from `map_add`. |
| "Born rule uniqueness" | PROVEN within class | Within rotation-invariant quadratic observables. Rotation invariance and quadratic assumption are conditions, not derived. |
| "Decoherence is dynamical" | PARTIALLY | DensityMatrix.lean has dephasing model. Decoherence.lean is discrete 2-point averaging, not continuous integration. |
| "Stable := True fixed" | YES | `metricDynamicalDefectBlock L` uses ker(L). `on_shell_charge_algebra` proves charge algebra on-shell. Both versions available. |
| "GB matches textbook form" | PARTIALLY | Standard quantities (Kretschner, Ric², R², Euler density) defined. 24-term Kronecker expansion not yet done. |
| "2 primitives" | CORRECT | Manifold + Lie algebra are structural; metric + connection are dynamical fields. |
| "1 free parameter" | CORRECT | ρ (discreteness density). All ratios are parameter-free. |
| "Zero axioms/sorrys" | VERIFIED | Only propext, Classical.choice, Quot.sound. |

**What this project IS**: A machine-checked formalization of the algebraic/kinematic structure connecting gravity, gauge theory, matter, and quantum mechanics, with uniqueness theorems within explicitly stated classes.

**What this project is NOT**: A complete derivation of physics from first principles. The assumptions (Lorentzian signature, Lie algebra structure, linear composition, rotation invariance, quadratic observables) are modeling choices, not derived from deeper axioms.

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
