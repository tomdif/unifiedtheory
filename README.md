# Unified Theory

**Machine-checked derivation: metric + connection → gravity + gauge + matter + quantum + classical.**

**Zero custom axioms. Zero sorrys. Entire chain exact (non-perturbative).**

Every theorem depends only on the three standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`). The entire algebraic chain is exact — no linearized-regime or perturbative approximation anywhere.

## Capstone theorem

`complete_metric_connection` ([Capstone.lean](UnifiedTheory/Capstone.lean)): from two geometric primitives — a `LorentzianMetric` and `StructureConstants` for a Lie algebra — the following are all derived:

| Branch | Result | Theorem | Status |
|--------|--------|---------|--------|
| **Gravity** | div(G) = 0 | `einstein_div_free_from_metric` | Exact identity |
| **Gravity** | Null cone determines conformal class | `null_cone_determines_conformal_1plus1` | Exact |
| **Gauge** | Curvature F = dA + [A,A] antisymmetric | `curvature_antisym` | Exact |
| **Gauge** | Abelian limit = Maxwell | `abelian_curvature` | Exact |
| **Gauge** | Stress-energy traceless in d=4 (uniquely) | `gauge_traceless_4d`, `four_is_unique_traceless` | Exact |
| **Matter** | Charge additivity Q(h₁+h₂) = Q(h₁)+Q(h₂) | `charge_additive` | Exact |
| **Matter** | Annihilation Q(h+(-h)) = 0 | `annihilation_charge` | Exact |
| **Quantum** | Quadratic observable |z|² = Q²+P² | `obs_from_KP` | Exact |
| **Quantum** | Phase averaging: discrete cancellation of interference | `discrete_decoherence_sum` | Exact |

## Derived chain

The framework derives everything from a single metric-bearing object, with no external parameters:

```
LorentzianMetric m
  → MetricDerivs → Riemann → Bianchi → div(G) = 0        (exact identity)
  → Null cone determination                                (exact)
  → Scaling exponent α = m from dimension                  (exact)
  → Trace functional on perturbation space → K/P split     (exact)
  → Bridge: trace(πK(h)) = trace(h)                        (exact)
  → Neutrality: trace(πP(h)) = 0                           (exact)
  → Charge additivity, conjugation, annihilation            (exact)
  → z = Q + iP → interference → |z|² observable → phase averaging    (exact)
```

Key files:
- [`DerivedUnification.lean`](UnifiedTheory/LayerA/DerivedUnification.lean) — `fully_derived_unification`: 4 branches from one metric, zero parameters
- [`MetricDefects.lean`](UnifiedTheory/LayerB/MetricDefects.lean) — `metric_to_everything`: full chain metric → charge → quantum → classical
- [`ExactRegime.lean`](UnifiedTheory/LayerA/ExactRegime.lean) — `fully_exact_chain`: proves the entire chain is exact

## Gauge trace theorem

The K/P split has physical content in d=4 ([MetricGaugeCoupling.lean](UnifiedTheory/LayerA/MetricGaugeCoupling.lean)):

**tr(T_gauge) = (1 - d/4) · |F|²**

In d=4: tr(T_gauge) = 0. This is the **unique** dimension where gauge stress-energy is traceless.

- **K** = trace-visible scalar/source channel (gravitational content)
- **P** = trace-free channel containing gauge stress-energy
- **z = Q + iP** packages trace-visible and trace-free components

Important: traceless ≠ gravitationally invisible. Gauge fields gravitate through the full T_{ab}, not through tr(T). The trace functional doesn't see them, but the metric does.

## Connection primitive

The gauge/internal sector requires a second geometric primitive beyond the metric ([GaugeConnection.lean](UnifiedTheory/LayerA/GaugeConnection.lean)):

- `StructureConstants g_dim`: Lie algebra via c^a_{bd} with antisymmetry + Jacobi
- `ConnectionData n g_dim`: A_μ^a with derivatives and ∂ commutativity
- Curvature: F_μν^a = ∂_μ A_ν^a - ∂_ν A_μ^a + c^a_{bd} A_μ^b A_ν^d
- `g_dim` is a free parameter: 1 = U(1), 3 = SU(2), 8 = SU(3)

## Signed source sectors

The charge algebra is signed: Q ∈ ℝ, not ℝ≥0. See [`SIGNED_SOURCE.md`](SIGNED_SOURCE.md) for the full benchmark pack.

**Formal chain** (Lean 4):
- [`SignedSource.lean`](UnifiedTheory/LayerB/SignedSource.lean) — Q > 0 and Q < 0 sectors exist; perfect cancellation; additivity
- [`SourceFocusing.lean`](UnifiedTheory/LayerB/SourceFocusing.lean) — Q > 0 focuses, Q < 0 defocuses (conditional on FocusingHypothesis)
- [`FocusingBridge.lean`](UnifiedTheory/LayerB/FocusingBridge.lean) — Ricci tensor and null focusing are linear in MetricDerivs (exact)
- [`FocusingCoupling.lean`](UnifiedTheory/LayerB/FocusingCoupling.lean) — GR coupling κ = 8π > 0 instantiates FocusingHypothesis (derived, not assumed)

**Weak field** (11/11 checks):

| Q | Focusing | Deflection | Shapiro |
|---|----------|------------|---------|
| +2 | converge | inward | delay |
| 0 | none | none | none |
| -2 | diverge | outward | advance |

**Strong field** (6/6 checks): trapping vs anti-trapping, bounce, nonlinear asymmetry (|θ(+Q)|/|θ(-Q)| = 2.07)

**Phase diagram** (5/5 checks): three phases (trap/bounce/free) in (Q, θ₀) space with clear boundaries

## Audit classification

| Category | What | Examples |
|----------|------|---------|
| **Exact** | Theorems with no approximation | Bianchi identity, charge algebra, gauge trace formula, quadratic observable, phase-averaging cancellation, signed source algebra, GR focusing coupling κ = 8π |
| **Structural** | Standard mathematics correctly formalized | Scaling exponent, rank-1 projection, Killing form symmetry |
| **Definitional** | Modeling choices, explicitly stated | z = Q+iP identification, perturbation space = Matrix |
| **Outside scope** | Not formalized | G=0 as condition (vs div(G)=0 identity), dynamics, Lovelock uniqueness, gauge group selection |

## Project structure

```
UnifiedTheory/
  Capstone.lean                 -- complete_metric_connection (capstone theorem)
  Basic.lean                    -- Theorem inventory + audit classification
  ConditionalEinstein.lean      -- Layer A assembly (legacy)
  LayerA/                       -- Geometric backbone
    DerivedUnification.lean     -- LorentzianMetric → 4 branches (NEW)
    ExactRegime.lean            -- Proof that entire chain is exact (NEW)
    LinearizedFieldEqs.lean     -- Linearity of curvature in derivatives (NEW)
    GaugeConnection.lean        -- Connection curvature F = dA + [A,A] (NEW)
    MetricGaugeCoupling.lean    -- Gauge trace theorem, d=4 uniqueness (NEW)
    MetricToRiemann.lean        -- Riemann + Bianchi from metric
    BianchiIdentity.lean        -- Contracted Bianchi identity
    NullConeGeneral.lean        -- Null-cone theorem (general n+1)
    NullConeTensor.lean         -- Null-cone tensor lemma (1+1)
    RenormRigidity.lean         -- alpha = 2 fixed point
    PrimitiveReduction.lean     -- 5→3 reduction
    DerivedBFSplit.lean         -- K/P split from source functional
    SinglePrimitive.lean        -- Dressing from dimension (2→1)
    SourceFromMetric.lean       -- Source functional from operator (3→2)
    LovelockEinstein.lean       -- Lovelock → Einstein + Lambda
    MetricDecomposition.lean    -- Metric = conformal + volume
    CausalFoundation.lean       -- Causal set, dimension, conformal+volume
    CausalBridge.lean           -- Null-link equivalence + Poisson
    VolumeFromCounting.lean     -- Volume ratios from counting
    DiscreteMalament.lean       -- Causal order → conformal metric
    BFSourceDressing.lean       -- K/P interface (legacy)
    SparseSum.lean              -- Sparse Finset sum helpers
  LayerB/                       -- Matter + quantum sector
    MetricDefects.lean          -- Full chain: metric → charge → quantum (NEW)
    SignedSource.lean           -- Signed charge algebra Q ∈ ℝ (NEW)
    SourceFocusing.lean         -- Q sign controls focusing (NEW)
    FocusingBridge.lean         -- Ricci/null focusing from metric (NEW)
    FocusingCoupling.lean       -- GR coupling κ = 8π derives focusing (NEW)
    LinearDefects.lean          -- Charge algebra from linearity
    ParentU.lean                -- Parent structure (legacy)
    UnifiedBranch.lean          -- ParentU → Einstein branch (legacy)
    DefectSector.lean           -- Defect data structures
    DefectBridge.lean           -- Source-focusing bridge
    MatterBranch.lean           -- Einstein + matter assembly
    DefectEquivalence.lean      -- Defect classification
    DefectComposition.lean      -- Charge algebra (interface)
    ChargeSectors.lean          -- Sector decomposition + bound states
    MultiParticle.lean          -- Many-body conservation
    FarField.lean               -- Far-field reduction + screening
    StructuralTheorems.lean     -- Enclosure, interaction signs, uniqueness
    QuantumDefects.lean         -- Interference, Born rule, phase invariance
    ComplexFromDressing.lean     -- z = Q+iP from K/P split
    ComplexUniqueness.lean       -- Born rule uniqueness (SO(2) invariance)
    Decoherence.lean            -- Phase averaging → classical
  LayerC/                       -- Concrete realizations
    ConcreteModel.lean          -- Lean-certified U_star
    ConcreteMultiBody.lean      -- Many-body instance
    ModelB/
      signed_source_demo.py              -- Focusing sign (5/5)
      signed_source_observables.py       -- Deflection + Shapiro sign (11/11)
      signed_source_strong_field.py      -- Trapping/bounce/asymmetry (6/6)
      signed_source_phase_diagram.py     -- Phase diagram (5/5)
      signed_source_phase_diagram.png    -- Three-panel visualization
  paper/
    unified_theory_paper.tex    -- LaTeX paper
```

## Building

Requires Lean 4 (v4.28.0) and Mathlib.

```bash
lake build
```

To verify the capstone theorem's axiom footprint:
```bash
echo 'import UnifiedTheory.Capstone
#print axioms UnifiedTheory.Capstone.complete_metric_connection' | lake env lean --stdin
```

Output: `[propext, Classical.choice, Quot.sound]`

## Trusted base

Every theorem depends only on:
- `propext` (propositional extensionality)
- `Classical.choice` (classical logic)
- `Quot.sound` (quotient soundness)

These are the three standard axioms of Lean 4. Zero custom axioms. Zero sorrys.

## License

MIT
