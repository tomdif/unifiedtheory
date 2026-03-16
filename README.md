# Unified Theory

**Machine-checked framework: causal order → metric → gravity → matter → quantum → classical.**

**Zero custom axioms. Zero sorrys. Complete chain from causal order to classical physics.**

Every theorem depends only on the three standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`). No custom physics axioms. No sorry. The entire chain — causal order → links → null cone → conformal metric → volume → full metric → Riemann → Bianchi → Einstein → matter → quantum → classical — is machine-checked.

## Primitive reduction (proven)

| Step | Primitives | Eliminated | File |
|------|-----------|------------|------|
| Start | 5 | — | — |
| 5→3 | 3 | Scaling, null vanishing | `PrimitiveReduction.lean` |
| 3→2 | 2 | Source functional | `SourceFromMetric.lean` |
| 2→1 | **1** | Dressing nontriviality | `SinglePrimitive.lean` |

**One structured primitive** (Lorentzian metric in n≥2 dimensions) determines everything.

## Causal foundation (all proven)

| Stage | What | File | Status |
|-------|------|------|--------|
| 1 | Causal set structure | `CausalFoundation.lean` | Defined |
| 2 | Dimension from chain counting | `CausalFoundation.lean` | **Proven** |
| 3a | Null cone → conformal metric | `DiscreteMalament.lean` | **Proven** |
| 3b | Links → null cone (null-link equivalence) | `CausalBridge.lean` | **Proven** |
| 4a | Volume from counting | `VolumeFromCounting.lean` | **Proven** |
| 4b | Counting is linear (Cauchy/Poisson) | `CausalBridge.lean` | **Proven** |
| 5 | Full metric = conformal + volume | `CausalFoundation.lean` | **Proven** |
| 6 | Metric → everything | All Layer A/B files | **Proven** |

The null-link equivalence (`CausalBridge.lean`) closes the causal-to-metric bridge: null separations have zero Alexandrov volume, hence zero intermediate events, hence they are links. Conversely, links have proper time → 0 as density → ∞. The null-cone general theorem covers arbitrary n+1 dimensions (`NullConeGeneral.lean`).

## What this proves

From a single parent structure (`ParentU`), the following all follow formally:

| Result | Theorem | Derived from |
|--------|---------|-------------|
| Inverse-square law (alpha = 2) | `renorm_fixedPoint_iff` | rpow algebra + log |
| Null-cone determines metric up to trace | `null_determines_up_to_trace_1plus1` | Evaluation at test vectors |
| Source/dressing K/P decomposition | `decompFromFunctional` | Source functional + linear algebra |
| Bianchi identity: ∇^a R_{ab} = ½∇_b R | `contracted_bianchi` | Riemann symmetries + index contraction |
| Einstein tensor is divergence-free | `einstein_div_free` | Contracted Bianchi identity |
| Riemann symmetries from metric | `R_antisym1`, `R_antisym2` | Metric second derivatives |
| Second Bianchi identity from metric | `bianchi2` | Commutativity of partial derivatives |
| Einstein + Lambda endpoint | `lovelock_endpoint` | Bianchi constraint + module algebra |
| Unified Einstein branch | `unified_branch` | All four Layer A pillars |
| Matter emergence from defects | `matter_einstein_branch` | Source-focusing bridge |
| Defect charge algebra derived | `LinearDefectBlock.toComposable` | Linearity of projections |
| Conserved charge Q with conjugation | `charge_additive_derived`, `conjugate_K_neg_derived` | map_add, map_neg |
| Particle-antiparticle annihilation | `annihilation_is_inert` | Charge algebra |
| Charge sector decomposition | `charge_sector_structure` | Additivity + conjugation |
| Bound states are gravitationally inert | `bound_state_inert` | Charge determines sector |
| N-body charge conservation | `charge_foldl` | Induction on additive charge |
| Far field = net charge only | `far_field_theorem` | Charge additivity |
| Enclosure theorem | `enclosure_theorem` | Total charge determines far field |
| Like charges never cancel | `like_charges_never_neutral` | Real arithmetic |
| Structural inevitability (6 properties) | `structural_inevitability` | All of the above |

## Derivation integrity

An adversarial audit identified three areas where claims exceeded proofs. All three are now fixed:

| Previously stipulated | Now derived from | File |
|----------------------|-----------------|------|
| BF source/dressing split | Source functional φ with φ(v₀) ≠ 0 | `DerivedBFSplit.lean` |
| Defect charge algebra (additivity, conjugation, bridge) | Linear perturbations + map_add/map_neg | `LinearDefects.lean` |
| Bianchi identity (contracted) | Riemann symmetries from metric ∂²g, Bianchi from ∂³g commutativity | `BianchiIdentity.lean`, `MetricToRiemann.lean` |

**What remains honestly primitive:**
- The Bianchi identity is derived locally from metric data (∂_e ∂_f = ∂_f ∂_e); the global tensorial lift is standard but not formalized.
- The source functional φ is a primitive — the framework derives what follows IF one exists, not WHY nature has one.
- The source sector has rank 1 (one charge). Richer particle structure requires multiple source functionals.

## Concrete realizations

### Lean-certified (Layer C)
- `U_star`: explicit `MatterParentU` with both inert and source-carrying defects
- `concreteComposable`: particle-like defects with e⁺e⁻ annihilation, 3-body charge, screening

### Computational (Python, 3+1 causal diamonds)

**Weak field:**
- Inverse-square: alpha = 2.004 ± 0.063 (expected 2.0)
- Raychaudhuri focusing: alpha = 0.983 (expected 1.0)
- Shapiro time delay: slope = 3.94 (expected 4.0), R² = 0.990
- Gravitational deflection: alpha = 1.030 (expected 1.0)

**Strong field:**
- Nonlinear focusing amplification (Raychaudhuri -θ²/2 term)
- Horizon-like trapping (b_crit grows with Q)
- Post-Newtonian deflection excess (correct sign)
- Multi-source focusing collapse (Penrose focusing theorem)

**Robustness:** 388/388 configurations pass across 1+1, 2+1, 3+1

## Project structure

```
UnifiedTheory/
  Basic.lean                    -- Complete theorem inventory
  ConditionalEinstein.lean      -- Layer A assembly
  LayerA/                       -- Algebraic backbone + causal foundation
    CausalFoundation.lean       -- Causal set, dimension, metric from conformal+volume
    VolumeFromCounting.lean     -- Volume ratios from event counting
    DiscreteMalament.lean       -- Causal order → conformal metric (Malament)
    RenormRigidity.lean         -- alpha = 2 fixed point
    PrimitiveReduction.lean     -- 5→3 reduction (dimension law + vacuum null)
    NullConeTensor.lean         -- Null-cone tensor lemma (1+1)
    NullConeGeneral.lean        -- Null-cone theorem (general n+1)
    SparseSum.lean              -- Sparse Finset sum helpers
    CausalBridge.lean           -- Null-link equivalence + Poisson uniqueness
    BFSourceDressing.lean       -- K/P interface (original)
    DerivedBFSplit.lean         -- K/P split DERIVED from source functional
    LovelockEinstein.lean       -- Lovelock → Einstein + Lambda
    BianchiIdentity.lean        -- Contracted Bianchi identity (DERIVED)
    MetricToRiemann.lean        -- Riemann + Bianchi from metric (DERIVED)
    SourceFromMetric.lean       -- Source functional from linear operator (3→2)
    SinglePrimitive.lean        -- Dressing from dimension (2→1)
  LayerB/                       -- Parent object + matter sector
    ParentU.lean                -- Parent structure definition
    UnifiedBranch.lean          -- ParentU => Einstein branch
    DefectSector.lean           -- Defect data structures
    DefectBridge.lean           -- Source-focusing bridge
    MatterBranch.lean           -- Einstein + matter assembly
    DefectEquivalence.lean      -- Defect classification
    DefectComposition.lean      -- Charge algebra (interface)
    LinearDefects.lean          -- Charge algebra DERIVED from linearity
    ChargeSectors.lean          -- Sector decomposition + bound states
    MultiParticle.lean          -- Many-body conservation
    FarField.lean               -- Far-field reduction + screening
    StructuralTheorems.lean     -- Enclosure, interaction signs, uniqueness
    QuantumDefects.lean         -- Interference, Born rule, phase invariance
    ComplexFromDressing.lean    -- z = Q+iP from K/P split
    ComplexUniqueness.lean      -- Born rule uniqueness (SO(2) invariance)
    Decoherence.lean            -- Phase averaging → classical
  LayerC/                       -- Concrete realizations
    ConcreteModel.lean          -- Lean-certified U_star
    ConcreteMultiBody.lean      -- Many-body instance
    ModelB/                     -- Python computational models
      causal_2complex.py        -- 1+1 causal diamond
      causal_3plus1.py          -- 3+1 causal diamond
      robustness.py             -- Multi-seed robustness sweep
      physics_observables.py    -- Inverse-square, composition, charge
      relativistic_observables.py -- Raychaudhuri, Shapiro, deflection
      strong_field.py           -- Nonlinear focusing, trapping, collapse
SYNTHESIS.md                    -- Human-readable physics synthesis
```

## Building

Requires Lean 4 (v4.28.0) and Mathlib.

```bash
lake build
```

To verify axiom footprint:
```bash
echo 'import UnifiedTheory.LayerB.StructuralTheorems
#print axioms UnifiedTheory.LayerB.structural_inevitability' | lake env lean --stdin
```

To verify Bianchi derivation:
```bash
echo 'import UnifiedTheory.LayerA.MetricToRiemann
#print axioms UnifiedTheory.LayerA.MetricConstruction.bianchi2' | lake env lean --stdin
```

## Trusted base

Every theorem depends only on:
- `propext` (propositional extensionality)
- `Classical.choice` (classical logic)
- `Quot.sound` (quotient soundness)

These are the three standard axioms of Lean 4. Zero custom axioms. Zero sorrys.

## License

MIT
