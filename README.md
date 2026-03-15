# Unified Theory

**Formally verified unified Einstein + matter branch, machine-checked in Lean 4.**

All theorems depend only on the three standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`). No custom physics axioms. No sorry. No opaque types.

## What this proves

From a single parent structure (`ParentU`), the following all follow formally:

| Result | Theorem |
|--------|---------|
| Inverse-square law (alpha = 2) | `renorm_fixedPoint_iff` |
| Null-cone determines metric up to trace | `null_determines_up_to_trace_1plus1` |
| Source/dressing K/P decomposition | `SourceDressingDecomp.decompose` |
| Einstein + Lambda endpoint | `lovelock_endpoint` |
| Unified Einstein branch | `unified_branch` |
| Matter emergence from defects | `matter_einstein_branch` |
| Conserved charge Q with conjugation | `charge_additive`, `charge_conjugate` |
| Particle-antiparticle annihilation | `annihilation_is_inert` |
| Charge sector decomposition | `charge_sector_structure` |
| Bound states are gravitationally inert | `bound_state_inert` |
| N-body charge conservation | `charge_foldl` |
| Far field = net charge only | `far_field_theorem` |
| Enclosure theorem | `enclosure_theorem` |
| Like charges never cancel | `like_charges_never_neutral` |
| Sector exhaustion (no third sector) | `sector_trichotomy` |
| Charge algebra uniqueness | `charge_algebra_unique` |
| Structural inevitability (6 properties) | `structural_inevitability` |

## Concrete realizations

### Lean-certified (Layer C)
- `U_star`: explicit `MatterParentU` with both inert and source-carrying defects
- `concreteComposable`: particle-like defects with e+e- annihilation, 3-body charge, screening

### Computational (Python, 3+1 causal diamonds)
- **Inverse-square**: alpha = 2.004 +/- 0.063 (expected 2.0)
- **Raychaudhuri focusing**: alpha = 0.983 (expected 1.0)
- **Shapiro time delay**: slope = 3.94 (expected 4.0), R^2 = 0.990
- **Gravitational deflection**: alpha = 1.030 (expected 1.0)
- **Strong-field**: nonlinear amplification, horizon trapping, focusing collapse
- **Robustness**: 388/388 configurations pass across 1+1, 2+1, 3+1

## Project structure

```
UnifiedTheory/
  Basic.lean                    -- Theorem inventory + dependency graph
  ConditionalEinstein.lean      -- Layer A assembly
  LayerA/                       -- Algebraic backbone (4 pillars)
    RenormRigidity.lean         -- alpha = 2 fixed point
    NullConeTensor.lean         -- Null-cone tensor lemma
    BFSourceDressing.lean       -- K/P decomposition
    LovelockEinstein.lean       -- Lovelock -> Einstein + Lambda
  LayerB/                       -- Parent object + matter sector
    ParentU.lean                -- Parent structure definition
    UnifiedBranch.lean          -- ParentU => Einstein branch
    DefectSector.lean           -- Defect data structures
    DefectBridge.lean           -- Source-focusing bridge
    MatterBranch.lean           -- Einstein + matter assembly
    DefectEquivalence.lean      -- Defect classification
    DefectComposition.lean      -- Charge algebra
    ChargeSectors.lean          -- Sector decomposition + bound states
    MultiParticle.lean          -- Many-body conservation
    FarField.lean               -- Far-field reduction + screening
    StructuralTheorems.lean     -- Enclosure, interaction signs, uniqueness
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
echo 'import UnifiedTheory
#print axioms UnifiedTheory.LayerB.structural_inevitability' | lake env lean --stdin
```

## Trusted base

Every theorem depends only on:
- `propext` (propositional extensionality)
- `Classical.choice` (classical logic)
- `Quot.sound` (quotient soundness)

These are the three standard axioms of Lean 4. No physics axioms are assumed.

## License

MIT
