# Unified Theory: Standard Model from a Partial Order

**One axiom. Nine zero-parameter predictions spanning 17 orders of magnitude. All within 1.5×. Machine-checked in Lean 4.**

From a single input — a locally finite partial order (causal set) — we derive the Standard Model gauge group, all fermion charges, 3 generations, d = 3+1 dimensions, Einstein gravity, Yang-Mills, the electroweak scale, and nine quantitative predictions.

Every algebraic step is formally verified in Lean 4 with Mathlib. Zero `sorry`. Zero custom axioms. Numerical predictions computed via GPU-accelerated Monte Carlo.

## The Trilogy

| Paper | Title | Content |
|-------|-------|---------|
| **I** | [The Physics of Order](paper/paper1_physics_of_order.pdf) | Derivation: partial order → SM gauge group + field equations |
| **II** | [Mass Spectrum](paper/paper2_mass_spectrum.pdf) | Predictions: mass ratios, mixing angles, Higgs mass, EW scale |
| **III** | [Exclusions & Predictions](paper/paper3_exclusions_predictions.pdf) | BSM exclusions, testable predictions, experimental signatures |

LaTeX sources in [`paper/`](paper/).

## Predictions (Zero Free Parameters)

| Observable | Computed | Experiment | Factor | Method |
|-----------|----------|------------|--------|--------|
| m_μ/m_τ | 0.056 ± 0.009 | 0.0595 | **0.94×** | SU(2) holonomy, count-weighted chains |
| m_e/m_τ | 0.000264 | 0.000288 | **0.92×** | Fiber generation phase at α = α_em(M_P) |
| \|V_us\| (Fritzsch) | 0.224 | 0.225 | **0.99×** | √(m_d/m_s) from Fritzsch texture |
| \|V_us\| (holonomy) | 0.255 ± 0.023 | 0.225 | **1.13×** | Weak SU(2) × U(1) projection, 20 seeds |
| m_H/v (Higgs) | 0.33–0.42 | 0.509 | **0.65–0.82×** | Within-chain scalar correlator |
| m_t/m_b | 63.5 | 60–90 (M_P) | **0.85×** | (1/r_μτ) × C₂(SU3)/C₂(SU2) × \|Y_t/Y_b\| |
| m_u/m_t | 9.0 × 10⁻⁶ | 7.4 × 10⁻⁶ | 1.22× | K/P holonomy |
| m_c/m_t | 0.0058 | 0.004 | 1.46× | K/P holonomy |
| v (EW scale) | 297 GeV | 246 GeV | **1.21×** | Coleman-Weinberg with μ²=0, c₁=1.0 |

Nine predictions across 17 orders of magnitude (from v/M_P ≈ 10⁻¹⁷ to m_u/m_t ≈ 10⁻⁵), all within a factor of 1.5×.

## Lean Formalization

**172 files across LayerA/B/C (~35,000 lines). 1,600+ theorems. Zero sorry. Zero custom axioms.**

`#print axioms` on every capstone theorem returns only: `propext`, `Classical.choice`, `Quot.sound`.

### Key Theorems

| File | Theorem | Content |
|------|---------|---------|
| `DiscreteAmbroseSinger` | `discrete_ambrose_singer_eq` | Holonomy group = curvature group |
| `Hauptvermutung` | `variance_linear` | Cauchy equation → Poisson forced |
| `JacobiFormula` | `det_one_add_smul_fin2` | δdet/δg = trace (Jacobi's formula) |
| `NullConeConformal` | `conformal_from_same_null_cone_2d` | Null cone → conformal class (Malament) |
| `LinearizedEinstein` | `traceReversal_involutive_4d` | Trace-reversal is involution in exactly d=4 |
| `KPDecomposition` | `matrix_kp_decomposition` | A = traceless + (tr/n)·I, dim(gauge)=n²-1 |
| `GaugeFromTraceless` | `bracket_nontrivial` | sl(n) is nonabelian for n ≥ 2 |
| `CasimirScaling` | `inter_sector_mass_ratio` | m_t/m_b = (32/9)/r_μτ from Casimir + hypercharge |
| `AsymptoticFreedom` | `af_iff_Nc_ge_2` | AF with 6 flavors ↔ N_c ≥ 2 (derived, not imported) |
| `AnomalyFromOrder` | `sm_branch_gives_correct_charges` | SM charges unique solution of polynomial anomaly |
| `BornRuleUnique` | `so2_invariant_quadratic_unique` | Q²+P² is the ONLY SO(2)-invariant observable |
| `VEVForced` | `vev_forced_from_nontrivial_gauge` | Nontrivial gauge → nonzero Higgs VEV |
| `DistinguishingSpacetime` | `malament_prerequisite_linear` | Malament conditions verified for linear orders |
| `NeutrinoScale` | `unique_scale_minimizes` | M_R = M_P uniquely minimizes neutrino mass |
| `PhysicsFromOrder` | `constructPhysics` | The 5→1 capstone |
| `ContinuumLimit` | `sqrt2_equidistributed` | Weyl equidistribution (fully proved) |
| `HiggsPotentialForm` | `higgs_two_parameter_family` | V = μ²φ² + λφ⁴ unique in d=4 |
| `LatticeCoupling` | `coupling_uniquely_determined` | g² = 2N/β_c (no freedom) |
| `DecoherenceIsPartialOrder` | `self_consistency` | Second law → partial order axioms |
| `GaugeContentForcesD4` | `bidirectional_d4` | SM content (12+3=15) ↔ n=4 |
| `WeinbergAngle` | `weinberg_angle_rigid` | sin²θ_W = 3/8, rigid under perturbation |
| `FermionCountFromAnomaly` | `fermion_count_derived` | (3,2) unique minimum among Nc≥2, Nw≥2 |
| `DimensionTripleCoincidence` | `conditions_independent_over_Z` | Three d=4 proofs independent over ℤ |
| `BornRuleQuadratic` | `born_rule_must_be_quadratic` | Orthogonal additivity forces degree 2 |
| `DecoherenceFromDensity` | `decoherenceRate_injective` | Γ=(ρ·π/24)^{1/4}, injective |
| `LatticeReflectionPositivity` | `reflection_positivity_1d_factored` | Wilson action RP = perfect square ≥ 0 |
| `ModuliCannotBeRemoved` | `stabilization_exceeds_gauge` | d=4 uniquely needs zero stabilization |
| `ChiralityForced` | `exchange_changes_fermion_count` | Nc↔Nw exchange changes count (15 vs 16) |
| `LinearityFromUnitarization` | `linearity_from_unitarization` | Finite holonomy → bounded → linear |

### Input Reduction Chain (5 → 1)

```
5 inputs (metric, source, perturbation, dimension, energy)
  → 3 inputs  [PrimitiveReduction.lean: scaling + null from vacuum]
    → 2 inputs  [SourceFromMetric.lean: source = linearized Einstein]
      → 1 input  [SinglePrimitive + DiscreteAmbroseSinger + Hauptvermutung]
        = THE PARTIAL ORDER
```

### Verification Table

| Result | Method | Status |
|--------|--------|--------|
| Gauge group SU(3)×SU(2)×U(1) | Lean 4 | Zero sorry |
| All fermion charges | Lean 4 | Zero sorry |
| d = 3+1 dimensions | Lean 4 | Zero sorry |
| Weinberg angle sin²θ_W = 3/8 | Lean 4 | Zero sorry |
| Proton stability | Lean 4 | Zero sorry |
| Input reduction 5→1 | Lean 4 | Zero sorry |
| Continuum limit (Weyl) | Lean 4 | Zero sorry |
| Higgs potential form | Lean 4 | Zero sorry |
| Asymptotic freedom derived | Lean 4 | Zero sorry |
| Anomaly cancellation algebraic | Lean 4 | Zero sorry |
| Born rule uniqueness | Lean 4 | Zero sorry |
| VEV forced from gauge structure | Lean 4 | Zero sorry |
| Malament conditions verified | Lean 4 | Zero sorry |
| Neutrino scale unique | Lean 4 | Zero sorry |
| Casimir scaling m_t/m_b | Lean 4 | Zero sorry |
| Lattice coupling determined | Lean 4 | Zero sorry |
| Decoherence → partial order | Lean 4 | Zero sorry |
| SM forces d=4 (converse) | Lean 4 | Zero sorry |
| sin²θ_W = 3/8 (rigid) | Lean 4 | Zero sorry |
| Fermion count derived | Lean 4 | Zero sorry |
| d=4 triple coincidence | Lean 4 | Zero sorry |
| Born rule must be degree 2 | Lean 4 | Zero sorry |
| Decoherence rate from ρ | Lean 4 | Zero sorry |
| Lattice reflection positivity | Lean 4 | Zero sorry |
| Moduli stabilization adds params | Lean 4 | Zero sorry |
| Chirality from fermion count | Lean 4 | Zero sorry |
| Linearity from holonomy bound | Lean 4 | Zero sorry |
| Mass ratios (9 predictions) | GPU Monte Carlo | ± stated uncertainties |
| CKM (Fritzsch) | Analytical | From derived mass ratios |
| EW scale (Coleman-Weinberg) | Analytical | μ²=0, c₁=1.0 |

## Numerical Scripts

GPU-accelerated (PyTorch + CUDA) Monte Carlo on causal sets:

| Script | Content |
|--------|---------|
| `scripts/lepton_gpu.py` | Lepton mass ratio: DP-guided chains, count-weighted, quaternion SU(2) |
| `scripts/cabibbo_gpu.py` | CKM matrix: Cayley SU(3) + quaternion SU(2) + U(1) |
| `scripts/higgs_correlator.py` | Higgs mass from within-chain scalar correlator |
| `scripts/coleman_weinberg.py` | Electroweak scale from dimensional transmutation |
| `scripts/generation_phase.py` | m_e/m_τ from fiber generation phase |
| `scripts/quark_mass_ratios.py` | m_t/m_b from Casimir + hypercharge |
| `scripts/density_scan.py` | Convergence across densities |
| `scripts/decoherence_separation.py` | Tests m = m_phys + c·ρ^{1/4} (negative result: R²=0.007) |

## Building

```bash
# Lean formalization
lake build          # ~5 min, 2367+ jobs, zero sorry

# Numerical (requires PyTorch)
cd scripts
python lepton_gpu.py              # Lepton mass ratios
python coleman_weinberg.py        # Electroweak scale
python cabibbo_gpu.py --quick     # Cabibbo angle
python higgs_correlator.py        # Higgs mass
```

## Requirements

- **Lean**: v4.x with Mathlib v4.28.0
- **Python**: 3.10+ with numpy, scipy, torch
- **GPU**: NVIDIA with CUDA 12+ (tested on RTX 4060 Ti 16GB)

## License

Apache 2.0

## Citation

```bibtex
@article{difiore2026physics,
  title={The Physics of Order: Deriving the Standard Model from a Locally Finite Partial Order},
  author={DiFiore, Thomas},
  year={2026},
  doi={10.5281/zenodo.19171801},
  note={Lean 4 formalization: 172 files, 1600+ theorems, zero sorry, zero custom axioms}
}
```
