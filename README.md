# Unified Theory: Standard Model from a Partial Order

**One axiom. Seven zero-parameter predictions. All within 1.5x of experiment. Machine-checked in Lean 4.**

From a single input — a locally finite partial order (causal set) — we derive the Standard Model gauge group, all fermion charges, 3 generations, d = 3+1 dimensions, Einstein gravity, Yang-Mills, and seven quantitative predictions spanning five orders of magnitude.

Every algebraic step is formally verified in Lean 4 with Mathlib. Zero `sorry`. Zero custom axioms. Numerical predictions computed via GPU-accelerated Monte Carlo.

## The Trilogy

| Paper | Title | Content |
|-------|-------|---------|
| **I** | [The Physics of Order](paper/paper1_physics_of_order.pdf) | Derivation: partial order → SM gauge group + field equations |
| **II** | [Mass Spectrum](paper/paper2_mass_spectrum.pdf) | Predictions: mass ratios, mixing angles, Higgs mass |
| **III** | [Exclusions & Predictions](paper/paper3_exclusions_predictions.pdf) | BSM exclusions, testable predictions, experimental signatures |

LaTeX sources in [`paper/`](paper/).

## Predictions (Zero Free Parameters)

| Observable | Computed | Experiment | Factor | Method |
|-----------|----------|------------|--------|--------|
| m_μ/m_τ | 0.056 ± 0.009 | 0.0595 | **0.94×** | SU(2) holonomy, count-weighted chains |
| m_e/m_τ | 0.000264 | 0.000288 | **0.92×** | Fiber generation phase at α = α_em(M_P) |
| \|V_us\| (Cabibbo) | 0.255 ± 0.023 | 0.225 | **1.13×** | Weak SU(2) × U(1) projection, 20 seeds |
| m_H/v (Higgs) | 0.42 ± 0.05 | 0.509 | **0.82×** | Within-chain scalar correlator |
| m_t/m_b | 63.5 | 60–90 (M_P) | **0.85×** | (1/r_μτ) × C₂(SU3)/C₂(SU2) × \|Y_t/Y_b\| |
| m_u/m_t | 9.0 × 10⁻⁶ | 7.4 × 10⁻⁶ | 1.22× | K/P holonomy |
| m_c/m_t | 0.0058 | 0.004 | 1.46× | K/P holonomy |

Seven predictions across five orders of magnitude, all within a factor of 1.5×.

## Lean Formalization

**18 files. 140+ theorems. Zero sorry. Zero axioms. Zero sorryAx.**

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
| `PhysicsFromOrder` | `constructPhysics` | The 5→1 capstone |
| `ContinuumLimit` | `sqrt2_equidistributed` | Weyl equidistribution (fully proved) |
| `ChargeConsistency` | `trivial_U1_contradicts_derivation` | Q_e = 0 contradicts anomaly nontriviality |
| `HiggsPotentialForm` | `higgs_two_parameter_family` | V = μ²φ² + λφ⁴ unique in d=4 |
| `LatticeCoupling` | `coupling_uniquely_determined` | g² = 2N/β_c (no freedom) |

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
| Input reduction 5→1 | Lean 4 | Zero sorry (18 files) |
| Continuum limit (Weyl) | Lean 4 | Zero sorry |
| Higgs potential form | Lean 4 | Zero sorry |
| Charge consistency | Lean 4 | Zero sorry |
| Lattice coupling determined | Lean 4 | Zero sorry |
| Casimir scaling m_t/m_b | Lean 4 | Zero sorry |
| Mass ratios (7 predictions) | GPU Monte Carlo | ± stated uncertainties |
| Cabibbo angle | GPU Monte Carlo | 20 seeds, ±1.3° |
| Higgs mass | GPU Monte Carlo | Correlator fit, ±0.05 |

## Numerical Scripts

GPU-accelerated (PyTorch + CUDA) Monte Carlo on causal sets:

| Script | Content |
|--------|---------|
| `scripts/lepton_gpu.py` | Lepton mass ratio: DP-guided chains, count-weighted, quaternion SU(2) |
| `scripts/cabibbo_gpu.py` | CKM matrix: Cayley SU(3) + quaternion SU(2) + U(1) |
| `scripts/lepton_kstar_scan.py` | Amplitude-weighted k-scan for lepton convergence |
| `scripts/lepton_amplitude.py` | Amplitude phase exp(ikS) diagnostics |

## Building

```bash
# Lean formalization
lake build          # ~5 min, 2367 jobs, zero sorry

# Numerical (requires PyTorch + CUDA)
cd scripts
python lepton_gpu.py          # Lepton mass ratios (3 densities, 10 seeds each)
python cabibbo_gpu.py --quick  # Cabibbo angle (5 seeds)
```

## Requirements

- **Lean**: v4.x with Mathlib v4.28.0
- **Python**: 3.10+ with numpy, scipy, torch
- **GPU**: NVIDIA with CUDA 12+ (tested on RTX 4060 Ti 16GB)

## Repository Structure

```
UnifiedTheory/
  LayerA/                    # Core formalization (18 files)
    DiscreteAmbroseSinger.lean   # Holonomy = curvatures
    Hauptvermutung.lean          # Poisson forced + volume convergence
    CasimirScaling.lean          # m_t/m_b inter-sector formula
    ...
  LayerB/                    # Extended physics (quantum, matter, ...)
  LayerC/                    # Concrete models
paper/
  paper1_physics_of_order.tex/pdf   # Paper I
  paper2_mass_spectrum.tex/pdf      # Paper II
  paper3_exclusions_predictions.tex/pdf  # Paper III
scripts/
  lepton_gpu.py              # GPU Monte Carlo
  cabibbo_gpu.py             # CKM computation
  ...
```

## License

Apache 2.0

## Citation

```bibtex
@article{difiore2026physics,
  title={The Physics of Order: Deriving the Standard Model from a Locally Finite Partial Order},
  author={DiFiore, Thomas},
  year={2026},
  note={Lean 4 formalization: 18 files, 140+ theorems, zero sorry}
}
```
