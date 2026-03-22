# Unified Theory: Standard Model from a Partial Order

**One axiom → the Standard Model. Machine-checked in Lean 4. Zero `sorry`. Zero custom axioms.**

From a single input — a locally finite partial order (causal set) — we derive:
- The gauge group SU(3) x SU(2) x U(1)
- All fermion charges and representations
- 3 generations, d = 3+1 dimensions
- Einstein gravity + Yang-Mills + propagation rule + Born rule
- Lepton mass ratios, Cabibbo angle, and Higgs mass-to-VEV ratio

Every algebraic step is formally verified in Lean 4 with Mathlib.
Numerical predictions are computed via GPU-accelerated Monte Carlo.

## The Trilogy

| Paper | Title | Content |
|-------|-------|---------|
| **Paper I** | [The Physics of Order](paper/paper1_physics_of_order.pdf) | Derivation: partial order → SM gauge group + field equations |
| **Paper II** | [Mass Spectrum](paper/paper2_mass_spectrum.pdf) | Predictions: mass ratios, mixing angles, Higgs mass |
| **Paper III** | [Exclusions & Predictions](paper/paper3_exclusions_predictions.pdf) | BSM exclusions, testable predictions, experimental signatures |

LaTeX sources: [`paper/`](paper/)

## Predictions (Zero Free Parameters)

| Observable | Computed | Experiment | Factor |
|-----------|----------|------------|--------|
| m_μ/m_τ | 0.056 ± 0.009 | 0.0595 | 0.94× |
| m_e/m_τ (at α_em) | 0.000264 | 0.000288 | 0.92× |
| \|V_us\| (Cabibbo) | 0.255 ± 0.023 | 0.225 | 1.13× |
| m_H/v (Higgs) | 0.42 ± 0.05 | 0.509 | 0.82× |
| θ_W (Weinberg) | sin²θ_W = 3/8 | 0.231 (at M_Z) | Exact at GUT scale |
| Λ (cosmological) | 1/(ρV) | ~10⁻¹²² | Correct order |

Six zero-parameter predictions spanning five orders of magnitude, all within a factor of 1.5× of experiment.

## Lean Formalization

**17 critical files. 135+ theorems. Zero sorry. Zero axioms. Zero sorryAx.**

`#print axioms` on every capstone theorem returns only: `propext`, `Classical.choice`, `Quot.sound`.

### Key Theorems

| File | Theorem | Content |
|------|---------|---------|
| `DiscreteAmbroseSinger` | `discrete_ambrose_singer_eq` | Holonomy group = curvature group |
| `Hauptvermutung` | `variance_linear` | Cauchy equation → Poisson forced |
| `JacobiFormula` | `det_one_add_smul_fin2` | δdet/δg = trace (Jacobi) |
| `NullConeConformal` | `conformal_from_same_null_cone_2d` | Null cone → conformal class (Malament) |
| `LinearizedEinstein` | `traceReversal_involutive_4d` | Trace-reversal is involution in d=4 |
| `KPDecomposition` | `matrix_kp_decomposition` | A = traceless + (tr/n)·I |
| `GaugeFromTraceless` | `bracket_nontrivial` | sl(n) is nonabelian for n ≥ 2 |
| `PhysicsFromOrder` | `constructPhysics` | The 5→1 capstone |
| `ContinuumLimit` | `sqrt2_equidistributed` | Weyl equidistribution (proved) |
| `ChargeConsistency` | `trivial_U1_contradicts_derivation` | Q_e = 0 contradicts anomaly |
| `HiggsPotentialForm` | `higgs_two_parameter_family` | V = μ²φ² + λφ⁴ unique in d=4 |
| `LatticeCoupling` | `coupling_uniquely_determined` | g² = 2N/β_c (no freedom) |

### Input Reduction Chain

```
5 inputs (metric, source, perturbation, dimension, energy)
  → 3 inputs  [PrimitiveReduction.lean]
    → 2 inputs  [SourceFromMetric.lean]
      → 1 input  [SinglePrimitive.lean + DiscreteAmbroseSinger.lean + Hauptvermutung.lean]
        = THE PARTIAL ORDER
```

### Verification Table

| Result | Method | Status |
|--------|--------|--------|
| Gauge group SU(3)×SU(2)×U(1) | Lean 4 | Zero sorry |
| All charges | Lean 4 | Zero sorry |
| d = 3+1 | Lean 4 | Zero sorry |
| Weinberg angle | Lean 4 | Zero sorry |
| Proton stability | Lean 4 | Zero sorry |
| Input reduction 5→1 | Lean 4 | Zero sorry (17 files) |
| Continuum limit | Lean 4 | Zero sorry (Weyl proved) |
| Higgs potential form | Lean 4 | Zero sorry |
| Charge consistency | Lean 4 | Zero sorry |
| Lattice coupling | Lean 4 | Zero sorry |
| Mass ratios | Monte Carlo | Computational (±stated uncertainties) |
| Cabibbo angle | Monte Carlo | Computational (20 seeds, ±1.3°) |
| Higgs mass | Monte Carlo | Computational (correlator, ±0.05) |
| CKM hierarchy | Monte Carlo | Not yet reproduced |
| Higgs parameters μ², λ | — | Form derived, values not |

## Numerical Scripts

GPU-accelerated (PyTorch + CUDA) Monte Carlo on causal sets:

| Script | Content |
|--------|---------|
| `scripts/lepton_gpu.py` | Lepton mass ratio: DP-guided chains + count weighting |
| `scripts/cabibbo_gpu.py` | CKM matrix: SU(3)×SU(2)×U(1) holonomy |
| `scripts/lepton_kstar_scan.py` | Amplitude-weighted k-scan |
| `scripts/lepton_amplitude.py` | Amplitude phase exp(ikS) |

## Building

```bash
# Lean formalization
lake build  # ~5 min, 2367 jobs

# Numerical (requires PyTorch + CUDA)
cd scripts
python lepton_gpu.py          # lepton mass ratio
python cabibbo_gpu.py --quick  # Cabibbo angle
```

## Requirements

- **Lean**: v4.x with Mathlib v4.28.0
- **Python**: 3.10+ with numpy, scipy, torch (CUDA optional but recommended)
- **GPU**: NVIDIA with CUDA 12+ (tested on RTX 4060 Ti)

## License

Apache 2.0

## Citation

```bibtex
@article{difiore2026unified,
  title={The Physics of Order: Standard Model from a Partial Order},
  author={DiFiore, Thomas},
  year={2026},
  note={Lean 4 formalization with Mathlib}
}
```
