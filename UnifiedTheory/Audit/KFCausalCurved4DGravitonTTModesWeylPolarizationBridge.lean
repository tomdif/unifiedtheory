import UnifiedTheory.LayerA.GravitonTTModes
import UnifiedTheory.Audit.KFCausalCurved4DLovelockCosmologicalConstantSynthesis
import UnifiedTheory.Audit.KFCausalCurved4DTwentyComponentRiemannMasterSynthesis

/-! 4D Graviton Transverse-Traceless Mode Count (`gravitonTTModes 4 = 2`),
Explicit `+` and `×` Weyl Polarization Jet Realization, Electric-Magnetic
Energy Equipartition, and Curved Einstein-Sorkin-Yang-Mills Wave Superposition:
1. Connects `LayerA.GravitonTTModes` (`gravitonTotalComponents`,
   `gravitonGaugeReduction`, `gravitonTTModes`, `gravitonTTModes_eq`,
   `gravitonTTModes_d3 = 0`, `gravitonTTModes_d4 = 2`, `gravitonTTModes_d5 = 5`,
   `gravitonTTModes_d11 = 44`, `gravitonTTModes_d26 = 299`,
   `gravitonTTModes_eq_spatial_polarizations`, `gravitonTTModes_eq_TT_gauge_count`)
   to the 20-component 4D Riemann curvature split (`20 = 10 + 5 * gravitonTTModes 4`).
2. Defines the 2-parameter 4D graviton polarization jet
   `gravitonPolarizationJet4D A B = addMetricDerivs (plusWaveMetricDerivs4D A) (crossWaveMetricDerivs4D B)`
   and its `Fin (gravitonTTModes 4) → ℝ` vector parameterization
   `gravitonPolarizationVecJet4D`, proving exact tracelessness, Ricci/scalar/Einstein
   flatness, pure Weyl curvature (`R_metric = weylTensor4D`), and vanishing
   third-jet curvature derivatives (`dR_metric = 0`, `dEinstein = 0`, `dWeylTensor4D = 0`).
3. Proves exact gravito-electric and gravito-magnetic component readouts,
   transverse-plane trace-freeness (`E_{11} + E_{22} + E_{33} = 0`), quadratic
   polarization invariant `E_{11}^2 + E_{22}^2 + 2 E_{12}^2 = 2 (A^2 + B^2)`,
   exact electric-magnetic energy equipartition, and injectivity of `(A, B)`.
4. Proves that superposing `gravitonPolarizationJet4D A B` onto ANY curved 4D
   background `md : MetricDerivs 4` leaves `ricci`, `scalar`, `einstein`,
   `einsteinLovelock4D`, `einsteinSorkin4D`, and `SatisfiesEinsteinLovelockYangMills4D`
   strictly invariant while shifting the Weyl electric/magnetic tensors by `(A, B)`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCurved4DGravitonTTModesWeylPolarizationBridge
noncomputable section

open scoped BigOperators
open UnifiedTheory.LayerA.MetricConstruction (MetricDerivs R_metric dR_metric riemannFromMetric)
open UnifiedTheory.LayerA.Graviton (gravitonPolarizations)
open UnifiedTheory.LayerA.GravitonTTModes (gravitonTotalComponents
  gravitonGaugeReduction gravitonTTModes gravitonTTModes_eq
  gravitonTTModes_d3 gravitonTTModes_d4 gravitonTTModes_d5
  gravitonTTModes_d11 gravitonTTModes_d26
  gravitonTTModes_eq_spatial_polarizations gravitonTTModes_d4_eq_spatial
  tracelessReduction transversalityReduction diffeomorphismGaugeReduction
  residualGaugeReduction gravitonTTModes_eq_TT_gauge_count gravitonTTModes_master)
open UnifiedTheory.LayerA.GaugeConnection (StructureConstants ConnectionData)
open KFCausalConformal4DDiamondBenchmark (sign)
open KFCausalLorentzianContractedBianchi (ricci scalar einstein dRic divRic dScalar dEinstein)
open KFCausalCurved4DLinearizedMetricDecomposition (zeroMetricDerivs addMetricDerivs
  R_metric_zero R_metric_add dR_metric_add
  ricci_add scalar_add einstein_add dEinstein_add
  lorentzianMetricTrace4D metricTraceHessian4D conformalPartMetricDerivs4D
  conformalPartMetricDerivs4D_h_eq)
open KFCausalCurved4DLinearizedWeylRicciSplit (ricciCurvaturePart4D
  scalarCurvaturePart4D ricciScalarRiemannPart4D weylTensor4D
  ricciScalarRiemannPart4D_add weylTensor4D_add)
open KFCausalCurved4DWeylElectricMagneticDecomposition (weylElectric4D weylMagnetic4D
  weylElectric4D_zero weylElectric4D_add weylMagnetic4D_zero weylMagnetic4D_add)
open KFCausalCurved4DTidalWeylProbeExtraction (nullWaveVec4D
  plusPolarizationTensor4D crossPolarizationTensor4D
  plusWaveMetricDerivs4D crossWaveMetricDerivs4D
  plusWave_traceless crossWave_traceless
  plusWave_ricci_eq_zero crossWave_ricci_eq_zero
  plusWave_vacuum_pure_weyl crossWave_vacuum_pure_weyl
  plusWave_electric_and_magnetic_components crossWave_electric_and_magnetic_components)
open KFCausalCurved4DTwentyComponentRiemannMasterSynthesis
  (riemann_eq_iff_einstein_electric_magnetic_eq)
open KFCausalCurved4DDifferentialBianchiIdentity (dWeylTensor4D dWeylTensor4D_linearity
  plusWave_differential_curvature_zero crossWave_differential_curvature_zero)
open KFCausalCurved4DLovelockCosmologicalConstantSynthesis (einsteinLovelock4D
  einsteinSorkin4D SatisfiesEinsteinLovelockYangMills4D
  SatisfiesEinsteinSorkinYangMills4D)

variable {g_dim : ℕ}

/-! ### 1. Graviton Transverse-Traceless Mode Count & 20-Component 4D Riemann Accounting -/

/-- Closed-form formula `gravitonTTModes d = d * (d - 3) / 2` for every spacetime
dimension `d ≥ 3`. -/
theorem gravitonTTModes_closed_form (d : ℕ) (hd : 3 ≤ d) :
    gravitonTTModes d = d * (d - 3) / 2 :=
  gravitonTTModes_eq d hd

/-- In `d = 3` spacetime dimensions, there are zero propagating graviton modes. -/
theorem gravitonTTModes_dim3_eq_zero :
    gravitonTTModes 3 = 0 :=
  gravitonTTModes_d3

/-- In `d = 4` spacetime dimensions, there are exactly `2` propagating graviton
polarizations (`h₊` and `h_×`). -/
theorem gravitonTTModes_dim4_eq_two :
    gravitonTTModes 4 = 2 :=
  gravitonTTModes_d4

/-- In `d = 5` spacetime dimensions, there are `5` propagating graviton modes. -/
theorem gravitonTTModes_dim5_eq_five :
    gravitonTTModes 5 = 5 :=
  gravitonTTModes_d5

/-- In `d = 10` spacetime dimensions, there are `35` propagating graviton modes. -/
theorem gravitonTTModes_dim10_eq_thirtyfive :
    gravitonTTModes 10 = 35 := by
  unfold gravitonTTModes gravitonTotalComponents gravitonGaugeReduction
  decide

/-- In `d = 11` spacetime dimensions, there are `44` propagating graviton modes. -/
theorem gravitonTTModes_dim11_eq_fortyfour :
    gravitonTTModes 11 = 44 :=
  gravitonTTModes_d11

/-- In `d = 26` spacetime dimensions, there are `299` propagating graviton modes. -/
theorem gravitonTTModes_dim26_eq_299 :
    gravitonTTModes 26 = 299 :=
  gravitonTTModes_d26

/-- Exact 4D metric-perturbation component budget: `10` symmetric metric components
minus `8` diffeomorphism gauge reductions leaves `2` physical TT graviton modes. -/
theorem graviton4D_component_budget :
    gravitonTotalComponents 4 = 10 ∧
    gravitonGaugeReduction 4 = 8 ∧
    gravitonTTModes 4 = 2 ∧
    gravitonTotalComponents 4 - gravitonGaugeReduction 4 = 2 := by
  decide

/-- Equivalent 4D TT-gauge breakdown:
`gravitonTTModes 4 = 10 - 1 (traceless) - 4 (transverse) - 4 (gauge) + 1 (residual) = 2`. -/
theorem graviton4D_tt_gauge_breakdown :
    gravitonTTModes 4 =
      gravitonTotalComponents 4 -
        tracelessReduction -
        transversalityReduction 4 -
        diffeomorphismGaugeReduction 4 +
        residualGaugeReduction :=
  gravitonTTModes_eq_TT_gauge_count 4 (by decide)

/-- Agreement between the spacetime-indexed TT count `gravitonTTModes d` and the
spatial-indexed count `gravitonPolarizations (d - 1)` for `d ≥ 3` (and at `d = 4`). -/
theorem gravitonTTModes_spatial_agreement :
    (∀ d : ℕ, 3 ≤ d → gravitonTTModes d = gravitonPolarizations (d - 1)) ∧
    gravitonTTModes 4 = gravitonPolarizations 3 :=
  ⟨gravitonTTModes_eq_spatial_polarizations, gravitonTTModes_d4_eq_spatial⟩

/-- Exact accounting connecting `gravitonTotalComponents 4 = 10` and `gravitonTTModes 4 = 2`
to the 20 independent components of the 4D Riemann tensor (`10` Einstein/Ricci +
`5` gravito-electric Weyl + `5` gravito-magnetic Weyl = `10 + 5 * 2 = 20`). -/
theorem riemann4D_twenty_component_graviton_accounting :
    2 * gravitonTotalComponents 4 = 20 ∧
    5 * gravitonTTModes 4 = 10 ∧
    gravitonTotalComponents 4 + 5 * gravitonTTModes 4 = 20 := by
  decide

/-! ### 2. 2-Parameter 4D Graviton Polarization Jet `gravitonPolarizationJet4D` -/

/-- **2-Parameter 4D Graviton Polarization Jet**:
superposition of the `+`-polarized gravitational wave of amplitude `A` and the
`×`-polarized gravitational wave of amplitude `B`. -/
def gravitonPolarizationJet4D (A B : ℝ) : MetricDerivs 4 :=
  addMetricDerivs (plusWaveMetricDerivs4D A) (crossWaveMetricDerivs4D B)

/-- Vector-indexed 4D graviton polarization jet mapping a 2-component polarization
vector `p : Fin (gravitonTTModes 4) → ℝ` (`gravitonTTModes 4 = 2`) to `MetricDerivs 4`. -/
def gravitonPolarizationVecJet4D (p : Fin (gravitonTTModes 4) → ℝ) : MetricDerivs 4 :=
  gravitonPolarizationJet4D (p ⟨0, by decide⟩) (p ⟨1, by decide⟩)

/-- For `(A, B) = (0, 0)`, `gravitonPolarizationJet4D 0 0` has identically zero
Riemann tensor. -/
theorem gravitonPolarizationJet4D_zero (a b c d : Fin 4) :
    R_metric (gravitonPolarizationJet4D 0 0) a b c d = 0 := by
  have hp0 : ∀ e f i j : Fin 4, (plusWaveMetricDerivs4D 0).h e f i j = 0 := by
    intro e f i j
    unfold plusWaveMetricDerivs4D plusPolarizationTensor4D
    dsimp
    split_ifs <;> ring
  have hc0 : ∀ e f i j : Fin 4, (crossWaveMetricDerivs4D 0).h e f i j = 0 := by
    intro e f i j
    unfold crossWaveMetricDerivs4D crossPolarizationTensor4D
    dsimp
    split_ifs <;> ring
  unfold gravitonPolarizationJet4D
  rw [R_metric_add]
  unfold R_metric
  simp_rw [hp0, hc0]
  ring

/-- `gravitonPolarizationJet4D A B` is strictly traceless: its Lorentzian metric
trace, `metricTraceHessian4D`, and `conformalPartMetricDerivs4D` all vanish identically. -/
theorem gravitonPolarizationJet4D_traceless (A B : ℝ) (e f a b : Fin 4) :
    lorentzianMetricTrace4D (gravitonPolarizationJet4D A B) e f = 0 ∧
    metricTraceHessian4D (gravitonPolarizationJet4D A B) e f = 0 ∧
    (conformalPartMetricDerivs4D (gravitonPolarizationJet4D A B)).h e f a b = 0 := by
  have htr : lorentzianMetricTrace4D (gravitonPolarizationJet4D A B) e f = 0 := by
    have hadd : lorentzianMetricTrace4D (gravitonPolarizationJet4D A B) e f =
        lorentzianMetricTrace4D (plusWaveMetricDerivs4D A) e f +
          lorentzianMetricTrace4D (crossWaveMetricDerivs4D B) e f := by
      unfold lorentzianMetricTrace4D gravitonPolarizationJet4D addMetricDerivs
      dsimp
      simp_rw [mul_add, Finset.sum_add_distrib]
    rw [hadd, (plusWave_traceless A e f 0 0).1, (crossWave_traceless B e f 0 0).1, add_zero]
  have hH : metricTraceHessian4D (gravitonPolarizationJet4D A B) e f = 0 := by
    unfold metricTraceHessian4D
    rw [htr, mul_zero]
  have hC : (conformalPartMetricDerivs4D (gravitonPolarizationJet4D A B)).h e f a b = 0 := by
    rw [(conformalPartMetricDerivs4D_h_eq (gravitonPolarizationJet4D A B) e f a b).1, hH]
    ring
  exact ⟨htr, hH, hC⟩

/-- `gravitonPolarizationJet4D A B` is identically Ricci-flat (`Ric = 0`). -/
theorem gravitonPolarizationJet4D_ricci_zero (A B : ℝ) (b d : Fin 4) :
    ricci (gravitonPolarizationJet4D A B) sign b d = 0 := by
  unfold gravitonPolarizationJet4D
  rw [ricci_add, plusWave_ricci_eq_zero, crossWave_ricci_eq_zero, add_zero]

/-- `gravitonPolarizationJet4D A B` has identically zero scalar curvature (`R = 0`). -/
theorem gravitonPolarizationJet4D_scalar_zero (A B : ℝ) :
    scalar (gravitonPolarizationJet4D A B) sign = 0 := by
  unfold gravitonPolarizationJet4D
  rw [scalar_add, (plusWave_vacuum_pure_weyl A).1, (crossWave_vacuum_pure_weyl B).1, add_zero]

/-- `gravitonPolarizationJet4D A B` is an exact linearized Einstein-vacuum solution (`G = 0`). -/
theorem gravitonPolarizationJet4D_einstein_zero (A B : ℝ) (b d : Fin 4) :
    einstein (gravitonPolarizationJet4D A B) sign b d = 0 := by
  unfold gravitonPolarizationJet4D
  rw [einstein_add, (plusWave_vacuum_pure_weyl A).2.1 b d,
    (crossWave_vacuum_pure_weyl B).2.1 b d, add_zero]

/-- The Ricci-Scalar Kulkarni-Nomizu part `ricciScalarRiemannPart4D` vanishes
identically on `gravitonPolarizationJet4D A B`. -/
theorem gravitonPolarizationJet4D_ricciScalarPart_zero (A B : ℝ) (a b c d : Fin 4) :
    ricciScalarRiemannPart4D (gravitonPolarizationJet4D A B) a b c d = 0 := by
  unfold gravitonPolarizationJet4D
  rw [ricciScalarRiemannPart4D_add, (plusWave_vacuum_pure_weyl A).2.2.1 a b c d,
    (crossWave_vacuum_pure_weyl B).2.2.1 a b c d, add_zero]

/-- **Pure Weyl Curvature of 4D Graviton Polarizations**: the Riemann tensor of
`gravitonPolarizationJet4D A B` equals its Weyl tensor everywhere. -/
theorem gravitonPolarizationJet4D_pure_weyl (A B : ℝ) (a b c d : Fin 4) :
    R_metric (gravitonPolarizationJet4D A B) a b c d =
      weylTensor4D (gravitonPolarizationJet4D A B) a b c d := by
  unfold gravitonPolarizationJet4D
  rw [R_metric_add, weylTensor4D_add,
    (plusWave_vacuum_pure_weyl A).2.2.2 a b c d,
    (crossWave_vacuum_pure_weyl B).2.2.2 a b c d]

/-- Third-jet curvature operators (`dR_metric`, `dEinstein`, `dWeylTensor4D`)
vanish identically on `gravitonPolarizationJet4D A B`. -/
theorem gravitonPolarizationJet4D_differential_curvature_zero (A B : ℝ) :
    (∀ e a b c d : Fin 4, dR_metric (gravitonPolarizationJet4D A B) e a b c d = 0) ∧
    (∀ e b d : Fin 4,
      dEinstein (riemannFromMetric (gravitonPolarizationJet4D A B)) sign e b d = 0) ∧
    (∀ e a b c d : Fin 4, dWeylTensor4D (gravitonPolarizationJet4D A B) e a b c d = 0) := by
  have hp := plusWave_differential_curvature_zero A
  have hc := crossWave_differential_curvature_zero B
  refine ⟨fun e a b c d => ?_, fun e b d => ?_, fun e a b c d => ?_⟩
  · unfold gravitonPolarizationJet4D
    rw [dR_metric_add, hp.1, hc.1, add_zero]
  · unfold gravitonPolarizationJet4D
    rw [dEinstein_add, hp.2.2.2.2.1, hc.2.2.2.2.1, add_zero]
  · unfold gravitonPolarizationJet4D
    rw [(dWeylTensor4D_linearity e a b c d).2.1, hp.2.2.2.2.2, hc.2.2.2.2.2, add_zero]

/-! ### 3. Weyl Electric/Magnetic Readout, Energy Equipartition, and Injectivity -/

/-- Exact gravito-electric Weyl components of `gravitonPolarizationJet4D A B`:
`E_{11} = A`, `E_{22} = -A`, `E_{12} = B`, `E_{21} = B`, `E_{33} = 0`. -/
theorem gravitonPolarizationJet4D_weylElectric_components (A B : ℝ) :
    weylElectric4D (gravitonPolarizationJet4D A B) 1 1 = A ∧
    weylElectric4D (gravitonPolarizationJet4D A B) 2 2 = -A ∧
    weylElectric4D (gravitonPolarizationJet4D A B) 1 2 = B ∧
    weylElectric4D (gravitonPolarizationJet4D A B) 2 1 = B ∧
    weylElectric4D (gravitonPolarizationJet4D A B) 3 3 = 0 := by
  have hp := plusWave_electric_and_magnetic_components A
  have hc := crossWave_electric_and_magnetic_components B
  have hp21 : weylElectric4D (plusWaveMetricDerivs4D A) 2 1 = 0 := by
    have hW := (plusWave_vacuum_pure_weyl A).2.2.2 0 2 0 1
    unfold weylElectric4D
    rw [hW]
    simp [R_metric, plusWaveMetricDerivs4D, plusPolarizationTensor4D, nullWaveVec4D]
  have hc33 : weylElectric4D (crossWaveMetricDerivs4D B) 3 3 = 0 := by
    have hW := (crossWave_vacuum_pure_weyl B).2.2.2 0 3 0 3
    unfold weylElectric4D
    rw [hW]
    simp [R_metric, crossWaveMetricDerivs4D, crossPolarizationTensor4D, nullWaveVec4D]
  unfold gravitonPolarizationJet4D
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [weylElectric4D_add, hp.1, hc.2.2.1, add_zero]
  · rw [weylElectric4D_add, hp.2.1, hc.2.2.2.1, add_zero]
  · rw [weylElectric4D_add, hp.2.2.1, hc.1, zero_add]
  · rw [weylElectric4D_add, hp21, hc.2.1, zero_add]
  · rw [weylElectric4D_add, hp.2.2.2.1, hc33, add_zero]

/-- Exact gravito-magnetic Weyl components of `gravitonPolarizationJet4D A B`:
`B_{131} = -A`, `B_{232} = A`, `B_{132} = -B`, `B_{231} = -B`. -/
theorem gravitonPolarizationJet4D_weylMagnetic_components (A B : ℝ) :
    weylMagnetic4D (gravitonPolarizationJet4D A B) 1 3 1 = -A ∧
    weylMagnetic4D (gravitonPolarizationJet4D A B) 2 3 2 = A ∧
    weylMagnetic4D (gravitonPolarizationJet4D A B) 1 3 2 = -B ∧
    weylMagnetic4D (gravitonPolarizationJet4D A B) 2 3 1 = -B := by
  have hp := plusWave_electric_and_magnetic_components A
  have hc := crossWave_electric_and_magnetic_components B
  have hc232 : weylMagnetic4D (crossWaveMetricDerivs4D B) 2 3 2 = 0 := by
    have hW := (crossWave_vacuum_pure_weyl B).2.2.2 0 2 3 2
    unfold weylMagnetic4D
    rw [hW]
    simp [R_metric, crossWaveMetricDerivs4D, crossPolarizationTensor4D, nullWaveVec4D]
  have hp231 : weylMagnetic4D (plusWaveMetricDerivs4D A) 2 3 1 = 0 := by
    have hW := (plusWave_vacuum_pure_weyl A).2.2.2 0 2 3 1
    unfold weylMagnetic4D
    rw [hW]
    simp [R_metric, plusWaveMetricDerivs4D, plusPolarizationTensor4D, nullWaveVec4D]
  unfold gravitonPolarizationJet4D
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [weylMagnetic4D_add, hp.2.2.2.2.1, hc.2.2.2.2.2.2, add_zero]
  · rw [weylMagnetic4D_add, hp.2.2.2.2.2.1, hc232, add_zero]
  · rw [weylMagnetic4D_add, hp.2.2.2.2.2.2, hc.2.2.2.2.1, zero_add]
  · rw [weylMagnetic4D_add, hp231, hc.2.2.2.2.2.1, zero_add]

/-- Spatial trace-freeness of the gravito-electric tensor of `gravitonPolarizationJet4D A B`:
`E_{11} + E_{22} + E_{33} = A + (-A) + 0 = 0`. -/
theorem gravitonPolarizationJet4D_transverse_electric_trace_zero (A B : ℝ) :
    weylElectric4D (gravitonPolarizationJet4D A B) 1 1 +
      weylElectric4D (gravitonPolarizationJet4D A B) 2 2 +
      weylElectric4D (gravitonPolarizationJet4D A B) 3 3 = 0 := by
  have hE := gravitonPolarizationJet4D_weylElectric_components A B
  rw [hE.1, hE.2.1, hE.2.2.2.2]
  ring

/-- **Quadratic Gravito-Electric Polarization Invariant**:
`E_{11}^2 + E_{22}^2 + 2 E_{12}^2 = 2 (A^2 + B^2)`. -/
theorem gravitonPolarizationJet4D_quadratic_electric_invariant (A B : ℝ) :
    weylElectric4D (gravitonPolarizationJet4D A B) 1 1 ^ 2 +
      weylElectric4D (gravitonPolarizationJet4D A B) 2 2 ^ 2 +
      2 * weylElectric4D (gravitonPolarizationJet4D A B) 1 2 ^ 2 =
      2 * (A ^ 2 + B ^ 2) := by
  have hE := gravitonPolarizationJet4D_weylElectric_components A B
  rw [hE.1, hE.2.1, hE.2.2.1]
  ring

/-- **Quadratic Gravito-Magnetic Polarization Invariant**:
`B_{131}^2 + B_{232}^2 + 2 B_{132}^2 = 2 (A^2 + B^2)`. -/
theorem gravitonPolarizationJet4D_quadratic_magnetic_invariant (A B : ℝ) :
    weylMagnetic4D (gravitonPolarizationJet4D A B) 1 3 1 ^ 2 +
      weylMagnetic4D (gravitonPolarizationJet4D A B) 2 3 2 ^ 2 +
      2 * weylMagnetic4D (gravitonPolarizationJet4D A B) 1 3 2 ^ 2 =
      2 * (A ^ 2 + B ^ 2) := by
  have hB := gravitonPolarizationJet4D_weylMagnetic_components A B
  rw [hB.1, hB.2.1, hB.2.2.1]
  ring

/-- **Gravito-Electric / Gravito-Magnetic Energy Equipartition for 4D Graviton Waves**:
the transverse quadratic gravito-electric norm equals the transverse quadratic
gravito-magnetic norm (`= 2 * (A^2 + B^2)`). -/
theorem gravitonPolarizationJet4D_electric_eq_magnetic_energy (A B : ℝ) :
    weylElectric4D (gravitonPolarizationJet4D A B) 1 1 ^ 2 +
      weylElectric4D (gravitonPolarizationJet4D A B) 2 2 ^ 2 +
      2 * weylElectric4D (gravitonPolarizationJet4D A B) 1 2 ^ 2 =
    weylMagnetic4D (gravitonPolarizationJet4D A B) 1 3 1 ^ 2 +
      weylMagnetic4D (gravitonPolarizationJet4D A B) 2 3 2 ^ 2 +
      2 * weylMagnetic4D (gravitonPolarizationJet4D A B) 1 3 2 ^ 2 := by
  rw [gravitonPolarizationJet4D_quadratic_electric_invariant,
    gravitonPolarizationJet4D_quadratic_magnetic_invariant]

/-- **Injectivity of the 2-Polarization Graviton Map on `weylElectric4D`**:
two 4D graviton polarization jets have the same gravito-electric Weyl tensor
if and only if their `+` and `×` amplitudes agree (`A₁ = A₂ ∧ B₁ = B₂`). -/
theorem gravitonPolarizationJet4D_injective (A₁ B₁ A₂ B₂ : ℝ) :
    weylElectric4D (gravitonPolarizationJet4D A₁ B₁) =
      weylElectric4D (gravitonPolarizationJet4D A₂ B₂) ↔
      (A₁ = A₂ ∧ B₁ = B₂) := by
  refine ⟨fun h => ?_, fun ⟨hA, hB⟩ => by rw [hA, hB]⟩
  have h1 := gravitonPolarizationJet4D_weylElectric_components A₁ B₁
  have h2 := gravitonPolarizationJet4D_weylElectric_components A₂ B₂
  have hA : A₁ = A₂ := by
    rw [← h1.1, ← h2.1]
    exact congr_fun (congr_fun h 1) 1
  have hB : B₁ = B₂ := by
    rw [← h1.2.2.1, ← h2.2.2.1]
    exact congr_fun (congr_fun h 1) 2
  exact ⟨hA, hB⟩

/-- Two 4D graviton polarization jets produce the same 4D Riemann tensor if and
only if `A₁ = A₂ ∧ B₁ = B₂`. -/
theorem gravitonPolarizationJet4D_riemann_eq_iff (A₁ B₁ A₂ B₂ : ℝ) :
    R_metric (gravitonPolarizationJet4D A₁ B₁) =
      R_metric (gravitonPolarizationJet4D A₂ B₂) ↔
      (A₁ = A₂ ∧ B₁ = B₂) := by
  refine ⟨fun hR => ?_, fun ⟨hA, hB⟩ => by rw [hA, hB]⟩
  have hE := (riemann_eq_iff_einstein_electric_magnetic_eq
    (gravitonPolarizationJet4D A₁ B₁)
    (gravitonPolarizationJet4D A₂ B₂)).mp hR
  exact (gravitonPolarizationJet4D_injective A₁ B₁ A₂ B₂).mp hE.2.1

/-- Readout and injectivity for the `Fin (gravitonTTModes 4) → ℝ` vector parameterization
`gravitonPolarizationVecJet4D`. -/
theorem gravitonPolarizationVecJet4D_readout_and_injective
    (p₁ p₂ : Fin (gravitonTTModes 4) → ℝ) :
    weylElectric4D (gravitonPolarizationVecJet4D p₁) 1 1 = p₁ ⟨0, by decide⟩ ∧
    weylElectric4D (gravitonPolarizationVecJet4D p₁) 1 2 = p₁ ⟨1, by decide⟩ ∧
    (R_metric (gravitonPolarizationVecJet4D p₁) =
      R_metric (gravitonPolarizationVecJet4D p₂) ↔
      (p₁ ⟨0, by decide⟩ = p₂ ⟨0, by decide⟩ ∧
        p₁ ⟨1, by decide⟩ = p₂ ⟨1, by decide⟩)) := by
  have hE := gravitonPolarizationJet4D_weylElectric_components
    (p₁ ⟨0, by decide⟩) (p₁ ⟨1, by decide⟩)
  exact ⟨hE.1, hE.2.2.1,
    gravitonPolarizationJet4D_riemann_eq_iff
      (p₁ ⟨0, by decide⟩) (p₁ ⟨1, by decide⟩)
      (p₂ ⟨0, by decide⟩) (p₂ ⟨1, by decide⟩)⟩

/-! ### 4. Superposition of 4D Graviton Waves onto Curved Cosmological / Yang-Mills Backgrounds -/

/-- **Curved-Background Invariance of Ricci, Scalar, Einstein, and Lovelock-Sorkin
Tensors under Graviton-Wave Superposition**: adding `gravitonPolarizationJet4D A B`
to ANY 4D metric perturbation `md : MetricDerivs 4` leaves `ricci`, `scalar`,
`einstein`, `einsteinLovelock4D`, and `einsteinSorkin4D` strictly invariant. -/
theorem superposeGravitonWave_ricci_scalar_einstein_invariant
    (md : MetricDerivs 4) (A B a Λ ρ V : ℝ) :
    let md' := addMetricDerivs md (gravitonPolarizationJet4D A B)
    (∀ b d : Fin 4, ricci md' sign b d = ricci md sign b d) ∧
    scalar md' sign = scalar md sign ∧
    (∀ b d : Fin 4, einstein md' sign b d = einstein md sign b d) ∧
    (∀ b d : Fin 4,
      einsteinLovelock4D md' a Λ b d = einsteinLovelock4D md a Λ b d) ∧
    (∀ b d : Fin 4,
      einsteinSorkin4D md' ρ V b d = einsteinSorkin4D md ρ V b d) := by
  intro md'
  have hric : ∀ b d : Fin 4, ricci md' sign b d = ricci md sign b d := by
    intro b d; unfold md'
    rw [ricci_add, gravitonPolarizationJet4D_ricci_zero, add_zero]
  have hscal : scalar md' sign = scalar md sign := by
    unfold md'
    rw [scalar_add, gravitonPolarizationJet4D_scalar_zero, add_zero]
  have hein : ∀ b d : Fin 4, einstein md' sign b d = einstein md sign b d := by
    intro b d; unfold md'
    rw [einstein_add, gravitonPolarizationJet4D_einstein_zero, add_zero]
  have hlov : ∀ b d : Fin 4,
      einsteinLovelock4D md' a Λ b d = einsteinLovelock4D md a Λ b d := by
    intro b d; unfold einsteinLovelock4D
    rw [hein b d]
  have hsork : ∀ b d : Fin 4,
      einsteinSorkin4D md' ρ V b d = einsteinSorkin4D md ρ V b d := by
    intro b d; unfold einsteinSorkin4D einsteinLovelock4D
    rw [hein b d]
  exact ⟨hric, hscal, hein, hlov, hsork⟩

/-- **Weyl Polarization Shift under Graviton-Wave Superposition**: adding
`gravitonPolarizationJet4D A B` to any 4D background `md` shifts its Weyl
electric and magnetic polarization channels by `(A, B)`. -/
theorem superposeGravitonWave_weyl_shift (md : MetricDerivs 4) (A B : ℝ) :
    let md' := addMetricDerivs md (gravitonPolarizationJet4D A B)
    weylElectric4D md' 1 1 = weylElectric4D md 1 1 + A ∧
    weylElectric4D md' 2 2 = weylElectric4D md 2 2 - A ∧
    weylElectric4D md' 1 2 = weylElectric4D md 1 2 + B ∧
    weylMagnetic4D md' 1 3 1 = weylMagnetic4D md 1 3 1 - A ∧
    weylMagnetic4D md' 1 3 2 = weylMagnetic4D md 1 3 2 - B := by
  intro md'
  have hE := gravitonPolarizationJet4D_weylElectric_components A B
  have hB := gravitonPolarizationJet4D_weylMagnetic_components A B
  unfold md'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [weylElectric4D_add, hE.1]
  · rw [weylElectric4D_add, hE.2.1]; ring
  · rw [weylElectric4D_add, hE.2.2.1]
  · rw [weylMagnetic4D_add, hB.1]; ring
  · rw [weylMagnetic4D_add, hB.2.2.1]; ring

/-- **On-Shell Gauge-Gravity Superposition Principle**: for any 4D metric perturbation
`md : MetricDerivs 4`, `addMetricDerivs md (gravitonPolarizationJet4D A B)`
satisfies the cosmological 4D Einstein-Lovelock-Yang-Mills equation (and the
Einstein-Sorkin-Yang-Mills equation) if and only if `md` does. -/
theorem superposeGravitonWave_preserves_einsteinLovelockYangMills4D
    (md : MetricDerivs 4) (A B Λ ρ V κ : ℝ)
    (sc : StructureConstants g_dim) (conn : ConnectionData 4 g_dim) :
    (SatisfiesEinsteinLovelockYangMills4D
        (addMetricDerivs md (gravitonPolarizationJet4D A B)) Λ κ sc conn ↔
      SatisfiesEinsteinLovelockYangMills4D md Λ κ sc conn) ∧
    (SatisfiesEinsteinSorkinYangMills4D
        (addMetricDerivs md (gravitonPolarizationJet4D A B)) ρ V κ sc conn ↔
      SatisfiesEinsteinSorkinYangMills4D md ρ V κ sc conn) := by
  have hL : ∀ Λ' : ℝ,
      SatisfiesEinsteinLovelockYangMills4D
        (addMetricDerivs md (gravitonPolarizationJet4D A B)) Λ' κ sc conn ↔
      SatisfiesEinsteinLovelockYangMills4D md Λ' κ sc conn := by
    intro Λ'
    have hinv := (superposeGravitonWave_ricci_scalar_einstein_invariant
      md A B 1 Λ' ρ V).2.2.2.1
    unfold SatisfiesEinsteinLovelockYangMills4D
    simp_rw [hinv]
  exact ⟨hL Λ, hL _⟩

/-- **Master 4D Graviton TT Modes & Weyl Polarization Bridge Theorem**:
Unites the spacetime dimension formula `gravitonTTModes d = d(d-3)/2` (`0` in 3D,
`2` in 4D, `5` in 5D, `44` in 11D), the 20-component 4D Riemann accounting
`10 + 5 * 2 = 20`, the exact vacuum pure-Weyl realization `gravitonPolarizationJet4D A B`,
electric-magnetic energy equipartition `2 (A^2 + B^2)`, amplitude injectivity, and
on-shell superposition invariance of `SatisfiesEinsteinSorkinYangMills4D`. -/
theorem graviton_tt_modes_weyl_polarization_4D_master_bridge
    (md : MetricDerivs 4) (A B ρ V κ : ℝ)
    (sc : StructureConstants g_dim) (conn : ConnectionData 4 g_dim) :
    -- (1) Graviton TT mode counts across spacetime dimensions
    ((∀ d : ℕ, 3 ≤ d → gravitonTTModes d = d * (d - 3) / 2) ∧
      gravitonTTModes 3 = 0 ∧
      gravitonTTModes 4 = 2 ∧
      gravitonTTModes 5 = 5 ∧
      gravitonTTModes 11 = 44 ∧
      gravitonTotalComponents 4 + 5 * gravitonTTModes 4 = 20) ∧
    -- (2) Exact vacuum pure-Weyl properties of gravitonPolarizationJet4D A B
    ((∀ b d : Fin 4,
        ricci (gravitonPolarizationJet4D A B) sign b d = 0 ∧
        einstein (gravitonPolarizationJet4D A B) sign b d = 0) ∧
      scalar (gravitonPolarizationJet4D A B) sign = 0 ∧
      (∀ a b c d : Fin 4,
        R_metric (gravitonPolarizationJet4D A B) a b c d =
          weylTensor4D (gravitonPolarizationJet4D A B) a b c d)) ∧
    -- (3) Weyl polarization readout & electric-magnetic energy equipartition
    (weylElectric4D (gravitonPolarizationJet4D A B) 1 1 = A ∧
      weylElectric4D (gravitonPolarizationJet4D A B) 1 2 = B ∧
      weylElectric4D (gravitonPolarizationJet4D A B) 1 1 ^ 2 +
        weylElectric4D (gravitonPolarizationJet4D A B) 2 2 ^ 2 +
        2 * weylElectric4D (gravitonPolarizationJet4D A B) 1 2 ^ 2 =
        2 * (A ^ 2 + B ^ 2) ∧
      weylMagnetic4D (gravitonPolarizationJet4D A B) 1 3 1 ^ 2 +
        weylMagnetic4D (gravitonPolarizationJet4D A B) 2 3 2 ^ 2 +
        2 * weylMagnetic4D (gravitonPolarizationJet4D A B) 1 3 2 ^ 2 =
        2 * (A ^ 2 + B ^ 2)) ∧
    -- (4) Superposition invariance of 4D Einstein-Sorkin-Yang-Mills equations
    (SatisfiesEinsteinSorkinYangMills4D
        (addMetricDerivs md (gravitonPolarizationJet4D A B)) ρ V κ sc conn ↔
      SatisfiesEinsteinSorkinYangMills4D md ρ V κ sc conn) := by
  have hE := gravitonPolarizationJet4D_weylElectric_components A B
  refine ⟨⟨gravitonTTModes_eq, gravitonTTModes_d3, gravitonTTModes_d4,
      gravitonTTModes_d5, gravitonTTModes_d11,
      riemann4D_twenty_component_graviton_accounting.2.2⟩,
    ⟨fun b d => ⟨gravitonPolarizationJet4D_ricci_zero A B b d,
        gravitonPolarizationJet4D_einstein_zero A B b d⟩,
      gravitonPolarizationJet4D_scalar_zero A B,
      fun a b c d => gravitonPolarizationJet4D_pure_weyl A B a b c d⟩,
    ⟨hE.1, hE.2.2.1,
      gravitonPolarizationJet4D_quadratic_electric_invariant A B,
      gravitonPolarizationJet4D_quadratic_magnetic_invariant A B⟩,
    (superposeGravitonWave_preserves_einsteinLovelockYangMills4D md A B 0 ρ V κ sc conn).2⟩

#print axioms gravitonTTModes_closed_form
#print axioms gravitonTTModes_dim3_eq_zero
#print axioms gravitonTTModes_dim4_eq_two
#print axioms gravitonTTModes_dim5_eq_five
#print axioms gravitonTTModes_dim10_eq_thirtyfive
#print axioms gravitonTTModes_dim11_eq_fortyfour
#print axioms gravitonTTModes_dim26_eq_299
#print axioms graviton4D_component_budget
#print axioms graviton4D_tt_gauge_breakdown
#print axioms gravitonTTModes_spatial_agreement
#print axioms riemann4D_twenty_component_graviton_accounting
#print axioms gravitonPolarizationJet4D_zero
#print axioms gravitonPolarizationJet4D_traceless
#print axioms gravitonPolarizationJet4D_ricci_zero
#print axioms gravitonPolarizationJet4D_scalar_zero
#print axioms gravitonPolarizationJet4D_einstein_zero
#print axioms gravitonPolarizationJet4D_ricciScalarPart_zero
#print axioms gravitonPolarizationJet4D_pure_weyl
#print axioms gravitonPolarizationJet4D_differential_curvature_zero
#print axioms gravitonPolarizationJet4D_weylElectric_components
#print axioms gravitonPolarizationJet4D_weylMagnetic_components
#print axioms gravitonPolarizationJet4D_transverse_electric_trace_zero
#print axioms gravitonPolarizationJet4D_quadratic_electric_invariant
#print axioms gravitonPolarizationJet4D_quadratic_magnetic_invariant
#print axioms gravitonPolarizationJet4D_electric_eq_magnetic_energy
#print axioms gravitonPolarizationJet4D_injective
#print axioms gravitonPolarizationJet4D_riemann_eq_iff
#print axioms gravitonPolarizationVecJet4D_readout_and_injective
#print axioms superposeGravitonWave_ricci_scalar_einstein_invariant
#print axioms superposeGravitonWave_weyl_shift
#print axioms superposeGravitonWave_preserves_einsteinLovelockYangMills4D
#print axioms graviton_tt_modes_weyl_polarization_4D_master_bridge

end
end UnifiedTheory.Audit.KFCausalCurved4DGravitonTTModesWeylPolarizationBridge
