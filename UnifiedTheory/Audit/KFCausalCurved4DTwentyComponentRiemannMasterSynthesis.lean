import UnifiedTheory.Audit.KFCausalCurved4DTidalWeylProbeExtraction
import UnifiedTheory.Audit.KFCausalConformal4DCurvedDiamondMasterSynthesis

/-! Master synthesis of the 20-component 4D Lorentzian Riemann curvature
reconstruction: proves that the full 4D linearized Riemann tensor `R_metric md`
is uniquely and explicitly reconstructed from `(einstein md sign, weylElectric4D md, weylMagnetic4D md)`
(10 Einstein components + 5 gravito-electric Weyl components + 5 gravito-magnetic
Weyl components = 20 independent curvature components), and proves the orthogonal
channel separation and joint causal-diamond + tidal-probe reconstruction for
superpositions of 10-component conformal curvature `H` with `+` and `×`
gravitational-wave modes `(A, B)`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCurved4DTwentyComponentRiemannMasterSynthesis
noncomputable section

open Set MeasureTheory Filter Topology
open scoped Real BigOperators
open UnifiedTheory.LayerA.MetricConstruction (MetricDerivs R_metric riemannFromMetric)
open KFCausalConformal4DDiamondBenchmark (sign eta)
open KFCausalLorentzianContractedBianchi (ricci scalar einstein dEinstein
  lorentzian_metric_divergence)
open KFCausalConformal4DCoupledWaveVariationSynthesis (temporalVariationDerivative
  joint_operator_and_derivative_tendsto)
open KFCausalConformal4DLorentzianBianchiTraceSynthesis (temporalEinsteinTrace
  bdg_temporal_variation_tendsto_half_einsteinTrace_deriv)
open KFCausalConformal4DOffDiagonalShearCurvatureSynthesis (Hessian4D ThirdJet4D
  IsSymmetricHessian4D IsSymmetricThirdJet4D minkMetric4D box4D
  fullConformalMetricDerivs fullRicciTensor4D fullScalarCurvature4D
  fullEinsteinTensor4D fullEinsteinTrace4D)
open KFCausalConformal4DCurvedDiamondMasterSynthesis (reconstructHessianFromEinstein4D
  reconstructHessianFromRicciAndScalar4D reconstructHessianFromProbes4D
  lorentzianStressEnergyDivergence4D reconstructHessianFromEinstein4D_exact
  reconstructHessianFromProbes4D_exact)
open KFCausalCurved4DLinearizedMetricDecomposition (zeroMetricDerivs addMetricDerivs
  smulMetricDerivs subMetricDerivs
  R_metric_zero R_metric_add ricci_zero ricci_add scalar_zero scalar_add
  einstein_zero einstein_add
  lorentzianMetricTrace4D metricTraceHessian4D metricTraceThirdJet4D
  metricTraceHessian4D_symmetric conformalPartMetricDerivs4D tracelessPartMetricDerivs4D
  metricTrace_of_fullConformalMetricDerivs)
open KFCausalCurved4DLinearizedWeylRicciSplit (ricciCurvaturePart4D
  scalarCurvaturePart4D ricciScalarRiemannPart4D weylTensor4D
  weylTensor4D_zero weylTensor4D_add
  weylTensor4D_fullConformal_eq_zero weylTensor4D_eq_tracelessPart)
open KFCausalCurved4DGeneralProbeCurvatureExtraction (einsteinRiemannPart4D
  riemann_eq_weyl_add_einsteinRiemannPart4D
  vacuum_einstein_iff_riemann_eq_weyl
  general_onShell_stressEnergy_conservation)
open KFCausalCurved4DWeylElectricMagneticDecomposition (weylElectric4D weylMagnetic4D
  weylElectric4D_zero weylElectric4D_add weylMagnetic4D_zero weylMagnetic4D_add
  weylElectric4D_fullConformal_eq_zero weylMagnetic4D_fullConformal_eq_zero
  weylElectric4D_spatial_trace_zero weylMagnetic4D_spatial_trace_zero
  weylMagnetic4D_cyclic_bianchi
  reconstructWeylFromElectricMagnetic4D reconstructWeylFromElectricMagnetic4D_exact
  weylTensor4D_eq_iff_electric_and_magnetic_eq
  weylTensor4D_eq_zero_iff_electric_and_magnetic_zero)
open KFCausalCurved4DTidalWeylProbeExtraction (riemannTidalProbe weylTidalProbe
  ricciTidalProbe basisVec4D
  weylTidalProbe_add weylTidalProbe_fullConformal_eq_zero
  weylTidalProbe_extract_electric weylTidalProbe_extract_magnetic
  plusWaveMetricDerivs4D crossWaveMetricDerivs4D
  plusWave_traceless crossWave_traceless
  plusWave_ricci_eq_zero crossWave_ricci_eq_zero
  plusWave_vacuum_pure_weyl crossWave_vacuum_pure_weyl
  plusWave_electric_and_magnetic_components crossWave_electric_and_magnetic_components
  gravitationalWave_tidalProbe_polarization_extraction)

/-! ### Complete 20-Component Reconstruction of the 4D Riemann Tensor -/

/-- Explicit reconstruction of all 256 components of the 4D Riemann tensor
from the 10-component Einstein tensor `G`, the 5-component symmetric traceless
gravito-electric Weyl tensor `E`, and the 5-component gravito-magnetic Weyl
tensor `B`. -/
def reconstructRiemannFromEinsteinAndWeyl4D
    (G : Fin 4 → Fin 4 → ℝ)
    (E : Fin 4 → Fin 4 → ℝ)
    (B : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (a b c d : Fin 4) : ℝ :=
  reconstructWeylFromElectricMagnetic4D E B a b c d +
    einsteinRiemannPart4D G a b c d

/-- **Exact 20-Component 4D Riemann Reconstruction Theorem**: for every linearized
4D metric perturbation `md : MetricDerivs 4` and all `a b c d : Fin 4`,
`reconstructRiemannFromEinsteinAndWeyl4D (einstein md sign) (weylElectric4D md) (weylMagnetic4D md) a b c d = R_metric md a b c d`. -/
theorem reconstructRiemannFromEinsteinAndWeyl4D_exact
    (md : MetricDerivs 4) (a b c d : Fin 4) :
    reconstructRiemannFromEinsteinAndWeyl4D
      (einstein md sign) (weylElectric4D md) (weylMagnetic4D md) a b c d =
      R_metric md a b c d := by
  unfold reconstructRiemannFromEinsteinAndWeyl4D
  rw [reconstructWeylFromElectricMagnetic4D_exact md a b c d,
    ← (riemann_eq_weyl_add_einsteinRiemannPart4D md a b c d).1]

/-- **20-Component Uniqueness Theorem for 4D Riemann Curvature**: two 4D metric
perturbations `md₁ md₂ : MetricDerivs 4` have the same Riemann tensor if and only
if they have the same Einstein tensor `G`, the same gravito-electric Weyl tensor `E`,
and the same gravito-magnetic Weyl tensor `B`. -/
theorem riemann_eq_iff_einstein_electric_magnetic_eq (md₁ md₂ : MetricDerivs 4) :
    R_metric md₁ = R_metric md₂ ↔
      (einstein md₁ sign = einstein md₂ sign ∧
        weylElectric4D md₁ = weylElectric4D md₂ ∧
        weylMagnetic4D md₁ = weylMagnetic4D md₂) := by
  refine ⟨fun hR => ?_, fun ⟨hG, hE, hB⟩ => ?_⟩
  · have hric : ricci md₁ sign = ricci md₂ sign := by
      funext b d
      unfold ricci
      rw [hR]
    have hscal : scalar md₁ sign = scalar md₂ sign := by
      unfold scalar
      rw [hric]
    have hG : einstein md₁ sign = einstein md₂ sign := by
      funext b d
      unfold einstein
      rw [hric, hscal]
    have hRS : ricciScalarRiemannPart4D md₁ = ricciScalarRiemannPart4D md₂ := by
      funext a b c d
      unfold ricciScalarRiemannPart4D ricciCurvaturePart4D scalarCurvaturePart4D
      rw [hric, hscal]
    have hW : weylTensor4D md₁ = weylTensor4D md₂ := by
      funext a b c d
      unfold weylTensor4D
      rw [hR, hRS]
    have hEB := (weylTensor4D_eq_iff_electric_and_magnetic_eq md₁ md₂).mp hW
    exact ⟨hG, hEB.1, hEB.2⟩
  · funext a b c d
    rw [← reconstructRiemannFromEinsteinAndWeyl4D_exact md₁ a b c d,
      ← reconstructRiemannFromEinsteinAndWeyl4D_exact md₂ a b c d,
      hG, hE, hB]

/-- **20-Component Flatness Characterization**: a 4D metric perturbation
`md : MetricDerivs 4` is Riemann-flat (`R_metric md = 0`) if and only if its
Einstein tensor `einstein md sign`, its gravito-electric Weyl tensor
`weylElectric4D md`, and its gravito-magnetic Weyl tensor `weylMagnetic4D md`
all vanish identically. -/
theorem riemann_eq_zero_iff_einstein_electric_magnetic_zero (md : MetricDerivs 4) :
    (∀ a b c d : Fin 4, R_metric md a b c d = 0) ↔
      ((∀ b d : Fin 4, einstein md sign b d = 0) ∧
        (∀ a b : Fin 4, weylElectric4D md a b = 0) ∧
        (∀ a b c : Fin 4, weylMagnetic4D md a b c = 0)) := by
  refine ⟨fun hR => ?_, fun ⟨hG, hE, hB⟩ a b c d => ?_⟩
  · have hR_fn : R_metric md = R_metric (zeroMetricDerivs 4) := by
      funext a b c d; rw [hR a b c d, R_metric_zero]
    have h := (riemann_eq_iff_einstein_electric_magnetic_eq md (zeroMetricDerivs 4)).mp hR_fn
    refine ⟨fun b d => ?_, fun a b => ?_, fun a b c => ?_⟩
    · exact congr_fun (congr_fun h.1 b) d |>.trans (einstein_zero sign b d)
    · exact congr_fun (congr_fun h.2.1 a) b |>.trans (weylElectric4D_zero a b)
    · exact congr_fun (congr_fun (congr_fun h.2.2 a) b) c |>.trans (weylMagnetic4D_zero a b c)
  · have hG_fn : einstein md sign = einstein (zeroMetricDerivs 4) sign := by
      funext i j; rw [hG i j, einstein_zero]
    have hE_fn : weylElectric4D md = weylElectric4D (zeroMetricDerivs 4) := by
      funext i j; rw [hE i j, weylElectric4D_zero]
    have hB_fn : weylMagnetic4D md = weylMagnetic4D (zeroMetricDerivs 4) := by
      funext i j k; rw [hB i j k, weylMagnetic4D_zero]
    have hR := (riemann_eq_iff_einstein_electric_magnetic_eq md (zeroMetricDerivs 4)).mpr
      ⟨hG_fn, hE_fn, hB_fn⟩
    exact congr_fun (congr_fun (congr_fun (congr_fun hR a) b) c) d |>.trans
      (R_metric_zero a b c d)

/-! ### Orthogonal Channel Separation for Conformal + Gravitational-Wave Superpositions -/

/-- Combined 4D metric perturbation jet superimposing a 10-component conformal
perturbation `fullConformalMetricDerivs H K` with `+` and `×` transverse-traceless
gravitational-wave modes of amplitudes `A` and `B`. -/
def conformalPlusGravitationalWaveMetricDerivs4D
    (H : Hessian4D) (K : ThirdJet4D) (A B : ℝ) : MetricDerivs 4 :=
  addMetricDerivs (fullConformalMetricDerivs H K)
    (addMetricDerivs (plusWaveMetricDerivs4D A) (crossWaveMetricDerivs4D B))

/-- The Lorentzian metric-trace Hessian of `conformalPlusGravitationalWaveMetricDerivs4D H K A B`
depends solely on the conformal Hessian `H`, because the gravitational-wave modes
are strictly traceless. -/
theorem conformalPlusGravitationalWave_metricTraceHessian
    (H : Hessian4D) (hH : IsSymmetricHessian4D H)
    (K : ThirdJet4D) (hK : IsSymmetricThirdJet4D K) (A B : ℝ) (e f : Fin 4) :
    metricTraceHessian4D
      (conformalPlusGravitationalWaveMetricDerivs4D H K A B) e f = H e f := by
  have htr_add : lorentzianMetricTrace4D
      (conformalPlusGravitationalWaveMetricDerivs4D H K A B) e f =
      lorentzianMetricTrace4D (fullConformalMetricDerivs H K) e f +
        lorentzianMetricTrace4D (plusWaveMetricDerivs4D A) e f +
        lorentzianMetricTrace4D (crossWaveMetricDerivs4D B) e f := by
    unfold lorentzianMetricTrace4D conformalPlusGravitationalWaveMetricDerivs4D addMetricDerivs
    dsimp
    simp_rw [mul_add, Finset.sum_add_distrib, ← add_assoc]
  have h0 : metricTraceHessian4D
      (conformalPlusGravitationalWaveMetricDerivs4D H K A B) e f =
      metricTraceHessian4D (fullConformalMetricDerivs H K) e f := by
    unfold metricTraceHessian4D
    rw [htr_add, (plusWave_traceless A e f 0 0).1, (crossWave_traceless B e f 0 0).1]
    ring
  rw [h0, (metricTrace_of_fullConformalMetricDerivs H hH K hK).1 e f]

/-- The Ricci tensor, scalar curvature, and Einstein tensor of
`conformalPlusGravitationalWaveMetricDerivs4D H K A B` depend ONLY on `H`:
the gravitational-wave modes `(A, B)` are exact vacuum solutions and contribute
zero to the Ricci, scalar, and Einstein curvature channels. -/
theorem conformalPlusGravitationalWave_ricci_scalar_einstein
    (H : Hessian4D) (K : ThirdJet4D) (A B : ℝ) :
    (∀ b d : Fin 4,
      ricci (conformalPlusGravitationalWaveMetricDerivs4D H K A B) sign b d =
        fullRicciTensor4D H b d) ∧
    scalar (conformalPlusGravitationalWaveMetricDerivs4D H K A B) sign =
      fullScalarCurvature4D H ∧
    (∀ b d : Fin 4,
      einstein (conformalPlusGravitationalWaveMetricDerivs4D H K A B) sign b d =
        fullEinsteinTensor4D H b d) := by
  refine ⟨fun b d => ?_, ?_, fun b d => ?_⟩
  · unfold conformalPlusGravitationalWaveMetricDerivs4D
    rw [ricci_add, ricci_add, plusWave_ricci_eq_zero, crossWave_ricci_eq_zero]
    change fullRicciTensor4D H b d + (0 + 0) = fullRicciTensor4D H b d
    ring
  · unfold conformalPlusGravitationalWaveMetricDerivs4D
    rw [scalar_add, scalar_add, (plusWave_vacuum_pure_weyl A).1,
      (crossWave_vacuum_pure_weyl B).1]
    change fullScalarCurvature4D H + (0 + 0) = fullScalarCurvature4D H
    ring
  · unfold conformalPlusGravitationalWaveMetricDerivs4D
    rw [einstein_add, einstein_add, (plusWave_vacuum_pure_weyl A).2.1 b d,
      (crossWave_vacuum_pure_weyl B).2.1 b d]
    change fullEinsteinTensor4D H b d + (0 + 0) = fullEinsteinTensor4D H b d
    ring

/-- The Weyl tensor, gravito-electric tensor, gravito-magnetic tensor, and Weyl
tidal probes of `conformalPlusGravitationalWaveMetricDerivs4D H K A B` depend
ONLY on the gravitational-wave modes `(A, B)`: the conformal sector `(H, K)`
contributes identically zero to all Weyl channels. -/
theorem conformalPlusGravitationalWave_weyl_channels
    (H : Hessian4D) (hH : IsSymmetricHessian4D H)
    (K : ThirdJet4D) (A B : ℝ) :
    (∀ a b c d : Fin 4,
      weylTensor4D (conformalPlusGravitationalWaveMetricDerivs4D H K A B) a b c d =
        weylTensor4D
          (addMetricDerivs (plusWaveMetricDerivs4D A) (crossWaveMetricDerivs4D B)) a b c d) ∧
    weylElectric4D (conformalPlusGravitationalWaveMetricDerivs4D H K A B) 1 1 = A ∧
    weylElectric4D (conformalPlusGravitationalWaveMetricDerivs4D H K A B) 2 2 = -A ∧
    weylElectric4D (conformalPlusGravitationalWaveMetricDerivs4D H K A B) 1 2 = B ∧
    weylMagnetic4D (conformalPlusGravitationalWaveMetricDerivs4D H K A B) 1 3 1 = -A ∧
    weylMagnetic4D (conformalPlusGravitationalWaveMetricDerivs4D H K A B) 1 3 2 = -B := by
  have hW : ∀ a b c d : Fin 4,
      weylTensor4D (conformalPlusGravitationalWaveMetricDerivs4D H K A B) a b c d =
        weylTensor4D
          (addMetricDerivs (plusWaveMetricDerivs4D A) (crossWaveMetricDerivs4D B)) a b c d := by
    intro a b c d
    unfold conformalPlusGravitationalWaveMetricDerivs4D
    rw [weylTensor4D_add, weylTensor4D_fullConformal_eq_zero H hH K a b c d, zero_add]
  have hplus := plusWave_electric_and_magnetic_components A
  have hcross := crossWave_electric_and_magnetic_components B
  refine ⟨hW, ?_, ?_, ?_, ?_, ?_⟩
  · unfold weylElectric4D
    rw [hW 0 1 0 1]
    change weylElectric4D (addMetricDerivs (plusWaveMetricDerivs4D A) (crossWaveMetricDerivs4D B)) 1 1 = A
    rw [weylElectric4D_add, hplus.1, hcross.2.2.1]; ring
  · unfold weylElectric4D
    rw [hW 0 2 0 2]
    change weylElectric4D (addMetricDerivs (plusWaveMetricDerivs4D A) (crossWaveMetricDerivs4D B)) 2 2 = -A
    rw [weylElectric4D_add, hplus.2.1, hcross.2.2.2.1]; ring
  · unfold weylElectric4D
    rw [hW 0 1 0 2]
    change weylElectric4D (addMetricDerivs (plusWaveMetricDerivs4D A) (crossWaveMetricDerivs4D B)) 1 2 = B
    rw [weylElectric4D_add, hplus.2.2.1, hcross.1]; ring
  · unfold weylMagnetic4D
    rw [hW 0 1 3 1]
    change weylMagnetic4D (addMetricDerivs (plusWaveMetricDerivs4D A) (crossWaveMetricDerivs4D B)) 1 3 1 = -A
    rw [weylMagnetic4D_add, hplus.2.2.2.2.1, hcross.2.2.2.2.2.2]; ring
  · unfold weylMagnetic4D
    rw [hW 0 1 3 2]
    change weylMagnetic4D (addMetricDerivs (plusWaveMetricDerivs4D A) (crossWaveMetricDerivs4D B)) 1 3 2 = -B
    rw [weylMagnetic4D_add, hplus.2.2.2.2.2.2, hcross.2.2.2.2.1]; ring

/-- Exact simultaneous extraction of all 10 conformal Hessian components `H μ ν`
(from the Einstein tensor and polarization probes) and both gravitational-wave
amplitudes `(A, B)` (from the Weyl tidal probes) for any combined perturbation
`md = conformalPlusGravitationalWaveMetricDerivs4D H K A B`. -/
theorem conformalPlusGravitationalWave_joint_reconstruction
    (H : Hessian4D) (hH : IsSymmetricHessian4D H)
    (K : ThirdJet4D) (A B : ℝ) :
    let md := conformalPlusGravitationalWaveMetricDerivs4D H K A B
    (∀ μ ν : Fin 4,
      reconstructHessianFromEinstein4D (einstein md sign) μ ν = H μ ν ∧
      reconstructHessianFromProbes4D (einstein md sign) μ ν = H μ ν) ∧
    weylTidalProbe (basisVec4D 0) (basisVec4D 1) (basisVec4D 0) (basisVec4D 1) md = A ∧
    weylTidalProbe (basisVec4D 0) (basisVec4D 2) (basisVec4D 0) (basisVec4D 2) md = -A ∧
    weylTidalProbe (basisVec4D 0) (basisVec4D 1) (basisVec4D 0) (basisVec4D 2) md = B ∧
    weylTidalProbe (basisVec4D 0) (basisVec4D 1) (basisVec4D 3) (basisVec4D 1) md = -A ∧
    weylTidalProbe (basisVec4D 0) (basisVec4D 1) (basisVec4D 3) (basisVec4D 2) md = -B := by
  intro md
  have hG_eq : einstein md sign = fullEinsteinTensor4D H := by
    funext b d
    exact (conformalPlusGravitationalWave_ricci_scalar_einstein H K A B).2.2 b d
  have hW := conformalPlusGravitationalWave_weyl_channels H hH K A B
  refine ⟨fun μ ν => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hG_eq]
    exact ⟨reconstructHessianFromEinstein4D_exact H hH μ ν,
      reconstructHessianFromProbes4D_exact H hH μ ν⟩
  · rw [weylTidalProbe_extract_electric]; exact hW.2.1
  · rw [weylTidalProbe_extract_electric]; exact hW.2.2.1
  · rw [weylTidalProbe_extract_electric]; exact hW.2.2.2.1
  · rw [weylTidalProbe_extract_magnetic]; exact hW.2.2.2.2.1
  · rw [weylTidalProbe_extract_magnetic]; exact hW.2.2.2.2.2

/-- **Joint Injectivity Theorem for `(H, A, B)`**: if two combined perturbations
`conformalPlusGravitationalWaveMetricDerivs4D H₁ K₁ A₁ B₁` and
`conformalPlusGravitationalWaveMetricDerivs4D H₂ K₂ A₂ B₂` (with symmetric `H₁, H₂`)
produce the same 4D Riemann tensor, then `H₁ = H₂`, `A₁ = A₂`, and `B₁ = B₂`. -/
theorem conformalPlusGravitationalWave_injective
    (H₁ H₂ : Hessian4D) (hH₁ : IsSymmetricHessian4D H₁) (hH₂ : IsSymmetricHessian4D H₂)
    (K₁ K₂ : ThirdJet4D) (A₁ B₁ A₂ B₂ : ℝ)
    (hR : R_metric (conformalPlusGravitationalWaveMetricDerivs4D H₁ K₁ A₁ B₁) =
      R_metric (conformalPlusGravitationalWaveMetricDerivs4D H₂ K₂ A₂ B₂)) :
    H₁ = H₂ ∧ A₁ = A₂ ∧ B₁ = B₂ := by
  have heq := (riemann_eq_iff_einstein_electric_magnetic_eq
    (conformalPlusGravitationalWaveMetricDerivs4D H₁ K₁ A₁ B₁)
    (conformalPlusGravitationalWaveMetricDerivs4D H₂ K₂ A₂ B₂)).mp hR
  have hrec₁ := conformalPlusGravitationalWave_joint_reconstruction H₁ hH₁ K₁ A₁ B₁
  have hrec₂ := conformalPlusGravitationalWave_joint_reconstruction H₂ hH₂ K₂ A₂ B₂
  have hH_eq : H₁ = H₂ := by
    funext μ ν
    rw [← (hrec₁.1 μ ν).1, ← (hrec₂.1 μ ν).1, heq.1]
  have hW₁ := conformalPlusGravitationalWave_weyl_channels H₁ hH₁ K₁ A₁ B₁
  have hW₂ := conformalPlusGravitationalWave_weyl_channels H₂ hH₂ K₂ A₂ B₂
  have hA_eq : A₁ = A₂ := by
    rw [← hW₁.2.1, ← hW₂.2.1, heq.2.1]
  have hB_eq : B₁ = B₂ := by
    rw [← hW₁.2.2.2.1, ← hW₂.2.2.2.1, heq.2.1]
  exact ⟨hH_eq, hA_eq, hB_eq⟩

/-- For any combined perturbation `conformalPlusGravitationalWaveMetricDerivs4D H K A B`
with symmetric `H` and `K`, its conformal projection recovers `fullConformalMetricDerivs H K`
and its traceless projection recovers the pure gravitational-wave sector
`addMetricDerivs (plusWaveMetricDerivs4D A) (crossWaveMetricDerivs4D B)`. -/
theorem conformalPlusGravitationalWave_projection_split
    (H : Hessian4D) (hH : IsSymmetricHessian4D H)
    (K : ThirdJet4D) (hK : IsSymmetricThirdJet4D K) (A B : ℝ) (e f a b : Fin 4) :
    (conformalPartMetricDerivs4D
      (conformalPlusGravitationalWaveMetricDerivs4D H K A B)).h e f a b =
      (fullConformalMetricDerivs H K).h e f a b ∧
    (tracelessPartMetricDerivs4D
      (conformalPlusGravitationalWaveMetricDerivs4D H K A B)).h e f a b =
      (addMetricDerivs (plusWaveMetricDerivs4D A) (crossWaveMetricDerivs4D B)).h e f a b := by
  have hCH : (conformalPartMetricDerivs4D
      (conformalPlusGravitationalWaveMetricDerivs4D H K A B)).h e f a b =
      (fullConformalMetricDerivs H K).h e f a b := by
    rw [(KFCausalCurved4DLinearizedMetricDecomposition.conformalPartMetricDerivs4D_h_eq
      (conformalPlusGravitationalWaveMetricDerivs4D H K A B) e f a b).1,
      conformalPlusGravitationalWave_metricTraceHessian H hH K hK A B e f]
    simp only [fullConformalMetricDerivs,
      KFCausalConformal4DOffDiagonalShearCurvatureSynthesis.fullConformalMetricSecond,
      minkMetric4D,
      KFCausalConformal4DOffDiagonalShearCurvatureSynthesis.symmetrizeHessian4D_eq_of_symm H hH]
  refine ⟨hCH, ?_⟩
  change (conformalPlusGravitationalWaveMetricDerivs4D H K A B).h e f a b -
      (conformalPartMetricDerivs4D
        (conformalPlusGravitationalWaveMetricDerivs4D H K A B)).h e f a b = _
  rw [hCH]
  unfold conformalPlusGravitationalWaveMetricDerivs4D addMetricDerivs
  dsimp
  ring

/-- A combined perturbation `conformalPlusGravitationalWaveMetricDerivs4D H K A B`
(with symmetric `H`) satisfies the linearized vacuum Einstein equation `G = 0`
if and only if its conformal Hessian vanishes (`H = 0`), for arbitrary
gravitational-wave amplitudes `(A, B)`. -/
theorem conformalPlusGravitationalWave_vacuum_iff_hessian_zero
    (H : Hessian4D) (hH : IsSymmetricHessian4D H)
    (K : ThirdJet4D) (A B : ℝ) :
    (∀ b d : Fin 4,
      einstein (conformalPlusGravitationalWaveMetricDerivs4D H K A B) sign b d = 0) ↔
      (∀ μ ν : Fin 4, H μ ν = 0) := by
  have hG := (conformalPlusGravitationalWave_ricci_scalar_einstein H K A B).2.2
  simp_rw [hG]
  exact (KFCausalCurved4DGeneralProbeCurvatureExtraction.fullConformal_vacuum_iff_riemann_flat_iff_hessian_zero
    H hH K).2

/-- A combined perturbation `conformalPlusGravitationalWaveMetricDerivs4D H K A B`
(with symmetric `H`) is conformally flat (`weylTensor4D = 0`) if and only if
both gravitational-wave amplitudes vanish (`A = 0 ∧ B = 0`), for arbitrary `H`. -/
theorem conformalPlusGravitationalWave_conformally_flat_iff_waves_zero
    (H : Hessian4D) (hH : IsSymmetricHessian4D H)
    (K : ThirdJet4D) (A B : ℝ) :
    (∀ a b c d : Fin 4,
      weylTensor4D (conformalPlusGravitationalWaveMetricDerivs4D H K A B) a b c d = 0) ↔
      (A = 0 ∧ B = 0) := by
  have hW := conformalPlusGravitationalWave_weyl_channels H hH K A B
  refine ⟨fun h => ?_, fun ⟨hA, hB⟩ a b c d => ?_⟩
  · have hA : A = 0 := by
      rw [← hW.2.1]
      exact h 0 1 0 1
    have hB : B = 0 := by
      rw [← hW.2.2.2.1]
      exact h 0 1 0 2
    exact ⟨hA, hB⟩
  · subst hA; subst hB
    have hp0 : ∀ i j : Fin 4,
        KFCausalCurved4DTidalWeylProbeExtraction.plusPolarizationTensor4D 0 i j = 0 := by
      intro i j
      unfold KFCausalCurved4DTidalWeylProbeExtraction.plusPolarizationTensor4D
      split_ifs <;> ring
    have hc0 : ∀ i j : Fin 4,
        KFCausalCurved4DTidalWeylProbeExtraction.crossPolarizationTensor4D 0 i j = 0 := by
      intro i j
      unfold KFCausalCurved4DTidalWeylProbeExtraction.crossPolarizationTensor4D
      split_ifs <;> ring
    rw [hW.1 a b c d, weylTensor4D_add,
      (plusWave_vacuum_pure_weyl 0).2.2.2 a b c d,
      (crossWave_vacuum_pure_weyl 0).2.2.2 a b c d]
    simp only [R_metric, plusWaveMetricDerivs4D, crossWaveMetricDerivs4D, hp0, hc0]
    ring

/-- A combined perturbation `conformalPlusGravitationalWaveMetricDerivs4D H K A B`
(with symmetric `H`) is Riemann-flat (`R_metric = 0`) if and only if its
conformal Hessian vanishes (`H = 0`) AND both gravitational-wave amplitudes
vanish (`A = 0 ∧ B = 0`). -/
theorem conformalPlusGravitationalWave_riemann_flat_iff_all_zero
    (H : Hessian4D) (hH : IsSymmetricHessian4D H)
    (K : ThirdJet4D) (A B : ℝ) :
    (∀ a b c d : Fin 4,
      R_metric (conformalPlusGravitationalWaveMetricDerivs4D H K A B) a b c d = 0) ↔
      ((∀ μ ν : Fin 4, H μ ν = 0) ∧ A = 0 ∧ B = 0) := by
  rw [riemann_eq_zero_iff_einstein_electric_magnetic_zero,
    ← weylTensor4D_eq_zero_iff_electric_and_magnetic_zero,
    conformalPlusGravitationalWave_vacuum_iff_hessian_zero H hH K A B,
    conformalPlusGravitationalWave_conformally_flat_iff_waves_zero H hH K A B]

/-- Linearity of `reconstructRiemannFromEinsteinAndWeyl4D` across metric
perturbation addition. -/
theorem reconstructRiemannFromEinsteinAndWeyl4D_add
    (md₁ md₂ : MetricDerivs 4) (a b c d : Fin 4) :
    reconstructRiemannFromEinsteinAndWeyl4D
      (einstein (addMetricDerivs md₁ md₂) sign)
      (weylElectric4D (addMetricDerivs md₁ md₂))
      (weylMagnetic4D (addMetricDerivs md₁ md₂)) a b c d =
    reconstructRiemannFromEinsteinAndWeyl4D
      (einstein md₁ sign) (weylElectric4D md₁) (weylMagnetic4D md₁) a b c d +
    reconstructRiemannFromEinsteinAndWeyl4D
      (einstein md₂ sign) (weylElectric4D md₂) (weylMagnetic4D md₂) a b c d := by
  rw [reconstructRiemannFromEinsteinAndWeyl4D_exact,
    reconstructRiemannFromEinsteinAndWeyl4D_exact,
    reconstructRiemannFromEinsteinAndWeyl4D_exact,
    R_metric_add]

/-! ### Master 20-Component 4D Riemann & Causal-Diamond Synthesis Theorem -/

/-- **Master 20-Component 4D Riemann Curvature & Causal-Diamond Continuum Synthesis**:
Simultaneously establishes for general 4D metric perturbations `md : MetricDerivs 4`
and combined conformal + gravitational-wave superpositions:
1. **Exact 20-Component Reconstruction**: `R_metric md` is explicitly reconstructed
   from `(einstein md sign, weylElectric4D md, weylMagnetic4D md)`, where `weylElectric4D`
   is symmetric and spatially traceless (`E_{11} + E_{22} + E_{33} = 0`, 5 components)
   and `weylMagnetic4D` is spatially traceless and satisfies the cyclic Bianchi identity
   (`B_{123} + B_{231} + B_{312} = 0`, 5 components).
2. **20-Component Flatness Equivalence**:
   `R_metric md = 0 ↔ (einstein md sign = 0 ∧ weylElectric4D md = 0 ∧ weylMagnetic4D md = 0)`.
3. **Orthogonal Conformal + Gravitational-Wave Channel Separation & Extraction**:
   for `md_comb = conformalPlusGravitationalWaveMetricDerivs4D H K A B`, the Einstein
   channel reconstructs all 10 components of `H` while the Weyl tidal probes extract
   both gravitational-wave polarization amplitudes `(A, B)`.
4. **General 4D Contracted Bianchi & On-Shell Stress-Energy Conservation**:
   `∑ e, sign e * dEinstein (riemannFromMetric md) sign e ν e = 0` and
   `lorentzianStressEnergyDivergence4D dT ν = 0`.
5. **Causal-Diamond Continuum Convergence**: joint convergence of the 4D causal-diamond
   operator and temporal BDG curvature variation. -/
theorem twenty_component_4D_riemann_diamond_master_synthesis
    (c : ℝ) (hc : |c| ≤ 1 / 54)
    (md : MetricDerivs 4)
    (H : Hessian4D) (hH : IsSymmetricHessian4D H)
    (K : ThirdJet4D) (A B : ℝ)
    (dT : Fin 4 → Fin 4 → Fin 4 → ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (hEFE : ∀ e a b : Fin 4,
      dEinstein (riemannFromMetric md) sign e a b = κ * dT e a b) :
    let md_comb := conformalPlusGravitationalWaveMetricDerivs4D H K A B
    -- (1) Exact 20-component Riemann reconstruction and gravito-EM trace/Bianchi constraints
    ((∀ a b c d : Fin 4,
        reconstructRiemannFromEinsteinAndWeyl4D
          (einstein md sign) (weylElectric4D md) (weylMagnetic4D md) a b c d =
          R_metric md a b c d) ∧
      weylElectric4D md 1 1 + weylElectric4D md 2 2 + weylElectric4D md 3 3 = 0 ∧
      weylMagnetic4D md 1 2 3 + weylMagnetic4D md 2 3 1 + weylMagnetic4D md 3 1 2 = 0) ∧
    -- (2) 20-component Riemann flatness equivalence
    ((∀ a b c d : Fin 4, R_metric md a b c d = 0) ↔
      ((∀ b d : Fin 4, einstein md sign b d = 0) ∧
        (∀ a b : Fin 4, weylElectric4D md a b = 0) ∧
        (∀ a b c : Fin 4, weylMagnetic4D md a b c = 0))) ∧
    -- (3) Simultaneous extraction of 10-component conformal H and 2-component GW (A, B)
    ((∀ μ ν : Fin 4,
        reconstructHessianFromEinstein4D (einstein md_comb sign) μ ν = H μ ν ∧
        reconstructHessianFromProbes4D (einstein md_comb sign) μ ν = H μ ν) ∧
      weylTidalProbe (basisVec4D 0) (basisVec4D 1) (basisVec4D 0) (basisVec4D 1) md_comb = A ∧
      weylTidalProbe (basisVec4D 0) (basisVec4D 1) (basisVec4D 0) (basisVec4D 2) md_comb = B) ∧
    -- (4) General 4D contracted Bianchi identity and on-shell stress-energy conservation
    (∀ ν : Fin 4,
      (∑ e : Fin 4, sign e * dEinstein (riemannFromMetric md) sign e ν e) = 0 ∧
      lorentzianStressEnergyDivergence4D dT ν = 0) ∧
    -- (5) Causal-diamond continuum limit of operator and temporal curvature derivative
    (Tendsto (fun rho =>
        (KFCausalConformal4DCoupledWaveVariationSynthesis.actual4DOperator rho c,
          temporalVariationDerivative rho)) atTop
      (𝓝 (8 - 6 * c, -6)) ∧
      Tendsto (fun rho => deriv (KFCausalBDG4DActualTemporalVariation.operator rho) 0) atTop
        (𝓝 ((1 / 2) * deriv temporalEinsteinTrace 0))) := by
  intro md_comb
  have hrec := conformalPlusGravitationalWave_joint_reconstruction H hH K A B
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨reconstructRiemannFromEinsteinAndWeyl4D_exact md,
      weylElectric4D_spatial_trace_zero md,
      weylMagnetic4D_cyclic_bianchi md 1 2 3⟩
  · exact riemann_eq_zero_iff_einstein_electric_magnetic_zero md
  · exact ⟨hrec.1, hrec.2.1, hrec.2.2.2.1⟩
  · intro ν
    exact ⟨lorentzian_metric_divergence md ν,
      general_onShell_stressEnergy_conservation md dT κ hκ hEFE ν⟩
  · exact ⟨(joint_operator_and_derivative_tendsto c hc).2,
      bdg_temporal_variation_tendsto_half_einsteinTrace_deriv⟩

#print axioms reconstructRiemannFromEinsteinAndWeyl4D_exact
#print axioms riemann_eq_iff_einstein_electric_magnetic_eq
#print axioms riemann_eq_zero_iff_einstein_electric_magnetic_zero
#print axioms conformalPlusGravitationalWave_metricTraceHessian
#print axioms conformalPlusGravitationalWave_ricci_scalar_einstein
#print axioms conformalPlusGravitationalWave_weyl_channels
#print axioms conformalPlusGravitationalWave_joint_reconstruction
#print axioms conformalPlusGravitationalWave_injective
#print axioms conformalPlusGravitationalWave_projection_split
#print axioms conformalPlusGravitationalWave_vacuum_iff_hessian_zero
#print axioms conformalPlusGravitationalWave_conformally_flat_iff_waves_zero
#print axioms conformalPlusGravitationalWave_riemann_flat_iff_all_zero
#print axioms reconstructRiemannFromEinsteinAndWeyl4D_add
#print axioms twenty_component_4D_riemann_diamond_master_synthesis

end
end UnifiedTheory.Audit.KFCausalCurved4DTwentyComponentRiemannMasterSynthesis
