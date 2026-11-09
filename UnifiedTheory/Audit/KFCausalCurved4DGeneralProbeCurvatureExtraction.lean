import UnifiedTheory.Audit.KFCausalCurved4DLinearizedWeylRicciSplit

/-! General 4D linearized metric curvature synthesis:
Einstein-tensor reconstruction of the 4D Ricci-Scalar Riemann part,
exact decomposition `R_metric = weylTensor4D(tracelessPart) + einsteinRiemannPart4D(G)`,
vacuum Einstein ↔ pure Weyl curvature equivalence, conformally flat vacuum
flatness theorem, general on-shell stress-energy conservation, and the master
4D Weyl-Einstein-diamond continuum synthesis. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCurved4DGeneralProbeCurvatureExtraction
noncomputable section

open Set MeasureTheory Filter Topology
open scoped Real BigOperators
open UnifiedTheory.LayerA.Bianchi (RiemannData)
open UnifiedTheory.LayerA.MetricConstruction (MetricDerivs R_metric dR_metric riemannFromMetric)
open KFCausalConformal4DDiamondBenchmark (sign eta)
open KFCausalLorentzianContractedBianchi (ricci scalar einstein dRic divRic
  dScalar dEinstein lorentzian_metric_divergence)
open KFCausalConformal4DCoupledWaveVariationSynthesis (temporalVariationDerivative
  joint_operator_and_derivative_tendsto)
open KFCausalConformal4DLorentzianBianchiTraceSynthesis (einsteinTrace
  temporalEinsteinTrace lorentzian_einsteinTrace_eq_neg_scalar
  bdg_temporal_variation_tendsto_half_einsteinTrace_deriv)
open KFCausalConformal4DOffDiagonalShearCurvatureSynthesis (Hessian4D ThirdJet4D
  IsSymmetricHessian4D IsSymmetricThirdJet4D minkMetric4D box4D
  fullConformalMetricDerivs fullRicciTensor4D fullScalarCurvature4D
  fullEinsteinTensor4D fullEinsteinTrace4D minkMetric4D_diag)
open KFCausalConformal4DCurvedDiamondMasterSynthesis (reconstructHessianFromEinstein4D
  reconstructHessianFromRicciAndScalar4D reconstructHessianFromProbes4D
  lorentzianStressEnergyDivergence4D reconstructHessianFromEinstein4D_exact
  reconstructHessianFromRicciAndScalar4D_exact reconstructHessianFromProbes4D_exact)
open KFCausalCurved4DLinearizedMetricDecomposition (zeroMetricDerivs addMetricDerivs
  smulMetricDerivs subMetricDerivs finsetSumMetricDerivs
  minkMetric4D_lorentzian_trace lorentzianMetricTrace4D lorentzianMetricThirdTrace4D
  metricTraceHessian4D metricTraceThirdJet4D
  metricTraceHessian4D_symmetric metricTraceThirdJet4D_symmetric
  conformalPartMetricDerivs4D tracelessPartMetricDerivs4D
  metricDerivs4D_conformal_traceless_decomposition
  tracelessPartMetricDerivs4D_trace_free
  metricTrace_projection_idempotent_and_orthogonal
  curvature_conformal_traceless_split)
open KFCausalCurved4DLinearizedWeylRicciSplit (ricciCurvaturePart4D
  scalarCurvaturePart4D ricciScalarRiemannPart4D weylTensor4D
  riemann_eq_weyl_add_ricciScalar
  weylTensor4D_antisym1 weylTensor4D_antisym2
  weylTensor4D_pair_symm weylTensor4D_first_bianchi
  ricciScalarRiemannPart4D_trace_eq_ricci
  weylTensor4D_trace_free_13 weylTensor4D_all_six_traces_vanish
  fullConformal_R_metric_formula
  weylTensor4D_fullConformal_eq_zero weylTensor4D_conformalPart_eq_zero
  weylTensor4D_eq_tracelessPart)

/-! ### Einstein Reconstruction of the 4D Ricci Tensor and Ricci-Scalar Riemann Part -/

/-- Lorentzian trace `Tr_η(G) = ∑ b, sign b * G b b` of any 4×4 tensor `G`. -/
def lorentzianTensorTrace4D (G : Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ b : Fin 4, sign b * G b b

/-- Lorentzian trace `Tr_η(G(md)) = ∑ b, sign b * einstein md sign b b` of the
4D linearized Einstein tensor of `md : MetricDerivs 4`. -/
def lorentzianEinsteinTrace4D (md : MetricDerivs 4) : ℝ :=
  lorentzianTensorTrace4D (einstein md sign)

/-- Reconstruction of the 4D Ricci tensor `Ric_{bd} = G_{bd} - (1/2) Tr_η(G) η_{bd}`
directly from the 4D Einstein tensor `G`. -/
def reconstructRicciFromEinstein4D (G : Fin 4 → Fin 4 → ℝ) (b d : Fin 4) : ℝ :=
  G b d - (1 / 2) * lorentzianTensorTrace4D G * minkMetric4D b d

/-- Direct expression for the Ricci-Scalar (Kulkarni-Nomizu) part of the 4D
Riemann tensor purely in terms of the 10 components of the Einstein tensor `G`:
`R^{(G)}_{abcd} = (1/2)(η_{ac} G_{bd} - η_{ad} G_{bc} - η_{bc} G_{ad} + η_{bd} G_{ac})`
`- (1/3) Tr_η(G) (η_{ac} η_{bd} - η_{ad} η_{bc})`. -/
def einsteinRiemannPart4D (G : Fin 4 → Fin 4 → ℝ) (a b c d : Fin 4) : ℝ :=
  (1 / 2) * (minkMetric4D a c * G b d -
    minkMetric4D a d * G b c -
    minkMetric4D b c * G a d +
    minkMetric4D b d * G a c) -
  (1 / 3) * lorentzianTensorTrace4D G *
    (minkMetric4D a c * minkMetric4D b d - minkMetric4D a d * minkMetric4D b c)

/-- In 4D Lorentzian signature, the trace of the Einstein tensor is the exact
negative of the scalar curvature for every `md : MetricDerivs 4`:
`lorentzianEinsteinTrace4D md = -scalar md sign`. -/
theorem lorentzianEinsteinTrace4D_eq_neg_scalar (md : MetricDerivs 4) :
    lorentzianEinsteinTrace4D md = -scalar md sign ∧
    scalar md sign = -lorentzianEinsteinTrace4D md := by
  have htr : lorentzianEinsteinTrace4D md = -scalar md sign :=
    (lorentzian_einsteinTrace_eq_neg_scalar md).2
  refine ⟨htr, ?_⟩
  linarith

/-- For every `md : MetricDerivs 4`, `einstein md sign b d` is related to
`ricci md sign b d` by `ricci = einstein - (1/2) Tr_η(G) η`. -/
theorem ricci_eq_reconstructRicciFromEinstein4D (md : MetricDerivs 4) (b d : Fin 4) :
    ricci md sign b d =
      einstein md sign b d - (1 / 2) * lorentzianEinsteinTrace4D md * minkMetric4D b d ∧
    reconstructRicciFromEinstein4D (einstein md sign) b d = ricci md sign b d := by
  have htr := (lorentzianEinsteinTrace4D_eq_neg_scalar md).1
  have hein : einstein md sign b d =
      ricci md sign b d - scalar md sign / 2 * minkMetric4D b d := rfl
  have h1 : ricci md sign b d =
      einstein md sign b d - (1 / 2) * lorentzianEinsteinTrace4D md * minkMetric4D b d := by
    rw [hein, htr]
    ring
  refine ⟨h1, ?_⟩
  unfold reconstructRicciFromEinstein4D lorentzianEinsteinTrace4D at *
  linarith

/-- For every `md : MetricDerivs 4`, the Ricci-Scalar part of the 4D Riemann
tensor equals `einsteinRiemannPart4D (einstein md sign)`. -/
theorem einsteinRiemannPart4D_eq_ricciScalarRiemannPart4D
    (md : MetricDerivs 4) (a b c d : Fin 4) :
    einsteinRiemannPart4D (einstein md sign) a b c d =
      ricciScalarRiemannPart4D md a b c d := by
  unfold einsteinRiemannPart4D ricciScalarRiemannPart4D
    ricciCurvaturePart4D scalarCurvaturePart4D
  have hR_bd := (ricci_eq_reconstructRicciFromEinstein4D md b d).1
  have hR_bc := (ricci_eq_reconstructRicciFromEinstein4D md b c).1
  have hR_ad := (ricci_eq_reconstructRicciFromEinstein4D md a d).1
  have hR_ac := (ricci_eq_reconstructRicciFromEinstein4D md a c).1
  have hS := (lorentzianEinsteinTrace4D_eq_neg_scalar md).2
  rw [hR_bd, hR_bc, hR_ad, hR_ac, hS]
  unfold lorentzianEinsteinTrace4D
  ring

/-- **4D Riemann-Weyl-Einstein Reconstruction Theorem**: for every general 4D
metric perturbation `md : MetricDerivs 4`, the full 20-component Riemann tensor
is the sum of:
1. the 10-component trace-free Weyl tensor `weylTensor4D (tracelessPartMetricDerivs4D md)`
   (determined purely by the traceless part of `md`), and
2. the 10-component Einstein curvature part `einsteinRiemannPart4D (einstein md sign)`
   (determined purely by the Einstein tensor `G_{bd}`). -/
theorem riemann_eq_weyl_add_einsteinRiemannPart4D
    (md : MetricDerivs 4) (a b c d : Fin 4) :
    R_metric md a b c d =
      weylTensor4D md a b c d +
        einsteinRiemannPart4D (einstein md sign) a b c d ∧
    R_metric md a b c d =
      weylTensor4D (tracelessPartMetricDerivs4D md) a b c d +
        einsteinRiemannPart4D (einstein md sign) a b c d := by
  have h1 : R_metric md a b c d =
      weylTensor4D md a b c d +
        einsteinRiemannPart4D (einstein md sign) a b c d := by
    rw [einsteinRiemannPart4D_eq_ricciScalarRiemannPart4D,
      (riemann_eq_weyl_add_ricciScalar md a b c d).1]
  refine ⟨h1, ?_⟩
  rw [← weylTensor4D_eq_tracelessPart md a b c d]
  exact h1

/-! ### Vacuum Einstein = Pure Weyl Curvature Equivalences -/

/-- In 4D Lorentzian signature, vanishing of the Einstein tensor `G_{bd} = 0`
is equivalent to vanishing of the Ricci tensor `Ric_{bd} = 0`. -/
theorem vacuum_einstein_iff_ricci_zero (md : MetricDerivs 4) :
    (∀ b d : Fin 4, einstein md sign b d = 0) ↔
      (∀ b d : Fin 4, ricci md sign b d = 0) := by
  refine ⟨fun hG b d => ?_, fun hRic b d => ?_⟩
  · have htr : lorentzianEinsteinTrace4D md = 0 := by
      unfold lorentzianEinsteinTrace4D lorentzianTensorTrace4D
      apply Finset.sum_eq_zero
      intro a _
      rw [hG a a, mul_zero]
    rw [(ricci_eq_reconstructRicciFromEinstein4D md b d).1, hG b d, htr]
    ring
  · have hS : scalar md sign = 0 := by
      unfold scalar
      apply Finset.sum_eq_zero
      intro a _
      rw [hRic a a, mul_zero]
    unfold einstein
    rw [hRic b d, hS]
    ring

/-- **Vacuum Einstein ↔ Pure Weyl Curvature Theorem**: a 4D linearized metric
perturbation `md : MetricDerivs 4` satisfies the vacuum Einstein equation
`einstein md sign = 0` if and only if its Riemann tensor equals its Weyl tensor
identically (`R_metric md = weylTensor4D md`). -/
theorem vacuum_einstein_iff_riemann_eq_weyl (md : MetricDerivs 4) :
    (∀ b d : Fin 4, einstein md sign b d = 0) ↔
      (∀ a b c d : Fin 4, R_metric md a b c d = weylTensor4D md a b c d) := by
  refine ⟨fun hG a b c d => ?_, fun hRW => ?_⟩
  · have htr : lorentzianTensorTrace4D (einstein md sign) = 0 := by
      unfold lorentzianTensorTrace4D
      apply Finset.sum_eq_zero
      intro i _
      rw [hG i i, mul_zero]
    have hEpart : einsteinRiemannPart4D (einstein md sign) a b c d = 0 := by
      unfold einsteinRiemannPart4D
      rw [hG b d, hG b c, hG a d, hG a c, htr]
      ring
    rw [(riemann_eq_weyl_add_einsteinRiemannPart4D md a b c d).1, hEpart, add_zero]
  · rw [vacuum_einstein_iff_ricci_zero]
    intro b d
    unfold ricci
    have hsum : (∑ a : Fin 4, sign a * R_metric md a b a d) =
        ∑ a : Fin 4, sign a * weylTensor4D md a b a d := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hRW a b a d]
    rw [hsum, weylTensor4D_trace_free_13]

/-- **Conformally Flat Vacuum Flatness Theorem**: if a 4D metric perturbation `md`
has vanishing Weyl tensor (`∀ a b c d, weylTensor4D md a b c d = 0`), then it
satisfies the vacuum Einstein equation `G_{bd} = 0` if and only if it is
Riemann-flat (`R_{abcd} = 0`). -/
theorem conformally_flat_vacuum_iff_riemann_flat (md : MetricDerivs 4)
    (hweyl : ∀ a b c d : Fin 4, weylTensor4D md a b c d = 0) :
    (∀ b d : Fin 4, einstein md sign b d = 0) ↔
      (∀ a b c d : Fin 4, R_metric md a b c d = 0) := by
  rw [vacuum_einstein_iff_riemann_eq_weyl]
  refine ⟨fun h a b c d => ?_, fun h a b c d => ?_⟩
  · rw [h a b c d, hweyl a b c d]
  · rw [h a b c d, hweyl a b c d]

/-- For any 4D conformal metric perturbation `fullConformalMetricDerivs H K`
with symmetric Hessian `H`, the following three conditions are equivalent:
1. Vacuum Einstein equation `einstein (fullConformalMetricDerivs H K) sign = 0`,
2. Vanishing Riemann tensor `R_metric (fullConformalMetricDerivs H K) = 0`,
3. Vanishing conformal Hessian `H = 0`. -/
theorem fullConformal_vacuum_iff_riemann_flat_iff_hessian_zero
    (H : Hessian4D) (hH : IsSymmetricHessian4D H) (K : ThirdJet4D) :
    ((∀ b d : Fin 4, einstein (fullConformalMetricDerivs H K) sign b d = 0) ↔
      (∀ a b c d : Fin 4, R_metric (fullConformalMetricDerivs H K) a b c d = 0)) ∧
    ((∀ b d : Fin 4, einstein (fullConformalMetricDerivs H K) sign b d = 0) ↔
      (∀ μ ν : Fin 4, H μ ν = 0)) := by
  refine ⟨conformally_flat_vacuum_iff_riemann_flat
      (fullConformalMetricDerivs H K) (weylTensor4D_fullConformal_eq_zero H hH K), ?_⟩
  refine ⟨fun hG μ ν => ?_, fun hH0 b d => ?_⟩
  · have hrec := reconstructHessianFromEinstein4D_exact H hH μ ν
    have hG_eq : fullEinsteinTensor4D H = fun a b => 0 := by
      funext a b
      exact hG a b
    rw [hG_eq] at hrec
    unfold reconstructHessianFromEinstein4D at hrec
    simp only [mul_zero, Finset.sum_const_zero, zero_mul, add_zero] at hrec
    exact hrec.symm
  · change fullEinsteinTensor4D H b d = 0
    rw [KFCausalConformal4DOffDiagonalShearCurvatureSynthesis.fullEinsteinTensor4D_master_formula
      H hH b d, hH0 b d]
    have hbox : box4D H = 0 := by
      unfold box4D
      apply Finset.sum_eq_zero
      intro a _
      rw [hH0 a a, mul_zero]
    rw [hbox]
    ring

/-! ### General On-Shell Stress-Energy Conservation for Arbitrary `MetricDerivs 4` -/

/-- General 4D on-shell stress-energy conservation: for ANY (not necessarily
conformal) 4D metric perturbation `md : MetricDerivs 4`, if the differentiated
Einstein tensor satisfies the coupled linearized field equation
`∂_e G_{ab}(md) = κ * dT e a b` with `κ ≠ 0`, then the Lorentzian divergence
`∑ e, sign e * dT e ν e` vanishes identically for all `ν : Fin 4`. -/
theorem general_onShell_stressEnergy_conservation (md : MetricDerivs 4)
    (dT : Fin 4 → Fin 4 → Fin 4 → ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (heq : ∀ e a b : Fin 4,
      dEinstein (riemannFromMetric md) sign e a b = κ * dT e a b)
    (ν : Fin 4) :
    lorentzianStressEnergyDivergence4D dT ν = 0 := by
  have hdiv : (∑ e : Fin 4, sign e * dEinstein (riemannFromMetric md) sign e ν e) = 0 :=
    lorentzian_metric_divergence md ν
  have hrel : (∑ e : Fin 4, sign e * dEinstein (riemannFromMetric md) sign e ν e) =
      κ * lorentzianStressEnergyDivergence4D dT ν := by
    unfold lorentzianStressEnergyDivergence4D
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [heq e ν e]
    ring
  rw [hrel] at hdiv
  exact (mul_eq_zero.mp hdiv).resolve_left hκ

/-! ### Master 4D General Linearized Metric Weyl-Einstein-Diamond Synthesis -/

/-- **Master Synthesis Theorem for General 4D Linearized Metric Perturbations**:
For any general 4D metric perturbation jet `md : MetricDerivs 4`, simultaneously establishes:
1. **Conformal/Traceless Jet Decomposition**: `md = conformalPart + tracelessPart`,
   where `tracelessPart` is identically trace-free (`Tr_η(h^{TT}) = 0`, `Tr_η(k^{TT}) = 0`)
   and `metricTraceHessian4D` is an idempotent projection annihilating `tracelessPart`.
2. **Exact 20 = 10 + 10 Riemann-Weyl-Einstein Decomposition**:
   `R_metric md = weylTensor4D (tracelessPartMetricDerivs4D md) + einsteinRiemannPart4D (einstein md sign)`,
   where `weylTensor4D` vanishes identically on `conformalPartMetricDerivs4D md` and satisfies all
   Riemann symmetries, the first Bianchi identity, and identical vanishing of all 6 Lorentzian traces.
3. **Vacuum Gravitational-Wave Characterization**:
   `einstein md sign = 0 ↔ R_metric md = weylTensor4D md`.
4. **General Contracted Bianchi & On-Shell Stress-Energy Conservation**:
   `∑ e, sign e * dEinstein (riemannFromMetric md) sign e ν e = 0` and
   `lorentzianStressEnergyDivergence4D dT ν = 0` for any coupled stress-energy jet `dT`.
5. **Causal-Diamond Continuum & Polarization-Probe Extraction of the Conformal Trace Hessian**:
   all 10 components of `H = metricTraceHessian4D md` are reconstructed from the conformal
   Einstein tensor and polarization probes, alongside the joint continuum limit of the 4D
   causal-diamond wave/curvature operator and temporal BDG variation. -/
theorem general_4D_metric_weyl_einstein_diamond_master_synthesis
    (c : ℝ) (hc : |c| ≤ 1 / 54)
    (md : MetricDerivs 4)
    (dT : Fin 4 → Fin 4 → Fin 4 → ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (hEFE : ∀ e a b : Fin 4,
      dEinstein (riemannFromMetric md) sign e a b = κ * dT e a b) :
    -- (1) Conformal + traceless jet decomposition and trace-freeness
    ((∀ e f a b : Fin 4,
        md.h e f a b =
          (conformalPartMetricDerivs4D md).h e f a b +
            (tracelessPartMetricDerivs4D md).h e f a b) ∧
      (∀ e f : Fin 4,
        (∑ a : Fin 4, sign a * (tracelessPartMetricDerivs4D md).h e f a a) = 0) ∧
      metricTraceHessian4D (conformalPartMetricDerivs4D md) = metricTraceHessian4D md ∧
      (∀ e f : Fin 4, metricTraceHessian4D (tracelessPartMetricDerivs4D md) e f = 0)) ∧
    -- (2) Exact 4D Riemann = Weyl(traceless) + Einstein decomposition & Weyl trace-freeness
    ((∀ a b c d : Fin 4,
        R_metric md a b c d =
          weylTensor4D (tracelessPartMetricDerivs4D md) a b c d +
            einsteinRiemannPart4D (einstein md sign) a b c d ∧
        weylTensor4D (conformalPartMetricDerivs4D md) a b c d = 0 ∧
        weylTensor4D md a b c d + weylTensor4D md b c a d + weylTensor4D md c a b d = 0) ∧
      (∀ b d : Fin 4, (∑ a : Fin 4, sign a * weylTensor4D md a b a d) = 0)) ∧
    -- (3) Vacuum Einstein ↔ pure Weyl curvature equivalence
    ((∀ b d : Fin 4, einstein md sign b d = 0) ↔
      (∀ a b c d : Fin 4, R_metric md a b c d = weylTensor4D md a b c d)) ∧
    -- (4) General contracted Bianchi identity and on-shell stress-energy conservation
    (∀ ν : Fin 4,
      (∑ e : Fin 4, sign e * dEinstein (riemannFromMetric md) sign e ν e) = 0 ∧
      lorentzianStressEnergyDivergence4D dT ν = 0) ∧
    -- (5) Full 10-component conformal trace Hessian reconstruction and causal-diamond continuum limit
    ((∀ μ ν : Fin 4,
        reconstructHessianFromEinstein4D
          (fullEinsteinTensor4D (metricTraceHessian4D md)) μ ν =
            metricTraceHessian4D md μ ν ∧
        reconstructHessianFromProbes4D
          (fullEinsteinTensor4D (metricTraceHessian4D md)) μ ν =
            metricTraceHessian4D md μ ν) ∧
      Tendsto (fun rho =>
          (KFCausalConformal4DCoupledWaveVariationSynthesis.actual4DOperator rho c,
            temporalVariationDerivative rho)) atTop
        (𝓝 (8 - 6 * c, -6)) ∧
      Tendsto (fun rho => deriv (KFCausalBDG4DActualTemporalVariation.operator rho) 0) atTop
        (𝓝 ((1 / 2) * deriv temporalEinsteinTrace 0))) := by
  have hH_symm := metricTraceHessian4D_symmetric md
  have hproj := metricTrace_projection_idempotent_and_orthogonal md
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨(metricDerivs4D_conformal_traceless_decomposition md).1,
      (tracelessPartMetricDerivs4D_trace_free md).1,
      hproj.1, hproj.2.1⟩
  · refine ⟨fun a b c d => ?_, weylTensor4D_trace_free_13 md⟩
    exact ⟨(riemann_eq_weyl_add_einsteinRiemannPart4D md a b c d).2,
      weylTensor4D_conformalPart_eq_zero md a b c d,
      weylTensor4D_first_bianchi md a b c d⟩
  · exact vacuum_einstein_iff_riemann_eq_weyl md
  · intro ν
    exact ⟨lorentzian_metric_divergence md ν,
      general_onShell_stressEnergy_conservation md dT κ hκ hEFE ν⟩
  · refine ⟨fun μ ν => ?_,
      (joint_operator_and_derivative_tendsto c hc).2,
      bdg_temporal_variation_tendsto_half_einsteinTrace_deriv⟩
    exact ⟨reconstructHessianFromEinstein4D_exact (metricTraceHessian4D md) hH_symm μ ν,
      reconstructHessianFromProbes4D_exact (metricTraceHessian4D md) hH_symm μ ν⟩

#print axioms lorentzianEinsteinTrace4D_eq_neg_scalar
#print axioms ricci_eq_reconstructRicciFromEinstein4D
#print axioms einsteinRiemannPart4D_eq_ricciScalarRiemannPart4D
#print axioms riemann_eq_weyl_add_einsteinRiemannPart4D
#print axioms vacuum_einstein_iff_ricci_zero
#print axioms vacuum_einstein_iff_riemann_eq_weyl
#print axioms conformally_flat_vacuum_iff_riemann_flat
#print axioms fullConformal_vacuum_iff_riemann_flat_iff_hessian_zero
#print axioms general_onShell_stressEnergy_conservation
#print axioms general_4D_metric_weyl_einstein_diamond_master_synthesis

end
end UnifiedTheory.Audit.KFCausalCurved4DGeneralProbeCurvatureExtraction
