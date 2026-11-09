/- The propagated chart-moment class contains the existing total coherent
span. Its initial inverse-gap moment is proved by Gaussian absorption,
not postulated as a property of physical packets. -/
import UnifiedTheory.Audit.KFCausalClockFloorChartMomentDomain
import UnifiedTheory.Audit.KFCausalClockFloorGaugeTestDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorChartMomentInitialStates
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart chart_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
open UnifiedTheory.Audit.KFCausalClockFloorLeftBarrier (gap_positive)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan coherentSpan_dense hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSources (state_configuration_coe)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentDerivative (physicalProfile physicalProfile_memLp clockMultiplier)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentClockMomentum (sourceProfile_eq)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry

def weight (ε s : ℝ) : ℝ := (1-(defect ε s)^2)⁻¹

theorem weight_measurable (ε : ℝ) : Measurable (weight ε) := by
  unfold weight defect KFCausalClockFloorFlow.clock
  fun_prop

theorem weight_upper (ε s : ℝ) (hε : 0 < ε) : weight ε s ≤ 1+ε*Real.exp (-s) := by
  have hr := (response_bounds ε s hε).1
  have hd := defect_positive ε s hε
  have he := response_add_defect ε s hε.le
  have hu : defect ε s ≤ 1 := by linarith
  have hg : response ε s ≤ 1-(defect ε s)^2 := by nlinarith
  have hi := inv_anti₀ hr hg
  have hc : (response ε s)⁻¹ = 1+ε*Real.exp (-s) := by
    unfold response KFCausalClockFloorFlow.clock
    rw [Real.exp_neg]
    field_simp
  exact hi.trans_eq hc

def absorptionConstant (ε : ℝ) : ℝ := 1+ε*Real.exp (1/ε+(ε⁻¹)^2/2)

theorem weight_gaussian (ε s : ℝ) (hε : 0 < ε) :
    weight ε s*Real.exp (-(chart ε s)^2) ≤
      absorptionConstant ε*Real.exp (-(1/2:ℝ)*(chart ε s)^2) := by
  have hs : -s ≤ (1+|chart ε s|)/ε := by
    apply (le_div_iff₀ hε).mpr
    by_cases hz : 0 ≤ s
    · nlinarith [abs_nonneg (chart ε s)]
    · have he : Real.exp s ≤ 1 := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (le_of_not_ge hz)
      have ha := neg_le_abs (chart ε s)
      have hchart : chart ε s = Real.exp s+ε*s := rfl
      nlinarith only [ha,he,hchart]
  have hq : -s-(chart ε s)^2 ≤ 1/ε+(ε⁻¹)^2/2-(1/2:ℝ)*(chart ε s)^2 := by
    rw [div_eq_mul_inv,add_mul,one_mul] at hs
    have hp := sq_nonneg (|chart ε s|-ε⁻¹)
    rw [one_div]
    nlinarith only [hs,hp,sq_abs (chart ε s)]
  have he : Real.exp (-s)*Real.exp (-(chart ε s)^2) ≤
      Real.exp (1/ε+(ε⁻¹)^2/2)*Real.exp (-(1/2:ℝ)*(chart ε s)^2) := by
    rw [← Real.exp_add,← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith only [hq])
  have hbase : Real.exp (-(chart ε s)^2) ≤ Real.exp (-(1/2:ℝ)*(chart ε s)^2) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (chart ε s)])
  have hu := mul_le_mul_of_nonneg_right (weight_upper ε s hε) (Real.exp_pos (-(chart ε s)^2)).le
  have hm := mul_le_mul_of_nonneg_left he hε.le
  unfold absorptionConstant
  nlinarith only [hu,hm,hbase]

theorem weighted_clock_memLp (ε : ℝ) (hε : 0 < ε) :
    MemLp (fun s => (weight ε s:ℂ)*clockFunction ε 1 s) 2 volume := by
  have hm := (clockFunction_memLp ε (1/2) hε (by norm_num)).const_smul (absorptionConstant ε:ℂ)
  apply hm.of_le ((Complex.measurable_ofReal.comp (weight_measurable ε)).aestronglyMeasurable.mul
    (clockFunction_continuous ε 1).aestronglyMeasurable)
  filter_upwards [] with s
  have hC : 0 < absorptionConstant ε := by unfold absorptionConstant; positivity
  change ‖(weight ε s:ℂ)*clockFunction ε 1 s‖ ≤
    ‖(absorptionConstant ε:ℂ)*clockFunction ε (1/2) s‖
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hC,clockFunction,
    abs_of_pos (realClock_positive ε 1 s hε.le),
    abs_of_pos (realClock_positive ε (1/2) s hε.le)]
  have hw : |weight ε s| = weight ε s := abs_of_pos (inv_pos.mpr (gap_positive ε hε s))
  rw [hw]
  unfold realClock
  simpa only [one_mul,neg_mul,mul_left_comm,mul_assoc] using
    mul_le_mul_of_nonneg_left (weight_gaussian ε s hε) (by positivity : 0 ≤ 1+ε*Real.exp (-s))

def leftOperator (ε : ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  KFCausalUnitaryRealMultiplier.realPullback (LinearIsometryEquiv.refl ℂ Hilbert)
    (fun x : Configuration => weight ε x.1) ((weight_measurable ε).comp measurable_fst)

theorem state_left_domain (ε h : ℝ) (hε : 0 < ε) (hne : h ≠ 0)
    (p : KFCausalEuclideanProductCoordinates.Joint 2 4) :
    state ε 1 h hε zero_lt_one hne p ∈ (leftOperator ε).domain := by
  apply (KFCausalUnitaryRealMultiplier.realPullback_domain (LinearIsometryEquiv.refl ℂ Hilbert) _ _ _).mpr
  have hm := physicalProfile_memLp (amplitudeConstant h p) (clockFrequency p)
    (groundWidth h) (neutralWidth h) (groundWidth_positive h hne)
    (neutralWidth_positive h hne) (neutralWidth_bound h) (sourceCoefficients h p)
    (fun s => (weight ε s:ℂ)*clockFunction ε 1 s) (weighted_clock_memLp ε hε)
  apply hm.ae_eq
  filter_upwards [state_configuration_coe ε 1 h hε zero_lt_one hne p] with x hx
  change _ = (weight ε x.1:ℂ)*state ε 1 h hε zero_lt_one hne p x
  rw [hx,sourceProfile_eq]
  simp only [physicalProfile,clockMultiplier,amplitudeConstant,clockFrequency,sourceCoefficients]
  ring

theorem domain_moment_integrable (ε : ℝ) (f : Hilbert) (hf : f ∈ (leftOperator ε).domain) :
    Integrable (KFCausalClockFloorInverseGapMoment.density ε f) := by
  let y := leftOperator ε ⟨f,hf⟩
  have hy := (KFCausalUnitaryRealMultiplier.realPullback_graph (LinearIsometryEquiv.refl ℂ Hilbert)
    (fun x : Configuration => weight ε x.1) ((weight_measurable ε).comp measurable_fst) f y).mp
      ((leftOperator ε).mem_graph ⟨f,hf⟩)
  apply ((L2.integrable_inner (𝕜 := ℂ) f y).re).congr
  filter_upwards [hy] with x hx
  change y x = (weight ε x.1:ℂ)*f x at hx
  rw [hx]
  change (inner ℂ (f x) ((weight ε x.1:ℂ) • f x)).re = _
  rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
  change ((weight ε x.1:ℂ)*(‖f x‖:ℂ)^2).re = _
  rw [← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.ofReal_re]
  rfl

theorem physical_initial_dense (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
    (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ) : Dense {f : Hilbert |
    ∃ w : KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hne hh m g k 0,
      KFCausalClockFloorAveragedFormTransport.embedding ε hε h hne hh m g k 0 w = f ∧
        Integrable (KFCausalClockFloorInverseGapMoment.density ε f)} := by
  have hd : Dense (coherentSpan ε 1 h hε zero_lt_one hne : Set Hilbert) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr (coherentSpan_dense ε 1 h hε zero_lt_one hne)
  have hl : coherentSpan ε 1 h hε zero_lt_one hne ≤ (leftOperator ε).domain := by
    apply Submodule.span_le.mpr
    rintro f ⟨p,rfl⟩
    exact state_left_domain ε h hε hne p
  apply hd.mono
  intro f hf
  have he := KFCausalClockFloorAveragedDensity.coherentSpan_le_energy_domain
    ε 1 h hε zero_lt_one hne hh m g k 0 hf
  exact ⟨KFCausalClosedGraphForm.graphVector
    (KFCausalClockFloorAveragedHamiltonian.formData ε hε h hne hh m g k 0) ⟨f,he⟩,
      rfl,domain_moment_integrable ε f (hl hf)⟩

#print axioms weight_measurable
#print axioms weight_upper
#print axioms weight_gaussian
#print axioms weighted_clock_memLp
#print axioms state_left_domain
#print axioms domain_moment_integrable
#print axioms physical_initial_dense
end
end UnifiedTheory.Audit.KFCausalClockFloorChartMomentInitialStates
