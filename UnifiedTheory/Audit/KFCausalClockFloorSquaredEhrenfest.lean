/- Exact Ehrenfest derivative of the squared defect for the actual unbounded
propagator, using form continuity and the weak equation. -/
import UnifiedTheory.Audit.KFCausalClockFloorExactEhrenfest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorSquaredEhrenfest
noncomputable section
open Filter MeasureTheory
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakTrajectory
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakIntegralEquation (limitSlope)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution
open UnifiedTheory.Audit.KFCausalClockFloorReferenceDefect
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorDefectForm (defect_inner)
open UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction
open UnifiedTheory.Audit.KFCausalClockFloorExactEhrenfest (evolvingOutput)

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
  (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum : ℝ)
local notation "V₀" => FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0
local notation "J" => embedding ε hε hbar hh hbound mass2 quartic vacuum 0
local notation "F" => formFlow ε hε hbar hh hbound mass2 quartic vacuum
local notation "U" => evolution ε hε hbar hh hbound mass2 quartic vacuum
local notation "D" => defectOperator ε hε
local notation "R₀" => outputAction ε hε hbar hbound
local notation "R" => ContinuousLinearMap.compLp R₀
local notation "A" => formDefect ε hε hbar hh hbound mass2 quartic vacuum 0

theorem square_inner (f g : Hilbert) : inner ℂ (D (D f)) g = inner ℂ f (D (D g)) :=
  (defect_inner ε hε (D f) g).trans (defect_inner ε hε f (D g))

theorem square_embedding (w : V₀) : J (A (A w)) = D (D (J w)) := rfl

theorem output_square_compLp (g : Lp (Output (Fin 8) Hilbert) 2 angleMeasure) :
    ((R₀).comp R₀).compLp g = R (R g) := by
  apply Lp.ext
  filter_upwards [((R₀).comp R₀).coeFn_compLp g,(R₀).coeFn_compLp (R g),(R₀).coeFn_compLp g]
    with θ h0 h1 h2
  rw [h0,h1,h2]
  rfl

theorem reference_square_pairing (t : ℝ) (u : V₀) :
    inner ℂ u (referenceFormOperator ε hε hbar hh hbound mass2 quartic vacuum t (A (A u))) =
      inner ℂ (energyOutput ε hε hbar hh hbound mass2 quartic vacuum t
        (formTransfer ε hε hbar hh hbound mass2 quartic vacuum 0 t u))
        (R (R (energyOutput ε hε hbar hh hbound mass2 quartic vacuum t
          (formTransfer ε hε hbar hh hbound mass2 quartic vacuum 0 t u)))) := by
  have hp := referenceForm_represents_closed_form ε hε hbar hh hbound mass2 quartic vacuum t u (A (A u))
  have hout (v : V₀) : energyOutput ε hε hbar hh hbound mass2 quartic vacuum t
      (formTransfer ε hε hbar hh hbound mass2 quartic vacuum 0 t (A v)) =
      R (energyOutput ε hε hbar hh hbound mass2 quartic vacuum t
        (formTransfer ε hε hbar hh hbound mass2 quartic vacuum 0 t v)) :=
    (congrArg (energyOutput ε hε hbar hh hbound mass2 quartic vacuum t)
      (formDefect_transfer ε hε hbar hh hbound mass2 quartic vacuum 0 t v)).trans
      (formDefect_output ε hε hbar hh hbound mass2 quartic vacuum t
        (formTransfer ε hε hbar hh hbound mass2 quartic vacuum 0 t v))
  have ho := (hout (A u)).trans (congrArg R (hout u))
  exact hp.trans (congrArg (fun z => inner ℂ
    (energyOutput ε hε hbar hh hbound mass2 quartic vacuum t
      (formTransfer ε hε hbar hh hbound mass2 quartic vacuum 0 t u)) z) ho)

def squaredRate (s t : ℝ) (w : V₀) : ℝ :=
  (-2/hbar)*(inner ℂ (evolvingOutput ε hε hbar hh hbound mass2 quartic vacuum s t w)
    (R (R (evolvingOutput ε hε hbar hh hbound mass2 quartic vacuum s t w)))).im

theorem squared_expectation_derivative (s t : ℝ) (w : V₀) :
    HasDerivAt (fun r => (inner ℂ (U s r (J w)) (D (D (U s r (J w))))).re)
      (squaredRate ε hε hbar hh hbound mass2 quartic vacuum s t w) t := by
  let V := weakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w
  have hd := KFCausalFormObservableDerivative.expectation_derivative J ((D).comp D)
    (massOperator ε hε hbar hh hbound mass2 quartic vacuum) ((A).comp A)
    (mass_left_pairing ε hε hbar hh hbound mass2 quartic vacuum)
    (square_embedding ε hε hbar hh hbound mass2 quartic vacuum)
    (square_inner ε hε)
    V.formState (massSlope ε hε hbar hh hbound mass2 quartic vacuum s w V t)
    t (massLipschitzBound ε hε hbar hh hbound mass2 quartic vacuum s (|t|+1) w)
    (massLipschitzBound_nonneg ε hε hbar hh hbound mass2 quartic vacuum s (|t|+1) w)
    (formFlow_continuous ε hε hbar hh hbound mass2 quartic vacuum s w).continuousAt
    ?_ (mass_pairing_derivative ε hε hbar hh hbound mass2 quartic vacuum s w V t)
  · have hr : 2*(inner ℂ (massSlope ε hε hbar hh hbound mass2 quartic vacuum s w V t)
        (A (A (V.formState t)))).re = squaredRate ε hε hbar hh hbound mass2 quartic vacuum s t w := by
      rw [massSlope_pairing,limitSlope,reference_square_pairing]
      simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,mul_zero,sub_zero,zero_add,zero_sub]
      unfold squaredRate evolvingOutput
      dsimp only [V,formFlow]
      ring
    simpa only [KFCausalFormObservableDerivative.expectation,ContinuousLinearMap.comp_apply,evolution_embedding] using hd.congr_deriv hr
  · have he : ∀ᶠ h in 𝓝 (0:ℝ), |h| < 1 := by
      simpa only [abs_zero] using (continuous_abs.tendsto (0:ℝ)).eventually
        (gt_mem_nhds (by norm_num : |(0:ℝ)| < 1))
    filter_upwards [he.filter_mono nhdsWithin_le_nhds] with h hsmall
    have hsum : |t+h| ≤ |t|+|h| := abs_add_le _ _
    simpa only [add_sub_cancel_left] using
      massState_window_lipschitz ε hε hbar hh hbound mass2 quartic vacuum s w V
        (|t|+1) t (t+h) (by positivity) (by linarith) (hsum.trans (by linarith))

theorem norm_square_derivative (s t : ℝ) (w : V₀) :
    HasDerivAt (fun r => ‖D (U s r (J w))‖^2)
      (squaredRate ε hε hbar hh hbound mass2 quartic vacuum s t w) t := by
  have he (r : ℝ) : (inner ℂ (U s r (J w)) (D (D (U s r (J w))))).re = ‖D (U s r (J w))‖^2 := by
    rw [← defect_inner ε hε]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  simpa only [he] using squared_expectation_derivative ε hε hbar hh hbound mass2 quartic vacuum s t w

#print axioms square_inner
#print axioms square_embedding
#print axioms output_square_compLp
#print axioms reference_square_pairing
#print axioms squared_expectation_derivative
#print axioms norm_square_derivative

end
end UnifiedTheory.Audit.KFCausalClockFloorSquaredEhrenfest
