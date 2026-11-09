/- Polarized full-energy covariance in the reference form used by the
actual propagator. The growing kinetic terms are retained explicitly. -/
import UnifiedTheory.Audit.KFCausalClockFloorGaugeEnergy
import UnifiedTheory.Audit.KFCausalClockFloorReferenceChartModulation
import UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGaugePairing
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalClockFloorGaugeEnergy
open UnifiedTheory.Audit.KFCausalClockFloorClosedChartModulation (outputAction)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedOutputTransport (timeOutputLp)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyTransport (timeOutput)
open UnifiedTheory.Audit.KFCausalFiniteOutputRescaling (selected_apply)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorReferenceChartModulation
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity

theorem output_compLp (ε h t : ℝ) (g : EnergyOutputSpace) :
    (outputAction ε h (rate h t)).compLp (timeOutputLp 0 t g) = gaugeOutputLp ε h t g := by
  apply Lp.ext
  filter_upwards [(outputAction ε h (rate h t)).coeFn_compLp (timeOutputLp 0 t g),
    (timeOutput 0 t).coeFn_compLp g,(gaugeOutput ε h t).coeFn_compLp g] with θ h1 h2 h3
  change (outputAction ε h (rate h t)).compLp (timeOutputLp 0 t g) θ =
    (gaugeOutput ε h t).compLp g θ
  rw [h1,h3]
  change outputAction ε h (rate h t) ((timeOutput 0 t).compLp g θ) = _
  rw [h2]
  rfl

theorem gaugeOutput_inner (ε h t : ℝ) (hne : h ≠ 0) (x y : Output (Fin 8) Hilbert) :
    inner ℂ (gaugeOutput ε h t x) (gaugeOutput ε h t y) =
      inner ℂ (fixedOutput x) (fixedOutput y)+(Real.exp (2*t):ℂ)*
        inner ℂ (kineticOutput x) (kineticOutput y) := by
  rw [PiLp.inner_apply,PiLp.inner_apply,PiLp.inner_apply,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have he : (Real.exp t:ℂ)*(Real.exp t:ℂ) = (Real.exp (2*t):ℂ) := by
    rw [← Complex.ofReal_mul,← Real.exp_add,two_mul]
  by_cases hi : kinetic i
  · simp only [gaugeOutput_apply ε h t hne,hi,if_true,fixedOutput,kineticOutput,selected_apply,
      not_true_eq_false,if_false,inner_zero_left,zero_add,inner_smul_left,inner_smul_right,
      Complex.conj_ofReal,LinearIsometryEquiv.inner_map_map,← mul_assoc,he]
  · simp only [gaugeOutput_apply ε h t hne,hi,if_false,fixedOutput,kineticOutput,selected_apply,
      not_false_eq_true,if_true,inner_zero_left,mul_zero,add_zero,LinearIsometryEquiv.inner_map_map]

theorem gaugeOutputLp_inner (ε h t : ℝ) (hne : h ≠ 0) (x y : EnergyOutputSpace) :
    inner ℂ (gaugeOutputLp ε h t x) (gaugeOutputLp ε h t y) =
      inner ℂ (fixedOutputLp x) (fixedOutputLp y)+(Real.exp (2*t):ℂ)*
        inner ℂ (kineticOutputLp x) (kineticOutputLp y) := by
  have he : (fun θ => inner ℂ (gaugeOutputLp ε h t x θ) (gaugeOutputLp ε h t y θ)) =ᵐ[angleMeasure]
      fun θ => inner ℂ (fixedOutputLp x θ) (fixedOutputLp y θ)+(Real.exp (2*t):ℂ)*
        inner ℂ (kineticOutputLp x θ) (kineticOutputLp y θ) := by
    filter_upwards [(gaugeOutput ε h t).coeFn_compLp x,(gaugeOutput ε h t).coeFn_compLp y,
      fixedOutput.coeFn_compLp x,fixedOutput.coeFn_compLp y,
      kineticOutput.coeFn_compLp x,kineticOutput.coeFn_compLp y] with θ h1 h2 h3 h4 h5 h6
    change inner ℂ ((gaugeOutput ε h t).compLp x θ) ((gaugeOutput ε h t).compLp y θ) =
      inner ℂ (fixedOutput.compLp x θ) (fixedOutput.compLp y θ)+(Real.exp (2*t):ℂ)*
        inner ℂ (kineticOutput.compLp x θ) (kineticOutput.compLp y θ)
    rw [h1,h2,h3,h4,h5,h6,gaugeOutput_inner ε h t hne]
  rw [L2.inner_def,integral_congr_ae he,
    integral_add (L2.integrable_inner (𝕜 := ℂ) (fixedOutputLp x) (fixedOutputLp y))
      ((L2.integrable_inner (𝕜 := ℂ) (kineticOutputLp x) (kineticOutputLp y)).const_mul _),
    integral_const_mul,← L2.inner_def,← L2.inner_def]

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)
  (m q k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m q k 0
local notation "A" => energyOutput ε hε h hne hh m q k 0
local notation "R" => (fun r : ℝ => formAction ε hε h hne hh m q k r 0)
local notation "Q" => referenceFormOperator ε hε h hne hh m q k

theorem formAction_time_output (t : ℝ) (u : V) :
    energyOutput ε hε h hne hh m q k t
      (formTransfer ε hε h hne hh m q k 0 t (R (rate h t) u)) = gaugeOutputLp ε h t (A u) := by
  have ht := formAction_transfer ε hε h hne hh m q k (rate h t) 0 t u
  have ho := formAction_output ε hε h hne hh m q k (rate h t) t
    (formTransfer ε hε h hne hh m q k 0 t u)
  have ha := transfer_energyOutput ε hε h hne hh m q k 0 t u
  exact (congrArg (energyOutput ε hε h hne hh m q k t) ht).trans
    (ho.trans ((congrArg (fun y => (outputAction ε h (rate h t)).compLp y) ha).trans
      (output_compLp ε h t (A u))))

theorem reference_gauge_pairing (t : ℝ) (u v : V) :
    inner ℂ (R (rate h t) u) (Q t (R (rate h t) v)) =
      inner ℂ (fixedOutputLp (A u)) (fixedOutputLp (A v))+(Real.exp (2*t):ℂ)*
        inner ℂ (kineticOutputLp (A u)) (kineticOutputLp (A v)) := by
  have hp := referenceForm_represents_closed_form ε hε h hne hh m q k t
    (R (rate h t) u) (R (rate h t) v)
  have he := congrArg₂ (fun x y : EnergyOutputSpace => inner ℂ x y)
    (formAction_time_output ε hε h hne hh m q k t u)
    (formAction_time_output ε hε h hne hh m q k t v)
  exact hp.trans (he.trans (gaugeOutputLp_inner ε h t hne (A u) (A v)))

theorem reference_mixed_pairing (t : ℝ) (u v : V) :
    inner ℂ u (Q t (R (rate h t) v)) =
      inner ℂ (fixedOutputLp (A (R (-rate h t) u))) (fixedOutputLp (A v))+(Real.exp (2*t):ℂ)*
        inner ℂ (kineticOutputLp (A (R (-rate h t) u))) (kineticOutputLp (A v)) := by
  have hp := reference_gauge_pairing ε hε h hne hh m q k t (R (-rate h t) u) v
  have hi := formAction_inverse ε hε h hne hh m q k (-rate h t) 0 u
  simp only [neg_neg] at hi
  exact (congrArg (fun z : V => inner ℂ z (Q t (R (rate h t) v))) hi).symm.trans hp

#print axioms output_compLp
#print axioms gaugeOutput_inner
#print axioms gaugeOutputLp_inner
#print axioms formAction_time_output
#print axioms reference_gauge_pairing
#print axioms reference_mixed_pairing
end
end UnifiedTheory.Audit.KFCausalClockFloorGaugePairing
