/- Exact bounded chart-phase commutators on the full completed energy
form. All eight factors are retained. Only the three ordered factors
contribute to this observable; no pure-momentum/shear cancellation is used. -/
import UnifiedTheory.Audit.KFCausalClockFloorGaugePairing
import UnifiedTheory.Audit.KFCausalNeutralEhrenfest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorChartPhasePairing
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalFiniteOutputRescaling (selected selected_apply)
open UnifiedTheory.Audit.KFCausalClockFloorChartModulation (modulation modulation_inverse)
open UnifiedTheory.Audit.KFCausalClockFloorClosedChartModulation (outputAction outputAction_apply)
open UnifiedTheory.Audit.KFCausalClockFloorFactorChartModulation (factorScale)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorGaugeEnergy (EnergyOutputSpace)
open UnifiedTheory.Audit.KFCausalClockFloorReferenceChartModulation
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity

def orderedOutput : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert :=
  selected (fun i : Fin 8 => ¬ i.val < 5)

def orderedOutputLp : EnergyOutputSpace →L[ℂ] EnergyOutputSpace :=
  orderedOutput.compLpL 2 angleMeasure

def phaseOutput (ε r : ℝ) : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert :=
  outputAction ε 0 r

def phaseOutputLp (ε r : ℝ) : EnergyOutputSpace →L[ℂ] EnergyOutputSpace :=
  (phaseOutput ε r).compLpL 2 angleMeasure

def difference (h r : ℝ) : ℝ := Real.exp (Real.pi*h*r)-Real.exp (-(Real.pi*h*r))

theorem modulation_dual (ε r : ℝ) (f g : Hilbert) :
    inner ℂ (modulation ε r f) g = inner ℂ f (modulation ε (-r) g) := by
  have he := (modulation ε r).inner_map_map f (modulation ε (-r) g)
  have hi := modulation_inverse ε (-r) g
  simp only [neg_neg] at hi
  rwa [hi] at he

theorem phaseOutput_apply (ε r : ℝ) (x : Output (Fin 8) Hilbert) (i : Fin 8) :
    phaseOutput ε r x i = modulation ε r (x i) := by
  simp only [phaseOutput,outputAction_apply,factorScale,mul_zero,zero_mul,Real.exp_zero,
    Complex.ofReal_one,ite_self,one_smul]

theorem output_difference (ε h r : ℝ) (x : Output (Fin 8) Hilbert) :
    inner ℂ x (outputAction ε h r x)-conj (inner ℂ x (outputAction ε h (-r) x)) =
      (difference h r:ℂ)*inner ℂ (orderedOutput x) (phaseOutput ε r (orderedOutput x)) := by
  rw [inner_conj_symm,PiLp.inner_apply,PiLp.inner_apply,PiLp.inner_apply,
    ← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [outputAction_apply,outputAction_apply,inner_smul_right,inner_smul_left,
    modulation_dual ε (-r),neg_neg,phaseOutput_apply,orderedOutput,selected_apply]
  by_cases hi : i.val < 5
  · simp only [factorScale,hi,if_true,not_true_eq_false,if_false,map_zero,
      inner_zero_left,mul_zero,map_one,one_mul,sub_self]
  · simp only [factorScale,hi,if_false,not_false_eq_true,if_true,Complex.conj_ofReal]
    rw [show Real.pi*h*(-r) = -(Real.pi*h*r) by ring]
    simp only [difference,Complex.ofReal_sub,sub_mul]

theorem lp_difference (ε h r : ℝ) (x : EnergyOutputSpace) :
    inner ℂ x ((outputAction ε h r).compLp x)-
      conj (inner ℂ x ((outputAction ε h (-r)).compLp x)) =
      (difference h r:ℂ)*inner ℂ (orderedOutputLp x) (phaseOutputLp ε r (orderedOutputLp x)) := by
  have he : (fun θ => inner ℂ (x θ) ((outputAction ε h r).compLp x θ)-
      inner ℂ ((outputAction ε h (-r)).compLp x θ) (x θ)) =ᵐ[angleMeasure]
      fun θ => (difference h r:ℂ)*inner ℂ (orderedOutputLp x θ)
        (phaseOutputLp ε r (orderedOutputLp x) θ) := by
    filter_upwards [(outputAction ε h r).coeFn_compLp x,(outputAction ε h (-r)).coeFn_compLp x,
      orderedOutput.coeFn_compLp x,(phaseOutput ε r).coeFn_compLp (orderedOutputLp x)]
      with θ h1 h2 h3 h4
    change inner ℂ (x θ) ((outputAction ε h r).compLp x θ)-
      inner ℂ ((outputAction ε h (-r)).compLp x θ) (x θ) =
      (difference h r:ℂ)*inner ℂ (orderedOutput.compLp x θ)
        ((phaseOutput ε r).compLp (orderedOutputLp x) θ)
    rw [h1,h2,h3,h4]
    change _ = (difference h r:ℂ)*inner ℂ (orderedOutput (x θ))
      (phaseOutput ε r (orderedOutput.compLp x θ))
    rw [h3,← output_difference,inner_conj_symm]
  rw [inner_conj_symm,L2.inner_def,L2.inner_def,
    ← integral_sub (L2.integrable_inner (𝕜 := ℂ) x ((outputAction ε h r).compLp x))
      (L2.integrable_inner (𝕜 := ℂ) ((outputAction ε h (-r)).compLp x) x),
    integral_congr_ae he,integral_const_mul,← L2.inner_def]

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)
  (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "R" => (fun r : ℝ => formAction ε hε h hne hh m g k r 0)

def timeOutput (t : ℝ) (u : V) : EnergyOutputSpace :=
  energyOutput ε hε h hne hh m g k t (formTransfer ε hε h hne hh m g k 0 t u)

theorem reference_output_pairing (r t : ℝ) (u v : V) :
    inner ℂ u (Q t (R r v)) = inner ℂ (timeOutput ε hε h hne hh m g k t u)
      ((outputAction ε h r).compLp (timeOutput ε hε h hne hh m g k t v)) := by
  have hp := referenceForm_represents_closed_form ε hε h hne hh m g k t u (R r v)
  have ht := formAction_transfer ε hε h hne hh m g k r 0 t v
  have ho := formAction_output ε hε h hne hh m g k r t
    (formTransfer ε hε h hne hh m g k 0 t v)
  exact hp.trans (congrArg (fun y : EnergyOutputSpace =>
    inner ℂ (timeOutput ε hε h hne hh m g k t u) y)
      ((congrArg (energyOutput ε hε h hne hh m g k t) ht).trans ho))

theorem reference_difference (r t : ℝ) (u : V) :
    inner ℂ u (Q t (R r u))-conj (inner ℂ u (Q t (R (-r) u))) =
      (difference h r:ℂ)*inner ℂ (orderedOutputLp (timeOutput ε hε h hne hh m g k t u))
        (phaseOutputLp ε r (orderedOutputLp (timeOutput ε hε h hne hh m g k t u))) := by
  exact (congrArg₂ (fun x y : ℂ => x-conj y)
    (reference_output_pairing ε hε h hne hh m g k r t u u)
    (reference_output_pairing ε hε h hne hh m g k (-r) t u u)).trans (lp_difference ε h r _)

#print axioms modulation_dual
#print axioms phaseOutput_apply
#print axioms output_difference
#print axioms lp_difference
#print axioms reference_output_pairing
#print axioms reference_difference
end
end UnifiedTheory.Audit.KFCausalClockFloorChartPhasePairing
