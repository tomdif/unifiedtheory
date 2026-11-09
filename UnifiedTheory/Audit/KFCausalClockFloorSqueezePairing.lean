/- The exact bounded squeeze commutator on the completed averaged energy
form. Opposite kinetic signs and both matter terms remain in its explicit
output. No positivity or generator-moment estimate is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorReferenceSqueeze
import UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSqueezePairing
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalPairedSqueezeTransport (transport)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeEnergy (degree factorScale outputAction outputAction_apply)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open UnifiedTheory.Audit.KFCausalClockFloorReferenceSqueeze
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity

def difference (a : ℝ) (i : Fin 8) : ℂ :=
  (Real.exp (degree i*a):ℂ)-(Real.exp (-(degree i*a)):ℂ)

def differenceOutput (a : ℝ) : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert where
  toFun g := WithLp.toLp 2 (fun i => difference a i • transport a (g i))
  map_add' f g := by
    apply PiLp.ext
    intro i
    simp only [PiLp.add_apply,map_add,smul_add]
  map_smul' c g := by
    apply PiLp.ext
    intro i
    simp only [PiLp.smul_apply,map_smul,RingHom.id_apply]
    exact smul_comm _ _ _
  cont := (PiLp.continuous_toLp 2 _).comp
    (continuous_pi (fun i => ((transport a).continuous.comp
      (PiLp.continuous_apply 2 _ i)).const_smul (difference a i)))

theorem differenceOutput_apply (a : ℝ) (g : Output (Fin 8) Hilbert) (i : Fin 8) :
    differenceOutput a g i = difference a i • transport a (g i) := rfl

theorem output_difference (a : ℝ) (x : Output (Fin 8) Hilbert) :
    inner ℂ x (outputAction a x)-conj (inner ℂ x (outputAction (-a) x)) =
      inner ℂ x (differenceOutput a x) := by
  rw [inner_conj_symm,PiLp.inner_apply,PiLp.inner_apply,PiLp.inner_apply,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [outputAction_apply,outputAction_apply,differenceOutput_apply,
    inner_smul_right,inner_smul_left,inner_smul_right,transport_dual (-a),neg_neg]
  simp only [factorScale,difference,Complex.conj_ofReal,mul_neg,sub_mul]

def differenceOutputLp (a : ℝ) : EnergyOutputSpace →L[ℂ] EnergyOutputSpace :=
  (differenceOutput a).compLpL 2 angleMeasure

theorem lp_difference (a : ℝ) (x : EnergyOutputSpace) :
    inner ℂ x ((outputAction a).compLp x)-
      conj (inner ℂ x ((outputAction (-a)).compLp x)) =
      inner ℂ x (differenceOutputLp a x) := by
  have he : (fun θ => inner ℂ (x θ) ((outputAction a).compLp x θ)-
      inner ℂ ((outputAction (-a)).compLp x θ) (x θ)) =ᵐ[angleMeasure]
      fun θ => inner ℂ (x θ) (differenceOutputLp a x θ) := by
    filter_upwards [(outputAction a).coeFn_compLp x,(outputAction (-a)).coeFn_compLp x,
      (differenceOutput a).coeFn_compLp x] with θ h1 h2 h3
    change _ = inner ℂ (x θ) ((differenceOutput a).compLp x θ)
    rw [h1,h2,h3,← output_difference,inner_conj_symm]
  rw [inner_conj_symm,L2.inner_def,L2.inner_def,
    ← integral_sub (L2.integrable_inner (𝕜 := ℂ) x ((outputAction a).compLp x))
      (L2.integrable_inner (𝕜 := ℂ) ((outputAction (-a)).compLp x) x),
    integral_congr_ae he,← L2.inner_def]

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)
  (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "R" => (fun a : ℝ => formAction ε hε h hne hh m g k a 0)

def timeOutput (t : ℝ) (u : V) : EnergyOutputSpace :=
  energyOutput ε hε h hne hh m g k t (formTransfer ε hε h hne hh m g k 0 t u)

theorem reference_output_pairing (a t : ℝ) (u v : V) :
    inner ℂ u (Q t (R a v)) = inner ℂ (timeOutput ε hε h hne hh m g k t u)
      ((outputAction a).compLp (timeOutput ε hε h hne hh m g k t v)) := by
  have hp := referenceForm_represents_closed_form ε hε h hne hh m g k t u (R a v)
  have ht := formAction_transfer ε hε h hne hh m g k a 0 t v
  have ho := formAction_output ε hε h hne hh m g k a t
    (formTransfer ε hε h hne hh m g k 0 t v)
  exact hp.trans (congrArg (fun y : EnergyOutputSpace =>
    inner ℂ (timeOutput ε hε h hne hh m g k t u) y)
      ((congrArg (energyOutput ε hε h hne hh m g k t) ht).trans ho))

theorem reference_difference (a t : ℝ) (u : V) :
    inner ℂ u (Q t (R a u))-conj (inner ℂ u (Q t (R (-a) u))) =
      inner ℂ (timeOutput ε hε h hne hh m g k t u)
        (differenceOutputLp a (timeOutput ε hε h hne hh m g k t u)) := by
  exact (congrArg₂ (fun x y : ℂ => x-conj y)
    (reference_output_pairing ε hε h hne hh m g k a t u u)
    (reference_output_pairing ε hε h hne hh m g k (-a) t u u)).trans (lp_difference a _)

#print axioms differenceOutput_apply
#print axioms output_difference
#print axioms lp_difference
#print axioms reference_output_pairing
#print axioms reference_difference

end
end UnifiedTheory.Audit.KFCausalClockFloorSqueezePairing
