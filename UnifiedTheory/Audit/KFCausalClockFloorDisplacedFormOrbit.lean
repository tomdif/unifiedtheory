/- Continuous graph-form lifts of the enlarged charge orbits. Every
factor output is identified with the actual operator before its bounded
source-curve estimate is used to prove integrability around the circle. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedCommonDomain
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedParameterBounds
import UnifiedTheory.Audit.KFCausalClockFloorSourcedFieldContinuity
import UnifiedTheory.Audit.KFCausalClockFloorCoherentGradientContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedFormOrbit
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedStates (state orbit_continuous action_state)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedParameterBounds
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedBoostOrbit (parameter_clock)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (physicalProfile_curve_continuous continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentGradientContinuity (derivative_curve_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy
  (halfClockFunction halfClockFunction_memLp dampedClockFunction dampedClockFunction_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
  (neutralWidth neutralWidth_positive neutralWidth_bound trialState)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy (factorValue jointOutput)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (q k : Joint 2 4)

theorem factorOutput_orbit_continuous (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) :
    Continuous (fun θ => factorOutput ε a h hε ha hh hb (parameter θ q) (parameter θ k) v l i) := by
  obtain ⟨B,hB⟩ := source_orbit_bound h q k
  let C := fun θ => amplitude h (parameter θ q) (parameter θ k)
  let p := fun θ => clockFrequency h (parameter θ k)
  let b := fun θ => source h (parameter θ q) (parameter θ k)
  have hCc : Continuous C := amplitude_curve_continuous h q k
  have hpc : Continuous p := (clockFrequency_continuous h).comp (parameter_curve_continuous k)
  have hbc : Continuous b := source_curve_continuous h q k
  have hC : ∀ θ, ‖C θ‖ ≤ 1 := fun θ => amplitude_norm_le_one h hh _ _
  have hp : ∀ θ, |p θ| ≤ |clockFrequency h k| := by
    intro θ
    dsimp only [p]
    rw [clockFrequency_parameter]
  have hc := physicalProfile_curve_continuous (groundWidth h) (neutralWidth h) B
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
    C p b (halfClockFunction ε a) (halfClockFunction_memLp ε a hε ha) hCc hpc hbc hC hB
  have hm (u : Transverse) := (continuous_const (y := -Complex.I*(h:ℂ))).smul
    (derivative_curve_continuous (groundWidth h) (neutralWidth h) B
      (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
      C p b (dampedClockFunction ε a) (dampedClockFunction_memLp ε a hε ha) hCc hpc hbc hC hB u)
  have hs := KFCausalClockFloorSourcedFieldContinuity.outputs_curve_continuous ε a h hε ha hh hb
    |clockFrequency h k| B C p b hCc hpc hbc hC hp hB
  fin_cases i
  · exact continuous_const.smul hc
  · exact continuous_const.smul (hm (v 0))
  · exact continuous_const.smul (hm (v 1))
  · exact continuous_const.smul (hm (v 2))
  · exact continuous_const.smul (hm (v 3))
  · exact continuous_const.smul (hs.2.1 l)
  · exact continuous_const.smul (hs.2.2 l)
  · exact continuous_const.smul hs.1

variable (hq : q (.inr 0) = 0)
include hq

theorem factorValue_eq (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) :
    factorValue ε hε h v l
      ⟨state ε a h hε ha hh q k,state_commonEnergyDomain ε a h hε ha hh hb q k hq v l⟩ i =
        factorOutput ε a h hε ha hh hb q k v l i :=
  (energyFactor ε hε h v l i).mem_graph_snd_inj' ((energyFactor ε hε h v l i).mem_graph _)
    (factorOutput_graph ε a h hε ha hh hb q k hq v l i) rfl

theorem jointOutput_eq (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (m g κ t : ℝ) :
    jointOutput ε hε h v l m g κ t
      ⟨state ε a h hε ha hh q k,state_commonEnergyDomain ε a h hε ha hh hb q k hq v l⟩ =
        WithLp.toLp 2 (fun i => energyWeight m g κ t i • factorOutput ε a h hε ha hh hb q k v l i) := by
  apply PiLp.ext
  intro i
  exact congrArg (fun f => energyWeight m g κ t i • f) (factorValue_eq ε a h hε ha hh hb q k hq v l i)

theorem jointOutput_orbit_continuous (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (m g κ t : ℝ) :
    Continuous (fun θ => jointOutput ε hε h v l m g κ t
      ⟨state ε a h hε ha hh (parameter θ q) (parameter θ k),
        state_commonEnergyDomain ε a h hε ha hh hb (parameter θ q) (parameter θ k)
          ((parameter_clock θ q).trans hq) v l⟩) := by
  have he := funext (fun θ => jointOutput_eq ε a h hε ha hh hb (parameter θ q) (parameter θ k)
    ((parameter_clock θ q).trans hq) v l m g κ t)
  rw [he]
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 8 => Hilbert)).comp
  exact continuous_pi (fun i => continuous_const.smul (factorOutput_orbit_continuous ε a h hε ha hh hb q k v l i))

theorem formVector_orbit_continuous (m g κ t : ℝ) :
    Continuous (fun θ => formVector ε a h hε ha hh hb (parameter θ q) (parameter θ k)
      ((parameter_clock θ q).trans hq) m g κ t) := by
  apply Continuous.subtype_mk
  exact (WithLp.prod_continuous_toLp 2 Hilbert (Output (Fin 8) Hilbert)).comp
    ((orbit_continuous ε a h hε ha hh q k).prodMk
      (jointOutput_orbit_continuous ε a h hε ha hh hb q k hq modelDirections pointField m g κ t))

theorem formVector_orbit_memLp (m g κ t : ℝ) :
    MemLp (fun θ => formVector ε a h hε ha hh hb (parameter (2*Real.pi*θ) q) (parameter (2*Real.pi*θ) k)
      ((parameter_clock (2*Real.pi*θ) q).trans hq) m g κ t) 2 KFCausalUnitIntervalOrbit.angleMeasure :=
  continuous_angle_memLp _ ((formVector_orbit_continuous ε a h hε ha hh hb q k hq m g κ t).comp
    (continuous_const.mul continuous_id))

#print axioms factorOutput_orbit_continuous
#print axioms factorValue_eq
#print axioms jointOutput_eq
#print axioms jointOutput_orbit_continuous
#print axioms formVector_orbit_continuous
#print axioms formVector_orbit_memLp

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedFormOrbit
