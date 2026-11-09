/- The enlarged normalized family, with zero clock displacement, lies in
all eight actual energy-factor domains. This applies to the entire charge
orbit of every canonical momentum boost. Averaged form lifts still require
integrability in the charge parameter. -/
import UnifiedTheory.Audit.KFCausalClockFloorSourcedCommonDomain
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources
import UnifiedTheory.Audit.KFCausalClockFloorFormHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedCommonDomain
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedStates
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedBoostOrbit
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound trialState)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorFormHamiltonian
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalDisplacedBoostParameters (boostQ)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit (boostedState)
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (positionFrequency)

theorem rawState_eq_sourced (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (q k : Joint 2 4) (hq : q (.inr 0) = 0) :
    rawState ε a h hε ha hh q k =
      KFCausalClockFloorSourcedClockMomentum.state ε a (groundWidth h) (neutralWidth h)
        hε ha (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
        (amplitude h q k) (clockFrequency h k) (source h q k) := by
  apply Lp.ext
  exact (rawState_configuration_coe ε a h hε ha hh q k hq).trans
    (KFCausalClockFloorSourcedClockMomentum.state_coe _ _ _ _ _ _ _ _ _ _ _ _).symm

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (q k : Joint 2 4) (hq : q (.inr 0) = 0)
include hb hq

theorem rawState_commonEnergyDomain (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    rawState ε a h hε ha hh q k ∈ commonEnergyDomain ε hε h v l := by
  rw [rawState_eq_sourced ε a h hε ha hh q k hq]
  exact KFCausalClockFloorSourcedCommonDomain.state_commonEnergyDomain _ _ _ _ _ _ _ _ _ _ _ _ h hb v l

theorem state_commonEnergyDomain (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    state ε a h hε ha hh q k ∈ commonEnergyDomain ε hε h v l := by
  rw [state_normalization]
  exact ((commonEnergyDomain ε hε h v l).restrictScalars ℝ).smul_mem _
    (rawState_commonEnergyDomain ε a h hε ha hh hb q k hq v l)

theorem action_state_commonEnergyDomain (θ : ℝ) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    KFCausalPhysicalCircleAction.action h hh θ (state ε a h hε ha hh q k) ∈
      commonEnergyDomain ε hε h v l := by
  rw [action_state]
  exact state_commonEnergyDomain ε a h hε ha hh hb (parameter θ q) (parameter θ k)
    ((parameter_clock θ q).trans hq) v l

omit q k hq in
theorem action_boostedState_commonEnergyDomain (p : Configuration) (θ : ℝ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    KFCausalPhysicalCircleAction.action h hh θ (boostedState ε a h hε ha hh (positionFrequency p.1 p.2)) ∈
      commonEnergyDomain ε hε h v l := by
  rw [action_boostedState]
  exact state_commonEnergyDomain ε a h hε ha hh hb _ _ (boost_orbit_clock_displacement h p θ) v l

def factorOutput (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) : Hilbert :=
  (‖trialState ε a h hε ha hh‖⁻¹ : ℝ) •
    KFCausalClockFloorSourcedCommonDomain.factorOutput ε a (groundWidth h) (neutralWidth h)
      hε ha (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
      (amplitude h q k) (clockFrequency h k) (source h q k) h hb v l i

theorem factorOutput_graph (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) :
    (state ε a h hε ha hh q k,factorOutput ε a h hε ha hh hb q k v l i) ∈
      (energyFactor ε hε h v l i).graph := by
  rw [state_normalization,rawState_eq_sourced ε a h hε ha hh q k hq]
  exact ((energyFactor ε hε h v l i).graph.restrictScalars ℝ).smul_mem
    (‖trialState ε a h hε ha hh‖⁻¹ : ℝ)
    (KFCausalClockFloorSourcedCommonDomain.factorOutput_graph _ _ _ _ _ _ _ _ _ _ _ _ h hb v l i)

def formVector (m g κ t : ℝ) :
    KFCausalClosedGraphForm.FormSpace (formData ε hε h (hamiltonian_bound ε h hb) m g κ t) :=
  commonFormVector ε hε h (hamiltonian_bound ε h hb) m g κ t
    ⟨state ε a h hε ha hh q k,state_commonEnergyDomain ε a h hε ha hh hb q k hq modelDirections pointField⟩

theorem formVector_embedding (m g κ t : ℝ) :
    KFCausalClosedGraphForm.embedding _ (formVector ε a h hε ha hh hb q k hq m g κ t) =
      state ε a h hε ha hh q k := rfl

theorem formVector_norm (m g κ t : ℝ) :
    ‖KFCausalClosedGraphForm.embedding _ (formVector ε a h hε ha hh hb q k hq m g κ t)‖ = 1 :=
  state_norm ε a h hε ha hh q k

theorem formVector_energy (m g κ t : ℝ) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ) :
    ‖KFCausalClosedGraphForm.energyOutput _ (formVector ε a h hε ha hh hb q k hq m g κ t)‖^2 =
      KFCausalClockFloorJointEnergy.seedEnergy ε hε h modelDirections pointField m g κ t
        ⟨state ε a h hε ha hh q k,state_commonEnergyDomain ε a h hε ha hh hb q k hq modelDirections pointField⟩ :=
  commonFormVector_energy ε hε h (hamiltonian_bound ε h hb) m g κ t hm hg hκ _

#print axioms rawState_eq_sourced
#print axioms rawState_commonEnergyDomain
#print axioms state_commonEnergyDomain
#print axioms action_state_commonEnergyDomain
#print axioms action_boostedState_commonEnergyDomain
#print axioms factorOutput_graph
#print axioms formVector_embedding
#print axioms formVector_norm
#print axioms formVector_energy

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedCommonDomain
