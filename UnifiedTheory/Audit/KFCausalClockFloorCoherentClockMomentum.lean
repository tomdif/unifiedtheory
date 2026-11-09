/- The actual enlarged physical family belongs to the clock-half domain
and every ordered transverse momentum domain. Derivative outputs are
constructed from square-integrable physical sourced Gaussians. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoherentDerivative
import UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoherentClockMomentum
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block Joint)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSources
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCoordinates (displacement spectatorParameter)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary
open UnifiedTheory.Audit.KFCausalClockFloorCoherentDerivative
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (clockHalf halfWeight)
open UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalTransverseTrialDerivative (derivative)
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum (transverseMomentum)
open UnifiedTheory.Audit.KFCausalTransverseMomentumDerivative (derivative_momentum_graph)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition

theorem sourceProfile_eq (α β : ℝ) (g : ℝ → ℂ) (v : Block 2) (r : Block 4) :
    configurationProfile α β g v r = physicalProfile (constant α v) (frequency r) α β (coefficients α v r) g := by
  funext x
  unfold configurationProfile KFCausalChargeGaussianIdentities.configurationProfile
    physicalProfile clockMultiplier KFCausalClockFloorCoherentMoments.sourcedPacket
  ring

theorem state_clockHalf_domain (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) :
    KFCausalClockFloorCoherentStates.state ε a hbar hε ha hh k ∈ (clockHalf ε).domain := by
  apply (clockHalf_domain ε _).mpr
  have hm := physicalProfile_memLp (amplitudeConstant hbar k) (clockFrequency k)
    (groundWidth hbar) (neutralWidth hbar) (groundWidth_positive hbar hh)
    (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) (sourceCoefficients hbar k)
    (halfClockFunction ε a) (halfClockFunction_memLp ε a hε ha)
  apply hm.ae_eq
  filter_upwards [state_configuration_coe ε a hbar hε ha hh k] with x hx
  rw [hx,sourceProfile_eq]
  simp only [physicalProfile,clockMultiplier,halfClockFunction,halfWeight,
    amplitudeConstant,clockFrequency,sourceCoefficients]
  ring

theorem dampedProfile_eq (ε a α β : ℝ) (v : Block 2) (r : Block 4) :
    dampedProfile ε a α β v r = physicalProfile (constant α v) (frequency r) α β (coefficients α v r)
      (dampedClockFunction ε a) := by
  funext x
  simp only [dampedProfile,sourceProfile_eq,physicalProfile,clockMultiplier,dampedClockFunction]
  ring

theorem dampedProfile_memLp (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) :
    MemLp (dampedProfile ε a (groundWidth hbar) (neutralWidth hbar)
      (displacement hbar k) (spectatorParameter k)) 2 volume := by
  rw [dampedProfile_eq]
  exact physicalProfile_memLp _ _ _ _ (groundWidth_positive hbar hh)
    (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) _ _ (dampedClockFunction_memLp ε a hε ha)

theorem dampedProfile_derivative_memLp (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (k : Joint 2 4) (v : Transverse) :
    MemLp (derivative v (dampedProfile ε a (groundWidth hbar) (neutralWidth hbar)
      (displacement hbar k) (spectatorParameter k))) 2 volume := by
  rw [dampedProfile_eq]
  exact physicalProfile_derivative_memLp _ _ _ _ (groundWidth_positive hbar hh)
    (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) _ _ (dampedClockFunction_memLp ε a hε ha) v

theorem dampedState_eq_toLp (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) :
    dampedState ε a hbar hε ha hh k = (dampedProfile_memLp ε a hbar hε ha hh k).toLp
      (dampedProfile ε a (groundWidth hbar) (neutralWidth hbar) (displacement hbar k) (spectatorParameter k)) := by
  apply Lp.ext
  exact (dampedState_coe ε a hbar hε ha hh k).trans (dampedProfile_memLp ε a hbar hε ha hh k).coeFn_toLp.symm

def momentumOutput (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) (v : Transverse) : Hilbert :=
  (-Complex.I*(hbar:ℂ)) • (dampedProfile_derivative_memLp ε a hbar hε ha hh k v).toLp
    (derivative v (dampedProfile ε a (groundWidth hbar) (neutralWidth hbar)
      (displacement hbar k) (spectatorParameter k)))

theorem dampedState_momentum_graph (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (k : Joint 2 4) (v : Transverse) :
    (dampedState ε a hbar hε ha hh k,momentumOutput ε a hbar hε ha hh k v) ∈
      (transverseMomentum hbar v).graph := by
  rw [dampedState_eq_toLp]
  apply derivative_momentum_graph
  rw [dampedProfile_eq]
  exact physicalProfile_transverse_differentiable _ _ _ _ _ _

theorem dampedState_momentum_domain (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (k : Joint 2 4) (v : Transverse) :
    dampedState ε a hbar hε ha hh k ∈ (transverseMomentum hbar v).domain :=
  LinearPMap.mem_domain_of_mem_graph (dampedState_momentum_graph ε a hbar hε ha hh k v)

theorem state_clockMomentum_graph (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (k : Joint 2 4) (v : Transverse) :
    (KFCausalClockFloorCoherentStates.state ε a hbar hε ha hh k,momentumOutput ε a hbar hε ha hh k v) ∈
      (clockMomentum ε hbar v).graph := by
  apply (composition_graph _ _ _ _).mpr
  exact ⟨_,dampedState_graph ε a hbar hε ha hh k,dampedState_momentum_graph ε a hbar hε ha hh k v⟩

theorem state_clockMomentum_domain (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (k : Joint 2 4) (v : Transverse) :
    KFCausalClockFloorCoherentStates.state ε a hbar hε ha hh k ∈ (clockMomentum ε hbar v).domain :=
  LinearPMap.mem_domain_of_mem_graph (state_clockMomentum_graph ε a hbar hε ha hh k v)

#print axioms sourceProfile_eq
#print axioms state_clockHalf_domain
#print axioms dampedProfile_eq
#print axioms dampedProfile_memLp
#print axioms dampedProfile_derivative_memLp
#print axioms dampedState_eq_toLp
#print axioms dampedState_momentum_graph
#print axioms dampedState_momentum_domain
#print axioms state_clockMomentum_graph
#print axioms state_clockMomentum_domain

end
end UnifiedTheory.Audit.KFCausalClockFloorCoherentClockMomentum
