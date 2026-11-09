/- Every transverse maximal momentum acts on the actual inverse-clock
dressed invariant trial. The ordered P_v D factor has its natural
composition domain and a derived, explicit derivative output. -/
import UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy
import UnifiedTheory.Audit.KFCausalPhysicalGaussianDerivative
import UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum
noncomputable section
open MeasureTheory Filter
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalChargeGaussianIdentities
open UnifiedTheory.Audit.KFCausalPhysicalGaussianCharge
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorTrialUnitary
open UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy
open UnifiedTheory.Audit.KFCausalPhysicalGaussianDerivative
open UnifiedTheory.Audit.KFCausalTransverseTrialDerivative (derivative)
open UnifiedTheory.Audit.KFCausalTransverseMomentumDerivative
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition

theorem dampedProfile_eq (ε a hbar : ℝ) : dampedProfile ε a hbar =
    configurationProfile (groundWidth hbar) (neutralWidth hbar) (dampedClockFunction ε a) := by
  funext x
  simp only [dampedProfile,configurationProfile,dampedClockFunction,mul_assoc]

theorem dampedProfile_memLp (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    MemLp (dampedProfile ε a hbar) 2 volume := by
  rw [dampedProfile_eq]
  exact configurationProfile_memLp _ _ (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh)
    _ (dampedClockFunction_continuous ε a hε) (dampedClockFunction_memLp ε a hε ha)

theorem dampedProfile_derivative_memLp (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (v : Transverse) : MemLp (derivative v (dampedProfile ε a hbar)) 2 volume := by
  rw [dampedProfile_eq]
  exact configurationProfile_derivative_memLp _ _ (groundWidth_positive hbar hh)
    (neutralWidth_positive hbar hh) _ (dampedClockFunction_memLp ε a hε ha) v

theorem dampedState_eq_toLp (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    dampedState ε a hbar hε ha hh =
      (dampedProfile_memLp ε a hbar hε ha hh).toLp (dampedProfile ε a hbar) := by
  apply Lp.ext
  exact (dampedState_coe ε a hbar hε ha hh).trans (dampedProfile_memLp ε a hbar hε ha hh).coeFn_toLp.symm

theorem dampedState_momentum_graph (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (v : Transverse) :
    (dampedState ε a hbar hε ha hh,(-Complex.I*(hbar:ℂ)) •
      (dampedProfile_derivative_memLp ε a hbar hε ha hh v).toLp (derivative v (dampedProfile ε a hbar))) ∈
        (transverseMomentum hbar v).graph := by
  rw [dampedState_eq_toLp]
  apply derivative_momentum_graph
  rw [dampedProfile_eq]
  exact configurationProfile_transverse_differentiable _ _ _

theorem dampedState_momentum_domain (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (v : Transverse) :
    dampedState ε a hbar hε ha hh ∈ (transverseMomentum hbar v).domain :=
  LinearPMap.mem_domain_of_mem_graph (dampedState_momentum_graph ε a hbar hε ha hh v)

def clockMomentum (ε hbar : ℝ) (v : Transverse) : Hilbert →ₗ.[ℂ] Hilbert :=
  composition (transverseMomentum hbar v) (inverseClockHalf ε)

theorem trialState_clockMomentum_domain (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (v : Transverse) :
    trialState ε a hbar hε ha hh ∈ (clockMomentum ε hbar v).domain := by
  apply (composition_domain _ _ _).mpr
  exact ⟨_,dampedState_graph ε a hbar hε ha hh,dampedState_momentum_domain ε a hbar hε ha hh v⟩

theorem trialState_clockMomentum_graph (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (v : Transverse) :
    (trialState ε a hbar hε ha hh,(-Complex.I*(hbar:ℂ)) •
      (dampedProfile_derivative_memLp ε a hbar hε ha hh v).toLp (derivative v (dampedProfile ε a hbar))) ∈
        (clockMomentum ε hbar v).graph := by
  apply (composition_graph _ _ _ _).mpr
  exact ⟨_,dampedState_graph ε a hbar hε ha hh,dampedState_momentum_graph ε a hbar hε ha hh v⟩

#print axioms dampedProfile_eq
#print axioms dampedProfile_memLp
#print axioms dampedProfile_derivative_memLp
#print axioms dampedState_eq_toLp
#print axioms dampedState_momentum_graph
#print axioms dampedState_momentum_domain
#print axioms trialState_clockMomentum_domain
#print axioms trialState_clockMomentum_graph

end
end UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum
