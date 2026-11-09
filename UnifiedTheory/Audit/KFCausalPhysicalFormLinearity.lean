/- Complex linearity of the constructed form-domain evolution. Linear
combinations solve the same weak equation, so uniqueness identifies them
with the constructed flow for the combined initial datum. -/
import UnifiedTheory.Audit.KFCausalPhysicalWeakSolution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalPhysicalFormLinearity
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalPhysicalFormTransport
open UnifiedTheory.Audit.KFCausalPhysicalFormGeometry
open UnifiedTheory.Audit.KFCausalPhysicalWeakTrajectory
open UnifiedTheory.Audit.KFCausalWeakFormSolution
open UnifiedTheory.Audit.KFCausalPhysicalWeakSolution
open UnifiedTheory.Audit.KFCausalPhysicalFormFlow

theorem formFlow_add (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s t : ℝ)
    (v w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    formFlow ε hε hbar hh mass2 quartic vacuum s t (v+w) =
      formFlow ε hε hbar hh mass2 quartic vacuum s t v+formFlow ε hε hbar hh mass2 quartic vacuum s t w := by
  let U := weakSolution ε hε hbar hh mass2 quartic vacuum s v (weakTrajectory ε hε hbar hh mass2 quartic vacuum s v)
  let V := weakSolution ε hε hbar hh mass2 quartic vacuum s w (weakTrajectory ε hε hbar hh mass2 quartic vacuum s w)
  have hi : (add U V).state s = v+w := by
    change (weakTrajectory ε hε hbar hh mass2 quartic vacuum s v).formState s+
      (weakTrajectory ε hε hbar hh mass2 quartic vacuum s w).formState s = v+w
    rw [weak_trajectory_initial,weak_trajectory_initial]
  have hpair := weakSolution_eq_flow ε hε hbar hh mass2 quartic vacuum s (v+w) (add U V) hi
  exact (congrFun hpair t).symm

theorem formFlow_smul (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s t : ℝ)
    (c : ℂ) (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    formFlow ε hε hbar hh mass2 quartic vacuum s t (c • w) = c • formFlow ε hε hbar hh mass2 quartic vacuum s t w := by
  let U := weakSolution ε hε hbar hh mass2 quartic vacuum s w (weakTrajectory ε hε hbar hh mass2 quartic vacuum s w)
  have hi : (smul c U).state s = c • w := by
    change c • (weakTrajectory ε hε hbar hh mass2 quartic vacuum s w).formState s = c • w
    rw [weak_trajectory_initial]
  have hpair := weakSolution_eq_flow ε hε hbar hh mass2 quartic vacuum s (c • w) (smul c U) hi
  exact (congrFun hpair t).symm

def formLinearMap (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s t : ℝ) :
    FormSpace ε hε hbar hh mass2 quartic vacuum 0 →ₗ[ℂ] FormSpace ε hε hbar hh mass2 quartic vacuum 0 where
  toFun := formFlow ε hε hbar hh mass2 quartic vacuum s t
  map_add' := formFlow_add ε hε hbar hh mass2 quartic vacuum s t
  map_smul' := formFlow_smul ε hε hbar hh mass2 quartic vacuum s t

theorem formLinearMap_physical_norm (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s t : ℝ)
    (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    ‖embedding ε hε hbar hh mass2 quartic vacuum 0 (formLinearMap ε hε hbar hh mass2 quartic vacuum s t w)‖ =
      ‖embedding ε hε hbar hh mass2 quartic vacuum 0 w‖ := formFlow_physical_norm ε hε hbar hh mass2 quartic vacuum s t w

#print axioms formFlow_add
#print axioms formFlow_smul
#print axioms formLinearMap
#print axioms formLinearMap_physical_norm

end
end UnifiedTheory.Audit.KFCausalPhysicalFormLinearity
