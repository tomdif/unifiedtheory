/- Complex linearity of the constructed form-domain evolution. Linear
combinations solve the same weak equation, so uniqueness identifies them
with the constructed flow for the combined initial datum. -/
import UnifiedTheory.Audit.KFCausalRegularizedWeakSolution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalRegularizedFormLinearity
noncomputable section
open UnifiedTheory.Audit.KFCausalRegularizedMomentumClosure
open UnifiedTheory.Audit.KFCausalRegularizedFormEmbedding
open UnifiedTheory.Audit.KFCausalRegularizedWeakTrajectory
open UnifiedTheory.Audit.KFCausalWeakFormSolution
open UnifiedTheory.Audit.KFCausalRegularizedWeakSolution
open UnifiedTheory.Audit.KFCausalRegularizedFormFlow

theorem formFlow_add (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ)
    (v w : FormSpace ε hε hbar coupling 0) :
    formFlow ε hε hbar coupling s t (v+w) =
      formFlow ε hε hbar coupling s t v+formFlow ε hε hbar coupling s t w := by
  let U := weakSolution ε hε hbar coupling s v (weakTrajectory ε hε hbar coupling s v)
  let V := weakSolution ε hε hbar coupling s w (weakTrajectory ε hε hbar coupling s w)
  have hi : (add U V).state s = v+w := by
    change (weakTrajectory ε hε hbar coupling s v).formState s+
      (weakTrajectory ε hε hbar coupling s w).formState s = v+w
    rw [weak_trajectory_initial,weak_trajectory_initial]
  have hh := weakSolution_eq_flow ε hε hbar coupling s (v+w) (add U V) hi
  exact (congrFun hh t).symm

theorem formFlow_smul (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ)
    (c : ℂ) (w : FormSpace ε hε hbar coupling 0) :
    formFlow ε hε hbar coupling s t (c • w) = c • formFlow ε hε hbar coupling s t w := by
  let U := weakSolution ε hε hbar coupling s w (weakTrajectory ε hε hbar coupling s w)
  have hi : (smul c U).state s = c • w := by
    change c • (weakTrajectory ε hε hbar coupling s w).formState s = c • w
    rw [weak_trajectory_initial]
  have hh := weakSolution_eq_flow ε hε hbar coupling s (c • w) (smul c U) hi
  exact (congrFun hh t).symm

def formLinearMap (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ) :
    FormSpace ε hε hbar coupling 0 →ₗ[ℂ] FormSpace ε hε hbar coupling 0 where
  toFun := formFlow ε hε hbar coupling s t
  map_add' := formFlow_add ε hε hbar coupling s t
  map_smul' := formFlow_smul ε hε hbar coupling s t

theorem formLinearMap_physical_norm (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ)
    (w : FormSpace ε hε hbar coupling 0) :
    ‖embedding ε hε hbar coupling 0 (formLinearMap ε hε hbar coupling s t w)‖ =
      ‖embedding ε hε hbar coupling 0 w‖ := formFlow_physical_norm ε hε hbar coupling s t w

#print axioms formFlow_add
#print axioms formFlow_smul
#print axioms formLinearMap
#print axioms formLinearMap_physical_norm

end
end UnifiedTheory.Audit.KFCausalRegularizedFormLinearity
