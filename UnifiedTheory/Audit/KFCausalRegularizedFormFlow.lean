/- The constructed homogeneous weak solutions give a reversible flow on
the common form domain. Uniqueness removes the choice of cutoff witness,
and comparison at an intermediate time proves composition. These maps
preserve physical distances; complex linearity and extension to all L2
initial data are separate obligations. -/
import UnifiedTheory.Audit.KFCausalRegularizedWeakUniqueness
import UnifiedTheory.Audit.KFCausalRegularizedWeakNormConservation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalRegularizedFormFlow
noncomputable section
open UnifiedTheory.Audit.KFCausalRegularizedFormEmbedding
open UnifiedTheory.Audit.KFCausalRegularizedWeakTrajectory
open UnifiedTheory.Audit.KFCausalRegularizedWeakUniqueness
open UnifiedTheory.Audit.KFCausalRegularizedWeakNormConservation

def formFlow (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ)
    (w : FormSpace ε hε hbar coupling 0) : FormSpace ε hε hbar coupling 0 :=
  (weakTrajectory ε hε hbar coupling s w).formState t

theorem formFlow_initial (ε : ℝ) (hε : 0 < ε) (hbar coupling s : ℝ)
    (w : FormSpace ε hε hbar coupling 0) : formFlow ε hε hbar coupling s s w = w :=
  weak_trajectory_initial ε hε hbar coupling s w _

theorem formFlow_eq_of_witness (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ)
    (w : FormSpace ε hε hbar coupling 0) (V : WeakTrajectory ε hε hbar coupling s w) :
    formFlow ε hε hbar coupling s t w = V.formState t :=
  congrFun (formState_unique ε hε hbar coupling s w (weakTrajectory ε hε hbar coupling s w) V) t

theorem formFlow_compose (ε : ℝ) (hε : 0 < ε) (hbar coupling s r t : ℝ)
    (w : FormSpace ε hε hbar coupling 0) :
    formFlow ε hε hbar coupling r t (formFlow ε hε hbar coupling s r w) =
      formFlow ε hε hbar coupling s t w := by
  apply embedding_injective ε hε hbar coupling 0
  have hh := physical_distance_conserved ε hε hbar coupling r s
    (formFlow ε hε hbar coupling s r w) w
    (weakTrajectory ε hε hbar coupling r (formFlow ε hε hbar coupling s r w))
    (weakTrajectory ε hε hbar coupling s w) r t
  rw [weak_trajectory_initial] at hh
  change ‖embedding ε hε hbar coupling 0 (formFlow ε hε hbar coupling r t (formFlow ε hε hbar coupling s r w))-
    embedding ε hε hbar coupling 0 (formFlow ε hε hbar coupling s t w)‖ =
    ‖embedding ε hε hbar coupling 0 (formFlow ε hε hbar coupling s r w)-
      embedding ε hε hbar coupling 0 (formFlow ε hε hbar coupling s r w)‖ at hh
  rw [sub_self,norm_zero] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp hh)

theorem formFlow_reverse (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ)
    (w : FormSpace ε hε hbar coupling 0) :
    formFlow ε hε hbar coupling t s (formFlow ε hε hbar coupling s t w) = w := by
  rw [formFlow_compose,formFlow_initial]

theorem formFlow_bijective (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ) :
    Function.Bijective (formFlow ε hε hbar coupling s t) := by
  constructor
  · exact Function.LeftInverse.injective (formFlow_reverse ε hε hbar coupling s t)
  · exact Function.RightInverse.surjective (formFlow_reverse ε hε hbar coupling t s)

theorem formFlow_physical_norm (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ)
    (w : FormSpace ε hε hbar coupling 0) :
    ‖embedding ε hε hbar coupling 0 (formFlow ε hε hbar coupling s t w)‖ =
      ‖embedding ε hε hbar coupling 0 w‖ :=
  physical_norm_initial ε hε hbar coupling s w _ t

theorem formFlow_physical_distance (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ)
    (v w : FormSpace ε hε hbar coupling 0) :
    ‖embedding ε hε hbar coupling 0 (formFlow ε hε hbar coupling s t v)-
      embedding ε hε hbar coupling 0 (formFlow ε hε hbar coupling s t w)‖ =
      ‖embedding ε hε hbar coupling 0 v-embedding ε hε hbar coupling 0 w‖ := by
  have hh := physical_distance_conserved ε hε hbar coupling s s v w
    (weakTrajectory ε hε hbar coupling s v) (weakTrajectory ε hε hbar coupling s w) s t
  simpa only [weak_trajectory_initial] using hh

theorem formFlow_physical_continuous (ε : ℝ) (hε : 0 < ε) (hbar coupling s : ℝ)
    (w : FormSpace ε hε hbar coupling 0) :
    Continuous (fun t => embedding ε hε hbar coupling 0 (formFlow ε hε hbar coupling s t w)) :=
  physical_state_continuous ε hε hbar coupling s w _

#print axioms formFlow_initial
#print axioms formFlow_eq_of_witness
#print axioms formFlow_compose
#print axioms formFlow_reverse
#print axioms formFlow_bijective
#print axioms formFlow_physical_norm
#print axioms formFlow_physical_distance
#print axioms formFlow_physical_continuous

end
end UnifiedTheory.Audit.KFCausalRegularizedFormFlow
