/- Integrability of the ordered spatial marginals used by the neutral
Fourier response bridge. The order is Y, u, v, then the neutral variable. -/
import UnifiedTheory.Audit.KFCausalJointNeutralFourierIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

namespace UnifiedTheory.Audit.KFCausalJointNeutralFourierOuterFubini
noncomputable section
open MeasureTheory
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalJointNeutralFourierIntegral (integral_finTwo)

theorem finTwo_marginal_integrable (f : (Fin 2 → ℝ) → ℝ) (hf : Integrable f) :
    Integrable (fun v : ℝ => ∫ x : ℝ, f ![v,x]) := by
  let e : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ) := MeasurableEquiv.finTwoArrow
  have hp : MeasurePreserving e.symm volume volume := (volume_preserving_finTwoArrow ℝ).symm
  have hi := hp.integrable_comp_of_integrable hf
  rw [Measure.volume_eq_prod ℝ ℝ] at hi
  exact hi.integral_prod_left

theorem plane_marginal_integrable (f : (ℝ × (Fin 2 → ℝ)) → ℝ) (hf : Integrable f) :
    Integrable (fun u : ℝ => ∫ v : ℝ, ∫ x : ℝ, f (u,![v,x])) ∧
      ∀ᵐ u : ℝ, Integrable (fun v : ℝ => ∫ x : ℝ, f (u,![v,x])) := by
  rw [Measure.volume_eq_prod ℝ (Fin 2 → ℝ)] at hf
  constructor
  · apply hf.integral_prod_left.congr
    filter_upwards [hf.prod_right_ae] with u hu
    exact integral_finTwo _ hu
  · filter_upwards [hf.prod_right_ae] with u hu
    exact finTwo_marginal_integrable _ hu

theorem joint_marginals_integrable (f : Joint → ℝ) (hf : Integrable f jointMeasure) :
    Integrable (fun Y : ℝ => ∫ u : ℝ, ∫ v : ℝ, ∫ x : ℝ, f ((u,![v,x]),Y))
        (volume.restrict (Set.Ioi (0:ℝ))) ∧
    (∀ᵐ Y : ℝ ∂volume.restrict (Set.Ioi (0:ℝ)),
      Integrable (fun u : ℝ => ∫ v : ℝ, ∫ x : ℝ, f ((u,![v,x]),Y))) ∧
    (∀ᵐ Y : ℝ ∂volume.restrict (Set.Ioi (0:ℝ)),
      ∀ᵐ u : ℝ, Integrable (fun v : ℝ => ∫ x : ℝ, f ((u,![v,x]),Y))) := by
  unfold jointMeasure at hf
  refine ⟨?_, ?_, ?_⟩
  · apply hf.integral_prod_right.congr
    filter_upwards [hf.prod_left_ae] with Y hY
    rw [Measure.volume_eq_prod ℝ (Fin 2 → ℝ)] at hY ⊢
    rw [integral_prod _ hY]
    apply integral_congr_ae
    filter_upwards [hY.prod_right_ae] with u hu
    exact integral_finTwo _ hu
  · filter_upwards [hf.prod_left_ae] with Y hY
    exact (plane_marginal_integrable _ hY).1
  · filter_upwards [hf.prod_left_ae] with Y hY
    exact (plane_marginal_integrable _ hY).2

#print axioms finTwo_marginal_integrable
#print axioms plane_marginal_integrable
#print axioms joint_marginals_integrable
end
end UnifiedTheory.Audit.KFCausalJointNeutralFourierOuterFubini
