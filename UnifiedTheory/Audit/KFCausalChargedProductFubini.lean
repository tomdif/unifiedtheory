/- Reconstruct full charged integrability from the ordered nonnegative
marginals. This permits a justified interchange with the neutral
Fourier integral once its actual marginal bounds have been derived. -/
import UnifiedTheory.Audit.KFCausalJointFourierMomentMatrix
import UnifiedTheory.Audit.KFCausalJointNeutralFourierOuterFubini

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalChargedProductFubini
noncomputable section
open MeasureTheory
open KFCausalChargedFourierGaussianMoments (Charged chargedMeasure)

def OrderedIntegrable (g : Charged → ℝ) : Prop :=
  Integrable (fun Y : ℝ => ∫ u : ℝ, ∫ v : ℝ, g ((u,v),Y))
      (volume.restrict (Set.Ioi (0:ℝ))) ∧
  (∀ᵐ Y : ℝ ∂volume.restrict (Set.Ioi (0:ℝ)),
    Integrable (fun u : ℝ => ∫ v : ℝ, g ((u,v),Y))) ∧
  (∀ᵐ Y : ℝ ∂volume.restrict (Set.Ioi (0:ℝ)),
    ∀ᵐ u : ℝ, Integrable (fun v : ℝ => g ((u,v),Y)))

theorem integrable_of_ordered (g : Charged → ℝ) (hg : StronglyMeasurable g)
    (hn : ∀ x, 0 ≤ g x) (hi : OrderedIntegrable g) : Integrable g chargedMeasure := by
  have hY : ∀ᵐ Y : ℝ ∂volume.restrict (Set.Ioi (0:ℝ)),
      Integrable (fun q : ℝ × ℝ => g (q,Y)) (volume.prod volume) := by
    filter_upwards [hi.2.1,hi.2.2] with Y hu hv
    have hm : StronglyMeasurable (fun q : ℝ × ℝ => g (q,Y)) :=
      hg.comp_measurable (by fun_prop)
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    refine ⟨hv,?_⟩
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hn _)] using hu
  unfold chargedMeasure
  apply (integrable_prod_iff' hg.aestronglyMeasurable).mpr
  refine ⟨hY,hi.1.congr ?_⟩
  filter_upwards [hY] with Y hY
  simp only [Real.norm_eq_abs,abs_of_nonneg (hn _)]
  exact (integral_prod _ hY).symm

theorem integral_order (g : Charged → ℝ) (hg : Integrable g chargedMeasure) :
    (∫ x, g x ∂chargedMeasure) = ∫ Y in Set.Ioi 0, ∫ u, ∫ v, g ((u,v),Y) := by
  unfold chargedMeasure at hg ⊢
  rw [integral_prod_symm _ hg]
  apply integral_congr_ae
  filter_upwards [hg.prod_left_ae] with Y hY
  exact integral_prod _ hY

#print axioms integrable_of_ordered
#print axioms integral_order
end
end UnifiedTheory.Audit.KFCausalChargedProductFubini
