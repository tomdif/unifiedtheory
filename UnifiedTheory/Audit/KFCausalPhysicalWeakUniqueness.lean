/- The distance between two constructed eight-factor weak solutions is
constant. This follows by applying the weak mass-energy identity to their
difference, without assuming that the difference has a cutoff certificate.
It proves uniqueness for identical initial data. -/
import UnifiedTheory.Audit.KFCausalWeakMassConservation
import UnifiedTheory.Audit.KFCausalPhysicalMassEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalPhysicalWeakUniqueness
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalBoundedFormCurve
open UnifiedTheory.Audit.KFCausalShiftedForm
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalPhysicalFormTransport
open UnifiedTheory.Audit.KFCausalPhysicalFormGeometry
open UnifiedTheory.Audit.KFCausalPhysicalFormRegularity
open UnifiedTheory.Audit.KFCausalPhysicalFormWindowBound
open UnifiedTheory.Audit.KFCausalPhysicalWeakTrajectory
open UnifiedTheory.Audit.KFCausalPhysicalWeakFormContinuity
open UnifiedTheory.Audit.KFCausalPhysicalMassEnergy
open UnifiedTheory.Audit.KFCausalMassEnergyIdentities
open UnifiedTheory.Audit.KFCausalWeakMassConservation

theorem massSlope_difference_diagonal_zero (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s₁ s₂ : ℝ)
    (w₁ w₂ : FormSpace ε hε hbar hh mass2 quartic vacuum 0)
    (V₁ : WeakTrajectory ε hε hbar hh mass2 quartic vacuum s₁ w₁)
    (V₂ : WeakTrajectory ε hε hbar hh mass2 quartic vacuum s₂ w₂) (z : ℝ) :
    (inner ℂ (massSlope ε hε hbar hh mass2 quartic vacuum s₁ w₁ V₁ z-massSlope ε hε hbar hh mass2 quartic vacuum s₂ w₂ V₂ z)
      (V₁.formState z-V₂.formState z)).re = 0 := by
  have hs := formOperator_inner_symm (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0) (H := KFCausalFiniteJointGraph.Output (Fin 8) Hilbert)
    (staticMap ε hε hbar hh mass2 quartic vacuum) (growingMap ε hε hbar hh mass2 quartic vacuum) z
  have hpair := schrodinger_diagonal_zero (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0)
    (referenceFormOperator ε hε hbar hh mass2 quartic vacuum z) hs hbar (V₁.formState z-V₂.formState z)
  simpa only [massSlope,map_sub,smul_sub] using hpair

theorem difference_norm_square_conserved (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s₁ s₂ : ℝ)
    (w₁ w₂ : FormSpace ε hε hbar hh mass2 quartic vacuum 0)
    (V₁ : WeakTrajectory ε hε hbar hh mass2 quartic vacuum s₁ w₁)
    (V₂ : WeakTrajectory ε hε hbar hh mass2 quartic vacuum s₂ w₂) (r t : ℝ) :
    ‖embedding ε hε hbar hh mass2 quartic vacuum 0 (V₁.formState t-V₂.formState t)‖^2 =
      ‖embedding ε hε hbar hh mass2 quartic vacuum 0 (V₁.formState r-V₂.formState r)‖^2 := by
  apply norm_square_conserved (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0) (H := Hilbert)
    (embedding ε hε hbar hh mass2 quartic vacuum 0) (embedding_injective ε hε hbar hh mass2 quartic vacuum 0)
    (fun z => V₁.formState z-V₂.formState z)
    (fun z => massSlope ε hε hbar hh mass2 quartic vacuum s₁ w₁ V₁ z-massSlope ε hε hbar hh mass2 quartic vacuum s₂ w₂ V₂ z)
    (fun T => windowRadius ε hε hbar hh mass2 quartic vacuum s₁ T w₁+windowRadius ε hε hbar hh mass2 quartic vacuum s₂ T w₂)
    (fun T => massLipschitzBound ε hε hbar hh mass2 quartic vacuum s₁ T w₁+massLipschitzBound ε hε hbar hh mass2 quartic vacuum s₂ T w₂)
    _ _ _ _ _ _ _ massScale massScale_pos massScale_tendsto r t
  · intro T
    exact add_nonneg (massLipschitzBound_nonneg ε hε hbar hh mass2 quartic vacuum s₁ T w₁)
      (massLipschitzBound_nonneg ε hε hbar hh mass2 quartic vacuum s₂ T w₂)
  · intro T z hT hz
    exact (norm_sub_le _ _).trans (add_le_add (formState_window_bound ε hε hbar hh mass2 quartic vacuum s₁ w₁ V₁ T z hT hz)
      (formState_window_bound ε hε hbar hh mass2 quartic vacuum s₂ w₂ V₂ T z hT hz))
  · intro T z hT hz
    exact (norm_sub_le _ _).trans (add_le_add (massSlope_window_bound ε hε hbar hh mass2 quartic vacuum s₁ w₁ V₁ T z hT hz)
      (massSlope_window_bound ε hε hbar hh mass2 quartic vacuum s₂ w₂ V₂ T z hT hz))
  · intro y
    simpa only [inner_sub_left] using
      (massSlope_weakly_continuous ε hε hbar hh mass2 quartic vacuum s₁ w₁ V₁ y).sub
        (massSlope_weakly_continuous ε hε hbar hh mass2 quartic vacuum s₂ w₂ V₂ y)
  · intro T x y hT hx hy
    have he : gram (embedding ε hε hbar hh mass2 quartic vacuum 0) (V₁.formState y-V₂.formState y)-
        gram (embedding ε hε hbar hh mass2 quartic vacuum 0) (V₁.formState x-V₂.formState x) =
        (massState ε hε hbar hh mass2 quartic vacuum s₁ w₁ V₁ y-massState ε hε hbar hh mass2 quartic vacuum s₁ w₁ V₁ x)-
        (massState ε hε hbar hh mass2 quartic vacuum s₂ w₂ V₂ y-massState ε hε hbar hh mass2 quartic vacuum s₂ w₂ V₂ x) := by
      simp only [massState,massOperator,map_sub]
      abel
    dsimp only
    rw [he]
    apply (norm_sub_le _ _).trans
    have hb := add_le_add (massState_window_lipschitz ε hε hbar hh mass2 quartic vacuum s₁ w₁ V₁ T x y hT hx hy)
      (massState_window_lipschitz ε hε hbar hh mass2 quartic vacuum s₂ w₂ V₂ T x y hT hx hy)
    simpa only [add_mul] using hb
  · intro z y
    have hpair := (mass_pairing_derivative ε hε hbar hh mass2 quartic vacuum s₁ w₁ V₁ z y).sub
      (mass_pairing_derivative ε hε hbar hh mass2 quartic vacuum s₂ w₂ V₂ z y)
    simpa only [massState,massOperator,map_sub,inner_sub_left] using hpair
  · intro z
    exact massSlope_difference_diagonal_zero ε hε hbar hh mass2 quartic vacuum s₁ s₂ w₁ w₂ V₁ V₂ z

theorem physical_distance_conserved (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s₁ s₂ : ℝ)
    (w₁ w₂ : FormSpace ε hε hbar hh mass2 quartic vacuum 0)
    (V₁ : WeakTrajectory ε hε hbar hh mass2 quartic vacuum s₁ w₁)
    (V₂ : WeakTrajectory ε hε hbar hh mass2 quartic vacuum s₂ w₂) (r t : ℝ) :
    ‖embedding ε hε hbar hh mass2 quartic vacuum 0 (V₁.formState t)-embedding ε hε hbar hh mass2 quartic vacuum 0 (V₂.formState t)‖ =
      ‖embedding ε hε hbar hh mass2 quartic vacuum 0 (V₁.formState r)-embedding ε hε hbar hh mass2 quartic vacuum 0 (V₂.formState r)‖ := by
  have hpair := difference_norm_square_conserved ε hε hbar hh mass2 quartic vacuum s₁ s₂ w₁ w₂ V₁ V₂ r t
  rw [map_sub,map_sub] at hpair
  nlinarith [norm_nonneg (embedding ε hε hbar hh mass2 quartic vacuum 0 (V₁.formState t)-embedding ε hε hbar hh mass2 quartic vacuum 0 (V₂.formState t)),
    norm_nonneg (embedding ε hε hbar hh mass2 quartic vacuum 0 (V₁.formState r)-embedding ε hε hbar hh mass2 quartic vacuum 0 (V₂.formState r))]

theorem formState_unique (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) (V₁ V₂ : WeakTrajectory ε hε hbar hh mass2 quartic vacuum s w) :
    V₁.formState = V₂.formState := by
  funext t
  apply embedding_injective ε hε hbar hh mass2 quartic vacuum 0
  have hpair := physical_distance_conserved ε hε hbar hh mass2 quartic vacuum s s w w V₁ V₂ s t
  rw [weak_trajectory_initial,weak_trajectory_initial,sub_self,norm_zero] at hpair
  exact sub_eq_zero.mp (norm_eq_zero.mp hpair)

#print axioms massSlope_difference_diagonal_zero
#print axioms difference_norm_square_conserved
#print axioms physical_distance_conserved
#print axioms formState_unique

end
end UnifiedTheory.Audit.KFCausalPhysicalWeakUniqueness
