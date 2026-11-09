/- All-time unitary evolution for the actual charge-averaged clock-floor
Hamiltonian. Form-domain trajectories satisfy its integrated unbounded
Schrodinger equation. Constraint preservation and physical limits are
separate obligations. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedFormLinearity
import UnifiedTheory.Audit.KFCausalDenseUnitaryExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormGeometry
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakTrajectory
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakIntegralEquation
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormLinearity
open UnifiedTheory.Audit.KFCausalDenseUnitaryExtension

def formEquiv (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s t : ℝ) :
    FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0 ≃ₗ[ℂ] FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0 where
  toLinearMap := formLinearMap ε hε hbar hh hbound mass2 quartic vacuum s t
  invFun := formFlow ε hε hbar hh hbound mass2 quartic vacuum t s
  left_inv := formFlow_reverse ε hε hbar hh hbound mass2 quartic vacuum s t
  right_inv := formFlow_reverse ε hε hbar hh hbound mass2 quartic vacuum t s

def evolution (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s t : ℝ) : Hilbert ≃ₗᵢ[ℂ] Hilbert :=
  extension (E := FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (H := Hilbert)
    (embedding ε hε hbar hh hbound mass2 quartic vacuum 0).toLinearMap (embedding_dense ε hε hbar hh hbound mass2 quartic vacuum 0)
    (formEquiv ε hε hbar hh hbound mass2 quartic vacuum s t) (formFlow_physical_norm ε hε hbar hh hbound mass2 quartic vacuum s t)

theorem evolution_embedding (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s t : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) :
    evolution ε hε hbar hh hbound mass2 quartic vacuum s t (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 w) =
      embedding ε hε hbar hh hbound mass2 quartic vacuum 0 (formFlow ε hε hbar hh hbound mass2 quartic vacuum s t w) := by
  have hpair := extension_embedding (E := FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (H := Hilbert)
    (embedding ε hε hbar hh hbound mass2 quartic vacuum 0).toLinearMap (embedding_dense ε hε hbar hh hbound mass2 quartic vacuum 0)
    (formEquiv ε hε hbar hh hbound mass2 quartic vacuum s t) (formFlow_physical_norm ε hε hbar hh hbound mass2 quartic vacuum s t) w
  exact hpair

theorem evolution_unitary (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s t : ℝ) :
    (evolution ε hε hbar hh hbound mass2 quartic vacuum s t : Hilbert →L[ℂ] Hilbert) ∈ unitary (Hilbert →L[ℂ] Hilbert) := by
  have hpair := extension_unitary (E := FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (H := Hilbert)
    (embedding ε hε hbar hh hbound mass2 quartic vacuum 0).toLinearMap (embedding_dense ε hε hbar hh hbound mass2 quartic vacuum 0)
    (formEquiv ε hε hbar hh hbound mass2 quartic vacuum s t) (formFlow_physical_norm ε hε hbar hh hbound mass2 quartic vacuum s t)
  exact hpair

theorem evolution_initial (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s : ℝ) :
    (evolution ε hε hbar hh hbound mass2 quartic vacuum s s : Hilbert →L[ℂ] Hilbert) = 1 := by
  apply equal_on_dense (E := FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (H := Hilbert)
    (embedding ε hε hbar hh hbound mass2 quartic vacuum 0).toLinearMap (embedding_dense ε hε hbar hh hbound mass2 quartic vacuum 0)
  intro w
  change evolution ε hε hbar hh hbound mass2 quartic vacuum s s (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 w) = embedding ε hε hbar hh hbound mass2 quartic vacuum 0 w
  rw [evolution_embedding,formFlow_initial]

theorem evolution_compose (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s r t : ℝ) :
    (evolution ε hε hbar hh hbound mass2 quartic vacuum r t : Hilbert →L[ℂ] Hilbert)*
      (evolution ε hε hbar hh hbound mass2 quartic vacuum s r : Hilbert →L[ℂ] Hilbert) =
      (evolution ε hε hbar hh hbound mass2 quartic vacuum s t : Hilbert →L[ℂ] Hilbert) := by
  apply equal_on_dense (E := FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (H := Hilbert)
    (embedding ε hε hbar hh hbound mass2 quartic vacuum 0).toLinearMap (embedding_dense ε hε hbar hh hbound mass2 quartic vacuum 0)
  intro w
  change evolution ε hε hbar hh hbound mass2 quartic vacuum r t (evolution ε hε hbar hh hbound mass2 quartic vacuum s r (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 w)) =
    evolution ε hε hbar hh hbound mass2 quartic vacuum s t (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 w)
  rw [evolution_embedding,evolution_embedding,evolution_embedding,formFlow_compose]

theorem evolution_reverse (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s t : ℝ) :
    (evolution ε hε hbar hh hbound mass2 quartic vacuum t s : Hilbert →L[ℂ] Hilbert)*
      (evolution ε hε hbar hh hbound mass2 quartic vacuum s t : Hilbert →L[ℂ] Hilbert) = 1 := by
  rw [evolution_compose,evolution_initial]

theorem evolution_adjoint (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s t : ℝ) :
    (evolution ε hε hbar hh hbound mass2 quartic vacuum s t : Hilbert →L[ℂ] Hilbert).adjoint =
      (evolution ε hε hbar hh hbound mass2 quartic vacuum t s : Hilbert →L[ℂ] Hilbert) := by
  apply ContinuousLinearMap.ext
  intro f
  have hr := congrArg (fun A : Hilbert →L[ℂ] Hilbert => A f)
    (evolution_reverse ε hε hbar hh hbound mass2 quartic vacuum t s)
  have hi : (evolution ε hε hbar hh hbound mass2 quartic vacuum s t).symm f =
      evolution ε hε hbar hh hbound mass2 quartic vacuum t s f :=
    (evolution ε hε hbar hh hbound mass2 quartic vacuum s t).injective
      (((evolution ε hε hbar hh hbound mass2 quartic vacuum s t).apply_symm_apply f).trans hr.symm)
  have ha := congrArg (fun A : Hilbert →L[ℂ] Hilbert => A f)
    (LinearIsometryEquiv.adjoint_eq_symm (evolution ε hε hbar hh hbound mass2 quartic vacuum s t))
  exact ha.trans hi

theorem evolution_norm (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s t : ℝ) (f : Hilbert) :
    ‖evolution ε hε hbar hh hbound mass2 quartic vacuum s t f‖ = ‖f‖ := (evolution ε hε hbar hh hbound mass2 quartic vacuum s t).norm_map f

theorem evolution_inner (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s t : ℝ) (f g : Hilbert) :
    inner ℂ (evolution ε hε hbar hh hbound mass2 quartic vacuum s t f) (evolution ε hε hbar hh hbound mass2 quartic vacuum s t g) = inner ℂ f g :=
  (evolution ε hε hbar hh hbound mass2 quartic vacuum s t).inner_map_map f g

theorem evolution_surjective (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s t : ℝ) :
    Function.Surjective (evolution ε hε hbar hh hbound mass2 quartic vacuum s t) := (evolution ε hε hbar hh hbound mass2 quartic vacuum s t).surjective

theorem evolution_strong_continuous (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s : ℝ) (f : Hilbert) :
    Continuous (fun t => evolution ε hε hbar hh hbound mass2 quartic vacuum s t f) := by
  have hpair := extension_strong_continuous (E := FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (H := Hilbert)
    (embedding ε hε hbar hh hbound mass2 quartic vacuum 0).toLinearMap (embedding_dense ε hε hbar hh hbound mass2 quartic vacuum 0)
    (fun t => formEquiv ε hε hbar hh hbound mass2 quartic vacuum s t) (formFlow_physical_norm ε hε hbar hh hbound mass2 quartic vacuum s)
    (formFlow_physical_continuous ε hε hbar hh hbound mass2 quartic vacuum s) f
  exact hpair

theorem evolution_schrodinger_integral (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s : ℝ)
    (hhbar : hbar ≠ 0) (w v : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (r t : ℝ) :
    (∫ z in r..t, inner ℂ (formFlow ε hε hbar hh hbound mass2 quartic vacuum s z w) (referenceFormOperator ε hε hbar hh hbound mass2 quartic vacuum z v)) =
      (-Complex.I*(hbar:ℂ)) *
        (inner ℂ (evolution ε hε hbar hh hbound mass2 quartic vacuum s t (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 w)) (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 v)-
         inner ℂ (evolution ε hε hbar hh hbound mass2 quartic vacuum s r (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 w)) (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 v)) := by
  have hi := weak_trajectory_schrodinger_integral ε hε hbar hh hbound mass2 quartic vacuum s hhbar w
    (weakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w) r t v
  have he := congrArg₂ (fun a b : Hilbert => (-Complex.I*(hbar:ℂ)) *
    (inner ℂ a (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 v) -
     inner ℂ b (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 v)))
    (evolution_embedding ε hε hbar hh hbound mass2 quartic vacuum s t w)
    (evolution_embedding ε hε hbar hh hbound mass2 quartic vacuum s r w)
  exact hi.trans he.symm

#print axioms formEquiv
#print axioms evolution
#print axioms evolution_embedding
#print axioms evolution_unitary
#print axioms evolution_initial
#print axioms evolution_compose
#print axioms evolution_reverse
#print axioms evolution_adjoint
#print axioms evolution_norm
#print axioms evolution_inner
#print axioms evolution_surjective
#print axioms evolution_strong_continuous
#print axioms evolution_schrodinger_integral

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
