/- All-time unitary evolution for the fixed-regulator homogeneous model.
The complex-linear form-domain flow extends through its dense embedding
to every physical L2 initial vector. Its form-domain trajectories satisfy
the actual integrated unbounded Schrodinger equation. This does not prove
the full six-mode theory or removal of the clock regulator. -/
import UnifiedTheory.Audit.KFCausalRegularizedFormLinearity
import UnifiedTheory.Audit.KFCausalDenseUnitaryExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalRegularizedHomogeneousEvolution
noncomputable section
open UnifiedTheory.Audit.KFCausalRegularizedMomentumClosure
open UnifiedTheory.Audit.KFCausalRegularizedFormEmbedding
open UnifiedTheory.Audit.KFCausalRegularizedFormRegularity
open UnifiedTheory.Audit.KFCausalRegularizedWeakTrajectory
open UnifiedTheory.Audit.KFCausalRegularizedWeakIntegralEquation
open UnifiedTheory.Audit.KFCausalRegularizedFormFlow
open UnifiedTheory.Audit.KFCausalRegularizedFormLinearity
open UnifiedTheory.Audit.KFCausalDenseUnitaryExtension

def formEquiv (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ) :
    FormSpace ε hε hbar coupling 0 ≃ₗ[ℂ] FormSpace ε hε hbar coupling 0 where
  toLinearMap := formLinearMap ε hε hbar coupling s t
  invFun := formFlow ε hε hbar coupling t s
  left_inv := formFlow_reverse ε hε hbar coupling s t
  right_inv := formFlow_reverse ε hε hbar coupling t s

def evolution (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ) : Hilbert ≃ₗᵢ[ℂ] Hilbert :=
  extension (E := FormSpace ε hε hbar coupling 0) (H := Hilbert)
    (embedding ε hε hbar coupling 0).toLinearMap (embedding_dense ε hε hbar coupling 0)
    (formEquiv ε hε hbar coupling s t) (formFlow_physical_norm ε hε hbar coupling s t)

theorem evolution_embedding (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ)
    (w : FormSpace ε hε hbar coupling 0) :
    evolution ε hε hbar coupling s t (embedding ε hε hbar coupling 0 w) =
      embedding ε hε hbar coupling 0 (formFlow ε hε hbar coupling s t w) := by
  have hh := extension_embedding (E := FormSpace ε hε hbar coupling 0) (H := Hilbert)
    (embedding ε hε hbar coupling 0).toLinearMap (embedding_dense ε hε hbar coupling 0)
    (formEquiv ε hε hbar coupling s t) (formFlow_physical_norm ε hε hbar coupling s t) w
  exact hh

theorem evolution_unitary (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ) :
    (evolution ε hε hbar coupling s t : Hilbert →L[ℂ] Hilbert) ∈ unitary (Hilbert →L[ℂ] Hilbert) := by
  have hh := extension_unitary (E := FormSpace ε hε hbar coupling 0) (H := Hilbert)
    (embedding ε hε hbar coupling 0).toLinearMap (embedding_dense ε hε hbar coupling 0)
    (formEquiv ε hε hbar coupling s t) (formFlow_physical_norm ε hε hbar coupling s t)
  exact hh

theorem evolution_initial (ε : ℝ) (hε : 0 < ε) (hbar coupling s : ℝ) :
    (evolution ε hε hbar coupling s s : Hilbert →L[ℂ] Hilbert) = 1 := by
  apply equal_on_dense (E := FormSpace ε hε hbar coupling 0) (H := Hilbert)
    (embedding ε hε hbar coupling 0).toLinearMap (embedding_dense ε hε hbar coupling 0)
  intro w
  change evolution ε hε hbar coupling s s (embedding ε hε hbar coupling 0 w) = embedding ε hε hbar coupling 0 w
  rw [evolution_embedding,formFlow_initial]

theorem evolution_compose (ε : ℝ) (hε : 0 < ε) (hbar coupling s r t : ℝ) :
    (evolution ε hε hbar coupling r t : Hilbert →L[ℂ] Hilbert)*
      (evolution ε hε hbar coupling s r : Hilbert →L[ℂ] Hilbert) =
      (evolution ε hε hbar coupling s t : Hilbert →L[ℂ] Hilbert) := by
  apply equal_on_dense (E := FormSpace ε hε hbar coupling 0) (H := Hilbert)
    (embedding ε hε hbar coupling 0).toLinearMap (embedding_dense ε hε hbar coupling 0)
  intro w
  change evolution ε hε hbar coupling r t (evolution ε hε hbar coupling s r (embedding ε hε hbar coupling 0 w)) =
    evolution ε hε hbar coupling s t (embedding ε hε hbar coupling 0 w)
  rw [evolution_embedding,evolution_embedding,evolution_embedding,formFlow_compose]

theorem evolution_reverse (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ) :
    (evolution ε hε hbar coupling t s : Hilbert →L[ℂ] Hilbert)*
      (evolution ε hε hbar coupling s t : Hilbert →L[ℂ] Hilbert) = 1 := by
  rw [evolution_compose,evolution_initial]

theorem evolution_adjoint (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ) :
    (evolution ε hε hbar coupling s t : Hilbert →L[ℂ] Hilbert).adjoint =
      (evolution ε hε hbar coupling t s : Hilbert →L[ℂ] Hilbert) := by
  apply equal_on_dense (E := FormSpace ε hε hbar coupling 0) (H := Hilbert)
    (embedding ε hε hbar coupling 0).toLinearMap (embedding_dense ε hε hbar coupling 0)
  intro w
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  apply (evolution ε hε hbar coupling s t).injective
  change evolution ε hε hbar coupling s t ((evolution ε hε hbar coupling s t).symm (embedding ε hε hbar coupling 0 w)) =
    evolution ε hε hbar coupling s t (evolution ε hε hbar coupling t s (embedding ε hε hbar coupling 0 w))
  rw [LinearIsometryEquiv.apply_symm_apply,evolution_embedding,evolution_embedding,formFlow_reverse]

theorem evolution_norm (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ) (f : Hilbert) :
    ‖evolution ε hε hbar coupling s t f‖ = ‖f‖ := (evolution ε hε hbar coupling s t).norm_map f

theorem evolution_inner (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ) (f g : Hilbert) :
    inner ℂ (evolution ε hε hbar coupling s t f) (evolution ε hε hbar coupling s t g) = inner ℂ f g :=
  (evolution ε hε hbar coupling s t).inner_map_map f g

theorem evolution_surjective (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ) :
    Function.Surjective (evolution ε hε hbar coupling s t) := (evolution ε hε hbar coupling s t).surjective

theorem evolution_strong_continuous (ε : ℝ) (hε : 0 < ε) (hbar coupling s : ℝ) (f : Hilbert) :
    Continuous (fun t => evolution ε hε hbar coupling s t f) := by
  have hh := extension_strong_continuous (E := FormSpace ε hε hbar coupling 0) (H := Hilbert)
    (embedding ε hε hbar coupling 0).toLinearMap (embedding_dense ε hε hbar coupling 0)
    (fun t => formEquiv ε hε hbar coupling s t) (formFlow_physical_norm ε hε hbar coupling s)
    (formFlow_physical_continuous ε hε hbar coupling s) f
  exact hh

theorem evolution_schrodinger_integral (ε : ℝ) (hε : 0 < ε) (hbar coupling s : ℝ)
    (hhbar : hbar ≠ 0) (w v : FormSpace ε hε hbar coupling 0) (r t : ℝ) :
    (∫ z in r..t, inner ℂ (formFlow ε hε hbar coupling s z w) (referenceFormOperator ε hε hbar coupling z v)) =
      (-Complex.I*(hbar:ℂ)) *
        (inner ℂ (evolution ε hε hbar coupling s t (embedding ε hε hbar coupling 0 w)) (embedding ε hε hbar coupling 0 v)-
         inner ℂ (evolution ε hε hbar coupling s r (embedding ε hε hbar coupling 0 w)) (embedding ε hε hbar coupling 0 v)) := by
  rw [evolution_embedding,evolution_embedding]
  exact weak_trajectory_schrodinger_integral ε hε hbar coupling s hhbar w
    (weakTrajectory ε hε hbar coupling s w) r t v

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
end UnifiedTheory.Audit.KFCausalRegularizedHomogeneousEvolution
