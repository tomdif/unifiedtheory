/- Reorder the original mixed Product into its unchanged clock q and
five real transverse coordinates. This is an actual volume-preserving
coordinate map, before the physical momentum dilation and real shear. -/
import UnifiedTheory.Audit.KFCausalPhysicalFourierGeneralCoordinates
import UnifiedTheory.Audit.KFCausalIndependentRadialPulledLaplacian

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalIndependentRadialTransverseMeasure
noncomputable section
open MeasureTheory
open KFCausalPhysicalFourierGeneralCoordinates (Product)
open KFCausalEuclideanProductCoordinates (Block Joint)

abbrev RealSpace := Fin 5→ℝ

def indices : (Fin 2⊕Fin 4)≃Fin 6 where
  toFun := Sum.elim (fun i=>![1,2] i) (fun i=>![0,3,4,5] i)
  invFun i := ![Sum.inr 0,Sum.inl 0,Sum.inl 1,Sum.inr 1,Sum.inr 2,Sum.inr 3] i
  left_inv i := by rcases i with i|i <;> fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def coordinateIsometry : Joint 2 4≃ₗᵢ[ℝ]EuclideanSpace ℝ (Fin 6) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ indices

def reorder : Product≃ᵐ(ℝ×RealSpace) :=
  (KFCausalEuclideanProductCoordinates.split 2 4).symm.trans
    (coordinateIsometry.toMeasurableEquiv.trans KFCausalEuclideanConfiguration.split)

def back (q : ℝ) (y : RealSpace) : Product :=
  (WithLp.toLp 2 ![y 0,y 1],WithLp.toLp 2 ![q,y 2,y 3,y 4])

theorem reorder_apply (x : Product) :
    reorder x=(x.2 0,![x.1 0,x.1 1,x.2 1,x.2 2,x.2 3]) := by
  apply Prod.ext
  · rfl
  · funext i
    fin_cases i <;> rfl

theorem reorder_back (q : ℝ) (y : RealSpace) : reorder (back q y)=(q,y) := by
  rw [reorder_apply]
  apply Prod.ext
  · rfl
  · funext i
    fin_cases i <;> rfl

theorem reorder_symm (q : ℝ) (y : RealSpace) : reorder.symm (q,y)=back q y := by
  apply reorder.injective
  rw [reorder.apply_symm_apply,reorder_back]

theorem reorder_preserving : MeasurePreserving reorder :=
  (KFCausalEuclideanConfiguration.split_preserves_volume.comp coordinateIsometry.measurePreserving).comp
    (KFCausalEuclideanProductCoordinates.split_preserves_volume 2 4).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem integrable_iff (f : Product→E) :
    Integrable (fun z:ℝ×RealSpace=>f (back z.1 z.2)) ↔ Integrable f := by
  have hback : (fun z:ℝ×RealSpace=>f (reorder.symm z)) =
      (fun z:ℝ×RealSpace=>f (back z.1 z.2)) := by
    funext z
    rcases z with ⟨q,y⟩
    rw [reorder_symm]
  simpa only [Function.comp_def,hback] using
    (reorder_preserving.symm.integrable_comp_emb reorder.symm.measurableEmbedding (g:=f))

theorem integral_order (f : Product→E) (hf : Integrable f) :
    (∫x:Product,f x)=∫q:ℝ,∫y:RealSpace,f (back q y) := by
  have he := reorder_preserving.symm.integral_comp reorder.symm.measurableEmbedding f
  calc
    (∫x:Product,f x) = ∫z:ℝ×RealSpace,f (reorder.symm z) := he.symm
    _ = ∫q:ℝ,∫y:RealSpace,f (reorder.symm (q,y)) :=
      integral_prod _ (by
        simpa only [←Measure.volume_eq_prod ℝ RealSpace] using
          (reorder_preserving.symm.integrable_comp_emb
            reorder.symm.measurableEmbedding (g:=f)).mpr hf)
    _ = ∫q:ℝ,∫y:RealSpace,f (back q y) := by simp only [reorder_symm]

#print axioms reorder_apply
#print axioms reorder_back
#print axioms reorder_symm
#print axioms reorder_preserving
#print axioms integrable_iff
#print axioms integral_order
end
end UnifiedTheory.Audit.KFCausalIndependentRadialTransverseMeasure
