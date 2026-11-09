/- The actual transverse shear in paired position coordinates, and its
linear candidate after partial Fourier transformation. No force sign is
assumed. The following module proves the Fourier identification. -/
import UnifiedTheory.Audit.KFCausalClockFloorPairedChart
import UnifiedTheory.Audit.KFCausalTransverseShearTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalChargeShearPairedFlow
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block ProductHilbert)
open UnifiedTheory.Audit.KFCausalPhysicalMixedCoordinates (pairedCoordinates)
open UnifiedTheory.Audit.KFCausalClockFloorPairedChart
open UnifiedTheory.Audit.KFCausalClockFloorSpectatorChart (flow flow_compose flow_zero)
open UnifiedTheory.Audit.KFCausalTransverseShearTransport (transport transport_coe shearFlow shearFlow_quasiMeasurePreserving)

abbrev Paired := Block 2 × Block 4

def pairFlow (b t : ℝ) (x : Paired) : Paired :=
  (Real.exp (b*t/2) • x.1,flow t x.2)

theorem pairFlow_zero (b : ℝ) (x : Paired) : pairFlow b 0 x = x := by
  simp [pairFlow,flow_zero]

theorem pairFlow_compose (b t u : ℝ) (x : Paired) :
    pairFlow b u (pairFlow b t x) = pairFlow b (t+u) x := by
  apply Prod.ext
  · simp only [pairFlow,smul_smul,← Real.exp_add]
    congr 2
    ring
  · exact flow_compose t u x.2

def pairEquiv (b t : ℝ) : Paired ≃L[ℝ] Paired :=
  (show Paired ≃ₗ[ℝ] Paired from
    { toFun := pairFlow b t
      invFun := pairFlow b (-t)
      left_inv := fun x => by rw [pairFlow_compose,add_neg_cancel,pairFlow_zero]
      right_inv := fun x => by rw [pairFlow_compose,neg_add_cancel,pairFlow_zero]
      map_add' := fun x y => by
        apply Prod.ext
        · exact smul_add _ _ _
        · ext i
          fin_cases i <;> simp [pairFlow,flow] <;> ring
      map_smul' := fun a x => by
        apply Prod.ext
        · exact smul_comm _ _ _
        · ext i
          fin_cases i <;> simp [pairFlow,flow] <;> ring }).toContinuousLinearEquiv

theorem pairEquiv_apply (b t : ℝ) (x : Paired) : pairEquiv b t x = pairFlow b t x := rfl

local instance pairedHaar : Measure.IsAddHaarMeasure (volume : Measure Paired) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem pairFlow_quasiMeasurePreserving (b t : ℝ) :
    Measure.QuasiMeasurePreserving (pairFlow b t) volume volume :=
  KFCausalCoupledCoordinateNullSets.homeomorph_quasiMeasurePreserving volume
    (pairEquiv b t).toHomeomorph (pairEquiv b t).symm.differentiable

theorem paired_shearFlow (t : ℝ) (x : Paired) :
    pair (shearFlow t (pair.symm x)) = pairFlow 1 t x := by
  rw [show shearFlow t (pair.symm x) =
    ((pair.symm x).1,KFCausalTransverseDilationFlow.flow t (pair.symm x).2) from rfl,
    pair_flow,MeasurableEquiv.apply_symm_apply]
  simp only [pairFlow,one_mul]

def pairedTransport (t : ℝ) : ProductHilbert 2 4 ≃ₗᵢ[ℂ] ProductHilbert 2 4 :=
  pairedCoordinates.symm.trans ((transport t).trans pairedCoordinates)

theorem pairedTransport_coe (t : ℝ) (f : ProductHilbert 2 4) :
    pairedTransport t f =ᵐ[volume] fun x => (Real.exp t:ℂ)*f (pairFlow 1 t x) := by
  filter_upwards [paired_coe (transport t (pairedCoordinates.symm f)),
    pair_preserves_volume.symm.quasiMeasurePreserving.ae
      (transport_coe t (pairedCoordinates.symm f)),
    ((shearFlow_quasiMeasurePreserving t).comp
      pair_preserves_volume.symm.quasiMeasurePreserving).ae (paired_inverse_coe f)] with x hp ht hf
  change pairedCoordinates (transport t (pairedCoordinates.symm f)) x = _
  dsimp only [Function.comp_apply] at hf
  rw [hp,ht,hf,paired_shearFlow]

theorem determinant_cancellation (t : ℝ) : Real.exp t*((Real.exp (t/2))^2)⁻¹ = 1 := by
  have he : (Real.exp (t/2))^2 = Real.exp t := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  rw [he,mul_inv_cancel₀ (Real.exp_ne_zero t)]

#print axioms pairFlow_zero
#print axioms pairFlow_compose
#print axioms pairEquiv_apply
#print axioms pairFlow_quasiMeasurePreserving
#print axioms paired_shearFlow
#print axioms pairedTransport_coe
#print axioms determinant_cancellation
end
end UnifiedTheory.Audit.KFCausalChargeShearPairedFlow
