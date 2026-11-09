/- The actual paired squeeze in paired position coordinates. Its two
antisymmetric variables expand under the inverse pullback; the three
nonclock spectator variables contract. -/
import UnifiedTheory.Audit.KFCausalClockFloorPairedChart
import UnifiedTheory.Audit.KFCausalPairedSqueezeTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalChargeSqueezePairedFlow
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block ProductHilbert)
open UnifiedTheory.Audit.KFCausalPhysicalMixedCoordinates (pairedCoordinates)
open UnifiedTheory.Audit.KFCausalClockFloorPairedChart
open UnifiedTheory.Audit.KFCausalPairedSqueezeFlow
open UnifiedTheory.Audit.KFCausalPairedSqueezeTransport

abbrev Paired := Block 2 × Block 4

def rightFlow (a : ℝ) (x : Block 4) : Block 4 :=
  WithLp.toLp 2 (fun i => if i = 0 then x i else Real.exp (-a)*x i)

def pairFlow (b a : ℝ) (x : Paired) : Paired :=
  (Real.exp (b*a) • x.1,rightFlow a x.2)

theorem pairFlow_zero (b : ℝ) (x : Paired) : pairFlow b 0 x = x := by
  apply Prod.ext
  · simp [pairFlow]
  · ext i
    fin_cases i <;> simp [pairFlow,rightFlow]

theorem pairFlow_compose (b a t : ℝ) (x : Paired) :
    pairFlow b t (pairFlow b a x) = pairFlow b (a+t) x := by
  apply Prod.ext
  · simp only [pairFlow,smul_smul,← Real.exp_add]
    congr 2
    ring
  · ext i
    fin_cases i <;> simp [pairFlow,rightFlow,Real.exp_add] <;> ring

def pairEquiv (b a : ℝ) : Paired ≃L[ℝ] Paired :=
  (show Paired ≃ₗ[ℝ] Paired from
    { toFun := pairFlow b a
      invFun := pairFlow b (-a)
      left_inv := fun x => by rw [pairFlow_compose,add_neg_cancel,pairFlow_zero]
      right_inv := fun x => by rw [pairFlow_compose,neg_add_cancel,pairFlow_zero]
      map_add' := fun x y => by
        apply Prod.ext
        · exact smul_add _ _ _
        · ext i
          fin_cases i <;> simp [pairFlow,rightFlow,mul_add]
      map_smul' := fun c x => by
        apply Prod.ext
        · exact smul_comm _ _ _
        · ext i
          fin_cases i <;> simp [pairFlow,rightFlow] <;> ring }).toContinuousLinearEquiv

theorem pairEquiv_apply (b a : ℝ) (x : Paired) : pairEquiv b a x = pairFlow b a x := rfl

local instance pairedHaar : Measure.IsAddHaarMeasure (volume : Measure Paired) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem pairFlow_quasiMeasurePreserving (b a : ℝ) :
    Measure.QuasiMeasurePreserving (pairFlow b a) volume volume :=
  KFCausalCoupledCoordinateNullSets.homeomorph_quasiMeasurePreserving volume
    (pairEquiv b a).toHomeomorph (pairEquiv b a).symm.differentiable

theorem pair_squeeze (a : ℝ) (x : Configuration) :
    pair (squeezeFlow a x) = pairFlow 1 a (pair x) := by
  rw [squeezeFlow_apply,pair_apply,pair_apply]
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [pairFlow,squeeze,diagonal,offDiagonal] <;> ring
  · ext i
    fin_cases i <;> simp [pairFlow,rightFlow,squeeze,diagonal,offDiagonal] <;> ring

theorem paired_squeezeFlow (a : ℝ) (x : Paired) :
    pair (squeezeFlow a (pair.symm x)) = pairFlow 1 a x := by
  rw [pair_squeeze,MeasurableEquiv.apply_symm_apply]

def pairedTransport (a : ℝ) : ProductHilbert 2 4 ≃ₗᵢ[ℂ] ProductHilbert 2 4 :=
  pairedCoordinates.symm.trans ((transport a).trans pairedCoordinates)

theorem pairedTransport_coe (a : ℝ) (f : ProductHilbert 2 4) :
    pairedTransport a f =ᵐ[volume] fun x => (Real.exp (-a/2):ℂ)*f (pairFlow 1 a x) := by
  filter_upwards [paired_coe (transport a (pairedCoordinates.symm f)),
    pair_preserves_volume.symm.quasiMeasurePreserving.ae
      (transport_coe a (pairedCoordinates.symm f)),
    ((squeezeFlow_quasiMeasurePreserving a).comp
      pair_preserves_volume.symm.quasiMeasurePreserving).ae (paired_inverse_coe f)] with x hp ht hf
  change pairedCoordinates (transport a (pairedCoordinates.symm f)) x = _
  dsimp only [Function.comp_apply] at hf
  rw [hp,ht,hf,paired_squeezeFlow]

theorem fourier_weight (a : ℝ) :
    Real.exp (-a/2)*((Real.exp a)^2)⁻¹ = Real.exp (-5*a/2) := by
  rw [← Real.exp_nat_mul,← Real.exp_neg,← Real.exp_add]
  congr 1
  norm_num
  ring

#print axioms pairFlow_zero
#print axioms pairFlow_compose
#print axioms pairEquiv_apply
#print axioms pairFlow_quasiMeasurePreserving
#print axioms pair_squeeze
#print axioms paired_squeezeFlow
#print axioms pairedTransport_coe
#print axioms fourier_weight

end
end UnifiedTheory.Audit.KFCausalChargeSqueezePairedFlow
