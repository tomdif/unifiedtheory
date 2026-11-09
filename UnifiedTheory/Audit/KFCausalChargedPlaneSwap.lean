/- A unitary interchange of the two charged standing-wave planes.
Its fixed space is closed. Clock and neutral-coordinate multipliers
commute with it; charge zero alone will not imply this extra symmetry. -/
import UnifiedTheory.Audit.KFCausalNeutralMixedClockCharge
import UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalChargedPlaneSwap
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint JointHilbert)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback

abbrev Space := Joint 2 4

def swap (x : Space) : Space := WithLp.toLp 2 fun
  | .inl i => ![x (.inl 1),x (.inl 0)] i
  | .inr i => ![x (.inr 0),x (.inr 2),x (.inr 1),x (.inr 3)] i

theorem swap_twice (x : Space) : swap (swap x) = x := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [swap]

def swapLinear : Space ≃ₗ[ℝ] Space where
  toFun := swap
  invFun := swap
  left_inv := swap_twice
  right_inv := swap_twice
  map_add' x y := by
    ext i
    rcases i with i | i <;> fin_cases i <;> simp [swap]
  map_smul' c x := by
    ext i
    rcases i with i | i <;> fin_cases i <;> simp [swap]

theorem swap_inner (x y : Space) : inner ℝ (swapLinear x) (swapLinear y) = inner ℝ x y := by
  simp [PiLp.inner_apply,Fintype.sum_sum_type,Fin.sum_univ_succ,swapLinear,swap,RCLike.inner_apply]
  ring

def swapIsometry : Space ≃ₗᵢ[ℝ] Space where
  toLinearEquiv := swapLinear
  norm_map' := (swapLinear.toLinearMap.isometryOfInner swap_inner).norm_map

def mixed : JointHilbert 2 4 ≃ₗᵢ[ℂ] JointHilbert 2 4 :=
  unitaryPullback swapIsometry.toMeasurableEquiv swapIsometry.measurePreserving

theorem mixed_coe (f : JointHilbert 2 4) : mixed f =ᵐ[volume] fun x => f (swap x) :=
  unitaryPullback_coe _ _ f

def operator : Hilbert ≃ₗᵢ[ℂ] Hilbert := chargeCoordinates.trans (mixed.trans chargeCoordinates.symm)

theorem coordinates_operator (f : Hilbert) : chargeCoordinates (operator f) = mixed (chargeCoordinates f) := by
  simp only [operator,LinearIsometryEquiv.trans_apply,LinearIsometryEquiv.apply_symm_apply]

def fixedSpace : Submodule ℂ Hilbert where
  carrier := {f | operator f = f}
  zero_mem' := map_zero _
  add_mem' hx hy := by
    dsimp only [Set.mem_setOf_eq] at *
    rw [map_add,hx,hy]
  smul_mem' c f hf := by
    dsimp only [Set.mem_setOf_eq] at *
    rw [map_smul,hf]

theorem mem_fixedSpace (f : Hilbert) : f ∈ fixedSpace ↔ operator f = f := Iff.rfl

theorem fixedSpace_closed : IsClosed (fixedSpace : Set Hilbert) :=
  isClosed_eq operator.continuous continuous_id

theorem neutral_multiplier (w : ℝ → ℂ) (hw : Measurable w) (hb : ∀ s, ‖w s‖ ≤ 1) (f : Hilbert) :
    KFCausalNeutralMultiplierCharge.multiplier w hw hb (operator f) =
      operator (KFCausalNeutralMultiplierCharge.multiplier w hw hb f) := by
  apply chargeCoordinates.injective
  apply Lp.ext
  filter_upwards [KFCausalNeutralMultiplierCharge.charge_multiplier_coe w hw hb (operator f),
    mixed_coe (chargeCoordinates f),
    mixed_coe (chargeCoordinates (KFCausalNeutralMultiplierCharge.multiplier w hw hb f)),
    swapIsometry.measurePreserving.quasiMeasurePreserving.ae
      (KFCausalNeutralMultiplierCharge.charge_multiplier_coe w hw hb f)] with x hv hu ha hf
  rw [hv,coordinates_operator,hu,coordinates_operator,ha]
  exact hf.symm

theorem clock_multiplier (w : ℝ → ℂ) (hw : Measurable w) (hb : ∀ s, ‖w s‖ ≤ 1) (f : Hilbert) :
    KFCausalClockChargeMultiplier.clockMultiplier w hw hb (operator f) =
      operator (KFCausalClockChargeMultiplier.clockMultiplier w hw hb f) := by
  apply chargeCoordinates.injective
  apply Lp.ext
  have hc (g : Hilbert) : chargeCoordinates (KFCausalClockChargeMultiplier.clockMultiplier w hw hb g) =ᵐ[volume]
      fun x => w (x (.inr 0))*chargeCoordinates g x := by
    rw [KFCausalClockChargeMultiplier.chargeCoordinates_multiplier]
    exact KFCausalClockChargeMultiplier.jointMultiplier_coe w hw hb _
  filter_upwards [hc (operator f),mixed_coe (chargeCoordinates f),
    mixed_coe (chargeCoordinates (KFCausalClockChargeMultiplier.clockMultiplier w hw hb f)),
    swapIsometry.measurePreserving.quasiMeasurePreserving.ae (hc f)] with x hv hu ha hf
  rw [hv,coordinates_operator,hu,coordinates_operator,ha]
  exact hf.symm

theorem radius_swap (c : ℝ) (x : Space) :
    KFCausalChargeGaussianGeometry.radius c (swap x) = KFCausalChargeGaussianGeometry.radius c x := by
  simp only [KFCausalChargeGaussianGeometry.radius_coordinates,swap]
  dsimp
  ring

theorem weight_swap (ε a h : ℝ) (x : Space) :
    KFCausalClockFloorCoherentStates.weight ε a h (swap x) =
      KFCausalClockFloorCoherentStates.weight ε a h x := by
  simp only [KFCausalClockFloorCoherentStates.weight,KFCausalChargeGaussianGeometry.profile,radius_swap]
  rfl

theorem trial_fixed (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) :
    KFCausalClockFloorInvariantTrial.trialState ε a h hε ha hh ∈ fixedSpace := by
  apply chargeCoordinates.injective
  rw [coordinates_operator]
  apply Lp.ext
  filter_upwards [mixed_coe (chargeCoordinates (KFCausalClockFloorInvariantTrial.trialState ε a h hε ha hh)),
    swapIsometry.measurePreserving.quasiMeasurePreserving.ae
      (KFCausalClockFloorCoherentStates.weight_coe ε a h hε ha hh),
    KFCausalClockFloorCoherentStates.weight_coe ε a h hε ha hh] with x hx hy hz
  change chargeCoordinates (KFCausalClockFloorInvariantTrial.trialState ε a h hε ha hh) (swap x) =
    KFCausalClockFloorCoherentStates.weight ε a h (swap x) at hy
  rw [hx,hy,weight_swap,hz]

#print axioms swap_twice
#print axioms swap_inner
#print axioms mixed_coe
#print axioms coordinates_operator
#print axioms mem_fixedSpace
#print axioms fixedSpace_closed
#print axioms neutral_multiplier
#print axioms clock_multiplier
#print axioms radius_swap
#print axioms weight_swap
#print axioms trial_fixed
end
end UnifiedTheory.Audit.KFCausalChargedPlaneSwap
