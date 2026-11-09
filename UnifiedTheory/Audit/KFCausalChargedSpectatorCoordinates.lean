/- The actual physical charge action splits into a four-dimensional charged
rotation and an identity on the clock/neutral spectator coordinates. -/
import UnifiedTheory.Audit.KFCausalPhysicalCircleAction
import UnifiedTheory.Audit.KFCausalEuclideanTensorUnitary

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalChargedSpectatorCoordinates
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates
open KFCausalMeasureUnitaryPullback
open KFCausalL2TensorEmbedding (productState productState_coe)

def rotate (θ : ℝ) (x : Block 4) : Block 4 := WithLp.toLp 2
  ![Real.cos θ*x 0-Real.sin θ*x 1,Real.sin θ*x 0+Real.cos θ*x 1,
    Real.cos θ*x 2-Real.sin θ*x 3,Real.sin θ*x 2+Real.cos θ*x 3]

theorem rotate_reverse (θ : ℝ) (x : Block 4) : rotate (-θ) (rotate θ x) = x := by
  ext i
  fin_cases i <;> simp [rotate]
  · linear_combination (x 0)*(Real.sin_sq_add_cos_sq θ)
  · linear_combination (x 1)*(Real.sin_sq_add_cos_sq θ)
  · linear_combination (x 2)*(Real.sin_sq_add_cos_sq θ)
  · linear_combination (x 3)*(Real.sin_sq_add_cos_sq θ)

def rotationEquiv (θ : ℝ) : Block 4 ≃ₗ[ℝ] Block 4 where
  toFun := rotate θ
  invFun := rotate (-θ)
  left_inv := rotate_reverse θ
  right_inv x := by simpa only [neg_neg] using rotate_reverse (-θ) x
  map_add' x y := by ext i; fin_cases i <;> simp [rotate] <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp [rotate] <;> ring

theorem rotation_inner (θ : ℝ) (x y : Block 4) :
    inner ℝ (rotationEquiv θ x) (rotationEquiv θ y) = inner ℝ x y := by
  have h0 := KFCausalPairedRotation.pair_inner θ (x 0) (x 1) (y 0) (y 1)
  have h1 := KFCausalPairedRotation.pair_inner θ (x 2) (x 3) (y 2) (y 3)
  simp only [PiLp.inner_apply,Fin.sum_univ_succ]
  simp [rotationEquiv,rotate,RCLike.inner_apply]
  linear_combination h0+h1

def rotationIsometry (θ : ℝ) : Block 4 ≃ₗᵢ[ℝ] Block 4 where
  toLinearEquiv := rotationEquiv θ
  norm_map' := ((rotationEquiv θ).toLinearMap.isometryOfInner (rotation_inner θ)).norm_map

def dilate (c : ℝ) (x : Block 4) : Block 4 := WithLp.toLp 2 ![c*x 0,x 1,c*x 2,x 3]

def dilationEquiv (c : ℝ) (hc : c ≠ 0) : Block 4 ≃ₗ[ℝ] Block 4 where
  toFun := dilate c
  invFun := dilate c⁻¹
  left_inv x := by ext i; fin_cases i <;> simp [dilate,hc]
  right_inv x := by ext i; fin_cases i <;> simp [dilate,hc]
  map_add' x y := by ext i; fin_cases i <;> simp [dilate,mul_add]
  map_smul' d x := by ext i; fin_cases i <;> simp [dilate] <;> ring

def flow (c : ℝ) (hc : c ≠ 0) (θ : ℝ) : Block 4 ≃ᵐ Block 4 :=
  KFCausalHaarConjugation.conjugate (dilationEquiv c hc).toContinuousLinearEquiv
    (rotationIsometry θ).toMeasurableEquiv

theorem flow_apply (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Block 4) :
    flow c hc θ x = dilate c⁻¹ (rotate θ (dilate c x)) := rfl

theorem flow_preserves (c : ℝ) (hc : c ≠ 0) (θ : ℝ) : MeasurePreserving (flow c hc θ) :=
  KFCausalHaarConjugation.conjugate_preserves volume _ _ (rotationIsometry θ).measurePreserving

def chargedAction (c : ℝ) (hc : c ≠ 0) (θ : ℝ) : BlockHilbert 4 ≃ₗᵢ[ℂ] BlockHilbert 4 :=
  unitaryPullback (flow c hc θ) (flow_preserves c hc θ)

theorem chargedAction_coe (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (f : BlockHilbert 4) :
    chargedAction c hc θ f =ᵐ[volume] f ∘ flow c hc θ := unitaryPullback_coe _ _ _

def repack (x : Joint 2 4) : Joint 4 2 := WithLp.toLp 2 fun
  | .inl i => ![x (.inl 0),x (.inr 1),x (.inl 1),x (.inr 2)] i
  | .inr i => ![x (.inr 0),x (.inr 3)] i

def unpack (x : Joint 4 2) : Joint 2 4 := WithLp.toLp 2 fun
  | .inl i => ![x (.inl 0),x (.inl 2)] i
  | .inr i => ![x (.inr 0),x (.inl 1),x (.inl 3),x (.inr 1)] i

def repackEquiv : Joint 2 4 ≃ₗ[ℝ] Joint 4 2 where
  toFun := repack
  invFun := unpack
  left_inv x := by ext i; rcases i with i | i <;> fin_cases i <;> simp [unpack,repack]
  right_inv x := by ext i; rcases i with i | i <;> fin_cases i <;> simp [unpack,repack]
  map_add' x y := by ext i; rcases i with i | i <;> fin_cases i <;> simp [repack]
  map_smul' c x := by ext i; rcases i with i | i <;> fin_cases i <;> simp [repack]

theorem repack_inner (x y : Joint 2 4) :
    inner ℝ (repackEquiv x) (repackEquiv y) = inner ℝ x y := by
  simp only [PiLp.inner_apply,Fintype.sum_sum_type,Fin.sum_univ_succ]
  simp [repackEquiv,repack,RCLike.inner_apply]
  ring

def repackIsometry : Joint 2 4 ≃ₗᵢ[ℝ] Joint 4 2 where
  toLinearEquiv := repackEquiv
  norm_map' := (repackEquiv.toLinearMap.isometryOfInner repack_inner).norm_map

def assemble : (Block 4 × Block 2) ≃ᵐ Joint 2 4 :=
  (split 4 2).symm.trans repackIsometry.symm.toMeasurableEquiv

theorem assemble_apply (x : Block 4 × Block 2) : assemble x = WithLp.toLp 2 (fun
    | .inl i => ![x.1 0,x.1 2] i
    | .inr i => ![x.2 0,x.1 1,x.1 3,x.2 1] i) := rfl

theorem assemble_preserves : MeasurePreserving assemble :=
  repackIsometry.symm.measurePreserving.comp (split_preserves_volume 4 2).symm

def mixedCoordinates : JointHilbert 2 4 ≃ₗᵢ[ℂ] ProductHilbert 4 2 :=
  unitaryPullback assemble assemble_preserves

theorem mixedCoordinates_coe (f : JointHilbert 2 4) :
    mixedCoordinates f =ᵐ[volume] f ∘ assemble := unitaryPullback_coe _ _ _

def productFlow (c : ℝ) (hc : c ≠ 0) (θ : ℝ) : (Block 4 × Block 2) ≃ᵐ (Block 4 × Block 2) :=
  (flow c hc θ).prodCongr (MeasurableEquiv.refl _)

theorem productFlow_apply (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Block 4 × Block 2) :
    productFlow c hc θ x = (flow c hc θ x.1,x.2) := rfl

theorem productFlow_preserves (c : ℝ) (hc : c ≠ 0) (θ : ℝ) : MeasurePreserving (productFlow c hc θ) :=
  (flow_preserves c hc θ).prod (MeasurePreserving.id volume)

theorem assemble_flow (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Block 4 × Block 2) :
    KFCausalNormalizedChargeFlow.flowEquiv c hc θ (assemble x) = assemble (productFlow c hc θ x) := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [assemble_apply,productFlow_apply,
      KFCausalNormalizedChargeFlow.flow_apply,KFCausalNormalizedChargeFlow.dilate,
      KFCausalPairedRotation.rotate,flow_apply,dilate,rotate]

def productAction (c : ℝ) (hc : c ≠ 0) (θ : ℝ) : ProductHilbert 4 2 ≃ₗᵢ[ℂ] ProductHilbert 4 2 :=
  unitaryPullback (productFlow c hc θ) (productFlow_preserves c hc θ)

theorem mixed_action (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (f : JointHilbert 2 4) :
    mixedCoordinates (KFCausalMixedCircleAction.action c hc θ f) =
      productAction c hc θ (mixedCoordinates f) := by
  apply Lp.ext
  filter_upwards [mixedCoordinates_coe (KFCausalMixedCircleAction.action c hc θ f),
    assemble_preserves.quasiMeasurePreserving.ae (KFCausalMixedCircleAction.action_coe c hc θ f),
    unitaryPullback_coe (productFlow c hc θ) (productFlow_preserves c hc θ) (mixedCoordinates f),
    (productFlow_preserves c hc θ).quasiMeasurePreserving.ae (mixedCoordinates_coe f)] with x h1 h2 h3 h4
  exact h1.trans (h2.trans ((congrArg f (assemble_flow c hc θ x)).trans (h4.symm.trans h3.symm)))

theorem productAction_product (c : ℝ) (hc : c ≠ 0) (θ : ℝ)
    (f : BlockHilbert 4) (g : BlockHilbert 2) :
    productAction c hc θ (productState volume volume f g) =
      productState volume volume (chargedAction c hc θ f) g := by
  apply Lp.ext
  filter_upwards [unitaryPullback_coe (productFlow c hc θ) (productFlow_preserves c hc θ)
      (productState volume volume f g),
    (productFlow_preserves c hc θ).quasiMeasurePreserving.ae (productState_coe volume volume f g),
    productState_coe volume volume (chargedAction c hc θ f) g,
    Measure.quasiMeasurePreserving_fst.ae (chargedAction_coe c hc θ f)] with x h1 h2 h3 h4
  exact h1.trans (h2.trans (h3.trans (congrArg (fun y => y*g x.2) h4)).symm)

theorem productAction_eq_lift (c : ℝ) (hc : c ≠ 0) (θ : ℝ) :
    productAction c hc θ = KFCausalEuclideanTensorUnitary.liftUnitary 4 2
      (chargedAction c hc θ) (LinearIsometryEquiv.refl ℂ _) := by
  apply KFCausalEuclideanTensorUnitary.unitary_eq_on_products
  intro f g
  exact (productAction_product c hc θ f g).trans
    (KFCausalEuclideanTensorUnitary.liftUnitary_product 4 2
      (chargedAction c hc θ) (LinearIsometryEquiv.refl ℂ _) f g).symm

def physicalCoordinates : KFCausalConfigurationTestSpace.Hilbert ≃ₗᵢ[ℂ] ProductHilbert 4 2 :=
  KFCausalPhysicalCircleAction.chargeCoordinates.trans mixedCoordinates

theorem physical_action (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f : KFCausalConfigurationTestSpace.Hilbert) :
    physicalCoordinates (KFCausalPhysicalCircleAction.action h hh θ f) =
      KFCausalEuclideanTensorUnitary.liftUnitary 4 2
        (chargedAction (KFCausalNormalizedChargeFlow.momentumScale h)
          (KFCausalNormalizedChargeFlow.momentumScale_ne_zero h hh) θ)
        (LinearIsometryEquiv.refl ℂ _) (physicalCoordinates f) := by
  change mixedCoordinates (KFCausalPhysicalCircleAction.chargeCoordinates
    (KFCausalPhysicalCircleAction.action h hh θ f)) = _
  rw [KFCausalPhysicalCircleAction.action_coordinates,mixed_action,productAction_eq_lift]
  rfl

#print axioms rotation_inner
#print axioms flow_preserves
#print axioms assemble_flow
#print axioms mixed_action
#print axioms productAction_eq_lift
#print axioms physical_action
end
end UnifiedTheory.Audit.KFCausalChargedSpectatorCoordinates
