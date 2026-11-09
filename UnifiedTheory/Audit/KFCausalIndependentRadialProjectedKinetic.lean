/- The actual continuous charge projection of kinetic packet outputs is
identified by four finite rotations and invariant radial representatives. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialKineticRepresentatives
import UnifiedTheory.Audit.KFCausalIndependentRadialMomentCharge
import UnifiedTheory.Audit.KFCausalIndependentRadialHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalIndependentRadialProjectedKinetic
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalNormalizedChargeFlow (momentumScale momentumScale_ne_zero flowEquiv flow_first_plane flow_second_plane)
open KFCausalStandingChargeOperator (zeroSector zeroProjection)
open KFCausalChargeRepresentativeAlgebra (add_coe smul_coe four four_coe projection_of_four fixed_of_rep four_inverse inverse_fixed)
open KFCausalIndependentRadialPacketProfiles (chargeProfile chargeProfile_flow)
open KFCausalIndependentRadialPacketDerivatives (momentProfile leftRadius rightRadius)
open KFCausalIndependentRadialPacketMoments (genericMomentState generic_charge_coe)
open KFCausalIndependentRadialMomentCharge (momentProfile_flow)
open KFCausalIndependentRadialKineticProfiles (position rate neutral radius fourAverage secondProfile_fourAverage)
open KFCausalIndependentRadialKineticRepresentatives (baseState singleState secondState base_coe single_coe second_coe antiFactor)
open KFCausalIndependentRadialCoordinateMoments (coordinate)
open KFCausalNeutralLinePackets (step)
open KFCausalClockFloorBoundedInverse (inverseL)

variable (α β wL wR h : ℝ) (hα : 0 < α) (hβ : 0 < β) (hL : 0 < wL) (hR : 0 < wR)
  (hh : h ≠ 0) (hmatch : Real.pi^2/α=α*(momentumScale h)^2)
  (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume)
local notation "c" => momentumScale h
local notation "B" => (fun Q : Polynomial ℂ => baseState α β wL wR c hα hβ hL hR hmatch b Q g hc hg)
local notation "S" => secondState α β wL wR c hα hβ hL hR hmatch b P g hc hg

def radialState (i : Fin 2) : Hilbert :=
  ![genericMomentState α β wL wR c hα hβ hL hR hmatch b P g hc hg 1 0,
    genericMomentState α β wL wR c hα hβ hL hR hmatch b P g hc hg 0 1] i

theorem radial_coe (i : Fin 2) :
    chargeCoordinates (radialState α β wL wR h hα hβ hL hR hmatch b P g hc hg i)=ᵐ[volume]
      fun x => (radius c i x:ℂ)*chargeProfile α β wL wR c b P g x := by
  fin_cases i
  · change chargeCoordinates (genericMomentState α β wL wR c hα hβ hL hR hmatch b P g hc hg 1 0)=ᵐ[volume]
      fun x => (leftRadius c x:ℂ)*chargeProfile α β wL wR c b P g x
    filter_upwards [generic_charge_coe α β wL wR c hα hβ hL hR hmatch b P g hc hg 1 0] with x hx
    simpa only [momentProfile,pow_one,pow_zero,mul_one] using hx
  · change chargeCoordinates (genericMomentState α β wL wR c hα hβ hL hR hmatch b P g hc hg 0 1)=ᵐ[volume]
      fun x => (rightRadius c x:ℂ)*chargeProfile α β wL wR c b P g x
    filter_upwards [generic_charge_coe α β wL wR c hα hβ hL hR hmatch b P g hc hg 0 1] with x hx
    simpa only [momentProfile,pow_one,pow_zero,one_mul] using hx

private theorem base_fixed : B P ∈ zeroSector h hh :=
  fixed_of_rep h hh _ _ (base_coe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (chargeProfile_flow α β wL wR c (momentumScale_ne_zero h hh) b P g)

private theorem radial_fixed (i : Fin 2) :
    radialState α β wL wR h hα hβ hL hR hmatch b P g hc hg i ∈ zeroSector h hh := by
  fin_cases i
  · exact fixed_of_rep h hh _ _ (generic_charge_coe α β wL wR c hα hβ hL hR hmatch b P g hc hg 1 0)
      (momentProfile_flow α β wL wR c (momentumScale_ne_zero h hh) b P g 1 0)
  · exact fixed_of_rep h hh _ _ (generic_charge_coe α β wL wR c hα hβ hL hR hmatch b P g hc hg 0 1)
      (momentProfile_flow α β wL wR c (momentumScale_ne_zero h hh) b P g 0 1)

def averageSecond (i : Fin 2) : Hilbert :=
  (-4*(α:ℂ)*(rate wL wR i:ℂ)) • B P+
    (4*((α:ℂ)*(rate wL wR i:ℂ))^2) • radialState α β wL wR h hα hβ hL hR hmatch b P g hc hg i+
    (neutral i:ℂ) • B (step β b (step β b P))

theorem four_second (i : Fin 2) :
    four h hh (S i)=averageSecond α β wL wR h hα hβ hL hR hmatch b P g hc hg i := by
  have ht := add_coe _ _ _ _ (add_coe _ _ _ _
    (smul_coe (-4*(α:ℂ)*(rate wL wR i:ℂ)) _ _ (base_coe α β wL wR c hα hβ hL hR hmatch b P g hc hg))
    (smul_coe (4*((α:ℂ)*(rate wL wR i:ℂ))^2) _ _ (radial_coe α β wL wR h hα hβ hL hR hmatch b P g hc hg i)))
    (smul_coe (neutral i:ℂ) _ _ (base_coe α β wL wR c hα hβ hL hR hmatch b (step β b (step β b P)) g hc hg))
  apply chargeCoordinates.injective
  apply Lp.ext
  filter_upwards [four_coe h hh (S i) _ (second_coe α β wL wR c hα hβ hL hR hmatch b P g hc hg i),ht]
    with x hx ht
  change (chargeCoordinates (four h hh (S i))) x=_
  change (chargeCoordinates (averageSecond α β wL wR h hα hβ hL hR hmatch b P g hc hg i)) x=_ at ht
  rw [hx,ht,secondProfile_fourAverage]
  ring

private theorem averageSecond_fixed (i : Fin 2) :
    averageSecond α β wL wR h hα hβ hL hR hmatch b P g hc hg i ∈ zeroSector h hh :=
  Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (base_fixed α β wL wR h hα hβ hL hR hh hmatch b P g hc hg))
    (Submodule.smul_mem _ _ (radial_fixed α β wL wR h hα hβ hL hR hh hmatch b P g hc hg i)))
    (Submodule.smul_mem _ _ (base_fixed α β wL wR h hα hβ hL hR hh hmatch b (step β b (step β b P)) g hc hg))

private theorem anti_position_flow (i : Fin 2) (θ : ℝ) (x : Joint 2 4) :
    c*(flowEquiv c (momentumScale_ne_zero h hh) θ x) (.inl i)=
      Real.cos θ*(c*x (.inl i))-Real.sin θ*position i x := by
  have hz := momentumScale_ne_zero h hh
  fin_cases i
  · have he := congrArg Prod.fst (flow_first_plane c hz θ x)
    change (flowEquiv c hz θ x) (.inl 0)=Real.cos θ*x (.inl 0)-Real.sin θ*x (.inr 1)/c at he
    change c*(flowEquiv c hz θ x) (.inl 0)=Real.cos θ*(c*x (.inl 0))-Real.sin θ*x (.inr 1)
    rw [he]
    field_simp
  · have he := congrArg Prod.fst (flow_second_plane c hz θ x)
    change (flowEquiv c hz θ x) (.inl 1)=Real.cos θ*x (.inl 1)-Real.sin θ*x (.inr 2)/c at he
    change c*(flowEquiv c hz θ x) (.inl 1)=Real.cos θ*(c*x (.inl 1))-Real.sin θ*x (.inr 2)
    rw [he]
    field_simp

theorem four_anti (i : Fin 2) :
    four h hh (singleState α β wL wR c hα hβ hL hR hmatch b P g hc hg i.castSucc.castSucc 2)=
      (1/2:ℂ) • radialState α β wL wR h hα hβ hL hR hmatch b P g hc hg i := by
  have hi (x : Joint 2 4) : coordinate c x i.castSucc.castSucc=c*x (.inl i) := by fin_cases i <;> rfl
  apply chargeCoordinates.injective
  apply Lp.ext
  filter_upwards [four_coe h hh _ _ (single_coe α β wL wR c hα hβ hL hR hmatch b P g hc hg i.castSucc.castSucc 2),
    smul_coe (1/2:ℂ) _ _ (radial_coe α β wL wR h hα hβ hL hR hmatch b P g hc hg i)] with x hx ht
  rw [hx,ht]
  unfold fourAverage
  simp only [hi,chargeProfile_flow α β wL wR c (momentumScale_ne_zero h hh),anti_position_flow h hh,
    neg_div,Real.cos_pi_div_two,Real.sin_pi_div_two,Real.cos_pi,Real.sin_pi,Real.cos_neg,Real.sin_neg,
    zero_mul,one_mul,zero_sub,sub_zero]
  have hr : (radius c i x:ℂ)=(c:ℂ)^2*(x (.inl i):ℂ)^2+(position i x:ℂ)^2 := by
    fin_cases i <;> simp [radius,leftRadius,rightRadius,position]
  rw [hr]
  push_cast
  ring

theorem projected_symmetric (ε : ℝ) (hε : 0 < ε) (i : Fin 2) :
    zeroProjection h hh (inverseL ε hε (inverseL ε hε ((-(h:ℂ)^2) • S i)))=
      inverseL ε hε (inverseL ε hε ((-(h:ℂ)^2) •
        averageSecond α β wL wR h hα hβ hL hR hmatch b P g hc hg i)) := by
  have he : zeroProjection h hh (inverseL ε hε (inverseL ε hε (S i)))=
      inverseL ε hε (inverseL ε hε (averageSecond α β wL wR h hα hβ hL hR hmatch b P g hc hg i)) :=
    projection_of_four h hh _ _ (by rw [four_inverse,four_inverse,four_second])
      (inverse_fixed ε hε h hh _ (inverse_fixed ε hε h hh _
        (averageSecond_fixed α β wL wR h hα hβ hL hR hh hmatch b P g hc hg i)))
  simp only [map_smul,he]

include hh in
theorem antiFactor_square : (antiFactor h c)^2=2 := by
  have he : antiFactor h c=2*(KFCausalPairedModeCoordinates.scale:ℂ) := by
    unfold antiFactor KFCausalNormalizedChargeFlow.momentumScale
    have hp : Real.pi ≠ 0 := Real.pi_ne_zero
    have hz : 2*Real.pi*h ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hp) hh
    rw [mul_div_cancel_left₀ _ hz]
    push_cast
    rfl
  rw [he,mul_pow,← Complex.ofReal_pow,KFCausalPairedModeCoordinates.scale_square]
  norm_num

theorem projected_antisymmetric (ε : ℝ) (hε : 0 < ε) (i : Fin 2) :
    zeroProjection h hh (inverseL ε hε (inverseL ε hε ((antiFactor h c)^2 •
      singleState α β wL wR c hα hβ hL hR hmatch b P g hc hg i.castSucc.castSucc 2)))=
      inverseL ε hε (inverseL ε hε (radialState α β wL wR h hα hβ hL hR hmatch b P g hc hg i)) := by
  have he := projection_of_four h hh _ _
    (show four h hh (inverseL ε hε (inverseL ε hε
      (singleState α β wL wR c hα hβ hL hR hmatch b P g hc hg i.castSucc.castSucc 2)))=
      inverseL ε hε (inverseL ε hε ((1/2:ℂ) • radialState α β wL wR h hα hβ hL hR hmatch b P g hc hg i)) by
        rw [four_inverse,four_inverse,four_anti])
    (inverse_fixed ε hε h hh _ (inverse_fixed ε hε h hh _
      (Submodule.smul_mem _ _ (radial_fixed α β wL wR h hα hβ hL hR hh hmatch b P g hc hg i))))
  rw [antiFactor_square h hh]
  simp only [map_smul,he,smul_smul]
  norm_num

#print axioms radial_coe
#print axioms four_second
#print axioms four_anti
#print axioms projected_symmetric
#print axioms antiFactor_square
#print axioms projected_antisymmetric
end
end UnifiedTheory.Audit.KFCausalIndependentRadialProjectedKinetic
