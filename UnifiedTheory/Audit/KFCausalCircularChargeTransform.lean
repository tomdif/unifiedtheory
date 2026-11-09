/- The actual six-dimensional physical charge is diagonal in a derived
complete circular basis; clock and neutral frequency remain continuous. -/
import UnifiedTheory.Audit.KFCausalFourCircularChargeBasis
import UnifiedTheory.Audit.KFCausalJointHermiteFourierTransform

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCircularChargeTransform
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates
open KFCausalHermiteProductBasis (Index)
open KFCausalL2TensorEmbedding (productState)
open KFCausalProductHilbertExpansion (partialTransform coefficient_inner)
open KFCausalChargedSpectatorCoordinates (physicalCoordinates chargedAction)
open KFCausalEuclideanTensorUnitary (liftUnitary liftUnitary_product)
open KFCausalNormalizedChargeFlow (momentumScale momentumScale_ne_zero)
open KFCausalJointHermiteFourierTransform (Coefficients neutralFourier neutralFourierBlock)
open KFCausalCircularChargeBasis (phase phase_unit)
open KFCausalFourCircularChargeBasis (charge)

private theorem inner_eigen {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : H ≃ₗᵢ[ℂ] H) (x y : H) (α : ℂ) (hα : α*star α = 1) (hx : U x = α • x) :
    inner ℂ x (U y) = α*inner ℂ x y := by
  have he := U.inner_map_map x y
  rw [hx,inner_smul_left] at he
  change star α*inner ℂ x (U y) = inner ℂ x y at he
  calc
    _ = (α*star α)*inner ℂ x (U y) := by rw [hα,one_mul]
    _ = α*(star α*inner ℂ x (U y)) := mul_assoc _ _ _
    _ = _ := by rw [he]

variable (h : ℝ) (hh : h ≠ 0) (b : ℝ) (hb : 0 < b)
local notation "c" => momentumScale h
local notation "hc" => momentumScale_ne_zero h hh
local notation "B" => KFCausalFourCircularChargeBasis.basis c hc b hb
local notation "T" => partialTransform 4 2 B

def transform : Hilbert ≃ₗᵢ[ℂ] Coefficients := physicalCoordinates.trans (neutralFourier.trans T)

theorem partial_diagonal (θ : ℝ) (f : ProductHilbert 4 2) (i : Index) :
    T (liftUnitary 4 2 (chargedAction c hc θ) (LinearIsometryEquiv.refl ℂ _) f) i =
      phase (charge i) θ • T f i := by
  apply ext_inner_left ℂ
  intro g
  rw [← coefficient_inner,inner_smul_right,← coefficient_inner]
  apply inner_eigen (liftUnitary 4 2 (chargedAction c hc θ) (LinearIsometryEquiv.refl ℂ _))
    (productState volume volume (B i) g) f _ (phase_unit (charge i) θ)
  exact (liftUnitary_product 4 2 (chargedAction c hc θ) (LinearIsometryEquiv.refl ℂ _) (B i) g).trans
    ((congrArg (fun z => productState volume volume z g)
      (KFCausalFourCircularChargeBasis.basis_action c hc b hb θ i)).trans
        (KFCausalL2TensorEmbedding.productState_smul_left volume volume _ _ _))

/-- Exact diagonal action for every physical Hilbert state. -/
theorem action_diagonal (θ : ℝ) (f : Hilbert) (i : Index) :
    transform h hh b hb (KFCausalPhysicalCircleAction.action h hh θ f) i =
      phase (charge i) θ • transform h hh b hb f i := by
  change T (neutralFourier (physicalCoordinates (KFCausalPhysicalCircleAction.action h hh θ f))) i = _
  rw [KFCausalChargedSpectatorCoordinates.physical_action]
  change T (liftUnitary 4 2 (LinearIsometryEquiv.refl ℂ _) neutralFourierBlock
    (liftUnitary 4 2 (chargedAction c hc θ) (LinearIsometryEquiv.refl ℂ _) (physicalCoordinates f))) i = _
  rw [← KFCausalEuclideanTensorUnitary.independent_actions_commute]
  exact partial_diagonal h hh b hb θ _ i

def packet (i : Index) (g : BlockHilbert 2) : Hilbert :=
  (transform h hh b hb).symm (lp.single 2 i g)

theorem transform_packet (i : Index) (g : BlockHilbert 2) :
    transform h hh b hb (packet h hh b hb i g) = lp.single 2 i g :=
  (transform h hh b hb).apply_symm_apply _

theorem packet_smul (i : Index) (z : ℂ) (g : BlockHilbert 2) :
    packet h hh b hb i (z • g) = z • packet h hh b hb i g := by
  unfold packet
  rw [lp.single_smul,map_smul]

theorem packet_action (θ : ℝ) (i : Index) (g : BlockHilbert 2) :
    KFCausalPhysicalCircleAction.action h hh θ (packet h hh b hb i g) =
      phase (charge i) θ • packet h hh b hb i g := by
  apply (transform h hh b hb).injective
  apply lp.ext
  funext j
  rw [action_diagonal,map_smul,transform_packet]
  change phase (charge j) θ • ((lp.single 2 i g:Coefficients) j) =
    phase (charge i) θ • ((lp.single 2 i g:Coefficients) j)
  by_cases hij : i = j
  · subst j
    rfl
  · simp [lp.single_apply,hij,Ne.symm hij]

theorem reconstruction (f : Hilbert) :
    HasSum (fun i => packet h hh b hb i (transform h hh b hb f i)) f := by
  have hs := (transform h hh b hb).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasSum
    (lp.hasSum_single (by norm_num : (2:ENNReal) ≠ ⊤) (transform h hh b hb f))
  change HasSum (fun i => packet h hh b hb i (transform h hh b hb f i))
    ((transform h hh b hb).symm (transform h hh b hb f)) at hs
  simpa only [LinearIsometryEquiv.symm_apply_apply] using hs

theorem phase_derivative (q : ℤ) : HasDerivAt (phase q) (Complex.I*(q:ℂ)) 0 := by
  change HasDerivAt (fun θ : ℝ => Complex.exp (Complex.ofReal ((q:ℝ)*θ)*Complex.I)) _ 0
  have hd := (((hasDerivAt_id (0:ℝ)).const_mul (q:ℝ)).ofReal_comp.mul_const Complex.I).cexp
  simpa only [id_eq,mul_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_mul,mul_one,
    Complex.ofReal_intCast,mul_comm] using hd

theorem packet_charge_graph (i : Index) (g : BlockHilbert 2) :
    (packet h hh b hb i g,(charge i:ℂ) • packet h hh b hb i g) ∈
      (KFCausalStandingChargeOperator.standingCharge h hh).graph := by
  rw [KFCausalStandingChargeOperator.standingCharge_graph]
  simpa only [packet_action,smul_smul] using
    (phase_derivative (charge i)).smul_const (packet h hh b hb i g)

#print axioms transform
#print axioms action_diagonal
#print axioms packet_action
#print axioms reconstruction
#print axioms packet_charge_graph
end
end UnifiedTheory.Audit.KFCausalCircularChargeTransform
