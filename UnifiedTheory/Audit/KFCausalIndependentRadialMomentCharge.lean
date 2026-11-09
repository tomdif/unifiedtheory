/- The linked radial moment states remain in the actual zero-charge
sector. This is an exact symmetry assertion, not a Hamiltonian domain claim. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialPacketMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalIndependentRadialMomentCharge
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalIndependentRadialPacketDerivatives (leftRadius rightRadius momentProfile)
open KFCausalIndependentRadialPacketMoments (momentState momentState_charge_coe)
open KFCausalNormalizedChargeFlow (momentumScale momentumScale_ne_zero flowEquiv flow_preserves_volume)
open KFCausalChargeGaussianGeometry (radius radius_coordinates radius_flow)
open KFCausalChargeZeroSwapWitness (imbalance imbalance_flow)
open KFCausalPhysicalCircleAction (chargeCoordinates action action_coordinates)
open KFCausalStandingChargeOperator (zeroSector)

private theorem radius_decomposition (c : ℝ) (x : Joint 2 4) :
    leftRadius c x=(radius c x+imbalance c x)/2 ∧
      rightRadius c x=(radius c x-imbalance c x)/2 := by
  simp only [radius_coordinates,imbalance,KFCausalChargeZeroSwapWitness.imbalanceRaw,
    KFCausalNormalizedChargeFlow.dilate,leftRadius,rightRadius]
  constructor <;> ring

theorem radii_flow (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Joint 2 4) :
    leftRadius c (flowEquiv c hc θ x)=leftRadius c x ∧
      rightRadius c (flowEquiv c hc θ x)=rightRadius c x := by
  obtain ⟨hl,hr⟩ := radius_decomposition c (flowEquiv c hc θ x)
  obtain ⟨hl',hr'⟩ := radius_decomposition c x
  rw [radius_flow,imbalance_flow,← hl'] at hl
  rw [radius_flow,imbalance_flow,← hr'] at hr
  exact ⟨hl,hr⟩

theorem momentProfile_flow (α β wL wR c : ℝ) (hc : c ≠ 0) (b : ℂ)
    (P : Polynomial ℂ) (g : ℝ → ℂ) (m n : ℕ) (θ : ℝ) (x : Joint 2 4) :
    momentProfile α β wL wR c b P g m n (flowEquiv c hc θ x)=
      momentProfile α β wL wR c b P g m n x := by
  rw [momentProfile,(radii_flow c hc θ x).1,(radii_flow c hc θ x).2,
    KFCausalIndependentRadialPacketProfiles.chargeProfile_flow]
  rfl

theorem momentState_action (ε a h wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hL : 1 ≤ wL) (hR : 1 ≤ wR)
    (m n : ℕ) (θ : ℝ) :
    action h hh θ (momentState ε a h wL wR C p b P hε ha hh hL hR m n)=
      momentState ε a h wL wR C p b P hε ha hh hL hR m n := by
  apply chargeCoordinates.injective
  rw [action_coordinates]
  apply Lp.ext
  have he := momentState_charge_coe ε a h wL wR C p b P hε ha hh hL hR m n
  filter_upwards [KFCausalMixedCircleAction.action_coe (momentumScale h) (momentumScale_ne_zero h hh) θ _,
    (flow_preserves_volume (momentumScale h) (momentumScale_ne_zero h hh) θ).quasiMeasurePreserving.ae he,he]
    with x hx hy hz
  simp only [Function.comp_apply] at hx
  rw [hx,hy,momentProfile_flow,hz]

theorem momentState_zeroSector (ε a h wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hL : 1 ≤ wL) (hR : 1 ≤ wR) (m n : ℕ) :
    momentState ε a h wL wR C p b P hε ha hh hL hR m n ∈ zeroSector h hh :=
  momentState_action ε a h wL wR C p b P hε ha hh hL hR m n

#print axioms radii_flow
#print axioms momentProfile_flow
#print axioms momentState_action
#print axioms momentState_zeroSector
end
end UnifiedTheory.Audit.KFCausalIndependentRadialMomentCharge
