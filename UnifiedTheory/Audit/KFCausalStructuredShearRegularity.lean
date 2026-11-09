/- Smooth representatives of the initial structured endpoint. Independent
widths, displacements and complex coefficients are retained. -/
import UnifiedTheory.Audit.KFCausalStructuredShearInterpolation
import UnifiedTheory.Audit.KFCausalImaginaryShearInitialRegularity

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalStructuredShearRegularity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint JointHilbert)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow (dilate momentumScale)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (weight weight_coe)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedStates (state rawState operator_coordinates state_normalization)
open UnifiedTheory.Audit.KFCausalImaginaryShearInitialEndpoint (initialOperator initialOperator_coordinates)
open UnifiedTheory.Audit.KFCausalImaginaryShearInitialMultiplier (symbol symbol_smooth)
open UnifiedTheory.Audit.KFCausalImaginaryShearInitialRegularity (weight_smooth finite_representatives)
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse (StructuredState)

def SmoothRepresentative (f : Hilbert) : Prop :=
  ∃ φ : Joint 2 4 → ℂ, chargeCoordinates f =ᵐ[volume] φ ∧ ContDiff ℝ 1 φ

theorem displaced_smooth (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (q k : Joint 2 4) : SmoothRepresentative (state ε a h hε ha hh q k) := by
  let φ : Joint 2 4 → ℂ := fun x =>
    KFCausalFourierTranslation.phase (dilate (momentumScale h) k) x *
      weight ε a h (x+dilate (momentumScale h)⁻¹ q)
  have hφ : chargeCoordinates (rawState ε a h hε ha hh q k) =ᵐ[volume] φ := by
    rw [rawState,operator_coordinates]
    filter_upwards [KFCausalChargeDisplacementCovariance.displacement_coe (momentumScale h) q k
        (chargeCoordinates (KFCausalClockFloorInvariantTrial.trialState ε a h hε ha hh)),
      (KFCausalFourierTranslation.shift_preserves_volume (dilate (momentumScale h)⁻¹ q)).quasiMeasurePreserving.ae
        (weight_coe ε a h hε ha hh)] with x hx hy
    exact hx.trans (congrArg (fun z : ℂ => KFCausalFourierTranslation.phase (dilate (momentumScale h) k) x*z) hy)
  have hs : ContDiff ℝ 1 φ := by
    have hi : ContDiff ℝ 1 (fun x : Joint 2 4 =>
        2*Real.pi*inner ℝ (dilate (momentumScale h) k) x) :=
      contDiff_const.mul (contDiff_const.inner ℝ contDiff_id)
    exact ((Complex.ofRealCLM.contDiff.comp hi).mul contDiff_const).cexp.mul
      ((weight_smooth ε a h).comp (contDiff_id.add contDiff_const))
  let N : ℝ := ‖KFCausalClockFloorInvariantTrial.trialState ε a h hε ha hh‖⁻¹
  refine ⟨fun x => (N:ℂ)*φ x,?_,contDiff_const.mul hs⟩
  rw [state_normalization]
  change chargeCoordinates ((N:ℂ) • rawState ε a h hε ha hh q k) =ᵐ[volume] _
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul (N:ℂ) (chargeCoordinates (rawState ε a h hε ha hh q k)),hφ] with x hx hy
  simp only [hx,Pi.smul_apply,smul_eq_mul,hy]

theorem initial_smooth (ε a p h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3)
    (f : Hilbert) (hf : SmoothRepresentative f) :
    SmoothRepresentative (initialOperator ε a p h hε hb f) := by
  obtain ⟨φ,hφ,hs⟩ := hf
  refine ⟨fun x => symbol ε a p h (x (.inr 0))*φ x,?_,
    ((symbol_smooth ε a p h hε hb).comp (by fun_prop)).mul hs⟩
  filter_upwards [initialOperator_coordinates ε a p h hε hb f,hφ] with x hx hy
  rw [hx,hy]

theorem finite_smooth {n : ℕ} (f : Fin n → Hilbert) (z : Fin n → ℂ)
    (hf : ∀ i, SmoothRepresentative (f i)) : SmoothRepresentative (∑ i, z i • f i) := by
  choose φ hφ hs using hf
  refine ⟨fun x => ∑ i, z i*φ i x,?_,ContDiff.sum (fun i _ => contDiff_const.mul (hs i))⟩
  rw [map_sum]
  apply finite_representatives
  intro i
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul (z i) (chargeCoordinates (f i)),hφ i] with x hx hy
  simp only [hx,Pi.smul_apply,smul_eq_mul,hy]

theorem initial_structured_smooth (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (S : StructuredState) (θ : ℝ) :
    SmoothRepresentative (KFCausalStructuredShearInterpolation.input ε h hε hh hb S θ 0) := by
  rw [KFCausalStructuredShearInterpolation.input_zero]
  apply finite_smooth
  intro i
  exact initial_smooth _ _ _ _ hε hb _
    (displaced_smooth ε (S.packet i).width h hε (S.packet i).width_pos hh _ _)

#print axioms displaced_smooth
#print axioms initial_smooth
#print axioms finite_smooth
#print axioms initial_structured_smooth
end
end UnifiedTheory.Audit.KFCausalStructuredShearRegularity
