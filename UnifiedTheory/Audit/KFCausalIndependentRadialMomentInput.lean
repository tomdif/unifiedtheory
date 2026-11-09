/- Exact bare mixed-coordinate input of the actual independent radial
moment states. The numerator represents D psi, with no additional clock
inverse or prior vacuum action. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialPacketMoments
import UnifiedTheory.Audit.KFCausalIndependentRadialHolomorphicQuotient
import UnifiedTheory.Audit.KFCausalBroadPairedHolomorphicBaseline
import UnifiedTheory.Audit.KFCausalChargeRotatedSecondInput

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalIndependentRadialMomentInput
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates (Joint Block split)
open KFCausalComplexShearPerturbation (Space)
open KFCausalComplexQuadraticPerturbation (quadratic)
open KFCausalIndependentRadialNormalization (normalize normalize_mixedMap)
open KFCausalIndependentRadialHolomorphicQuotient (baselineVector)
open KFCausalIndependentRadialPacketDerivatives (leftRadius rightRadius momentProfile)
open KFCausalIndependentRadialPacketProfiles (chargeProfile chargeQuadratic_coordinates)
open KFCausalIndependentRadialPacketMoments (momentState momentState_charge_coe)
open KFCausalIndependentRadialPackets (clock)
open KFCausalClockFloorCoherentStrip (clockPhase)
open KFCausalComplexClockInverse (complexInverse)
open KFCausalClockFloorMixedChart (mixedMap)
open KFCausalClockFloorPairedStraightening (clockInverse)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorMixedRadial (clockMixed)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth)
open KFCausalNormalizedChargeFlow (momentumScale)

def left (α wL : ℝ) (Y : Space) : ℂ := (Y 0^2+Y 2^2)/(α/wL:ℝ)
def right (α wR : ℝ) (Y : Space) : ℂ := (Y 1^2+Y 3^2)/(α*wR:ℝ)
def neutral (α : ℝ) (Y : Space) : ℂ := Y 4/(Real.sqrt (α/32):ℂ)

def numerator (ε a α wL wR c : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (m n : ℕ) (q : ℂ) (x : Joint 2 4) : ℂ :=
  let Y := baselineVector ε α wL wR c q x
  left α wL Y^m*right α wR Y^n*
    ((Real.pi/α:ℝ)*C*clockPhase p (complexInverse ε q)*Complex.exp (-complexInverse ε q)*
      Complex.exp (-(a:ℂ)*q^2)*Complex.exp (-quadratic (fun i => Y i))*
      Complex.exp (b*neutral α Y)*P.eval (neutral α Y))

theorem normalized_coordinates (α wL wR c : ℝ) (hα : 0 < α) (hL : 0 < wL)
    (hR : 0 < wR) (x : Joint 2 4) :
    left α wL (normalize α wL wR c x)=(leftRadius c x:ℂ) ∧
    right α wR (normalize α wL wR c x)=(rightRadius c x:ℂ) ∧
    neutral α (normalize α wL wR c x)=(x (.inr 3):ℂ) ∧
    quadratic (fun i => normalize α wL wR c x i)=
      (α:ℂ)*((1/wL:ℝ)*(leftRadius c x:ℂ)+(wR:ℂ)*(rightRadius c x:ℂ))+
        (α/32:ℝ)*(x (.inr 3):ℂ)^2 := by
  have hs : (Real.sqrt (α/wL):ℂ)^2=(α/wL:ℝ) := by
    exact_mod_cast Real.sq_sqrt (div_nonneg hα.le hL.le)
  have ht : (Real.sqrt (α*wR):ℂ)^2=(α*wR:ℝ) := by
    exact_mod_cast Real.sq_sqrt (mul_nonneg hα.le hR.le)
  have hn : (Real.sqrt (α/32):ℂ)^2=(α/32:ℝ) := by
    exact_mod_cast Real.sq_sqrt (show 0 ≤ α/32 by positivity)
  have hz : (Real.sqrt (α/32):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  simp only [left,right,neutral,KFCausalIndependentRadialNormalization.normalize,quadratic,Fin.sum_univ_succ,
    Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ]
  push_cast
  simp only [mul_pow,hs,ht,hn]
  refine ⟨?_,?_,?_,?_⟩
  · unfold leftRadius
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hα.ne',Complex.ofReal_ne_zero.mpr hL.ne']
  · unfold rightRadius
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hα.ne',Complex.ofReal_ne_zero.mpr hR.ne']
  · exact mul_div_cancel_left₀ _ hz
  · unfold leftRadius rightRadius
    push_cast
    ring

theorem normalized_input (ε a α wL wR c : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (m n : ℕ) (hε : 0 < ε) (hα : 0 < α)
    (hL : 0 < wL) (hR : 0 < wR) (x : Block 2 × Block 4) :
    ((Real.exp (clockInverse ε hε x.2)+ε:ℝ):ℂ)⁻¹*
      momentProfile α (α/32) wL wR c b P (clock ε a C p) m n
        ((split 2 4).symm (mixedMap ε hε x)) =
      numerator ε a α wL wR c C p b P m n (x.2 0:ℂ) ((split 2 4).symm x) := by
  let s := clockInverse ε hε x.2
  let Z := (split 2 4).symm (mixedMap ε hε x)
  have hY : baselineVector ε α wL wR c (x.2 0:ℂ) ((split 2 4).symm x)=
      normalize α wL wR c Z := by
    unfold baselineVector
    rw [KFCausalComplexClockInverse.complexInverse_real ε hε]
    exact (normalize_mixedMap ε hε α wL wR c hα hR x).symm
  obtain ⟨hl,hr,hn,hq⟩ := normalized_coordinates α wL wR c hα hL hR Z
  have hc : Z (.inr 0)=s := rfl
  have hchart : KFCausalRegularizedLongitudinalChart.chart ε s=x.2 0 :=
    (KFCausalRegularizedLongitudinalChart.chartIso ε hε).apply_symm_apply _
  have hclock := KFCausalBroadPairedHolomorphicBaseline.clock_cancellation ε a s hε
  rw [hchart] at hclock
  unfold numerator
  dsimp only
  rw [hY,hl,hr,hn,hq,KFCausalComplexClockInverse.complexInverse_real ε hε]
  change _ = (leftRadius c Z:ℂ)^m*(rightRadius c Z:ℂ)^n*
    ((Real.pi/α:ℝ)*C*clockPhase p (s:ℂ)*Complex.exp (-(s:ℂ))*
      Complex.exp (-(a:ℂ)*(x.2 0:ℂ)^2)*
      Complex.exp (-((α:ℂ)*((1/wL:ℝ)*(leftRadius c Z:ℂ)+(wR:ℂ)*(rightRadius c Z:ℂ))+
        (α/32:ℝ)*(Z (.inr 3):ℂ)^2))*Complex.exp (b*(Z (.inr 3):ℂ))*P.eval (Z (.inr 3):ℂ))
  change ((Real.exp s+ε:ℝ):ℂ)⁻¹*momentProfile α (α/32) wL wR c b P (clock ε a C p) m n Z=_
  simp only [momentProfile,chargeProfile,chargeQuadratic_coordinates,clock,hc,
    KFCausalNeutralLinePackets.packet,KFCausalNeutralLinePackets.entire]
  have he := congrArg (fun z : ℂ =>
    (leftRadius c Z:ℂ)^m*(rightRadius c Z:ℂ)^n*(Real.pi/α:ℝ)*C*clockPhase p (s:ℂ)*
      Complex.exp (-(α:ℂ)*((1/wL:ℝ)*(leftRadius c Z:ℂ)+(wR:ℂ)*(rightRadius c Z:ℂ)))*
      Complex.exp (-((α/32:ℝ):ℂ)*(Z (.inr 3):ℂ)^2+b*(Z (.inr 3):ℂ))*
      P.eval (Z (.inr 3):ℂ)*z) hclock
  convert he using 1 <;> dsimp only [leftRadius,rightRadius]
  all_goals push_cast
  all_goals simp only [neg_add,Complex.exp_add]
  all_goals ring

theorem moment_input_coe (ε a h wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hL : 1 ≤ wL) (hR : 1 ≤ wR) (m n : ℕ) :
    clockMixed ε hε (inverseL ε hε
      (momentState ε a h wL wR C p b P hε ha hh hL hR m n)) =ᵐ[volume]
      fun x => numerator ε a (groundWidth h) wL wR (momentumScale h) C p b P m n
        (x.2 0:ℂ) ((split 2 4).symm x) := by
  have hm := KFCausalChargeRotatedSecondInput.mixed_of_charge _ _
    (momentState_charge_coe ε a h wL wR C p b P hε ha hh hL hR m n)
  have ht := KFCausalChargeRotatedSecondInput.rotated_second_input ε hε h hh 0 _ _ hm
  simp only [KFCausalPhysicalCircleAction.action_zero,
    KFCausalChargeRotatedSecondInput.rotatedPoint,KFCausalNormalizedChargeFlow.flow_zero,
    MeasurableEquiv.apply_symm_apply] at ht
  filter_upwards [ht] with x hx
  rw [hx]
  exact normalized_input ε a (groundWidth h) wL wR (momentumScale h) C p b P m n hε
    (groundWidth_positive h hh) (zero_lt_one.trans_le hL) (zero_lt_one.trans_le hR) x

#print axioms normalized_coordinates
#print axioms normalized_input
#print axioms moment_input_coe
end
end UnifiedTheory.Audit.KFCausalIndependentRadialMomentInput
