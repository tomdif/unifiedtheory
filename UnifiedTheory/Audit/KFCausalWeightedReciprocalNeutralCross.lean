/- Weighted physical cross-channel kernels retain the actual finite packet
profiles. Their differentiability and clock-normalized bounds follow from
the existing per-channel integrable envelopes, before clock integration. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralCrossBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalWeightedReciprocalNeutralCross
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate Topology
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalReciprocalNeutralCrossBounds (pairIntegral pairDerivative density densityDerivative)
open KFCausalPolynomialOrbitEnvelope (clockSlope)
open KFCausalClockResponseTransport (clock)

def actual (mass2 quartic vacuum ε y α β w v : ℝ) (b d : ℂ)
    (P Q : Polynomial ℂ) (s : ℝ) : ℂ :=
  (vacuum:ℂ)*pairIntegral ε y α β w v b d P Q 0 s+
    (mass2:ℂ)*pairIntegral ε y α β w v b d P Q 1 s/2+
    (quartic:ℂ)*pairIntegral ε y α β w v b d P Q 2 s/4

def slope (mass2 quartic vacuum ε y α β w v : ℝ) (b d : ℂ)
    (P Q : Polynomial ℂ) (s : ℝ) : ℂ :=
  (vacuum:ℂ)*pairDerivative ε y α β w v b d P Q 0 s+
    (mass2:ℂ)*pairDerivative ε y α β w v b d P Q 1 s/2+
    (quartic:ℂ)*pairDerivative ε y α β w v b d P Q 2 s/4

theorem actual_conj (mass2 quartic vacuum ε y α β w v : ℝ) (b d : ℂ)
    (P Q : Polynomial ℂ) (s : ℝ) :
    conj (actual mass2 quartic vacuum ε y α β w v b d P Q s)=
      actual mass2 quartic vacuum ε y α β v w d b Q P s := by
  have he (k : ℕ) : conj (pairIntegral ε y α β w v b d P Q k s)=
      pairIntegral ε y α β v w d b Q P k s := by
    unfold pairIntegral
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [density,map_mul,starRingEnd_self_apply]
    ring
  simp only [actual,map_add,map_mul,map_div₀,Complex.conj_ofReal,map_ofNat,he]

variable (ε y α β w v : ℝ) (b d : ℂ) (P Q : Polynomial ℂ)
  (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hα : 0 < α) (hβ : 0 < β)
  (hwidth : 32*β ≤ α) (hw : 1 ≤ w) (hv : 1 ≤ v)

include hε hy hα hβ hwidth hw hv in
private theorem pair_slope_continuous (k : ℕ) :
    Continuous (pairDerivative ε y α β w v b d P Q k) := by
  obtain ⟨D,hD,hD₀,hb⟩ := KFCausalReciprocalNeutralCrossBounds.common_bounds
    ε y α β w v b d P Q hε hy hα hβ hwidth hw hv k
  have hc := (KFCausalReciprocalNeutralCrossBounds.density_continuity
    ε y α β w v b d P Q hε hy hw hv k).2
  apply continuous_iff_continuousAt.mpr
  intro s
  obtain ⟨M,hM,hm⟩ := KFCausalTransverseClockDifferentiation.continuous_local_bound
    (clockSlope ε y) (KFCausalReciprocalNeutralClockDerivative.clockSlope_continuous ε y hε hy) s
  apply continuousAt_of_dominated
    (F := densityDerivative ε y α β w v b d P Q k) (bound := fun q => M*(2*D q))
    (Filter.Eventually.of_forall (fun t =>
      (hc.comp (continuous_const.prodMk continuous_id (f := fun _ : Transverse => t))).aestronglyMeasurable))
    _ ((hD.const_mul 2).const_mul M)
    (Filter.Eventually.of_forall (fun q =>
      (hc.comp (continuous_id.prodMk continuous_const (g := fun _ : ℝ => q))).continuousAt))
  filter_upwards [Icc_mem_nhds (by linarith : s-1<s) (by linarith : s<s+1)] with t ht
  exact Filter.Eventually.of_forall (fun q => (hb t q).2.trans
    (mul_le_mul_of_nonneg_right (hm t ht) (mul_nonneg (by norm_num) (hD₀ q))))

include hε hy hα hβ hwidth hw hv in
theorem pair_contDiff (k : ℕ) : ContDiff ℝ 1 (pairIntegral ε y α β w v b d P Q k) := by
  have hd := KFCausalReciprocalNeutralCrossBounds.pair_derivative
    ε y α β w v b d P Q hε hy hα hβ hwidth hw hv k
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun s => (hd s).differentiableAt,?_⟩
  rw [show deriv (pairIntegral ε y α β w v b d P Q k)=
    pairDerivative ε y α β w v b d P Q k from funext (fun s => (hd s).deriv)]
  exact pair_slope_continuous ε y α β w v b d P Q hε hy hα hβ hwidth hw hv k

variable (mass2 quartic vacuum : ℝ)
include hε hy hα hβ hwidth hw hv in
theorem actual_derivative (s : ℝ) :
    HasDerivAt (actual mass2 quartic vacuum ε y α β w v b d P Q)
      (slope mass2 quartic vacuum ε y α β w v b d P Q s) s := by
  have hd := KFCausalReciprocalNeutralCrossBounds.pair_derivative
    ε y α β w v b d P Q hε hy hα hβ hwidth hw hv
  exact (((hd 0 s).const_mul (vacuum:ℂ)).add
    (((hd 1 s).const_mul (mass2:ℂ)).div_const 2)).add
    (((hd 2 s).const_mul (quartic:ℂ)).div_const 4)

include hε hy hα hβ hwidth hw hv in
theorem actual_contDiff : ContDiff ℝ 1 (actual mass2 quartic vacuum ε y α β w v b d P Q) := by
  have hc := pair_contDiff ε y α β w v b d P Q hε hy hα hβ hwidth hw hv
  exact ((contDiff_const.mul (hc 0)).add ((contDiff_const.mul (hc 1)).div_const 2)).add
    ((contDiff_const.mul (hc 2)).div_const 4)

private theorem three_bound (a b c : ℂ) (x y z : ℂ) :
    ‖a*x+b*y/2+c*z/4‖ ≤ ‖a‖*‖x‖+‖b‖*‖y‖/2+‖c‖*‖z‖/4 := by
  calc
    _ ≤ ‖a*x+b*y/2‖+‖c*z/4‖ := norm_add_le _ _
    _ ≤ ‖a*x‖+‖b*y/2‖+‖c*z/4‖ := add_le_add (norm_add_le _ _) le_rfl
    _ = _ := by simp only [norm_mul,norm_div]; norm_num

include hε hy hα hβ hwidth hw hv in
theorem actual_bounds : ∃ M : ℝ, 0 ≤ M ∧ ∀ s,
    ‖actual mass2 quartic vacuum ε y α β w v b d P Q s‖ ≤ M ∧
      ‖deriv (actual mass2 quartic vacuum ε y α β w v b d P Q) s‖ ≤ ‖clockSlope ε y s‖*(2*M) := by
  obtain ⟨A,hA,ha⟩ := KFCausalReciprocalNeutralCrossBounds.pair_bounds
    ε y α β w v b d P Q hε hy hα hβ hwidth hw hv 0
  obtain ⟨B,hB,hb⟩ := KFCausalReciprocalNeutralCrossBounds.pair_bounds
    ε y α β w v b d P Q hε hy hα hβ hwidth hw hv 1
  obtain ⟨D,hD,hd⟩ := KFCausalReciprocalNeutralCrossBounds.pair_bounds
    ε y α β w v b d P Q hε hy hα hβ hwidth hw hv 2
  refine ⟨‖(vacuum:ℂ)‖*A+‖(mass2:ℂ)‖*B/2+‖(quartic:ℂ)‖*D/4,by positivity,?_⟩
  intro s
  constructor
  · apply (three_bound _ _ _ _ _ _).trans
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left (ha s).1 (norm_nonneg _))
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hb s).1 (norm_nonneg _)) (by norm_num)))
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hd s).1 (norm_nonneg _)) (by norm_num))
  · rw [(actual_derivative ε y α β w v b d P Q hε hy hα hβ hwidth hw hv mass2 quartic vacuum s).deriv]
    apply (three_bound _ _ _ _ _ _).trans
    have ha' := mul_le_mul_of_nonneg_left (ha s).2 (norm_nonneg (vacuum:ℂ))
    have hb' := mul_le_mul_of_nonneg_left (hb s).2 (norm_nonneg (mass2:ℂ))
    have hd' := mul_le_mul_of_nonneg_left (hd s).2 (norm_nonneg (quartic:ℂ))
    nlinarith

include hε hy hα hβ hwidth hw hv in
theorem normalized_derivative_bounds : ∃ M : ℝ, 0 ≤ M ∧ ∀ s,
    ‖actual mass2 quartic vacuum ε y α β w v b d P Q s‖ ≤ M ∧
      ‖deriv (actual mass2 quartic vacuum ε y α β w v b d P Q) s/(clock ε s:ℂ)‖ ≤ (4/ε)*M := by
  obtain ⟨M,hM,hm⟩ := actual_bounds ε y α β w v b d P Q hε hy hα hβ hwidth hw hv mass2 quartic vacuum
  refine ⟨M,hM,fun s => ⟨(hm s).1,?_⟩⟩
  have hc : (clock ε s:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by unfold clock; positivity)
  have he : clockSlope ε y s/(clock ε s:ℂ) = KFCausalGaussianResponseIntegrability.relativeInverse ε y s := by
    unfold clockSlope KFCausalGaussianResponseIntegrability.relativeInverse
    field_simp
  calc
    _ ≤ (‖clockSlope ε y s‖*(2*M))/‖(clock ε s:ℂ)‖ := by
      rw [norm_div]; exact div_le_div_of_nonneg_right (hm s).2 (norm_nonneg _)
    _ = ‖KFCausalGaussianResponseIntegrability.relativeInverse ε y s‖*(2*M) := by
      rw [← he,norm_div]; ring
    _ ≤ (2/ε)*(2*M) := mul_le_mul_of_nonneg_right
      (KFCausalGaussianResponseIntegrability.relativeInverse_bound ε y s hε hy) (by positivity)
    _ = _ := by ring

#print axioms actual_conj
#print axioms pair_contDiff
#print axioms actual_derivative
#print axioms actual_contDiff
#print axioms actual_bounds
#print axioms normalized_derivative_bounds
end
end UnifiedTheory.Audit.KFCausalWeightedReciprocalNeutralCross
