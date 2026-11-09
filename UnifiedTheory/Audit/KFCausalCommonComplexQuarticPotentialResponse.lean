/- The universal common-complex-source raw quartic bound is attached to
its original physical clock kernel and Hilbert output. The existing full
clock integration by parts retains the actual changing clock amplitudes.
No mass-channel or unrestricted-neutral-profile bound is asserted. -/
import UnifiedTheory.Audit.KFCausalCommonComplexQuarticClockKernel
import UnifiedTheory.Audit.KFCausalWeightedReciprocalNeutralPotentialTransport
import UnifiedTheory.Audit.KFCausalCommonRealGaussianPotentialResponse

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
namespace UnifiedTheory.Audit.KFCausalCommonComplexQuarticPotentialResponse
noncomputable section
open MeasureTheory
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalCommonComplexQuarticJointAngular (source energyDensity)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalReciprocalNeutralPositiveEnergy (coefficients)
open KFCausalWeightedReciprocalNeutralWholeClock
  (clockPairing positiveSlice transportResponse reducedResponse)
open KFCausalWeightedReciprocalNeutralPotentialTransport (potentialEnergy potentialResponse)
open KFCausalClockResponseTransport (clock coefficient coefficient_lower)
open KFCausalNeutralPlaneNormalizedGeometry (fraction)
open KFCausalCommonRealGaussianPotentialResponse (fraction_div_clock_bound)

theorem positiveSlice_joint (n : ℕ) (ε h A D : ℝ) (a w p : Fin n→ℝ)
    (C : Fin n→ℂ) (hε : 0<ε) (hh : h≠0) (hw : ∀i,1≤w i)
    (hb : |h|≤2*Real.pi*ε/3) (s : ℝ) :
    positiveSlice 0 4 0 n ε h a w p C (fun _=>source A D) (fun _=>1) s=
      Real.pi/4*(∫z,energyDensity n (groundWidth h) (neutralWidth h) A D w
        (scale ε (-h/2) s) (coefficients n ε h a p C s) z ∂jointMeasure) := by
  have hy : |-h/2|≤Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  have he := KFCausalCommonComplexQuarticClockKernel.actual_energy_eq_family n
    (groundWidth h) (neutralWidth h) ε (-h/2) s A D w (coefficients n ε h a p C s)
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy hw
  change (clockPairing 0 4 0 n ε h a w p C (fun _=>source A D) (fun _=>1) s).re=_
  rw [KFCausalCommonRealGaussianWeightedTransport.clockPairing_family 0 4 0 n ε h a w p C
    (fun _=>source A D) hε hh hw hb]
  simp only [Complex.mul_re,Complex.div_ofNat_re,Complex.div_ofNat_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_div,zero_mul,sub_zero]
  rw [he]

private theorem slice_nonnegative (n : ℕ) (ε h A D : ℝ) (a w p : Fin n→ℝ)
    (C : Fin n→ℂ) (hε : 0<ε) (hh : h≠0) (hw : ∀i,1≤w i)
    (hb : |h|≤2*Real.pi*ε/3) (s : ℝ) :
    0≤positiveSlice 0 4 0 n ε h a w p C (fun _=>source A D) (fun _=>1) s := by
  rw [positiveSlice_joint n ε h A D a w p C hε hh hw hb s]
  apply mul_nonneg (by positivity)
  apply integral_nonneg
  intro z
  unfold energyDensity KFCausalCommonComplexQuarticJointAngular.channel
    KFCausalCommonComplexQuarticJointAngular.jointBase
  positivity

theorem transport_bound : ∃ K : ℝ,0≤K ∧ ∀ (n : ℕ) (ε h A D : ℝ) (a w p : Fin n→ℝ)
    (C : Fin n→ℂ),0<ε→h≠0→(∀i,1≤w i)→|h|≤2*Real.pi*ε/3→∀s:ℝ,
    transportResponse 0 4 0 n ε h a w p C (fun _=>source A D) (fun _=>1) s≤
      K*fraction ε s*positiveSlice 0 4 0 n ε h a w p C (fun _=>source A D) (fun _=>1) s := by
  obtain ⟨K,hK,hbound⟩ := KFCausalCommonComplexQuarticActualBound.global_bound
  refine ⟨K,hK,?_⟩
  intro n ε h A D a w p C hε hh hw hb s
  have hy : |-h/2|≤Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  rw [KFCausalCommonRealGaussianWeightedTransport.transport_family 0 4 0 n ε h a w p C
    (fun _=>source A D) hε hh hw hb,positiveSlice_joint n ε h A D a w p C hε hh hw hb]
  rw [←KFCausalCommonComplexQuarticClockKernel.actual_response_eq_familySlope n
    (groundWidth h) (neutralWidth h) ε (-h/2) s A D w (coefficients n ε h a p C s)
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy hw]
  have he := hbound n (groundWidth h) (neutralWidth h) ε (-h/2) s A D w
    (coefficients n ε h a p C s) (groundWidth_positive h hh) (neutralWidth_positive h hh)
    (neutralWidth_bound h) hε hy hw
  convert mul_le_mul_of_nonneg_left he (by positivity : 0≤Real.pi/4) using 1
  ring

theorem reduced_bound : ∃ M : ℝ,0≤M ∧ ∀ (n : ℕ) (ε h A D : ℝ) (a w p : Fin n→ℝ)
    (C : Fin n→ℂ),0<ε→h≠0→(∀i,1≤w i)→|h|≤2*Real.pi*ε/3→∀s:ℝ,
    -(M/ε)*positiveSlice 0 4 0 n ε h a w p C (fun _=>source A D) (fun _=>1) s≤
      reducedResponse 0 4 0 n ε h a w p C (fun _=>source A D) (fun _=>1) s := by
  obtain ⟨K,hK,hbound⟩ := transport_bound
  refine ⟨2+K/4,by positivity,?_⟩
  intro n ε h A D a w p C hε hh hw hb s
  let E := positiveSlice 0 4 0 n ε h a w p C (fun _=>source A D) (fun _=>1) s
  have hE : 0≤E := slice_nonnegative n ε h A D a w p C hε hh hw hb s
  have hc : 0<clock ε s := by unfold clock; positivity
  have hy : |-h/2|≤Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  have hcoef := mul_le_mul_of_nonneg_right (coefficient_lower ε (-h/2) s hε hy) hE
  have ht := hbound n ε h A D a w p C hε hh hw hb s
  have hdiv : transportResponse 0 4 0 n ε h a w p C (fun _=>source A D) (fun _=>1) s/clock ε s≤
      (K/(4*ε))*E := by
    calc
      _≤(K*fraction ε s*E)/clock ε s := div_le_div_of_nonneg_right ht hc.le
      _=K*(fraction ε s/clock ε s)*E := by ring
      _≤K*(1/(4*ε))*E := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (fraction_div_clock_bound ε s hε) hK) hE
      _=_ := by ring
  rw [KFCausalWeightedReciprocalNeutralWholeClock.reduced_identity]
  change -((2+K/4)/ε)*E≤coefficient ε (-h/2) s*E-
    transportResponse 0 4 0 n ε h a w p C (fun _=>source A D) (fun _=>1) s/clock ε s
  have he : -((2+K/4)/ε)*E=-(2/ε)*E-(K/(4*ε))*E := by ring
  rw [he]
  linarith

theorem potential_response_lower : ∃ M : ℝ,0≤M ∧ ∀ (n : ℕ) (ε h A D : ℝ)
    (a w p : Fin n→ℝ) (C : Fin n→ℂ) (hε : 0<ε) (ha : ∀i,0<a i) (hh : h≠0)
    (hw : ∀i,1≤w i) (hb : |h|≤2*Real.pi*ε/3),
    -(M/ε)*potentialEnergy 0 4 0 n ε h a w p C (fun _=>source A D) (fun _=>1)
      hε ha hh hw hb≤
    potentialResponse 0 4 0 n ε h a w p C (fun _=>source A D) (fun _=>1)
      hε ha hh hw hb := by
  obtain ⟨M,hM,hbound⟩ := reduced_bound
  refine ⟨M,hM,?_⟩
  intro n ε h A D a w p C hε ha hh hw hb
  rw [KFCausalWeightedReciprocalNeutralPotentialTransport.potentialEnergy_integral,
    KFCausalWeightedReciprocalNeutralPotentialTransport.potentialResponse_reduced_integral,
    ←integral_const_mul]
  exact integral_mono
    ((KFCausalWeightedReciprocalNeutralPotentialTransport.positiveSlice_integrable 0 4 0
      n ε h a w p C (fun _=>source A D) (fun _=>1) hε ha hh hw hb).const_mul _)
    (KFCausalWeightedReciprocalNeutralWholeClock.response_integrability 0 4 0
      n ε h a w p C (fun _=>source A D) (fun _=>1) hε hh hw hb ha).2.1
    (hbound n ε h A D a w p C hε hh hw hb)

#print axioms positiveSlice_joint
#print axioms transport_bound
#print axioms reduced_bound
#print axioms potential_response_lower
end
end UnifiedTheory.Audit.KFCausalCommonComplexQuarticPotentialResponse
