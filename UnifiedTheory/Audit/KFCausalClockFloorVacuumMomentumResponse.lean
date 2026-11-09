/- The actual ordered vacuum factor has a positive longitudinal momentum
response form. Its equality to the weak commutator is proved on the
natural composition domain. No Hamiltonian evolution identity is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorOrderedMomentumCommutator
import UnifiedTheory.Audit.KFCausalClockFloorShiftedMomentumSign
import UnifiedTheory.Audit.KFCausalAveragedEnergyGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorVacuumMomentumResponse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (longitudinalMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates (coupledFourier)
open UnifiedTheory.Audit.KFCausalClockFloorFourierMultiplier
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorOrderedMomentumCommutator
open UnifiedTheory.Audit.KFCausalClockFloorShiftedMomentumSign
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical
open UnifiedTheory.Audit.KFCausalClockFloorShiftedResponseContraction

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : |h| ≤ 2*Real.pi*ε/3)
local notation "Z" => shiftedDefect ε hε h hh
local notation "S" => shiftedResponse ε hε h hh
local notation "L" => longitudinalMomentum ε hε h
local notation "T" => orderedExponential ε hε h

def multiplier : Hilbert →L[ℂ] Hilbert := (Z).comp S
def response (f : Hilbert) : ℝ := (1/ε)*(inner ℂ f (multiplier ε hε h hh f)).re

theorem multiplier_coe (f : Hilbert) : multiplier ε hε h hh f =ᵐ[volume]
    fun x => (physicalSymbol ε h x*(1-physicalSymbol ε h x))*f x := by
  filter_upwards [shiftedDefect_physical_coe ε hε h hh (S f),shiftedResponse_coe ε hε h hh f] with x hz hs
  change Z (S f) x = _
  rw [hz,hs,mul_assoc]

theorem multiplier_bound (f : Hilbert) : ‖multiplier ε hε h hh f‖ ≤ (1/2)*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiplier_coe ε hε h hh f] with x hx
  rw [hx,norm_mul]
  exact mul_le_mul_of_nonneg_right (physical_momentum_norm ε hε h hh x) (norm_nonneg _)

private theorem scalar_re (z w : ℂ) : (inner ℂ z (w*z)).re = w.re*‖z‖^2 := by
  change (inner ℂ z (w • z)).re = _
  rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
  change (w*(‖z‖:ℂ)^2).re = _
  rw [← Complex.ofReal_pow]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

include hε hh in
theorem density_integrable (f : Hilbert) :
    Integrable (fun x => (physicalSymbol ε h x*(1-physicalSymbol ε h x)).re*‖f x‖^2) volume := by
  apply ((L2.integrable_inner (𝕜 := ℂ) f (multiplier ε hε h hh f)).re).congr
  filter_upwards [multiplier_coe ε hε h hh f] with x hx
  change (inner ℂ (f x) (multiplier ε hε h hh f x)).re = _
  rw [hx,scalar_re]

theorem pairing_integral (f : Hilbert) :
    (inner ℂ f (multiplier ε hε h hh f)).re =
      ∫ x, (physicalSymbol ε h x*(1-physicalSymbol ε h x)).re*‖f x‖^2 := by
  have he := integral_re (L2.integrable_inner (𝕜 := ℂ) f (multiplier ε hε h hh f))
  change (∫ x, (inner ℂ (f x) (multiplier ε hε h hh f x)).re) =
    (∫ x, inner ℂ (f x) (multiplier ε hε h hh f x)).re at he
  rw [L2.inner_def,← he]
  apply integral_congr_ae
  filter_upwards [multiplier_coe ε hε h hh f] with x hx
  rw [hx,scalar_re]

theorem response_bounds (f : Hilbert) :
    0 ≤ response ε hε h hh f ∧ response ε hε h hh f ≤ (1/(2*ε))*‖f‖^2 := by
  have hp : 0 ≤ (inner ℂ f (multiplier ε hε h hh f)).re := by
    rw [pairing_integral]
    exact integral_nonneg (fun x => mul_nonneg (physical_momentum_sign ε hε h hh x).1.le (sq_nonneg _))
  refine ⟨mul_nonneg (by positivity) hp,?_⟩
  have hb := (re_inner_le_norm (𝕜 := ℂ) f (multiplier ε hε h hh f)).trans
    (mul_le_mul_of_nonneg_left (multiplier_bound ε hε h hh f) (norm_nonneg f))
  exact (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 1/ε)).trans_eq (by ring)

theorem response_positive (f : Hilbert) (hf : f ≠ 0) : 0 < response ε hε h hh f := by
  have hp : ∀ᵐ x ∂volume, 0 ≤ (physicalSymbol ε h x*(1-physicalSymbol ε h x)).re*‖f x‖^2 :=
    Filter.Eventually.of_forall (fun x => mul_nonneg (physical_momentum_sign ε hε h hh x).1.le (sq_nonneg _))
  have hn : (inner ℂ f (multiplier ε hε h hh f)).re ≠ 0 := by
    intro he
    rw [pairing_integral] at he
    have hz := (integral_eq_zero_iff_of_nonneg_ae hp (density_integrable ε hε h hh f)).mp he
    apply hf
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [hz] with x hx
    have hs := (mul_eq_zero.mp hx).resolve_left (physical_momentum_sign ε hε h hh x).1.ne'
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hs)
  apply mul_pos (by positivity)
  rw [pairing_integral] at hn ⊢
  exact lt_of_le_of_ne (integral_nonneg_of_ae hp) (Ne.symm hn)

theorem response_continuous : Continuous (response ε hε h hh) :=
  continuous_const.mul (Complex.continuous_re.comp (continuous_id.inner (multiplier ε hε h hh).continuous))

theorem correction_sharp_bound (f : Hilbert) :
    ‖correction ε hε h hh f‖ ≤ (|h|/(4*ε))*‖f‖ := by
  change ‖(Complex.I*(h:ℂ)/(2*(ε:ℂ))) • multiplier ε hε h hh f‖ ≤ _
  rw [norm_smul,norm_div,norm_mul,Complex.norm_I,one_mul,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε]
  norm_num only [Complex.norm_ofNat]
  exact (mul_le_mul_of_nonneg_left (multiplier_bound ε hε h hh f)
    (by positivity : 0 ≤ |h|/(2*ε))).trans_eq (by ring)

omit hh in
theorem momentum_pairing_real (hne : h ≠ 0) (f g : Hilbert) (hg : (f,g) ∈ (L).graph) :
    (inner ℂ f g).im = 0 := by
  have hf := (momentum_graph_fourier_iff ε hε h hne f g).mp hg
  have he := real_multiplier_inner (symbol h) (coupledFourier ε hε f) (coupledFourier ε hε g)
    (coupledFourier ε hε f) (coupledFourier ε hε g) hf hf
  simp only [LinearIsometryEquiv.inner_map_map] at he
  have hi := congrArg Complex.im he
  have hs : (inner ℂ g f).im = -(inner ℂ f g).im := inner_im_symm (𝕜 := ℂ) g f
  linarith

theorem weak_momentum_response (hne : h ≠ 0) (f lf tf tlf : Hilbert)
    (hl : (f,lf) ∈ (L).graph) (ht : (f,tf) ∈ (T).graph) (htl : (lf,tlf) ∈ (T).graph) :
    (-2/h)*(inner ℂ tf tlf).im = response ε hε h hh tf := by
  have hr := momentum_pairing_real ε hε h hne tf _
    (ordered_momentum_graph ε hε h hne hh f lf tf tlf hl ht htl)
  change (inner ℂ tf (tlf+(Complex.I*(h:ℂ)/(2*(ε:ℂ))) • multiplier ε hε h hh tf)).im = 0 at hr
  rw [inner_add_right,inner_smul_right,Complex.add_im,Complex.mul_im] at hr
  have hc : Complex.I*(h:ℂ)/(2*(ε:ℂ)) = ((h/(2*ε):ℝ):ℂ)*Complex.I := by push_cast; ring
  rw [hc] at hr
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_mul,sub_zero,add_zero,zero_add] at hr
  unfold response
  field_simp [hε.ne'] at hr
  field_simp [hε.ne',hne]
  linarith

#print axioms multiplier_coe
#print axioms multiplier_bound
#print axioms density_integrable
#print axioms pairing_integral
#print axioms response_bounds
#print axioms response_positive
#print axioms response_continuous
#print axioms correction_sharp_bound
#print axioms momentum_pairing_real
#print axioms weak_momentum_response
end
end UnifiedTheory.Audit.KFCausalClockFloorVacuumMomentumResponse
