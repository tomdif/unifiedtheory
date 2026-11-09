/- Actual compact-state comparison of canonical, pure-clock and coupled
longitudinal momentum. The scalar density correction has a uniform bound;
the transverse shear output remains explicit and is not assumed controlled. -/
import UnifiedTheory.Audit.KFCausalClockFloorPureClockSandwich
import UnifiedTheory.Audit.KFCausalClockFloorCompactMomentumReconstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockCommonDomain
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive defect)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockDerivative (rate differential longitudinal_split)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockDifferential
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalCanonicalClockDerivative
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (clockMomentum longitudinalMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalReconstruction (shearDerivative)

variable (ε : ℝ) (hε : 0 < ε)

def clockInverse : Hilbert →L[ℂ] Hilbert := (1/(ε:ℂ)) • defectOperator ε hε

theorem clockInverse_coe (f : Hilbert) :
    clockInverse ε hε f =ᵐ[volume] fun x => (clock ε x.1:ℂ)⁻¹*f x := by
  filter_upwards [Lp.coeFn_smul (1/(ε:ℂ)) (defectOperator ε hε f),defectOperator_coe ε hε f] with x hx hy
  change ((1/(ε:ℂ)) • defectOperator ε hε f) x = _
  rw [hx]
  simp only [Pi.smul_apply,smul_eq_mul,hy,defect,Complex.ofReal_div]
  field_simp [Complex.ofReal_ne_zero.mpr hε.ne']

theorem clockInverse_norm (f : Hilbert) : ‖clockInverse ε hε f‖ ≤ (1/ε)*‖f‖ := by
  change ‖(1/(ε:ℂ)) • defectOperator ε hε f‖ ≤ _
  rw [norm_smul,norm_div,norm_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε]
  exact mul_le_mul_of_nonneg_left (defectOperator_norm_le ε hε f) (by positivity)

include hε in
theorem rate_bound (s : ℝ) : |rate ε s| ≤ 1/(8*ε) := by
  have hc := clock_positive ε s hε.le
  rw [rate,abs_div,abs_neg,abs_of_pos (Real.exp_pos s),abs_of_pos (by positivity : 0 < 2*(clock ε s)^2)]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  unfold clock
  nlinarith [sq_nonneg (Real.exp s-ε)]

private theorem output_coe (h : ℝ) (d : Configuration → ℂ) (hd : MemLp d 2 (volume : Measure Configuration)) :
    (-Complex.I*(h:ℂ)) • hd.toLp d =ᵐ[volume] fun x => (-Complex.I*(h:ℂ))*d x := by
  filter_upwards [Lp.coeFn_smul (-Complex.I*(h:ℂ)) (hd.toLp d),hd.coeFn_toLp] with x hx hy
  rw [hx]
  simp only [Pi.smul_apply,smul_eq_mul,hy]

include hε in
theorem correction_coefficient_bound (h s : ℝ) :
    ‖(-Complex.I*(h:ℂ))*(rate ε s:ℂ)‖ ≤ |h|/(8*ε) := by
  rw [norm_mul,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_real,
    Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (rate_bound ε hε s) (abs_nonneg h)).trans_eq (by ring)

theorem compact_common_outputs (h : ℝ) (hne : h ≠ 0) (f : Configuration → ℂ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    let state : Hilbert := (hf.continuous.memLp_of_hasCompactSupport hc).toLp f
    ∃ p b l d r : Hilbert,
      (state,p) ∈ (clockMomentum h).graph ∧
      (state,b) ∈ (pureMomentum ε hε h).graph ∧
      (state,l) ∈ (longitudinalMomentum ε hε h).graph ∧
      d =ᵐ[volume] (fun x => (clock ε x.1:ℂ)⁻¹*((-Complex.I*(h:ℂ))*shearDerivative f x)) ∧
      r =ᵐ[volume] (fun x => ((-Complex.I*(h:ℂ))*(rate ε x.1:ℂ))*f x) ∧
      b = clockInverse ε hε p+r ∧ l = b+d ∧
      ‖r‖ ≤ (|h|/(8*ε))*‖state‖ ∧
      ‖b‖ ≤ (1/ε)*‖p‖+(|h|/(8*ε))*‖state‖ := by
  let hm : MemLp f 2 (volume : Measure Configuration) := hf.continuous.memLp_of_hasCompactSupport hc
  let hp := compact_clock_memLp f hf hc
  let hb := compact_differential_memLp ε hε f hf hc
  let hl := KFCausalClockFloorDifferentialMomentum.compact_differential_memLp ε hε f hf hc
  let p : Hilbert := (-Complex.I*(h:ℂ)) • hp.toLp (clockDerivative f)
  let b : Hilbert := (-Complex.I*(h:ℂ)) • hb.toLp (differential ε f)
  let l : Hilbert := (-Complex.I*(h:ℂ)) • hl.toLp (KFCausalClockFloorDifferentialMomentum.differential ε f)
  let d : Hilbert := l-b
  let r : Hilbert := b-clockInverse ε hε p
  have hpc := output_coe h (clockDerivative f) hp
  have hbc := output_coe h (differential ε f) hb
  have hlc := output_coe h (KFCausalClockFloorDifferentialMomentum.differential ε f) hl
  have hrc : r =ᵐ[volume] fun x => ((-Complex.I*(h:ℂ))*(rate ε x.1:ℂ))*f x := by
    filter_upwards [Lp.coeFn_sub b (clockInverse ε hε p),clockInverse_coe ε hε p,hpc,hbc] with x hs hv hpx hbx
    change (b-clockInverse ε hε p) x = _
    rw [hs]
    simp only [Pi.sub_apply,hv,p,b,hpx,hbx,differential]
    ring
  have hrb : ‖r‖ ≤ (|h|/(8*ε))*‖hm.toLp f‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hrc,hm.coeFn_toLp] with x hx hy
    rw [hx,hy,norm_mul]
    exact mul_le_mul_of_nonneg_right (correction_coefficient_bound ε hε h x.1) (norm_nonneg _)
  have he : b = clockInverse ε hε p+r := by dsimp only [r]; abel
  refine ⟨p,b,l,d,r,clock_derivative_graph h hne f hm hp (hf.differentiable (by norm_num)),
    differential_graph ε hε h hne f hm hb (hf.differentiable (by norm_num)),
    KFCausalClockFloorDifferentialMomentum.differential_graph ε hε h hne f hm hl
      (hf.differentiable (by norm_num)),?_,hrc,he,?_,hrb,?_⟩
  · filter_upwards [Lp.coeFn_sub l b,hlc,hbc] with x hs hlx hbx
    change (l-b) x = _
    rw [hs]
    simp only [Pi.sub_apply,l,b,hlx,hbx,longitudinal_split,shearDerivative]
    ring
  · dsimp only [d]; abel
  · calc
      ‖b‖ = ‖clockInverse ε hε p+r‖ := congrArg norm he
      _ ≤ ‖clockInverse ε hε p‖+‖r‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (clockInverse_norm ε hε p) hrb

#print axioms clockInverse_coe
#print axioms clockInverse_norm
#print axioms rate_bound
#print axioms correction_coefficient_bound
#print axioms compact_common_outputs
end
end UnifiedTheory.Audit.KFCausalClockFloorPureClockCommonDomain
