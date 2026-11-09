/- The pure-clock differential is R P R with R=C^(-1/2), on actual
composition states. The compact-state corollary derives all L2 conditions.
No maximal-domain equality for an unclosed sandwich is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorPureClockDifferential
import UnifiedTheory.Audit.KFCausalClockFloorInverseHalfTransportOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockSandwich
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive)
open UnifiedTheory.Audit.KFCausalClockFloorInverseHalfTransportScalar (value)
open UnifiedTheory.Audit.KFCausalClockFloorInverseHalfTransportOperator (inverseL_coe)
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse (inverseL)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockDerivative (rate differential)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockDifferential
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalCanonicalClockDerivative
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (clockMomentum)

variable (ε : ℝ) (hε : 0 < ε)

def weighted (f : Configuration → ℂ) (x : Configuration) : ℂ := (value ε x.1:ℂ)*f x

include hε in
theorem value_derivative (s : ℝ) :
    HasDerivAt (value ε) (-(Real.exp s/(2*clock ε s))*value ε s) s := by
  have hc := clock_positive ε s hε.le
  have hr := (Real.sqrt_pos.mpr hc).ne'
  have hs := Real.sq_sqrt hc.le
  have hd := (((Real.hasDerivAt_exp s).add_const ε).sqrt hc.ne').inv hr
  change HasDerivAt (value ε) _ s at hd
  convert hd using 1
  unfold value
  change _ = -(Real.exp s/(2*Real.sqrt (clock ε s)))/(Real.sqrt (clock ε s))^2
  rw [hs]
  ring

include hε in
theorem weight_contDiff (n : ℕ) : ContDiff ℝ n (fun x : Configuration => (value ε x.1:ℂ)) := by
  have hr : ContDiff ℝ n (fun x : Configuration => value ε x.1) := by
    unfold value clock
    fun_prop (disch := intro x; positivity)
  exact Complex.ofRealCLM.contDiff.comp hr

include hε in
theorem weighted_contDiff (f : Configuration → ℂ) (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (weighted ε f) := (weight_contDiff ε hε 1).mul hf

theorem weighted_compact (f : Configuration → ℂ) (hf : HasCompactSupport f) :
    HasCompactSupport (weighted ε f) := hf.mul_left

include hε in
theorem weighted_derivative (f : Configuration → ℂ) (hf : ContDiff ℝ 1 f) (x : Configuration) :
    clockDerivative (weighted ε f) x =
      (-(Real.exp x.1/(2*clock ε x.1))*value ε x.1:ℂ)*f x+
        (value ε x.1:ℂ)*clockDerivative f x := by
  have hr := ((value_derivative ε hε (x.1+0)).comp 0
    ((hasDerivAt_id (0:ℝ)).const_add x.1)).ofReal_comp
  simp only [add_zero,mul_one] at hr
  have hf' := hf.differentiable (by norm_num)
  have hl := (hf' x).hasFDerivAt.hasLineDerivAt ((1,0):Configuration)
  change HasDerivAt (fun t : ℝ => f (x+t • ((1,0):Configuration))) _ 0 at hl
  have hd := hr.mul hl
  have hd' : HasLineDerivAt ℝ (weighted ε f)
      ((-(Real.exp x.1/(2*clock ε x.1))*value ε x.1:ℂ)*f x+
        (value ε x.1:ℂ)*clockDerivative f x) x ((1,0):Configuration) := by
    simpa only [HasLineDerivAt,weighted,clockDerivative,Function.comp_def,Pi.mul_apply,Prod.add_def,
      Prod.smul_mk,smul_eq_mul,mul_one,smul_zero,add_zero,zero_smul,Complex.ofReal_mul,
      Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat] using hd
  exact (((weighted_contDiff ε hε f hf).differentiable (by norm_num) x).hasFDerivAt.hasLineDerivAt
    ((1,0):Configuration)).unique hd'

include hε in
theorem sandwich_differential (f : Configuration → ℂ) (hf : ContDiff ℝ 1 f) (x : Configuration) :
    (value ε x.1:ℂ)*clockDerivative (weighted ε f) x = differential ε f x := by
  have hc := clock_positive ε x.1 hε.le
  have hv : (value ε x.1:ℂ)^2 = (clock ε x.1:ℂ)⁻¹ := by
    rw [value,Complex.ofReal_inv,inv_pow,← Complex.ofReal_pow,Real.sq_sqrt hc.le]
  rw [weighted_derivative ε hε f hf x]
  unfold differential rate
  simp only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_ofNat]
  calc
    _ = (value ε x.1:ℂ)^2*clockDerivative f x-
      (Real.exp x.1:ℂ)/(2*(clock ε x.1:ℂ))*(value ε x.1:ℂ)^2*f x := by ring
    _ = _ := by rw [hv]; ring

theorem inverseL_weighted (f : Configuration → ℂ) (hf : MemLp f 2 (volume : Measure Configuration))
    (hg : MemLp (weighted ε f) 2 (volume : Measure Configuration)) :
    inverseL ε hε (hf.toLp f) = hg.toLp (weighted ε f) := by
  apply Lp.ext
  filter_upwards [inverseL_coe ε hε (hf.toLp f),hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy hz
  rw [hx,hy,hz]
  rfl

theorem compact_sandwich (h : ℝ) (hne : h ≠ 0) (f : Configuration → ℂ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    let state : Hilbert := (hf.continuous.memLp_of_hasCompactSupport hc).toLp f
    ∃ p b : Hilbert,
      (inverseL ε hε state,p) ∈ (clockMomentum h).graph ∧
      (state,b) ∈ (pureMomentum ε hε h).graph ∧ inverseL ε hε p = b := by
  let hm : MemLp f 2 (volume : Measure Configuration) := hf.continuous.memLp_of_hasCompactSupport hc
  let hg : MemLp (weighted ε f) 2 (volume : Measure Configuration) :=
    (weighted_contDiff ε hε f hf).continuous.memLp_of_hasCompactSupport (weighted_compact ε f hc)
  let hp := compact_clock_memLp (weighted ε f) (weighted_contDiff ε hε f hf) (weighted_compact ε f hc)
  let hb := compact_differential_memLp ε hε f hf hc
  let p : Hilbert := (-Complex.I*(h:ℂ)) • hp.toLp (clockDerivative (weighted ε f))
  let b : Hilbert := (-Complex.I*(h:ℂ)) • hb.toLp (differential ε f)
  refine ⟨p,b,?_,?_,?_⟩
  · rw [inverseL_weighted ε hε f hm hg]
    exact clock_derivative_graph h hne (weighted ε f) hg hp
      ((weighted_contDiff ε hε f hf).differentiable (by norm_num))
  · exact differential_graph ε hε h hne f hm hb (hf.differentiable (by norm_num))
  · apply Lp.ext
    filter_upwards [inverseL_coe ε hε p,
      Lp.coeFn_smul (-Complex.I*(h:ℂ)) (hp.toLp (clockDerivative (weighted ε f))),hp.coeFn_toLp,
      Lp.coeFn_smul (-Complex.I*(h:ℂ)) (hb.toLp (differential ε f)),hb.coeFn_toLp] with x hx hy hz hu hv
    rw [hx]
    change (value ε x.1:ℂ)*(((-Complex.I*(h:ℂ)) • hp.toLp (clockDerivative (weighted ε f))) x) =
      (((-Complex.I*(h:ℂ)) • hb.toLp (differential ε f)) x)
    rw [hy,hu]
    simp only [Pi.smul_apply,smul_eq_mul,hz,hv]
    rw [mul_left_comm, sandwich_differential ε hε f hf x]

#print axioms value_derivative
#print axioms weight_contDiff
#print axioms weighted_contDiff
#print axioms weighted_compact
#print axioms weighted_derivative
#print axioms sandwich_differential
#print axioms inverseL_weighted
#print axioms compact_sandwich
end
end UnifiedTheory.Audit.KFCausalClockFloorPureClockSandwich
