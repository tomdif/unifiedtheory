/- The physical clock derivative and longitudinal differential expression
have their exact commutator on C2 functions. Second derivatives cancel by
the symmetry of the real Hessian, rather than by a formal substitution. -/
import UnifiedTheory.Audit.KFCausalClockFloorMomentumCoefficients

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockFloorDifferentialCommutator
noncomputable section
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (velocity)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (mobility coupledVelocity)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (response)
open UnifiedTheory.Audit.KFCausalClockFloorTransportDerivative (rate)
open UnifiedTheory.Audit.KFCausalClockFloorDifferentialMomentum (differential)
open UnifiedTheory.Audit.KFCausalCanonicalClockDerivative (clockDerivative)
open UnifiedTheory.Audit.KFCausalClockFloorMomentumCoefficients

theorem velocity_contDiff (ε : ℝ) (hε : 0 < ε) (n : ℕ) : ContDiff ℝ n (coupledVelocity ε) := by
  have hv : ContDiff ℝ n (fun x : Configuration => velocity x.2) := by
    apply contDiff_pi.mpr
    intro i
    unfold velocity
    split_ifs <;> fun_prop
  exact ((mobility_contDiff ε hε n).comp contDiff_fst).prodMk
    (((mobility_contDiff ε hε n).comp contDiff_fst).smul hv)

theorem clockDerivative_contDiff (f : Configuration → ℂ) (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (clockDerivative f) :=
  (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem differential_contDiff (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ)
    (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (differential ε f) := by
  have hr : ContDiff ℝ 1 (fun x : Configuration => (rate ε x.1:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((rate_contDiff ε hε 1).comp contDiff_fst)
  exact (hr.mul (hf.of_le (by norm_num))).add
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply (velocity_contDiff ε hε 1))

theorem velocity_clock_derivative (ε : ℝ) (hε : 0 < ε) (x : Configuration) :
    HasLineDerivAt ℝ (coupledVelocity ε) (-response ε x.1 • coupledVelocity ε x)
      x ((1,0):Configuration) := by
  have hb := (mobility_derivative ε (x.1+0) hε).comp 0
    ((hasDerivAt_id (0:ℝ)).const_add x.1)
  simp only [add_zero,mul_one] at hb
  have hd := hb.prodMk (hb.smul_const (velocity x.2))
  simpa only [HasLineDerivAt,coupledVelocity,Prod.add_def,Prod.smul_mk,smul_eq_mul,
    mul_one,smul_zero,add_zero,smul_smul] using hd

theorem clock_hessian (f : Configuration → ℂ) (hf : ContDiff ℝ 2 f) (x v : Configuration) :
    fderiv ℝ (clockDerivative f) x v =
      fderiv ℝ (fderiv ℝ f) x v ((1,0):Configuration) := by
  have hd := ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)
  change fderiv ℝ (fun y => fderiv ℝ f y ((1,0):Configuration)) x v = _
  rw [fderiv_clm_apply hd (differentiableAt_const ((1,0):Configuration))]
  simp

theorem differential_commutator (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ)
    (hf : ContDiff ℝ 2 f) (x : Configuration) :
    clockDerivative (differential ε f) x-differential ε (clockDerivative f) x =
      -(response ε x.1:ℂ)*differential ε f x-(remainderRate ε x.1:ℂ)*f x := by
  have hf' := hf.differentiable (by norm_num)
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hr := ((rate_derivative ε (x.1+0) hε).comp 0
    ((hasDerivAt_id (0:ℝ)).const_add x.1)).ofReal_comp
  simp only [add_zero,mul_one] at hr
  have hline := (hf' x).hasFDerivAt.hasLineDerivAt ((1,0):Configuration)
  have hsecond := (hdf x).hasFDerivAt.hasLineDerivAt ((1,0):Configuration)
  have hvel := velocity_clock_derivative ε hε x
  change HasDerivAt (fun t : ℝ => f (x+t • ((1,0):Configuration))) _ 0 at hline
  change HasDerivAt (fun t : ℝ => fderiv ℝ f (x+t • ((1,0):Configuration))) _ 0 at hsecond
  change HasDerivAt (fun t : ℝ => coupledVelocity ε (x+t • ((1,0):Configuration))) _ 0 at hvel
  have hd := (hr.mul hline).add (hsecond.clm_apply hvel)
  have hd' : HasLineDerivAt ℝ (differential ε f)
      (((-response ε x.1*rate ε x.1-remainderRate ε x.1:ℝ):ℂ)*f x+
        (rate ε x.1:ℂ)*clockDerivative f x+
        (fderiv ℝ (fderiv ℝ f) x ((1,0):Configuration) (coupledVelocity ε x)+
          fderiv ℝ f x (-response ε x.1 • coupledVelocity ε x))) x ((1,0):Configuration) := by
    simpa only [HasLineDerivAt,differential,clockDerivative,Function.comp_def,Pi.mul_apply,Pi.add_apply,Prod.add_def,Prod.smul_mk,
      smul_eq_mul,mul_one,smul_zero,add_zero,zero_smul] using hd
  have he := ((differential_contDiff ε hε f hf).differentiable (by norm_num) x).hasFDerivAt.hasLineDerivAt
    ((1,0):Configuration)
  have hx := he.unique hd'
  change clockDerivative (differential ε f) x = _ at hx
  rw [hx,differential,clock_hessian f hf x (coupledVelocity ε x),
    (hf.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq ((1,0):Configuration) (coupledVelocity ε x),
    map_smul]
  simp only [Complex.real_smul,differential]
  push_cast
  ring

#print axioms velocity_contDiff
#print axioms clockDerivative_contDiff
#print axioms differential_contDiff
#print axioms velocity_clock_derivative
#print axioms clock_hessian
#print axioms differential_commutator

end
end UnifiedTheory.Audit.KFCausalClockFloorDifferentialCommutator
