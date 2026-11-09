/- The missing clock-half/momentum composition is derived from the
physical differential and actual L2 representatives. The square-root
density correction is retained; no reverse inverse-domain rule is assumed. -/
import UnifiedTheory.Audit.KFCausalPureClockOutputMultipliers
import UnifiedTheory.Audit.KFCausalClockFloorPureClockClockResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockHalfMomentumDifferential
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (halfWeight clockHalf clockHalf_graph halfWeight_positive)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockDerivative (rate differential)
open UnifiedTheory.Audit.KFCausalCanonicalClockDerivative (clockDerivative)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalPureClockOutputMultipliers (rateOperator rateOperator_coe)

variable (ε : ℝ) (hε : 0 < ε)

def halfProfile (f : Configuration → ℂ) (x : Configuration) : ℂ := (halfWeight ε x:ℂ)*f x

include hε in
theorem halfProfile_differentiable (f : Configuration → ℂ) (hf : Differentiable ℝ f) :
    Differentiable ℝ (halfProfile ε f) := by
  have hm : Differentiable ℝ (fun x : Configuration => (halfWeight ε x:ℂ)) := by
    apply Complex.ofRealCLM.differentiable.comp
    fun_prop (disch := intro x; positivity)
  exact hm.mul hf

include hε in
theorem halfProfile_clock_derivative (f : Configuration → ℂ) (hf : Differentiable ℝ f) (x : Configuration) :
    clockDerivative (halfProfile ε f) x =
      ((Real.exp x.1/(2*halfWeight ε x):ℝ):ℂ)*f x+(halfWeight ε x:ℂ)*clockDerivative f x := by
  have hs := ((Real.hasDerivAt_exp x.1).add_const ε).sqrt (by positivity : Real.exp x.1+ε ≠ 0)
  have hd := (hf x).hasFDerivAt.comp_hasDerivAt x.1
    ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))
  have hp := hs.ofReal_comp.mul hd
  have hg := ((halfProfile_differentiable ε hε f hf) x).hasFDerivAt.comp_hasDerivAt x.1
    ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))
  exact hg.unique hp

include hε in
theorem differential_halfProfile (f : Configuration → ℂ) (hf : Differentiable ℝ f) (x : Configuration) :
    differential ε (halfProfile ε f) x =
      (halfWeight ε x:ℂ)*differential ε f x-(rate ε x.1:ℂ)*halfProfile ε f x := by
  unfold differential
  rw [halfProfile_clock_derivative ε hε f hf x]
  have hH : (halfWeight ε x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (halfWeight_positive ε hε x).ne'
  have hC : (clock ε x.1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by unfold clock; positivity)
  have hsq : (halfWeight ε x:ℂ)^2 = (clock ε x.1:ℂ) := by
    rw [← Complex.ofReal_pow]
    exact congrArg (fun r : ℝ => (r:ℂ)) (Real.sq_sqrt (by positivity))
  unfold halfProfile rate
  simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat,
    Complex.ofReal_neg,Complex.ofReal_pow]
  field_simp [hH,hC]
  linear_combination -(Real.exp x.1:ℂ)*f x*hsq

theorem half_momentum_domain (h : ℝ) (hh : h ≠ 0) (f : Configuration → ℂ) (hs : Differentiable ℝ f)
    (u b g k : Hilbert) (hu : u =ᵐ[volume] f)
    (hb : b =ᵐ[volume] fun x => (-Complex.I*(h:ℂ))*differential ε f x)
    (hg : (u,g) ∈ (clockHalf ε).graph) (hk : (b,k) ∈ (clockHalf ε).graph) :
    g ∈ (pureMomentum ε hε h).domain := by
  have hgf : g =ᵐ[volume] halfProfile ε f := by
    filter_upwards [(clockHalf_graph ε u g).mp hg,hu] with x hx hy
    rw [hx,hy]
    rfl
  let d : Hilbert := (Complex.I/(h:ℂ)) • k-rateOperator ε hε g
  have hc : Complex.I/(h:ℂ)*(-Complex.I*(h:ℂ)) = 1 := by
    field_simp [Complex.ofReal_ne_zero.mpr hh]
    simp
  have hd : d =ᵐ[volume] differential ε (halfProfile ε f) := by
    filter_upwards [Lp.coeFn_sub ((Complex.I/(h:ℂ)) • k) (rateOperator ε hε g),
      Lp.coeFn_smul (Complex.I/(h:ℂ)) k,rateOperator_coe ε hε g,
      (clockHalf_graph ε b k).mp hk,hb,hgf] with x hd' hsm hr hk' hb' hg'
    change ((Complex.I/(h:ℂ)) • k-rateOperator ε hε g) x = _
    rw [hd']
    simp only [Pi.sub_apply,hsm,Pi.smul_apply,smul_eq_mul,hr,hk',hb',hg']
    rw [differential_halfProfile ε hε f hs x]
    calc
      _ = (Complex.I/(h:ℂ)*(-Complex.I*(h:ℂ)))*((halfWeight ε x:ℂ)*differential ε f x)-
          (rate ε x.1:ℂ)*halfProfile ε f x := by ring
      _ = _ := by rw [hc,one_mul]
  have hm := (Lp.memLp g).ae_eq hgf
  have he : g = hm.toLp (halfProfile ε f) := Lp.ext (hgf.trans hm.coeFn_toLp.symm)
  rw [he]
  exact KFCausalClockFloorPureClockDifferential.differential_domain ε hε h hh _ hm
    ((Lp.memLp d).ae_eq hd) (halfProfile_differentiable ε hε f hs)

#print axioms halfProfile_differentiable
#print axioms halfProfile_clock_derivative
#print axioms differential_halfProfile
#print axioms half_momentum_domain
end
end UnifiedTheory.Audit.KFCausalClockHalfMomentumDifferential
