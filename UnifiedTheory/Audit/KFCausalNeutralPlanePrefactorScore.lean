/- An invariant of the exactly integrated Gaussian prefactor yields its
logarithmic derivative. The actual score equals a rational expression
that has no inverse power of the imaginary scale. -/
import UnifiedTheory.Audit.KFCausalNeutralPlaneNormalizedGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2500000

namespace UnifiedTheory.Audit.KFCausalNeutralPlanePrefactorScore
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift
open UnifiedTheory.Audit.KFCausalNeutralPlaneCoordinates
open UnifiedTheory.Audit.KFCausalNeutralPlaneMarginal
open UnifiedTheory.Audit.KFCausalNeutralPlaneClockGeometry
open UnifiedTheory.Audit.KFCausalNeutralPlaneActualBound
open UnifiedTheory.Audit.KFCausalNeutralPlaneNormalizedGeometry

theorem prefactor_invariant (α : ℝ) (r : ℂ) (hα : 0 < α)
    (hA : 0 < r.re^2-r.im^2) (hb : r.im ≠ 0) :
    (prefactor α r)^2*r.im^2*(r.re^2-r.im^2)^3 = Real.pi^3/(64*α^3) := by
  have h1 := Real.sq_sqrt (show 0 ≤ Real.pi/(2*α*(r.re^2-r.im^2)) by positivity)
  have h2 := Real.sq_sqrt (show 0 ≤ Real.pi/(α*(r.re^2-r.im^2)) by positivity)
  have he : (prefactor α r)^2 =
      (1/(4*|r.im|))^2*(Real.sqrt (Real.pi/(2*α*(r.re^2-r.im^2)))^2)^2*
        (Real.sqrt (Real.pi/(α*(r.re^2-r.im^2))))^2 := by
    unfold prefactor
    ring
  rw [he,h1,h2]
  simp only [div_pow,mul_pow,one_pow,sq_abs]
  field_simp
  ring

theorem prefactor_log_derivative (α : ℝ) (r : ℝ → ℂ) (v : ℂ) (s : ℝ)
    (hr : HasDerivAt r v s) (hα : 0 < α)
    (hA : 0 < (r s).re^2-(r s).im^2) (hb : (r s).im ≠ 0) :
    deriv (fun t => prefactor α (r t)) s / prefactor α (r s) =
      -3*((r s).re*v.re-(r s).im*v.im)/((r s).re^2-(r s).im^2)-v.im/(r s).im := by
  have ha := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hr
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hr
  have harea := (ha.pow 2).sub (hi.pow 2)
  have hD := (prefactor_differentiableAt α r s hr.differentiableAt hα hA hb).hasDerivAt
  have he : (fun t => (prefactor α (r t))^2*(r t).im^2*
      ((r t).re^2-(r t).im^2)^3) =ᶠ[𝓝 s] fun _ => Real.pi^3/(64*α^3) := by
    filter_upwards [harea.continuousAt.eventually (lt_mem_nhds hA),
      hi.continuousAt.eventually (eventually_ne_nhds hb)] with t htA htb
    exact prefactor_invariant α (r t) hα htA htb
  have hz := (((hD.pow 2).mul (hi.pow 2)).mul (harea.pow 3)).unique
    ((hasDerivAt_const s (Real.pi^3/(64*α^3))).congr_of_eventuallyEq he)
  simp only [Nat.cast_ofNat,show 2-1=1 from rfl,show 3-1=2 from rfl,pow_one] at hz
  let D := prefactor α (r s)
  let Dp := deriv (fun t => prefactor α (r t)) s
  let A := (r s).re^2-(r s).im^2
  have hD0 : D ≠ 0 := (prefactor_positive α (r s) hα hA hb).ne'
  have hA0 : A ≠ 0 := hA.ne'
  change ((2*D*Dp*(r s).im^2+D^2*(2*(r s).im*v.im))*A^3+
      D^2*(r s).im^2*(3*A^2*(2*(r s).re*v.re-2*(r s).im*v.im))) = 0 at hz
  have hf : (2*D*(r s).im*A^2) *
      (Dp*(r s).im*A+D*v.im*A+3*D*(r s).im*((r s).re*v.re-(r s).im*v.im)) = 0 := by
    nlinarith [hz]
  have hbr := (mul_eq_zero.mp hf).resolve_left (by positivity)
  change Dp/D = -3*((r s).re*v.re-(r s).im*v.im)/A-v.im/(r s).im
  field_simp
  nlinarith [hbr]

theorem normalized_prefactor_log_derivative (α t : ℝ) (r : ℝ → ℂ) (s : ℝ)
    (hr : HasDerivAt r (velocity (1-t) t (r s)) s) (hα : 0 < α)
    (hA : 0 < (r s).re^2-(r s).im^2) (hb : (r s).im ≠ 0)
    (hd : denominator (1-t) t (r s) ≠ 0) :
    deriv (fun u => prefactor α (r u)) s / prefactor α (r s) =
      logPrefactorSlope t (r s) := by
  rw [prefactor_log_derivative α r _ s hr hα hA hb,
    normalized_velocity_re,normalized_velocity_im]
  unfold logPrefactorSlope
  field_simp
  ring

theorem actual_score_regular (α ε y s : ℝ) (hα : 0 < α) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hy0 : y ≠ 0) :
    score α ε y s = regularScore α (fraction ε s) (scale ε y s) := by
  have ht := fraction_bounds ε s hε
  have hA := scale_square_re_positive ε y s hε hy
  have ha := (scale_re_positive ε y s hε hy).ne'
  have hb := scale_im_ne_zero ε y s hε hy hy0
  have hd := (normalized_denominator_positive (fraction ε s) (scale ε y s)
    ⟨ht.1.le,ht.2.le⟩ hA).ne'
  have hv := actual_normalized_velocity ε y s hε hy
  have hlog := normalized_prefactor_log_derivative α (fraction ε s) (scale ε y) s
    hv hα hA hb hd
  have hL := normalized_fieldSlope_derivative (scale ε y) (fraction ε s) s hv hb hd
  have hw := widthSlope_normalize α ε (Real.exp s) (scale ε y s) (by positivity)
    (denominator_positive ε (Real.exp s) (scale ε y s) (Real.exp_pos _) ha hb).ne'
  unfold score regularScore
  rw [hlog,hL.deriv,hw]
  exact congrArg (logPrefactorSlope (fraction ε s) (scale ε y s)+·)
    (normalized_shear_quotient α (fraction ε s) (scale ε y s) hα.ne' ht.1.ne' ha hb
      (by positivity) hd)

#print axioms prefactor_invariant
#print axioms prefactor_log_derivative
#print axioms normalized_prefactor_log_derivative
#print axioms actual_score_regular
end
end UnifiedTheory.Audit.KFCausalNeutralPlanePrefactorScore
