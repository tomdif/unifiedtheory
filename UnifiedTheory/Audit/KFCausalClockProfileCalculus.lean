/- Bounded continuous clock profiles act continuously on the physical L2
space. Their Banach-algebra exponential gives a strong operator derivative,
so transporting a polynomial field does not assume an unbounded product rule. -/
import UnifiedTheory.Audit.KFCausalBoundedClockCharge
import UnifiedTheory.Audit.KFCausalClockShearPositiveVariation
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockProfileCalculus
noncomputable section
open MeasureTheory
open scoped BoundedContinuousFunction
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalBoundedClockCharge

abbrev Profiles := ℝ →ᵇ ℂ

def multiply (p : Profiles) : Hilbert →L[ℂ] Hilbert :=
  multiplier p p.continuous.measurable ‖p‖ (norm_nonneg p) p.norm_coe_le_norm

theorem multiply_coe (p : Profiles) (f : Hilbert) :
    multiply p f =ᵐ[volume] fun x => p x.1*f x := multiplier_coe _ _ _ _ _ f

theorem multiply_add (p q : Profiles) : multiply (p+q) = multiply p+multiply q := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [multiply_coe (p+q) f,multiply_coe p f,multiply_coe q f,
    Lp.coeFn_add (multiply p f) (multiply q f)] with x hp hq hr ha
  change multiply (p+q) f x = (multiply p f+multiply q f) x
  simp only [hp,ha,Pi.add_apply,hq,hr,BoundedContinuousFunction.add_apply]
  ring

theorem multiply_smul (z : ℂ) (p : Profiles) : multiply (z • p) = z • multiply p := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [multiply_coe (z • p) f,multiply_coe p f,
    Lp.coeFn_smul z (multiply p f)] with x hz hp hs
  change multiply (z • p) f x = (z • multiply p f) x
  simp only [hz,hs,Pi.smul_apply,smul_eq_mul,BoundedContinuousFunction.smul_apply,hp]
  ring

def multiplyL : Profiles →L[ℂ] (Hilbert →L[ℂ] Hilbert) :=
  LinearMap.mkContinuous
    { toFun := multiply
      map_add' := multiply_add
      map_smul' := multiply_smul }
    1 (fun p => by
      simpa only [one_mul] using (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg p)
        (multiplier_norm p p.continuous.measurable ‖p‖ (norm_nonneg p) p.norm_coe_le_norm)))

theorem multiply_mul (p q : Profiles) (f : Hilbert) :
    multiply (p*q) f = multiply p (multiply q f) := by
  apply Lp.ext
  filter_upwards [multiply_coe (p*q) f,multiply_coe p (multiply q f),multiply_coe q f]
    with x hp hq hr
  rw [hp,hq,hr]
  exact mul_assoc _ _ _

theorem multiply_one (f : Hilbert) : multiply 1 f = f := by
  apply Lp.ext
  filter_upwards [multiply_coe 1 f] with x hx
  simpa using hx

def evalRing (s : ℝ) : Profiles →+* ℂ where
  toFun p := p s
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem exponential_apply (p : Profiles) (s : ℝ) :
    NormedSpace.exp p s = Complex.exp (p s) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.map_exp (evalRing s) (BoundedContinuousFunction.evalCLM ℂ s).continuous p

def transport (p : Profiles) (t : ℝ) : Hilbert →L[ℂ] Hilbert :=
  multiply (NormedSpace.exp ((t-1) • p))

theorem transport_coe (p : Profiles) (t : ℝ) (f : Hilbert) :
    transport p t f =ᵐ[volume] fun x => Complex.exp ((t-1:ℝ)*p x.1)*f x := by
  filter_upwards [multiply_coe (NormedSpace.exp ((t-1) • p)) f] with x hx
  simpa only [exponential_apply,BoundedContinuousFunction.smul_apply,Complex.real_smul] using hx

theorem transport_one (p : Profiles) (f : Hilbert) : transport p 1 f = f := by
  simp only [transport,sub_self,zero_smul,NormedSpace.exp_zero]
  exact multiply_one f

theorem transport_derivative (p : Profiles) (t : ℝ) :
    HasDerivAt (transport p) (multiply (NormedSpace.exp ((t-1) • p)*p)) t := by
  have he := (hasDerivAt_exp_smul_const p (t-1)).scomp t ((hasDerivAt_id t).sub_const 1)
  have hd := (multiplyL.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t he
  simpa only [one_smul,Function.comp_def] using hd

theorem transport_continuous (p : Profiles) : Continuous (transport p) :=
  (show Differentiable ℝ (transport p) from fun t => (transport_derivative p t).differentiableAt).continuous

#print axioms multiply_coe
#print axioms multiply_add
#print axioms multiply_smul
#print axioms multiply_mul
#print axioms multiply_one
#print axioms exponential_apply
#print axioms transport_coe
#print axioms transport_one
#print axioms transport_derivative
#print axioms transport_continuous
end
end UnifiedTheory.Audit.KFCausalClockProfileCalculus
