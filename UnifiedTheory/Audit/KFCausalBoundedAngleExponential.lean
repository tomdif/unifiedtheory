/- Smooth dependence of charge-orbit exponential integrals. Bounded angle
profiles form a commutative Banach algebra; its analytic exponential and a
bounded integral functional supply all parameter derivatives rigorously. -/
import UnifiedTheory.Audit.KFCausalClassicalChargeMean
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalBoundedAngleExponential
noncomputable section
open MeasureTheory
open scoped BoundedContinuousFunction
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

abbrev Profiles := ℝ →ᵇ ℝ

def meanL : Profiles →L[ℝ] ℝ := LinearMap.mkContinuous
  { toFun := fun f => ∫ θ, f θ ∂angleMeasure
    map_add' := fun f g => integral_add (f.integrable _) (g.integrable _)
    map_smul' := fun c f => by simp only [BoundedContinuousFunction.smul_apply,
      RingHom.id_apply, smul_eq_mul, integral_const_mul] }
  1 (fun f => by simpa only [one_mul] using f.norm_integral_le_norm angleMeasure)

theorem meanL_apply (f : Profiles) : meanL f = ∫ θ, f θ ∂angleMeasure := rfl

def evalRing (θ : ℝ) : Profiles →+* ℝ where
  toFun f := f θ
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem exponential_apply (f : Profiles) (θ : ℝ) :
    NormedSpace.exp f θ = Real.exp (f θ) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.map_exp (evalRing θ) (BoundedContinuousFunction.evalCLM ℝ θ).continuous f

def exponentialMean (f : Profiles) : ℝ := meanL (NormedSpace.exp f)

theorem exponentialMean_integral (f : Profiles) :
    exponentialMean f = ∫ θ, Real.exp (f θ) ∂angleMeasure := by
  simp only [exponentialMean, meanL_apply, exponential_apply]

theorem exponential_contDiff (n : WithTop ℕ∞) :
    ContDiff ℝ n (NormedSpace.exp : Profiles → Profiles) :=
  (show AnalyticOnNhd ℝ (NormedSpace.exp : Profiles → Profiles) Set.univ from
    fun f _ => NormedSpace.exp_analytic f).contDiff

theorem exponentialMean_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n exponentialMean :=
  meanL.contDiff.comp (exponential_contDiff n)

def sinAngle : Profiles := BoundedContinuousFunction.mkOfBound
  ⟨fun θ => Real.sin (2*Real.pi*θ), by fun_prop⟩ 2 (fun θ φ => by
    calc
      _ ≤ ‖Real.sin (2*Real.pi*θ)‖+‖Real.sin (2*Real.pi*φ)‖ := by simpa only [dist_eq_norm] using norm_sub_le _ _
      _ ≤ 2 := by simpa only [Real.norm_eq_abs, one_add_one_eq_two] using
        add_le_add (Real.abs_sin_le_one (2*Real.pi*θ)) (Real.abs_sin_le_one (2*Real.pi*φ)))

def cosAngle : Profiles := BoundedContinuousFunction.mkOfBound
  ⟨fun θ => Real.cos (2*Real.pi*θ), by fun_prop⟩ 2 (fun θ φ => by
    calc
      _ ≤ ‖Real.cos (2*Real.pi*θ)‖+‖Real.cos (2*Real.pi*φ)‖ := by simpa only [dist_eq_norm] using norm_sub_le _ _
      _ ≤ 2 := by simpa only [Real.norm_eq_abs, one_add_one_eq_two] using
        add_le_add (Real.abs_cos_le_one (2*Real.pi*θ)) (Real.abs_cos_le_one (2*Real.pi*φ)))

def harmonics (a b c d : ℝ) : Profiles :=
  a • (cosAngle^2-sinAngle^2)+b • (sinAngle*cosAngle)+c • sinAngle+d • cosAngle

theorem harmonics_apply (a b c d θ : ℝ) : harmonics a b c d θ =
    a*(Real.cos (2*Real.pi*θ)^2-Real.sin (2*Real.pi*θ)^2)+
    b*(Real.sin (2*Real.pi*θ)*Real.cos (2*Real.pi*θ))+
    c*Real.sin (2*Real.pi*θ)+d*Real.cos (2*Real.pi*θ) := rfl

#print axioms meanL_apply
#print axioms exponential_apply
#print axioms exponentialMean_integral
#print axioms exponential_contDiff
#print axioms exponentialMean_contDiff
#print axioms harmonics_apply

end
end UnifiedTheory.Audit.KFCausalBoundedAngleExponential
