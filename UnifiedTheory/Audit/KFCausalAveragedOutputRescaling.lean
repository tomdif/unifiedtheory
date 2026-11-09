/- Orthogonal static/growing splitting and exact time rescaling on the
angle-L2 output space. These identities retain the actual averaged energy. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedOutputTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalAveragedOutputRescaling
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalFiniteOutputRescaling
open UnifiedTheory.Audit.KFCausalPhysicalEnergyTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedOutputTransport (timeOutputLp)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

abbrev EnergyOutputSpace := Lp (Output (Fin 8) Hilbert) 2 angleMeasure

def staticOutputLp : EnergyOutputSpace →L[ℂ] EnergyOutputSpace := staticOutput.compLpL 2 angleMeasure
def growingOutputLp : EnergyOutputSpace →L[ℂ] EnergyOutputSpace := growingOutput.compLpL 2 angleMeasure

theorem staticOutputLp_norm_le_one : ‖staticOutputLp‖ ≤ 1 := by
  apply (ContinuousLinearMap.norm_compLpL_le staticOutput).trans
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using selected_norm_le (fun i : Fin 8 => i.val<3) x

theorem growingOutputLp_norm_le_one : ‖growingOutputLp‖ ≤ 1 := by
  apply (ContinuousLinearMap.norm_compLpL_le growingOutput).trans
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using selected_norm_le (fun i : Fin 8 => ¬ i.val<3) x

theorem timeOutputLp_inner (s t : ℝ) (x y : EnergyOutputSpace) :
    inner ℂ (timeOutputLp s t x) (timeOutputLp s t y) =
      inner ℂ (staticOutputLp x) (staticOutputLp y) +
        (Real.exp (2*(t-s)):ℂ)*inner ℂ (growingOutputLp x) (growingOutputLp y) := by
  have he : (fun θ => inner ℂ (timeOutputLp s t x θ) (timeOutputLp s t y θ)) =ᵐ[angleMeasure]
      (fun θ => inner ℂ (staticOutputLp x θ) (staticOutputLp y θ) +
        (Real.exp (2*(t-s)):ℂ)*inner ℂ (growingOutputLp x θ) (growingOutputLp y θ)) := by
    filter_upwards [(timeOutput s t).coeFn_compLp x,(timeOutput s t).coeFn_compLp y,
      staticOutput.coeFn_compLp x,staticOutput.coeFn_compLp y,
      growingOutput.coeFn_compLp x,growingOutput.coeFn_compLp y] with θ h1 h2 h3 h4 h5 h6
    change inner ℂ ((timeOutput s t).compLp x θ) ((timeOutput s t).compLp y θ) =
      inner ℂ (staticOutput.compLp x θ) (staticOutput.compLp y θ) +
        (Real.exp (2*(t-s)):ℂ)*inner ℂ (growingOutput.compLp x θ) (growingOutput.compLp y θ)
    rw [h1,h2,h3,h4,h5,h6,timeOutput_inner]
  rw [L2.inner_def,integral_congr_ae he,
    integral_add (L2.integrable_inner (𝕜 := ℂ) (staticOutputLp x) (staticOutputLp y))
      ((L2.integrable_inner (𝕜 := ℂ) (growingOutputLp x) (growingOutputLp y)).const_mul _),
    integral_const_mul,← L2.inner_def,← L2.inner_def]

theorem norm_timeOutputLp_sq (s t : ℝ) (x : EnergyOutputSpace) :
    ‖timeOutputLp s t x‖^2 = ‖staticOutputLp x‖^2+Real.exp (2*(t-s))*‖growingOutputLp x‖^2 := by
  apply Complex.ofReal_injective
  simpa only [inner_self_eq_norm_sq_to_K,Complex.ofReal_pow,Complex.ofReal_mul,
    Complex.ofReal_add] using timeOutputLp_inner s t x x

theorem timeOutputLp_self (s : ℝ) (x : EnergyOutputSpace) : timeOutputLp s s x = x := by
  apply Lp.ext
  filter_upwards [(timeOutput s s).coeFn_compLp x] with θ hθ
  refine hθ.trans ?_
  apply PiLp.ext
  intro i
  simp only [timeOutput_apply,sub_self,Real.exp_zero,Complex.ofReal_one,one_smul,ite_self]

theorem split_norm (x : EnergyOutputSpace) : ‖x‖^2 = ‖staticOutputLp x‖^2+‖growingOutputLp x‖^2 := by
  have h := norm_timeOutputLp_sq 0 0 x
  simpa only [timeOutputLp_self,sub_self,mul_zero,Real.exp_zero,one_mul] using h

#print axioms staticOutputLp_norm_le_one
#print axioms growingOutputLp_norm_le_one
#print axioms timeOutputLp_inner
#print axioms norm_timeOutputLp_sq
#print axioms timeOutputLp_self
#print axioms split_norm

end
end UnifiedTheory.Audit.KFCausalAveragedOutputRescaling
