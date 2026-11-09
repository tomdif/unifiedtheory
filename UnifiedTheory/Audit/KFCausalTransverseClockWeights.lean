/- Integrable clock weights controlling the full transverse flow norm,
including its undilated fifth direction and its shear. -/
import UnifiedTheory.Audit.KFCausalClockTrialWeights

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalTransverseClockWeights
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalCoupledDampedGaussian
open UnifiedTheory.Audit.KFCausalDampedGaussianMomentum
open UnifiedTheory.Audit.KFCausalClockTrialWeights

def baseDensity (ε a s : ℝ) : ℝ := (Real.exp s+ε)*‖realTrial ε a (chart ε s)‖^2

theorem baseDensity_continuous (ε a : ℝ) : Continuous (baseDensity ε a) :=
  (Real.continuous_exp.add continuous_const).mul (((realTrial_continuous ε a).comp (chart_continuous ε)).norm.pow 2)

theorem baseDensity_integrable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) : Integrable (baseDensity ε a) := by
  apply (chart_gaussian_integrable ε a hε ha).mono' (baseDensity_continuous ε a).aestronglyMeasurable
  filter_upwards [] with s
  rw [Real.norm_eq_abs,abs_of_nonneg (by unfold baseDensity; positivity)]
  exact mul_le_mul_of_nonneg_left (realTrial_square_bound ε a (chart ε s) hε.le) (by positivity)

theorem baseDensity_damped (ε a s : ℝ) :
    baseDensity ε a s*Real.exp (-phase ε s)=dampedDensity ε a s := by
  unfold baseDensity realTrial dampedGaussian dampedDensity
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [mul_assoc,← Real.exp_add]
  congr 2
  ring

theorem combinedDensity_integrable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    Integrable (fun s => baseDensity ε a s*(1+Real.exp (-phase ε s))) := by
  simpa only [mul_add,mul_one,baseDensity_damped] using
    (baseDensity_integrable ε a hε ha).add (damped_density_integrable ε a hε ha)

#print axioms baseDensity_continuous
#print axioms baseDensity_integrable
#print axioms baseDensity_damped
#print axioms combinedDensity_integrable

end
end UnifiedTheory.Audit.KFCausalTransverseClockWeights
