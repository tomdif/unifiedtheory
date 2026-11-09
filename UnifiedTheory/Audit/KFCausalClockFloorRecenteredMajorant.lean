/- Integrability of the actual recentered envelope, including the clock
Jacobian. Positive clock width and positive clock floor are retained. -/
import UnifiedTheory.Audit.KFCausalClockFloorRecenteredJacobian
import UnifiedTheory.Audit.KFCausalClockFloorBoostedOrbitDensityBound
import UnifiedTheory.Audit.KFCausalClockFloorBoostedEnergyIdentification

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorRecenteredMajorant
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredJacobian
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (clockFactor clockFactor_norm)
open UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy (dampedClockFunction dampedClockFunction_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedEnergyIdentification (dampedClock_density)
open UnifiedTheory.Audit.KFCausalClockFloorCenteredEstimates (energy energy_eq)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (physicalGaussian)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments (physicalGaussian_memLp)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization (physicalGaussian_mass gaussianMass)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth)

theorem clock_change_integrable (ε : ℝ) (hε : 0 < ε) (g : ℝ → ℝ) :
    Integrable g ↔ Integrable (fun s => (Real.exp s+ε)*g (chart ε s)) := by
  have he := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun s (_ : s ∈ (univ : Set ℝ)) => (chart_derivative ε s).hasDerivWithinAt)
    (chart_strictMono ε hε).injective.injOn g
  have hw (s : ℝ) : |Real.exp s+ε| = Real.exp s+ε := abs_of_pos (by positivity)
  simpa only [image_univ,(chart_surjective ε hε).range_eq,integrableOn_univ,hw,smul_eq_mul] using he

theorem clockFactor_real_square (a u : ℝ) :
    ‖clockFactor a (u:ℂ)‖^2 = Real.exp (-2*a*u^2) := by
  have he := congrArg (fun r : ℝ => r^2) (clockFactor_norm a u 0)
  simp only [Complex.ofReal_zero,zero_mul,add_zero,zero_pow (by decide : 2 ≠ 0),sub_zero] at he
  rw [he,← Real.exp_nat_mul]
  congr 1
  norm_num only [Nat.cast_ofNat]
  ring

def clockWeight (ε a : ℝ) (hε : 0 < ε) (u : ℝ) : ℝ :=
  clockJacobian ε hε u*‖clockFactor a (u:ℂ)‖^2

theorem clockWeight_chart (ε a s : ℝ) (hε : 0 < ε) :
    (Real.exp s+ε)*clockWeight ε a hε (chart ε s) = ‖dampedClockFunction ε a s‖^2 := by
  have hc : (chartIso ε hε).symm (chart ε s) = s := (chartIso ε hε).symm_apply_apply s
  rw [clockWeight,clockJacobian,hc,clockFactor_real_square,dampedClock_density ε a s hε]
  unfold KFCausalClockFloorFlow.clock
  ring

theorem clockWeight_integrable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    Integrable (clockWeight ε a hε) := by
  rw [clock_change_integrable ε hε]
  simp_rw [clockWeight_chart ε a _ hε]
  have hm := dampedClockFunction_memLp ε a hε ha
  exact (memLp_two_iff_integrable_sq_norm hm.1).mp hm

def gaussianEnvelope (c : ℝ) (ξ : Transverse) : ℝ := Real.exp (-c*energy ξ)

theorem gaussianEnvelope_square (c : ℝ) (ξ : Transverse) :
    gaussianEnvelope c ξ = ‖physicalGaussian (c/2*groundWidth 1) (c/2*neutralWidth 1) ξ‖^2 := by
  rw [physicalGaussian,Complex.norm_exp,← Real.exp_nat_mul]
  simp only [Complex.neg_re,Complex.ofReal_re]
  simp [gaussianEnvelope,energy_eq,groundWidth,neutralWidth,Fin.sum_univ_succ]
  ring

theorem gaussianEnvelope_integrable (c : ℝ) (hc : 0 < c) : Integrable (gaussianEnvelope c) := by
  have hp : 0 < c/2*groundWidth 1 := by unfold groundWidth; norm_num; positivity
  have hn : 0 < c/2*neutralWidth 1 := by unfold neutralWidth groundWidth; norm_num; positivity
  have hm := physicalGaussian_memLp (c/2*groundWidth 1) (c/2*neutralWidth 1) hp hn
  change Integrable (fun ξ => gaussianEnvelope c ξ)
  simp_rw [gaussianEnvelope_square]
  exact (memLp_two_iff_integrable_sq_norm hm.1).mp hm

theorem gaussianEnvelope_mass :
    (∫ ξ : Transverse, gaussianEnvelope 2 ξ) = gaussianMass (groundWidth 1) (neutralWidth 1) := by
  simp_rw [gaussianEnvelope_square]
  norm_num only [div_self (by norm_num : (2:ℝ) ≠ 0),one_mul]
  exact physicalGaussian_mass _ _ (KFCausalChargeGaussianGeometry.groundWidth_positive 1 one_ne_zero)

theorem productEnvelope_integrable (ε a B : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    Integrable (fun z : ℝ × Transverse => B*clockWeight ε a hε z.1*gaussianEnvelope (1/4) z.2) := by
  rw [Measure.volume_eq_prod ℝ Transverse]
  exact ((clockWeight_integrable ε a hε ha).const_mul B).mul_prod
    (gaussianEnvelope_integrable (1/4) (by norm_num))

#print axioms clock_change_integrable
#print axioms clockFactor_real_square
#print axioms clockWeight_chart
#print axioms clockWeight_integrable
#print axioms gaussianEnvelope_square
#print axioms gaussianEnvelope_integrable
#print axioms gaussianEnvelope_mass
#print axioms productEnvelope_integrable

end
end UnifiedTheory.Audit.KFCausalClockFloorRecenteredMajorant
