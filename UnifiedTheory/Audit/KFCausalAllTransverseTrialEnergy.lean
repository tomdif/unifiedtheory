/- All transverse directional derivatives of the same repaired physical
trial are in L2. A single integrable bound includes the full shear. -/
import UnifiedTheory.Audit.KFCausalTransverseTrialDerivative
import UnifiedTheory.Audit.KFCausalTransverseFlowBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalAllTransverseTrialEnergy
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalCoupledCoordinateHomeomorph
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalTransverseDilationPullback
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalDampedProductDomain
open UnifiedTheory.Audit.KFCausalTransverseClockWeights
open UnifiedTheory.Audit.KFCausalTransverseFlowBounds
open UnifiedTheory.Audit.KFCausalTransverseTrialDerivative

def boundDensity (ε a : ℝ) (ψ : SchwartzMap TailSpace ℂ) (v : Transverse) (z : Configuration) : ℝ :=
  (50*‖v‖^2)*(baseDensity ε a z.1*(1+Real.exp (-phase ε z.1)))*
    ‖pullback (phase ε z.1) (gradientNorm ψ) z.2‖^2

theorem boundDensity_continuous (ε a : ℝ) (ψ : SchwartzMap TailSpace ℂ) (v : Transverse) :
    Continuous (boundDensity ε a ψ v) := by
  have hc : Continuous (fun s => baseDensity ε a s*(1+Real.exp (-phase ε s))) :=
    (baseDensity_continuous ε a).mul (continuous_const.add (Real.continuous_exp.comp (phase_continuous ε).neg))
  exact (continuous_const.mul (hc.comp continuous_fst)).mul
    ((gradientNorm_pullback_continuous ε ψ).norm.pow 2)

theorem boundDensity_nonnegative (ε a : ℝ) (hε : 0 < ε) (ψ : SchwartzMap TailSpace ℂ)
    (v : Transverse) (z : Configuration) : 0 ≤ boundDensity ε a ψ v z := by
  unfold boundDensity baseDensity
  positivity

theorem boundDensity_integrable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : SchwartzMap TailSpace ℂ) (v : Transverse) : Integrable (boundDensity ε a ψ v) := by
  have hm : AEStronglyMeasurable (boundDensity ε a ψ v) volume := (boundDensity_continuous ε a ψ v).aestronglyMeasurable
  rw [Measure.volume_eq_prod ℝ Transverse] at hm ⊢
  apply (integrable_prod_iff hm).mpr
  constructor
  · apply Filter.Eventually.of_forall
    intro s
    exact ((pullback_square_integrable_iff (phase ε s) (gradientNorm ψ)).mpr
      (gradientNorm_square_integrable ψ)).const_mul ((50*‖v‖^2)*(baseDensity ε a s*(1+Real.exp (-phase ε s))))
  · have hn (s : ℝ) (x : Transverse) : ‖boundDensity ε a ψ v (s,x)‖=boundDensity ε a ψ v (s,x) :=
      Real.norm_of_nonneg (boundDensity_nonnegative ε a hε ψ v (s,x))
    simp_rw [hn]
    simp only [boundDensity,integral_const_mul,pullback_square_integral]
    exact ((combinedDensity_integrable ε a hε ha).const_mul (50*‖v‖^2)).mul_const _

theorem all_derivative_density_bound (ε a p : ℝ) (hε : 0 < ε) (ψ : SchwartzMap TailSpace ℂ)
    (v : Transverse) (z : Configuration) :
    ‖derivative v (trialFunction ε a p ψ) z‖^2 ≤ boundDensity ε a ψ v z := by
  have hb : 0 ≤ baseDensity ε a z.1 := by unfold baseDensity; positivity
  calc
    _ ≤ baseDensity ε a z.1*‖flow (-phase ε z.1) v‖^2*
        ‖pullback (phase ε z.1) (gradientNorm ψ) z.2‖^2 := derivative_density_bound ε a p hε ψ v z.1 z.2
    _ ≤ baseDensity ε a z.1*(50*(1+Real.exp (-phase ε z.1))*‖v‖^2)*
        ‖pullback (phase ε z.1) (gradientNorm ψ) z.2‖^2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (flow_norm_square_bound (phase ε z.1) v) hb) (sq_nonneg _)
    _ = _ := by unfold boundDensity; ring

theorem all_derivative_energy (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : SchwartzMap TailSpace ℂ) (v : Transverse) :
    Integrable (fun z : Configuration => ‖derivative v (trialFunction ε a p ψ) z‖^2) := by
  apply (boundDensity_integrable ε a hε ha ψ v).mono'
    ((derivative_continuous ε a p ψ v).norm.pow 2).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact all_derivative_density_bound ε a p hε ψ v z

theorem all_derivative_memLp (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : SchwartzMap TailSpace ℂ) (v : Transverse) : MemLp (derivative v (trialFunction ε a p ψ)) 2 :=
  (memLp_two_iff_integrable_sq_norm (derivative_continuous ε a p ψ v).aestronglyMeasurable).mpr
    (all_derivative_energy ε a p hε ha ψ v)

#print axioms boundDensity_continuous
#print axioms boundDensity_nonnegative
#print axioms boundDensity_integrable
#print axioms all_derivative_density_bound
#print axioms all_derivative_energy
#print axioms all_derivative_memLp

end
end UnifiedTheory.Audit.KFCausalAllTransverseTrialEnergy
