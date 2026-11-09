/- Scalar clock estimates for a dense product-core candidate. The shifted
clock half and full clock are controlled by already proved clock moments;
the revised transverse derivative weight is bounded by the old damped
scalar estimate, without importing the old coordinate unitary. -/
import UnifiedTheory.Audit.KFCausalClockTrialWeights
import UnifiedTheory.Audit.KFCausalTransverseClockWeights
import UnifiedTheory.Audit.KFCausalWeightedProductTotality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoreWeights
noncomputable section
open MeasureTheory Filter
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalDampedGaussianMomentum
open UnifiedTheory.Audit.KFCausalDampedGaussianTotality
open UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
open UnifiedTheory.Audit.KFCausalClockTrialWeights
open UnifiedTheory.Audit.KFCausalTransverseClockWeights (baseDensity baseDensity_continuous)

def halfScalar (ε a : ℝ) (hε : 0 < ε) (q : ℝ) : ℂ :=
  (Real.sqrt (clock ε hε q+ε):ℂ)*realTrial ε a q

theorem halfScalar_continuous (ε a : ℝ) (hε : 0 < ε) : Continuous (halfScalar ε a hε) := by
  have hc : Continuous (clock ε hε) := Real.continuous_exp.comp (chartIso ε hε).symm.toHomeomorph.continuous
  exact (Complex.continuous_ofReal.comp (hc.add continuous_const).sqrt).mul (realTrial_continuous ε a)

theorem halfScalar_memLp (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) : MemLp (halfScalar ε a hε) 2 := by
  apply (memLp_two_iff_integrable_sq_norm (halfScalar_continuous ε a hε).aestronglyMeasurable).mpr
  apply ((clock_energy ε a hε ha).add ((realTrial_square_integrable ε a hε.le ha).const_mul ε)).congr
  filter_upwards [] with q
  simp only [Pi.add_apply,halfScalar,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [Real.sq_sqrt (by unfold clock; positivity)]
  ring

theorem halfScalar_ne_zero (ε a : ℝ) (hε : 0 < ε) (q : ℝ) : halfScalar ε a hε q ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by unfold clock; positivity)).ne')
    (realTrial_ne_zero ε a q)

def dressedScalar (ε a : ℝ) (hε : 0 < ε) (p : ℝ) : ℝ → ℂ := modulate p (halfScalar ε a hε)
def wholeScalar (ε a : ℝ) (hε : 0 < ε) (p q : ℝ) : ℂ :=
  (clock ε hε q+ε:ℂ)*modulate p (realTrial ε a) q

theorem dressedScalar_memLp (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : ℝ) :
    MemLp (dressedScalar ε a hε p) 2 :=
  KFCausalWeightedProductTotality.modulate_memLp _ (halfScalar_memLp ε a hε ha) p

theorem wholeScalar_memLp (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : ℝ) :
    MemLp (wholeScalar ε a hε p) 2 := by
  have he : wholeScalar ε a hε p = clockTrial ε a hε p 1+
      fun q => (ε:ℂ)*modulate p (realTrial ε a) q := by
    funext q
    simp only [wholeScalar,clockTrial,clock,one_mul,Pi.add_apply,add_mul]
  rw [he]
  exact (clockTrial_one_memLp ε a hε ha p).add ((modulated_memLp ε a p hε.le ha).const_mul (ε:ℂ))

theorem combinedDensity_integrable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    Integrable (fun s : ℝ => baseDensity ε a s*(1+Real.exp (-s))) := by
  have hc : Continuous (fun s : ℝ => baseDensity ε a s*(1+Real.exp (-s))) :=
    (baseDensity_continuous ε a).mul (continuous_const.add (Real.continuous_exp.comp continuous_id.neg))
  apply (KFCausalTransverseClockWeights.combinedDensity_integrable ε a hε ha).mono' hc.aestronglyMeasurable
  filter_upwards [] with s
  have hb : 0 ≤ baseDensity ε a s := by unfold baseDensity; positivity
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hb (by positivity))]
  apply mul_le_mul_of_nonneg_left _ hb
  apply add_le_add_right
  apply Real.exp_le_exp.mpr
  unfold KFCausalCoupledLongitudinalFlow.phase
  have ht : 0 ≤ ε*Real.exp (-s) := by positivity
  linarith

#print axioms halfScalar_continuous
#print axioms halfScalar_memLp
#print axioms halfScalar_ne_zero
#print axioms dressedScalar_memLp
#print axioms wholeScalar_memLp
#print axioms combinedDensity_integrable

end
end UnifiedTheory.Audit.KFCausalClockFloorCoreWeights
