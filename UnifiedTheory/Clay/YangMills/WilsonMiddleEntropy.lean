/- The explicit middle bridge has a uniform paired translation-entropy
budget for every endpoint pair. This does not bound log-ground insertions
or close the signed variance-profile remainder. -/
import UnifiedTheory.Clay.YangMills.WilsonMiddleBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonMiddleEntropy
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonMiddleBridge CompactDensityEntropy

variable (n : ℕ) [NeZero n]
local instance haar_left : (WilsonSlabOperator.measure n).IsMulLeftInvariant := by
  unfold WilsonSlabOperator.measure WilsonSlabGauge.spatialHaar
  infer_instance

def density (β : ℝ) (v w u : Slice n) : ℝ := weight n β v w u/mass n β v w

theorem density_pos (β : ℝ) (v w u : Slice n) : 0 < density n β v w u :=
  div_pos (weight_pos n β v w u) (mass_pos n β v w)

theorem density_continuous (β : ℝ) (v w : Slice n) : Continuous (density n β v w) :=
  (weight_continuous n β v w).div_const _

theorem density_mass (β : ℝ) (v w : Slice n) :
    (∫ u, density n β v w u ∂WilsonSlabOperator.measure n) = 1 := by
  unfold density
  rw [integral_div]
  exact div_self (mass_pos n β v w).ne'

theorem rotated_mass (β : ℝ) (q v w : Slice n) :
    (∫ u, density n β v w (q*u) ∂WilsonSlabOperator.measure n) = 1 := by
  rw [integral_mul_left_eq_self]
  exact density_mass n β v w

theorem density_integral (β : ℝ) (v w : Slice n) (H : Slice n → ℝ) :
    (∫ u, density n β v w u*H u ∂WilsonSlabOperator.measure n) =
      ∫ u, H u ∂law n β v w := by
  unfold density
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div]
  exact (law_integral n β v w H).symm

theorem log_density (β : ℝ) (v w u : Slice n) :
    Real.log (density n β v w u) =
      Real.log (spatialWeight WilsonSingleLinkStaples.character β 2 v) +
        Real.log (spatialWeight WilsonSingleLinkStaples.character β 2 w) -
          action n β v w u - Real.log (mass n β v w) := by
  rw [density, Real.log_div (weight_pos n β v w u).ne' (mass_pos n β v w).ne', weight_action]
  have hv : 0 < spatialWeight WilsonSingleLinkStaples.character β 2 v := Real.exp_pos _
  have hw : 0 < spatialWeight WilsonSingleLinkStaples.character β 2 w := Real.exp_pos _
  rw [Real.log_mul (mul_pos hv hw).ne' (Real.exp_pos _).ne',
    Real.log_mul hv.ne' hw.ne', Real.log_exp]
  ring

def meanEntropy (β : ℝ) (q v w : Slice n) : ℝ :=
  entropy (WilsonSlabOperator.measure n) (density n β v w) (fun u => density n β v w (q*u))

theorem meanEntropy_nonneg (β : ℝ) (q v w : Slice n) : 0 ≤ meanEntropy n β q v w :=
  entropy_nonneg (WilsonSlabOperator.measure n) _ _ (density_continuous n β v w)
    ((density_continuous n β v w).comp (continuous_const.mul continuous_id))
    (density_pos n β v w) (fun u => density_pos n β v w (q*u))
    (density_mass n β v w) (rotated_mass n β q v w)

theorem entropy_formula (β : ℝ) (q v w : Slice n) :
    meanEntropy n β q v w = ∫ u, (action n β v w (q*u)-action n β v w u) ∂law n β v w := by
  unfold meanEntropy entropy
  rw [← density_integral]
  apply integral_congr_ae
  filter_upwards with u
  rw [Real.log_div (density_pos n β v w u).ne' (density_pos n β v w (q*u)).ne',
    log_density, log_density]
  ring

/-- No conditioning or endpoint penalty occurs in the actual middle-law entropy budget. -/
theorem paired_bound (β : ℝ) (hβ : 0 ≤ β) (q v w : Slice n) :
    meanEntropy n β q v w+meanEntropy n β q⁻¹ v w ≤
      36*β*WilsonJointRotation.cost n q := by
  letI := law_probability n β v w
  have hA := action_continuous n β v w
  have hp := continuous_integrable (law n β v w) _
    ((hA.comp (f := fun u : Slice n => q*u) (continuous_const.mul continuous_id)).sub hA)
  have hm := continuous_integrable (law n β v w) _
    ((hA.comp (f := fun u : Slice n => q⁻¹*u) (continuous_const.mul continuous_id)).sub hA)
  have hi := integral_mono (hp.add hm) (integrable_const (36*β*WilsonJointRotation.cost n q))
    (fun u => by
      have h := action_second_bound n β hβ q v w u
      simp only [Pi.add_apply, Function.comp_apply]
      linarith)
  have he := integral_add hp hm
  simp only [Pi.add_apply, Function.comp_apply] at hi he
  rw [he, integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
  rw [entropy_formula, entropy_formula]
  exact hi

theorem bound (β : ℝ) (hβ : 0 ≤ β) (q v w : Slice n) :
    meanEntropy n β q v w ≤ 36*β*WilsonJointRotation.cost n q := by
  linarith [paired_bound n β hβ q v w, meanEntropy_nonneg n β q⁻¹ v w]

end
end UnifiedTheory.Clay.YangMills.WilsonMiddleEntropy
