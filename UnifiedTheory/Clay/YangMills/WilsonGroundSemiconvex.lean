/- A quadratic symmetric bound on the actual ground amplitude, and its
consequence at a maximum along one true spatial link. No mixing is assumed. -/
import UnifiedTheory.Clay.YangMills.WilsonGroundSmallRotation

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonGroundSemiconvex
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonSymmetricLinkChange WilsonStationaryEntropy CompactDensityEntropy
open scoped Quaternion

variable (n : ℕ) [NeZero n]

/-- A lower second difference, not a two-sided Hessian or a convexity assertion. -/
theorem log_second_lower (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (u : Slice n) :
    -(66*β*‖(q : ℍ)-1‖^2) ≤
      Real.log (ground n β hβ (shift n e q u)) +
        Real.log (ground n β hβ (shift n e q⁻¹ u)) - 2*Real.log (ground n β hβ u) := by
  have h := rowEntropy_pair_bound n β hβ e q u
  have hp := rowEntropy_nonneg n β hβ u (shift n e q u)
  have hm := rowEntropy_nonneg n β hβ u (shift n e q⁻¹ u)
  unfold logGain at h
  linarith

theorem ground_product_lower (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (u : Slice n) :
    Real.exp (-(66*β*‖(q : ℍ)-1‖^2))*(ground n β hβ u)^2 ≤
      ground n β hβ (shift n e q u)*ground n β hβ (shift n e q⁻¹ u) := by
  have h := Real.exp_le_exp.mpr (show
      -(66*β*‖(q : ℍ)-1‖^2) +
        (Real.log (ground n β hβ u)+Real.log (ground n β hβ u)) ≤
      Real.log (ground n β hβ (shift n e q u)) +
        Real.log (ground n β hβ (shift n e q⁻¹ u)) by
    linarith [log_second_lower n β hβ e q u])
  simpa only [Real.exp_add, Real.exp_log (ground_pos n β hβ _), pow_two] using h

/-- At a link maximum, the opposite rotation supplies the missing one-sided bound. -/
theorem at_link_maximum (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (u : Slice n)
    (hmax : ∀ r : Q, ground n β hβ (shift n e r u) ≤ ground n β hβ u) (q : Q) :
    Real.exp (-(66*β*‖(q : ℍ)-1‖^2))*ground n β hβ u ≤
      ground n β hβ (shift n e q u) := by
  have h := (ground_product_lower n β hβ e q u).trans
    (mul_le_mul_of_nonneg_left (hmax q⁻¹) (ground_pos n β hβ _).le)
  have hh : (Real.exp (-(66*β*‖(q : ℍ)-1‖^2))*ground n β hβ u)*ground n β hβ u ≤
      ground n β hβ (shift n e q u)*ground n β hβ u := by nlinarith
  exact (mul_le_mul_iff_left₀ (ground_pos n β hβ u)).mp hh

theorem density_at_link_maximum (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (u : Slice n)
    (hmax : ∀ r : Q, ground n β hβ (shift n e r u) ≤ ground n β hβ u) (q : Q) :
    Real.exp (-(132*β*‖(q : ℍ)-1‖^2))*(ground n β hβ u)^2 ≤
      (ground n β hβ (shift n e q u))^2 := by
  have h := (sq_le_sq₀ (mul_nonneg (Real.exp_pos _).le
    (ground_pos n β hβ u).le) (ground_pos n β hβ _).le).mpr
    (at_link_maximum n β hβ e u hmax q)
  have he : (Real.exp (-(66*β*‖(q : ℍ)-1‖^2)))^2 =
      Real.exp (-(132*β*‖(q : ℍ)-1‖^2)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simpa only [mul_pow, he] using h

/-- The shifted true ground density has a quadratic relative-entropy cost. -/
theorem ground_entropy_bound (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) :
    entropy (measure n) (fun u => (ground n β hβ u)^2)
      (fun u => (ground n β hβ (shift n e q u))^2) ≤ 132*β*‖(q : ℍ)-1‖^2 := by
  have hp := continuous_integrable (measure n) _
    (((ground n β hβ).continuous.pow 2).mul (logGain_continuous n β hβ e q))
  have hm := continuous_integrable (measure n) _
    (((ground n β hβ).continuous.pow 2).mul (logGain_continuous n β hβ e q⁻¹))
  have h := integral_mono
    ((continuous_integrable (measure n) _ ((ground n β hβ).continuous.pow 2)).mul_const
      (-(66*β*‖(q : ℍ)-1‖^2))) (hp.add hm) (fun u => by
        have hh := mul_le_mul_of_nonneg_left (log_second_lower n β hβ e q u)
          (sq_nonneg (ground n β hβ u))
        simp only [Pi.add_apply, Pi.mul_apply]
        unfold logGain
        nlinarith)
  have he := integral_add hp hm
  simp only [Pi.add_apply, Pi.mul_apply] at h he
  rw [he, integral_mul_const, ground_square_integral, one_mul] at h
  change -(66*β*‖(q : ℍ)-1‖^2) ≤
    groundGain n β hβ e q + groundGain n β hβ e q⁻¹ at h
  rw [ground_entropy_eq]
  linarith [groundGain_nonpos n β hβ e q⁻¹]

end
end UnifiedTheory.Clay.YangMills.WilsonGroundSemiconvex
