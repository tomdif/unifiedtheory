/- Actual simultaneous-rotation entropy estimates in squared l2 displacement.
Stationary ground normalization cancels the unknown signed ground gain. -/
import UnifiedTheory.Clay.YangMills.WilsonJointRotation

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonJointEntropy
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonTemporalGauge WilsonStationaryEntropy CompactDensityEntropy WilsonSymmetricLinkChange

variable (n : ℕ) [NeZero n]
local instance haar_left : (WilsonSlabOperator.measure n).IsMulLeftInvariant := by
  unfold WilsonSlabOperator.measure WilsonSlabGauge.spatialHaar
  infer_instance

theorem rotation_integral (q : Slice n) (F : Slice n → ℝ) :
    (∫ u, F (q*u) ∂measure n) = ∫ u, F u ∂measure n :=
  integral_mul_left_eq_self F q

def logGain (β : ℝ) (hβ : 0 ≤ β) (q : Slice n) (u : Slice n) : ℝ :=
  Real.log (ground n β hβ (q*u)) - Real.log (ground n β hβ u)

theorem logGain_continuous (β : ℝ) (hβ : 0 ≤ β) (q : Slice n) :
    Continuous (logGain n β hβ q) := by
  have hg := (ground n β hβ).continuous.log (fun u => (ground_pos n β hβ u).ne')
  exact (hg.comp ((continuous_const.mul continuous_id))).sub hg

def groundGain (β : ℝ) (hβ : 0 ≤ β) (q : Slice n) : ℝ :=
  ∫ u, (ground n β hβ u)^2 * logGain n β hβ q u ∂measure n

/-- The unknown ground term is minus one half of a genuine relative entropy. -/
theorem ground_entropy_eq (β : ℝ) (hβ : 0 ≤ β) (q : Slice n) :
    entropy (measure n) (fun u => (ground n β hβ u)^2)
      (fun u => (ground n β hβ (q*u))^2) = -2*groundGain n β hβ q := by
  unfold entropy groundGain
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  rw [Real.log_div (sq_pos_of_pos (ground_pos n β hβ u)).ne'
    (sq_pos_of_pos (ground_pos n β hβ (q*u))).ne', Real.log_pow, Real.log_pow]
  unfold logGain
  norm_num
  ring

theorem groundGain_nonpos (β : ℝ) (hβ : 0 ≤ β) (q : Slice n) :
    groundGain n β hβ q ≤ 0 := by
  have hm : (∫ u, (ground n β hβ (q*u))^2 ∂measure n) = 1 :=
    (rotation_integral n q (fun u => (ground n β hβ u)^2)).trans
      (ground_square_integral n β hβ)
  have h := entropy_nonneg (measure n) _ _ ((ground n β hβ).continuous.pow 2)
    (((ground n β hβ).continuous.comp ((continuous_const.mul continuous_id))).pow 2)
    (fun u => sq_pos_of_pos (ground_pos n β hβ u))
    (fun u => sq_pos_of_pos (ground_pos n β hβ (q*u)))
    (ground_square_integral n β hβ) hm
  simp only [Function.comp_apply, Pi.mul_apply, id_eq] at h
  rw [ground_entropy_eq] at h
  linarith

theorem rowEntropy_pair_bound (β : ℝ) (hβ : 0 ≤ β)
    (q : Slice n) (u : Slice n) :
    rowEntropy n β hβ u (q*u) + rowEntropy n β hβ u (q⁻¹*u) ≤
      18*β*WilsonJointRotation.cost n q + logGain n β hβ q u + logGain n β hβ q⁻¹ u := by
  have hc (w : Slice n) : Continuous (fun v => rawTransition n β hβ u v *
      (inputAction n β w v-inputAction n β u v)) :=
    (row_continuous n β hβ u).mul (((inputAction_continuous n β).comp
      (f := fun v : Slice n => (w,v)) (continuous_const.prodMk continuous_id)).sub
      ((inputAction_continuous n β).comp (f := fun v : Slice n => (u,v))
        (continuous_const.prodMk continuous_id)))
  have hp := continuous_integrable (measure n) _ (hc (q*u))
  have hm := continuous_integrable (measure n) _ (hc (q⁻¹*u))
  have h := integral_mono (hp.add hm)
    ((continuous_integrable (measure n) _ (row_continuous n β hβ u)).mul_const
      (18*β*WilsonJointRotation.cost n q)) (fun v => by
        have h := mul_le_mul_of_nonneg_left
          (WilsonJointRotation.inputAction_second_bound n β hβ q u v)
          (rawTransition_pos n β hβ u v).le
        simp only [Pi.add_apply]
        nlinarith)
  have hi := integral_add hp hm
  simp only [Pi.add_apply] at h hi
  rw [hi, integral_mul_const, rawTransition_mass, one_mul] at h
  rw [rowEntropy_formula, rowEntropy_formula]
  unfold logGain
  linarith

def meanEntropy (β : ℝ) (hβ : 0 ≤ β) (q : Slice n) : ℝ :=
  ∫ u, (ground n β hβ u)^2 * rowEntropy n β hβ u (q*u) ∂measure n

theorem meanEntropy_nonneg (β : ℝ) (hβ : 0 ≤ β) (q : Slice n) :
    0 ≤ meanEntropy n β hβ q :=
  integral_nonneg (fun u => mul_nonneg (sq_nonneg _) (rowEntropy_nonneg n β hβ u _))

theorem meanEntropy_pair_bound (β : ℝ) (hβ : 0 ≤ β)
    (q : Slice n) :
    meanEntropy n β hβ q + meanEntropy n β hβ q⁻¹ ≤ 18*β*WilsonJointRotation.cost n q := by
  have hc (r : Slice n) : Continuous (fun u : Slice n => rowEntropy n β hβ u (r*u)) :=
    (rowEntropy_continuous n β hβ).comp (f := fun u : Slice n => (u,r*u))
      (continuous_id.prodMk (continuous_const.mul continuous_id))
  have hg := (ground n β hβ).continuous.pow 2
  have he (r : Slice n) := continuous_integrable (measure n) _ (hg.mul (hc r))
  have hl (r : Slice n) :=
    continuous_integrable (measure n) _ (hg.mul (logGain_continuous n β hβ r))
  have h := integral_mono ((he q).add (he q⁻¹))
    ((((continuous_integrable (measure n) _ hg).mul_const (18*β*WilsonJointRotation.cost n q)).add
      (hl q)).add (hl q⁻¹)) (fun u => by
        have h := mul_le_mul_of_nonneg_left (rowEntropy_pair_bound n β hβ q u)
          (sq_nonneg (ground n β hβ u))
        simp only [Pi.add_apply, Pi.mul_apply]
        nlinarith)
  have headd := integral_add (he q) (he q⁻¹)
  have hladd := integral_add
    (((continuous_integrable (measure n) _ hg).mul_const (18*β*WilsonJointRotation.cost n q)).add
      (hl q)) (hl q⁻¹)
  have hcadd := integral_add
    ((continuous_integrable (measure n) _ hg).mul_const (18*β*WilsonJointRotation.cost n q)) (hl q)
  simp only [Pi.add_apply, Pi.mul_apply] at h headd hladd hcadd
  rw [headd, hladd, hcadd, integral_mul_const, ground_square_integral, one_mul] at h
  change meanEntropy n β hβ q + meanEntropy n β hβ q⁻¹ ≤
    18*β*WilsonJointRotation.cost n q + groundGain n β hβ q + groundGain n β hβ q⁻¹ at h
  linarith [groundGain_nonpos n β hβ q, groundGain_nonpos n β hβ q⁻¹]

/-- The coefficient is linear in beta and quadratic in the actual rotation displacement. -/
theorem meanEntropy_bound (β : ℝ) (hβ : 0 ≤ β)
    (q : Slice n) :
    meanEntropy n β hβ q ≤ 18*β*WilsonJointRotation.cost n q := by
  linarith [meanEntropy_pair_bound n β hβ q, meanEntropy_nonneg n β hβ q⁻¹]

theorem meanEntropy_eq_groundLaw (β : ℝ) (hβ : 0 ≤ β)
    (q : Slice n) :
    meanEntropy n β hβ q =
      ∫ u, rowEntropy n β hβ u (q*u) ∂WilsonGroundHeatBath.groundLaw n β hβ := by
  exact (GroundStateDirichlet.stationary_integral (measure n)
    (ground n β hβ) (ground n β hβ).continuous _).symm

/-- A collective lower second difference of the actual log ground amplitude. -/
theorem log_second_lower (β : ℝ) (hβ : 0 ≤ β) (q u : Slice n) :
    -(18*β*WilsonJointRotation.cost n q) ≤
      Real.log (ground n β hβ (q*u)) + Real.log (ground n β hβ (q⁻¹*u)) -
        2*Real.log (ground n β hβ u) := by
  have h := rowEntropy_pair_bound n β hβ q u
  have hp := rowEntropy_nonneg n β hβ u (q*u)
  have hm := rowEntropy_nonneg n β hβ u (q⁻¹*u)
  unfold logGain at h
  linarith

/-- A ground-density entropy bound for one simultaneous rotation, without a link-count loss. -/
theorem ground_entropy_bound (β : ℝ) (hβ : 0 ≤ β) (q : Slice n) :
    entropy (measure n) (fun u => (ground n β hβ u)^2)
      (fun u => (ground n β hβ (q*u))^2) ≤ 36*β*WilsonJointRotation.cost n q := by
  have hp := continuous_integrable (measure n) _
    (((ground n β hβ).continuous.pow 2).mul (logGain_continuous n β hβ q))
  have hm := continuous_integrable (measure n) _
    (((ground n β hβ).continuous.pow 2).mul (logGain_continuous n β hβ q⁻¹))
  have h := integral_mono
    ((continuous_integrable (measure n) _ ((ground n β hβ).continuous.pow 2)).mul_const
      (-(18*β*WilsonJointRotation.cost n q))) (hp.add hm) (fun u => by
        have hh := mul_le_mul_of_nonneg_left (log_second_lower n β hβ q u)
          (sq_nonneg (ground n β hβ u))
        simp only [Pi.add_apply, Pi.mul_apply]
        unfold logGain
        nlinarith)
  have he := integral_add hp hm
  simp only [Pi.add_apply, Pi.mul_apply] at h he
  rw [he, integral_mul_const, ground_square_integral, one_mul] at h
  change -(18*β*WilsonJointRotation.cost n q) ≤
    groundGain n β hβ q + groundGain n β hβ q⁻¹ at h
  rw [ground_entropy_eq]
  linarith [groundGain_nonpos n β hβ q⁻¹]

end
end UnifiedTheory.Clay.YangMills.WilsonJointEntropy
