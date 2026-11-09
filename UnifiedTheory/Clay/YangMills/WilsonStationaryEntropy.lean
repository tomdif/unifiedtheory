/- Stationary averaging removes the unknown ground-density contribution
from the actual temporal-gauge row entropy. Paired one-link rotations give
a volume-independent quadratic bound. No contraction is concluded. -/
import UnifiedTheory.Clay.YangMills.WilsonSymmetricLinkChange
import UnifiedTheory.Clay.YangMills.CompactDensityEntropy
import UnifiedTheory.Clay.YangMills.WilsonGroundHeatBath

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonStationaryEntropy
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonTemporalGauge WilsonTemporalInfluence WilsonSymmetricLinkChange CompactDensityEntropy
open scoped Quaternion

variable (n : ℕ) [NeZero n]

def rowEntropy (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n) : ℝ :=
  entropy (measure n) (rawTransition n β hβ u) (rawTransition n β hβ w)

theorem row_continuous (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    Continuous (rawTransition n β hβ u) :=
  (rawTransition_continuous n β hβ).comp (f := fun v : Slice n => (u,v))
    (continuous_const.prodMk continuous_id)

theorem rowEntropy_nonneg (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n) :
    0 ≤ rowEntropy n β hβ u w :=
  entropy_nonneg (measure n) _ _ (row_continuous n β hβ u) (row_continuous n β hβ w)
    (rawTransition_pos n β hβ u) (rawTransition_pos n β hβ w)
    (rawTransition_mass n β hβ u) (rawTransition_mass n β hβ w)

theorem rowEntropy_continuous (β : ℝ) (hβ : 0 ≤ β) :
    Continuous (fun uw : Slice n × Slice n => rowEntropy n β hβ uw.1 uw.2) := by
  have hp : Continuous (fun z : (Slice n × Slice n) × Slice n =>
      rawTransition n β hβ z.1.1 z.2) := (rawTransition_continuous n β hβ).comp
        (f := fun z : (Slice n × Slice n) × Slice n => (z.1.1,z.2))
        ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have hq : Continuous (fun z : (Slice n × Slice n) × Slice n =>
      rawTransition n β hβ z.1.2 z.2) := (rawTransition_continuous n β hβ).comp
        (f := fun z : (Slice n × Slice n) × Slice n => (z.1.2,z.2))
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  exact GibbsMarginalTower.fiber_integral_continuous (measure n) _
    (hp.mul ((hp.div hq (fun z => (rawTransition_pos n β hβ z.1.2 z.2).ne')).log
      (fun z => (div_pos (rawTransition_pos n β hβ z.1.1 z.2)
        (rawTransition_pos n β hβ z.1.2 z.2)).ne')))

def logGain (β : ℝ) (hβ : 0 ≤ β) (e : SpatialVertex n × Fin 3) (q : Q) (u : Slice n) : ℝ :=
  Real.log (ground n β hβ (shift n e q u)) - Real.log (ground n β hβ u)

theorem logGain_continuous (β : ℝ) (hβ : 0 ≤ β) (e : SpatialVertex n × Fin 3) (q : Q) :
    Continuous (logGain n β hβ e q) := by
  have hg := (ground n β hβ).continuous.log (fun u => (ground_pos n β hβ u).ne')
  exact (hg.comp (shift_continuous n e q)).sub hg

def groundGain (β : ℝ) (hβ : 0 ≤ β) (e : SpatialVertex n × Fin 3) (q : Q) : ℝ :=
  ∫ u, (ground n β hβ u)^2 * logGain n β hβ e q u ∂measure n

/-- The unknown ground term is minus one half of a genuine relative entropy. -/
theorem ground_entropy_eq (β : ℝ) (hβ : 0 ≤ β) (e : SpatialVertex n × Fin 3) (q : Q) :
    entropy (measure n) (fun u => (ground n β hβ u)^2)
      (fun u => (ground n β hβ (shift n e q u))^2) = -2*groundGain n β hβ e q := by
  unfold entropy groundGain
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  rw [Real.log_div (sq_pos_of_pos (ground_pos n β hβ u)).ne'
    (sq_pos_of_pos (ground_pos n β hβ (shift n e q u))).ne', Real.log_pow, Real.log_pow]
  unfold logGain
  norm_num
  ring

theorem groundGain_nonpos (β : ℝ) (hβ : 0 ≤ β) (e : SpatialVertex n × Fin 3) (q : Q) :
    groundGain n β hβ e q ≤ 0 := by
  have hm : (∫ u, (ground n β hβ (shift n e q u))^2 ∂measure n) = 1 :=
    (shift_integral n e q (fun u => (ground n β hβ u)^2)).trans
      (ground_square_integral n β hβ)
  have h := entropy_nonneg (measure n) _ _ ((ground n β hβ).continuous.pow 2)
    (((ground n β hβ).continuous.comp (shift_continuous n e q)).pow 2)
    (fun u => sq_pos_of_pos (ground_pos n β hβ u))
    (fun u => sq_pos_of_pos (ground_pos n β hβ (shift n e q u)))
    (ground_square_integral n β hβ) hm
  simp only [Function.comp_apply] at h
  rw [ground_entropy_eq] at h
  linarith

theorem log_row (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n) :
    Real.log (rawTransition n β hβ u v) = -inputAction n β u v -
      (β/2)*potential WilsonSingleLinkStaples.character 2 v + Real.log (ground n β hβ v) -
      Real.log ‖transfer n β‖ - Real.log (ground n β hβ u) := by
  have hk := rawKernel_pos WilsonSingleLinkStaples.character β 2 u v
  have htop := (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1
  rw [rawTransition, Real.log_div (mul_pos hk (ground_pos n β hβ v)).ne'
    (mul_pos htop (ground_pos n β hβ u)).ne',
    Real.log_mul hk.ne' (ground_pos n β hβ v).ne',
    Real.log_mul htop.ne' (ground_pos n β hβ u).ne']
  unfold rawKernel spatialWeight kineticWeight
  rw [Real.log_mul (mul_pos (Real.exp_pos _) (Real.exp_pos _)).ne' (Real.exp_pos _).ne',
    Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne']
  simp only [Real.log_exp]
  unfold inputAction
  ring

theorem log_row_ratio (β : ℝ) (hβ : 0 ≤ β) (u w v : Slice n) :
    Real.log (rawTransition n β hβ u v / rawTransition n β hβ w v) =
      inputAction n β w v - inputAction n β u v +
        (Real.log (ground n β hβ w)-Real.log (ground n β hβ u)) := by
  rw [Real.log_div (rawTransition_pos n β hβ u v).ne'
    (rawTransition_pos n β hβ w v).ne', log_row, log_row]
  ring

theorem rowEntropy_formula (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n) :
    rowEntropy n β hβ u w =
      (∫ v, rawTransition n β hβ u v * (inputAction n β w v-inputAction n β u v)
        ∂measure n) + (Real.log (ground n β hβ w)-Real.log (ground n β hβ u)) := by
  have hd : Continuous (fun v : Slice n => inputAction n β w v-inputAction n β u v) :=
    ((inputAction_continuous n β).comp (f := fun v : Slice n => (w,v))
      (continuous_const.prodMk continuous_id)).sub
      ((inputAction_continuous n β).comp (f := fun v : Slice n => (u,v))
        (continuous_const.prodMk continuous_id))
  have hi := integral_add
    (continuous_integrable (measure n) _ ((row_continuous n β hβ u).mul hd))
    ((continuous_integrable (measure n) _ (row_continuous n β hβ u)).mul_const
      (Real.log (ground n β hβ w)-Real.log (ground n β hβ u)))
  simp only [Pi.mul_apply] at hi
  unfold rowEntropy entropy
  simp_rw [log_row_ratio, mul_add]
  rw [hi, integral_mul_const, rawTransition_mass, one_mul]

theorem rowEntropy_pair_bound (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (u : Slice n) :
    rowEntropy n β hβ u (shift n e q u) + rowEntropy n β hβ u (shift n e q⁻¹ u) ≤
      66*β*‖(q : ℍ)-1‖^2 + logGain n β hβ e q u + logGain n β hβ e q⁻¹ u := by
  have hc (w : Slice n) : Continuous (fun v => rawTransition n β hβ u v *
      (inputAction n β w v-inputAction n β u v)) :=
    (row_continuous n β hβ u).mul (((inputAction_continuous n β).comp
      (f := fun v : Slice n => (w,v)) (continuous_const.prodMk continuous_id)).sub
      ((inputAction_continuous n β).comp (f := fun v : Slice n => (u,v))
        (continuous_const.prodMk continuous_id)))
  have hp := continuous_integrable (measure n) _ (hc (shift n e q u))
  have hm := continuous_integrable (measure n) _ (hc (shift n e q⁻¹ u))
  have h := integral_mono (hp.add hm)
    ((continuous_integrable (measure n) _ (row_continuous n β hβ u)).mul_const
      (66*β*‖(q : ℍ)-1‖^2)) (fun v => by
        have h := mul_le_mul_of_nonneg_left (inputAction_second_bound n β hβ e q u v)
          (rawTransition_pos n β hβ u v).le
        simp only [Pi.add_apply]
        nlinarith)
  have hi := integral_add hp hm
  simp only [Pi.add_apply] at h hi
  rw [hi, integral_mul_const, rawTransition_mass, one_mul] at h
  rw [rowEntropy_formula, rowEntropy_formula]
  unfold logGain
  linarith

def meanEntropy (β : ℝ) (hβ : 0 ≤ β) (e : SpatialVertex n × Fin 3) (q : Q) : ℝ :=
  ∫ u, (ground n β hβ u)^2 * rowEntropy n β hβ u (shift n e q u) ∂measure n

theorem meanEntropy_nonneg (β : ℝ) (hβ : 0 ≤ β) (e : SpatialVertex n × Fin 3) (q : Q) :
    0 ≤ meanEntropy n β hβ e q :=
  integral_nonneg (fun u => mul_nonneg (sq_nonneg _) (rowEntropy_nonneg n β hβ u _))

theorem meanEntropy_pair_bound (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) :
    meanEntropy n β hβ e q + meanEntropy n β hβ e q⁻¹ ≤ 66*β*‖(q : ℍ)-1‖^2 := by
  have hc (r : Q) := (rowEntropy_continuous n β hβ).comp
    (continuous_id.prodMk (shift_continuous n e r))
  have hg := (ground n β hβ).continuous.pow 2
  have he (r : Q) := continuous_integrable (measure n) _ (hg.mul (hc r))
  have hl (r : Q) := continuous_integrable (measure n) _ (hg.mul (logGain_continuous n β hβ e r))
  have h := integral_mono ((he q).add (he q⁻¹))
    ((((continuous_integrable (measure n) _ hg).mul_const (66*β*‖(q : ℍ)-1‖^2)).add
      (hl q)).add (hl q⁻¹)) (fun u => by
        have h := mul_le_mul_of_nonneg_left (rowEntropy_pair_bound n β hβ e q u)
          (sq_nonneg (ground n β hβ u))
        simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply, id_eq]
        nlinarith)
  have headd := integral_add (he q) (he q⁻¹)
  have hladd := integral_add
    (((continuous_integrable (measure n) _ hg).mul_const (66*β*‖(q : ℍ)-1‖^2)).add
      (hl q)) (hl q⁻¹)
  have hcadd := integral_add
    ((continuous_integrable (measure n) _ hg).mul_const (66*β*‖(q : ℍ)-1‖^2)) (hl q)
  simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply, id_eq] at h headd hladd hcadd
  rw [headd, hladd, hcadd, integral_mul_const, ground_square_integral, one_mul] at h
  change meanEntropy n β hβ e q + meanEntropy n β hβ e q⁻¹ ≤
    66*β*‖(q : ℍ)-1‖^2 + groundGain n β hβ e q + groundGain n β hβ e q⁻¹ at h
  linarith [groundGain_nonpos n β hβ e q, groundGain_nonpos n β hβ e q⁻¹]

/-- The coefficient is linear in beta and quadratic in the actual rotation displacement. -/
theorem meanEntropy_bound (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) :
    meanEntropy n β hβ e q ≤ 66*β*‖(q : ℍ)-1‖^2 := by
  linarith [meanEntropy_pair_bound n β hβ e q, meanEntropy_nonneg n β hβ e q⁻¹]

theorem meanEntropy_eq_groundLaw (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) :
    meanEntropy n β hβ e q =
      ∫ u, rowEntropy n β hβ u (shift n e q u) ∂WilsonGroundHeatBath.groundLaw n β hβ := by
  exact (GroundStateDirichlet.stationary_integral (measure n)
    (ground n β hβ) (ground n β hβ).continuous _).symm

end
end UnifiedTheory.Clay.YangMills.WilsonStationaryEntropy
