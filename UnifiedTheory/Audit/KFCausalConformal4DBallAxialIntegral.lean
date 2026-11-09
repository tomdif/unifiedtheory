/- Sharp spatial balls: the axial slice integral is derived from Lebesgue disk
area and Fubini, with the indicator and all integrability obligations explicit. -/
import UnifiedTheory.Audit.KFCausalConformal4DDiamondMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalConformal4DBallAxialIntegral
noncomputable section
open MeasureTheory Real Set Metric WithLp

abbrev Plane := Fin 2 → ℝ
abbrev Space := Fin 3 → ℝ
def disk (d : ℝ) : Set Plane := {v | v 0^2+v 1^2<d}
def spatialBall (R : ℝ) : Set Space := {v | v 0^2+v 1^2+v 2^2<R^2}
def split : Space ≃ᵐ ℝ × Plane := MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0

private theorem disk_measurable (d : ℝ) : MeasurableSet (disk d) := by
  exact measurableSet_lt (by fun_prop) measurable_const

private theorem ball_measurable (R : ℝ) : MeasurableSet (spatialBall R) := by
  exact measurableSet_lt (by fun_prop) measurable_const

theorem disk_volume (d : ℝ) (hd : 0<d) : volume (disk d)=ENNReal.ofReal (π*d) := by
  have he : disk d = (toLp 2) ⁻¹' ball (0:EuclideanSpace ℝ (Fin 2)) (sqrt d) := by
    ext v
    simp only [disk,mem_setOf_eq,mem_preimage,mem_ball_zero_iff]
    have hn : ‖(toLp 2 v : EuclideanSpace ℝ (Fin 2))‖^2=v 0^2+v 1^2 := by
      simp [EuclideanSpace.norm_sq_eq,Fin.sum_univ_two,Real.norm_eq_abs]
    have hs := sq_sqrt hd.le
    have hp := sqrt_pos.2 hd
    constructor <;> intro hv <;> nlinarith [norm_nonneg (toLp 2 v : EuclideanSpace ℝ (Fin 2))]
  rw [he,(PiLp.volume_preserving_toLp (Fin 2)).measure_preimage
    measurableSet_ball.nullMeasurableSet,EuclideanSpace.volume_ball_fin_two]
  rw [← ENNReal.ofReal_pow (sqrt_nonneg d),sq_sqrt hd.le,
    ← ENNReal.ofReal_mul hd.le]
  congr 1
  ring

theorem disk_empty (d : ℝ) (hd : d≤0) : disk d=∅ := by
  ext v
  simp only [disk,mem_setOf_eq,mem_empty_iff_false,iff_false]
  nlinarith [sq_nonneg (v 0),sq_nonneg (v 1)]

theorem ball_subset_closedBall (R : ℝ) (hR : 0≤R) :
    spatialBall R ⊆ closedBall (0:Space) R := by
  intro v hv
  have hs : v 0^2+v 1^2+v 2^2<R^2 := hv
  have hb : ∀ z : ℝ, z^2≤R^2 → |z|≤R := by
    intro z hz
    exact (sq_le_sq₀ (abs_nonneg z) hR).1 (by simpa only [sq_abs] using hz)
  rw [mem_closedBall_zero_iff,pi_norm_le_iff_of_nonneg hR]
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · change |v 0|≤R
    exact hb _ (by nlinarith [sq_nonneg (v 1),sq_nonneg (v 2)])
  · change |v 1|≤R
    exact hb _ (by nlinarith [sq_nonneg (v 0),sq_nonneg (v 2)])
  · change |v 2|≤R
    exact hb _ (by nlinarith [sq_nonneg (v 0),sq_nonneg (v 1)])

theorem ball_integrable (R : ℝ) (hR : 0≤R) (f : Space → ℝ) (hf : Continuous f) :
    IntegrableOn f (spatialBall R) :=
  (hf.continuousOn.integrableOn_compact (isCompact_closedBall (0:Space) R)).mono_set
    (ball_subset_closedBall R hR)

private theorem split_symm (z : ℝ) (p : Plane) : split.symm (z,p)=![z,p 0,p 1] := by
  ext i
  fin_cases i <;> rfl

theorem ball_axial_integral (R : ℝ) (hR : 0<R) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ v in spatialBall R, f (v 0)) =
      π * ∫ z in (-R)..R, (R^2-z^2)*f z := by
  let F : Space → ℝ := (spatialBall R).indicator (fun v => f (v 0))
  have hi : Integrable F :=
    (ball_integrable R hR.le _ (hf.comp (continuous_apply 0))).integrable_indicator
      (ball_measurable R)
  have mp : MeasurePreserving split := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have hic : Integrable (fun p : ℝ × Plane => F (split.symm p)) :=
    (mp.symm.integrable_comp_emb split.symm.measurableEmbedding).2 hi
  have hslice (z : ℝ) : (∫ p : Plane, F (split.symm (z,p))) =
      (Ioo (-R) R).indicator (fun z => π*(R^2-z^2)*f z) z := by
    have he : (fun p : Plane => F (split.symm (z,p))) =
        (disk (R^2-z^2)).indicator (fun _ => f z) := by
      funext p
      rw [split_symm]
      dsimp only [F]
      by_cases hp : p 0^2+p 1^2<R^2-z^2
      · have hv : ![z,p 0,p 1]∈spatialBall R := by
          change z^2+p 0^2+p 1^2<R^2
          linarith
        rw [indicator_of_mem hv,indicator_of_mem (show p∈disk (R^2-z^2) from hp)]
        rfl
      · have hv : ![z,p 0,p 1]∉spatialBall R := by
          change ¬z^2+p 0^2+p 1^2<R^2
          linarith
        rw [indicator_of_notMem hv,indicator_of_notMem (show p∉disk (R^2-z^2) from hp)]
    rw [he,integral_indicator (disk_measurable _)]
    by_cases hz : z∈Ioo (-R) R
    · have hd : 0<R^2-z^2 := by nlinarith [hz.1,hz.2]
      rw [indicator_of_mem hz,setIntegral_const,Measure.real,disk_volume _ hd,
        ENNReal.toReal_ofReal (by positivity),smul_eq_mul]
    · have hd : R^2-z^2≤0 := by
        simp only [mem_Ioo,not_and_or,not_lt] at hz
        rcases hz with hz | hz <;> nlinarith
      rw [disk_empty _ hd,setIntegral_empty,indicator_of_notMem hz]
  rw [← integral_indicator (ball_measurable R)]
  change (∫ v, F v)=_
  rw [← mp.symm.integral_comp' F]
  change (∫ x : ℝ × Plane, F (split.symm x) ∂volume.prod volume)=_
  rw [integral_prod _ hic]
  simp_rw [hslice]
  rw [integral_indicator measurableSet_Ioo]
  simp_rw [mul_assoc]
  rw [integral_const_mul,intervalIntegral.integral_of_le (by linarith : -R≤R),
    integral_Ioc_eq_integral_Ioo]

#print axioms disk_volume
#print axioms disk_empty
#print axioms ball_subset_closedBall
#print axioms ball_integrable
#print axioms ball_axial_integral
end
end UnifiedTheory.Audit.KFCausalConformal4DBallAxialIntegral
