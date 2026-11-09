/- A compact continuous radial spacetime profile has an actual four-coordinate
L1 representative. Sharp past-cone integration is reduced exactly to the
radial two-coordinate integral, with the Euclidean factor4pi derived. -/
import UnifiedTheory.Audit.KFCausalConformal4DSpatialRadialMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalConformal4DSpatialRadialMeasureProduct
noncomputable section
open MeasureTheory Set Real Metric
open KFCausalConformal4DSpatialRadialMeasure
open KFCausalConformal4DCoordinateVolume (timeSplit)
open KFCausalConformal4DDiamondBenchmark (Point)
open KFCausalConformal4DDiamondMeasure (spatialRadius)

def radialLift (F : ℝ×ℝ → ℝ) (p : ℝ×Space) : ℝ := F (p.1,radius p.2)
def pastCone : Set (ℝ×Space) := {p | p.1<0 ∧ radius p.2 < -p.1}
def pointLift (F : ℝ×ℝ → ℝ) (p : Point) : ℝ := F (p 0,spatialRadius p)
def pointPastCone : Set Point := {p | p 0<0 ∧ spatialRadius p < -(p 0)}

theorem radialLift_continuous (F : ℝ×ℝ → ℝ) (hF : Continuous F) : Continuous (radialLift F) :=
  hF.comp (continuous_fst.prodMk (radius_continuous.comp continuous_snd))

theorem radialLift_compact (F : ℝ×ℝ → ℝ) (hF : HasCompactSupport F) :
    HasCompactSupport (radialLift F) := by
  obtain ⟨R,hR,hb⟩ := hF.isBounded.exists_pos_norm_lt
  apply HasCompactSupport.intro (isCompact_closedBall (0:ℝ×Space) R)
  intro p hp
  by_contra hn
  have hmem : (p.1,radius p.2)∈tsupport F := subset_tsupport F hn
  have hr := hb (p.1,radius p.2) hmem
  have ht : ‖p.1‖≤R := (le_max_left _ _).trans (le_of_lt hr)
  have hv : radius p.2≤R := by
    have hh := (le_max_right ‖p.1‖ ‖radius p.2‖).trans (le_of_lt hr)
    simpa only [Real.norm_eq_abs,abs_of_nonneg (radius_nonnegative p.2)] using hh
  have hvs : ‖p.2‖≤R := by
    rw [pi_norm_le_iff_of_nonneg hR.le]
    intro i
    exact (PiLp.norm_apply_le (WithLp.toLp 2 p.2 : Euclidean) i).trans hv
  apply hp
  rw [mem_closedBall_zero_iff,Prod.norm_def]
  exact max_le ht hvs

theorem radialLift_integrable (F : ℝ×ℝ → ℝ) (hF : Continuous F) (hs : HasCompactSupport F) :
    Integrable (radialLift F) :=
  (radialLift_continuous F hF).integrable_of_hasCompactSupport (radialLift_compact F hs)

private theorem past_measurable : MeasurableSet pastCone :=
  (isOpen_lt continuous_fst continuous_const).measurableSet.inter
    (isOpen_lt (radius_continuous.comp continuous_snd) continuous_fst.neg).measurableSet

theorem past_integrable (F : ℝ×ℝ → ℝ) (hF : Continuous F) (hs : HasCompactSupport F) :
    IntegrableOn (radialLift F) pastCone := (radialLift_integrable F hF hs).integrableOn

theorem product_past_integral (F : ℝ×ℝ → ℝ) (hF : Continuous F) (hs : HasCompactSupport F) :
    (∫ p in pastCone, radialLift F p) =
      4*π*(∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t), r^2*F (t,r)) := by
  have hi : Integrable (pastCone.indicator (radialLift F)) :=
    (radialLift_integrable F hF hs).indicator past_measurable
  rw [← integral_indicator past_measurable]
  change (∫ p : ℝ×Space, pastCone.indicator (radialLift F) p ∂volume.prod volume)=_
  rw [integral_prod _ hi]
  have he (t : ℝ) : (∫ v : Space, pastCone.indicator (radialLift F) (t,v)) =
      (Iio (0:ℝ)).indicator (fun t => 4*π*(∫ r in Ioo (0:ℝ) (-t), r^2*F (t,r))) t := by
    by_cases ht : t<0
    · rw [indicator_of_mem (show t∈Iio (0:ℝ) from ht)]
      have hv : (fun v : Space => pastCone.indicator (radialLift F) (t,v)) =
          (radiusBall (-t)).indicator (fun v : Space => F (t,radius v)) := by
        funext v
        by_cases hv : radius v < -t
        · rw [indicator_of_mem (show (t,v)∈pastCone from ⟨ht,hv⟩),
            indicator_of_mem (show v∈radiusBall (-t) from hv)]
          rfl
        · rw [indicator_of_notMem (show (t,v)∉pastCone from fun h => hv h.2),
            indicator_of_notMem (show v∉radiusBall (-t) from hv)]
      rw [hv,integral_indicator (radius_ball_measurable (-t))]
      exact ball_integral (fun r => F (t,r)) (-t)
    · rw [indicator_of_notMem (show t∉Iio (0:ℝ) from ht)]
      apply integral_eq_zero_of_ae
      exact Filter.Eventually.of_forall (fun v =>
        indicator_of_notMem (show (t,v)∉pastCone from fun h => ht h.1) (radialLift F))
  simp_rw [he]
  rw [integral_indicator measurableSet_Iio,integral_const_mul]

private theorem timeSplit_apply (p : Point) : timeSplit p=(p 0,fun i : Fin 3 => p i.succ) := by
  apply Prod.ext
  · rfl
  · funext i
    fin_cases i <;> rfl

private theorem pointLift_eq (F : ℝ×ℝ → ℝ) : pointLift F=radialLift F ∘ timeSplit := by
  funext p
  rw [Function.comp_apply,timeSplit_apply]
  exact congrArg (fun r => F (p 0,r)) (point_radius p)

private theorem point_past_measurable : MeasurableSet pointPastCone := by
  apply (isOpen_lt (continuous_apply 0) continuous_const).measurableSet.inter
  apply IsOpen.measurableSet
  apply isOpen_lt _ (continuous_apply 0).neg
  unfold spatialRadius
  fun_prop

theorem pointLift_integrable (F : ℝ×ℝ → ℝ) (hF : Continuous F) (hs : HasCompactSupport F) :
    Integrable (pointLift F) := by
  have mp : MeasurePreserving timeSplit := volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0
  rw [pointLift_eq]
  exact mp.integrable_comp_of_integrable (radialLift_integrable F hF hs)

theorem point_past_integrable (F : ℝ×ℝ → ℝ) (hF : Continuous F) (hs : HasCompactSupport F) :
    IntegrableOn (pointLift F) pointPastCone := (pointLift_integrable F hF hs).integrableOn

theorem point_past_integral (F : ℝ×ℝ → ℝ) (hF : Continuous F) (hs : HasCompactSupport F) :
    (∫ p in pointPastCone, pointLift F p) =
      4*π*(∫ t in Iio (0:ℝ), ∫ r in Ioo (0:ℝ) (-t), r^2*F (t,r)) := by
  have mp : MeasurePreserving timeSplit := volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0
  have he : pointPastCone.indicator (pointLift F) =
      (pastCone.indicator (radialLift F)) ∘ timeSplit := by
    funext p
    have hm : timeSplit p∈pastCone ↔ p∈pointPastCone := by
      rw [timeSplit_apply]
      simp only [pastCone,pointPastCone,mem_setOf_eq,← point_radius]
    by_cases hp : p∈pointPastCone
    · rw [indicator_of_mem hp,Function.comp_apply,indicator_of_mem (hm.mpr hp),pointLift_eq]
      rfl
    · rw [indicator_of_notMem hp,Function.comp_apply,indicator_of_notMem (fun h => hp (hm.mp h))]
  rw [← integral_indicator point_past_measurable,he]
  simp only [Function.comp_apply]
  rw [mp.integral_comp timeSplit.measurableEmbedding,integral_indicator past_measurable,
    product_past_integral F hF hs]

#print axioms radialLift_continuous
#print axioms radialLift_compact
#print axioms radialLift_integrable
#print axioms past_integrable
#print axioms product_past_integral
#print axioms pointLift_integrable
#print axioms point_past_integrable
#print axioms point_past_integral
end
end UnifiedTheory.Audit.KFCausalConformal4DSpatialRadialMeasureProduct
