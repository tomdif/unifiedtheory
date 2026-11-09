/- The regular score is continuous on a fixed compact set containing all
admissible clock geometries, including their limiting real scales. This
produces a bound uniform in clock position and polynomial degree. -/
import UnifiedTheory.Audit.KFCausalNeutralPlanePrefactorScore

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalNeutralPlaneUniformScore
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift
open UnifiedTheory.Audit.KFCausalNeutralPlaneClockGeometry
open UnifiedTheory.Audit.KFCausalNeutralPlaneActualBound
open UnifiedTheory.Audit.KFCausalNeutralPlaneNormalizedGeometry
open UnifiedTheory.Audit.KFCausalNeutralPlanePrefactorScore

def areaFloor : ℝ := Real.exp (-Real.pi/3)/2
def scaleCap : ℝ := Real.exp (Real.pi/6)
def region : Set (ℝ × ℂ) :=
  Icc 0 1 ×ˢ (Metric.closedBall 0 scaleCap ∩ {r | areaFloor ≤ r.re^2-r.im^2})

theorem areaFloor_positive : 0 < areaFloor := by unfold areaFloor; positivity

theorem region_compact : IsCompact region := by
  have hc : Continuous (fun r : ℂ => r.re^2-r.im^2) := by fun_prop
  exact isCompact_Icc.prod ((isCompact_closedBall (0:ℂ) scaleCap).inter_right
    (isClosed_le continuous_const hc))

theorem actual_mem_region (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    (fraction ε s,scale ε y s) ∈ region := by
  have ht := fraction_bounds ε s hε
  refine ⟨⟨ht.1.le,ht.2.le⟩,?_,?_⟩
  · rw [Metric.mem_closedBall,dist_zero_right]
    apply (scale_bound ε y s hε hy).trans
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ (by positivity : 0 < 2*ε)).mpr
    nlinarith
  · have hb : ‖relative ε y s‖ ≤ Real.pi/3 :=
      (relative_bound ε y s hε hy).trans ((div_le_iff₀ hε).mpr (by nlinarith))
    have hre : -Real.pi/3 ≤ (relative ε y s).re := by
      have hr := (Complex.abs_re_le_norm (relative ε y s)).trans hb
      linarith [(abs_le.mp hr).1]
    have he := Real.exp_le_exp.mpr hre
    exact (div_le_div_of_nonneg_right he (by norm_num : (0:ℝ) ≤ 2)).trans
      (scale_square_re_lower ε y s hε hy)

theorem regularScore_continuousOn (α : ℝ) (hα : 0 < α) :
    ContinuousOn (fun p : ℝ × ℂ => regularScore α p.1 p.2) region := by
  intro p hp
  have hA : 0 < p.2.re^2-p.2.im^2 := lt_of_lt_of_le areaFloor_positive hp.2.2
  have ha : p.2.re ≠ 0 := by
    intro hz
    rw [hz] at hA
    nlinarith [sq_nonneg p.2.im]
  have hS : 0 < p.2.re^2+p.2.im^2 := by positivity
  have hd := normalized_denominator_positive p.1 p.2 hp.1 hA
  apply ContinuousAt.continuousWithinAt
  unfold regularScore logPrefactorSlope shearNumerator realNumerator imagNumerator denominator
  unfold denominator at hd
  fun_prop (disch := positivity)

theorem exists_uniform_score (α : ℝ) (hα : 0 < α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε y s : ℝ, 0 < ε → |y| ≤ Real.pi*ε/3 → y ≠ 0 →
      score α ε y s ≤ C := by
  obtain ⟨M,hM⟩ := (region_compact.image_of_continuousOn
    (regularScore_continuousOn α hα)).bddAbove
  refine ⟨max M 0,le_max_right _ _,?_⟩
  intro ε y s hε hy hy0
  rw [actual_score_regular α ε y s hα hε hy hy0]
  exact (hM (mem_image_of_mem _ (actual_mem_region ε y s hε hy))).trans (le_max_left _ _)

theorem exists_uniform_density_bound (α : ℝ) (hα : 0 < α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ε y s : ℝ, 0 < ε → |y| ≤ Real.pi*ε/3 → y ≠ 0 →
      ∀ (P : Polynomial ℂ) (x z : ℝ),
        deriv (fun t => actualDensity α β ε y t P x z) s ≤
          C*actualDensity α β ε y s P x z := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_score α hα
  refine ⟨C,hC,?_⟩
  intro β ε y s hε hy hy0 P x z
  exact (actualDensity_derivative_bound α β ε y s hα hε hy hy0 P x z).trans
    (mul_le_mul_of_nonneg_right (hbound ε y s hε hy hy0)
      (actualDensity_nonnegative α β ε y s hα hε hy hy0 P x z))

#print axioms areaFloor_positive
#print axioms region_compact
#print axioms actual_mem_region
#print axioms regularScore_continuousOn
#print axioms exists_uniform_score
#print axioms exists_uniform_density_bound
end
end UnifiedTheory.Audit.KFCausalNeutralPlaneUniformScore
