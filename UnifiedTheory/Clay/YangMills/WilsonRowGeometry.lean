/- A linear geometric response bound for the actual temporal-gauge row law.
The spatial action and constructed ground density cancel from action
differences. Their values are retained in the law, not bounded or replaced. -/
import UnifiedTheory.Clay.YangMills.WilsonPhysicalResponse
import UnifiedTheory.Clay.YangMills.CompactGibbsOscillation
import UnifiedTheory.Clay.YangMills.SU2HaarTilt

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonRowGeometry
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonSingleLinkStaples
open WilsonGroundLocalComparison WilsonTemporalInfluence WilsonPhysicalResponse
open scoped Quaternion RealInnerProductSpace

theorem character_pair (u v : WilsonSlabOperator.Q) :
    (character (u⁻¹ * v)).re = 2 * ⟪(u : ℍ), (v : ℍ)⟫ := by
  rw [character_re]
  change 2 * (star (u : ℍ) * (v : ℍ)).re = _
  rw [SU2HaarTilt.rotated_real]

theorem character_difference_bound (u u' v : WilsonSlabOperator.Q) :
    |(character (u⁻¹ * v)).re - (character (u'⁻¹ * v)).re| ≤
      2 * ‖(u : ℍ) - (u' : ℍ)‖ := by
  rw [character_pair, character_pair, ← mul_sub, ← inner_sub_left, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h := abs_real_inner_le_norm ((u : ℍ) - (u' : ℍ)) (v : ℍ)
  rw [CStarRing.norm_of_mem_unitary v.property, mul_one] at h
  exact mul_le_mul_of_nonneg_left h (by norm_num)

variable (n : ℕ) [NeZero n]

def inputCost (u v : Slice n) : ℝ := ∑ e, ‖(u e : ℍ) - (v e : ℍ)‖

theorem inputCost_nonneg (u v : Slice n) : 0 ≤ inputCost n u v :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem inputCost_self (u : Slice n) : inputCost n u u = 0 := by simp [inputCost]

theorem inputCost_symm (u v : Slice n) : inputCost n u v = inputCost n v u := by
  simp only [inputCost, norm_sub_rev]

theorem inputCost_triangle (u v w : Slice n) :
    inputCost n u w ≤ inputCost n u v + inputCost n v w := by
  unfold inputCost
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  calc
    _ = ‖((u e : ℍ) - (v e : ℍ)) + ((v e : ℍ) - (w e : ℍ))‖ := by congr 1; abel
    _ ≤ _ := norm_add_le _ _

theorem inputCost_eq_zero_iff (u v : Slice n) : inputCost n u v = 0 ↔ u = v := by
  constructor
  · intro h
    funext e
    have he : ‖(u e : ℍ) - (v e : ℍ)‖ ≤ inputCost n u v :=
      Finset.single_le_sum (fun j _ => norm_nonneg ((u j : ℍ) - (v j : ℍ)))
        (Finset.mem_univ e)
    rw [h] at he
    exact Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm he (norm_nonneg _))))
  · rintro rfl
    exact inputCost_self n u

theorem inputCost_continuous :
    Continuous (fun uv : Slice n × Slice n => inputCost n uv.1 uv.2) := by
  unfold inputCost
  fun_prop

/-- Simultaneous gauge transformations preserve this actual link cost exactly. -/
theorem inputCost_gauge (h : SliceGauge n WilsonSlabOperator.Q) (u v : Slice n) :
    inputCost n (gaugeSlice h u) (gaugeSlice h v) = inputCost n u v := by
  unfold inputCost
  apply Finset.sum_congr rfl
  intro e _
  change ‖(h e.1 : ℍ) * (u e : ℍ) * ((h (spatialStep n e.1 e.2))⁻¹ : WilsonSlabOperator.Q) -
    (h e.1 : ℍ) * (v e : ℍ) * ((h (spatialStep n e.1 e.2))⁻¹ : WilsonSlabOperator.Q)‖ = _
  rw [← sub_mul, ← mul_sub, norm_mul, norm_mul,
    CStarRing.norm_of_mem_unitary (h e.1).property,
    CStarRing.norm_of_mem_unitary ((h (spatialStep n e.1 e.2))⁻¹).property,
    one_mul, mul_one]

theorem inputCost_eq_support (S : Finset (SpatialVertex n × Fin 3)) (u v : Slice n)
    (huv : ∀ e, e ∉ S → u e = v e) :
    inputCost n u v = ∑ e ∈ S, ‖(u e : ℍ) - (v e : ℍ)‖ := by
  unfold inputCost
  symm
  exact Finset.sum_subset (Finset.subset_univ _)
    (fun e _ he => by rw [huv e he]; simp)

/-- A literal action for the actual row law, including its constructed ground amplitude. -/
def rowAction (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n) : ℝ :=
  β * kineticAction character 2 u v - Real.log (spatialWeight character β 2 v) -
    Real.log (ground n β hβ v)

theorem rowAction_continuous (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    Continuous (rowAction n β hβ u) := by
  have hc := character_continuous
  have hk : Continuous (fun v : Slice n => kineticAction character 2 u v) := by
    unfold kineticAction
    fun_prop
  have hw : Continuous (fun v : Slice n => spatialWeight character β 2 v) := by
    unfold spatialWeight potential spatialHolonomy
    fun_prop
  exact ((continuous_const.mul hk).sub (hw.log (fun _ => (Real.exp_pos _).ne'))).sub
    ((ground n β hβ).continuous.log (fun v => (ground_pos n β hβ v).ne'))

theorem rowAction_weight (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n) :
    Real.exp (-rowAction n β hβ u v) = rowWeight n β hβ u v := by
  have hw : 0 < spatialWeight character β 2 v := Real.exp_pos _
  have he : -rowAction n β hβ u v = -β * kineticAction character 2 u v +
      Real.log (spatialWeight character β 2 v) + Real.log (ground n β hβ v) := by
    unfold rowAction
    ring
  rw [he, Real.exp_add, Real.exp_add, Real.exp_log hw,
    Real.exp_log (ground_pos n β hβ v)]
  rfl

theorem rowAction_law (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    CompactGibbsContinuity.law (measure n) (rowAction n β hβ u) = rowLaw n β hβ u := by
  unfold CompactGibbsContinuity.law rowLaw
  congr 1
  funext v
  exact rowAction_weight n β hβ u v

theorem kinetic_difference (u u' v : Slice n) :
    kineticAction character 2 u' v - kineticAction character 2 u v =
      ∑ e, ((character ((u e)⁻¹ * v e)).re - (character ((u' e)⁻¹ * v e)).re) := by
  unfold kineticAction
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem kinetic_difference_bound (u u' v : Slice n) :
    |kineticAction character 2 u' v - kineticAction character 2 u v| ≤
      2 * inputCost n u u' := by
  rw [kinetic_difference]
  calc
    _ ≤ ∑ e, |(character ((u e)⁻¹ * v e)).re -
        (character ((u' e)⁻¹ * v e)).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e, 2 * ‖(u e : ℍ) - (u' e : ℍ)‖ :=
      Finset.sum_le_sum (fun e _ => character_difference_bound (u e) (u' e) (v e))
    _ = _ := by rw [← Finset.mul_sum]; rfl

/-- The entire unknown output factor cancels from the finite input difference. -/
theorem rowAction_difference_bound (β : ℝ) (hβ : 0 ≤ β) (u u' v : Slice n) :
    |rowAction n β hβ u' v - rowAction n β hβ u v| ≤
      2 * β * inputCost n u u' := by
  have he : rowAction n β hβ u' v - rowAction n β hβ u v =
      β * (kineticAction character 2 u' v - kineticAction character 2 u v) := by
    unfold rowAction
    ring
  rw [he, abs_mul, abs_of_nonneg hβ]
  have h := mul_le_mul_of_nonneg_left (kinetic_difference_bound n u u' v) hβ
  convert h using 1
  ring

/-- Actual finite response grows linearly in beta times input displacement, with no ground ratio. -/
theorem rowMean_difference_bound (β : ℝ) (hβ : 0 ≤ β) (u u' : Slice n)
    (f : C(Slice n, ℝ)) (lo hi : ℝ) (hlo : lo ≤ hi)
    (hf : ∀ v, f v ∈ Set.Icc lo hi) :
    |rowMean n β hβ f u - rowMean n β hβ f u'| ≤
      β * (hi - lo) * inputCost n u u' := by
  have hc := inputCost_nonneg n u u'
  have hb : 0 ≤ 2 * β * inputCost n u u' := by positivity
  have h := CompactGibbsOscillation.action_expectation_difference (measure n)
    (rowAction n β hβ u') (rowAction n β hβ u) f
    (rowAction_continuous n β hβ u') (rowAction_continuous n β hβ u) f.continuous
    (-(2 * β * inputCost n u u')) (2 * β * inputCost n u u') lo hi
    (by linarith) hlo
    (fun v => abs_le.mp (rowAction_difference_bound n β hβ u u' v)) hf
  rw [rowAction_law, rowAction_law] at h
  change |rowMean n β hβ f u - rowMean n β hβ f u'| ≤ _ at h
  convert h using 1
  ring

end
end UnifiedTheory.Clay.YangMills.WilsonRowGeometry
