/- A symmetric seam comparison with its noncommuting-input error retained.
All transformations are fixed. No adaptive change-of-variables assertion is used. -/
import UnifiedTheory.Clay.YangMills.WilsonFlatSeamComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSeamCommutatorGeometry
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonCenterTwist WilsonRowGeometry
open WilsonJointRotation WilsonDistributedSeam
open WilsonSingleLinkStaples (character character_classFunction)
open scoped Quaternion

variable (n : ℕ) [NeZero n]

omit [NeZero n] in
theorem twist_mul_right (i : Fin 3) (a u : Slice n) : twist n i (a*u) = a * twist n i u := by
  funext e
  simp only [twist_apply, Pi.mul_apply]
  split_ifs <;> simp

theorem inputCost_twist (i : Fin 3) (u v : Slice n) :
    inputCost n (twist n i u) (twist n i v) = inputCost n u v := by
  unfold inputCost
  apply Finset.sum_congr rfl
  intro e _
  simp only [twist_apply]
  split_ifs
  · simp only [Unitary.coe_neg, neg_sub_neg, norm_sub_rev]
  · rfl

/-- The error is measured against the two ideal inverse rotations in the same link coordinates. -/
def mismatch (i : Fin 3) (q : Slice n) (h : SliceGauge n Q) (u : Slice n) : ℝ :=
  inputCost n (gaugeSlice h (twist n i u)) (q*u) +
    inputCost n (gaugeSlice h⁻¹ (twist n i u)) (q⁻¹*u)

theorem mismatch_nonneg (i : Fin 3) (q : Slice n) (h : SliceGauge n Q) (u : Slice n) :
    0 ≤ mismatch n i q h u := add_nonneg (inputCost_nonneg n _ _) (inputCost_nonneg n _ _)

theorem mismatch_continuous (i : Fin 3) (q : Slice n) (h : SliceGauge n Q) :
    Continuous (mismatch n i q h) := by
  unfold mismatch inputCost gaugeSlice twist
  fun_prop

/-- The retained error is exactly invariant under the same central seam involution. -/
theorem mismatch_twist (i : Fin 3) (q : Slice n) (h : SliceGauge n Q) (u : Slice n) :
    mismatch n i q h (twist n i u) = mismatch n i q h u := by
  unfold mismatch
  have he (k : SliceGauge n Q) (r : Slice n) :
      inputCost n (gaugeSlice k (twist n i (twist n i u))) (r * twist n i u) =
        inputCost n (gaugeSlice k (twist n i u)) (r*u) := by
    rw [← twist_gauge, ← twist_mul_right, inputCost_twist]
  rw [he, he]

/-- The original kinetic second-difference bound plus two explicit first-difference errors. -/
theorem kinetic_second (i : Fin 3) (q u v : Slice n) (h : SliceGauge n Q) :
    kineticAction character 2 (gaugeSlice h (twist n i u)) v +
      kineticAction character 2 (gaugeSlice h⁻¹ (twist n i u)) v -
      2 * kineticAction character 2 u v ≤ 2 * (cost n q + mismatch n i q h u) := by
  have hp := (abs_le.mp (kinetic_difference_bound n
    (gaugeSlice h (twist n i u)) (q*u) v)).1
  have hm := (abs_le.mp (kinetic_difference_bound n
    (gaugeSlice h⁻¹ (twist n i u)) (q⁻¹*u) v)).1
  have hs := WilsonJointRotation.kinetic_second_bound n q u v
  unfold mismatch
  linarith

/-- Spatial potentials cancel by actual gauge and center symmetry, even away from flat fields. -/
theorem slab_second (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (q u v : Slice n)
    (h k : SliceGauge n Q) :
    slabAction character β 2 (gaugeSlice h (twist n i u)) v k +
      slabAction character β 2 (gaugeSlice h⁻¹ (twist n i u)) v k -
      2 * slabAction character β 2 u v k ≤ 2 * β * (cost n q + mismatch n i q h u) := by
  have hh := mul_le_mul_of_nonneg_left (kinetic_second n i q u (gaugeSlice k v) h) hβ
  simp only [slabAction, temporalAction_eq character character_classFunction,
    WilsonSlabGauge.potential_gauge character character_classFunction, potential_twist]
  nlinarith only [hh]

omit [NeZero n] in
theorem distributing_inverse (i : Fin 3) (q : Q) :
    (distributingGauge n i q)⁻¹ = distributingGauge n i q⁻¹ := by
  funext x
  simp only [distributingGauge, Pi.inv_apply, inv_pow]

/-- Common-axis inputs have no mismatch; they need not be flat. -/
theorem gauge_twist_of_commute (i : Fin 3) (q : Q) (hq : q ^ n = -1) (u : Slice n)
    (hu : ∀ e, Commute q (u e)) :
    gaugeSlice (distributingGauge n i q) (twist n i u) = uniform n i q * u := by
  have he := seam_gauge_uniform n i q
  rw [hq] at he
  funext e
  have hh := congrArg (fun z : Slice n => z e) he
  simp only at hh
  have hc : Commute (distributingGauge n i q (spatialStep n e.1 e.2)) (u e) :=
    (hu e).pow_left _
  change distributingGauge n i q e.1 *
    (WilsonWindingLoop.seam n i (-1) e * u e) *
      (distributingGauge n i q (spatialStep n e.1 e.2))⁻¹ = uniform n i q e * u e
  rw [← hh]
  change _ = (distributingGauge n i q e.1 * WilsonWindingLoop.seam n i (-1) e *
    (distributingGauge n i q (spatialStep n e.1 e.2))⁻¹) * u e
  calc
    _ = distributingGauge n i q e.1 * WilsonWindingLoop.seam n i (-1) e *
        (u e * (distributingGauge n i q (spatialStep n e.1 e.2))⁻¹) := by group
    _ = _ := by rw [hc.inv_left.eq.symm]; group

theorem mismatch_zero_of_commute (i : Fin 3) (q : Q) (hq : q ^ n = -1) (u : Slice n)
    (hu : ∀ e, Commute q (u e)) :
    mismatch n i (uniform n i q) (distributingGauge n i q) u = 0 := by
  have hi : (q⁻¹)^n = -1 := by rw [inv_pow, hq]; simp
  unfold mismatch
  rw [gauge_twist_of_commute n i q hq u hu, distributing_inverse, uniform_inv,
    gauge_twist_of_commute n i q⁻¹ hi u (fun e => (hu e).inv_left)]
  simp only [inputCost_self, add_zero]

/-- The fixed small root supplies a continuous error weight on every SU(2) input. -/
def rootMismatch (i : Fin 3) (u : Slice n) : ℝ :=
  mismatch n i (uniform n i (WilsonSeamRoot.root n))
    (distributingGauge n i (WilsonSeamRoot.root n)) u

theorem rootMismatch_nonneg (i : Fin 3) (u : Slice n) : 0 ≤ rootMismatch n i u :=
  mismatch_nonneg n i _ _ u

theorem rootMismatch_continuous (i : Fin 3) : Continuous (rootMismatch n i) :=
  mismatch_continuous n i _ _

theorem rootMismatch_twist (i : Fin 3) (u : Slice n) :
    rootMismatch n i (twist n i u) = rootMismatch n i u := mismatch_twist n i _ _ u

theorem rootMismatch_zero (i : Fin 3) (u : Slice n)
    (hu : ∀ e, Commute (WilsonSeamRoot.root n) (u e)) : rootMismatch n i u = 0 :=
  mismatch_zero_of_commute n i _ (WilsonSeamRoot.root_power n) u hu

end
end UnifiedTheory.Clay.YangMills.WilsonSeamCommutatorGeometry
