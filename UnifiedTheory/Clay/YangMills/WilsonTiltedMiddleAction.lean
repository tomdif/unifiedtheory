/- The exact two boundary sources preserve a quantitative small-field
second-difference lower bound for the middle Wilson action. This is a
pointwise statement, not a global covariance or Poincare inequality. -/
import UnifiedTheory.Clay.YangMills.WilsonSmallFieldCurvature
import UnifiedTheory.Clay.YangMills.WilsonBoundaryDecayBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonTiltedMiddleAction
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonBoundaryConnected WilsonJointRotation
open scoped Quaternion RealInnerProductSpace

variable (n : ℕ) [NeZero n]

theorem kinetic_symmetric (u v : Slice n) :
    kineticAction WilsonSingleLinkStaples.character 2 u v =
      kineticAction WilsonSingleLinkStaples.character 2 v u := by
  unfold kineticAction
  simp only [WilsonRowGeometry.character_pair, real_inner_comm]

/-- The boundary insertion is linear in precisely one middle quaternion. -/
theorem source_linear (β : ℝ) (e : SpatialVertex n × Fin 3) (q : Q) (u v : Slice n) :
    source n β e q u v =
      2 * β * ⟪((q * u e : Q) : ℍ) - (u e : ℍ), (v e : ℍ)⟫ := by
  rw [source_local]
  simp only [WilsonRowGeometry.character_pair, inner_sub_left]
  ring

/-- No supremum or derivative estimate is used in this exact finite difference. -/
theorem source_second (β : ℝ) (e : SpatialVertex n × Fin 3) (q : Q)
    (u v a : Slice n) :
    source n β e q u (a * v) + source n β e q u (a⁻¹ * v) -
      2 * source n β e q u v = -(displacement n a e) ^ 2 * source n β e q u v := by
  have hs : ((a e * v e : Q) : ℍ) + (((a e)⁻¹ * v e : Q) : ℍ) =
      (2 * (a e : ℍ).re) • (v e : ℍ) := by
    change (a e : ℍ) * (v e : ℍ) + star (a e : ℍ) * (v e : ℍ) = _
    rw [← add_mul, Quaternion.self_add_star']
    exact (Algebra.smul_def (2 * (a e : ℍ).re) (v e : ℍ)).symm
  have hi := congrArg (fun x : ℍ => ⟪((q * u e : Q) : ℍ) - (u e : ℍ), x⟫) hs
  simp only [inner_add_right, real_inner_smul_right] at hi
  simp only [source_linear, Pi.mul_apply, Pi.inv_apply, displacement,
    SU2GaussianMass.chord_square]
  linear_combination 2 * β * hi

def action (β : ℝ) (u w : Slice n) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (s t : ℝ) (v : Slice n) : ℝ :=
  WilsonMiddleBridge.action n β u w v - s * source n β e q u v - t * source n β d r u v

theorem action_continuous (β : ℝ) (u w : Slice n) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (s t : ℝ) : Continuous (action n β u w e d q r s t) :=
  ((WilsonMiddleBridge.action_continuous n β u w).sub
    (continuous_const.mul (source_continuous n β e q u))).sub
    (continuous_const.mul (source_continuous n β d r u))

theorem action_joint_continuous (β : ℝ) (u : Slice n) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (s t : ℝ) :
    Continuous (fun z : Slice n × Slice n => action n β u z.1 e d q r s t z.2) := by
  have hc := WilsonSingleLinkStaples.character_continuous
  have hm : Continuous (fun z : Slice n × Slice n => WilsonMiddleBridge.action n β u z.1 z.2) := by
    unfold WilsonMiddleBridge.action potential kineticAction spatialHolonomy
    fun_prop
  exact (hm.sub (continuous_const.mul ((source_continuous n β e q u).comp continuous_snd))).sub
    (continuous_const.mul ((source_continuous n β d r u).comp continuous_snd))

/-- The correction has support only at the two inserted links. -/
theorem action_second (β : ℝ) (u w : Slice n) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (s t : ℝ) (v a : Slice n) :
    action n β u w e d q r s t (a * v) + action n β u w e d q r s t (a⁻¹ * v) -
      2 * action n β u w e d q r s t v =
      WilsonMiddleBridge.action n β u w (a * v) +
        WilsonMiddleBridge.action n β u w (a⁻¹ * v) -
        2 * WilsonMiddleBridge.action n β u w v +
        s * (displacement n a e) ^ 2 * source n β e q u v +
        t * (displacement n a d) ^ 2 * source n β d r u v := by
  have he := source_second n β e q u v a
  have hd := source_second n β d r u v a
  unfold action
  linear_combination -s * he - t * hd

theorem pair_cost (e d : SpatialVertex n × Fin 3) (hed : e ≠ d) (a : Slice n) :
    (displacement n a e) ^ 2 + (displacement n a d) ^ 2 ≤ cost n a := by
  classical
  have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {e, d})
    (f := fun b => (displacement n a b) ^ 2) (fun _ _ _ => sq_nonneg _)
  simpa only [Finset.sum_pair hed, cost] using h

/-- Unit source strengths and beta-scaled rotations cost at most two times
the collective squared displacement, independently of the volume or depth. -/
theorem action_second_lower (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n)
    (e d : SpatialVertex n × Fin 3) (hed : e ≠ d) (q r : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (v a : Slice n) :
    WilsonMiddleBridge.action n β u w (a * v) +
      WilsonMiddleBridge.action n β u w (a⁻¹ * v) -
      2 * WilsonMiddleBridge.action n β u w v - 2 * cost n a ≤
      action n β u w e d q r s t (a * v) + action n β u w e d q r s t (a⁻¹ * v) -
        2 * action n β u w e d q r s t v := by
  have he : -(2 : ℝ) ≤ source n β e q u v := by
    have h := (abs_le.mp (source_bound n β hβ e q u v)).1
    linarith
  have hd : -(2 : ℝ) ≤ source n β d r u v := by
    have h := (abs_le.mp (source_bound n β hβ d r u v)).1
    linarith
  have hse : -2 ≤ s * source n β e q u v := by nlinarith only [he, hs.1, hs.2]
  have htd : -2 ≤ t * source n β d r u v := by nlinarith only [hd, ht.1, ht.2]
  have h1 := mul_le_mul_of_nonneg_right hse (sq_nonneg (displacement n a e))
  have h2 := mul_le_mul_of_nonneg_right htd (sq_nonneg (displacement n a d))
  rw [action_second]
  nlinarith only [h1, h2, pair_cost n e d hed a]

/-- The explicit small-field lower bound survives the entire two-source
rectangle. Positivity follows at beta greater than one within this sector. -/
theorem action_second_small (β : ℝ) (hβ : 0 ≤ β) (u w : Slice n)
    (e d : SpatialVertex n × Fin 3) (hed : e ≠ d) (q r : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (v a : Slice n)
    (hflat : ∀ (x : SpatialVertex n) (p : SpatialPlane),
      ‖((spatialHolonomy v x p.1.1 p.1.2 : Q) : ℍ) - 1‖ ≤ 1 / 32)
    (hu : ∀ b, ‖(v b : ℍ) - (u b : ℍ)‖ ^ 2 ≤ 1 / 2)
    (hw : ∀ b, ‖(v b : ℍ) - (w b : ℍ)‖ ^ 2 ≤ 1 / 2) :
    (2 * β - 2) * cost n a ≤
      action n β u w e d q r s t (a * v) + action n β u w e d q r s t (a⁻¹ * v) -
        2 * action n β u w e d q r s t v := by
  have h1 := WilsonSmallFieldCurvature.middle_second_small n β hβ a u w v hflat hu hw
  have h2 := action_second_lower n β hβ u w e d hed q r hq hr s t hs ht v a
  linarith

end
end UnifiedTheory.Clay.YangMills.WilsonTiltedMiddleAction
