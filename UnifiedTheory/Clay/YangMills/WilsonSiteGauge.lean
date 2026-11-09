/- One-vertex gauge rotations and their volume-independent temporal cost.
Repeated edge occurrences, including period one, are counted explicitly. -/
import UnifiedTheory.Clay.YangMills.WilsonJointRotation

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonSiteGauge
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonSlabGauge WilsonRowGeometry
open scoped Quaternion

variable (n : ℕ) [NeZero n]

def siteGauge (x : SpatialVertex n) (q : Q) : SliceGauge n Q := by
  classical
  exact fun y => if y = x then q else 1

def rotate (x : SpatialVertex n) (q : Q) (v : Slice n) : Slice n :=
  gaugeSlice (siteGauge n x q) v

omit [NeZero n] in
theorem rotate_one (x : SpatialVertex n) (v : Slice n) : rotate n x 1 v = v := by
  have h : siteGauge n x 1 = 1 := by funext y; simp [siteGauge]
  rw [rotate, h, gaugeSlice_one]

omit [NeZero n] in
theorem rotate_mul (x : SpatialVertex n) (q r : Q) (v : Slice n) :
    rotate n x q (rotate n x r v) = rotate n x (q*r) v := by
  have h : siteGauge n x q * siteGauge n x r = siteGauge n x (q*r) := by
    funext y
    by_cases hy : y = x <;> simp [siteGauge, hy]
  rw [rotate, rotate, ← gaugeSlice_mul, h]
  rfl

omit [NeZero n] in
theorem rotate_continuous (x : SpatialVertex n) :
    Continuous (fun z : Q × Slice n => rotate n x z.1 z.2) := by
  classical
  have hg (y : SpatialVertex n) : Continuous (fun q : Q => siteGauge n x q y) := by
    by_cases hy : y = x
    · simpa only [siteGauge, if_pos hy] using (continuous_id : Continuous (fun q : Q => q))
    · simpa only [siteGauge, if_neg hy] using
        (continuous_const : Continuous (fun _q : Q => (1 : Q)))
  unfold rotate gaugeSlice
  apply continuous_pi
  intro e
  exact (((hg e.1).comp continuous_fst).mul ((continuous_apply e).comp continuous_snd)).mul
    (((hg (spatialStep n e.1 e.2)).comp continuous_fst).inv)

theorem rotate_integral (x : SpatialVertex n) (q : Q) (F : Slice n → ℝ) :
    (∫ v, F (rotate n x q v) ∂WilsonSlabOperator.measure n) =
      ∫ v, F v ∂WilsonSlabOperator.measure n :=
  (gauge_preserves_spatial (siteGauge n x q)).integral_comp
    (gaugeHomeomorph (siteGauge n x q)).measurableEmbedding F

omit n [NeZero n] in
theorem chord_gauge (a b v : Q) :
    ‖((a*v*b⁻¹ : Q) : ℍ)-(v : ℍ)‖ ≤ ‖(a : ℍ)-1‖+‖(b : ℍ)-1‖ := by
  have hi : ‖((b⁻¹ : Q) : ℍ)-1‖ = ‖(b : ℍ)-1‖ := by
    change ‖star (b : ℍ)-1‖ = _
    simpa only [star_sub, star_one] using norm_star ((b : ℍ)-1)
  change ‖(a : ℍ)*(v : ℍ)*((b⁻¹ : Q) : ℍ)-(v : ℍ)‖ ≤ _
  calc
    _ = ‖((a : ℍ)-1)*(v : ℍ)*((b⁻¹ : Q) : ℍ)+
        (v : ℍ)*(((b⁻¹ : Q) : ℍ)-1)‖ := by congr 1; noncomm_ring
    _ ≤ _ := (norm_add_le _ _).trans_eq (by
      rw [norm_mul, norm_mul, norm_mul, QuaternionSymmetricChange.unit_norm,
        QuaternionSymmetricChange.unit_norm, one_mul, mul_one, mul_one, hi])

theorem gauge_cost (x : SpatialVertex n) (q : Q) (v : Slice n) :
    inputCost n (rotate n x q v) v ≤ 6*‖(q : ℍ)-1‖ := by
  classical
  let d : SpatialVertex n → ℝ := fun y => if y = x then ‖(q : ℍ)-1‖ else 0
  have hd (y : SpatialVertex n) : ‖(siteGauge n x q y : ℍ)-1‖ = d y := by
    by_cases hy : y = x <;> simp [siteGauge, d, hy]
  have he (e : SpatialVertex n × Fin 3) :
      ‖((rotate n x q v e : Q) : ℍ)-(v e : ℍ)‖ ≤ d e.1+d (spatialStep n e.1 e.2) := by
    simpa only [rotate, gaugeSlice, hd] using chord_gauge
      (siteGauge n x q e.1) (siteGauge n x q (spatialStep n e.1 e.2)) (v e)
  apply (Finset.sum_le_sum (fun e _ => he e)).trans_eq
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [Finset.sum_add_distrib, WilsonJointRotation.step_sum n d]
  simp [d]
  ring

theorem kinetic_difference (x : SpatialVertex n) (q : Q) (u v : Slice n) :
    |kineticAction WilsonSingleLinkStaples.character 2 u (rotate n x q v)-
      kineticAction WilsonSingleLinkStaples.character 2 u v| ≤ 12*‖(q : ℍ)-1‖ := by
  have h := kinetic_difference_bound n v (rotate n x q v) u
  rw [kineticAction_symm WilsonSingleLinkStaples.character
    WilsonSingleLinkStaples.character_inverse_re 2 (rotate n x q v) u,
    kineticAction_symm WilsonSingleLinkStaples.character
      WilsonSingleLinkStaples.character_inverse_re 2 v u, inputCost_symm] at h
  exact h.trans (by linarith [gauge_cost n x q v])

end
end UnifiedTheory.Clay.YangMills.WilsonSiteGauge
