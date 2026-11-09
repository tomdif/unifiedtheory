/- Finite-block gauge rotations. The cost counts only rotated vertices,
including all edge endpoint occurrences on small periodic lattices. -/
import UnifiedTheory.Clay.YangMills.WilsonGaugeOrbitTail
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonGaugeBlock
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonSlabGauge WilsonRowGeometry
open scoped Quaternion

variable (n : ℕ) [NeZero n]

abbrev Parameters (B : Finset (SpatialVertex n)) := B → Q
abbrev haar (B : Finset (SpatialVertex n)) : Measure (Parameters n B) :=
  Measure.pi (fun _ : B => RegulatedGauge.compactHaar Q)

def gauge (B : Finset (SpatialVertex n)) (q : Parameters n B) : SliceGauge n Q := by
  classical
  exact fun y => if hy : y ∈ B then q ⟨y,hy⟩ else 1

def rotate (B : Finset (SpatialVertex n)) (q : Parameters n B) (v : Slice n) : Slice n :=
  gaugeSlice (gauge n B q) v

omit [NeZero n] in
theorem rotate_mul (B : Finset (SpatialVertex n)) (q r : Parameters n B) (v : Slice n) :
    rotate n B q (rotate n B r v) = rotate n B (q*r) v := by
  classical
  have h : gauge n B q*gauge n B r = gauge n B (q*r) := by
    funext y
    by_cases hy : y ∈ B <;> simp [gauge, hy]
  rw [rotate, rotate, ← gaugeSlice_mul, h]
  rfl

omit [NeZero n] in
theorem rotate_continuous (B : Finset (SpatialVertex n)) :
    Continuous (fun z : Parameters n B × Slice n => rotate n B z.1 z.2) := by
  classical
  have hg (y : SpatialVertex n) : Continuous (fun q : Parameters n B => gauge n B q y) := by
    by_cases hy : y ∈ B
    · simpa only [gauge, dif_pos hy] using (continuous_apply (⟨y,hy⟩ : B))
    · simpa only [gauge, dif_neg hy] using
        (continuous_const : Continuous (fun _q : Parameters n B => (1 : Q)))
  unfold rotate gaugeSlice
  apply continuous_pi
  intro e
  exact (((hg e.1).comp continuous_fst).mul ((continuous_apply e).comp continuous_snd)).mul
    (((hg (spatialStep n e.1 e.2)).comp continuous_fst).inv)

theorem rotate_integral (B : Finset (SpatialVertex n)) (q : Parameters n B)
    (F : Slice n → ℝ) :
    (∫ v, F (rotate n B q v) ∂WilsonSlabOperator.measure n) =
      ∫ v, F v ∂WilsonSlabOperator.measure n :=
  (gauge_preserves_spatial (gauge n B q)).integral_comp
    (gaugeHomeomorph (gauge n B q)).measurableEmbedding F

theorem gauge_cost (h : SliceGauge n Q) (v : Slice n) :
    inputCost n (gaugeSlice h v) v ≤ 6*∑ y, ‖(h y : ℍ)-1‖ := by
  let d := fun y : SpatialVertex n => ‖(h y : ℍ)-1‖
  have he (e : SpatialVertex n × Fin 3) :
      ‖((gaugeSlice h v e : Q) : ℍ)-(v e : ℍ)‖ ≤ d e.1+d (spatialStep n e.1 e.2) :=
    WilsonSiteGauge.chord_gauge (h e.1) (h (spatialStep n e.1 e.2)) (v e)
  apply (Finset.sum_le_sum (fun e _ => he e)).trans_eq
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [Finset.sum_add_distrib, WilsonJointRotation.step_sum n d]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  dsimp only [d]
  ring

theorem gauge_sum (B : Finset (SpatialVertex n)) (q : Parameters n B) :
    (∑ y, ‖(gauge n B q y : ℍ)-1‖) = ∑ y : B, ‖(q y : ℍ)-1‖ := by
  classical
  let F := fun y : SpatialVertex n => ‖(gauge n B q y : ℍ)-1‖
  have hz (y : SpatialVertex n) (hy : y ∉ B) : F y = 0 := by simp [F, gauge, hy]
  have hs : (∑ y ∈ B, F y) = ∑ y, F y :=
    Finset.sum_subset (Finset.subset_univ B) (fun y _ hy => hz y hy)
  change (∑ y, F y) = _
  rw [← hs, Finset.sum_subtype B (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro y _
  simp only [F, gauge, dif_pos y.property]

theorem kinetic_difference (B : Finset (SpatialVertex n)) (q : Parameters n B)
    (u v : Slice n) :
    |kineticAction WilsonSingleLinkStaples.character 2 u (rotate n B q v)-
      kineticAction WilsonSingleLinkStaples.character 2 u v| ≤
      12*∑ y : B, ‖(q y : ℍ)-1‖ := by
  have h := kinetic_difference_bound n v (rotate n B q v) u
  rw [kineticAction_symm WilsonSingleLinkStaples.character
    WilsonSingleLinkStaples.character_inverse_re 2 (rotate n B q v) u,
    kineticAction_symm WilsonSingleLinkStaples.character
      WilsonSingleLinkStaples.character_inverse_re 2 v u, inputCost_symm] at h
  have hg := gauge_cost n (gauge n B q) v
  rw [gauge_sum] at hg
  change inputCost n (rotate n B q v) v ≤ 6*∑ y : B, ‖(q y : ℍ)-1‖ at hg
  exact h.trans (by linarith)

end
end UnifiedTheory.Clay.YangMills.WilsonGaugeBlock
