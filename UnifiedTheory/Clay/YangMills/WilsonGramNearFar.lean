/- The nearby part of every actual likelihood Gram row has a proved
volume-independent bound. The remaining term is an explicit sum of
mixed responses of the constructed ground amplitude at distant links. -/
import UnifiedTheory.Clay.YangMills.WilsonSpatialGramNeighborhood
import UnifiedTheory.Clay.YangMills.WilsonCollectiveGram

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonGramNearFar
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonTemporalInfluence
open WilsonRowGram WilsonMixedGroundResponse WilsonSpatialGramNeighborhood
open WilsonVarianceResponse WilsonPhysicalVariance WilsonDissipationIteration CompactDensityEntropy

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

/-- Diagonal control bounds each correlation, without asserting independence. -/
theorem gram_abs_of_cap (β : ℝ) (hβ : 0 ≤ β) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (u : Slice n) (D : ℝ) (hD : 0 ≤ D)
    (hq : coefficient β q ≤ D) (hr : coefficient β r ≤ D) :
    |gram n β hβ e d q r u| ≤ D := by
  letI := rowLaw_probability n β hβ u
  have hc := integral_product_sq (rowLaw n β hβ u)
    (score n β hβ e q u) (score n β hβ d r u)
    (score_continuous n β hβ e q u) (score_continuous n β hβ d r u)
  simp only [pow_two] at hc
  change gram n β hβ e d q r u * gram n β hβ e d q r u ≤
    gram n β hβ e e q q u * gram n β hβ d d r r u at hc
  have hb := mul_le_mul ((gram_diagonal_bound n β hβ e q u).trans hq)
    ((gram_diagonal_bound n β hβ d r u).trans hr) (gram_diagonal_nonneg n β hβ d r u) hD
  have hs : |gram n β hβ e d q r u|^2 ≤ D^2 := by
    rw [sq_abs, pow_two, pow_two]
    exact hc.trans hb
  exact (sq_le_sq₀ (abs_nonneg _) hD).mp hs

def farCost (β : ℝ) (hβ : 0 ≤ β) (rotations : SpatialVertex n × Fin 3 → Q)
    (u : Slice n) (e : SpatialVertex n × Fin 3) : ℝ :=
  ∑ d ∈ Finset.univ \ near n e,
    |Real.exp (groundMixedLog n β hβ e d (rotations e) (rotations d) u)-1|

theorem farCost_nonneg (β : ℝ) (hβ : 0 ≤ β) (rotations : SpatialVertex n × Fin 3 → Q)
    (u : Slice n) (e : SpatialVertex n × Fin 3) : 0 ≤ farCost n β hβ rotations u e :=
  Finset.sum_nonneg (fun d _ => abs_nonneg
    (Real.exp (groundMixedLog n β hβ e d (rotations e) (rotations d) u)-1))

/-- Exact separation of the bare-action neighborhood from the remaining ground response. -/
theorem row_split (β : ℝ) (hβ : 0 ≤ β) (rotations : SpatialVertex n × Fin 3 → Q)
    (u : Slice n) (e : SpatialVertex n × Fin 3) :
    (∑ d, |gram n β hβ e d (rotations e) (rotations d) u|) =
      (∑ d ∈ near n e, |gram n β hβ e d (rotations e) (rotations d) u|) +
        farCost n β hβ rotations u e := by
  have hf : (∑ d ∈ Finset.univ \ near n e,
      |gram n β hβ e d (rotations e) (rotations d) u|) = farCost n β hβ rotations u e := by
    apply Finset.sum_congr rfl
    intro d hd
    have hdn := (Finset.mem_sdiff.mp hd).2
    rw [gram_ground_log n β hβ e d (rotations e) (rotations d)
      (far_ne n e d hdn) (far_disjoint n e d hdn)]
  rw [← hf]
  exact (Finset.sum_add_sum_compl (near n e) _).symm

/-- Only sixteen nearby entries are charged the full local diagonal bound. -/
theorem near_sum_bound (β : ℝ) (hβ : 0 ≤ β) (rotations : SpatialVertex n × Fin 3 → Q)
    (u : Slice n) (e : SpatialVertex n × Fin 3) (D : ℝ) (hD : 0 ≤ D)
    (hcap : ∀ d, coefficient β (rotations d) ≤ D) :
    (∑ d ∈ near n e, |gram n β hβ e d (rotations e) (rotations d) u|) ≤ 16*D := by
  calc
    _ ≤ ∑ _d ∈ near n e, D := Finset.sum_le_sum (fun d _ =>
      gram_abs_of_cap n β hβ e d _ _ u D hD (hcap e) (hcap d))
    _ = ((near n e).card : ℝ)*D := by simp
    _ ≤ 16*D := by
      have hn : ((near n e).card : ℝ) ≤ 16 := by exact_mod_cast near_card n e
      exact mul_le_mul_of_nonneg_right hn hD

theorem row_bound (β : ℝ) (hβ : 0 ≤ β) (rotations : SpatialVertex n × Fin 3 → Q)
    (u : Slice n) (e : SpatialVertex n × Fin 3) (D : ℝ) (hD : 0 ≤ D)
    (hcap : ∀ d, coefficient β (rotations d) ≤ D) :
    (∑ d, |gram n β hβ e d (rotations e) (rotations d) u|) ≤
      16*D + farCost n β hβ rotations u e := by
  rw [row_split]
  exact _root_.add_le_add (near_sum_bound n β hβ rotations u e D hD hcap) le_rfl

theorem scaled_near_sum_bound (β : ℝ) (hβ : 0 ≤ β)
    (rotations : SpatialVertex n × Fin 3 → Q)
    (hscale : ∀ d, β * ‖(rotations d : Quaternion ℝ) - 1‖ ≤ 1)
    (u : Slice n) (e : SpatialVertex n × Fin 3) :
    (∑ d ∈ near n e, |gram n β hβ e d (rotations e) (rotations d) u|) ≤
      16*(Real.exp 4-1)^2 :=
  near_sum_bound n β hβ rotations u e _ (sq_nonneg _)
    (fun d => coefficient_scaled β hβ (rotations d) (hscale d))

/-- All nearby entries have a common cutoff-independent bound for these shrinking rotations. -/
theorem scaled_row_bound (β : ℝ) (hβ : 0 ≤ β)
    (rotations : SpatialVertex n × Fin 3 → Q)
    (hscale : ∀ d, β * ‖(rotations d : Quaternion ℝ) - 1‖ ≤ 1)
    (u : Slice n) (e : SpatialVertex n × Fin 3) :
    (∑ d, |gram n β hβ e d (rotations e) (rotations d) u|) ≤
      16*(Real.exp 4-1)^2 + farCost n β hβ rotations u e :=
  row_bound n β hβ rotations u e _ (sq_nonneg _)
    (fun d => coefficient_scaled β hβ (rotations d) (hscale d))

/-- The sole missing upper-bound input is now the displayed actual distant-ground sum. -/
theorem energy_le_loss_of_far (β : ℝ) (hβ : 0 ≤ β)
    (rotations : SpatialVertex n × Fin 3 → Q) (D R : ℝ) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hcap : ∀ d, coefficient β (rotations d) ≤ D)
    (hfar : ∀ u e, farCost n β hβ rotations u e ≤ R) (f : C(Slice n, ℝ)) :
    WilsonCollectiveGram.energy n β hβ id rotations (fun _ => 1) (step n β hβ f) ≤
      (16*D+R)*loss n β hβ f := by
  apply WilsonCollectiveGram.energy_le_loss n β hβ id rotations (fun _ => 1)
    (16*D+R) (by positivity)
  intro u e
  simpa only [WilsonCollectiveGram.matrix, id_eq, one_mul] using
    (row_bound n β hβ rotations u e D hD hcap).trans (_root_.add_le_add le_rfl (hfar u e))

theorem time_sum_of_far (β : ℝ) (hβ : 0 ≤ β)
    (rotations : SpatialVertex n × Fin 3 → Q) (D R : ℝ) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hcap : ∀ d, coefficient β (rotations d) ≤ D)
    (hfar : ∀ u e, farCost n β hβ rotations u e ≤ R) (f : C(Slice n, ℝ)) (k : ℕ) :
    (∑ j ∈ Finset.range k, WilsonCollectiveGram.energy n β hβ id rotations (fun _ => 1)
      (flow n β hβ f (j+1))) ≤
        (16*D+R)*(variance n β hβ f-variance n β hβ (flow n β hβ f k)) := by
  calc
    _ ≤ ∑ j ∈ Finset.range k, (16*D+R)*loss n β hβ (flow n β hβ f j) :=
      Finset.sum_le_sum (fun j _ => energy_le_loss_of_far n β hβ rotations D R hD hR hcap hfar _)
    _ = _ := by rw [← Finset.mul_sum, loss_telescope]

end
end UnifiedTheory.Clay.YangMills.WilsonGramNearFar
