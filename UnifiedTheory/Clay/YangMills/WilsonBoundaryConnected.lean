/- The literal finite Wilson boundary mixed partition is an integrated
connected covariance of two local kinetic defects. The finite endpoint
message and every source normalizer remain in the law. The unconditional
oscillation estimate is bilinear in the displacements but has no spatial
decay; it does not close the distant sum. -/
import UnifiedTheory.Clay.YangMills.WilsonBoundaryMixedLimit
import UnifiedTheory.Clay.YangMills.CompactConnectedRectangle

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonBoundaryConnected
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator
open WilsonSingleLinkStaples (character character_continuous)
open WilsonBoundaryPointwise WilsonBoundaryMixedLimit WilsonSymmetricLinkChange
open WilsonRowGeometry WilsonVarianceResponse

variable (n : ℕ) [NeZero n]

/-- The true finite output action, including the propagated spatial endpoint. -/
def boundaryAction (β : ℝ) (j : ℕ) (u v : Slice n) : ℝ :=
  β*kineticAction character 2 u v-Real.log (spatialWeight character β 2 v)-
    Real.log (boundaryMessage n β j v)

theorem boundaryAction_continuous (β : ℝ) (j : ℕ) (u : Slice n) :
    Continuous (boundaryAction n β j u) := by
  have hc := character_continuous
  have hk : Continuous (fun v : Slice n => kineticAction character 2 u v) := by
    unfold kineticAction
    fun_prop
  have hw : Continuous (fun v : Slice n => spatialWeight character β 2 v) := by
    unfold spatialWeight potential spatialHolonomy
    fun_prop
  exact ((continuous_const.mul hk).sub (hw.log (fun _ => (Real.exp_pos _).ne'))).sub
    ((boundaryMessage n β j).continuous.log (fun v => (boundaryMessage_pos n β j v).ne'))

theorem boundaryAction_weight (β : ℝ) (j : ℕ) (u v : Slice n) :
    Real.exp (-boundaryAction n β j u v) =
      kineticWeight character β 2 u v*spatialWeight character β 2 v*boundaryMessage n β j v := by
  have he : -boundaryAction n β j u v = -β*kineticAction character 2 u v+
      Real.log (spatialWeight character β 2 v)+Real.log (boundaryMessage n β j v) := by
    unfold boundaryAction
    ring
  have hw : 0 < spatialWeight character β 2 v := Real.exp_pos _
  rw [he, Real.exp_add, Real.exp_add, Real.exp_log hw,
    Real.exp_log (boundaryMessage_pos n β j v)]
  rfl

theorem boundaryPartition_action (β : ℝ) (j : ℕ) (u : Slice n) :
    boundaryPartition n β j u = ∫ v, Real.exp (-boundaryAction n β j u v) ∂measure n := by
  simp only [boundaryAction_weight, boundaryPartition]

theorem boundaryPartition_pos (β : ℝ) (j : ℕ) (u : Slice n) :
    0 < boundaryPartition n β j u := by
  rw [boundaryPartition_action]
  exact CompactGibbsContinuity.partition_positive (measure n) _
    (boundaryAction_continuous n β j u)

/-- The source is the exact kinetic action difference for one input rotation. -/
def source (β : ℝ) (e : SpatialVertex n × Fin 3) (q : Q) (u v : Slice n) : ℝ :=
  β*(kineticAction character 2 u v-kineticAction character 2 (shift n e q u) v)

theorem source_continuous (β : ℝ) (e : SpatialVertex n × Fin 3) (q : Q) (u : Slice n) :
    Continuous (source n β e q u) := by
  have hc := character_continuous
  unfold source kineticAction
  fun_prop

/-- Despite the full-action definition, only one output link occurs in this insertion. -/
theorem source_local (β : ℝ) (e : SpatialVertex n × Fin 3) (q : Q) (u v : Slice n) :
    source n β e q u v = β*((character ((q*u e)⁻¹*v e)).re-
      (character ((u e)⁻¹*v e)).re) := by
  classical
  unfold source
  rw [kinetic_difference]
  congr 1
  rw [Finset.sum_eq_single e]
  · rw [shift_at]
  · intro d _ hde
    rw [shift_away n e q u d hde, sub_self]
  · simp

theorem source_shift_away (β : ℝ) (e d : SpatialVertex n × Fin 3) (q r : Q)
    (hed : e ≠ d) (u v : Slice n) :
    source n β e q (shift n d r u) v = source n β e q u v := by
  simp only [source_local, shift_away n d r u e hed]

theorem source_bound (β : ℝ) (hβ : 0 ≤ β) (e : SpatialVertex n × Fin 3)
    (q : Q) (u v : Slice n) :
    |source n β e q u v| ≤ 2*β*‖(q : Quaternion ℝ)-1‖ := by
  unfold source
  rw [abs_mul, abs_of_nonneg hβ]
  have h := mul_le_mul_of_nonneg_left
    (kinetic_difference_bound n (shift n e q u) u v) hβ
  rw [shift_cost] at h
  convert h using 1
  ring

theorem boundaryAction_shift (β : ℝ) (j : ℕ) (e : SpatialVertex n × Fin 3)
    (q : Q) (u v : Slice n) :
    boundaryAction n β j (shift n e q u) v =
      boundaryAction n β j u v-source n β e q u v := by
  unfold boundaryAction source
  ring

/-- Every point of the source rectangle retains the actual finite weight. -/
theorem tilted_weight (β : ℝ) (j : ℕ) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (u v : Slice n) (s t : ℝ) :
    CompactGibbsSource.weight
      (CompactGibbsSource.action (boundaryAction n β j u) (source n β e q u) s)
      (source n β d r u) t v =
      (kineticWeight character β 2 u v*spatialWeight character β 2 v*boundaryMessage n β j v)*
        Real.exp (s*source n β e q u v+t*source n β d r u v) := by
  simp only [CompactGibbsSource.weight, CompactGibbsSource.action]
  rw [show -(boundaryAction n β j u v-s*source n β e q u v-t*source n β d r u v) =
    -boundaryAction n β j u v+(s*source n β e q u v+t*source n β d r u v) by ring,
    Real.exp_add, boundaryAction_weight]

/-- The direct range argument is uniform in both sources and depth, but it
does not improve when the two links are farther apart. -/
theorem connected_bound (β : ℝ) (hβ : 0 ≤ β) (j : ℕ)
    (e d : SpatialVertex n × Fin 3) (q r : Q) (u : Slice n) (s t : ℝ) :
    |CompactGibbsSource.covariance (measure n)
      (CompactGibbsSource.action (boundaryAction n β j u) (source n β e q u) s)
      (source n β d r u) (source n β e q u) (source n β d r u) t| ≤
        4*β^2*‖(q : Quaternion ℝ)-1‖*‖(r : Quaternion ℝ)-1‖ := by
  have h := CompactGibbsOscillation.source_covariance_bound (measure n)
    (CompactGibbsSource.action (boundaryAction n β j u) (source n β e q u) s)
    (source n β d r u) (source n β e q u)
    (CompactGibbsSource.action_continuous _ _ (boundaryAction_continuous n β j u)
      (source_continuous n β e q u) s)
    (source_continuous n β d r u) (source_continuous n β e q u)
    (-(2*β*‖(r : Quaternion ℝ)-1‖)) (2*β*‖(r : Quaternion ℝ)-1‖)
    (-(2*β*‖(q : Quaternion ℝ)-1‖)) (2*β*‖(q : Quaternion ℝ)-1‖)
    (by
      have : 0 ≤ 2*β*‖(r : Quaternion ℝ)-1‖ := by positivity
      linarith)
    (by
      have : 0 ≤ 2*β*‖(q : Quaternion ℝ)-1‖ := by positivity
      linarith)
    (fun v => abs_le.mp (source_bound n β hβ d r u v))
    (fun v => abs_le.mp (source_bound n β hβ e q u v)) t
  convert h using 1
  ring

/-- Positive mixed logarithmic partition increment; no spatial factor is included. -/
def mixedLog (β : ℝ) (j : ℕ) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (u : Slice n) : ℝ :=
  Real.log (boundaryPartition n β j u)+
    Real.log (boundaryPartition n β j (shift n e q (shift n d r u)))-
    Real.log (boundaryPartition n β j (shift n e q u))-
    Real.log (boundaryPartition n β j (shift n d r u))

theorem mixedLog_eq_mixed (β : ℝ) (j : ℕ) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (hed : e ≠ d) (u : Slice n) :
    mixedLog n β j e d q r u = -GibbsMixedInteraction.mixed (measure n)
      (boundaryAction n β j u) (source n β e q u) (source n β d r u) := by
  have he (v : Slice n) : boundaryAction n β j u v-source n β e q u v-
      source n β d r u v = boundaryAction n β j (shift n e q (shift n d r u)) v := by
    rw [boundaryAction_shift, source_shift_away n β e d q r hed, boundaryAction_shift]
    ring
  unfold GibbsMixedInteraction.mixed GibbsMixedInteraction.freeEnergy mixedLog
  simp_rw [he, ← boundaryAction_shift, ← boundaryPartition_action]
  ring

/-- Exact normalized connected covariance, integrated over both source strengths.
The original finite message stays inside every tilted law. -/
theorem mixedLog_integral (β : ℝ) (j : ℕ) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (hed : e ≠ d) (u : Slice n) :
    mixedLog n β j e d q r u =
      ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
        CompactGibbsSource.covariance (measure n)
          (CompactGibbsSource.action (boundaryAction n β j u) (source n β e q u) s)
          (source n β d r u) (source n β e q u) (source n β d r u) t := by
  rw [mixedLog_eq_mixed n β j e d q r hed]
  exact CompactConnectedRectangle.mixed_integral (measure n) _ _ _
    (boundaryAction_continuous n β j u) (source_continuous n β e q u)
    (source_continuous n β d r u)

/-- An unconditional bilinear bound, uniform in cylinder depth and background.
There is no distance decay in this estimate, so its far sum can cost the volume. -/
theorem mixedLog_bound (β : ℝ) (hβ : 0 ≤ β) (j : ℕ)
    (e d : SpatialVertex n × Fin 3) (q r : Q) (hed : e ≠ d) (u : Slice n) :
    |mixedLog n β j e d q r u| ≤
      4*β^2*‖(q : Quaternion ℝ)-1‖*‖(r : Quaternion ℝ)-1‖ := by
  rw [mixedLog_eq_mixed n β j e d q r hed, abs_neg]
  have h := GibbsMixedInteraction.mixed_bound (measure n)
    (boundaryAction n β j u) (source n β e q u) (source n β d r u)
    (boundaryAction_continuous n β j u) (source_continuous n β e q u)
    (source_continuous n β d r u)
    (-(2*β*‖(q : Quaternion ℝ)-1‖)) (2*β*‖(q : Quaternion ℝ)-1‖)
    (-(2*β*‖(r : Quaternion ℝ)-1‖)) (2*β*‖(r : Quaternion ℝ)-1‖)
    (by
      have : 0 ≤ 2*β*‖(q : Quaternion ℝ)-1‖ := by positivity
      linarith)
    (by
      have : 0 ≤ 2*β*‖(r : Quaternion ℝ)-1‖ := by positivity
      linarith)
    (fun v => abs_le.mp (source_bound n β hβ e q u v))
    (fun v => abs_le.mp (source_bound n β hβ d r u v))
  convert h using 1
  ring

/-- For the actual distant pair, exponentiating gives precisely the earlier
finite-boundary response, not a proxy partition or a linearized response. -/
theorem boundaryRatio_eq_exp (β : ℝ) (j : ℕ) (e d : SpatialVertex n × Fin 3)
    (q r : Q) (hed : e ≠ d)
    (hd : Disjoint (WilsonSlabLocalComparison.affected n e.1 e.2)
      (WilsonSlabLocalComparison.affected n d.1 d.2)) (u : Slice n) :
    boundaryRatio n β j e d q r u = Real.exp (mixedLog n β j e d q r u)-1 := by
  rw [boundaryRatio_partition n β j e d q r hed hd]
  unfold mixedLog
  rw [Real.exp_sub, Real.exp_sub, Real.exp_add]
  simp only [Real.exp_log (boundaryPartition_pos n β j _)]
  ring

end
end UnifiedTheory.Clay.YangMills.WilsonBoundaryConnected
