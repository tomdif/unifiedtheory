/- The entire row of high-defect bridge events has a volume-independent
source bound after one actual transfer step. Marking the other endpoint
costs cluster size, absorbed in the activity. No loss term is summed over
targets. A slow eigenfunction inherits this bound without a residual charge.
These events are not asserted to represent the complete ground response. -/
import UnifiedTheory.Clay.YangMills.FiniteMarkedEventSum
import UnifiedTheory.Clay.YangMills.WilsonMarkedClusterActivity
import UnifiedTheory.Clay.YangMills.WilsonBadClusterBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonBridgeOutputSum
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonTimeSlab WilsonGroundHeatBath
open WilsonPhysicalVariance WilsonHighFieldDecay WilsonHighFieldReduction
open SpatialPlaquetteCutGeometry WilsonGroundSlabEnergy WilsonClusterSourceDecay
open WilsonConnectedActivity WilsonConnectedSource
open WilsonPatchSourceTail (hard hard_measurable cutoff cutoff_one cutoff_range cutoff_supported)

variable (n : ℕ) [NeZero n]

/-- A direct output estimate, before the slow-mode residual is introduced. -/
theorem hard_output (S : Finset (Plaquette (2 * n)))
    (β : ℝ) (hβ : 0 < β) (R : ℝ) (hmargin : 96 * envelope β ≤ R) (hR : 0 < R)
    (f : C(Slice (2 * (2 * n)), ℝ)) :
    (∫ u, (hard (2 * n) S R).indicator
      (fun v => (step (2 * (2 * n)) β hβ.le f v)^2) u
      ∂groundLaw (2 * (2 * n)) β hβ.le) ≤
      (rate β R)^S.card * mass (2 * (2 * n)) β hβ.le f := by
  letI := groundLaw_probability (2 * (2 * n)) β hβ.le
  let P := step (2 * (2 * n)) β hβ.le f
  have hi : (∫ u, (hard (2 * n) S R).indicator (fun v => (P v)^2) u
      ∂groundLaw (2 * (2 * n)) β hβ.le) ≤
      mass (2 * (2 * n)) β hβ.le (cutoff (2 * n) S R * P) := by
    apply integral_mono
    · exact (CompactDensityEntropy.continuous_integrable _ _ (P.continuous.pow 2)).indicator
        (hard_measurable (2 * n) S R)
    · exact CompactDensityEntropy.continuous_integrable _ _
        ((cutoff (2 * n) S R * P).continuous.pow 2)
    · intro u
      by_cases hu : u ∈ hard (2 * n) S R
      · rw [Set.indicator_of_mem hu]
        simp only [ContinuousMap.mul_apply,
          cutoff_one (2 * n) S R hR u (fun p hp => hu ⟨p,hp⟩), one_mul, le_refl]
      · rw [Set.indicator_of_notMem hu]
        exact sq_nonneg _
  exact hi.trans (WilsonClusterSourceTail.cutoff_output n S β hβ R hmargin
    (cutoff (2 * n) S R) f (cutoff_range (2 * n) S R)
    (cutoff_supported (2 * n) S R hR))

/-- Distance is discrete plaquette-graph distance; m=1 includes every target. -/
def farEvent (p q : Plaquette (2 * n)) (m : ℕ) (R : ℝ) : Set (Slice (2 * (2 * n))) :=
  if m ≤ WilsonBadClusterBridge.distance n p q + 1 then
    WilsonBadClusterBridge.event n p q R else ∅

theorem farEvent_measurable (p q : Plaquette (2 * n)) (m : ℕ) (R : ℝ) :
    MeasurableSet (farEvent n p q m R) := by
  unfold farEvent
  split_ifs
  · exact WilsonBadClusterBridge.event_measurable n p q R
  · exact MeasurableSet.empty

/-- A bridge to a distant target has a rooted connected witness containing that target. -/
theorem farEvent_cover (p q : Plaquette (2 * n)) (m : ℕ) (R : ℝ)
    (u : Slice (2 * (2 * n))) (hu : u ∈ farEvent n p q m R) :
    ∃ i : PatternIndex n p m, q ∈ patterns n p m i ∧
      u ∈ hard (2 * n) (patterns n p m i) R := by
  unfold farEvent at hu
  split_ifs at hu with hd
  · obtain ⟨S,hS⟩ := hu
    obtain ⟨hp,hq,hconn⟩ := (WilsonBadClusterBridge.sets_mem n p q S.val).mp S.property
    have hdist := FiniteConnectedDistance.distance_lt_card
      (WilsonPlaquetteGraph.graph (2 * (2 * n))) S.val p q hp hq hconn
    change (WilsonPlaquetteGraph.graph (2 * (2 * n))).dist p q + 1 ≥ m at hd
    obtain ⟨i,hi⟩ := (exists_index (2 * (2 * n)) p m S.val).mpr ⟨hp,by omega,hconn⟩
    refine ⟨i,?_,?_⟩
    · change q ∈ marked _ _ _ _ i
      rwa [hi]
    · change u ∈ hard (2 * n) (marked _ _ _ _ i) R
      rw [hi]
      exact hS
  · exact False.elim hu

/-- Source-squared mass summed over every target connected to the root by a bad bridge. -/
def weightedCount (p : Plaquette (2 * n)) (m : ℕ) (R β : ℝ) (hβ : 0 ≤ β)
    (f : C(Slice (2 * (2 * n)), ℝ)) : ℝ :=
  ∑ q, ∫ u, (farEvent n p q m R).indicator (fun v => (f v)^2) u
    ∂groundLaw (2 * (2 * n)) β hβ

theorem weightedCount_nonneg (p : Plaquette (2 * n)) (m : ℕ) (R β : ℝ) (hβ : 0 ≤ β)
    (f : C(Slice (2 * (2 * n)), ℝ)) : 0 ≤ weightedCount n p m R β hβ f :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg
    (fun u => Set.indicator_nonneg (fun _ _ => sq_nonneg _) u))

theorem weightedCount_smul (p : Plaquette (2 * n)) (m : ℕ) (R β : ℝ) (hβ : 0 ≤ β)
    (c : ℝ) (f : C(Slice (2 * (2 * n)), ℝ)) :
    weightedCount n p m R β hβ (c • f) = c^2 * weightedCount n p m R β hβ f := by
  unfold weightedCount
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  by_cases hu : u ∈ farEvent n p q m R
  · simp only [Set.indicator_of_mem hu, ContinuousMap.smul_apply, smul_eq_mul, mul_pow]
  · simp only [Set.indicator_of_notMem hu, mul_zero]

/-- The whole distant-target sum, with no volume factor and no source-loss charge. -/
theorem output_sum (p : Plaquette (2 * n)) (m : ℕ) (hm : 0 < m)
    (β : ℝ) (hβ : 0 < β) (R : ℝ) (hmargin : 96 * envelope β ≤ R) (hR : 0 < R)
    (hsmall : 512 * rate β R < 1) (f : C(Slice (2 * (2 * n)), ℝ)) :
    weightedCount n p m R β hβ.le (step (2 * (2 * n)) β hβ.le f) ≤
      budget (2 * rate β R) m * mass (2 * (2 * n)) β hβ.le f := by
  classical
  letI := groundLaw_probability (2 * (2 * n)) β hβ.le
  let P := step (2 * (2 * n)) β hβ.le f
  have hc := FiniteMarkedEventSum.integral_sum
    (groundLaw (2 * (2 * n)) β hβ.le) (patterns n p m)
    (fun q => farEvent n p q m R) (fun i => hard (2 * n) (patterns n p m i) R)
    (fun q => farEvent_measurable n p q m R)
    (fun i => hard_measurable (2 * n) (patterns n p m i) R)
    (fun q u hu => farEvent_cover n p q m R u hu) (fun u => (P u)^2)
    (fun u => sq_nonneg _) (CompactDensityEntropy.continuous_integrable _ _ (P.continuous.pow 2))
  apply hc.trans
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hard_output n (patterns n p m i) β hβ R hmargin hR f)
      (Nat.cast_nonneg (patterns n p m i).card))
  simp only [← mul_assoc, ← Finset.sum_mul] at hsum
  apply hsum.trans
  exact mul_le_mul_of_nonneg_right
    (WilsonMarkedClusterActivity.activity_bound (2 * (2 * n)) p m _ hm
      (rate β R) (rate_pos β R).le hsmall) (mass_nonneg (2 * (2 * n)) β hβ.le f)

/-- Smoothing can be transferred to the eigenvalue for an actual eigenfunction. -/
theorem eigen_sum (p : Plaquette (2 * n)) (m : ℕ) (hm : 0 < m)
    (β : ℝ) (hβ : 0 < β) (R : ℝ) (hmargin : 96 * envelope β ≤ R) (hR : 0 < R)
    (hsmall : 512 * rate β R < 1) (f : C(Slice (2 * (2 * n)), ℝ)) (σ : ℝ)
    (heigen : step (2 * (2 * n)) β hβ.le f = σ • f) :
    σ^2 * weightedCount n p m R β hβ.le f ≤
      budget (2 * rate β R) m * mass (2 * (2 * n)) β hβ.le f := by
  have h := output_sum n p m hm β hβ R hmargin hR hsmall f
  rwa [heigen, weightedCount_smul] at h

theorem weak_output_sum (p : Plaquette (2 * n)) (m : ℕ) (hm : 0 < m)
    (β : ℝ) (hβ : 512 ≤ β) (f : C(Slice (2 * (2 * n)), ℝ)) :
    weightedCount n p m (WilsonClusterActivity.threshold β) β (by linarith)
      (step (2 * (2 * n)) β (by linarith) f) ≤
      (4 / (2 * β + 5)) * (1 / 2 : ℝ)^(m - 1) *
        mass (2 * (2 * n)) β (by linarith) f := by
  have hb : 0 < β := by linarith
  exact (output_sum n p m hm β hb (WilsonClusterActivity.threshold β)
    (WilsonClusterActivity.threshold_margin β hb) (WilsonClusterActivity.threshold_pos β hb)
    (by nlinarith [WilsonMarkedClusterActivity.rate_half β hβ]) f).trans
    (mul_le_mul_of_nonneg_right (WilsonMarkedClusterActivity.budget_bound β hβ m)
      (mass_nonneg (2 * (2 * n)) β hb.le f))

/-- A slow eigenfunction pays a small mass coefficient, with no loss charge per endpoint. -/
theorem slow_eigen_sum (p : Plaquette (2 * n)) (m : ℕ) (hm : 0 < m)
    (β : ℝ) (hβ : 512 ≤ β) (f : C(Slice (2 * (2 * n)), ℝ)) (σ : ℝ)
    (hσ : 1 / 2 ≤ σ ^ 2) (heigen : step (2 * (2 * n)) β (by linarith) f = σ • f) :
    weightedCount n p m (WilsonClusterActivity.threshold β) β (by linarith) f ≤
      (8 / (2 * β + 5)) * (1 / 2 : ℝ)^(m - 1) *
        mass (2 * (2 * n)) β (by linarith) f := by
  have hb : 0 < β := by linarith
  have hsmall : 512 * rate β (WilsonClusterActivity.threshold β) < 1 := by
    nlinarith [WilsonMarkedClusterActivity.rate_half β hβ]
  have h := eigen_sum n p m hm β hb (WilsonClusterActivity.threshold β)
    (WilsonClusterActivity.threshold_margin β hb) (WilsonClusterActivity.threshold_pos β hb)
    hsmall f σ heigen
  have hc := mul_le_mul_of_nonneg_right (WilsonMarkedClusterActivity.budget_bound β hβ m)
    (mass_nonneg (2 * (2 * n)) β hb.le f)
  have hl := mul_le_mul_of_nonneg_right hσ
    (weightedCount_nonneg n p m (WilsonClusterActivity.threshold β) β hb.le f)
  have he : 8 / (2 * β + 5) = 2 * (4 / (2 * β + 5)) := by ring
  rw [he]
  nlinarith

/-- On invariant sources this is an estimate for the original full gauge-averaged transition. -/
theorem physical_output_sum (p : Plaquette (2 * n)) (m : ℕ) (hm : 0 < m)
    (β : ℝ) (hβ : 512 ≤ β) (f : C(Slice (2 * (2 * n)), ℝ))
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) :
    (∑ q, ∫ u, (farEvent n p q m (WilsonClusterActivity.threshold β)).indicator
      (fun z => (∫ v, WilsonGroundLocalComparison.transition (2 * (2 * n)) β
        (by linarith) z v * f v ∂measure (2 * (2 * n)))^2) u
      ∂groundLaw (2 * (2 * n)) β (by linarith)) ≤
      (4 / (2 * β + 5)) * (1 / 2 : ℝ)^(m - 1) *
        mass (2 * (2 * n)) β (by linarith) f := by
  have h := weak_output_sum n p m hm β hβ f
  simpa only [weightedCount, step_full _ _ _ f hinv] using h

/-- The slow-mode estimate explicitly applies to eigenfunctions of that same physical transition. -/
theorem physical_slow_eigen_sum (p : Plaquette (2 * n)) (m : ℕ) (hm : 0 < m)
    (β : ℝ) (hβ : 512 ≤ β) (f : C(Slice (2 * (2 * n)), ℝ)) (σ : ℝ)
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) (hσ : 1 / 2 ≤ σ ^ 2)
    (heigen : ∀ u, (∫ v, WilsonGroundLocalComparison.transition (2 * (2 * n)) β
      (by linarith) u v * f v ∂measure (2 * (2 * n))) = σ * f u) :
    weightedCount n p m (WilsonClusterActivity.threshold β) β (by linarith) f ≤
      (8 / (2 * β + 5)) * (1 / 2 : ℝ)^(m - 1) *
        mass (2 * (2 * n)) β (by linarith) f := by
  apply slow_eigen_sum n p m hm β hβ f σ hσ
  ext u
  rw [step_full _ _ _ f hinv, heigen]
  rfl

end
end UnifiedTheory.Clay.YangMills.WilsonBridgeOutputSum
