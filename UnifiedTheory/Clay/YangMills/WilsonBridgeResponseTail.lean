/- Summed local response energy on actual bad-bridge events. Small fixed
link rotations are transported under the original ground law, retaining
the source and an explicit threshold allowance. Transfer outputs and slow
physical eigenfunctions have a volume-independent small response tail.
The complementary retained-field response is not estimated here. -/
import UnifiedTheory.Clay.YangMills.WilsonGroundEventTransport
import UnifiedTheory.Clay.YangMills.WilsonBridgeRotationStability
import UnifiedTheory.Clay.YangMills.WilsonCollectiveGram

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonBridgeResponseTail
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonTimeSlab WilsonGroundHeatBath
open WilsonPhysicalVariance WilsonHighFieldDecay WilsonBridgeOutputSum
open WilsonSymmetricLinkChange WilsonBridgeRotationStability
open SpatialPlaquetteCutGeometry WilsonGroundSlabEnergy WilsonClusterSourceDecay
open WilsonConnectedActivity
open scoped Quaternion

variable (n : ℕ) [NeZero n]

/-- A fixed root, all distant target plaquettes, and one fixed link rotation per target. -/
def response (p : Plaquette (2 * n)) (m : ℕ) (R β : ℝ) (hβ : 0 ≤ β)
    (edges : Plaquette (2 * n) → SpatialVertex (2 * (2 * n)) × Fin 3)
    (rotations : Plaquette (2 * n) → Q) (f : C(Slice (2 * (2 * n)), ℝ)) : ℝ :=
  ∑ z, ∫ u, (farEvent n p z m R).indicator
    (fun v => (f (shift (2 * (2 * n)) (edges z) (rotations z) v) - f v)^2) u
      ∂groundLaw (2 * (2 * n)) β hβ

theorem response_nonneg (p : Plaquette (2 * n)) (m : ℕ) (R β : ℝ) (hβ : 0 ≤ β)
    (edges : Plaquette (2 * n) → SpatialVertex (2 * (2 * n)) × Fin 3)
    (rotations : Plaquette (2 * n) → Q) (f : C(Slice (2 * (2 * n)), ℝ)) :
    0 ≤ response n p m R β hβ edges rotations f :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg
    (fun u => Set.indicator_nonneg (fun _ _ => sq_nonneg _) u))

/-- No invariance of the event or the ground density is assumed. Both changes are controlled. -/
theorem response_le_count (p : Plaquette (2 * n)) (m : ℕ) (R r β : ℝ) (hβ : 0 ≤ β)
    (hr : 0 ≤ r) (edges : Plaquette (2 * n) → SpatialVertex (2 * (2 * n)) × Fin 3)
    (rotations : Plaquette (2 * n) → Q)
    (hrot : ∀ z, ‖(rotations z : ℍ) - 1‖ ≤ r) (f : C(Slice (2 * (2 * n)), ℝ)) :
    response n p m (R + 4 * r) β hβ edges rotations f ≤
      2 * (Real.exp (36 * β * r) + 1) * weightedCount n p m R β hβ f := by
  unfold response weightedCount
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  have h := WilsonGroundEventTransport.difference_le (2 * (2 * n)) β hβ (edges z)
    (rotations z) (farEvent n p z m (R + 4 * r)) (farEvent n p z m R)
    (farEvent_measurable n p z m (R + 4 * r)) (farEvent_measurable n p z m R)
    (farEvent_mono n p z m R (R + 4 * r) (by linarith))
    (farEvent_shift n p z m R r (edges z) (rotations z) (hrot z)) f
  apply h.trans
  have he : Real.exp (36 * β * ‖(rotations z : ℍ) - 1‖) ≤ Real.exp (36 * β * r) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hrot z) (by positivity))
  exact mul_le_mul_of_nonneg_right (by linarith)
    (integral_nonneg (fun u => Set.indicator_nonneg (fun _ _ => sq_nonneg _) u))

/-- A bound on actual transfer response, restricted only in the displayed integration event. -/
theorem output_response (p : Plaquette (2 * n)) (m : ℕ) (hm : 0 < m)
    (β : ℝ) (hβ : 0 < β) (R r : ℝ) (hmargin : 96 * envelope β ≤ R) (hR : 0 < R)
    (hr : 0 ≤ r) (hsmall : 512 * rate β R < 1)
    (edges : Plaquette (2 * n) → SpatialVertex (2 * (2 * n)) × Fin 3)
    (rotations : Plaquette (2 * n) → Q) (hrot : ∀ z, ‖(rotations z : ℍ) - 1‖ ≤ r)
    (f : C(Slice (2 * (2 * n)), ℝ)) :
    response n p m (R + 4 * r) β hβ.le edges rotations (step (2 * (2 * n)) β hβ.le f) ≤
      (2 * (Real.exp (36 * β * r) + 1) * budget (2 * rate β R) m) *
        mass (2 * (2 * n)) β hβ.le f := by
  apply (response_le_count n p m R r β hβ.le hr edges rotations hrot _).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (output_sum n p m hm β hβ R hmargin hR hsmall f)
    (by positivity : 0 ≤ 2 * (Real.exp (36 * β * r) + 1))

/-- The threshold allowance still tends to zero and the rotation cost is an absolute constant. -/
theorem weak_output_response (p : Plaquette (2 * n)) (m : ℕ) (hm : 0 < m)
    (β : ℝ) (hβ : 512 ≤ β)
    (edges : Plaquette (2 * n) → SpatialVertex (2 * (2 * n)) × Fin 3)
    (rotations : Plaquette (2 * n) → Q)
    (hrot : ∀ z, ‖(rotations z : ℍ) - 1‖ ≤ (36 * β)⁻¹)
    (f : C(Slice (2 * (2 * n)), ℝ)) :
    response n p m (bufferedThreshold β) β (by linarith) edges rotations
      (step (2 * (2 * n)) β (by linarith) f) ≤
      (8 * (Real.exp 1 + 1) / (2 * β + 5)) * (1 / 2 : ℝ)^(m - 1) *
        mass (2 * (2 * n)) β (by linarith) f := by
  have hb : 0 < β := by linarith
  have h := response_le_count n p m (WilsonClusterActivity.threshold β) (36 * β)⁻¹
    β hb.le (by positivity) edges rotations hrot (step (2 * (2 * n)) β hb.le f)
  rw [mul_inv_cancel₀ (by positivity : 36 * β ≠ 0)] at h
  have hs := mul_le_mul_of_nonneg_left (weak_output_sum n p m hm β hβ f)
    (by positivity : 0 ≤ 2 * (Real.exp 1 + 1))
  change response n p m (bufferedThreshold β) β hb.le edges rotations _ ≤ _ at h
  apply (h.trans hs).trans_eq
  ring

/-- Exact slow eigenfunctions inherit a small bad-bridge response, with no summed residual. -/
theorem slow_eigen_response (p : Plaquette (2 * n)) (m : ℕ) (hm : 0 < m)
    (β : ℝ) (hβ : 512 ≤ β)
    (edges : Plaquette (2 * n) → SpatialVertex (2 * (2 * n)) × Fin 3)
    (rotations : Plaquette (2 * n) → Q)
    (hrot : ∀ z, ‖(rotations z : ℍ) - 1‖ ≤ (36 * β)⁻¹)
    (f : C(Slice (2 * (2 * n)), ℝ)) (σ : ℝ) (hσ : 1 / 2 ≤ σ ^ 2)
    (heigen : step (2 * (2 * n)) β (by linarith) f = σ • f) :
    response n p m (bufferedThreshold β) β (by linarith) edges rotations f ≤
      (16 * (Real.exp 1 + 1) / (2 * β + 5)) * (1 / 2 : ℝ)^(m - 1) *
        mass (2 * (2 * n)) β (by linarith) f := by
  have hb : 0 < β := by linarith
  have h := response_le_count n p m (WilsonClusterActivity.threshold β) (36 * β)⁻¹
    β hb.le (by positivity) edges rotations hrot f
  rw [mul_inv_cancel₀ (by positivity : 36 * β ≠ 0)] at h
  have hs := mul_le_mul_of_nonneg_left (slow_eigen_sum n p m hm β hβ f σ hσ heigen)
    (by positivity : 0 ≤ 2 * (Real.exp 1 + 1))
  change response n p m (bufferedThreshold β) β hb.le edges rotations f ≤ _ at h
  apply (h.trans hs).trans_eq
  ring

/-- The responding observable is the full original physical transfer on invariant sources. -/
theorem physical_output_response (p : Plaquette (2 * n)) (m : ℕ) (hm : 0 < m)
    (β : ℝ) (hβ : 512 ≤ β)
    (edges : Plaquette (2 * n) → SpatialVertex (2 * (2 * n)) × Fin 3)
    (rotations : Plaquette (2 * n) → Q)
    (hrot : ∀ z, ‖(rotations z : ℍ) - 1‖ ≤ (36 * β)⁻¹)
    (f : C(Slice (2 * (2 * n)), ℝ)) (hinv : ∀ h u, f (gaugeSlice h u) = f u) :
    (∑ z, ∫ u, (farEvent n p z m (bufferedThreshold β)).indicator (fun w =>
      ((∫ v, WilsonGroundLocalComparison.transition (2 * (2 * n)) β (by linarith)
        (shift (2 * (2 * n)) (edges z) (rotations z) w) v * f v ∂measure (2 * (2 * n))) -
       (∫ v, WilsonGroundLocalComparison.transition (2 * (2 * n)) β (by linarith)
        w v * f v ∂measure (2 * (2 * n))))^2) u
      ∂groundLaw (2 * (2 * n)) β (by linarith)) ≤
      (8 * (Real.exp 1 + 1) / (2 * β + 5)) * (1 / 2 : ℝ)^(m - 1) *
        mass (2 * (2 * n)) β (by linarith) f := by
  simpa only [response, step_full _ _ _ f hinv] using
    weak_output_response n p m hm β hβ edges rotations hrot f

/-- No raw/full identification is made without the physical invariance hypothesis. -/
theorem physical_slow_eigen_response (p : Plaquette (2 * n)) (m : ℕ) (hm : 0 < m)
    (β : ℝ) (hβ : 512 ≤ β)
    (edges : Plaquette (2 * n) → SpatialVertex (2 * (2 * n)) × Fin 3)
    (rotations : Plaquette (2 * n) → Q)
    (hrot : ∀ z, ‖(rotations z : ℍ) - 1‖ ≤ (36 * β)⁻¹)
    (f : C(Slice (2 * (2 * n)), ℝ)) (σ : ℝ)
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) (hσ : 1 / 2 ≤ σ ^ 2)
    (heigen : ∀ u, (∫ v, WilsonGroundLocalComparison.transition (2 * (2 * n)) β
      (by linarith) u v * f v ∂measure (2 * (2 * n))) = σ * f u) :
    response n p m (bufferedThreshold β) β (by linarith) edges rotations f ≤
      (16 * (Real.exp 1 + 1) / (2 * β + 5)) * (1 / 2 : ℝ)^(m - 1) *
        mass (2 * (2 * n)) β (by linarith) f := by
  apply slow_eigen_response n p m hm β hβ edges rotations hrot f σ hσ
  ext u
  rw [step_full _ _ _ f hinv, heigen]
  rfl

/-- The complement excludes only the indicated bad bridge, not every defective plaquette. -/
def complement (p : Plaquette (2 * n)) (m : ℕ) (R β : ℝ) (hβ : 0 ≤ β)
    (edges : Plaquette (2 * n) → SpatialVertex (2 * (2 * n)) × Fin 3)
    (rotations : Plaquette (2 * n) → Q) (f : C(Slice (2 * (2 * n)), ℝ)) : ℝ :=
  ∑ z, ∫ u, (farEvent n p z m R)ᶜ.indicator
    (fun v => (f (shift (2 * (2 * n)) (edges z) (rotations z) v) - f v)^2) u
      ∂groundLaw (2 * (2 * n)) β hβ

/-- This is an exact split of the previously constructed collective response energy. -/
theorem energy_split (p : Plaquette (2 * n)) (m : ℕ) (R β : ℝ) (hβ : 0 ≤ β)
    (edges : Plaquette (2 * n) → SpatialVertex (2 * (2 * n)) × Fin 3)
    (rotations : Plaquette (2 * n) → Q) (f : C(Slice (2 * (2 * n)), ℝ)) :
    WilsonCollectiveGram.energy (2 * (2 * n)) β hβ edges rotations (fun _ => 1) f =
      complement n p m R β hβ edges rotations f + response n p m R β hβ edges rotations f := by
  letI := groundLaw_probability (2 * (2 * n)) β hβ
  unfold WilsonCollectiveGram.energy complement response responseEnergy
  simp only [one_pow, one_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  have hi := CompactDensityEntropy.continuous_integrable (groundLaw (2 * (2 * n)) β hβ) _
    (((f.continuous.comp (shift_continuous (2 * (2 * n)) (edges z) (rotations z))).sub
      f.continuous).pow 2)
  have hE := farEvent_measurable n p z m R
  simp only [Function.comp_apply] at hi
  rw [← integral_add (hi.indicator hE.compl) (hi.indicator hE)]
  apply integral_congr_ae
  filter_upwards [] with u
  by_cases hu : u ∈ farEvent n p z m R
  · simp only [Set.indicator_of_mem hu, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hu),
      zero_add]
  · simp only [Set.indicator_of_notMem hu, Set.indicator_of_mem (Set.mem_compl hu), add_zero]

end
end UnifiedTheory.Clay.YangMills.WilsonBridgeResponseTail
