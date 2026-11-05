/- Transport of hard measurable events under actual link rotations.
The original ground density is retained. The estimate uses its proved
small-rotation comparison and applies to source squares, not background
probability alone. -/
import UnifiedTheory.Clay.YangMills.WilsonGroundSmallRotation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonGroundEventTransport
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonTimeSlab WilsonGroundLocalComparison
open WilsonGroundHeatBath WilsonSymmetricLinkChange WilsonGroundSmallRotation
open CompactDensityEntropy
open scoped Quaternion

variable (n : ℕ) [NeZero n]

theorem shifted_event_integral (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (E : Set (Slice n)) (f : C(Slice n, ℝ)) :
    (∫ u, E.indicator (fun v => (f (shift n e q v))^2) u ∂groundLaw n β hβ) =
      ∫ u, ((shift n e q⁻¹) ⁻¹' E).indicator
        (fun v => (ground n β hβ (shift n e q⁻¹ v))^2 * (f v)^2) u ∂measure n := by
  rw [groundLaw, GroundStateDirichlet.stationary_integral _ _ (ground n β hβ).continuous]
  have he := shift_integral n e q (fun u => (ground n β hβ (shift n e q⁻¹ u))^2 *
    E.indicator (fun v => (f (shift n e q v))^2) (shift n e q⁻¹ u))
  simp only [shift_inverse] at he
  rw [he]
  apply integral_congr_ae
  filter_upwards [] with u
  have hc : shift n e q (shift n e q⁻¹ u) = u := by
    simpa only [inv_inv] using shift_inverse n e q⁻¹ u
  by_cases hu : shift n e q⁻¹ u ∈ E
  · rw [Set.indicator_of_mem hu,
      Set.indicator_of_mem (show u ∈ (shift n e q⁻¹) ⁻¹' E from hu), hc]
  · rw [Set.indicator_of_notMem hu,
      Set.indicator_of_notMem (show u ∉ (shift n e q⁻¹) ⁻¹' E from hu), mul_zero]

/-- Event transport keeps the source square and costs only the local ground-density ratio. -/
theorem shifted_square_le (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (E F : Set (Slice n))
    (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hshift : ∀ u, u ∈ E → shift n e q u ∈ F) (f : C(Slice n, ℝ)) :
    (∫ u, E.indicator (fun v => (f (shift n e q v))^2) u ∂groundLaw n β hβ) ≤
      Real.exp (36 * β * ‖(q : ℍ) - 1‖) *
        ∫ u, F.indicator (fun v => (f v)^2) u ∂groundLaw n β hβ := by
  rw [shifted_event_integral, groundLaw,
    GroundStateDirichlet.stationary_integral _ _ (ground n β hβ).continuous]
  have he : (fun u => (ground n β hβ u)^2 * F.indicator (fun v => (f v)^2) u) =
      F.indicator (fun u => (ground n β hβ u)^2 * (f u)^2) := by
    funext u
    by_cases hu : u ∈ F
    · simp only [Set.indicator_of_mem hu]
    · simp only [Set.indicator_of_notMem hu, mul_zero]
  rw [he, ← integral_const_mul]
  apply integral_mono
    ((continuous_integrable (measure n) _
      ((((ground n β hβ).continuous.comp (shift_continuous n e q⁻¹)).pow 2).mul
        (f.continuous.pow 2))).indicator (hE.preimage (shift_continuous n e q⁻¹).measurable))
    (((continuous_integrable (measure n) _
      (((ground n β hβ).continuous.pow 2).mul (f.continuous.pow 2))).indicator hF).const_mul _)
  intro u
  dsimp only [Pi.mul_apply, Function.comp_apply]
  by_cases hu : shift n e q⁻¹ u ∈ E
  · have hc : shift n e q (shift n e q⁻¹ u) = u := by
      simpa only [inv_inv] using shift_inverse n e q⁻¹ u
    have hFu : u ∈ F := by simpa only [hc] using hshift (shift n e q⁻¹ u) hu
    rw [Set.indicator_of_mem (show u ∈ (shift n e q⁻¹) ⁻¹' E from hu),
      Set.indicator_of_mem hFu]
    have h := ground_square_shift n β hβ e q⁻¹ u
    rw [inverse_distance] at h
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h (sq_nonneg (f u))
  · rw [Set.indicator_of_notMem (show u ∉ (shift n e q⁻¹) ⁻¹' E from hu)]
    exact mul_nonneg (Real.exp_pos _).le
      (Set.indicator_nonneg (fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) u)

theorem square_mono (β : ℝ) (hβ : 0 ≤ β) (E F : Set (Slice n))
    (hE : MeasurableSet E) (hF : MeasurableSet F) (hEF : E ⊆ F) (f : C(Slice n, ℝ)) :
    (∫ u, E.indicator (fun v => (f v)^2) u ∂groundLaw n β hβ) ≤
      ∫ u, F.indicator (fun v => (f v)^2) u ∂groundLaw n β hβ := by
  letI := groundLaw_probability n β hβ
  have hi := continuous_integrable (groundLaw n β hβ) _ (f.continuous.pow 2)
  apply integral_mono (hi.indicator hE) (hi.indicator hF)
  intro u
  by_cases hu : u ∈ E
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (hEF hu)]
  · rw [Set.indicator_of_notMem hu]
    exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) u

/-- A restricted finite-difference response is bounded by the enlarged event's source mass. -/
theorem difference_le (β : ℝ) (hβ : 0 ≤ β)
    (e : SpatialVertex n × Fin 3) (q : Q) (E F : Set (Slice n))
    (hE : MeasurableSet E) (hF : MeasurableSet F) (hEF : E ⊆ F)
    (hshift : ∀ u, u ∈ E → shift n e q u ∈ F) (f : C(Slice n, ℝ)) :
    (∫ u, E.indicator (fun v => (f (shift n e q v) - f v)^2) u ∂groundLaw n β hβ) ≤
      2 * (Real.exp (36 * β * ‖(q : ℍ) - 1‖) + 1) *
        ∫ u, F.indicator (fun v => (f v)^2) u ∂groundLaw n β hβ := by
  letI := groundLaw_probability n β hβ
  have h0 := continuous_integrable (groundLaw n β hβ) _ (f.continuous.pow 2)
  have h1 := continuous_integrable (groundLaw n β hβ) _
    ((f.continuous.comp (shift_continuous n e q)).pow 2)
  have hd := continuous_integrable (groundLaw n β hβ) _
    (((f.continuous.comp (shift_continuous n e q)).sub f.continuous).pow 2)
  have hi := integral_mono (hd.indicator hE)
    (((h1.indicator hE).const_mul 2).add ((h0.indicator hE).const_mul 2)) (fun u => by
      by_cases hu : u ∈ E
      · simp only [Set.indicator_of_mem hu, Pi.add_apply, Function.comp_apply]
        nlinarith [sq_nonneg (f (shift n e q u) + f u)]
      · simp only [Set.indicator_of_notMem hu, Pi.add_apply, mul_zero, add_zero, le_refl])
  simp only [Pi.add_apply] at hi
  rw [integral_add ((h1.indicator hE).const_mul 2) ((h0.indicator hE).const_mul 2),
    integral_const_mul, integral_const_mul] at hi
  simp only [Function.comp_apply] at hi
  have hs := shifted_square_le n β hβ e q E F hE hF hshift f
  have hm := square_mono n β hβ E F hE hF hEF f
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonGroundEventTransport
