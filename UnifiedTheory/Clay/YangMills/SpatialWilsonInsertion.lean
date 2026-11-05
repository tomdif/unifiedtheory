/- Polynomial removal of an actual spatial crossing plaquette from the full
spatial Wilson weight. The omitted weight is proved reflection positive,
with all other plaquettes retained. This is a spatial slice result; passing
to a modified temporal ground marginal remains a separate obligation. -/
import UnifiedTheory.Clay.YangMills.SpatialWilsonReflectionKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SpatialWilsonInsertion
noncomputable section
open MeasureTheory WilsonTimeSlab SpatialHalfEdgeGeometry SpatialHalfEdgeSplit
open SpatialPlaquetteCutGeometry SpatialPlaquetteHalfPaths SpatialWilsonPlaquetteKernels
open SpatialWilsonReflectionKernel WilsonSingleLinkStaples
open PositiveKernelForm PositiveKernelInsertion WilsonReflectionForm

variable (n : ℕ) [NeZero n]

omit [NeZero n] in
theorem crossing_fixed (q : Plaquette n) (hq : Crossing n q) :
    reflectPlaquette n q = q := by
  apply Prod.ext
  · change (reflectLink (2 * n) (q.1,q.2.val.1)).1 = q.1
    rw [hq.1, boundary_link_fixed (2 * n) q.1 hq.2]
  · rfl

def omitted (q : Plaquette n) (s : ℝ) (p : Plaquette n) : ℝ := by
  classical
  exact if p = q then 0 else s

omit [NeZero n] in
theorem omitted_nonneg (q : Plaquette n) (s : ℝ) (hs : 0 ≤ s) (p : Plaquette n) :
    0 ≤ omitted n q s p := by
  classical
  unfold omitted
  split_ifs <;> linarith

omit [NeZero n] in
theorem omitted_reflection (q : Plaquette n) (hq : Crossing n q) (s : ℝ) (p : Plaquette n) :
    omitted n q s (reflectPlaquette n p) = omitted n q s p := by
  classical
  have he : reflectPlaquette n p = q ↔ p = q := by
    constructor
    · intro h
      have h' := congrArg (reflectPlaquette n) h
      rwa [reflectPlaquette_involutive, crossing_fixed n q hq] at h'
    · rintro rfl
      exact crossing_fixed n p hq
  simp only [omitted, he]

theorem action_restore (q : Plaquette n) (s : ℝ) (u : SpatialLinks (2 * n) Q) :
    action n (fun _ => s) u = action n (omitted n q s) u + s * defect n q u := by
  classical
  have he (p : Plaquette n) : s * defect n p u =
      omitted n q s p * defect n p u + if p = q then s * defect n q u else 0 := by
    by_cases hp : p = q <;> simp [omitted, hp]
  unfold action
  calc
    _ = ∑ p, (omitted n q s p * defect n p u +
        if p = q then s * defect n q u else 0) := Finset.sum_congr rfl (fun p _ => he p)
    _ = _ := by rw [Finset.sum_add_distrib]; simp

theorem weight_restore (q : Plaquette n) (s : ℝ) (u : SpatialLinks (2 * n) Q) :
    weight n (fun _ => s) u = weight n (omitted n q s) u * Real.exp (-s * defect n q u) := by
  unfold weight
  rw [action_restore, neg_add, Real.exp_add]
  congr 2
  ring

theorem marked_product_value (q : Plaquette n) (hq : Crossing n q) (s : ℝ) (hs : 0 ≤ s)
    (a b : Half n Q) :
    (product (positiveKernel n (omitted n q s) (omitted_nonneg n q s hs))
      (pullback (SU2CrossingHaarFloor.positiveKernel s hs) (halfPath Q n q.1 q.2.val.2))).value
        (a,b) = (weight n (fun _ => s) (assemble n Q (a,b)) : ℂ) := by
  rw [product_value, positiveKernel_value n _ _ (omitted_reflection n q hq s),
    weight_restore, Complex.ofReal_mul, crossing_factor n q hq]
  rfl

variable (μ : Measure (Half n Q)) [IsFiniteMeasure μ]

/-- The source is any continuous complex function of a half configuration.
The whole actual spatial Wilson action is retained apart from the marked
crossing. No ground-state reflection premise appears in this slice theorem. -/
theorem polynomial_removal (q : Plaquette n) (hq : Crossing n q)
    (s : ℝ) (hs : 3 / 4 ≤ s) (f : Half n Q → ℂ) (hf : Continuous f) :
    (reflectionForm μ (fun a b => weight n (omitted n q s) (assemble n Q (a,b))) f).re ≤
      SU2GaussianMass.cap s *
        (reflectionForm μ (fun a b => weight n (fun _ => s) (assemble n Q (a,b))) f).re := by
  have h0 : 0 ≤ s := by linarith
  have hi := SU2ReflectionInsertion.polynomial_removal μ
    (positiveKernel n (omitted n q s) (omitted_nonneg n q s h0))
    (positiveKernel_continuous n _ _ (omitted_reflection n q hq s))
    (halfPath Q n q.1 q.2.val.2) (halfPath_continuous Q n q.1 q.2.val.2) s hs f hf
  convert hi using 1 <;> congr 1
  · unfold form reflectionForm
    apply integral_congr_ae
    filter_upwards [] with z
    rw [positiveKernel_value n _ _ (omitted_reflection n q hq s)]
  · unfold form reflectionForm
    congr 1
    apply integral_congr_ae
    filter_upwards [] with z
    rw [marked_product_value n q hq]

omit [IsFiniteMeasure μ] in
theorem constant_source_form (γ : Plaquette n → ℝ) :
    (reflectionForm (halfHaar n Q)
      (fun a b => weight n γ (assemble n Q (a,b))) (fun _ => 1)).re =
      ∫ u, weight n γ u ∂WilsonSlabGauge.spatialHaar := by
  unfold reflectionForm
  simp only [star_one, one_mul, mul_one, integral_complex_ofReal, Complex.ofReal_re]
  exact integral_assemble n Q (weight n γ) (weight_continuous n γ)

omit [IsFiniteMeasure μ] in
/-- Actual Haar partition functions on the spatial slice obey the same
volume-independent polynomial removal price. This is not the ground marginal. -/
theorem haar_removal (q : Plaquette n) (hq : Crossing n q)
    (s : ℝ) (hs : 3 / 4 ≤ s) :
    (∫ u, weight n (omitted n q s) u ∂WilsonSlabGauge.spatialHaar) ≤
      SU2GaussianMass.cap s *
        ∫ u, weight n (fun _ => s) u ∂WilsonSlabGauge.spatialHaar := by
  have hi := polynomial_removal n (halfHaar n Q) q hq s hs (fun _ => 1) continuous_const
  rwa [constant_source_form, constant_source_form] at hi

end
end UnifiedTheory.Clay.YangMills.SpatialWilsonInsertion
