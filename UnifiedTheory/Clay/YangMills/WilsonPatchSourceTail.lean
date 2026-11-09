/- Source-sensitive simultaneous high-defect events on an aligned patch.
Their mass error is exponential in the number of distinct marked plaquettes;
the original ground law and one actual variance-loss charge are retained. -/
import UnifiedTheory.Clay.YangMills.WilsonPatchSourceDecay

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPatchSourceTail
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundHeatBath
open WilsonPhysicalVariance WilsonHighFieldDecay WilsonHighFieldReduction CompactDensityEntropy
open SpatialPlaquetteCutGeometry SpatialWilsonPatchWeights
open SpatialWilsonPlaquetteKernels (defect defect_continuous)
open WilsonPlaquetteColumnTail (rate rate_nonneg)

variable (n : ℕ) [NeZero n]

def cutoff (S : Finset (Plaquette n)) (R : ℝ) : C(Slice (2 * n), ℝ) :=
  ∏ p ∈ S, WilsonPlaquetteColumnTail.cutoff n p R

omit [NeZero n] in
theorem cutoff_range (S : Finset (Plaquette n)) (R : ℝ) (u : Slice (2 * n)) :
    cutoff n S R u ∈ Set.Icc 0 1 := by
  simp only [cutoff, ContinuousMap.prod_apply]
  exact ⟨Finset.prod_nonneg (fun p _ => (WilsonPlaquetteColumnTail.cutoff_range n p R u).1),
    Finset.prod_le_one (fun p _ => (WilsonPlaquetteColumnTail.cutoff_range n p R u).1)
      (fun p _ => (WilsonPlaquetteColumnTail.cutoff_range n p R u).2)⟩

omit [NeZero n] in
theorem cutoff_supported (S : Finset (Plaquette n)) (R : ℝ) (hR : 0 < R)
    (u : Slice (2 * n)) (hu : ∃ p ∈ S, defect n p u < R) : cutoff n S R u = 0 := by
  obtain ⟨p,hp,hu⟩ := hu
  simp only [cutoff, ContinuousMap.prod_apply]
  exact Finset.prod_eq_zero hp (WilsonPlaquetteColumnTail.cutoff_supported n p R hR u hu)

omit [NeZero n] in
theorem cutoff_one (S : Finset (Plaquette n)) (R : ℝ) (hR : 0 < R)
    (u : Slice (2 * n)) (hu : ∀ p ∈ S, 2 * R ≤ defect n p u) : cutoff n S R u = 1 := by
  simp only [cutoff, ContinuousMap.prod_apply]
  exact Finset.prod_eq_one (fun p hp => WilsonPlaquetteColumnTail.cutoff_one n p R hR u (hu p hp))

theorem cutoff_output (S : Finset (Plaquette n)) (hS : Aligned n S)
    (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (χ f : C(Slice (2 * n), ℝ))
    (hχ : ∀ u, χ u ∈ Set.Icc 0 1)
    (hs : ∀ u, (∃ p ∈ S, defect n p u < R) → χ u = 0) :
    mass (2 * n) β (by linarith) (χ * step (2 * n) β (by linarith) f) ≤
      (rate β R) ^ S.card * mass (2 * n) β (by linarith) f := by
  apply WilsonCutoffCover.cutoff_output (2 * n) β (by linarith) χ _
    (pow_nonneg (rate_nonneg β R) _) hχ _ f
  intro g hg
  exact WilsonPatchSourceDecay.intersection_decay n S hS β hβ R g
    (fun u hu => hg u (hs u hu))

theorem source_cutoff (S : Finset (Plaquette n)) (hS : Aligned n S)
    (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (χ f : C(Slice (2 * n), ℝ))
    (hχ : ∀ u, χ u ∈ Set.Icc 0 1)
    (hs : ∀ u, (∃ p ∈ S, defect n p u < R) → χ u = 0) :
    mass (2 * n) β (by linarith) (χ * f) ≤ 2 * loss (2 * n) β (by linarith) f +
      2 * (rate β R) ^ S.card * mass (2 * n) β (by linarith) f := by
  let h0 : 0 ≤ β := by linarith
  let P2 := step (2 * n) β h0 (step (2 * n) β h0 f)
  have hi := WilsonCutoffCover.mass_split (2 * n) β h0 χ f P2
  have ha := (cutoff_mass_le (2 * n) β h0 χ (f-P2) hχ).trans (residual_le_loss (2 * n) β h0 f)
  have hb := (cutoff_output n S hS β hβ R χ (step (2 * n) β h0 f) hχ hs).trans
    (mul_le_mul_of_nonneg_left (mass_step_le (2 * n) β h0 f) (pow_nonneg (rate_nonneg β R) _))
  change mass (2 * n) β h0 (χ*P2) ≤ _ at hb
  linarith

def hard (S : Finset (Plaquette n)) (R : ℝ) : Set (Slice (2 * n)) :=
  {u | ∀ p : S, 2 * R ≤ defect n p.val u}

theorem hard_measurable (S : Finset (Plaquette n)) (R : ℝ) : MeasurableSet (hard n S R) := by
  have he : hard n S R = ⋂ p : S, {u | 2 * R ≤ defect n p.val u} := by ext u; simp [hard]
  rw [he]
  exact MeasurableSet.iInter (fun p =>
    (isClosed_le continuous_const (defect_continuous n p.val)).measurableSet)

/-- A genuine joint pattern estimate. The source can concentrate on this
rare event; it is not replaced by an unweighted background probability. -/
theorem source_tail (S : Finset (Plaquette n)) (hS : Aligned n S)
    (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (hR : 0 < R) (f : C(Slice (2 * n), ℝ)) :
    (∫ u, (hard n S R).indicator (fun v => (f v) ^ 2) u ∂groundLaw (2 * n) β (by linarith)) ≤
      2 * loss (2 * n) β (by linarith) f +
        2 * (rate β R) ^ S.card * mass (2 * n) β (by linarith) f := by
  let h0 : 0 ≤ β := by linarith
  letI := groundLaw_probability (2 * n) β h0
  have hi : (∫ u, (hard n S R).indicator (fun v => (f v) ^ 2) u ∂groundLaw (2 * n) β h0) ≤
      mass (2 * n) β h0 (cutoff n S R * f) := by
    apply integral_mono
    · exact (continuous_integrable (groundLaw (2 * n) β h0) _ (f.continuous.pow 2)).indicator
        (hard_measurable n S R)
    · exact continuous_integrable (groundLaw (2 * n) β h0) _ ((cutoff n S R * f).continuous.pow 2)
    · intro u
      by_cases hu : u ∈ hard n S R
      · rw [Set.indicator_of_mem hu]
        simp only [ContinuousMap.mul_apply,
          cutoff_one n S R hR u (fun p hp => hu ⟨p,hp⟩), one_mul, le_refl]
      · rw [Set.indicator_of_notMem hu]
        exact sq_nonneg _
  exact hi.trans (source_cutoff n S hS β hβ R (cutoff n S R) f
    (cutoff_range n S R) (cutoff_supported n S R hR))

end
end UnifiedTheory.Clay.YangMills.WilsonPatchSourceTail
