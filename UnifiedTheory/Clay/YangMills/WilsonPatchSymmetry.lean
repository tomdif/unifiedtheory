/- Simultaneous patch and defect-count estimates transported through exact
symmetries of the original ground law. Concrete translations and coordinate
permutations cover every position and orientation of the reflection plane. -/
import UnifiedTheory.Clay.YangMills.WilsonPatchCountTail
import UnifiedTheory.Clay.YangMills.WilsonSpatialRotations

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPatchSymmetry
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator
open WilsonGroundLocalComparison WilsonGroundHeatBath
open WilsonPhysicalVariance WilsonHighFieldDecay WilsonRawSymmetry WilsonSpatialRotations
open SpatialPlaquetteCutGeometry SpatialWilsonPatchWeights
open WilsonPlaquetteColumnTail (rate)

variable (n : ℕ) [NeZero n]

theorem law_integral (T : Symmetry n) (β : ℝ) (hβ : 0 ≤ β) (F : Slice n → ℝ) :
    (∫ u, F (T.map u) ∂groundLaw n β hβ) = ∫ u, F u ∂groundLaw n β hβ := by
  rw [groundLaw, GroundStateDirichlet.stationary_integral _ _ (ground n β hβ).continuous,
    GroundStateDirichlet.stationary_integral _ _ (ground n β hβ).continuous]
  have h := integral_pull n T (fun u => (ground n β hβ u) ^ 2 * F u)
  simpa only [ground_invariant] using h

/-- The original source is pulled with the event; no unweighted probability replaces it. -/
theorem event_integral (T : Symmetry n) (β : ℝ) (hβ : 0 ≤ β)
    (E : Set (Slice n)) (f : C(Slice n, ℝ)) :
    (∫ u, (T.map ⁻¹' E).indicator (fun v => (f v) ^ 2) u ∂groundLaw n β hβ) =
      ∫ u, E.indicator (fun v => (pull n (inverse n T) f v) ^ 2) u ∂groundLaw n β hβ := by
  rw [← law_integral n T β hβ (fun u =>
    E.indicator (fun v => (pull n (inverse n T) f v) ^ 2) u)]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hu : T.map u ∈ E
  · rw [Set.indicator_of_mem (s := T.map ⁻¹' E) hu, Set.indicator_of_mem hu]
    simp only [pull, inverse, ContinuousMap.coe_mk, MeasurableEquiv.symm_apply_apply]
  · rw [Set.indicator_of_notMem (s := T.map ⁻¹' E) hu, Set.indicator_of_notMem hu]

theorem patch_tail (T : Symmetry (2 * n)) (A : Finset (Plaquette n)) (hA : Aligned n A)
    (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (hR : 0 < R) (f : C(Slice (2 * n), ℝ)) :
    (∫ u, (T.map ⁻¹' WilsonPatchSourceTail.hard n A R).indicator (fun v => (f v) ^ 2) u
      ∂groundLaw (2 * n) β (by linarith)) ≤ 2 * loss (2 * n) β (by linarith) f +
        2 * (rate β R) ^ A.card * mass (2 * n) β (by linarith) f := by
  rw [event_integral]
  have h := WilsonPatchSourceTail.source_tail n A hA β hβ R hR
    (pull (2 * n) (inverse (2 * n) T) f)
  simpa only [loss_pull, mass_pull] using h

theorem count_tail (T : Symmetry (2 * n)) (A : Finset (Plaquette n)) (hA : Aligned n A)
    (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (hR : 0 < R) (k : ℕ) (f : C(Slice (2 * n), ℝ)) :
    (∫ u, (T.map ⁻¹' WilsonPatchCountTail.event n A R k).indicator (fun v => (f v) ^ 2) u
      ∂groundLaw (2 * n) β (by linarith)) ≤ 2 * loss (2 * n) β (by linarith) f +
        2 * (A.card.choose k : ℝ) * (rate β R) ^ k * mass (2 * n) β (by linarith) f := by
  rw [event_integral]
  have h := WilsonPatchCountTail.binomial_tail n A hA β hβ R hR k
    (pull (2 * n) (inverse (2 * n) T) f)
  simpa only [loss_pull, mass_pull] using h

theorem count_decay (T : Symmetry (2 * n)) (A : Finset (Plaquette n)) (hA : Aligned n A)
    (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (hR : 0 < R) (k : ℕ) (f : C(Slice (2 * n), ℝ))
    (hs : ∀ u, T.map u ∉ WilsonPatchCountTail.event n A R k → f u = 0) :
    mass (2 * n) β (by linarith) (step (2 * n) β (by linarith) f) ≤
      (A.card.choose k : ℝ) * (rate β R) ^ k * mass (2 * n) β (by linarith) f := by
  have h := WilsonPatchCountTail.binomial_decay n A hA β hβ R hR k
    (pull (2 * n) (inverse (2 * n) T) f) (by
      intro u hu
      exact hs (T.map.symm u) (by simpa only [T.map.apply_symm_apply] using hu))
  simpa only [step_pull, mass_pull] using h

theorem intersection_decay (T : Symmetry (2 * n)) (A : Finset (Plaquette n))
    (hA : Aligned n A) (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (f : C(Slice (2 * n), ℝ))
    (hs : ∀ u, (∃ p ∈ A, SpatialWilsonPlaquetteKernels.defect n p (T.map u) < R) → f u = 0) :
    mass (2 * n) β (by linarith) (step (2 * n) β (by linarith) f) ≤
      (rate β R) ^ A.card * mass (2 * n) β (by linarith) f := by
  have h := WilsonPatchSourceDecay.intersection_decay n A hA β hβ R
    (pull (2 * n) (inverse (2 * n) T) f) (by
      intro u hu
      exact hs (T.map.symm u) (by simpa only [T.map.apply_symm_apply] using hu))
  simpa only [step_pull, mass_pull] using h

theorem cutoff_output (T : Symmetry (2 * n)) (A : Finset (Plaquette n))
    (hA : Aligned n A) (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (χ f : C(Slice (2 * n), ℝ))
    (hχ : ∀ u, χ u ∈ Set.Icc 0 1)
    (hs : ∀ u, (∃ p ∈ A, SpatialWilsonPlaquetteKernels.defect n p (T.map u) < R) → χ u = 0) :
    mass (2 * n) β (by linarith) (χ * step (2 * n) β (by linarith) f) ≤
      (rate β R) ^ A.card * mass (2 * n) β (by linarith) f := by
  apply WilsonCutoffCover.cutoff_output (2 * n) β (by linarith) χ _
    (pow_nonneg (WilsonPlaquetteColumnTail.rate_nonneg β R) _) hχ _ f
  intro g hg
  exact intersection_decay n T A hA β hβ R g (fun u hu => hg u (hs u hu))

def affine (σ : Equiv.Perm (Fin 3)) (s : SpatialVertex (2 * n)) : Symmetry (2 * n) :=
  composition (2 * n) (translation (2 * n) s) (rotation (2 * n) σ)

/-- The transported defect is literally the plaquette at the translated,
permuted vertex and directions. Inverse orientations have the same real trace. -/
theorem affine_defect (σ : Equiv.Perm (Fin 3)) (s : SpatialVertex (2 * n))
    (p : Plaquette n) (u : Slice (2 * n)) :
    SpatialWilsonPlaquetteKernels.defect n p ((affine n σ s).map u) =
      orientedDefect (2 * n) u (vertexEquiv (2 * n) σ p.1 + s) (σ p.2.val.1) (σ p.2.val.2) := by
  change (2 - (WilsonSingleLinkStaples.character (spatialHolonomy
    (rotationEquiv (2 * n) σ (WilsonGroundTranslation.sliceEquiv (2 * n) s u))
    p.1 p.2.val.1 p.2.val.2)).re) = _
  rw [rotationEquiv_apply, WilsonGroundTranslation.sliceEquiv_apply,
    holonomy_rotate, WilsonGroundTranslation.spatialHolonomy_shift]
  rfl

end
end UnifiedTheory.Clay.YangMills.WilsonPatchSymmetry
