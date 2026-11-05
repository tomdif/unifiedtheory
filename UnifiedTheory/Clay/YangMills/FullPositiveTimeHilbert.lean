/- The bounded-slab and unrestricted positive-time reflected Hilbert spaces
are unitarily equivalent. Explicit cutoff convergence proves surjectivity;
the enlargement of test labels does not postulate a different physical space. -/
import UnifiedTheory.Clay.YangMills.FullPositiveTimeReflection
import UnifiedTheory.Clay.YangMills.KernelHilbertRealization

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.FullPositiveTimeHilbert
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 PeriodicCellSampling
open WilsonReflectedTensor PositiveTimeCutoff KernelHilbertCompletion
open SchwartzConfigurationTensor SchwartzConfigurationConjugation AffineCellReflection
open scoped Topology NNReal

/-- Inclusion preserves the actual Schwartz test, forgetting only its upper bound. -/
def inclusion (i : OSPositiveTimeKernel.Label) : FullPositiveTimeReflection.Label :=
  ⟨i.1, i.2.1, by
    obtain ⟨R,hR⟩ := i.2.2
    exact fun x hx j => (hR x hx j).1⟩

/-- Every unrestricted label has a constructed sequence of bounded-slab labels. -/
def approximation (R : ℕ) (i : FullPositiveTimeReflection.Label) : OSPositiveTimeKernel.Label :=
  ⟨i.1, cutoff i.1 R i.2.1, cutoff_supported i.1 R i.2.1 i.2.2⟩

variable (W : Hierarchy) (plane : Plane)
    (hp : OSPositiveTimeKernel.Positive W plane)
    (hfull : FullPositiveTimeReflection.Positive W plane)

/-- The kernel inclusion extends through both actual null quotients/completions. -/
def embedding : Hilbert (OSPositiveTimeKernel.positiveKernel W plane hp) →ₗᵢ[ℂ]
    Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull) :=
  KernelHilbertRealization.realization (OSPositiveTimeKernel.positiveKernel W plane hp)
    (fun i => canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) (inclusion i))
    (fun i j => by rw [canonical_inner]; rfl)

@[simp] theorem embedding_canonical (i : OSPositiveTimeKernel.Label) :
    embedding W plane hp hfull (canonical (OSPositiveTimeKernel.positiveKernel W plane hp) i) =
      canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) (inclusion i) :=
  KernelHilbertRealization.realization_canonical _ _ _ i

/-- Exact sesquilinearity in the two Schwartz tests. -/
theorem reflected_difference (m : ℕ) (f g : CorrelationTest m) :
    reflectedTensor m m 0 plane (f-g) (f-g) =
      reflectedTensor m m 0 plane f f - reflectedTensor m m 0 plane f g -
        reflectedTensor m m 0 plane g f + reflectedTensor m m 0 plane g g := by
  ext x
  simp only [reflectedTensor, tensor_apply, conjugation_apply, reflectionPullback_apply,
    SchwartzMap.sub_apply, SchwartzMap.add_apply, star_sub]
  ring

theorem canonical_difference_norm_sq (m : ℕ) (f g : CorrelationTest m)
    (hf : PositiveTimeCutoff.Supported m f) (hg : PositiveTimeCutoff.Supported m g) :
    ‖canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) ⟨m,f,hf⟩ -
      canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) ⟨m,g,hg⟩‖^2 =
      (W.correlation (m+m) (reflectedTensor m m 0 plane (f-g) (f-g))).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  change (inner ℂ
    (canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) ⟨m,f,hf⟩ -
      canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) ⟨m,g,hg⟩)
    (canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) ⟨m,f,hf⟩ -
      canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) ⟨m,g,hg⟩)).re = _
  simp only [inner_sub_left, inner_sub_right, canonical_inner,
    FullPositiveTimeReflection.positiveKernel, FullPositiveTimeReflection.kernel,
    reflected_difference, map_sub, map_add, Complex.sub_re, Complex.add_re]
  ring

theorem canonical_difference_bound (B : ℝ≥0) (hb : OSPositiveTimeKernel.Bounded W B)
    (m : ℕ) (f g : CorrelationTest m)
    (hf : PositiveTimeCutoff.Supported m f) (hg : PositiveTimeCutoff.Supported m g) :
    ‖canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) ⟨m,f,hf⟩ -
      canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) ⟨m,g,hg⟩‖^2 ≤
      (B : ℝ)^(m+m) * (BoundedKernelDistribution.l1Seminorm volume (f-g))^2 := by
  rw [canonical_difference_norm_sq W plane hfull]
  apply (Complex.re_le_norm _).trans
  apply (hb (m+m) (reflectedTensor m m 0 plane (f-g) (f-g))).trans
  simp only [BoundedKernelDistribution.boundSeminorm, Seminorm.smul_apply,
    NNReal.smul_def, smul_eq_mul, NNReal.coe_pow, OSTestTranslation.l1_reflectedTensor,
    pow_two, le_refl]

/-- The cutoff labels converge in the actual reflected Hilbert norm. -/
theorem canonical_approximation_tendsto (B : ℝ≥0) (hb : OSPositiveTimeKernel.Bounded W B)
    (i : FullPositiveTimeReflection.Label) :
    Tendsto (fun R => canonical (FullPositiveTimeReflection.positiveKernel W plane hfull)
      (inclusion (approximation R i))) atTop
        (𝓝 (canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) i)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs : Tendsto (fun R => ‖canonical
      (FullPositiveTimeReflection.positiveKernel W plane hfull) (inclusion (approximation R i)) -
      canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) i‖^2) atTop (𝓝 0) := by
    apply squeeze_zero (fun R => sq_nonneg _)
      (fun R => canonical_difference_bound W plane hfull B hb i.1
        (cutoff i.1 R i.2.1) i.2.1 (inclusion (approximation R i)).2.2 i.2.2)
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using
      ((cutoff_l1_tendsto i.1 i.2.1).pow 2).const_mul ((B : ℝ)^(i.1+i.1))
  have hh := Real.continuous_sqrt.tendsto 0 |>.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hh

/-- Completeness closes the isometric image, and cutoff convergence puts every
canonical full-test vector in that image. -/
theorem embedding_surjective (B : ℝ≥0) (hb : OSPositiveTimeKernel.Bounded W B) :
    Function.Surjective (embedding W plane hp hfull) := by
  have hclosed : IsClosed (Set.range (embedding W plane hp hfull)) :=
    (embedding W plane hp hfull).isometry.isUniformInducing.isComplete_range.isClosed
  have hcanon (i : FullPositiveTimeReflection.Label) :
      canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) i ∈
        Set.range (embedding W plane hp hfull) := by
    apply hclosed.mem_of_tendsto (canonical_approximation_tendsto W plane hfull B hb i)
    exact Eventually.of_forall (fun R => ⟨canonical
      (OSPositiveTimeKernel.positiveKernel W plane hp) (approximation R i),
        embedding_canonical W plane hp hfull (approximation R i)⟩)
  intro v
  refine (denseRange_embed (FullPositiveTimeReflection.positiveKernel W plane hfull)).induction_on v hclosed ?_
  intro x
  have hspan : Submodule.span ℂ
      (Set.range (canonical (FullPositiveTimeReflection.positiveKernel W plane hfull))) ≤
        LinearMap.range (embedding W plane hp hfull).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hcanon i
  exact hspan (embed_mem_canonical_span _ x)

/-- A proved unitary identification of the existing OS state space with all
positive-time Schwartz labels, preserving each bounded-slab canonical state. -/
def equivalence (B : ℝ≥0) (hb : OSPositiveTimeKernel.Bounded W B) :
    Hilbert (OSPositiveTimeKernel.positiveKernel W plane hp) ≃ₗᵢ[ℂ]
      Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull) :=
  LinearIsometryEquiv.ofSurjective (embedding W plane hp hfull)
    (embedding_surjective W plane hp hfull B hb)

@[simp] theorem equivalence_canonical (B : ℝ≥0) (hb : OSPositiveTimeKernel.Bounded W B)
    (i : OSPositiveTimeKernel.Label) :
    equivalence W plane hp hfull B hb (canonical (OSPositiveTimeKernel.positiveKernel W plane hp) i) =
      canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) (inclusion i) :=
  embedding_canonical W plane hp hfull i

end
end UnifiedTheory.Clay.YangMills.FullPositiveTimeHilbert
