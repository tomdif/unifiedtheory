/- The bounded-slab and full positive-time Hilbert spaces coincide for every
continuous reflected hierarchy. Schwartz cutoff convergence replaces the bare
L1 bound used in the earlier unitary equivalence. -/
import UnifiedTheory.Clay.YangMills.FullSchwartzReflection
import UnifiedTheory.Clay.YangMills.FullPositiveTimeHilbert

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.FullSchwartzHilbert
noncomputable section
open Filter ContinuumControl PeriodicLattice4 KernelHilbertCompletion
open FullPositiveTimeHilbert WilsonReflectedTensor
open scoped Topology NNReal

def approximation (R : ℕ) (i : FullPositiveTimeReflection.Label) : OSPositiveTimeKernel.Label :=
  ⟨i.1, FullSchwartzReflection.cutoff i.1 R i.2.1,
    FullSchwartzReflection.cutoff_supported i.1 R i.2.1 i.2.2⟩

variable (W : Hierarchy) (plane : Plane)
  (hp : OSPositiveTimeKernel.Positive W plane)
  (hfull : FullPositiveTimeReflection.Positive W plane)

/-- Full Schwartz convergence of the actual tests gives Hilbert-norm
convergence, without requiring a special correlation seminorm. -/
theorem canonical_tendsto {ι : Type*} {l : Filter ι} (m : ℕ)
    (u : ι → CorrelationTest m) (f : CorrelationTest m)
    (hu : ∀ r, PositiveTimeCutoff.Supported m (u r))
    (hf : PositiveTimeCutoff.Supported m f) (ht : Tendsto u l (𝓝 f)) :
    Tendsto (fun r => canonical (FullPositiveTimeReflection.positiveKernel W plane hfull)
      ⟨m,u r,hu r⟩) l
      (𝓝 (canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) ⟨m,f,hf⟩)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hd : Tendsto (fun r => u r - f) l (𝓝 0) := by
    simpa only [sub_self] using ht.sub_const f
  have hz : reflectedTensor m m 0 plane (0 : CorrelationTest m) 0 = 0 := by
    ext x
    simp [reflectedTensor, SchwartzConfigurationTensor.tensor_apply]
  have hs : Tendsto (fun r => ‖canonical
      (FullPositiveTimeReflection.positiveKernel W plane hfull) ⟨m,u r,hu r⟩ -
      canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) ⟨m,f,hf⟩‖^2) l (𝓝 0) := by
    have hh := ((Complex.continuous_re.comp
      (W.correlation (m+m)).continuous).continuousAt.tendsto).comp
      (SchwartzTensorContinuity.reflected_tensor_tendsto m m 0 plane _ _ 0 0 hd hd)
    simpa only [canonical_difference_norm_sq W plane hfull, Function.comp_def,
      hz, map_zero, Complex.zero_re] using hh
  have hh := Real.continuous_sqrt.tendsto 0 |>.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero] using hh

theorem canonical_approximation_tendsto (i : FullPositiveTimeReflection.Label) :
    Tendsto (fun R => canonical (FullPositiveTimeReflection.positiveKernel W plane hfull)
      (inclusion (approximation R i))) atTop
      (𝓝 (canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) i)) :=
  canonical_tendsto W plane hfull i.1 _ i.2.1
    (fun R => (inclusion (approximation R i)).2.2) i.2.2
    (SchwartzCutoffDensity.cutoff_tendsto (Configuration i.1) i.2.1)

theorem embedding_surjective :
    Function.Surjective (embedding W plane hp hfull) := by
  have hclosed : IsClosed (Set.range (embedding W plane hp hfull)) :=
    (embedding W plane hp hfull).isometry.isUniformInducing.isComplete_range.isClosed
  have hcanon (i : FullPositiveTimeReflection.Label) :
      canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) i ∈
        Set.range (embedding W plane hp hfull) := by
    apply hclosed.mem_of_tendsto (canonical_approximation_tendsto W plane hfull i)
    exact Eventually.of_forall (fun R => ⟨canonical
      (OSPositiveTimeKernel.positiveKernel W plane hp) (approximation R i),
        embedding_canonical W plane hp hfull (approximation R i)⟩)
  intro v
  refine (denseRange_embed (FullPositiveTimeReflection.positiveKernel W plane hfull)).induction_on
    v hclosed ?_
  intro x
  have hspan : Submodule.span ℂ
      (Set.range (canonical (FullPositiveTimeReflection.positiveKernel W plane hfull))) ≤
        LinearMap.range (embedding W plane hp hfull).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hcanon i
  exact hspan (embed_mem_canonical_span _ x)

def equivalence :
    Hilbert (OSPositiveTimeKernel.positiveKernel W plane hp) ≃ₗᵢ[ℂ]
      Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull) :=
  LinearIsometryEquiv.ofSurjective (embedding W plane hp hfull)
    (embedding_surjective W plane hp hfull)

@[simp] theorem equivalence_canonical (i : OSPositiveTimeKernel.Label) :
    equivalence W plane hp hfull (canonical (OSPositiveTimeKernel.positiveKernel W plane hp) i) =
      canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) (inclusion i) :=
  embedding_canonical W plane hp hfull i

end
end UnifiedTheory.Clay.YangMills.FullSchwartzHilbert
