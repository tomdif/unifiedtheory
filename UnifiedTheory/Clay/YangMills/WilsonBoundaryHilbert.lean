/- The actual finite site-reflected Wilson Hilbert space embeds isometrically
into an explicit L2 boundary-amplitude space. This uses the proved lattice
coordinate/action identification; no transfer law is assumed. -/
import UnifiedTheory.Clay.YangMills.BoundaryAmplitudeRealization
import UnifiedTheory.Clay.YangMills.KernelHilbertRealization
import UnifiedTheory.Clay.YangMills.ReflectedWilsonKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonBoundaryHilbert
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 PeriodicHalfSplit
open PeriodicTimeReflection PeriodicSiteReflection PositiveKernelForm KernelHilbertCompletion

variable {ι : Type*} (n : ℕ) [NeZero n]
  (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def amplitudeMeasure (χ : G → ℂ) (β c : ℝ) : Measure (BoundaryConfiguration n G) :=
  BoundaryAmplitudeRealization.boundaryMeasure (boundaryMeasure n G) (halfMeasure n G)
    (boundaryWeight n G χ β c) (halfAction n G χ β c)

def boundaryAmplitude (χ : G → ℂ) (hcχ : Continuous χ) (β c : ℝ)
    (f : C(BoundaryConfiguration n G × HalfConfiguration n G, ℂ)) :
    Lp ℂ 2 (amplitudeMeasure n G χ β c) :=
  BoundaryAmplitudeRealization.amplitudeL2 (boundaryMeasure n G) (halfMeasure n G)
    (boundaryWeight n G χ β c) (boundaryWeight_continuous n G χ hcχ β c)
    (boundaryWeight_positive n G χ β c) (halfAction n G χ β c)
    (halfAction_continuous n G χ hcχ β c) f

theorem kernel_amplitude_inner (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ)
    (F : ι → BoundaryConfiguration n G × HalfConfiguration n G → ℂ)
    (hF : ∀ i, Continuous (F i)) (i j : ι) :
    inner ℂ (boundaryAmplitude n G χ hcχ β c ⟨F i, hF i⟩)
      (boundaryAmplitude n G χ hcχ β c ⟨F j, hF j⟩) =
      ReflectedWilsonKernel.kernel n G χ β c F (i, j) := by
  rw [boundaryAmplitude, boundaryAmplitude, BoundaryAmplitudeRealization.amplitudeL2_inner]
  have hR (U : Configuration (Vertex (2 * n)) G) :
      coordinates n G (reflectConfiguration (2 * n) G U) =
        BoundaryReflectionGluing.reflection (coordinates n G U) := split_reflection n G U
  unfold ReflectedWilsonKernel.kernel observable
  simp_rw [hR]
  exact ((wilsonLaw_to_boundary n G χ hcχ hχ hinv β c).integral_comp
    (coordinates n G).measurableEmbedding
    (fun z => star (BoundaryReflectionGluing.halfObservable (F i)
      (BoundaryReflectionGluing.reflection z)) * BoundaryReflectionGluing.halfObservable (F j) z)).symm

variable (χ : G → ℂ) (hcχ : Continuous χ) (hχ : ClassFunction G χ)
  (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ)
  (F : ι → BoundaryConfiguration n G × HalfConfiguration n G → ℂ)
  (hF : ∀ i, Continuous (F i))

/-- An actual isometry of the completed reflected Wilson state space. -/
def realization : Hilbert (ReflectedWilsonKernel.positiveKernel n G χ hcχ hχ hinv β c F hF)
    →ₗᵢ[ℂ] Lp ℂ 2 (amplitudeMeasure n G χ β c) :=
  KernelHilbertRealization.realization _
    (fun i => boundaryAmplitude n G χ hcχ β c ⟨F i, hF i⟩)
    (kernel_amplitude_inner n G χ hcχ hχ hinv β c F hF)

@[simp] theorem realization_canonical (i : ι) :
    realization n G χ hcχ hχ hinv β c F hF
      (canonical (ReflectedWilsonKernel.positiveKernel n G χ hcχ hχ hinv β c F hF) i) =
      boundaryAmplitude n G χ hcχ β c ⟨F i, hF i⟩ :=
  KernelHilbertRealization.realization_canonical _ _ _ i

theorem realization_injective : Function.Injective (realization n G χ hcχ hχ hinv β c F hF) :=
  (realization n G χ hcχ hχ hinv β c F hF).injective

/-- The null space is exactly the vanishing L2 boundary amplitude, including
arbitrary finite linear combinations before quotienting. -/
theorem formal_null_iff (x : Formal (ReflectedWilsonKernel.positiveKernel n G χ hcχ hχ hinv β c F hF)) :
    embed (ReflectedWilsonKernel.positiveKernel n G χ hcχ hχ hinv β c F hF) x = 0 ↔
      KernelHilbertRealization.sumMap
        (ReflectedWilsonKernel.positiveKernel n G χ hcχ hχ hinv β c F hF)
        (fun i => boundaryAmplitude n G χ hcχ β c ⟨F i, hF i⟩) x = 0 := by
  have he := KernelHilbertRealization.realization_embed
    (ReflectedWilsonKernel.positiveKernel n G χ hcχ hχ hinv β c F hF)
    (fun i => boundaryAmplitude n G χ hcχ β c ⟨F i, hF i⟩)
    (kernel_amplitude_inner n G χ hcχ hχ hinv β c F hF) x
  change realization n G χ hcχ hχ hinv β c F hF
    (embed (ReflectedWilsonKernel.positiveKernel n G χ hcχ hχ hinv β c F hF) x) = _ at he
  rw [← he]
  exact ((realization n G χ hcχ hχ hinv β c F hF).toLinearMap.map_eq_zero_iff
    (realization n G χ hcχ hχ hinv β c F hF).injective).symm

end
end UnifiedTheory.Clay.YangMills.WilsonBoundaryHilbert
