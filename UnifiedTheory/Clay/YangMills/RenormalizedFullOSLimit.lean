/- State transfer from bounded-slab to unrestricted positive-time labels uses
the proved kernel isometry and needs no uniform bare L1 bound. The actual
renormalized existence package below keeps its analytic hypotheses explicit. -/
import UnifiedTheory.Clay.YangMills.RenormalizedSpacetimeTranslation
import UnifiedTheory.Clay.YangMills.FullPositiveTimeHilbert
import UnifiedTheory.Clay.YangMills.FullSchwartzReflection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.RenormalizedFullOSLimit
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 LocalFields
open KernelHilbertCompletion CellSpacetimeTranslation SchwartzTranslations
open UltrafilterHierarchyCompactness
open scoped Topology NNReal

def fullVacuum (W : Hierarchy) (plane : Plane)
    (hp : FullPositiveTimeReflection.Positive W plane) :
    Hilbert (FullPositiveTimeReflection.positiveKernel W plane hp) :=
  canonical (FullPositiveTimeReflection.positiveKernel W plane hp)
    (FullPositiveTimeHilbert.inclusion OSFactorizedCollapse.vacuumLabel)

theorem embedding_vacuum (W : Hierarchy) (plane : Plane)
    (hp : OSPositiveTimeKernel.Positive W plane)
    (hfull : FullPositiveTimeReflection.Positive W plane) :
    FullPositiveTimeHilbert.embedding W plane hp hfull (OSVacuumSector.vacuum W plane hp) =
      fullVacuum W plane hfull :=
  FullPositiveTimeHilbert.embedding_canonical W plane hp hfull OSFactorizedCollapse.vacuumLabel

theorem fullVacuum_norm (W : Hierarchy) (plane : Plane)
    (hp : OSPositiveTimeKernel.Positive W plane)
    (hfull : FullPositiveTimeReflection.Positive W plane)
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x) :
    ‖fullVacuum W plane hfull‖ = 1 := by
  rw [← embedding_vacuum W plane hp hfull,
    (FullPositiveTimeHilbert.embedding W plane hp hfull).norm_map]
  exact OSVacuumSector.vacuum_norm W plane hp hn

/-- The nonzero witness is a vector of the actual unrestricted reflected
Hilbert completion. Its norm and vacuum orthogonality are preserved exactly. -/
theorem nonzero_full_state (W : Hierarchy) (plane : Plane)
    (hp : OSPositiveTimeKernel.Positive W plane)
    (hfull : FullPositiveTimeReflection.Positive W plane)
    (v : Hilbert (OSPositiveTimeKernel.positiveKernel W plane hp))
    (hv : v ≠ 0) (ho : inner ℂ (OSVacuumSector.vacuum W plane hp) v = 0)
    (eta : ℝ) (hn : eta ≤ ‖v‖^2) :
    ∃ w : Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull),
      w ≠ 0 ∧ inner ℂ (fullVacuum W plane hfull) w = 0 ∧ eta ≤ ‖w‖^2 := by
  let e := FullPositiveTimeHilbert.embedding W plane hp hfull
  refine ⟨e v, ?_, ?_, ?_⟩
  · intro he
    apply hv
    apply e.injective
    simpa using he
  · rw [← embedding_vacuum W plane hp hfull, e.inner_map_map]
    exact ho
  · simpa only [e.norm_map] using hn

/-- One actual original-action affine Wilson limit carries normalization,
all four Euclidean translations, unrestricted positive-time reflection
positivity, and a nonzero vacuum-orthogonal full-test state. The uniform
renormalized bounds and actual positive reflected floor remain explicit
hypotheses; this does not establish physical scale selection or a mass gap. -/
theorem exists_affine_candidate
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (period : ℕ → ℕ) [∀ k, NeZero (period k)] (a : ℕ → ℝ) (plane : Plane)
    (χ : G → ℂ) (hcχ : Continuous χ) (hχ : RegulatedGauge.ClassFunction G χ)
    (hinvχ : ∀ g, (χ g⁻¹).re = (χ g).re) (beta offset : ℕ → ℝ)
    (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
    (hlarge : Tendsto (fun k => (period k : ℝ) * a k) atTop atTop)
    (C : ℝ≥0) (hC : ∀ g, ‖χ g‖ ≤ C) (center scale : ℕ → ℝ)
    (p : ∀ m, Seminorm ℂ (CorrelationTest m)) (hp : ∀ m, Continuous (p m))
    (hb : ∀ k m f, ‖(RenormalizedWilsonUltrafilter.affineSequence G period a plane
      χ hcχ beta offset C hC center scale k).correlation m f‖ ≤ p m f)
    (f : CorrelationTest 1) (hf : OSPositiveTimeKernel.Supported 1 f)
    (eta : ℝ) (heta : 0 < eta)
    (hfloor : ∀ᶠ k in atTop, eta ≤ (scale k)^2 *
      (ReflectedWilsonRenormalization.reflectedForm G (2 * period k) (a k) plane
        (CellReflectionCovariance.realPartCharacter G χ) χ (beta k) (offset k) f f).re) :
    ∃ W : Hierarchy,
      WeakAlong (regulatorUltrafilter : Filter ℕ)
        (RenormalizedWilsonUltrafilter.affineSequence G period a plane χ hcχ beta offset
          C hC center scale) W ∧
      (∀ m f, ‖W.correlation m f‖ ≤ p m f) ∧
      (∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x) ∧
      (∀ (m : ℕ) (v : Spacetime) (g : CorrelationTest m),
        W.correlation m (translationCLM (displacement m v) g) = W.correlation m g) ∧
      ∃ hfull : FullPositiveTimeReflection.Positive W plane,
        ‖fullVacuum W plane hfull‖ = 1 ∧
        ∃ w : Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull),
          w ≠ 0 ∧ inner ℂ (fullVacuum W plane hfull) w = 0 ∧ eta ≤ ‖w‖^2 := by
  obtain ⟨W,hW,hbound,hn,hpos,v,hv,ho,hlower⟩ :=
    RenormalizedWilsonUltrafilter.exists_affine_nonzero_limit G period a plane χ hcχ
      beta offset ha ha0 hlarge hχ hinvχ p hp C hC center scale hb f hf eta heta hfloor
  have ht (m : ℕ) (v : Spacetime) (g : CorrelationTest m) :
      W.correlation m (translationCLM (displacement m v) g) = W.correlation m g :=
    RenormalizedSpacetimeTranslation.limit_translation G regulatorUltrafilter
      regulatorUltrafilter_le (fun k => 2 * period k) a ha ha0 plane
      (fun k => AffineWilsonSmearing.affineCharacter χ (center k) (scale k))
      (fun k => RenormalizedWilsonHierarchy.affine_continuous G χ hcχ (center k) (scale k))
      χ hcχ (fun k => RenormalizedWilsonUltrafilter.affineBound C (center k) (scale k))
      (fun k z => RenormalizedWilsonHierarchy.affine_bound G χ C hC (center k) (scale k) z)
      beta offset p hp hb W hW m v g
  have hfull := FullSchwartzReflection.positive_of_positive W plane hpos
  exact ⟨W,hW,hbound,hn,ht,hfull,fullVacuum_norm W plane hpos hfull hn,
    nonzero_full_state W plane hpos hfull v hv ho eta hlower⟩

end
end UnifiedTheory.Clay.YangMills.RenormalizedFullOSLimit
