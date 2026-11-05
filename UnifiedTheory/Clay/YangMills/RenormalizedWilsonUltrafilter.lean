/- Actual renormalized Wilson extraction on one fixed regulator ultrafilter.
All orders and all Schwartz tests share the same limit; no dense test family
or sequential extraction is asserted. Actual Wilson reflection positivity and
a supplied positive connected reflected floor construct a nonzero OS state.
The regulator-uniform renormalized seminorm estimates and floor are not proved
by this extraction theorem. No physical coupling or field identification follows. -/
import UnifiedTheory.Clay.YangMills.RenormalizedOSWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.RenormalizedWilsonUltrafilter
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 CellReflectionCovariance
open WilsonReflectedTensor OSPositiveTimeKernel KernelHilbertCompletion
open UltrafilterHierarchyCompactness
open scoped Topology NNReal

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (period : ℕ → ℕ) [∀ k, NeZero (period k)] (a : ℕ → ℝ) (plane : Plane)
  (ψ : ℕ → G → ℂ) (χ : G → ℂ) (hcχ : Continuous χ)
  (B : ℕ → ℝ≥0) (hB : ∀ k g, ‖ψ k g‖ ≤ B k) (beta offset : ℕ → ℝ)
  (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
  (hlarge : Tendsto (fun k => (period k : ℝ) * a k) atTop atTop)
  (hcψ : ∀ k, Continuous (ψ k)) (hψ : ∀ k, RegulatedGauge.ClassFunction G (ψ k))
  (hinvψ : ∀ k g, (ψ k g⁻¹).re = (ψ k g).re)
  (hχ : RegulatedGauge.ClassFunction G χ) (hinvχ : ∀ g, (χ g⁻¹).re = (χ g).re)
  (p : ∀ m, Seminorm ℂ (CorrelationTest m)) (hp : ∀ m, Continuous (p m))
  (hb : ∀ k m f, ‖(RenormalizedOSWitness.sequence G period a plane ψ χ hcχ B hB
    beta offset k).correlation m f‖ ≤ p m f)

include ha ha0 hlarge hcψ hψ hinvψ hχ hinvχ hp hb in
/-- Conditional on the actual renormalized estimates, all finite polynomial
reflection forms on bounded positive-time slabs are positive in one limit. -/
theorem exists_positive_limit :
    ∃ W : Hierarchy,
      WeakAlong (regulatorUltrafilter : Filter ℕ)
        (RenormalizedOSWitness.sequence G period a plane ψ χ hcχ B hB beta offset) W ∧
      (∀ m f, ‖W.correlation m f‖ ≤ p m f) ∧
      (∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x) ∧
      OSPositiveTimeKernel.Positive W plane := by
  obtain ⟨W,hW,hbound⟩ := exists_regulator_limit
    (RenormalizedOSWitness.sequence G period a plane ψ χ hcχ B hB beta offset) p hp hb
  have hn (f : CorrelationTest 0) : W.correlation 0 f = ∫ x, f x := by
    apply tendsto_nhds_unique (hW 0 f)
    simpa only [RenormalizedOSWitness.sequence, RenormalizedWilsonHierarchy.realHierarchy,
      RenormalizedWilsonHierarchy.hierarchy_order_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∫ x, f x)
        (regulatorUltrafilter : Filter ℕ) (𝓝 (∫ x, f x)))
  exact ⟨W,hW,hbound,hn,RenormalizedOSWitness.positive G period a plane ψ χ hcχ B hB
    beta offset regulatorUltrafilter regulatorUltrafilter_le ha ha0 hcψ hψ hinvψ hχ hinvχ
    p hp hb W hW hlarge⟩

include ha ha0 hlarge hcψ hψ hinvψ hχ hinvχ hp hb in
/-- The floor is an actual centered reflected expectation in the original
Wilson law. It is not ordinary variance and is not an assumed limiting kernel. -/
theorem exists_nonzero_limit
    (f : CorrelationTest 1) (hf : OSPositiveTimeKernel.Supported 1 f)
    (eta : ℝ) (heta : 0 < eta)
    (hfloor : ∀ᶠ k in atTop, eta ≤
      (ReflectedWilsonRenormalization.reflectedForm G (2 * period k) (a k) plane
        (realPartCharacter G (ψ k)) χ (beta k) (offset k) f f).re) :
    ∃ W : Hierarchy,
      WeakAlong (regulatorUltrafilter : Filter ℕ)
        (RenormalizedOSWitness.sequence G period a plane ψ χ hcχ B hB beta offset) W ∧
      (∀ m f, ‖W.correlation m f‖ ≤ p m f) ∧
      (∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x) ∧
      ∃ hpos : OSPositiveTimeKernel.Positive W plane,
        ∃ v : Hilbert (positiveKernel W plane hpos),
          v ≠ 0 ∧ inner ℂ (OSVacuumSector.vacuum W plane hpos) v = 0 ∧ eta ≤ ‖v‖^2 := by
  obtain ⟨W,hW,hbound,hn,_⟩ := exists_positive_limit G period a plane ψ χ hcχ B hB
    beta offset ha ha0 hlarge hcψ hψ hinvψ hχ hinvχ p hp hb
  exact ⟨W,hW,hbound,hn,RenormalizedOSWitness.exists_nonzero_orthogonal G period a plane
    ψ χ hcχ B hB beta offset regulatorUltrafilter regulatorUltrafilter_le ha ha0 hcψ hψ
    hinvψ hχ hinvχ p hp hb W hW hlarge hn f hf eta heta hfloor⟩

omit [∀ k, NeZero (period k)] in
/-- Identity mixing cancels in the actual centered form, leaving exactly the
square of the prescribed real multiplicative normalization. -/
theorem affine_reflected_form (N : ℕ) [NeZero N] (a : ℝ) (plane : Plane)
    (ψ χ : G → ℂ) (hcψ : Continuous ψ) (hcχ : Continuous χ) (beta offset : ℝ)
    (center scale : ℝ) (f g : CorrelationTest 1) :
    ReflectedWilsonRenormalization.reflectedForm G N a plane
      (realPartCharacter G (AffineWilsonSmearing.affineCharacter ψ center scale))
      χ beta offset f g =
      ((scale^2 : ℝ) : ℂ) * ReflectedWilsonRenormalization.reflectedForm G N a plane
        (realPartCharacter G ψ) χ beta offset f g := by
  rw [RenormalizedWilsonHierarchy.realPart_affine,
    ReflectedWilsonRenormalization.reflectedForm_affine G N a plane
      (realPartCharacter G ψ) (realPart_continuous G ψ hcψ) χ hcχ]
  simp only [Complex.star_def, Complex.conj_ofReal, pow_two, Complex.ofReal_mul]

def affineBound (C : ℝ≥0) (center scale : ℝ) : ℝ≥0 :=
  ‖(scale : ℂ)‖₊ * (C + ‖(center : ℂ)‖₊)

def affineSequence (C : ℝ≥0) (hC : ∀ g, ‖χ g‖ ≤ C) (center scale : ℕ → ℝ) :
    ℕ → Hierarchy :=
  RenormalizedOSWitness.sequence G period a plane
    (fun k => AffineWilsonSmearing.affineCharacter χ (center k) (scale k)) χ hcχ
    (fun k => affineBound C (center k) (scale k))
    (fun k g => RenormalizedWilsonHierarchy.affine_bound G χ C hC (center k) (scale k) g)
    beta offset

include ha ha0 hlarge hχ hinvχ hp in
/-- A fully actual affine/rescaled insertion family, with the original Wilson
action retained. Uniform seminorms and the scaled reflected floor are explicit
inputs. The conclusion uses no assumed positivity, dense test family, or
physical field identification. -/
theorem exists_affine_nonzero_limit
    (C : ℝ≥0) (hC : ∀ g, ‖χ g‖ ≤ C) (center scale : ℕ → ℝ)
    (hbAffine : ∀ k m f, ‖(affineSequence G period a plane χ hcχ beta offset
      C hC center scale k).correlation m f‖ ≤ p m f)
    (f : CorrelationTest 1) (hf : OSPositiveTimeKernel.Supported 1 f)
    (eta : ℝ) (heta : 0 < eta)
    (hfloor : ∀ᶠ k in atTop, eta ≤ (scale k) ^ 2 *
      (ReflectedWilsonRenormalization.reflectedForm G (2 * period k) (a k) plane
        (realPartCharacter G χ) χ (beta k) (offset k) f f).re) :
    ∃ W : Hierarchy,
      WeakAlong (regulatorUltrafilter : Filter ℕ)
        (affineSequence G period a plane χ hcχ beta offset C hC center scale) W ∧
      (∀ m f, ‖W.correlation m f‖ ≤ p m f) ∧
      (∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x) ∧
      ∃ hpos : OSPositiveTimeKernel.Positive W plane,
        ∃ v : Hilbert (positiveKernel W plane hpos),
          v ≠ 0 ∧ inner ℂ (OSVacuumSector.vacuum W plane hpos) v = 0 ∧ eta ≤ ‖v‖^2 := by
  apply exists_nonzero_limit G period a plane
    (fun k => AffineWilsonSmearing.affineCharacter χ (center k) (scale k)) χ hcχ
    (fun k => affineBound C (center k) (scale k))
    (fun k g => RenormalizedWilsonHierarchy.affine_bound G χ C hC (center k) (scale k) g)
    beta offset ha ha0 hlarge
    (fun k => RenormalizedWilsonHierarchy.affine_continuous G χ hcχ (center k) (scale k))
    (fun k => RenormalizedWilsonHierarchy.affine_class G χ hχ (center k) (scale k))
    (fun k => RenormalizedWilsonHierarchy.affine_inverse G χ hinvχ (center k) (scale k))
    hχ hinvχ p hp hbAffine f hf eta heta
  filter_upwards [hfloor] with k hk
  rw [affine_reflected_form G _ _ plane χ χ hcχ hcχ]
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    using hk

end
end UnifiedTheory.Clay.YangMills.RenormalizedWilsonUltrafilter
