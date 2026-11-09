/- A concrete obstruction to nontriviality of the β=0 bare candidate.
For any actual weak Wilson hierarchy limit with beta=0, vanishing positive
spacing and growing physical half-volume, fixed strict-positive-time slab tests
have exactly factorized reflected pairs. Every corresponding connected
reflected norm vanishes. Interacting or renormalized trajectories are not ruled out. -/
import UnifiedTheory.Clay.YangMills.ZeroCouplingFactorization
import UnifiedTheory.Clay.YangMills.WilsonReflectedTensor
import UnifiedTheory.Clay.YangMills.BareSchwingerCandidate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ZeroCouplingSchwingerCollapse
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 PeriodicCellSampling
open CellReflectionCovariance WilsonReflectedTensor PeriodicTimeReflection
open scoped Topology NNReal

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- Exact factorization in every actual weak limit on this β=0
trajectory, for fixed tests and any pair of insertion orders. -/
theorem limiting_reflected_pair_factorizes
    (period : ℕ → ℕ) [∀ k, NeZero (period k)] (a : ℕ → ℝ)
    (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
    (hlarge : Tendsto (fun k => (period k : ℝ) * a k) atTop atTop)
    (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : RegulatedGauge.ClassFunction G χ) (hinv : ∀ z, (χ z⁻¹).re = (χ z).re)
    (B : ℝ≥0) (hB : ∀ z, ‖χ z‖ ≤ B) (offset : ℕ → ℝ) (W : Hierarchy)
    (hW : WeakConvergence (fun k => realHierarchy G (2 * period k) (a k) plane
      χ hcχ B hB 0 (offset k)) W)
    (m l : ℕ) (f : CorrelationTest m) (h : CorrelationTest l)
    (δf Rf δh Rh : ℝ) (hδf : 0 < δf) (hδh : 0 < δh)
    (hf : ∀ x, f x ≠ 0 → ∀ j, δf ≤ point m j x 0 ∧ point m j x 0 ≤ Rf)
    (hh : ∀ x, h x ≠ 0 → ∀ j, δh ≤ point l j x 0 ∧ point l j x 0 ≤ Rh) :
    W.correlation (m+l) (reflectedTensor m l 0 plane f h) =
      star (W.correlation m f) * W.correlation l h := by
  letI : ∀ k, NeZero (2 * period k) := fun k => inferInstance
  have hp := reflected_pair_tendsto G (fun k => 2 * period k) a
    (fun k => ne_of_gt (ha k)) ha0 plane χ hcχ hχ hinv B hB (fun _ => 0) offset W hW m l f h
  have hmean (q : ℕ) (u : CorrelationTest q) :
      Tendsto (fun k => ∫ U, WilsonSmearedObservable.observable G (2 * period k)
        (a k) plane (realPartCharacter G χ) q u U
        ∂wilsonLaw (2 * period k) G (realPartCharacter G χ) 0 (offset k)) atTop
        (𝓝 (W.correlation q u)) := by
    have he (k : ℕ) := WilsonSmearedObservable.expectation_eq_hierarchy G (2 * period k)
      (a k) plane (realPartCharacter G χ) (realPart_continuous G χ hcχ)
      B (realPart_bound G χ B hB) 0 (offset k) q u
    simp_rw [he]
    exact hW q u
  have he : (fun k => ∫ U,
      star (WilsonSmearedObservable.observable G (2 * period k) (a k) plane
        (realPartCharacter G χ) m f (reflectConfiguration (2 * period k) G U)) *
      WilsonSmearedObservable.observable G (2 * period k) (a k) plane
        (realPartCharacter G χ) l h U
        ∂wilsonLaw (2 * period k) G (realPartCharacter G χ) 0 (offset k)) =ᶠ[atTop]
      (fun k => star (∫ U, WilsonSmearedObservable.observable G (2 * period k) (a k)
          plane (realPartCharacter G χ) m f U
          ∂wilsonLaw (2 * period k) G (realPartCharacter G χ) 0 (offset k)) *
        (∫ U, WilsonSmearedObservable.observable G (2 * period k) (a k)
          plane (realPartCharacter G χ) l h U
          ∂wilsonLaw (2 * period k) G (realPartCharacter G χ) 0 (offset k))) := by
    filter_upwards [InteriorCellSupport.eventually_supported period a ha ha0 hlarge
      plane m f δf Rf hδf hf,
      InteriorCellSupport.eventually_supported period a ha ha0 hlarge plane l h δh Rh hδh hh]
      with k hkf hkh
    exact ZeroCouplingFactorization.reflected_pair_factorizes G (period k) (a k) plane
      (realPartCharacter G χ) (offset k) m l f h hkf hkh
  exact tendsto_nhds_unique (hp.congr' he) ((hmean m f).star.mul (hmean l h))

/-- The connected reflected value of a fixed smeared bulk test is zero.
This contradicts a positive OS fluctuation claim on this beta=0 trajectory. -/
theorem limiting_connected_reflected_zero
    (period : ℕ → ℕ) [∀ k, NeZero (period k)] (a : ℕ → ℝ)
    (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
    (hlarge : Tendsto (fun k => (period k : ℝ) * a k) atTop atTop)
    (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : RegulatedGauge.ClassFunction G χ) (hinv : ∀ z, (χ z⁻¹).re = (χ z).re)
    (B : ℝ≥0) (hB : ∀ z, ‖χ z‖ ≤ B) (offset : ℕ → ℝ) (W : Hierarchy)
    (hW : WeakConvergence (fun k => realHierarchy G (2 * period k) (a k) plane
      χ hcχ B hB 0 (offset k)) W)
    (m : ℕ) (f : CorrelationTest m) (δ R : ℝ) (hδ : 0 < δ)
    (hf : ∀ x, f x ≠ 0 → ∀ j, δ ≤ point m j x 0 ∧ point m j x 0 ≤ R) :
    W.correlation (m+m) (reflectedTensor m m 0 plane f f) -
      star (W.correlation m f) * W.correlation m f = 0 :=
  sub_eq_zero.mpr (limiting_reflected_pair_factorizes G period a ha ha0 hlarge plane χ hcχ
    hχ hinv B hB offset W hW m m f f δ R δ R hδ hδ hf hf)

/-- Explicit fine-mesh/infinite-volume candidate subsequences inherit the
obstruction. This applies to the same W delivered by BareSchwingerCandidate
when its coupling sequence is zero; no independent limit is substituted. -/
theorem explicit_candidate_connected_zero (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (plane : Plane) (χ : G → ℂ) (hcχ : Continuous χ)
    (hχ : RegulatedGauge.ClassFunction G χ) (hinv : ∀ z, (χ z⁻¹).re = (χ z).re)
    (B : ℝ≥0) (hB : ∀ z, ‖χ z‖ ≤ B) (offset : ℕ → ℝ) (W : Hierarchy)
    (hW : WeakConvergence (fun k => realHierarchy G
      (2 * ExplicitLatticeScales.halfPeriod (phi k)) (ExplicitLatticeScales.spacing (phi k))
      plane χ hcχ B hB 0 (offset (phi k))) W)
    (m : ℕ) (f : CorrelationTest m) (δ R : ℝ) (hδ : 0 < δ)
    (hf : ∀ x, f x ≠ 0 → ∀ j, δ ≤ point m j x 0 ∧ point m j x 0 ≤ R) :
    W.correlation (m+m) (reflectedTensor m m 0 plane f f) -
      star (W.correlation m f) * W.correlation m f = 0 := by
  letI : ∀ k, NeZero (ExplicitLatticeScales.halfPeriod (phi k)) :=
    fun k => ExplicitLatticeScales.halfPeriod_ne_zero (phi k)
  exact limiting_connected_reflected_zero G
    (fun k => ExplicitLatticeScales.halfPeriod (phi k))
    (fun k => ExplicitLatticeScales.spacing (phi k))
    (fun k => ExplicitLatticeScales.spacing_pos (phi k))
    (ExplicitLatticeScales.spacing_to_zero.comp hphi.tendsto_atTop)
    (ExplicitLatticeScales.half_extent_to_infinity.comp hphi.tendsto_atTop)
    plane χ hcχ hχ hinv B hB (offset ∘ phi) W hW m f δ R hδ hf

end
end UnifiedTheory.Clay.YangMills.ZeroCouplingSchwingerCollapse
