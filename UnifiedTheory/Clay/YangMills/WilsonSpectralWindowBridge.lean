/- The physical-energy window criterion is connected to the actual original-
action affine Wilson sequence and its full OS Hamiltonian. This is a conditional
bridge: exact spectral identification, retained window mass, a trajectory and
compatible all-order bounds are inputs, not established Wilson facts. -/
import UnifiedTheory.Clay.YangMills.ContinuumSpectralWindow
import UnifiedTheory.Clay.YangMills.TunedRenormalizedDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSpectralWindowBridge
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 LocalFields
open KernelHilbertCompletion CellSpacetimeTranslation SchwartzTranslations
open UltrafilterHierarchyCompactness RenormalizedFullOSLimit ContinuumSpectralWindow
open TunedRenormalizedDynamics
open scoped Topology NNReal

/-- No positive limiting covariance or supplied OS dynamics is assumed.
The exact finite-cutoff spectral dictionary and retained window must still
be proved for the chosen physical Wilson observables and coupling sequence. -/
theorem exists_candidate_from_window
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (period : ℕ → ℕ) [∀ k, NeZero (period k)] (a : ℕ → ℝ) (plane : Plane)
    (χ : G → ℂ) (hcχ : Continuous χ) (hχ : RegulatedGauge.ClassFunction G χ)
    (hinvχ : ∀ g, (χ g⁻¹).re = (χ g).re) (beta offset : ℕ → ℝ)
    (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
    (hlarge : Tendsto (fun k => (period k : ℝ)*a k) atTop atTop)
    (C : ℝ≥0) (hC : ∀ g, ‖χ g‖ ≤ C) (center scale : ℕ → ℝ)
    (p : ∀ m, Seminorm ℂ (CorrelationTest m)) (hp : ∀ m, Continuous (p m))
    (hb : ∀ k m g, ‖(RenormalizedWilsonUltrafilter.affineSequence G period a plane
      χ hcχ beta offset C hC center scale k).correlation m g‖ ≤ p m g)
    (f : CorrelationTest 1) (hf : OSPositiveTimeKernel.Supported 1 f)
    (ν : ℕ → Measure ℝ≥0) [∀ k, IsFiniteMeasure (ν k)]
    (tau : ℝ) (htau : 0 < tau) (R : ℝ≥0) (c : ℝ) (hc : 0 < c)
    (hwindow : ∀ᶠ k in atTop, c ≤ (ν k).real (Set.Iic R))
    (hidentify : ∀ᶠ k in atTop,
      (scale k)^2 * (ReflectedWilsonRenormalization.reflectedForm G (2*period k) (a k) plane
        (CellReflectionCovariance.realPartCharacter G χ) χ (beta k) (offset k) f f).re =
      laplace (ν k) tau) :
    ∃ W : Hierarchy,
      WeakAlong (regulatorUltrafilter : Filter ℕ)
        (RenormalizedWilsonUltrafilter.affineSequence G period a plane χ hcχ beta offset
          C hC center scale) W ∧
      (∀ m g, ‖W.correlation m g‖ ≤ p m g) ∧
      (∀ g : CorrelationTest 0, W.correlation 0 g = ∫ x, g x) ∧
      (∀ (m : ℕ) (v : Spacetime) (g : CorrelationTest m),
        W.correlation m (translationCLM (displacement m v) g) = W.correlation m g) ∧
      ∃ hfull : FullPositiveTimeReflection.Positive W plane,
        ‖fullVacuum W plane hfull‖ = 1 ∧
        (∃ w : Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull),
          w ≠ 0 ∧ inner ℂ (fullVacuum W plane hfull) w = 0 ∧
            c*Real.exp (-tau*(R : ℝ)) ≤ ‖w‖^2) ∧
        HasHamiltonian W plane hfull := by
  have he : 0 < c*Real.exp (-tau*(R : ℝ)) := mul_pos hc (Real.exp_pos _)
  have hfloor : ∀ᶠ k in atTop, c*Real.exp (-tau*(R : ℝ)) ≤
      (scale k)^2 * (ReflectedWilsonRenormalization.reflectedForm G (2*period k) (a k) plane
        (CellReflectionCovariance.realPartCharacter G χ) χ (beta k) (offset k) f f).re := by
    filter_upwards [hwindow,hidentify] with k hk hi
    rw [hi]
    exact (mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le).trans
      (window_lower (ν k) tau htau.le R)
  obtain ⟨W,hW,hbW,hn,ht,hfull,hvac,hw⟩ := exists_affine_candidate G period a plane χ hcχ hχ
    hinvχ beta offset ha ha0 hlarge C hC center scale p hp hb f hf _ he hfloor
  exact ⟨W,hW,hbW,hn,ht,hfull,hvac,hw,hasHamiltonian W plane hfull (stationary W ht)⟩

end
end UnifiedTheory.Clay.YangMills.WilsonSpectralWindowBridge
