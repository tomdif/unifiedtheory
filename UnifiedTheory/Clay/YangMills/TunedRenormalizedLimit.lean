/- One actual tuned Wilson sequence and one full reflected hierarchy limit.
The prescribed normalization is a^-4 times the real trace minus a supplied
cutoff- and coupling-dependent identity counterterm.
A positive ultraviolet endpoint and uniform renormalized seminorm bounds above
that endpoint remain explicit hypotheses. The small endpoint is constructed by
the proved Wilson tail estimate. No physical running or mass gap is asserted. -/
import UnifiedTheory.Clay.YangMills.RenormalizedFullOSLimit
import UnifiedTheory.Clay.YangMills.ProposedCouplingSelection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.TunedRenormalizedLimit
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 LocalFields WilsonCrossingKernel
open CellReflectionCovariance ReflectedWilsonRenormalization UnitaryCharacterObservables
open WilsonReflectedTensor CellSpacetimeTranslation SchwartzTranslations
open KernelHilbertCompletion UltrafilterHierarchyCompactness RenormalizedFullOSLimit
open scoped Topology NNReal

variable (d : Type*) [Fintype d] [Nonempty d] [DecidableEq d]
  (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def proposedSequence (period : ℕ → ℕ) [∀ k, NeZero (period k)] (a : ℕ → ℝ)
    (plane : Plane) (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (center : ℕ → ℝ → ℝ) (beta : ℕ → ℝ) : ℕ → Hierarchy :=
  RenormalizedWilsonUltrafilter.affineSequence G period a plane (unitaryCharacter ρ)
    (unitaryCharacter_continuous ρ hρ) beta (fun _ => Fintype.card d)
    (Fintype.card d) (fun g => unitary_trace_bound (ρ g))
    (fun k => center k (beta k)) (fun k => ((a k)^4)⁻¹)

theorem signal_one_eq_scaled (N : ℕ) [NeZero N] (a : ℝ) (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (f : CorrelationTest 1) (beta : ℝ) :
    ProposedCouplingTail.signal d G N 1 a plane ρ 1 f beta =
      ((a^4)⁻¹)^2 * (reflectedForm G N a plane (realPartCharacter G (unitaryCharacter ρ))
        (unitaryCharacter ρ) beta (Fintype.card d) f f).re := by
  simp only [ProposedCouplingTail.signal, one_pow, norm_one, one_mul]
  unfold proposedCurvatureForm
  rw [reflectedForm_affine G N a plane (realPartCharacter G (unitaryCharacter ρ))
    (realPart_continuous G _ (unitaryCharacter_continuous ρ hρ))
    (unitaryCharacter ρ) (unitaryCharacter_continuous ρ hρ)]
  simp only [Complex.star_def, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, pow_two]

/-- The selected beta(k) tends to infinity, has the prescribed positive actual
reflected signal, and supplies the very same affine hierarchy in the limit.
The positive endpoint and all-order estimates are the remaining analytic input;
neither a limiting positive kernel nor a tuning bracket is assumed. -/
theorem exists_tuned_candidate
    (period : ℕ → ℕ) [∀ k, NeZero (period k)] (a : ℕ → ℝ) (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
    (hlarge : Tendsto (fun k => (period k : ℝ) * a k) atTop atTop)
    (f : CorrelationTest 1) (hf : OSPositiveTimeKernel.Supported 1 f)
    (start : ℕ → ℝ) (hstart : Tendsto start atTop atTop)
    (target : ℝ) (htarget : 0 < target) (center : ℕ → ℝ → ℝ)
    (hsignal : ∀ k, target < ProposedCouplingTail.signal d G (2 * period k)
      1 (a k) plane ρ 1 f (start k))
    (p : ∀ m, Seminorm ℂ (CorrelationTest m)) (hp : ∀ m, Continuous (p m))
    (hbound : ∀ (k : ℕ) (b : ℝ), start k ≤ b → ∀ m (g : CorrelationTest m),
      ‖(proposedSequence d G period a plane ρ hρ center (fun _ => b) k).correlation m g‖ ≤ p m g) :
    ∃ (beta : ℕ → ℝ) (W : Hierarchy),
      (∀ k, start k < beta k) ∧ Tendsto beta atTop atTop ∧
      (∀ k, ProposedCouplingTail.signal d G (2 * period k) 1 (a k) plane ρ 1 f
        (beta k) = target) ∧
      WeakAlong (regulatorUltrafilter : Filter ℕ) (proposedSequence d G period a plane ρ hρ center beta) W ∧
      (∀ m g, ‖W.correlation m g‖ ≤ p m g) ∧
      (∀ g : CorrelationTest 0, W.correlation 0 g = ∫ x, g x) ∧
      (∀ (m : ℕ) (v : Spacetime) (g : CorrelationTest m),
        W.correlation m (translationCLM (displacement m v) g) = W.correlation m g) ∧
      ∃ hfull : FullPositiveTimeReflection.Positive W plane,
        ‖fullVacuum W plane hfull‖ = 1 ∧
        ∃ w : Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull),
          w ≠ 0 ∧ inner ℂ (fullVacuum W plane hfull) w = 0 ∧ target ≤ ‖w‖^2 := by
  obtain ⟨beta,hbeta,hs,ht⟩ := ProposedCouplingSelection.positive_endpoint_trajectory d G
    (fun k => 2 * period k) (fun _ => 1) a ha plane ρ hρ (fun _ => 1) f start hstart
    target htarget hsignal
  have hb (k m : ℕ) (g : CorrelationTest m) :
      ‖(proposedSequence d G period a plane ρ hρ center beta k).correlation m g‖ ≤ p m g :=
    hbound k (beta k) (hbeta k).le m g
  have hfloor : ∀ᶠ k in atTop, target ≤ (((a k)^4)⁻¹)^2 *
      (reflectedForm G (2 * period k) (a k) plane (realPartCharacter G (unitaryCharacter ρ))
        (unitaryCharacter ρ) (beta k) (Fintype.card d) f f).re := by
    exact Eventually.of_forall (fun k => by
      rw [← signal_one_eq_scaled d G (2 * period k) (a k) plane ρ hρ]
      exact (hs k).ge)
  obtain ⟨W,hW,hWb,hn,htrans,hfull,hvac,w,hw,ho,hwn⟩ :=
    RenormalizedFullOSLimit.exists_affine_candidate G period a plane (unitaryCharacter ρ)
      (unitaryCharacter_continuous ρ hρ) (unitaryCharacter_class ρ)
      (PeriodicPlaquetteReflection.unitaryCharacter_inverse_re G ρ) beta (fun _ => Fintype.card d) ha ha0 hlarge
      (Fintype.card d) (fun g => unitary_trace_bound (ρ g))
      (fun k => center k (beta k)) (fun k => ((a k)^4)⁻¹) p hp hb f hf target htarget hfloor
  exact ⟨beta,W,hbeta,ht,hs,hW,hWb,hn,htrans,hfull,hvac,w,hw,ho,hwn⟩

end
end UnifiedTheory.Clay.YangMills.TunedRenormalizedLimit
