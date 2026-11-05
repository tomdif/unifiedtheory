/- The actual conditional tuned affine Wilson limit has OS time evolution
and its maximal self-adjoint nonnegative Hamiltonian on all positive-time
Schwartz states. The positive endpoint and all-order renormalized estimates
remain analytic hypotheses; no mass gap or physical field identification is
asserted. No bare L1 bound or separately assumed dynamics is used. -/
import UnifiedTheory.Clay.YangMills.OSTemperedDynamics
import UnifiedTheory.Clay.YangMills.TunedRenormalizedLimit
import UnifiedTheory.Clay.YangMills.FullSchwartzVacuum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.TunedRenormalizedDynamics
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 LocalFields WilsonCrossingKernel
open CellReflectionCovariance ReflectedWilsonRenormalization UnitaryCharacterObservables
open WilsonReflectedTensor CellSpacetimeTranslation SchwartzTranslations
open KernelHilbertCompletion UltrafilterHierarchyCompactness RenormalizedFullOSLimit
open TunedRenormalizedLimit
open scoped Topology NNReal

theorem slab_positive (W : Hierarchy) (plane : Plane)
    (hfull : FullPositiveTimeReflection.Positive W plane) :
    OSPositiveTimeKernel.Positive W plane := by
  intro l index coeff
  exact hfull l (fun i => FullPositiveTimeHilbert.inclusion (index i)) coeff

theorem stationary (W : Hierarchy)
    (ht : ∀ (m : ℕ) (v : Spacetime) (g : CorrelationTest m),
      W.correlation m (translationCLM (displacement m v) g) = W.correlation m g) :
    OSPositiveTimeKernel.Stationary W := by
  intro m t f
  exact ht m (WithLp.toLp 2 (fun μ : Fin 4 => if μ = 0 then t else 0)) f

/-- All operators below act on the actual reflected full-test Hilbert space.
The generator relation uses the entire right-derivative domain. -/
def HasHamiltonian (W : Hierarchy) (plane : Plane)
    (hfull : FullPositiveTimeReflection.Positive W plane) : Prop :=
  ∃ (hp : OSPositiveTimeKernel.Positive W plane) (D : OSScalarDynamics.Evolution W plane hp),
    IsSelfAdjoint (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D) ∧
    Dense ((FullSchwartzHamiltonian.hamiltonian W plane hp hfull D).domain :
      Set (FullSchwartzHamiltonian.State W plane hfull)) ∧
    (∀ x : (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D).domain,
      0 ≤ (inner ℂ (x : FullSchwartzHamiltonian.State W plane hfull)
        (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D x)).re) ∧
    (fullVacuum W plane hfull,0) ∈
      (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D).graph ∧
    Nonempty (SpectralGap.ResolventWitness
      (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D) (-1)) ∧
    (∀ t (i : FullPositiveTimeReflection.Label),
      FullSchwartzDynamics.operator W plane hp hfull D t
        (canonical (FullPositiveTimeReflection.positiveKernel W plane hfull) i) =
        canonical (FullPositiveTimeReflection.positiveKernel W plane hfull)
          (FullPositiveTimeDynamics.shift t i)) ∧
    ∀ v w : FullSchwartzHamiltonian.State W plane hfull,
      HasDerivWithinAt (fun t : ℝ => FullSchwartzDynamics.operator W plane hp hfull D
        t.toNNReal v) w (Set.Ici 0) 0 ↔
        (v,-w) ∈ (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D).graph

/-- Continuity is already part of Hierarchy. Thus full reflection positivity
and actual stationarity construct the dynamics, rather than assume it. -/
theorem hasHamiltonian (W : Hierarchy) (plane : Plane)
    (hfull : FullPositiveTimeReflection.Positive W plane)
    (ht : OSPositiveTimeKernel.Stationary W) : HasHamiltonian W plane hfull := by
  let hp := slab_positive W plane hfull
  let D := OSTemperedDynamics.evolution W plane hp ht
  exact ⟨hp,D,FullSchwartzHamiltonian.selfAdjoint W plane hp hfull D,
    FullSchwartzHamiltonian.dense_domain W plane hp hfull D,
    FullSchwartzHamiltonian.nonnegative W plane hp hfull D,
    FullSchwartzVacuum.vacuum_graph W plane hp hfull D,
    ⟨FullSchwartzVacuum.negativeOneResolvent W plane hp hfull D⟩,
    FullSchwartzDynamics.operator_canonical W plane hp hfull D,
    FullSchwartzHamiltonian.derivative_iff_graph W plane hp hfull D⟩

variable (d : Type*) [Fintype d] [Nonempty d] [DecidableEq d]
  (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- The very same tuned original-action affine Wilson sequence, ultrafilter
limit, and nonzero reflected state now carry the constructed OS Hamiltonian.
The two unproved quantitative inputs are retained without strengthening them. -/
theorem exists_tuned_dynamics
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
      WeakAlong (regulatorUltrafilter : Filter ℕ)
        (proposedSequence d G period a plane ρ hρ center beta) W ∧
      (∀ m g, ‖W.correlation m g‖ ≤ p m g) ∧
      (∀ g : CorrelationTest 0, W.correlation 0 g = ∫ x, g x) ∧
      (∀ (m : ℕ) (v : Spacetime) (g : CorrelationTest m),
        W.correlation m (translationCLM (displacement m v) g) = W.correlation m g) ∧
      ∃ hfull : FullPositiveTimeReflection.Positive W plane,
        ‖fullVacuum W plane hfull‖ = 1 ∧
        (∃ w : Hilbert (FullPositiveTimeReflection.positiveKernel W plane hfull),
          w ≠ 0 ∧ inner ℂ (fullVacuum W plane hfull) w = 0 ∧ target ≤ ‖w‖^2) ∧
        HasHamiltonian W plane hfull := by
  obtain ⟨beta,W,hbeta,hbt,hs,hW,hb,hn,ht,hfull,hvac,hw⟩ :=
    exists_tuned_candidate d G period a plane ρ hρ ha ha0 hlarge f hf start hstart
      target htarget center hsignal p hp hbound
  exact ⟨beta,W,hbeta,hbt,hs,hW,hb,hn,ht,hfull,hvac,hw,
    hasHamiltonian W plane hfull (stationary W ht)⟩

end
end UnifiedTheory.Clay.YangMills.TunedRenormalizedDynamics
