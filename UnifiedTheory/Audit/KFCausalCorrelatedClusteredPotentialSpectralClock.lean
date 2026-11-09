/- The actual three physical potential spectral endpoints lie in the
maximal pure-clock domain. Their original finite clock derivatives converge
strongly, with independent clock widths, frequencies and neutral polynomials. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredPotentialFourierIdentification
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredFourierClockGraphs
import UnifiedTheory.Audit.KFCausalNarrowFourierPureClockGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredPotentialSpectralClock
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalNarrowFourierCoordinates (mixedCoordinates)
open KFCausalNarrowFourierGeneralCoordinates (frequencyCoordinates)
open KFCausalNarrowFourierPureClockGraph
open KFCausalCorrelatedClusteredPotentialFourierIdentification
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalMixedFieldGaussianStrip (degree)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |h| ≤ Real.pi*ε/3)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hy" => le_trans (le_of_eq (abs_neg h)) hb
local notation "hz" => KFCausalCorrelatedClusteredPhysicalClockLimit.shift_bound ε h
  (KFCausalGaussianVacuumSquare.original_strip ε h hε hb)

def finiteDerivative (k : ℕ) (δ : ℝ) : Hilbert :=
  transform.symm (KFCausalCorrelatedClusteredFourierClockGraphs.finiteDerivative f α β ε (-h) (-h/2) a p k
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy hz ha h δ)

def limitingDerivative (k : ℕ) : Hilbert :=
  transform.symm (KFCausalCorrelatedClusteredFourierClockGraphs.limitingDerivative f α β ε (-h) (-h/2) a p k
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy hz ha h)

include hh in
theorem graph_of_identification (u v w : Hilbert)
    (he : mixedCoordinates u = frequencyCoordinates v)
    (hg : (v,w) ∈ (pureMomentum ε hε h).graph) :
    (u,transform.symm w) ∈ (pureMomentum ε hε h).graph := by
  have hu : transform.symm v = u := by
    apply transform.injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    apply frequencyCoordinates.injective
    rw [frequency_transform,he]
  simpa only [hu] using graph_inverse_transform ε hε h hh v w hg

theorem finite_vacuum_graph (δ : ℝ) (hδ : 0 < δ) :
    (KFCausalCorrelatedClusteredDoubleVacuumProfiles.finiteOutput f ε h a p hε hh ha hb δ,
      finiteDerivative f ε h a p hε hh ha hb 0 δ) ∈ (pureMomentum ε hε h).graph :=
  graph_of_identification ε h hε hh _ _ _ (finite_vacuum_identification f ε h a p hε hh ha hb δ hδ)
    (KFCausalCorrelatedClusteredFourierClockGraphs.finite_graph f α β ε (-h) (-h/2) a p 0
      (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy hz ha h hh δ hδ)

theorem finite_matter_graph (δ : ℝ) (hδ : 0 < δ) (j : Fin 2) :
    (KFCausalCorrelatedClusteredMatterSpectralProfiles.finiteSpectral f ε h a p hε hh ha hb δ j,
      finiteDerivative f ε h a p hε hh ha hb (degree j) δ) ∈ (pureMomentum ε hε h).graph :=
  graph_of_identification ε h hε hh _ _ _ (finite_matter_identification f ε h a p hε hh ha hb δ hδ j)
    (KFCausalCorrelatedClusteredFourierClockGraphs.finite_graph f α β ε (-h) (-h/2) a p (degree j)
      (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy hz ha h hh δ hδ)

theorem vacuum_graph :
    (KFCausalCorrelatedClusteredDoubleVacuumLimit.limitingOutput f ε h a p hε hh ha hb,
      limitingDerivative f ε h a p hε hh ha hb 0) ∈ (pureMomentum ε hε h).graph :=
  graph_of_identification ε h hε hh _ _ _ (vacuum_identification f ε h a p hε hh ha hb)
    (KFCausalCorrelatedClusteredFourierClockGraphs.limiting_graph f α β ε (-h) (-h/2) a p 0
      (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy hz ha h hh)

theorem matter_graph (j : Fin 2) :
    (KFCausalCorrelatedClusteredMatterSecondLimit.limitingSpectral f ε h a p hε hh ha hb j,
      limitingDerivative f ε h a p hε hh ha hb (degree j)) ∈ (pureMomentum ε hε h).graph :=
  graph_of_identification ε h hε hh _ _ _ (matter_identification f ε h a p hε hh ha hb j)
    (KFCausalCorrelatedClusteredFourierClockGraphs.limiting_graph f α β ε (-h) (-h/2) a p (degree j)
      (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy hz ha h hh)

theorem derivative_tendsto (k : ℕ) :
    Tendsto (finiteDerivative f ε h a p hε hh ha hb k) (𝓝[>] 0)
      (𝓝 (limitingDerivative f ε h a p hε hh ha hb k)) :=
  transform.symm.continuous.tendsto _ |>.comp
    (KFCausalCorrelatedClusteredFourierClockGraphs.finiteDerivative_tendsto f α β ε (-h) (-h/2) a p k
      (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy hz ha h)

#print axioms graph_of_identification
#print axioms finite_vacuum_graph
#print axioms finite_matter_graph
#print axioms vacuum_graph
#print axioms matter_graph
#print axioms derivative_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredPotentialSpectralClock
