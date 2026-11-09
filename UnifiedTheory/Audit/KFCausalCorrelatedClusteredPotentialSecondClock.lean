/- The three retained potential second actions have actual pure-clock
graphs and convergent original finite derivatives. The bounded inverse
half-clock commutator is included explicitly. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredPotentialSpectralClock
import UnifiedTheory.Audit.KFCausalClockFloorPureClockInverseHalf
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredFiniteSecondPureClock

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredPotentialSecondClock
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorInverseHalfTransportOperator (driftOperator)
open KFCausalClockFloorPureClockInverseHalf (inverse_momentum_drift)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalMixedFieldGaussianStrip (degree)
open KFCausalReciprocalNeutralMatterSpectral (matterIndex)
open KFCausalCorrelatedClusteredOriginalKineticSeconds (finiteSeconds)
open KFCausalCorrelatedClusteredFiniteSecondPureClock (finiteDerivative finite_derivative_graph)

def inverseDerivative (ε h : ℝ) (hε : 0 < ε) (u v : Hilbert) : Hilbert :=
  inverseL ε hε v+(-Complex.I*(h:ℂ)) • driftOperator ε hε u

theorem inverseDerivative_tendsto (ε h : ℝ) (hε : 0 < ε) (u v : ℝ → Hilbert) (u₀ v₀ : Hilbert)
    (hu : Tendsto u (𝓝[>] 0) (𝓝 u₀)) (hv : Tendsto v (𝓝[>] 0) (𝓝 v₀)) :
    Tendsto (fun δ => inverseDerivative ε h hε (u δ) (v δ)) (𝓝[>] 0)
      (𝓝 (inverseDerivative ε h hε u₀ v₀)) :=
  ((inverseL ε hε).continuous.tendsto _ |>.comp hv).add
    (tendsto_const_nhds.smul ((driftOperator ε hε).continuous.tendsto _ |>.comp hu))

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |h| ≤ Real.pi*ε/3)
local notation "D" => KFCausalCorrelatedClusteredPotentialSpectralClock.finiteDerivative f ε h a p hε hh ha hb
local notation "d" => KFCausalCorrelatedClusteredPotentialSpectralClock.limitingDerivative f ε h a p hε hh ha hb
local notation "B" => pureMomentum ε hε h

def finiteMatterDerivative (j : Fin 2) (δ : ℝ) : Hilbert := inverseDerivative ε h hε
  (KFCausalCorrelatedClusteredMatterSpectralProfiles.finiteSpectral f ε h a p hε hh ha hb δ j) (D (degree j) δ)
def matterDerivative (j : Fin 2) : Hilbert := inverseDerivative ε h hε
  (KFCausalCorrelatedClusteredMatterSecondLimit.limitingSpectral f ε h a p hε hh ha hb j) (d (degree j))
def finiteVacuumDerivative (δ : ℝ) : Hilbert := inverseDerivative ε h hε
  (KFCausalCorrelatedClusteredDoubleVacuumProfiles.finiteOutput f ε h a p hε hh ha hb δ) (D 0 δ)
def vacuumDerivative : Hilbert := inverseDerivative ε h hε
  (KFCausalCorrelatedClusteredDoubleVacuumLimit.limitingOutput f ε h a p hε hh ha hb) (d 0)

theorem finite_matter_graph (δ : ℝ) (hδ : 0 < δ) (j : Fin 2) :
    (finiteSeconds f ε h a p hε hh ha hb δ (matterIndex j),finiteMatterDerivative f ε h a p hε hh ha hb j δ) ∈ (B).graph := by
  rw [KFCausalCorrelatedClusteredMatterSpectralProfiles.finiteSeconds_eq f ε h a p hε hh ha hb δ hδ j]
  exact inverse_momentum_drift ε hε h hh _ _
    (KFCausalCorrelatedClusteredPotentialSpectralClock.finite_matter_graph f ε h a p hε hh ha hb δ hδ j)

theorem finite_vacuum_graph (δ : ℝ) (hδ : 0 < δ) :
    (finiteSeconds f ε h a p hε hh ha hb δ 7,finiteVacuumDerivative f ε h a p hε hh ha hb δ) ∈ (B).graph := by
  rw [KFCausalCorrelatedClusteredVacuumSecondLimit.finiteSeconds_eq f ε h a p hε hh ha hb δ hδ]
  exact inverse_momentum_drift ε hε h hh _ _
    (KFCausalCorrelatedClusteredPotentialSpectralClock.finite_vacuum_graph f ε h a p hε hh ha hb δ hδ)

theorem matter_graph (j : Fin 2) :
    (KFCausalCorrelatedClusteredMatterSecondLimit.second f ε h a p hε hh ha hb j,
      matterDerivative f ε h a p hε hh ha hb j) ∈ (B).graph :=
  inverse_momentum_drift ε hε h hh _ _
    (KFCausalCorrelatedClusteredPotentialSpectralClock.matter_graph f ε h a p hε hh ha hb j)

theorem vacuum_graph :
    (KFCausalCorrelatedClusteredVacuumSecondLimit.inputSecond f ε h a p hε hh ha hb,
      vacuumDerivative f ε h a p hε hh ha hb) ∈ (B).graph :=
  inverse_momentum_drift ε hε h hh _ _
    (KFCausalCorrelatedClusteredPotentialSpectralClock.vacuum_graph f ε h a p hε hh ha hb)

theorem finite_matter_identification (δ : ℝ) (hδ : 0 < δ) (j : Fin 2) :
    finiteDerivative f ε h a p hε hh ha hb δ (matterIndex j) = finiteMatterDerivative f ε h a p hε hh ha hb j δ :=
  (B).mem_graph_snd_inj' (finite_derivative_graph f ε h a p hε hh ha hb δ hδ (matterIndex j))
    (finite_matter_graph f ε h a p hε hh ha hb δ hδ j) rfl

theorem finite_vacuum_identification (δ : ℝ) (hδ : 0 < δ) :
    finiteDerivative f ε h a p hε hh ha hb δ 7 = finiteVacuumDerivative f ε h a p hε hh ha hb δ :=
  (B).mem_graph_snd_inj' (finite_derivative_graph f ε h a p hε hh ha hb δ hδ 7)
    (finite_vacuum_graph f ε h a p hε hh ha hb δ hδ) rfl

theorem matter_derivative_tendsto (j : Fin 2) :
    Tendsto (fun δ => finiteDerivative f ε h a p hε hh ha hb δ (matterIndex j)) (𝓝[>] 0)
      (𝓝 (matterDerivative f ε h a p hε hh ha hb j)) := by
  apply Tendsto.congr' _ (inverseDerivative_tendsto ε h hε _ _ _ _
    (KFCausalCorrelatedClusteredMatterSecondLimit.spectral_tendsto f ε h a p hε hh ha hb j)
    (KFCausalCorrelatedClusteredPotentialSpectralClock.derivative_tendsto f ε h a p hε hh ha hb (degree j)))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (finite_matter_identification f ε h a p hε hh ha hb δ hδ j).symm

theorem vacuum_derivative_tendsto :
    Tendsto (fun δ => finiteDerivative f ε h a p hε hh ha hb δ 7) (𝓝[>] 0)
      (𝓝 (vacuumDerivative f ε h a p hε hh ha hb)) := by
  apply Tendsto.congr' _ (inverseDerivative_tendsto ε h hε _ _ _ _
    (KFCausalCorrelatedClusteredDoubleVacuumLimit.output_tendsto f ε h a p hε hh ha hb)
    (KFCausalCorrelatedClusteredPotentialSpectralClock.derivative_tendsto f ε h a p hε hh ha hb 0))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (finite_vacuum_identification f ε h a p hε hh ha hb δ hδ).symm

#print axioms inverseDerivative_tendsto
#print axioms finite_matter_graph
#print axioms finite_vacuum_graph
#print axioms matter_graph
#print axioms vacuum_graph
#print axioms finite_matter_identification
#print axioms finite_vacuum_identification
#print axioms matter_derivative_tendsto
#print axioms vacuum_derivative_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredPotentialSecondClock
