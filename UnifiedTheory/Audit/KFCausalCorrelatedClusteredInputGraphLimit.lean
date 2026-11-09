/- Original physical input states converge. Their ordered-exponential,
linear-potential and quadratic-potential graphs and zero charge survive
the clustered-width limit. Kinetic and second-action Hamiltonian graphs
are separate obligations. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredInputCauchy
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredPotentialGraphLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredInputGraphLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredInputProfiles
open KFCausalCorrelatedClusteredInputCauchy
open KFCausalCorrelatedClusteredL2Error (errorMass)
open KFCausalCorrelatedClusteredPhysicalClockLimit (lift)
open KFCausalCorrelatedClusteredPhysicalCauchy (finiteOutput potentialIndex)
open KFCausalCorrelatedClusteredPotentialGraphLimit (limitingOutput output_tendsto limit_field_graph limit_square_graph)
open KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open KFCausalClockFloorBoundedInverse (orderedExponential_closed)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalOrderedOperatorComposition (composition_graph)
open KFCausalStandingChargeOperator (zeroSector zeroSector_closed standingCharge standingCharge_zero_iff)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i)
local notation "U" => finiteState f ε h a p hε hh ha

theorem state_exists_limit : ∃ u : Hilbert, Tendsto U (𝓝[>] 0) (𝓝 u) := by
  apply KFCausalSquaredErrorCompleteness.exists_limit U
    (fun δ => 2*errorMass f (amplitudes ε a p) (KFCausalChargeGaussianGeometry.groundWidth h)
      (KFCausalClockFloorInvariantTrial.neutralWidth h) ε 0 δ)
  · simpa only [mul_zero] using (input_error_tendsto f ε h a p hε hh ha).const_mul 2
  · exact state_distance_bound f ε h a p hε hh ha

def limitingState : Hilbert := Classical.choose (state_exists_limit f ε h a p hε hh ha)

theorem state_tendsto : Tendsto U (𝓝[>] 0) (𝓝 (limitingState f ε h a p hε hh ha)) :=
  Classical.choose_spec (state_exists_limit f ε h a p hε hh ha)

local notation "u" => limitingState f ε h a p hε hh ha

theorem limitingState_zeroSector : u ∈ zeroSector h hh := by
  apply (zeroSector_closed h hh).mem_of_tendsto (state_tendsto f ε h a p hε hh ha)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  change 0 < δ at hδ
  rw [finiteState,dif_pos hδ]
  exact KFCausalReciprocalNeutralSuperposition.state_zeroSector (count f) ε h (lift f a) (widths f δ)
    (lift f p) (coefficients f δ) (sources f) (polynomials f) hε
    (fun i => ha (index f i).1) hh (widths_admissible f δ hδ.le)

theorem limitingState_charge_graph : (u,0) ∈ (standingCharge h hh).graph :=
  (standingCharge_zero_iff h hh u).mpr (limitingState_zeroSector f ε h a p hε hh ha)

variable (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "V" => limitingOutput f ε h a p hε hh hb ha

theorem finite_output_graph (δ : ℝ) (hδ : 0 < δ) (j : Fin 8) :
    (U δ,finiteOutput f ε h a p hε hh hb ha δ j) ∈
      (energyFactor ε hε h modelDirections pointField j).graph := by
  rw [finiteState,finiteOutput,dif_pos hδ,dif_pos hδ]
  exact KFCausalReciprocalNeutralSuperposition.output_graph (count f) ε h (lift f a) (widths f δ)
    (lift f p) (coefficients f δ) (sources f) (polynomials f) hε
    (fun i => ha (index f i).1) hh (widths_admissible f δ hδ.le) hb j

theorem limiting_ordered_graph : (u,V 0) ∈ (orderedExponential ε hε h).graph := by
  have hv : Tendsto (fun δ => finiteOutput f ε h a p hε hh hb ha δ 7) (𝓝[>] 0) (𝓝 (V 0)) :=
    output_tendsto f ε h a p hε hh hb ha 0
  apply (orderedExponential_closed ε hε h).mem_of_tendsto
    ((state_tendsto f ε h a p hε hh ha).prodMk_nhds hv)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact finite_output_graph f ε h a p hε hh ha hb δ hδ 7

theorem limiting_potential_graph (k : Fin 3) :
    (u,V k) ∈ (energyFactor ε hε h modelDirections pointField (potentialIndex k)).graph := by
  fin_cases k
  · exact limiting_ordered_graph f ε h a p hε hh ha hb
  · exact (composition_graph _ _ _ _).mpr ⟨V 0,limiting_ordered_graph f ε h a p hε hh ha hb,
      limit_field_graph f ε h a p hε hh hb ha⟩
  · exact (composition_graph _ _ _ _).mpr ⟨V 0,limiting_ordered_graph f ε h a p hε hh ha hb,
      limit_square_graph f ε h a p hε hh hb ha⟩

include hb in
theorem limiting_potential_domains (k : Fin 3) :
    u ∈ (energyFactor ε hε h modelDirections pointField (potentialIndex k)).domain :=
  LinearPMap.mem_domain_of_mem_graph (limiting_potential_graph f ε h a p hε hh ha hb k)

theorem potential_graph_tendsto (k : Fin 3) :
    Tendsto (fun δ => (U δ,finiteOutput f ε h a p hε hh hb ha δ (potentialIndex k)))
      (𝓝[>] 0) (𝓝 (u,V k)) :=
  (state_tendsto f ε h a p hε hh ha).prodMk_nhds (output_tendsto f ε h a p hε hh hb ha k)

theorem state_nonzero_of_output_nonzero (hv : V 0 ≠ 0) : u ≠ 0 := by
  intro hu
  exact hv ((orderedExponential ε hε h).graph_fst_eq_zero_snd (limiting_ordered_graph f ε h a p hε hh ha hb) hu)

#print axioms state_exists_limit
#print axioms state_tendsto
#print axioms limitingState_zeroSector
#print axioms limitingState_charge_graph
#print axioms finite_output_graph
#print axioms limiting_ordered_graph
#print axioms limiting_potential_graph
#print axioms limiting_potential_domains
#print axioms potential_graph_tendsto
#print axioms state_nonzero_of_output_nonzero
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredInputGraphLimit
