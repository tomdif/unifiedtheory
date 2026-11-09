/- Actual ordered-potential outputs of pure-clock momentum converge.
Their natural graphs close at the proved limiting momentum state. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumPotentialProfiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumPotentialLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredPhysicalClockLimit (shift_bound)
open KFCausalCorrelatedClusteredPhysicalCauchy (potentialIndex)
open KFCausalCorrelatedClusteredMomentumPotentialProfiles
open KFCausalCorrelatedClusteredPureMomentumLimit (finiteMomentum limitingMomentum momentum_tendsto)
open KFCausalShiftedMomentumClockAmplitude (amplitudes amplitude_continuous amplitude_memLp)
open KFCausalCorrelatedClusteredL2Error (errorMass)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalPhysicalField (physicalField physicalField_closed)
open KFCausalTransverseFieldSquare (fieldSquare fieldSquare_selfAdjoint)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open KFCausalClockFloorBoundedInverse (orderedExponential_closed)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalClockFloorPureClockMomentum (pureMomentum)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (ha : ∀ i, 0 < a i)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "c" => amplitudes ε h a p
local notation "U" => finiteMomentumOutput f ε h a p hε hh hb ha
local notation "B" => limitingMomentum f ε h a p hε hh ha
local notation "ψ" => KFCausalCorrelatedClusteredInputGraphLimit.limitingState f ε h a p hε hh ha

theorem output_distance_bound (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) (k : Fin 3) :
    ‖U δ (potentialIndex k)-U η (potentialIndex k)‖^2 ≤
      8*errorMass f c α β ε (-h/2) δ+8*errorMass f c α β ε (-h/2) η :=
  KFCausalCorrelatedClusteredFieldTransfer.distance_bound f c α β ε (-h/2) k
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε (shift_bound ε h hb)
    (fun i => amplitude_continuous ε (a i) (p i) (-h/2) h hε (shift_bound ε h hb))
    (fun i => amplitude_memLp ε (a i) (p i) (-h/2) h hε (ha i) (shift_bound ε h hb))
    (fun δ => U δ (potentialIndex k))
    (fun δ hδ => finiteMomentumOutput_coe f ε h a p hε hh hb ha δ hδ k) δ η hδ hη

theorem output_exists_limit (k : Fin 3) :
    ∃ v : Hilbert, Tendsto (fun δ => U δ (potentialIndex k)) (𝓝[>] 0) (𝓝 v) :=
  KFCausalCorrelatedClusteredFieldTransfer.exists_limit f c α β ε (-h/2) k
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε (shift_bound ε h hb)
    (fun i => amplitude_continuous ε (a i) (p i) (-h/2) h hε (shift_bound ε h hb))
    (fun i => amplitude_memLp ε (a i) (p i) (-h/2) h hε (ha i) (shift_bound ε h hb))
    (fun δ => U δ (potentialIndex k))
    (fun δ hδ => finiteMomentumOutput_coe f ε h a p hε hh hb ha δ hδ k)

def limitingOutput (k : Fin 3) : Hilbert := Classical.choose (output_exists_limit f ε h a p hε hh hb ha k)

theorem output_tendsto (k : Fin 3) :
    Tendsto (fun δ => U δ (potentialIndex k)) (𝓝[>] 0) (𝓝 (limitingOutput f ε h a p hε hh hb ha k)) :=
  Classical.choose_spec (output_exists_limit f ε h a p hε hh hb ha k)

theorem finite_field_graph (δ : ℝ) (hδ : 0 < δ) : (U δ 7,U δ 5) ∈ (physicalField pointField).graph := by
  have hg := finiteMomentumOutput_graph f ε h a p hε hh hb ha δ hδ
  obtain ⟨Y,hY,hL⟩ := (composition_graph _ _ _ _).mp (hg 5)
  have he := (orderedExponential ε hε h).mem_graph_snd_inj' hY (hg 7) rfl
  dsimp only at he
  exact he ▸ hL

theorem finite_square_graph (δ : ℝ) (hδ : 0 < δ) : (U δ 7,U δ 6) ∈ (fieldSquare pointField).graph := by
  have hg := finiteMomentumOutput_graph f ε h a p hε hh hb ha δ hδ
  obtain ⟨Y,hY,hQ⟩ := (composition_graph _ _ _ _).mp (hg 6)
  have he := (orderedExponential ε hε h).mem_graph_snd_inj' hY (hg 7) rfl
  dsimp only at he
  exact he ▸ hQ

local notation "W" => limitingOutput f ε h a p hε hh hb ha

theorem limit_field_graph : (W 0,W 1) ∈ (physicalField pointField).graph := by
  have h0 : Tendsto (fun δ => U δ 7) (𝓝[>] 0) (𝓝 (W 0)) := output_tendsto f ε h a p hε hh hb ha 0
  have h1 : Tendsto (fun δ => U δ 5) (𝓝[>] 0) (𝓝 (W 1)) := output_tendsto f ε h a p hε hh hb ha 1
  apply (physicalField_closed pointField).mem_of_tendsto (h0.prodMk_nhds h1)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact finite_field_graph f ε h a p hε hh hb ha δ hδ

theorem limit_square_graph : (W 0,W 2) ∈ (fieldSquare pointField).graph := by
  have h0 : Tendsto (fun δ => U δ 7) (𝓝[>] 0) (𝓝 (W 0)) := output_tendsto f ε h a p hε hh hb ha 0
  have h2 : Tendsto (fun δ => U δ 6) (𝓝[>] 0) (𝓝 (W 2)) := output_tendsto f ε h a p hε hh hb ha 2
  apply (fieldSquare_selfAdjoint pointField).isClosed.mem_of_tendsto (h0.prodMk_nhds h2)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact finite_square_graph f ε h a p hε hh hb ha δ hδ

theorem limiting_ordered_graph : (B,W 0) ∈ (orderedExponential ε hε h).graph := by
  have hv : Tendsto (fun δ => U δ 7) (𝓝[>] 0) (𝓝 (W 0)) := output_tendsto f ε h a p hε hh hb ha 0
  apply (orderedExponential_closed ε hε h).mem_of_tendsto
    ((momentum_tendsto f ε h a p hε hh ha).prodMk_nhds hv)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact finiteMomentumOutput_graph f ε h a p hε hh hb ha δ hδ 7

theorem limiting_potential_graph (k : Fin 3) :
    (B,W k) ∈ (energyFactor ε hε h modelDirections pointField (potentialIndex k)).graph := by
  fin_cases k
  · exact limiting_ordered_graph f ε h a p hε hh hb ha
  · exact (composition_graph _ _ _ _).mpr ⟨W 0,limiting_ordered_graph f ε h a p hε hh hb ha,
      limit_field_graph f ε h a p hε hh hb ha⟩
  · exact (composition_graph _ _ _ _).mpr ⟨W 0,limiting_ordered_graph f ε h a p hε hh hb ha,
      limit_square_graph f ε h a p hε hh hb ha⟩

include hb in
theorem limiting_potential_domains (k : Fin 3) :
    B ∈ (energyFactor ε hε h modelDirections pointField (potentialIndex k)).domain :=
  LinearPMap.mem_domain_of_mem_graph (limiting_potential_graph f ε h a p hε hh hb ha k)

theorem composition_graph_limit (k : Fin 3) :
    (ψ,W k) ∈ (composition (energyFactor ε hε h modelDirections pointField (potentialIndex k))
      (pureMomentum ε hε h)).graph :=
  (composition_graph _ _ _ _).mpr ⟨B,
    KFCausalCorrelatedClusteredPureMomentumLimit.limiting_graph f ε h a p hε hh ha,
    limiting_potential_graph f ε h a p hε hh hb ha k⟩

include hb in
theorem composition_domain_limit (k : Fin 3) :
    ψ ∈ (composition (energyFactor ε hε h modelDirections pointField (potentialIndex k))
      (pureMomentum ε hε h)).domain :=
  LinearPMap.mem_domain_of_mem_graph (composition_graph_limit f ε h a p hε hh hb ha k)

theorem graph_tendsto (k : Fin 3) :
    Tendsto (fun δ => (finiteMomentum f ε h a p hε hh ha δ,U δ (potentialIndex k)))
      (𝓝[>] 0) (𝓝 (B,W k)) :=
  (momentum_tendsto f ε h a p hε hh ha).prodMk_nhds (output_tendsto f ε h a p hε hh hb ha k)

#print axioms output_distance_bound
#print axioms output_exists_limit
#print axioms output_tendsto
#print axioms finite_field_graph
#print axioms finite_square_graph
#print axioms limit_field_graph
#print axioms limit_square_graph
#print axioms limiting_ordered_graph
#print axioms limiting_potential_graph
#print axioms limiting_potential_domains
#print axioms composition_graph_limit
#print axioms composition_domain_limit
#print axioms graph_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredMomentumPotentialLimit
