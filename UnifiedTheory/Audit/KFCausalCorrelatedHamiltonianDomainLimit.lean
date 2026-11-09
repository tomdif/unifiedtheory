/- Forward evolution preserves the proved Hamiltonian-graph convergence
of the original finite correlated approximants. Both the states and their
Hamiltonian outputs converge. The output map acts on initial graph data;
it does not transport pure-clock momentum or assert a joint clock core. -/
import UnifiedTheory.Audit.KFCausalCorrelatedHamiltonianDomainEvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCorrelatedHamiltonianDomainLimit
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredStrongHamiltonianLimit
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalClockFloorAveragedEvolution (evolution)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (mass2 quartic vacuum : ℝ)
local notation "hb₀" => KFCausalGaussianVacuumSquare.original_strip ε h hε hb
local notation "H" => hamiltonian ε hε h hh hb₀ mass2 quartic vacuum
local notation "U" => evolution ε hε h hh hb₀ mass2 quartic vacuum
local notation "R" => KFCausalClockFloorAveragedShiftedResolvent.shiftedResolvent ε hε h hh hb₀ mass2 quartic vacuum

def outputMap (s t : ℝ) (hst : s ≤ t) : Hilbert →L[ℂ] Hilbert :=
  (KFCausalClockFloorPhysicalGraphEvolution.exists_graph_evolution
    ε hε h hh hb₀ mass2 quartic vacuum 1 s t zero_lt_one hst).choose

theorem outputMap_graph (s t : ℝ) (hst : s ≤ t) (x z : Hilbert)
    (hx : (x,z) ∈ (H s).graph) :
    (U s t x,outputMap ε hε h hh hb mass2 quartic vacuum s t hst (z+x)) ∈ (H t).graph := by
  obtain ⟨v,hvx,hvz⟩ := ((H s).mem_graph_iff).mp hx
  change (v:Hilbert) = x at hvx
  change H s v = z at hvz
  have hg := (KFCausalClockFloorPhysicalGraphEvolution.exists_graph_evolution
    ε hε h hh hb₀ mass2 quartic vacuum 1 s t zero_lt_one hst).choose_spec
      (H s v+(v:Hilbert))
  have hr := KFCausalClockFloorAveragedShiftedResolvent.shiftedResolvent_left
    ε hε h hh hb₀ mass2 quartic vacuum 1 s zero_lt_one v
  simp only [one_smul] at hr
  rw [hr] at hg
  simpa only [outputMap,hvx,hvz] using hg

variable {m : ℕ} (f : Family m) (a p : Fin m → ℝ) (ha : ∀ i, 0 < a i)
local notation "ψ" => KFCausalCorrelatedClusteredInputGraphLimit.limitingState f ε h a p hε hh ha
local notation "b" => KFCausalCorrelatedClusteredPureMomentumLimit.limitingMomentum f ε h a p hε hh ha
local notation "ψδ" => KFCausalCorrelatedClusteredInputProfiles.finiteState f ε h a p hε hh ha
local notation "bδ" => KFCausalCorrelatedClusteredPureMomentumLimit.finiteMomentum f ε h a p hε hh ha
local notation "Hψ" => inputHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum
local notation "Hb" => momentumHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum
local notation "Hψδ" => finiteInputHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum
local notation "Hbδ" => finiteMomentumHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum

theorem input_output_graph (s t : ℝ) (hst : s ≤ t) :
    (U s t ψ,outputMap ε hε h hh hb mass2 quartic vacuum s t hst (Hψ s+ψ)) ∈ (H t).graph :=
  outputMap_graph ε hε h hh hb mass2 quartic vacuum s t hst _ _
    (input_hamiltonian_graph f ε h a p hε hh ha hb mass2 quartic vacuum s)

theorem momentum_output_graph (s t : ℝ) (hst : s ≤ t) :
    (U s t b,outputMap ε hε h hh hb mass2 quartic vacuum s t hst (Hb s+b)) ∈ (H t).graph :=
  outputMap_graph ε hε h hh hb mass2 quartic vacuum s t hst _ _
    (momentum_hamiltonian_graph f ε h a p hε hh ha hb mass2 quartic vacuum s)

theorem finite_input_output_graph (s t : ℝ) (hst : s ≤ t) (δ : ℝ) (hδ : 0 < δ) :
    (U s t (ψδ δ),outputMap ε hε h hh hb mass2 quartic vacuum s t hst (Hψδ s δ+ψδ δ)) ∈ (H t).graph :=
  outputMap_graph ε hε h hh hb mass2 quartic vacuum s t hst _ _
    (finite_input_hamiltonian_graph f ε h a p hε hh ha hb mass2 quartic vacuum s δ hδ)

theorem finite_momentum_output_graph (s t : ℝ) (hst : s ≤ t) (δ : ℝ) (hδ : 0 < δ) :
    (U s t (bδ δ),outputMap ε hε h hh hb mass2 quartic vacuum s t hst (Hbδ s δ+bδ δ)) ∈ (H t).graph :=
  outputMap_graph ε hε h hh hb mass2 quartic vacuum s t hst _ _
    (finite_momentum_hamiltonian_graph f ε h a p hε hh ha hb mass2 quartic vacuum s δ hδ)

theorem input_evolved_graph_tendsto (s t : ℝ) (hst : s ≤ t) :
    Tendsto (fun δ =>
      (U s t (ψδ δ),outputMap ε hε h hh hb mass2 quartic vacuum s t hst (Hψδ s δ+ψδ δ)))
      (𝓝[>] 0) (𝓝 (U s t ψ,outputMap ε hε h hh hb mass2 quartic vacuum s t hst (Hψ s+ψ))) := by
  have hs := KFCausalCorrelatedClusteredInputGraphLimit.state_tendsto f ε h a p hε hh ha
  have hhg := inputHamiltonian_tendsto f ε h a p hε hh ha hb mass2 quartic vacuum s
  exact ((U s t).continuous.tendsto ψ |>.comp hs).prodMk_nhds
    ((outputMap ε hε h hh hb mass2 quartic vacuum s t hst).continuous.tendsto _ |>.comp (hhg.add hs))

theorem momentum_evolved_graph_tendsto (s t : ℝ) (hst : s ≤ t) :
    Tendsto (fun δ =>
      (U s t (bδ δ),outputMap ε hε h hh hb mass2 quartic vacuum s t hst (Hbδ s δ+bδ δ)))
      (𝓝[>] 0) (𝓝 (U s t b,outputMap ε hε h hh hb mass2 quartic vacuum s t hst (Hb s+b))) := by
  have hs := KFCausalCorrelatedClusteredPureMomentumLimit.momentum_tendsto f ε h a p hε hh ha
  have hhg := momentumHamiltonian_tendsto f ε h a p hε hh ha hb mass2 quartic vacuum s
  exact ((U s t).continuous.tendsto b |>.comp hs).prodMk_nhds
    ((outputMap ε hε h hh hb mass2 quartic vacuum s t hst).continuous.tendsto _ |>.comp (hhg.add hs))

#print axioms outputMap_graph
#print axioms input_output_graph
#print axioms momentum_output_graph
#print axioms finite_input_output_graph
#print axioms finite_momentum_output_graph
#print axioms input_evolved_graph_tendsto
#print axioms momentum_evolved_graph_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedHamiltonianDomainLimit
