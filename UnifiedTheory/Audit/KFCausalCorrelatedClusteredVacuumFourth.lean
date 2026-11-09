/- The actual correlated limiting state and its pure-clock momentum admit
two successive vacuum-square actions in an explicit smaller strip. Their
fourth outputs are constructed from the quadrupled exponential parameter;
no full Hamiltonian-square or Hamiltonian-evolution assertion is made. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredQuadrupleVacuumLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredVacuumFourth
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorShiftedDefect (shiftedDefect)
open KFCausalClockFloorVacuumSquare (square square_adjoint_graph)
open KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalGaussianVacuumFourth (fourthFrom fourth_graph_of_exponential full_strip)
open KFCausalCorrelatedClusteredQuadrupleVacuumLimit

def adjointSquare (ε : ℝ) (hε : 0 < ε) (h : ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  composition (orderedExponential ε hε h).adjoint (orderedExponential ε hε h)

theorem adjoint_graph_of_square_fourth (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hb : |2*h| ≤ Real.pi*ε/3) (f z : Hilbert)
    (hfz : (f,z) ∈ (composition (square ε hε h) (square ε hε h)).graph) :
    (f,z) ∈ (composition (adjointSquare ε hε h) (adjointSquare ε hε h)).graph := by
  obtain ⟨g,hg,hz⟩ := (composition_graph _ _ _ _).mp hfz
  have hp : |h| ≤ Real.pi*ε := by
    have hp0 := mul_pos Real.pi_pos hε
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)] at hb
    linarith
  exact (composition_graph _ _ _ _).mpr ⟨g,
    square_adjoint_graph ε hε h hp _ _ hg,
    square_adjoint_graph ε hε h hp _ _ hz⟩

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |2*h| ≤ Real.pi*ε/3)
local notation "ψ" => KFCausalCorrelatedClusteredInputGraphLimit.limitingState f ε h a p hε hh ha
local notation "Bψ" => KFCausalCorrelatedClusteredPureMomentumLimit.limitingMomentum f ε h a p hε hh ha
local notation "U" => KFCausalCorrelatedClusteredQuadrupleVacuumProfiles.finiteOutput f ε h a p hε hh ha hb
local notation "V" => KFCausalCorrelatedClusteredQuadrupleVacuumProfiles.finiteMomentumOutput f ε h a p hε hh ha hb

def inputFourth : Hilbert := fourthFrom ε hε h (full_strip ε h hε hb)
  (limitingOutput f ε h a p hε hh ha hb)

def momentumFourth : Hilbert := fourthFrom ε hε h (full_strip ε h hε hb)
  (limitingMomentumOutput f ε h a p hε hh ha hb)

theorem input_fourth_graph : (ψ,inputFourth f ε h a p hε hh ha hb) ∈
    (composition (square ε hε h) (square ε hε h)).graph :=
  fourth_graph_of_exponential ε hε h (full_strip ε h hε hb) ψ _
    (input_spectral_graph f ε h a p hε hh ha hb)

theorem momentum_fourth_graph : (Bψ,momentumFourth f ε h a p hε hh ha hb) ∈
    (composition (square ε hε h) (square ε hε h)).graph :=
  fourth_graph_of_exponential ε hε h (full_strip ε h hε hb) Bψ _
    (momentum_spectral_graph f ε h a p hε hh ha hb)

theorem input_adjoint_fourth_graph : (ψ,inputFourth f ε h a p hε hh ha hb) ∈
    (composition (adjointSquare ε hε h) (adjointSquare ε hε h)).graph :=
  adjoint_graph_of_square_fourth ε hε h hb _ _
    (input_fourth_graph f ε h a p hε hh ha hb)

theorem momentum_adjoint_fourth_graph : (Bψ,momentumFourth f ε h a p hε hh ha hb) ∈
    (composition (adjointSquare ε hε h) (adjointSquare ε hε h)).graph :=
  adjoint_graph_of_square_fourth ε hε h hb _ _
    (momentum_fourth_graph f ε h a p hε hh ha hb)

include hb in
theorem fourth_domains :
    ψ ∈ (composition (adjointSquare ε hε h) (adjointSquare ε hε h)).domain ∧
    Bψ ∈ (composition (adjointSquare ε hε h) (adjointSquare ε hε h)).domain :=
  ⟨LinearPMap.mem_domain_of_mem_graph (input_adjoint_fourth_graph f ε h a p hε hh ha hb),
    LinearPMap.mem_domain_of_mem_graph (momentum_adjoint_fourth_graph f ε h a p hε hh ha hb)⟩

theorem inputFourth_tendsto :
    Tendsto (fun δ => fourthFrom ε hε h (full_strip ε h hε hb) (U δ)) (𝓝[>] 0)
      (𝓝 (inputFourth f ε h a p hε hh ha hb)) := by
  have hc : Continuous (fourthFrom ε hε h (full_strip ε h hε hb)) :=
    continuous_const.smul ((inverseL ε hε).continuous.comp
      (shiftedDefect ε hε (2*h) (full_strip ε h hε hb)).continuous)
  exact (hc.tendsto _).comp (output_tendsto f ε h a p hε hh ha hb)

theorem momentumFourth_tendsto :
    Tendsto (fun δ => fourthFrom ε hε h (full_strip ε h hε hb) (V δ)) (𝓝[>] 0)
      (𝓝 (momentumFourth f ε h a p hε hh ha hb)) := by
  have hc : Continuous (fourthFrom ε hε h (full_strip ε h hε hb)) :=
    continuous_const.smul ((inverseL ε hε).continuous.comp
      (shiftedDefect ε hε (2*h) (full_strip ε h hε hb)).continuous)
  exact (hc.tendsto _).comp (momentumOutput_tendsto f ε h a p hε hh ha hb)

#print axioms adjoint_graph_of_square_fourth
#print axioms input_fourth_graph
#print axioms momentum_fourth_graph
#print axioms input_adjoint_fourth_graph
#print axioms momentum_adjoint_fourth_graph
#print axioms fourth_domains
#print axioms inputFourth_tendsto
#print axioms momentumFourth_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredVacuumFourth
