/- Close the field-square step of both remaining quadratic matter
reverse actions on the actual clustered state and its clock momentum.
The subsequent ordered exponential is a separate, still required step. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredQuarticIntermediates
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredAllFactorLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredQuarticLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredQuarticIntermediates
open KFCausalCorrelatedClusteredMixedFieldLimits (input_exists_limit momentum_exists_limit)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalCorrelatedClusteredPhysicalClockLimit (shift_bound)
open KFCausalPhysicalField (physicalField physicalField_graph)
open KFCausalTransverseFieldSquare (fieldSquare fieldSquare_graph fieldSquare_selfAdjoint)
open KFCausalMatterOrderedDomain (pointField)

theorem linear_graph_of_square (u v w : Hilbert)
    (hv : (u,v) ∈ (physicalField pointField).graph)
    (hw : (u,w) ∈ (fieldSquare pointField).graph) :
    (v,w) ∈ (physicalField pointField).graph := by
  apply (physicalField_graph pointField _ _).mpr
  filter_upwards [(physicalField_graph pointField _ _).mp hv,
    (fieldSquare_graph pointField _ _).mp hw] with x hv hw
  rw [hv,hw]
  ring

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |h| ≤ Real.pi*ε/3)
local notation "hb₀" => original_strip ε h hε hb
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hy" => shift_bound ε h hb₀
local notation "U" => finiteQuartic f ε h a p hε hh ha hb
local notation "V" => finiteMomentumQuartic f ε h a p hε hh ha hb
local notation "F" => KFCausalCorrelatedClusteredAllFactorLimit.output f ε h a p hε hh hb₀ ha
local notation "G" => KFCausalCorrelatedClusteredAllFactorLimit.momentumOutput f ε h a p hε hh hb₀ ha

theorem quartic_exists_limit : ∃ v : Hilbert, Tendsto U (𝓝[>] 0) (𝓝 v) :=
  input_exists_limit f α β ε (-h/2) 0 a p 4
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε ha hy
    (by simp; positivity) (div_ne_zero (neg_ne_zero.mpr hh) (by norm_num)) U
    (finiteQuartic_coe f ε h a p hε hh ha hb)

theorem momentumQuartic_exists_limit : ∃ v : Hilbert, Tendsto V (𝓝[>] 0) (𝓝 v) :=
  momentum_exists_limit f α β ε (-h/2) 0 a p 4
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) hε ha hy
    (by simp; positivity) (div_ne_zero (neg_ne_zero.mpr hh) (by norm_num)) h V
    (finiteMomentumQuartic_coe f ε h a p hε hh ha hb)

def quartic : Hilbert := Classical.choose (quartic_exists_limit f ε h a p hε hh ha hb)
def momentumQuartic : Hilbert := Classical.choose (momentumQuartic_exists_limit f ε h a p hε hh ha hb)

theorem quartic_tendsto : Tendsto U (𝓝[>] 0) (𝓝 (quartic f ε h a p hε hh ha hb)) :=
  Classical.choose_spec (quartic_exists_limit f ε h a p hε hh ha hb)

theorem momentumQuartic_tendsto : Tendsto V (𝓝[>] 0) (𝓝 (momentumQuartic f ε h a p hε hh ha hb)) :=
  Classical.choose_spec (momentumQuartic_exists_limit f ε h a p hε hh ha hb)

theorem quartic_graph : (F 6,quartic f ε h a p hε hh ha hb) ∈ (fieldSquare pointField).graph := by
  apply (fieldSquare_selfAdjoint pointField).isClosed.mem_of_tendsto
    ((KFCausalCorrelatedClusteredAllFactorLimit.output_tendsto f ε h a p hε hh hb₀ ha 6).prodMk_nhds
      (quartic_tendsto f ε h a p hε hh ha hb))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact finite_graph f ε h a p hε hh ha hb δ hδ

theorem momentumQuartic_graph : (G 6,momentumQuartic f ε h a p hε hh ha hb) ∈ (fieldSquare pointField).graph := by
  apply (fieldSquare_selfAdjoint pointField).isClosed.mem_of_tendsto
    ((KFCausalCorrelatedClusteredAllFactorLimit.momentumOutput_tendsto f ε h a p hε hh hb₀ ha 6).prodMk_nhds
      (momentumQuartic_tendsto f ε h a p hε hh ha hb))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact finiteMomentum_graph f ε h a p hε hh ha hb δ hδ

theorem linear_intermediate_graph : (F 5,F 6) ∈ (physicalField pointField).graph :=
  linear_graph_of_square _ _ _
    (KFCausalCorrelatedClusteredPotentialGraphLimit.limit_field_graph f ε h a p hε hh hb₀ ha)
    (KFCausalCorrelatedClusteredPotentialGraphLimit.limit_square_graph f ε h a p hε hh hb₀ ha)

theorem momentum_linear_intermediate_graph : (G 5,G 6) ∈ (physicalField pointField).graph :=
  linear_graph_of_square _ _ _
    (KFCausalCorrelatedClusteredMomentumPotentialLimit.limit_field_graph f ε h a p hε hh hb₀ ha)
    (KFCausalCorrelatedClusteredMomentumPotentialLimit.limit_square_graph f ε h a p hε hh hb₀ ha)

theorem intermediate_domains : F 5 ∈ (physicalField pointField).domain ∧
    F 6 ∈ (fieldSquare pointField).domain ∧ G 5 ∈ (physicalField pointField).domain ∧
    G 6 ∈ (fieldSquare pointField).domain :=
  ⟨LinearPMap.mem_domain_of_mem_graph (linear_intermediate_graph f ε h a p hε hh ha hb),
   LinearPMap.mem_domain_of_mem_graph (quartic_graph f ε h a p hε hh ha hb),
   LinearPMap.mem_domain_of_mem_graph (momentum_linear_intermediate_graph f ε h a p hε hh ha hb),
   LinearPMap.mem_domain_of_mem_graph (momentumQuartic_graph f ε h a p hε hh ha hb)⟩

#print axioms linear_graph_of_square
#print axioms quartic_exists_limit
#print axioms momentumQuartic_exists_limit
#print axioms quartic_tendsto
#print axioms momentumQuartic_tendsto
#print axioms quartic_graph
#print axioms momentumQuartic_graph
#print axioms linear_intermediate_graph
#print axioms momentum_linear_intermediate_graph
#print axioms intermediate_domains
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredQuarticLimit
