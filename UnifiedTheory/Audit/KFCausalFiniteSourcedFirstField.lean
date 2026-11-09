/- Arbitrary physical linear fields after the actual first vacuum square
of the original finite sourced family. Graph linearity retains all finite
sum cancellations. No further square or Hamiltonian domain is asserted. -/
import UnifiedTheory.Audit.KFCausalSourcedWidthFirstField
import UnifiedTheory.Audit.KFCausalFiniteSourcedMixedVacuum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalFiniteSourcedFirstField
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalPhysicalField (physicalField)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalClockFloorVacuumSquare (square)
open KFCausalPhysicalMixedCoordinates (mixedCoordinates)
open KFCausalPhysicalSpectatorGraph (symmetricPosition symmetricIndex symmetric_position_graph_iff)
open KFCausalReciprocalNeutralSuperposition (state)
open KFCausalFiniteSourcedMixedVacuum (firstOutput first_graph)
open KFCausalSingleGaussianMixedSquare (original_strip)

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i)
  (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ ε/10)
local notation "ψ" => state n ε h a w p C b P hε ha hh hw
local notation "u" => firstOutput n ε h a w p C b P hε ha hh hw hb
local notation "hb₀" => original_strip ε h hε hb

def fieldOutput (l : Transverse →L[ℝ] ℝ) : Hilbert := ∑ i,
  KFCausalSourcedWidthFirstField.fieldOutput ε h (a i) (w i) (C i) (p i) (b i) (P i)
    hε hh (ha i) (hw i) hb₀ l

theorem first_field_graph (l : Transverse →L[ℝ] ℝ) :
    (u,fieldOutput n ε h a w p C b P hε ha hh hw hb l) ∈ (physicalField l).graph := by
  have hs := (physicalField l).graph.sum_mem
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalSourcedWidthFirstField.first_field_graph ε h (a i) (w i) (C i) (p i) (b i) (P i)
        hε hh (ha i) (hw i) hb₀ l)
  simpa only [← prod_mk_sum,firstOutput,fieldOutput] using hs

theorem first_field_domain (l : Transverse →L[ℝ] ℝ) :
    u ∈ (physicalField l).domain :=
  LinearPMap.mem_domain_of_mem_graph (first_field_graph n ε h a w p C b P hε ha hh hw hb l)

theorem field_after_square_graph (l : Transverse →L[ℝ] ℝ) :
    (ψ,fieldOutput n ε h a w p C b P hε ha hh hw hb l) ∈
      (composition (physicalField l) (square ε hε h)).graph :=
  (composition_graph _ _ _ _).mpr ⟨u,first_graph n ε h a w p C b P hε ha hh hw hb,
    first_field_graph n ε h a w p C b P hε ha hh hw hb l⟩

theorem symmetric_mixed_graph (i : Fin 2) :
    mixedCoordinates (fieldOutput n ε h a w p C b P hε ha hh hw hb (symmetricPosition i)) =ᵐ[volume]
      fun z => (z.2 (symmetricIndex i) : ℂ)*(mixedCoordinates u) z :=
  (symmetric_position_graph_iff i _ _).mp
    (first_field_graph n ε h a w p C b P hε ha hh hw hb (symmetricPosition i))

#print axioms first_field_graph
#print axioms first_field_domain
#print axioms field_after_square_graph
#print axioms symmetric_mixed_graph
end
end UnifiedTheory.Audit.KFCausalFiniteSourcedFirstField
