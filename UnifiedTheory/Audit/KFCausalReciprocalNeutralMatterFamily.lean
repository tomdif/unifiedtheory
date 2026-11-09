/- Both actual second matter actions on the full finite joint family.
Charged and clock widths, frequencies, neutral sources, amplitudes and
polynomials can vary independently. Finite linearity preserves the exact
operator graphs, including coincident widths and cancelling states. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralMatterSquare
import UnifiedTheory.Audit.KFCausalReciprocalNeutralSuperposition

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralMatterFamily
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalReciprocalNeutralSuperposition (state output output_graph)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorTrialMatter (matterFactor)
open KFCausalClockFloorMatterClosure (reversedMatterFactor)
open KFCausalPhysicalField (physicalField)
open KFCausalTransverseFieldSquare (fieldSquare)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalOrderedOperatorComposition (composition composition_graph)

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0)
  (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ Real.pi*ε/3)
local notation "hb₀" => original_strip ε h hε hb

def linearSecond : Hilbert := ∑ i,
  KFCausalReciprocalNeutralMatterSquare.linearOutput ε (a i) h (w i)
    hε (ha i) hh (hw i) hb (C i) (p i) (b i) (P i)

def quadraticSecond : Hilbert := ∑ i,
  KFCausalReciprocalNeutralMatterSquare.quadraticOutput ε (a i) h (w i)
    hε (ha i) hh (hw i) hb (C i) (p i) (b i) (P i)

theorem linear_reverse_graph :
    (output n ε h a w p C b P hε ha hh hw hb₀ 5,
      linearSecond n ε h a w p C b P hε ha hh hw hb) ∈
        (reverseFactor ε hε h modelDirections pointField 5).graph := by
  have hs := (reverseFactor ε hε h modelDirections pointField 5).graph.sum_mem
    fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalReciprocalNeutralMatterSquare.linear_reverse_graph ε (a i) h (w i)
        hε (ha i) hh (hw i) hb (C i) (p i) (b i) (P i)
  simpa only [output,linearSecond,← prod_mk_sum] using hs

theorem quadratic_reverse_graph :
    (output n ε h a w p C b P hε ha hh hw hb₀ 6,
      quadraticSecond n ε h a w p C b P hε ha hh hw hb) ∈
        (reverseFactor ε hε h modelDirections pointField 6).graph := by
  have hs := (reverseFactor ε hε h modelDirections pointField 6).graph.sum_mem
    fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalReciprocalNeutralMatterSquare.quadratic_reverse_graph ε (a i) h (w i)
        hε (ha i) hh (hw i) hb (C i) (p i) (b i) (P i)
  simpa only [output,quadraticSecond,← prod_mk_sum] using hs

theorem linear_square_graph :
    (state n ε h a w p C b P hε ha hh hw,linearSecond n ε h a w p C b P hε ha hh hw hb) ∈
      (composition (reversedMatterFactor ε hε h (physicalField pointField))
        (matterFactor ε hε h (physicalField pointField))).graph :=
  (composition_graph _ _ _ _).mpr
    ⟨_,output_graph n ε h a w p C b P hε ha hh hw hb₀ 5,
      linear_reverse_graph n ε h a w p C b P hε ha hh hw hb⟩

theorem quadratic_square_graph :
    (state n ε h a w p C b P hε ha hh hw,quadraticSecond n ε h a w p C b P hε ha hh hw hb) ∈
      (composition (reversedMatterFactor ε hε h (fieldSquare pointField))
        (matterFactor ε hε h (fieldSquare pointField))).graph :=
  (composition_graph _ _ _ _).mpr
    ⟨_,output_graph n ε h a w p C b P hε ha hh hw hb₀ 6,
      quadratic_reverse_graph n ε h a w p C b P hε ha hh hw hb⟩

#print axioms linear_reverse_graph
#print axioms quadratic_reverse_graph
#print axioms linear_square_graph
#print axioms quadratic_square_graph
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralMatterFamily
