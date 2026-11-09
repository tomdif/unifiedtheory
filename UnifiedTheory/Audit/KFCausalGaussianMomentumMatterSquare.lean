/- Constructed natural matter-square graphs for the actual clock momentum
of the physical Gaussian. The bounded analytic coefficient theorem supplies
the second exponential action; no Hamiltonian-domain premise is used. -/
import UnifiedTheory.Audit.KFCausalGaussianMatterSquare
import UnifiedTheory.Audit.KFCausalSecondShiftReducedOutput
import UnifiedTheory.Audit.KFCausalSourcedMomentumFactors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalGaussianMomentumMatterSquare
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalPhysicalField (physicalField)
open KFCausalTransverseFieldSquare (fieldSquare)
open KFCausalClockFloorTrialMatter (matterFactor)
open KFCausalClockFloorMatterClosure (reversedMatterFactor)
open KFCausalClockFloorTrialSpectralDomain (reversedExponential)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorExponential (longitudinalExponential)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalCoherentMomentumOutputReduction (reducedOutput)
open KFCausalClockFloorSourcedCommonDomain (linearOutput quadraticOutput)
open KFCausalSourcedMomentumFactors (pureOutput factorOutput_graph)
open KFCausalGaussianVacuumSquare (original_strip double_strip)

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α)
  (hβ : 0 < β) (hw : 32*β ≤ α) (h : ℝ) (hb : |h| ≤ Real.pi*ε/3)
local notation "hb₀" => original_strip ε h hε hb
local notation "hb₂" => double_strip ε h hb
local notation "ha₂" => half_pos ha
local notation "Bψ" => pureOutput ε a α β hε ha hα hβ hw 1 0 0 h

def input (j : Fin 2) : Hilbert := reducedOutput ε a h hε ha hb₀ 0
  (KFCausalGaussianMatterSquare.input ε a α β hε ha hα hβ hw h hb j)
  (KFCausalGaussianMatterSquare.input ε (a/2) α β hε ha₂ hα hβ hw h hb j)

def spectralOutput (j : Fin 2) : Hilbert := (1/2:ℂ) • reducedOutput ε a (2*h) hε ha hb₂ 0
  (KFCausalGaussianMatterSquare.spectralOutput ε a α β hε ha hα hβ hw h hb j)
  (KFCausalGaussianMatterSquare.spectralOutput ε (a/2) α β hε ha₂ hα hβ hw h hb j)

def output (j : Fin 2) : Hilbert := inverseL ε hε
  (spectralOutput ε a α β hε ha hα hβ hw h hb j)

theorem input_exponential_graph (j : Fin 2) :
    (input ε a α β hε ha hα hβ hw h hb j,spectralOutput ε a α β hε ha hα hβ hw h hb j) ∈
      (longitudinalExponential ε hε h (1/2)).graph :=
  KFCausalSecondShiftReducedOutput.exponential_graph ε a h hε ha hb 0 _ _ _ _
    (KFCausalGaussianMatterSquare.input_exponential_graph ε a α β hε ha hα hβ hw h hb j)
    (KFCausalGaussianMatterSquare.input_exponential_graph ε (a/2) α β hε ha₂ hα hβ hw h hb j)

theorem input_reverse_graph (j : Fin 2) :
    (input ε a α β hε ha hα hβ hw h hb j,output ε a α β hε ha hα hβ hw h hb j) ∈
      (reversedExponential ε hε h).graph :=
  (KFCausalClockFloorVacuumSquare.reversed_graph ε hε h _ _).mpr
    ⟨_,input_exponential_graph ε a α β hε ha hα hβ hw h hb j,rfl⟩

theorem linear_second_field_graph :
    (reducedOutput ε a h hε ha hb₀ 0
      (linearOutput ε a α β hε ha hα hβ hw 1 0 0 h hb₀ pointField)
      (linearOutput ε (a/2) α β hε ha₂ hα hβ hw 1 0 0 h hb₀ pointField),
        input ε a α β hε ha hα hβ hw h hb 0) ∈ (physicalField pointField).graph :=
  KFCausalBoundedClockMatterGraphs.reducedOutput_field_graph ε a h hε ha hb₀ pointField 0 _ _ _ _
    (KFCausalGaussianMatterSquare.linear_second_field_graph ε a α β hε ha hα hβ hw h hb)
    (KFCausalGaussianMatterSquare.linear_second_field_graph ε (a/2) α β hε ha₂ hα hβ hw h hb)

theorem quadratic_second_field_graph :
    (reducedOutput ε a h hε ha hb₀ 0
      (quadraticOutput ε a α β hε ha hα hβ hw 1 0 0 h hb₀ pointField)
      (quadraticOutput ε (a/2) α β hε ha₂ hα hβ hw 1 0 0 h hb₀ pointField),
        input ε a α β hε ha hα hβ hw h hb 1) ∈ (fieldSquare pointField).graph :=
  KFCausalBoundedClockMatterGraphs.reducedOutput_square_graph ε a h hε ha hb₀ pointField 0 _ _ _ _
    (KFCausalGaussianMatterSquare.quadratic_second_field_graph ε a α β hε ha hα hβ hw h hb)
    (KFCausalGaussianMatterSquare.quadratic_second_field_graph ε (a/2) α β hε ha₂ hα hβ hw h hb)

theorem linear_reverse_graph :
    (reducedOutput ε a h hε ha hb₀ 0
      (linearOutput ε a α β hε ha hα hβ hw 1 0 0 h hb₀ pointField)
      (linearOutput ε (a/2) α β hε ha₂ hα hβ hw 1 0 0 h hb₀ pointField),
        output ε a α β hε ha hα hβ hw h hb 0) ∈
      (reversedMatterFactor ε hε h (physicalField pointField)).graph :=
  (composition_graph _ _ _ _).mpr
    ⟨_,linear_second_field_graph ε a α β hε ha hα hβ hw h hb,
      input_reverse_graph ε a α β hε ha hα hβ hw h hb 0⟩

theorem quadratic_reverse_graph :
    (reducedOutput ε a h hε ha hb₀ 0
      (quadraticOutput ε a α β hε ha hα hβ hw 1 0 0 h hb₀ pointField)
      (quadraticOutput ε (a/2) α β hε ha₂ hα hβ hw 1 0 0 h hb₀ pointField),
        output ε a α β hε ha hα hβ hw h hb 1) ∈
      (reversedMatterFactor ε hε h (fieldSquare pointField)).graph :=
  (composition_graph _ _ _ _).mpr
    ⟨_,quadratic_second_field_graph ε a α β hε ha hα hβ hw h hb,
      input_reverse_graph ε a α β hε ha hα hβ hw h hb 1⟩

theorem linear_square_graph (hh : h ≠ 0) :
    (Bψ,output ε a α β hε ha hα hβ hw h hb 0) ∈
      (composition (reversedMatterFactor ε hε h (physicalField pointField))
        (matterFactor ε hε h (physicalField pointField))).graph :=
  (composition_graph _ _ _ _).mpr
    ⟨_,factorOutput_graph ε a α β hε ha hα hβ hw 1 0 0 h hh hb₀ 0 pointField 5,
      linear_reverse_graph ε a α β hε ha hα hβ hw h hb⟩

theorem quadratic_square_graph (hh : h ≠ 0) :
    (Bψ,output ε a α β hε ha hα hβ hw h hb 1) ∈
      (composition (reversedMatterFactor ε hε h (fieldSquare pointField))
        (matterFactor ε hε h (fieldSquare pointField))).graph :=
  (composition_graph _ _ _ _).mpr
    ⟨_,factorOutput_graph ε a α β hε ha hα hβ hw 1 0 0 h hh hb₀ 0 pointField 6,
      quadratic_reverse_graph ε a α β hε ha hα hβ hw h hb⟩

#print axioms input_exponential_graph
#print axioms input_reverse_graph
#print axioms linear_second_field_graph
#print axioms quadratic_second_field_graph
#print axioms linear_reverse_graph
#print axioms quadratic_reverse_graph
#print axioms linear_square_graph
#print axioms quadratic_square_graph
end
end UnifiedTheory.Audit.KFCausalGaussianMomentumMatterSquare
