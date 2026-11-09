/- The two natural matter squares on an actual physical Gaussian.
Their second spectral actions are constructed from a mixed contour,
without an assumed reverse-factor or Hamiltonian-domain premise. -/
import UnifiedTheory.Audit.KFCausalMixedFieldGaussianPhysical
import UnifiedTheory.Audit.KFCausalClockFloorSourcedCommonDomain
import UnifiedTheory.Audit.KFCausalGaussianVacuumSquare
import UnifiedTheory.Audit.KFCausalClockFloorMatterClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalGaussianMatterSquare
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalPhysicalField (physicalField physicalField_graph)
open KFCausalTransverseFieldSquare (fieldSquare fieldSquare_graph)
open KFCausalClockFloorSourcedCommonDomain
open KFCausalClockFloorSourcedSpectral (shiftedOutput)
open KFCausalClockFloorTrialMatter (matterFactor)
open KFCausalClockFloorMatterClosure (reversedMatterFactor)
open KFCausalClockFloorTrialSpectralDomain (reversedExponential)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorExponential (longitudinalExponential)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalMixedFieldGaussianContour (strip_pair double_shift_bound)
open KFCausalGaussianVacuumSquare (original_strip)

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α)
  (hβ : 0 < β) (hw : 32*β ≤ α) (h : ℝ) (hb : |h| ≤ Real.pi*ε/3)
local notation "hb₀" => original_strip ε h hε hb
local notation "hd" => double_shift_bound ε h hb
local notation "h0" => strip_pair ε (-h/2) |-h/2| 0 hd (by simp)
local notation "hs" => strip_pair ε (-h/2) |-h/2| (-h/2) hd le_rfl
local notation "S" => KFCausalClockFloorSourcedClockMomentum.state ε a α β hε ha hα hβ hw 1 0 0
local notation "Y" => shiftedOutput ε a α β hε ha hα hβ hw 1 0 0 h hb₀

def input (j : Fin 2) : Hilbert :=
  KFCausalMixedFieldGaussianSpectral.state ε a α β (-h/2) 0 j hε ha hα hβ hw h0.1 h0.2

def spectralOutput (j : Fin 2) : Hilbert :=
  KFCausalMixedFieldGaussianSpectral.state ε a α β (-h/2) (-h/2) j hε ha hα hβ hw hs.1 hs.2

def output (j : Fin 2) : Hilbert :=
  inverseL ε hε (spectralOutput ε a α β hε ha hα hβ hw h hb j)

theorem input_coe (j : Fin 2) :
    input ε a α β hε ha hα hβ hw h hb j =ᵐ[volume]
      fun x => (pointField x.2:ℂ)^KFCausalMixedFieldGaussianStrip.degree j * Y x := by
  have hg := KFCausalMixedFieldGaussianPhysical.state_zero_coe ε a α β (-h/2) j hε ha hα hβ hw
    (KFCausalClockFloorShiftedOutput.shift_bound ε h hb₀)
  simpa only [input,shiftedOutput,one_smul] using hg

theorem input_exponential_graph (j : Fin 2) :
    (input ε a α β hε ha hα hβ hw h hb j,
      spectralOutput ε a α β hε ha hα hβ hw h hb j) ∈
        (longitudinalExponential ε hε h (1/2)).graph :=
  KFCausalMixedFieldGaussianSpectral.state_exponential_graph ε a α β (-h/2) h j hε ha hα hβ hw hd

theorem linear_second_field_graph :
    (linearOutput ε a α β hε ha hα hβ hw 1 0 0 h hb₀ pointField,
      input ε a α β hε ha hα hβ hw h hb 0) ∈ (physicalField pointField).graph := by
  have hl := (physicalField_graph pointField _ _).mp ((physicalField pointField).mem_graph
    ⟨Y,shiftedOutput_physicalField_domain ε a α β hε ha hα hβ hw 1 0 0 h hb₀ pointField⟩)
  apply (physicalField_graph pointField _ _).mpr
  filter_upwards [input_coe ε a α β hε ha hα hβ hw h hb 0,hl] with x hx hy
  change linearOutput ε a α β hε ha hα hβ hw 1 0 0 h hb₀ pointField x = _ at hy
  rw [hx,hy]
  norm_num [KFCausalMixedFieldGaussianStrip.degree]
  ring

theorem quadratic_second_field_graph :
    (quadraticOutput ε a α β hε ha hα hβ hw 1 0 0 h hb₀ pointField,
      input ε a α β hε ha hα hβ hw h hb 1) ∈ (fieldSquare pointField).graph := by
  have hl := (fieldSquare_graph pointField _ _).mp ((fieldSquare pointField).mem_graph
    ⟨Y,shiftedOutput_fieldSquare_domain ε a α β hε ha hα hβ hw 1 0 0 h hb₀ pointField⟩)
  apply (fieldSquare_graph pointField _ _).mpr
  filter_upwards [input_coe ε a α β hε ha hα hβ hw h hb 1,hl] with x hx hy
  change quadraticOutput ε a α β hε ha hα hβ hw 1 0 0 h hb₀ pointField x = _ at hy
  rw [hx,hy]
  norm_num [KFCausalMixedFieldGaussianStrip.degree]
  ring

theorem input_reverse_graph (j : Fin 2) :
    (input ε a α β hε ha hα hβ hw h hb j,output ε a α β hε ha hα hβ hw h hb j) ∈
      (reversedExponential ε hε h).graph :=
  (KFCausalClockFloorVacuumSquare.reversed_graph ε hε h _ _).mpr
    ⟨_,input_exponential_graph ε a α β hε ha hα hβ hw h hb j,rfl⟩

theorem linear_reverse_graph :
    (linearOutput ε a α β hε ha hα hβ hw 1 0 0 h hb₀ pointField,
      output ε a α β hε ha hα hβ hw h hb 0) ∈
        (reversedMatterFactor ε hε h (physicalField pointField)).graph :=
  (composition_graph _ _ _ _).mpr
    ⟨_,linear_second_field_graph ε a α β hε ha hα hβ hw h hb,
      input_reverse_graph ε a α β hε ha hα hβ hw h hb 0⟩

theorem quadratic_reverse_graph :
    (quadraticOutput ε a α β hε ha hα hβ hw 1 0 0 h hb₀ pointField,
      output ε a α β hε ha hα hβ hw h hb 1) ∈
        (reversedMatterFactor ε hε h (fieldSquare pointField)).graph :=
  (composition_graph _ _ _ _).mpr
    ⟨_,quadratic_second_field_graph ε a α β hε ha hα hβ hw h hb,
      input_reverse_graph ε a α β hε ha hα hβ hw h hb 1⟩

theorem linear_square_graph :
    (S,output ε a α β hε ha hα hβ hw h hb 0) ∈
      (composition (reversedMatterFactor ε hε h (physicalField pointField))
        (matterFactor ε hε h (physicalField pointField))).graph :=
  (composition_graph _ _ _ _).mpr
    ⟨_,linearOutput_graph ε a α β hε ha hα hβ hw 1 0 0 h hb₀ pointField,
      linear_reverse_graph ε a α β hε ha hα hβ hw h hb⟩

theorem quadratic_square_graph :
    (S,output ε a α β hε ha hα hβ hw h hb 1) ∈
      (composition (reversedMatterFactor ε hε h (fieldSquare pointField))
        (matterFactor ε hε h (fieldSquare pointField))).graph :=
  (composition_graph _ _ _ _).mpr
    ⟨_,quadraticOutput_graph ε a α β hε ha hα hβ hw 1 0 0 h hb₀ pointField,
      quadratic_reverse_graph ε a α β hε ha hα hβ hw h hb⟩

#print axioms input_coe
#print axioms input_exponential_graph
#print axioms linear_second_field_graph
#print axioms quadratic_second_field_graph
#print axioms input_reverse_graph
#print axioms linear_reverse_graph
#print axioms quadratic_reverse_graph
#print axioms linear_square_graph
#print axioms quadratic_square_graph
end
end UnifiedTheory.Audit.KFCausalGaussianMatterSquare
