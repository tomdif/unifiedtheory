/- Primitive graph assembly for the two exponential half steps of the
actual quadratic and quartic matter components. Midpoint uniqueness
uses only the proved exponential square graph identity. -/
import UnifiedTheory.Audit.KFCausalSourcedWidthMatterSquare

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalMatterHalfStepAssembly
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorBoundedInverse (inverseL inverseL_graph ordered_graph_iff)
open KFCausalClockFloorExponential (longitudinalExponential longitudinal_exponential_square)
open KFCausalClockFloorTrialSpectralDomain (orderedExponential reversedExponential)
open KFCausalClockFloorTrialMatter (matterFactor)
open KFCausalClockFloorMatterClosure (reversedMatterFactor)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalPhysicalField (physicalField)
open KFCausalTransverseFieldSquare (fieldSquare)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalReciprocalNeutralMatterSpectral (matterIndex)
open KFCausalSourcedWidthMatterSquare (matterSecond)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ)
local notation "E" => longitudinalExponential ε hε h (1/2)
local notation "D" => inverseL ε hε

theorem second_half_graph (f z y : Hilbert)
    (hz : (f,z) ∈ (E).graph)
    (hy : (f,y) ∈ (longitudinalExponential ε hε h 1).graph) : (z,y) ∈ (E).graph := by
  obtain ⟨g,hg,hgy⟩ := (longitudinal_exponential_square ε hε h f y).mp hy
  have he : g=z := (E).mem_graph_snd_inj' hg hz rfl
  rwa [he] at hgy

theorem reversed_exponential_graph (z y : Hilbert) (hy : (z,y) ∈ (E).graph) :
    (z,D y) ∈ (reversedExponential ε hε h).graph :=
  (composition_graph _ _ _ _).mpr ⟨y,hy,(inverseL_graph ε hε y _).mpr rfl⟩

theorem matter_forward_graph (T : Hilbert →ₗ.[ℂ] Hilbert) (f g a : Hilbert)
    (hg : (D f,g) ∈ (E).graph) (ha : (g,a) ∈ T.graph) :
    (f,a) ∈ (matterFactor ε hε h T).graph :=
  (composition_graph _ _ _ _).mpr ⟨g,(ordered_graph_iff ε hε h f g).mpr hg,ha⟩

theorem matter_reverse_graph (T : Hilbert →ₗ.[ℂ] Hilbert) (a z y : Hilbert)
    (hz : (a,z) ∈ T.graph) (hy : (z,y) ∈ (E).graph) :
    (a,D y) ∈ (reversedMatterFactor ε hε h T).graph :=
  (composition_graph _ _ _ _).mpr ⟨z,hz,reversed_exponential_graph ε hε h z y hy⟩

def fieldFactor (j : Fin 2) : Hilbert →ₗ.[ℂ] Hilbert :=
  ![physicalField pointField,fieldSquare pointField] j

theorem energyFactor_eq (j : Fin 2) :
    energyFactor ε hε h modelDirections pointField (matterIndex j) =
      matterFactor ε hε h (fieldFactor j) := by
  fin_cases j <;> rfl

theorem reverseFactor_eq (j : Fin 2) :
    reverseFactor ε hε h modelDirections pointField (matterIndex j) =
      reversedMatterFactor ε hε h (fieldFactor j) := by
  fin_cases j <;> rfl

theorem actual_forward_graph (j : Fin 2) (f g a : Hilbert)
    (hg : (D f,g) ∈ (E).graph) (ha : (g,a) ∈ (fieldFactor j).graph) :
    (f,a) ∈ (energyFactor ε hε h modelDirections pointField (matterIndex j)).graph := by
  rw [energyFactor_eq]
  exact matter_forward_graph ε hε h (fieldFactor j) f g a hg ha

theorem actual_reverse_graph (j : Fin 2) (a z y : Hilbert)
    (hz : (a,z) ∈ (fieldFactor j).graph) (hy : (z,y) ∈ (E).graph) :
    (a,D y) ∈ (reverseFactor ε hε h modelDirections pointField (matterIndex j)).graph := by
  rw [reverseFactor_eq]
  exact matter_reverse_graph ε hε h (fieldFactor j) a z y hz hy

theorem actual_second_graph (j : Fin 2) (f g a z y : Hilbert)
    (hg : (D f,g) ∈ (E).graph) (ha : (g,a) ∈ (fieldFactor j).graph)
    (hz : (a,z) ∈ (fieldFactor j).graph) (hy : (z,y) ∈ (E).graph) :
    (f,D y) ∈ (matterSecond ε h j hε).graph :=
  (composition_graph _ _ _ _).mpr ⟨a,actual_forward_graph ε hε h j f g a hg ha,
    actual_reverse_graph ε hε h j a z y hz hy⟩

#print axioms second_half_graph
#print axioms reversed_exponential_graph
#print axioms matter_forward_graph
#print axioms matter_reverse_graph
#print axioms energyFactor_eq
#print axioms reverseFactor_eq
#print axioms actual_forward_graph
#print axioms actual_reverse_graph
#print axioms actual_second_graph
end
end UnifiedTheory.Audit.KFCausalMatterHalfStepAssembly
