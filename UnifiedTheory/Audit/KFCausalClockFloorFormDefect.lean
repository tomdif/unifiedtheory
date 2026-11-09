/- The real defect is a bounded map of the complete unaveraged form
space, with its actual output identity and signed squared-defect pairing.
The representing Hamiltonian inherits the pairing; no evolution derivative
or invariance of its operator domain is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorClosedEnergyDefect
import UnifiedTheory.Audit.KFCausalClockFloorFormHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorFormDefect
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalClosedGraphForm
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction
open UnifiedTheory.Audit.KFCausalClockFloorClosedEnergyDefect

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ 2*Real.pi*ε/3)
  (mass2 quartic vacuum t : ℝ)

local notation "hb" => energy_bound ε hε hbar hh
local notation "𝒟" => KFCausalClockFloorFormHamiltonian.formData ε hε hbar hb mass2 quartic vacuum t

def formLinear : FormSpace 𝒟 →ₗ[ℂ] FormSpace 𝒟 where
  toFun u := ⟨WithLp.toLp 2 (defectOperator ε hε (embedding 𝒟 u),
    outputAction ε hε hbar hh (energyOutput 𝒟 u)),
    closedEnergy_graph_defect ε hε hbar hh modelDirections pointField mass2 quartic vacuum t
      (embedding 𝒟 u) (energyOutput 𝒟 u) u.property⟩
  map_add' u v := by
    apply embedding_injective 𝒟
    change defectOperator ε hε (embedding 𝒟 (u+v)) =
      embedding 𝒟 (_+_)
    simp only [map_add]
    rfl
  map_smul' c u := by
    apply embedding_injective 𝒟
    change defectOperator ε hε (embedding 𝒟 (c • u)) = embedding 𝒟 (c • _)
    simp only [map_smul]
    rfl

theorem formLinear_embedding (u : FormSpace 𝒟) :
    embedding 𝒟 (formLinear ε hε hbar hh mass2 quartic vacuum t u) = defectOperator ε hε (embedding 𝒟 u) := rfl

theorem formLinear_output (u : FormSpace 𝒟) :
    energyOutput 𝒟 (formLinear ε hε hbar hh mass2 quartic vacuum t u) =
      outputAction ε hε hbar hh (energyOutput 𝒟 u) := rfl

theorem formLinear_norm (u : FormSpace 𝒟) : ‖formLinear ε hε hbar hh mass2 quartic vacuum t u‖ ≤ 2*‖u‖ := by
  have hD := pow_le_pow_left₀ (norm_nonneg _) (defectOperator_norm_le ε hε (embedding 𝒟 u)) 2
  have hR := pow_le_pow_left₀ (norm_nonneg _) (outputAction_norm ε hε hbar hh (energyOutput 𝒟 u)) 2
  rw [mul_pow] at hR
  have h1 := form_norm_identity 𝒟 (formLinear ε hε hbar hh mass2 quartic vacuum t u)
  have h0 := form_norm_identity 𝒟 u
  rw [formLinear_embedding,formLinear_output] at h1
  nlinarith [sq_nonneg ‖embedding 𝒟 u‖,norm_nonneg u,norm_nonneg (formLinear ε hε hbar hh mass2 quartic vacuum t u)]

def formAction : FormSpace 𝒟 →L[ℂ] FormSpace 𝒟 :=
  (formLinear ε hε hbar hh mass2 quartic vacuum t).mkContinuous 2
    (formLinear_norm ε hε hbar hh mass2 quartic vacuum t)

theorem formAction_embedding (u : FormSpace 𝒟) :
    embedding 𝒟 (formAction ε hε hbar hh mass2 quartic vacuum t u) = defectOperator ε hε (embedding 𝒟 u) := rfl

theorem formAction_output (u : FormSpace 𝒟) :
    energyOutput 𝒟 (formAction ε hε hbar hh mass2 quartic vacuum t u) =
      outputAction ε hε hbar hh (energyOutput 𝒟 u) := rfl

theorem formAction_square_sign (u : FormSpace 𝒟) :
    0 ≤ hbar*(inner ℂ (energyOutput 𝒟 u)
      (energyOutput 𝒟 (formAction ε hε hbar hh mass2 quartic vacuum t
        (formAction ε hε hbar hh mass2 quartic vacuum t u)))).im := by
  rw [formAction_output,formAction_output]
  exact outputAction_square_sign ε hε hbar hh _

theorem unaveraged_hamiltonian_square_sign (f : (hamiltonian 𝒟).domain) :
    0 ≤ hbar*(inner ℂ (hamiltonian 𝒟 f) (defectOperator ε hε (defectOperator ε hε f))).im := by
  have hp := hamiltonian_represents_form 𝒟 f
    (formAction ε hε hbar hh mass2 quartic vacuum t
      (formAction ε hε hbar hh mass2 quartic vacuum t (formLift 𝒟 f)))
  rw [formAction_embedding,formAction_embedding,embedding_formLift] at hp
  rw [← hp]
  exact formAction_square_sign ε hε hbar hh mass2 quartic vacuum t (formLift 𝒟 f)

#print axioms formLinear_embedding
#print axioms formLinear_output
#print axioms formLinear_norm
#print axioms formAction_embedding
#print axioms formAction_output
#print axioms formAction_square_sign
#print axioms unaveraged_hamiltonian_square_sign

end
end UnifiedTheory.Audit.KFCausalClockFloorFormDefect
