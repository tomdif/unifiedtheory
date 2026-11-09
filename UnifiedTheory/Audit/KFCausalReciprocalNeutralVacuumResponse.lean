/- Identify the source-free, constant-neutral-profile specialization
with the existing reciprocal model by uniqueness of actual operator
graphs. Its proved uniform lower response bound transfers unchanged. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralPotentialTransport
import UnifiedTheory.Audit.KFCausalReciprocalSuperpositionEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralVacuumResponse
noncomputable section
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)

variable (n : ℕ) (ε h : ℝ) (a w : Fin n → ℝ) (c : Fin n → ℂ)
  (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
local notation "NS" => KFCausalReciprocalNeutralSuperposition.state n ε h a w (fun _ => 0) c (fun _ => 0) (fun _ => 1) hε ha hh hw
local notation "NM" => KFCausalReciprocalNeutralSuperposition.momentum n ε h a w (fun _ => 0) c (fun _ => 0) (fun _ => 1) hε ha hh hw
local notation "RS" => KFCausalReciprocalSuperpositionFactors.state n ε h a w c hε ha hh hw
local notation "RM" => KFCausalReciprocalSuperpositionFactors.momentum n ε h a w c hε ha hh hw

theorem momentum_reciprocal : NM = RM :=
  (pureMomentum ε hε h).mem_graph_snd_inj'
    (KFCausalReciprocalNeutralSuperposition.momentum_graph n ε h a w _ c _ _ hε ha hh hw)
    (KFCausalReciprocalSuperpositionFactors.momentum_graph n ε h a w c hε ha hh hw)
    (KFCausalReciprocalNeutralSuperposition.state_reciprocal n ε h a w c hε ha hh hw)

variable (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "NU" => KFCausalReciprocalNeutralSuperposition.output n ε h a w (fun _ => 0) c (fun _ => 0) (fun _ => 1) hε ha hh hw hb
local notation "NV" => KFCausalReciprocalNeutralSuperposition.momentumOutput n ε h a w (fun _ => 0) c (fun _ => 0) (fun _ => 1) hε ha hh hw hb
local notation "RU" => KFCausalReciprocalSuperpositionFactors.output n ε h a w c hε ha hh hw hb
local notation "RV" => KFCausalReciprocalSuperpositionFactors.momentumOutput n ε h a w c hε ha hh hw hb

theorem output_reciprocal (j : Fin 8) : NU j = RU j :=
  (energyFactor ε hε h modelDirections pointField j).mem_graph_snd_inj'
    (KFCausalReciprocalNeutralSuperposition.output_graph n ε h a w _ c _ _ hε ha hh hw hb j)
    (KFCausalReciprocalSuperpositionFactors.output_graph n ε h a w c hε ha hh hw hb j)
    (KFCausalReciprocalNeutralSuperposition.state_reciprocal n ε h a w c hε ha hh hw)

theorem momentumOutput_reciprocal (j : Fin 8) : NV j = RV j :=
  (energyFactor ε hε h modelDirections pointField j).mem_graph_snd_inj'
    (KFCausalReciprocalNeutralSuperposition.momentumOutput_graph n ε h a w _ c _ _ hε ha hh hw hb j)
    (KFCausalReciprocalSuperpositionFactors.momentumOutput_graph n ε h a w c hε ha hh hw hb j)
    (momentum_reciprocal n ε h a w c hε ha hh hw)

theorem energy_reciprocal :
    KFCausalReciprocalNeutralPositiveEnergy.potentialEnergy n ε h a w (fun _ => 0) c (fun _ => 0)
      (fun _ => 1) hε ha hh hw hb =
      KFCausalReciprocalSuperpositionEnergy.potentialEnergy n ε h a w c hε ha hh hw hb := by
  unfold KFCausalReciprocalNeutralPositiveEnergy.potentialEnergy KFCausalReciprocalSuperpositionEnergy.potentialEnergy
    KFCausalReciprocalSuperpositionFactors.factorEnergy
  simp only [output_reciprocal n ε h a w c hε ha hh hw hb]

theorem response_reciprocal :
    KFCausalReciprocalNeutralPotentialTransport.potentialResponse n ε h a w (fun _ => 0) c (fun _ => 0)
      (fun _ => 1) hε ha hh hw hb =
      KFCausalReciprocalSuperpositionEnergy.potentialResponse n ε h a w c hε ha hh hw hb := by
  unfold KFCausalReciprocalNeutralPotentialTransport.potentialResponse KFCausalReciprocalSuperpositionEnergy.potentialResponse
    KFCausalReciprocalSuperpositionFactors.factorRate
  rw [output_reciprocal n ε h a w c hε ha hh hw hb 7,output_reciprocal n ε h a w c hε ha hh hw hb 5,
    output_reciprocal n ε h a w c hε ha hh hw hb 6,
    momentumOutput_reciprocal n ε h a w c hε ha hh hw hb 7,momentumOutput_reciprocal n ε h a w c hε ha hh hw hb 5,
    momentumOutput_reciprocal n ε h a w c hε ha hh hw hb 6]
  norm_num [Complex.add_im,Complex.div_im]
  ring

theorem exists_uniform_response :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (ε h : ℝ) (a w : Fin n → ℝ) (c : Fin n → ℂ)
      (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
      (hb : |h| ≤ 2*Real.pi*ε/3), |h| ≤ Real.pi*ε/3 →
      -((C+2)/ε)*KFCausalReciprocalNeutralPositiveEnergy.potentialEnergy n ε h a w (fun _ => 0) c
        (fun _ => 0) (fun _ => 1) hε ha hh hw hb ≤
      KFCausalReciprocalNeutralPotentialTransport.potentialResponse n ε h a w (fun _ => 0) c
        (fun _ => 0) (fun _ => 1) hε ha hh hw hb := by
  obtain ⟨C,hC,hbound⟩ := KFCausalReciprocalSuperpositionClockResponse.exists_uniform_potential_response
  refine ⟨C,hC,?_⟩
  intro n ε h a w c hε ha hh hw hb hs
  rw [energy_reciprocal n ε h a w c hε ha hh hw hb,response_reciprocal n ε h a w c hε ha hh hw hb,
    KFCausalReciprocalSuperpositionEnergy.potentialEnergy_integral,
    KFCausalReciprocalSuperpositionEnergy.potentialResponse_integral]
  exact hbound n ε h a w c hε ha hh hw hs

#print axioms momentum_reciprocal
#print axioms output_reciprocal
#print axioms momentumOutput_reciprocal
#print axioms energy_reciprocal
#print axioms response_reciprocal
#print axioms exists_uniform_response
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralVacuumResponse
