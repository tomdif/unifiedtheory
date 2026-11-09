/- A bounded action on the original completed, weighted eight-factor
form, obtained from its literal simultaneous graph closure. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaEnergy
import UnifiedTheory.Audit.KFCausalClockFloorFormHamiltonian

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaForm
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFiniteJointGraph (Output)
open KFCausalClockFloorRadialYosidaSymbol (action)
open KFCausalClockFloorRadialYosidaEnergy
open KFCausalJointGraphBoundedCorrection (outputMap correctionMap)
open KFCausalPhysicalEnergyFactors (energyWeight)
open KFCausalClosedGraphForm (FormSpace embedding energyOutput energyGraph)
open KFCausalClockFloorFormHamiltonian (formData)

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
  (hb : |h| ≤ Real.pi*ε/3) (hne : h ≠ 0) (m g k t : ℝ)

local notation "𝒟" => formData ε hε h (energy_bound ε hε h hb) m g k t
local notation "W" => WithLp 2 (Hilbert × Output (Fin 8) Hilbert)

def outputAction : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert :=
  outputMap (factorOutput ε hε h N hN hb)

def extra : Hilbert →L[ℂ] Output (Fin 8) Hilbert :=
  correctionMap (factorCorrection ε hε h N hN) (energyWeight m g k t)

def ambientAction : W →L[ℂ] W :=
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ Hilbert (Output (Fin 8) Hilbert)
  let b := ((action ε hε h N hN).comp (ContinuousLinearMap.fst ℂ Hilbert (Output (Fin 8) Hilbert))).prod
    ((outputAction ε hε h N hN hb).comp (ContinuousLinearMap.snd ℂ Hilbert (Output (Fin 8) Hilbert))+
      (extra ε hε h N hN m g k t).comp (ContinuousLinearMap.fst ℂ Hilbert (Output (Fin 8) Hilbert)))
  e.symm.toContinuousLinearMap.comp (b.comp e.toContinuousLinearMap)

include hne in
theorem ambient_mem (u : FormSpace 𝒟) :
    ambientAction ε hε h N hN hb m g k t u.val ∈ energyGraph 𝒟 :=
  closed_graph ε hε h N hN hb hne m g k t (embedding 𝒟 u) (energyOutput 𝒟 u) u.property

def formAction : FormSpace 𝒟 →L[ℂ] FormSpace 𝒟 where
  toFun u := ⟨ambientAction ε hε h N hN hb m g k t u.val,
    ambient_mem ε hε h N hN hb hne m g k t u⟩
  map_add' u v := by apply Subtype.ext; exact (ambientAction ε hε h N hN hb m g k t).map_add u.val v.val
  map_smul' c u := by apply Subtype.ext; exact (ambientAction ε hε h N hN hb m g k t).map_smul c u.val
  cont := ((ambientAction ε hε h N hN hb m g k t).continuous.comp continuous_subtype_val).subtype_mk _

theorem formAction_embedding (u : FormSpace 𝒟) :
    embedding 𝒟 (formAction ε hε h N hN hb hne m g k t u)=action ε hε h N hN (embedding 𝒟 u) := rfl

theorem formAction_output (u : FormSpace 𝒟) :
    energyOutput 𝒟 (formAction ε hε h N hN hb hne m g k t u)=
      outputAction ε hε h N hN hb (energyOutput 𝒟 u)+extra ε hε h N hN m g k t (embedding 𝒟 u) := rfl

#print axioms ambient_mem
#print axioms formAction_embedding
#print axioms formAction_output
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaForm
