/- The actual zero-charge projection commutes with the averaged
Hamiltonian's resolvents, Yosida operators and their time-dependent
unitary evolutions. The unbounded evolution limit remains separate. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaDynamics
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedDynamicsProjection
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open UnifiedTheory.Audit.KFCausalClockFloorHamiltonianProjection
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosida
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaDynamics

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
  (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum a : ℝ) (ha : 0 < a)

local notation "P" => zeroProjection hbar hh
local notation "𝓗" => hamiltonian ε hε hbar hh hbound mass2 quartic vacuum
local notation "𝓡" => shiftedResolvent ε hε hbar hh hbound mass2 quartic vacuum a
local notation "𝒰" => dynamics ε hε hbar hh hbound mass2 quartic vacuum a ha

include ha

theorem shiftedResolvent_zeroProjection (t : ℝ) (f : Hilbert) : 𝓡 t (P f) = P (𝓡 t f) := by
  let x := resolventVector ε hε hbar hh hbound mass2 quartic vacuum a t ha f
  let y : (𝓗 t).domain := ⟨P (x:Hilbert),
    zeroProjection_mem_hamiltonian_domain ε hε hbar hh hbound mass2 quartic vacuum t x⟩
  have hl := shiftedResolvent_left ε hε hbar hh hbound mass2 quartic vacuum a t ha y
  have hH := hamiltonian_zeroProjection ε hε hbar hh hbound mass2 quartic vacuum t x
  have hr := shiftedResolvent_right ε hε hbar hh hbound mass2 quartic vacuum a t ha f
  have he : 𝓗 t y+a • (y:Hilbert) = P f := by
    calc
      _ = P (𝓗 t x)+a • P (x:Hilbert) := congrArg (fun z => z+a • P (x:Hilbert)) hH
      _ = P (𝓗 t x+a • (x:Hilbert)) := by
        simp only [map_add,ContinuousLinearMap.map_smul_of_tower]
      _ = P f := congrArg (P) hr
  exact (congrArg (𝓡 t) he).symm.trans hl

theorem averagedYosida_zeroProjection (t : ℝ) (f : Hilbert) :
    averagedYosida ε hε hbar hh hbound mass2 quartic vacuum a t (P f) =
      P (averagedYosida ε hε hbar hh hbound mass2 quartic vacuum a t f) := by
  simp only [averagedYosida,KFCausalYosidaApproximation.yosida_apply,map_sub,
    ContinuousLinearMap.map_smul_of_tower,shiftedResolvent_zeroProjection ε hε hbar hh hbound mass2 quartic vacuum a ha]

theorem generator_zeroProjection (t : ℝ) (f : Hilbert) :
    generator ε hε hbar hh hbound mass2 quartic vacuum a t (P f) =
      P (generator ε hε hbar hh hbound mass2 quartic vacuum a t f) := by
  simp only [generator,ContinuousLinearMap.smul_apply,map_smul,
    averagedYosida_zeroProjection ε hε hbar hh hbound mass2 quartic vacuum a ha]

theorem dynamics_zeroProjection (s t : ℝ) (f : Hilbert) : 𝒰 s t (P f) = P (𝒰 s t f) := by
  have hinit : P (𝒰 s s f) = P f := by
    rw [dynamics_initial]
    rfl
  have hd : ∀ r, HasDerivAt (fun z => P (𝒰 s z f))
      (generator ε hε hbar hh hbound mass2 quartic vacuum a r (P (𝒰 s r f))) r := by
    intro r
    rw [generator_zeroProjection ε hε hbar hh hbound mass2 quartic vacuum a ha]
    exact ((P).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r
      (dynamics_state_derivative ε hε hbar hh hbound mass2 quartic vacuum a ha s r f)
  have hu := dynamics_state_unique ε hε hbar hh hbound mass2 quartic vacuum a ha s (P f)
    (fun z => P (𝒰 s z f)) hinit hd
  exact (congrFun hu t).symm

theorem dynamics_zero_sector (s t : ℝ) (f : Hilbert) (hf : f ∈ zeroSector hbar hh) :
    𝒰 s t f ∈ zeroSector hbar hh := by
  have hp := dynamics_zeroProjection ε hε hbar hh hbound mass2 quartic vacuum a ha s t f
  have he : P (𝒰 s t f) = 𝒰 s t f :=
    hp.symm.trans (congrArg (𝒰 s t) (zeroProjection_fixes hbar hh f hf))
  exact (congrArg (fun g : Hilbert => g ∈ zeroSector hbar hh) he).mp (zeroProjection_mem hbar hh _)

theorem dynamics_charge_zero (s t : ℝ) (f : Hilbert) (hf : f ∈ zeroSector hbar hh) :
    (𝒰 s t f,0) ∈ (standingCharge hbar hh).graph :=
  (standingCharge_zero_iff hbar hh _).mpr
    (dynamics_zero_sector ε hε hbar hh hbound mass2 quartic vacuum a ha s t f hf)

#print axioms shiftedResolvent_zeroProjection
#print axioms averagedYosida_zeroProjection
#print axioms generator_zeroProjection
#print axioms dynamics_zeroProjection
#print axioms dynamics_zero_sector
#print axioms dynamics_charge_zero

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedDynamicsProjection
