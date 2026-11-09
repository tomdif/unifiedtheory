/- Explicit integrable coherent orbit lifts prove density of the actual
averaged energy domain. Their zero-charge projections are energy
admissible and total in the physical zero sector. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoherentFormOrbit
import UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
import UnifiedTheory.Audit.KFCausalClockFloorCoherentProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedDensity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentProjection
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorCoherentFormOrbit
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (group)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure orbit orbitState_coe)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)

variable (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
  (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ)

local notation "hb" => hamiltonian_bound ε hbar hbound
local notation "𝒟" => KFCausalClockFloorFormHamiltonian.formData ε hε hbar hb mass2 quartic vacuum t
local notation "BaseSpace" => KFCausalClosedGraphForm.FormSpace 𝒟
local notation "J" => KFCausalClosedGraphForm.embedding 𝒟

def orbitLift (k : Joint 2 4) : Lp BaseSpace 2 angleMeasure :=
  (formVector_orbit_memLp ε a hbar hε ha hh hbound mass2 quartic vacuum t k).toLp
    (fun θ => formVector ε a hbar hε ha hh hbound mass2 quartic vacuum t (parameter (2*Real.pi*θ) k))

theorem orbitLift_compatibility (k : Joint 2 4) :
    (J).compLp (orbitLift ε a hbar hε ha hh hbound mass2 quartic vacuum t k) =
      orbit (group hbar hh) (2*Real.pi) (state ε a hbar hε ha hh k) := by
  apply Lp.ext
  filter_upwards [(J).coeFn_compLp (orbitLift ε a hbar hε ha hh hbound mass2 quartic vacuum t k),
    (formVector_orbit_memLp ε a hbar hε ha hh hbound mass2 quartic vacuum t k).coeFn_toLp,
    orbitState_coe (group hbar hh) (2*Real.pi) (state ε a hbar hε ha hh k)] with θ hJ hv ho
  refine hJ.trans ?_
  change orbitLift ε a hbar hε ha hh hbound mass2 quartic vacuum t k θ = _ at hv
  rw [hv,orbit_formVector_embedding]
  exact ho.symm

def averagedVector (k : Joint 2 4) : AveragedSpace ε hε hbar hb hh mass2 quartic vacuum t :=
  ⟨WithLp.toLp 2 (state ε a hbar hε ha hh k,orbitLift ε a hbar hε ha hh hbound mass2 quartic vacuum t k),by
    change (J).compLp (orbitLift ε a hbar hε ha hh hbound mass2 quartic vacuum t k) -
      orbit (group hbar hh) (2*Real.pi) (state ε a hbar hε ha hh k) = 0
    exact sub_eq_zero.mpr (orbitLift_compatibility ε a hbar hε ha hh hbound mass2 quartic vacuum t k)⟩

theorem averagedVector_embedding (k : Joint 2 4) :
    embedding ε hε hbar hb hh mass2 quartic vacuum t
      (averagedVector ε a hbar hε ha hh hbound mass2 quartic vacuum t k) = state ε a hbar hε ha hh k := rfl

theorem averagedVector_energy (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) (k : Joint 2 4) :
    ‖energyOutput ε hε hbar hb hh mass2 quartic vacuum t
      (averagedVector ε a hbar hε ha hh hbound mass2 quartic vacuum t k)‖^2 =
        ∫ θ, KFCausalClockFloorJointEnergy.seedEnergy ε hε hbar
          KFCausalPhysicalEnergyFactors.modelDirections KFCausalMatterOrderedDomain.pointField mass2 quartic vacuum t
          ⟨state ε a hbar hε ha hh (parameter (2*Real.pi*θ) k),
            state_commonEnergyDomain ε a hbar hε ha hh hbound (parameter (2*Real.pi*θ) k)
              KFCausalPhysicalEnergyFactors.modelDirections KFCausalMatterOrderedDomain.pointField⟩ ∂angleMeasure := by
  rw [energy_integral]
  apply integral_congr_ae
  filter_upwards [(formVector_orbit_memLp ε a hbar hε ha hh hbound mass2 quartic vacuum t k).coeFn_toLp] with θ hθ
  change ‖KFCausalClosedGraphForm.energyOutput 𝒟
    (orbitLift ε a hbar hε ha hh hbound mass2 quartic vacuum t k θ)‖^2 = _
  change orbitLift ε a hbar hε ha hh hbound mass2 quartic vacuum t k θ = _ at hθ
  rw [hθ]
  exact formVector_energy ε a hbar hε ha hh hbound mass2 quartic vacuum t hm hq hv _

theorem state_mem_energy_domain (k : Joint 2 4) :
    state ε a hbar hε ha hh k ∈ (energyOperator ε hε hbar hb hh mass2 quartic vacuum t).domain :=
  (energy_domain ε hε hbar hb hh mass2 quartic vacuum t _).mpr
    ⟨averagedVector ε a hbar hε ha hh hbound mass2 quartic vacuum t k,rfl⟩

theorem coherentSpan_le_energy_domain :
    coherentSpan ε a hbar hε ha hh ≤ (energyOperator ε hε hbar hb hh mass2 quartic vacuum t).domain := by
  apply Submodule.span_le.mpr
  rintro f ⟨k,rfl⟩
  exact state_mem_energy_domain ε a hbar hε ha hh hbound mass2 quartic vacuum t k

theorem energy_domain_dense :
    Dense ((energyOperator ε hε hbar hb hh mass2 quartic vacuum t).domain : Set Hilbert) := by
  have hd : Dense (coherentSpan ε 1 hbar hε zero_lt_one hh : Set Hilbert) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr (coherentSpan_dense ε 1 hbar hε zero_lt_one hh)
  exact hd.mono (coherentSpan_le_energy_domain ε 1 hbar hε zero_lt_one hh hbound mass2 quartic vacuum t)

theorem projectedState_mem_energy_domain (k : Joint 2 4) :
    projectedState ε a hbar hε ha hh k ∈ (energyOperator ε hε hbar hb hh mass2 quartic vacuum t).domain :=
  zeroProjection_mem_energy_domain ε hε hbar hb hh mass2 quartic vacuum t _
    (state_mem_energy_domain ε a hbar hε ha hh hbound mass2 quartic vacuum t k)

theorem projected_span_le_zero_energy_domain :
    Submodule.span ℂ (Set.range (projectedState ε a hbar hε ha hh)) ≤
      zeroSector hbar hh ⊓ (energyOperator ε hε hbar hb hh mass2 quartic vacuum t).domain := by
  apply Submodule.span_le.mpr
  rintro f ⟨k,rfl⟩
  exact ⟨projectedState_mem ε a hbar hε ha hh k,
    projectedState_mem_energy_domain ε a hbar hε ha hh hbound mass2 quartic vacuum t k⟩

theorem zero_energy_domain_closure :
    (zeroSector hbar hh ⊓ (energyOperator ε hε hbar hb hh mass2 quartic vacuum t).domain).topologicalClosure =
      zeroSector hbar hh := by
  apply le_antisymm
  · have hc := Submodule.topologicalClosure_mono
      (show zeroSector hbar hh ⊓ (energyOperator ε hε hbar hb hh mass2 quartic vacuum t).domain ≤
        zeroSector hbar hh from inf_le_left)
    rwa [(zeroSector_closed hbar hh).submodule_topologicalClosure_eq] at hc
  · have hc := Submodule.topologicalClosure_mono
      (projected_span_le_zero_energy_domain ε 1 hbar hε zero_lt_one hh hbound mass2 quartic vacuum t)
    rwa [dense_projected_span] at hc

#print axioms orbitLift_compatibility
#print axioms averagedVector_embedding
#print axioms averagedVector_energy
#print axioms state_mem_energy_domain
#print axioms coherentSpan_le_energy_domain
#print axioms energy_domain_dense
#print axioms projectedState_mem_energy_domain
#print axioms projected_span_le_zero_energy_domain
#print axioms zero_energy_domain_closure

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedDensity
