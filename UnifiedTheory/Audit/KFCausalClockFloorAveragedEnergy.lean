/- The actual regulated eight-factor energy, averaged over the constructed
standing-wave circle action. Its operator graph is closed and its zero
projection is energy-contractive on its actual averaged domain. No density of the averaged
domain or averaged Hamiltonian is assumed. A normalized zero-charge state
is constructed from the previously proved invariant common-domain trial. -/
import UnifiedTheory.Audit.KFCausalAveragedEnergyGraph
import UnifiedTheory.Audit.KFCausalClockFloorFormHamiltonian
import UnifiedTheory.Audit.KFCausalStandingChargeOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (group action action_full_period)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (hne : hbar ≠ 0)
  (mass2 quartic vacuum t : ℝ)

local notation "𝒟" => KFCausalClockFloorFormHamiltonian.formData ε hε hbar hh mass2 quartic vacuum t
local notation "BaseSpace" => KFCausalClosedGraphForm.FormSpace 𝒟
local notation "J" => KFCausalClosedGraphForm.embedding 𝒟
local notation "A" => KFCausalClosedGraphForm.energyOutput 𝒟
local notation "U" => group hbar hne
local notation "T" => (2*Real.pi)

abbrev AveragedSpace := KFCausalAveragedFormSpace.FormSpace (H := Hilbert) (E := BaseSpace) U T J

abbrev embedding :=
  KFCausalAveragedFormSpace.embedding (H := Hilbert) (E := BaseSpace) U T J

abbrev sectionMap := KFCausalAveragedFormSpace.sectionMap (H := Hilbert) (E := BaseSpace) U T J

abbrev energyOutput :=
  KFCausalAveragedFormProjection.averagedOutput (H := Hilbert) (E := BaseSpace) (K := Output (Fin 8) Hilbert) U T J A

abbrev energyOperator :=
  KFCausalAveragedEnergyGraph.averagedOperator (H := Hilbert) (E := BaseSpace) (K := Output (Fin 8) Hilbert) U T J A

abbrev projectedForm (u : AveragedSpace ε hε hbar hh hne mass2 quartic vacuum t) := by
  let P := KFCausalAveragedFormProjection.project (H := Hilbert) (E := BaseSpace) U T
    (by positivity) (action_full_period hbar hne) J
  exact P u

theorem embedding_injective :
    Function.Injective (embedding ε hε hbar hh hne mass2 quartic vacuum t) := by
  have h := KFCausalAveragedFormSpace.embedding_injective (H := Hilbert) (E := BaseSpace) U T J
    (KFCausalClosedGraphForm.embedding_injective 𝒟)
  exact h

theorem energy_closed : (energyOperator ε hε hbar hh hne mass2 quartic vacuum t).IsClosed := by
  have h := KFCausalAveragedEnergyGraph.averagedOperator_closed (H := Hilbert) (E := BaseSpace) (K := Output (Fin 8) Hilbert) U T J A
  have hJ := KFCausalClosedGraphForm.embedding_injective 𝒟
  have hJA := KFCausalClosedGraphForm.form_norm_identity 𝒟
  exact h hJ hJA

theorem energy_domain (f : Hilbert) :
    f ∈ (energyOperator ε hε hbar hh hne mass2 quartic vacuum t).domain ↔
      ∃ u : AveragedSpace ε hε hbar hh hne mass2 quartic vacuum t,
        embedding ε hε hbar hh hne mass2 quartic vacuum t u = f := by
  have h := KFCausalAveragedEnergyGraph.averagedOperator_domain (H := Hilbert) (E := BaseSpace) (K := Output (Fin 8) Hilbert) U T J A
    (KFCausalClosedGraphForm.embedding_injective 𝒟) f
  exact h

theorem orbit_lift_ae (u : AveragedSpace ε hε hbar hh hne mass2 quartic vacuum t) :
    ∀ᵐ θ ∂angleMeasure,
      J (sectionMap ε hε hbar hh hne mass2 quartic vacuum t u θ) =
        action hbar hne (T*θ) (embedding ε hε hbar hh hne mass2 quartic vacuum t u) := by
  have h := KFCausalAveragedFormSpace.compatibility_ae (H := Hilbert) (E := BaseSpace) U T J
  exact h u

theorem energy_integral (u : AveragedSpace ε hε hbar hh hne mass2 quartic vacuum t) :
    ‖energyOutput ε hε hbar hh hne mass2 quartic vacuum t u‖^2 =
      ∫ θ, ‖A (sectionMap ε hε hbar hh hne mass2 quartic vacuum t u θ)‖^2 ∂angleMeasure := by
  have h := KFCausalAveragedEnergyGraph.output_energy_integral (H := Hilbert) (E := BaseSpace) (K := Output (Fin 8) Hilbert) U T J A
  exact h u

theorem graph_norm_identity (u : AveragedSpace ε hε hbar hh hne mass2 quartic vacuum t) :
    ‖u‖^2 = 2*‖embedding ε hε hbar hh hne mass2 quartic vacuum t u‖^2 +
      ‖energyOutput ε hε hbar hh hne mass2 quartic vacuum t u‖^2 := by
  have h := KFCausalAveragedEnergyGraph.form_energy_identity (H := Hilbert) (E := BaseSpace) (K := Output (Fin 8) Hilbert) U T J A
  have hJA := KFCausalClosedGraphForm.form_norm_identity 𝒟
  exact h hJA u

theorem projected_embedding (u : AveragedSpace ε hε hbar hh hne mass2 quartic vacuum t) :
    embedding ε hε hbar hh hne mass2 quartic vacuum t
      (projectedForm ε hε hbar hh hne mass2 quartic vacuum t u) =
        zeroProjection hbar hne (embedding ε hε hbar hh hne mass2 quartic vacuum t u) := rfl

theorem projected_energy_le (u : AveragedSpace ε hε hbar hh hne mass2 quartic vacuum t) :
    ‖energyOutput ε hε hbar hh hne mass2 quartic vacuum t
      (projectedForm ε hε hbar hh hne mass2 quartic vacuum t u)‖^2 ≤
        ‖energyOutput ε hε hbar hh hne mass2 quartic vacuum t u‖^2 := by
  have h := KFCausalAveragedFormProjection.project_energy_le (H := Hilbert) (E := BaseSpace) (K := Output (Fin 8) Hilbert) U T (by positivity)
    (action_full_period hbar hne) J A
  exact h u

theorem zeroProjection_mem_energy_domain (f : Hilbert)
    (hf : f ∈ (energyOperator ε hε hbar hh hne mass2 quartic vacuum t).domain) :
    zeroProjection hbar hne f ∈ (energyOperator ε hε hbar hh hne mass2 quartic vacuum t).domain := by
  rcases (energy_domain ε hε hbar hh hne mass2 quartic vacuum t f).mp hf with ⟨u, rfl⟩
  apply (energy_domain ε hε hbar hh hne mass2 quartic vacuum t _).mpr
  exact ⟨projectedForm ε hε hbar hh hne mass2 quartic vacuum t u, rfl⟩

theorem zero_sector_energy_domain (f : Hilbert) (hf : f ∈ zeroSector hbar hne) :
    f ∈ (energyOperator ε hε hbar hh hne mass2 quartic vacuum t).domain ↔ f ∈ (J).range := by
  have h1 := KFCausalAveragedEnergyGraph.averagedOperator_domain (H := Hilbert) (E := BaseSpace) (K := Output (Fin 8) Hilbert) U T J A
    (KFCausalClosedGraphForm.embedding_injective 𝒟) f
  have h2 := KFCausalAveragedFormSpace.fixed_mem_domain_iff (H := Hilbert) (E := BaseSpace) U T J (by positivity) f hf
  exact h1.trans h2

theorem projected_charge_zero (u : AveragedSpace ε hε hbar hh hne mass2 quartic vacuum t) :
    (embedding ε hε hbar hh hne mass2 quartic vacuum t
      (projectedForm ε hε hbar hh hne mass2 quartic vacuum t u), 0) ∈
        (standingCharge hbar hne).graph :=
  standingCharge_projection_zero hbar hne _

theorem common_zero_mem_energy_domain (f : Hilbert) (hf : f ∈ zeroSector hbar hne)
    (hc : f ∈ KFCausalClockFloorCommonDomain.commonEnergyDomain ε hε hbar
      KFCausalPhysicalEnergyFactors.modelDirections KFCausalMatterOrderedDomain.pointField) :
    f ∈ (energyOperator ε hε hbar hh hne mass2 quartic vacuum t).domain := by
  apply (zero_sector_energy_domain ε hε hbar hh hne mass2 quartic vacuum t f hf).mpr
  exact ⟨KFCausalClockFloorFormHamiltonian.commonFormVector ε hε hbar hh mass2 quartic vacuum t ⟨f,hc⟩,rfl⟩

theorem exists_unit_charge_zero_energy (hbound : |hbar| ≤ 2*Real.pi*ε/3) :
    ∃ f : Hilbert, ‖f‖ = 1 ∧ f ∈ zeroSector hbar hne ∧
      f ∈ (energyOperator ε hε hbar hh hne mass2 quartic vacuum t).domain ∧
      (f,0) ∈ (standingCharge hbar hne).graph := by
  obtain ⟨f,hn,hz,hc,hQ⟩ := KFCausalClockFloorCommonDomain.exists_unit_charge_zero_common
    ε hbar hε hne hbound KFCausalPhysicalEnergyFactors.modelDirections KFCausalMatterOrderedDomain.pointField
  exact ⟨f,hn,hz,common_zero_mem_energy_domain ε hε hbar hh hne mass2 quartic vacuum t f hz hc,hQ⟩

#print axioms common_zero_mem_energy_domain
#print axioms exists_unit_charge_zero_energy
#print axioms embedding_injective
#print axioms energy_closed
#print axioms energy_domain
#print axioms orbit_lift_ae
#print axioms energy_integral
#print axioms graph_norm_identity
#print axioms projected_embedding
#print axioms projected_energy_le
#print axioms zeroProjection_mem_energy_domain
#print axioms zero_sector_energy_domain
#print axioms projected_charge_zero

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
