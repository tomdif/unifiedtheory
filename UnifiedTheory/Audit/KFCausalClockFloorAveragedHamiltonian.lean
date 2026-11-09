/- A fixed-time positive self-adjoint Hamiltonian for the actual averaged
clock-floor energy. Density is proved by the coherent family, not assumed.
The representing form is the integral of the original ordered-factor
energy. This is not a time-dependent propagator or a regulator limit. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalClockFloorAveragedDensity (energy_domain_dense)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
  (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ)

local notation "hb" => hamiltonian_bound ε hbar hbound
local notation "BaseData" => KFCausalClockFloorFormHamiltonian.formData ε hε hbar hb mass2 quartic vacuum t

def formData : KFCausalClosedGraphForm.Data Hilbert (Lp (Output (Fin 8) Hilbert) 2 angleMeasure) where
  operator := energyOperator ε hε hbar hb hh mass2 quartic vacuum t
  closed := energy_closed ε hε hbar hb hh mass2 quartic vacuum t
  dense := energy_domain_dense ε hbar hε hh hbound mass2 quartic vacuum t

local notation "𝒟" => formData ε hε hbar hh hbound mass2 quartic vacuum t

def hamiltonian : Hilbert →ₗ.[ℂ] Hilbert := KFCausalClosedGraphForm.hamiltonian 𝒟

theorem hamiltonian_selfAdjoint : IsSelfAdjoint (hamiltonian ε hε hbar hh hbound mass2 quartic vacuum t) :=
  KFCausalClosedGraphForm.hamiltonian_selfAdjoint 𝒟

theorem hamiltonian_closed : (hamiltonian ε hε hbar hh hbound mass2 quartic vacuum t).IsClosed :=
  KFCausalClosedGraphForm.hamiltonian_closed 𝒟

theorem hamiltonian_dense : Dense ((hamiltonian ε hε hbar hh hbound mass2 quartic vacuum t).domain : Set Hilbert) :=
  KFCausalClosedGraphForm.hamiltonian_dense 𝒟

theorem hamiltonian_positive (x : (hamiltonian ε hε hbar hh hbound mass2 quartic vacuum t).domain) :
    0 ≤ (inner ℂ (hamiltonian ε hε hbar hh hbound mass2 quartic vacuum t x) (x:Hilbert)).re :=
  KFCausalClosedGraphForm.hamiltonian_positive 𝒟 x

def graphFormVector (u : AveragedSpace ε hε hbar hb hh mass2 quartic vacuum t) :
    KFCausalClosedGraphForm.FormSpace 𝒟 :=
  ⟨WithLp.toLp 2 (embedding ε hε hbar hb hh mass2 quartic vacuum t u,
    energyOutput ε hε hbar hb hh mass2 quartic vacuum t u),
    KFCausalAveragedEnergyGraph.averagedOperator_form_graph _ _ _ _
      (KFCausalClosedGraphForm.embedding_injective BaseData) u⟩

theorem graphFormVector_embedding (u : AveragedSpace ε hε hbar hb hh mass2 quartic vacuum t) :
    KFCausalClosedGraphForm.embedding 𝒟 (graphFormVector ε hε hbar hh hbound mass2 quartic vacuum t u) =
      embedding ε hε hbar hb hh mass2 quartic vacuum t u := rfl

theorem graphFormVector_output (u : AveragedSpace ε hε hbar hb hh mass2 quartic vacuum t) :
    KFCausalClosedGraphForm.energyOutput 𝒟 (graphFormVector ε hε hbar hh hbound mass2 quartic vacuum t u) =
      energyOutput ε hε hbar hb hh mass2 quartic vacuum t u := rfl

theorem graphFormVector_surjective : Function.Surjective (graphFormVector ε hε hbar hh hbound mass2 quartic vacuum t) := by
  intro v
  have hf : KFCausalClosedGraphForm.embedding 𝒟 v ∈
      (energyOperator ε hε hbar hb hh mass2 quartic vacuum t).domain :=
    LinearPMap.mem_domain_iff.mpr ⟨KFCausalClosedGraphForm.energyOutput 𝒟 v,v.property⟩
  have hv := (energy_domain ε hε hbar hb hh mass2 quartic vacuum t _).mp hf
  rcases hv with ⟨u,hu⟩
  refine ⟨u,?_⟩
  exact KFCausalClosedGraphForm.embedding_injective 𝒟 hu

theorem hamiltonian_represents_averaged_form
    (x : (hamiltonian ε hε hbar hh hbound mass2 quartic vacuum t).domain)
    (u : AveragedSpace ε hε hbar hb hh mass2 quartic vacuum t) :
    inner ℂ (KFCausalClosedGraphForm.energyOutput 𝒟 (KFCausalClosedGraphForm.formLift 𝒟 x))
      (energyOutput ε hε hbar hb hh mass2 quartic vacuum t u) =
        inner ℂ (hamiltonian ε hε hbar hh hbound mass2 quartic vacuum t x)
          (embedding ε hε hbar hb hh mass2 quartic vacuum t u) :=
  KFCausalClosedGraphForm.hamiltonian_represents_form 𝒟 x
    (graphFormVector ε hε hbar hh hbound mass2 quartic vacuum t u)

theorem hamiltonian_integrated_energy
    (x : (hamiltonian ε hε hbar hh hbound mass2 quartic vacuum t).domain) :
    ∃ u : AveragedSpace ε hε hbar hb hh mass2 quartic vacuum t,
      embedding ε hε hbar hb hh mass2 quartic vacuum t u = (x:Hilbert) ∧
        (inner ℂ (hamiltonian ε hε hbar hh hbound mass2 quartic vacuum t x) (x:Hilbert)).re =
          ∫ θ, ‖KFCausalClosedGraphForm.energyOutput BaseData
            (sectionMap ε hε hbar hb hh mass2 quartic vacuum t u θ)‖^2 ∂angleMeasure := by
  have hs := graphFormVector_surjective ε hε hbar hh hbound mass2 quartic vacuum t
    (KFCausalClosedGraphForm.formLift 𝒟 x)
  rcases hs with ⟨u,hu⟩
  refine ⟨u,?_,?_⟩
  · exact (congrArg (KFCausalClosedGraphForm.embedding 𝒟) hu).trans
      (KFCausalClosedGraphForm.embedding_formLift 𝒟 x)
  · have he := congrArg (fun v : KFCausalClosedGraphForm.FormSpace 𝒟 =>
      ‖KFCausalClosedGraphForm.energyOutput 𝒟 v‖^2) hu.symm
    exact (KFCausalClosedGraphForm.hamiltonian_energy 𝒟 x).trans
      (he.trans (energy_integral ε hε hbar hb hh mass2 quartic vacuum t u))

theorem hamiltonian_domain_characterization (u : AveragedSpace ε hε hbar hb hh mass2 quartic vacuum t) (y : Hilbert) :
    (∃ hx : embedding ε hε hbar hb hh mass2 quartic vacuum t u ∈
        (hamiltonian ε hε hbar hh hbound mass2 quartic vacuum t).domain,
      hamiltonian ε hε hbar hh hbound mass2 quartic vacuum t
        ⟨embedding ε hε hbar hb hh mass2 quartic vacuum t u,hx⟩ = y) ↔
      ∀ v : AveragedSpace ε hε hbar hb hh mass2 quartic vacuum t,
        inner ℂ (energyOutput ε hε hbar hb hh mass2 quartic vacuum t u)
          (energyOutput ε hε hbar hb hh mass2 quartic vacuum t v) =
            inner ℂ y (embedding ε hε hbar hb hh mass2 quartic vacuum t v) := by
  have h := KFCausalClosedGraphForm.hamiltonian_domain_characterization 𝒟
    (graphFormVector ε hε hbar hh hbound mass2 quartic vacuum t u) y
  refine h.trans ?_
  constructor
  · intro hp v
    exact hp (graphFormVector ε hε hbar hh hbound mass2 quartic vacuum t v)
  · intro hp v
    have hs := graphFormVector_surjective ε hε hbar hh hbound mass2 quartic vacuum t v
    rcases hs with ⟨w,hw⟩
    exact (congrArg (fun z : KFCausalClosedGraphForm.FormSpace 𝒟 =>
      inner ℂ (KFCausalClosedGraphForm.energyOutput 𝒟
        (graphFormVector ε hε hbar hh hbound mass2 quartic vacuum t u))
        (KFCausalClosedGraphForm.energyOutput 𝒟 z) = inner ℂ y (KFCausalClosedGraphForm.embedding 𝒟 z)) hw).mp (hp w)

#print axioms hamiltonian_selfAdjoint
#print axioms hamiltonian_closed
#print axioms hamiltonian_dense
#print axioms hamiltonian_positive
#print axioms graphFormVector_embedding
#print axioms graphFormVector_output
#print axioms graphFormVector_surjective
#print axioms hamiltonian_represents_averaged_form
#print axioms hamiltonian_integrated_energy
#print axioms hamiltonian_domain_characterization

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian
