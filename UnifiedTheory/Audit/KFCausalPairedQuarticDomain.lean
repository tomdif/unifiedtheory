/- The corrected quartic tensor state equals an explicit sum of
directional source states. Its actual pure-clock momentum and all
eight state/momentum factor graphs follow from proved graph linearity. -/
import UnifiedTheory.Audit.KFCausalPairedQuarticPolarization
import UnifiedTheory.Audit.KFCausalPairedQuarticCharge
import UnifiedTheory.Audit.KFCausalDirectionalClockComposition
import UnifiedTheory.Audit.KFCausalPureClockZeroProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalPairedQuarticDomain
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalPairedQuarticPolarization
open KFCausalPairedQuarticCharge (correctedState corrected_configuration_coe corrected_zeroSector)
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalClockFloorInvariantTrial (neutralWidth clockFunction)
open KFCausalChargeGaussianIdentities (configurationProfile)
open KFCausalQuarticChargeProfiles (quarticPolynomial)
open KFCausalClockFloorCommonDomain (energyFactor commonEnergyDomain commonEnergyDomain_iff)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalStandingChargeOperator (zeroSector standingCharge standingCharge_zero_iff)
open KFCausalFiniteLpRepresentatives (sum_coe)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorPureClockKinetic (correction)

theorem directional_profile (α β : ℝ) (g : ℝ → ℂ) (C : ℂ) (d : Transverse)
    (n : ℕ) (x : Configuration) :
    KFCausalDirectionalGaussianStates.profile C 0 α β g d n x =
      (C*(KFCausalDirectionalGaussianStates.linearForm d x.2:ℂ)^n)*
        configurationProfile α β g x := by
  simp only [KFCausalDirectionalGaussianStates.profile,
    KFCausalClockFloorCoherentDerivative.physicalProfile,
    KFCausalClockFloorCoherentDerivative.clockMultiplier,
    KFCausalClockFloorCoherentMoments.sourcedPacket,
    KFCausalClockFloorCoherentSources.linearSource,
    KFCausalClockFloorCoherentStrip.clockPhase,Pi.zero_apply,Complex.ofReal_zero,zero_mul,
    Finset.sum_const_zero,Complex.exp_zero,one_mul]
  unfold configurationProfile
  ring

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
local notation "α" => groundWidth h
local notation "ψ" => correctedState ε a h hε ha hh

def polarizedState : Hilbert := ∑ i : Fin 21,
  KFCausalDirectionalGaussianDomain.input ε a h hε ha hh
    (coefficients α i) 0 (directions i) (degrees i)
def momentum : Hilbert := ∑ i : Fin 21,
  KFCausalDirectionalClockMomentum.momentum ε a h hε ha hh
    0 (directions i) (coefficients α i) (degrees i)

theorem polarizedState_coe :
    polarizedState ε a h hε ha hh =ᵐ[volume] fun x =>
      (quarticPolynomial α x.2:ℂ)*configurationProfile α (neutralWidth h) (clockFunction ε a) x := by
  have hs := sum_coe volume Finset.univ (fun i : Fin 21 =>
    KFCausalDirectionalGaussianDomain.input ε a h hε ha hh
      (coefficients α i) 0 (directions i) (degrees i))
  have hi := ae_all_iff.mpr (fun i : Fin 21 =>
    KFCausalDirectionalGaussianDomain.input_coe ε a h hε ha hh
      (coefficients α i) 0 (directions i) (degrees i))
  filter_upwards [hs,hi] with x hx hy
  change (∑ i : Fin 21, KFCausalDirectionalGaussianDomain.input ε a h hε ha hh
    (coefficients α i) 0 (directions i) (degrees i) : Hilbert) x = _
  rw [hx]
  simp_rw [hy,directional_profile]
  rw [← Finset.sum_mul,polarization]

theorem polarizedState_eq : polarizedState ε a h hε ha hh = ψ := by
  apply Lp.ext
  exact (polarizedState_coe ε a h hε ha hh).trans
    (corrected_configuration_coe ε a h hε ha hh).symm

theorem momentum_graph : (ψ,momentum ε a h hε ha hh) ∈ (pureMomentum ε hε h).graph := by
  have hs := (pureMomentum ε hε h).graph.sum_mem
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 21))) =>
      KFCausalDirectionalClockMomentum.momentum_graph ε a h hε ha hh
        0 (directions i) (coefficients α i) (degrees i))
  have he : (polarizedState ε a h hε ha hh,momentum ε a h hε ha hh) ∈
      (pureMomentum ε hε h).graph := by
    simpa only [polarizedState,momentum,← prod_mk_sum] using hs
  rwa [polarizedState_eq] at he

theorem momentum_zeroSector : momentum ε a h hε ha hh ∈ zeroSector h hh :=
  KFCausalPureClockZeroProjection.output_zeroSector ε hε h hh _ _
    (momentum_graph ε a h hε ha hh) (corrected_zeroSector ε a h hε ha hh)

theorem momentum_charge_zero :
    (momentum ε a h hε ha hh,0) ∈ (standingCharge h hh).graph :=
  (standingCharge_zero_iff h hh _).mpr (momentum_zeroSector ε a h hε ha hh)

variable (hb : |h| ≤ 2*Real.pi*ε/3)
  (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ)

def output (j : Fin 8) : Hilbert := ∑ i : Fin 21,
  KFCausalDirectionalGaussianDomain.output ε a h hε ha hh
    (coefficients α i) 0 (directions i) (degrees i) hb v l j
def momentumOutput (j : Fin 8) : Hilbert := ∑ i : Fin 21,
  KFCausalDirectionalClockMomentum.factor ε a h hε ha hh
    0 (directions i) (coefficients α i) hb (degrees i) v l j

theorem output_graph (j : Fin 8) :
    (ψ,output ε a h hε ha hh hb v l j) ∈ (energyFactor ε hε h v l j).graph := by
  have hs := (energyFactor ε hε h v l j).graph.sum_mem
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 21))) =>
      KFCausalDirectionalGaussianDomain.output_graph ε a h hε ha hh
        (coefficients α i) 0 (directions i) (degrees i) hb v l j)
  have he : (polarizedState ε a h hε ha hh,output ε a h hε ha hh hb v l j) ∈
      (energyFactor ε hε h v l j).graph := by
    simpa only [polarizedState,output,← prod_mk_sum] using hs
  rwa [polarizedState_eq] at he

theorem momentumOutput_graph (j : Fin 8) :
    (momentum ε a h hε ha hh,momentumOutput ε a h hε ha hh hb v l j) ∈
      (energyFactor ε hε h v l j).graph := by
  have hs := (energyFactor ε hε h v l j).graph.sum_mem
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 21))) =>
      KFCausalDirectionalClockMomentum.factor_graph ε a h hε ha hh
        0 (directions i) (coefficients α i) hb (degrees i) v l j)
  simpa only [momentum,momentumOutput,← prod_mk_sum] using hs

include hb in
theorem common_domains :
    ψ ∈ commonEnergyDomain ε hε h v l ∧
      momentum ε a h hε ha hh ∈ commonEnergyDomain ε hε h v l :=
  ⟨(commonEnergyDomain_iff ε hε h v l _).mpr fun j =>
      LinearPMap.mem_domain_of_mem_graph (output_graph ε a h hε ha hh hb v l j),
    (commonEnergyDomain_iff ε hε h v l _).mpr fun j =>
      LinearPMap.mem_domain_of_mem_graph (momentumOutput_graph ε a h hε ha hh hb v l j)⟩

theorem clock_composition_graph :
    (output ε a h hε ha hh hb modelDirections pointField 0,
      momentumOutput ε a h hε ha hh hb modelDirections pointField 0 -
        correction ε hε h (output ε a h hε ha hh hb modelDirections pointField 0)) ∈
      (pureMomentum ε hε h).graph := by
  have hs := (pureMomentum ε hε h).graph.sum_mem
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 21))) =>
      KFCausalDirectionalClockComposition.composition_graph ε a h hε ha hh hb
        (coefficients α i) 0 (directions i) (degrees i))
  simpa only [output,momentumOutput,← prod_mk_sum,Finset.sum_sub_distrib,map_sum] using hs

#print axioms directional_profile
#print axioms polarizedState_coe
#print axioms polarizedState_eq
#print axioms momentum_graph
#print axioms momentum_zeroSector
#print axioms momentum_charge_zero
#print axioms output_graph
#print axioms momentumOutput_graph
#print axioms common_domains
#print axioms clock_composition_graph
end
end UnifiedTheory.Audit.KFCausalPairedQuarticDomain
