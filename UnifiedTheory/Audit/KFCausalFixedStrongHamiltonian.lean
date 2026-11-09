/- A zero-charge state with actual forward and reverse factor graphs
belongs to the strong averaged Hamiltonian domain. The output is the
charge projection of the weighted sum of second factor outputs. -/
import UnifiedTheory.Audit.KFCausalEnergyReverseFactors
import UnifiedTheory.Audit.KFCausalFixedCommonEnergyPairing
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalFixedStrongHamiltonian
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalStandingChargeOperator (zeroSector zeroProjection zeroProjection_selfAdjoint)
open KFCausalPhysicalCircleAction (group)
open KFCausalPhysicalEnergyFactors (modelDirections energyWeight)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalFixedCommonEnergyPairing (fixedLift fixed_orbit_graph)
open KFCausalClockFloorAveragedEnergy
open KFCausalClockFloorAveragedHamiltonian (hamiltonian hamiltonian_domain_characterization)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalProbabilityL2Mean (mean mean_comp)
open KFCausalJointSecondPairing (weighted secondWeighted joint_closure_pairing)
open KFCausalEnergyReverseFactors (reverseFactor factor_pairing)

section Abstract
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (D₀ : KFCausalClosedGraphForm.Data H K)
  (U : KFCausalUnitaryOrbitAverage.StrongUnitaryGroup H) (T : ℝ) (hT : T ≠ 0)
local notation "J₀" => KFCausalClosedGraphForm.embedding D₀
local notation "A₀" => KFCausalClosedGraphForm.energyOutput D₀
local notation "Full₀" => KFCausalAveragedFormSpace.FormSpace U T J₀
local notation "out₀" => KFCausalAveragedFormProjection.averagedOutput U T J₀ A₀

include hT in
private theorem graph_averaged_pairing (u v : Full₀) (q : K) (z : H)
    (hu : out₀ u = Lp.const 2 angleMeasure q)
    (hz : ∀ x : KFCausalClosedGraphForm.FormSpace D₀,
      inner ℂ q (A₀ x) = inner ℂ z (J₀ x)) :
    inner ℂ (out₀ u) (out₀ v) = inner ℂ z
      (KFCausalUnitaryOrbitAverage.average U (KFCausalAveragedFormSpace.embedding U T J₀ v) T) := by
  have hm := mean_comp angleMeasure A₀ (KFCausalAveragedFormSpace.sectionMap U T J₀ v)
  calc
    _ = inner ℂ (Lp.const 2 angleMeasure q) (out₀ v) :=
      congrArg (fun x : Lp K 2 angleMeasure => inner ℂ x (out₀ v)) hu
    _ = inner ℂ q (mean angleMeasure (out₀ v)) :=
      ((Lp.constL 2 angleMeasure ℂ : K →L[ℂ] Lp K 2 angleMeasure).adjoint_inner_right _ _).symm
    _ = inner ℂ q (A₀ (KFCausalAveragedFormSpace.meanLift U T J₀ v)) :=
      congrArg (inner ℂ q) hm
    _ = inner ℂ z (J₀ (KFCausalAveragedFormSpace.meanLift U T J₀ v)) := hz _
    _ = _ := congrArg (inner ℂ z)
      (KFCausalAveragedFormSpace.embedding_meanLift U T J₀ hT v)
end Abstract

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (mass2 quartic vacuum t : ℝ)
local notation "hp" => hamiltonian_bound ε h hb
local notation "D" => KFCausalClockFloorFormHamiltonian.formData ε hε h hp mass2 quartic vacuum t
local notation "Base" => KFCausalClosedGraphForm.FormSpace D
local notation "J" => KFCausalClosedGraphForm.embedding D
local notation "A" => KFCausalClosedGraphForm.energyOutput D
local notation "Full" => AveragedSpace ε hε h hp hh mass2 quartic vacuum t
local notation "embed" => embedding ε hε h hp hh mass2 quartic vacuum t
local notation "out" => energyOutput ε hε h hp hh mass2 quartic vacuum t
local notation "F" => energyFactor ε hε h modelDirections pointField
local notation "R" => reverseFactor ε hε h modelDirections pointField
local notation "c" => energyWeight mass2 quartic vacuum t

variable (f : Hilbert) (hf : f ∈ zeroSector h hh) (g z : Fin 8 → Hilbert)
  (hg : ∀ i, (f,g i) ∈
    (energyFactor ε hε h modelDirections pointField i).graph)
  (hz : ∀ i, (g i,z i) ∈
    (reverseFactor ε hε h modelDirections pointField i).graph)

include hg in
theorem fixed_output :
    out (fixedLift ε h hε hh hb mass2 quartic vacuum t f hf g hg) =
      Lp.const 2 angleMeasure (weighted c g) := by
  apply Lp.ext
  filter_upwards [KFCausalCoherentMomentumEnergyLift.lift_output_coe
    ε h hε hh hb mass2 quartic vacuum t f (fun i _ => g i) (fun _ => continuous_const)
      (fixed_orbit_graph ε h hε hh f hf g hg),
    Lp.coeFn_const 2 angleMeasure (weighted c g)] with θ hθ hc
  exact hθ.trans hc.symm

include hz in
theorem base_pairing (v : Base) :
    inner ℂ (weighted c g) (A v) = inner ℂ (secondWeighted c z) (J v) := by
  have hv : (J v,A v) ∈
      (KFCausalClockFloorJointEnergy.closedEnergy ε hε h modelDirections pointField mass2 quartic vacuum t).graph :=
    v.property
  rw [KFCausalClockFloorJointEnergy.closedEnergy_graph ε hε h modelDirections pointField
    mass2 quartic vacuum t hp] at hv
  exact joint_closure_pairing F c g z
    (fun i v w hvw => factor_pairing ε hε h modelDirections pointField i _ _ v w (hz i) hvw) _ _ hv

include hg hz in
theorem averaged_pairing (v : Full) :
    inner ℂ (out (fixedLift ε h hε hh hb mass2 quartic vacuum t f hf g hg)) (out v) =
      inner ℂ (zeroProjection h hh (secondWeighted c z)) (embed v) := by
  have hc := graph_averaged_pairing D (group h hh) (2*Real.pi) (by positivity)
    (fixedLift ε h hε hh hb mass2 quartic vacuum t f hf g hg) v (weighted c g) (secondWeighted c z)
    (fixed_output ε h hε hh hb mass2 quartic vacuum t f hf g hg)
    (base_pairing ε h hε hb mass2 quartic vacuum t g z hz)
  exact hc.trans (((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (zeroProjection_selfAdjoint h hh)) (secondWeighted c z) (embed v)).symm)

include hf hg hz in
theorem hamiltonian_graph :
    (f,zeroProjection h hh (secondWeighted c z)) ∈
      (hamiltonian ε hε h hh hb mass2 quartic vacuum t).graph := by
  have hs := (hamiltonian_domain_characterization ε hε h hh hb mass2 quartic vacuum t
    (fixedLift ε h hε hh hb mass2 quartic vacuum t f hf g hg)
    (zeroProjection h hh (secondWeighted c z))).mpr
      (averaged_pairing ε h hε hh hb mass2 quartic vacuum t f hf g z hg hz)
  obtain ⟨hd,hvalue⟩ := hs
  exact ((hamiltonian ε hε h hh hb mass2 quartic vacuum t).mem_graph_iff').mpr
    ⟨⟨_,hd⟩,Prod.ext rfl hvalue⟩

include hf hg hz in
theorem hamiltonian_domain : f ∈ (hamiltonian ε hε h hh hb mass2 quartic vacuum t).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (hamiltonian_graph ε h hε hh hb mass2 quartic vacuum t f hf g z hg hz)

#print axioms fixed_output
#print axioms base_pairing
#print axioms averaged_pairing
#print axioms hamiltonian_graph
#print axioms hamiltonian_domain
end
end UnifiedTheory.Audit.KFCausalFixedStrongHamiltonian
