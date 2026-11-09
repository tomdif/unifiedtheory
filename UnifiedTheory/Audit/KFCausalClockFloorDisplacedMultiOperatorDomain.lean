/- Every ambient displaced Gaussian state with zero clock displacement belongs
to the unconditional common operator domain
(Dom T ∩ Dom Kr ∩ Dom P) ∩ Dom Tres(0) (as well as Dom clockHalf) for all real
couplings m, g, κ, and therefore simultaneously to the domains of T, Kr, P, G,
S(t), H(t), and Tres(0) at every time t, satisfying the exact three-operator
decomposition H(t)ψ = Tψ + e^{2t}(Krψ + Pψ) and two-time evolution identities
H(t)ψ - H(s)ψ = (e^{2t} - e^{2s})(Krψ + Pψ) and S(t)ψ - S(s)ψ = (e^{2t} - e^{2s})Pψ. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedSecondDomain
import UnifiedTheory.Audit.KFCausalClockFloorUnconditionalTwoTimeEvolution

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedMultiOperatorDomain
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorCommonDomain (commonEnergyDomain_iff)
open KFCausalClockFloorDisplacedStates (rawState state state_normalization)
open KFCausalClockFloorDisplacedCommonDomain (rawState_commonEnergyDomain state_commonEnergyDomain)
open KFCausalClockFloorDisplacedSecondDomain
  (hamiltonianOutput hamiltonian_graph hamiltonian_domain growing_domain)
open KFCausalClockFloorUnconditionalThreeOperatorDecomposition
  (unconditional_three_operator_residual_graph
   unconditional_three_operator_hamiltonian_graph
   unconditional_static_growing_hamiltonian_graph
   hamiltonian_growing_common_domain_eq)
open KFCausalClockFloorUnconditionalTwoTimeEvolution
  (commonOperatorDomain common_domain_subset_hamiltonian common_domain_subset_residual
   common_domain_subset_growing unconditional_two_time_residual_difference
   unconditional_two_time_hamiltonian_growing_difference
   unconditional_two_time_hamiltonian_three_operator_difference)

theorem mem_commonOperatorDomain_of_mem_hamiltonian_and_growing
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ Real.pi * ε / 3) (m g κ t : ℝ) (x : Hilbert)
    (hH : x ∈ (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh
      (KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb) m g κ t).domain)
    (hG : x ∈ (KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh
      (KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb) m g κ).domain) :
    x ∈ commonOperatorDomain ε hε h hh hb m g κ := by
  change x ∈ (((KFCausalClockFloorStaticOperator.operator ε hε h).domain ⊓
    (KFCausalClockFloorRadialYosidaDomain.operator ε hε h).domain ⊓
    (KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh
      (KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb) m g κ).domain) ⊓
    (KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh
      (KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb) m g κ 0).domain)
  rw [← hamiltonian_growing_common_domain_eq ε hε h hh hb m g κ t]
  exact ⟨hH, hG⟩

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (q k : Joint 2 4) (hq : q (.inr 0) = 0)
local notation "hw" => KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "Kr" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "Pot" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw
local notation "Grow" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw
local notation "Res" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw
local notation "FullH" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw

include hq in
theorem rawState_mem_commonOperatorDomain (m g κ : ℝ) :
    rawState ε a h hε ha hh q k ∈ commonOperatorDomain ε hε h hh hb m g κ :=
  mem_commonOperatorDomain_of_mem_hamiltonian_and_growing ε hε h hh hb m g κ 0
    (rawState ε a h hε ha hh q k)
    (hamiltonian_domain ε a h hε ha hh hb q k hq m g κ 0)
    (growing_domain ε a h hε ha hh hb q k hq m g κ)

include hb hq in
theorem rawState_static_domain :
    rawState ε a h hε ha hh q k ∈ (T).domain :=
  (rawState_mem_commonOperatorDomain ε a h hε ha hh hb q k hq 0 0 0).1.1.1

include hb hq in
theorem rawState_radial_domain :
    rawState ε a h hε ha hh q k ∈ (Kr).domain :=
  (rawState_mem_commonOperatorDomain ε a h hε ha hh hb q k hq 0 0 0).1.1.2

include hq in
theorem rawState_potential_domain (m g κ : ℝ) :
    rawState ε a h hε ha hh q k ∈ (Pot m g κ).domain :=
  (rawState_mem_commonOperatorDomain ε a h hε ha hh hb q k hq m g κ).1.2

include hq in
theorem rawState_residual_form_domain (m g κ : ℝ) :
    rawState ε a h hε ha hh q k ∈ (Tres m g κ 0).domain :=
  (rawState_mem_commonOperatorDomain ε a h hε ha hh hb q k hq m g κ).2

include hq in
theorem rawState_residual_domain (m g κ t : ℝ) :
    rawState ε a h hε ha hh q k ∈ (Res m g κ t).domain :=
  common_domain_subset_residual ε hε h hh hb m g κ t
    (rawState_mem_commonOperatorDomain ε a h hε ha hh hb q k hq m g κ)

include hb hq in
theorem rawState_clockHalf_domain :
    rawState ε a h hε ha hh q k ∈ (clockHalf ε).domain :=
  (commonEnergyDomain_iff ε hε h modelDirections pointField _).mp
    (rawState_commonEnergyDomain ε a h hε ha hh hw q k hq modelDirections pointField) 0

def rawStaticPoint : (T).domain :=
  ⟨rawState ε a h hε ha hh q k, rawState_static_domain ε a h hε ha hh hb q k hq⟩

def rawRadialPoint : (Kr).domain :=
  ⟨rawState ε a h hε ha hh q k, rawState_radial_domain ε a h hε ha hh hb q k hq⟩

def rawPotentialPoint (m g κ : ℝ) : (Pot m g κ).domain :=
  ⟨rawState ε a h hε ha hh q k, rawState_potential_domain ε a h hε ha hh hb q k hq m g κ⟩

def rawGrowingPoint (m g κ : ℝ) : (Grow m g κ).domain :=
  ⟨rawState ε a h hε ha hh q k, growing_domain ε a h hε ha hh hb q k hq m g κ⟩

def rawResidualPoint (m g κ t : ℝ) : (Res m g κ t).domain :=
  ⟨rawState ε a h hε ha hh q k, rawState_residual_domain ε a h hε ha hh hb q k hq m g κ t⟩

def rawHamiltonianPoint (m g κ t : ℝ) : (FullH m g κ t).domain :=
  ⟨rawState ε a h hε ha hh q k, hamiltonian_domain ε a h hε ha hh hb q k hq m g κ t⟩

theorem rawState_growing_decomposition (m g κ : ℝ) :
    Grow m g κ (rawGrowingPoint ε a h hε ha hh hb q k hq m g κ) =
      (Kr) (rawRadialPoint ε a h hε ha hh hb q k hq) +
      (Pot m g κ) (rawPotentialPoint ε a h hε ha hh hb q k hq m g κ) := by
  have hmem : (rawState ε a h hε ha hh q k,
      (Kr) (rawRadialPoint ε a h hε ha hh hb q k hq) +
      (Pot m g κ) (rawPotentialPoint ε a h hε ha hh hb q k hq m g κ)) ∈ (Grow m g κ).graph := by
    rw [KFCausalClockFloorGrowingPotentialSum.operator_sum ε hε h hh hb m g κ]
    exact (LinearPMap.mem_graph_iff _).mpr
      ⟨⟨rawState ε a h hε ha hh q k,
        ⟨rawState_radial_domain ε a h hε ha hh hb q k hq,
          rawState_potential_domain ε a h hε ha hh hb q k hq m g κ⟩⟩, rfl, rfl⟩
  exact (Grow m g κ).mem_graph_snd_inj'
    ((Grow m g κ).mem_graph (rawGrowingPoint ε a h hε ha hh hb q k hq m g κ)) hmem rfl

theorem rawState_residual_decomposition (m g κ t : ℝ) :
    Res m g κ t (rawResidualPoint ε a h hε ha hh hb q k hq m g κ t) =
      (T) (rawStaticPoint ε a h hε ha hh hb q k hq) +
      (Real.exp (2 * t) : ℂ) • (Pot m g κ) (rawPotentialPoint ε a h hε ha hh hb q k hq m g κ) :=
  (Res m g κ t).mem_graph_snd_inj'
    ((Res m g κ t).mem_graph (rawResidualPoint ε a h hε ha hh hb q k hq m g κ t))
    (unconditional_three_operator_residual_graph ε hε h hh hb m g κ t
      (rawState ε a h hε ha hh q k)
      ((T) (rawStaticPoint ε a h hε ha hh hb q k hq))
      ((Pot m g κ) (rawPotentialPoint ε a h hε ha hh hb q k hq m g κ))
      ((T).mem_graph (rawStaticPoint ε a h hε ha hh hb q k hq))
      ((Pot m g κ).mem_graph (rawPotentialPoint ε a h hε ha hh hb q k hq m g κ))
      (rawState_residual_form_domain ε a h hε ha hh hb q k hq m g κ)) rfl

theorem rawState_hamiltonian_growing_decomposition (m g κ t : ℝ) :
    FullH m g κ t (rawHamiltonianPoint ε a h hε ha hh hb q k hq m g κ t) =
      (T) (rawStaticPoint ε a h hε ha hh hb q k hq) +
      (Real.exp (2 * t) : ℂ) • Grow m g κ (rawGrowingPoint ε a h hε ha hh hb q k hq m g κ) :=
  (FullH m g κ t).mem_graph_snd_inj'
    ((FullH m g κ t).mem_graph (rawHamiltonianPoint ε a h hε ha hh hb q k hq m g κ t))
    (unconditional_static_growing_hamiltonian_graph ε hε h hh hb m g κ t
      (rawState ε a h hε ha hh q k)
      ((T) (rawStaticPoint ε a h hε ha hh hb q k hq))
      (Grow m g κ (rawGrowingPoint ε a h hε ha hh hb q k hq m g κ))
      ((T).mem_graph (rawStaticPoint ε a h hε ha hh hb q k hq))
      ((Grow m g κ).mem_graph (rawGrowingPoint ε a h hε ha hh hb q k hq m g κ))
      (rawState_residual_form_domain ε a h hε ha hh hb q k hq m g κ)) rfl

theorem rawState_three_operator_decomposition (m g κ t : ℝ) :
    FullH m g κ t (rawHamiltonianPoint ε a h hε ha hh hb q k hq m g κ t) =
      (T) (rawStaticPoint ε a h hε ha hh hb q k hq) +
      (Real.exp (2 * t) : ℂ) •
        ((Kr) (rawRadialPoint ε a h hε ha hh hb q k hq) +
          (Pot m g κ) (rawPotentialPoint ε a h hε ha hh hb q k hq m g κ)) :=
  (FullH m g κ t).mem_graph_snd_inj'
    ((FullH m g κ t).mem_graph (rawHamiltonianPoint ε a h hε ha hh hb q k hq m g κ t))
    (unconditional_three_operator_hamiltonian_graph ε hε h hh hb m g κ t
      (rawState ε a h hε ha hh q k)
      ((T) (rawStaticPoint ε a h hε ha hh hb q k hq))
      ((Kr) (rawRadialPoint ε a h hε ha hh hb q k hq))
      ((Pot m g κ) (rawPotentialPoint ε a h hε ha hh hb q k hq m g κ))
      ((T).mem_graph (rawStaticPoint ε a h hε ha hh hb q k hq))
      ((Kr).mem_graph (rawRadialPoint ε a h hε ha hh hb q k hq))
      ((Pot m g κ).mem_graph (rawPotentialPoint ε a h hε ha hh hb q k hq m g κ))
      (rawState_residual_form_domain ε a h hε ha hh hb q k hq m g κ)) rfl

include hq in
theorem hamiltonianOutput_three_operator_decomposition (m g κ t : ℝ) :
    hamiltonianOutput ε a h hε ha hh hb q k m g κ t =
      (T) (rawStaticPoint ε a h hε ha hh hb q k hq) +
      (Real.exp (2 * t) : ℂ) •
        ((Kr) (rawRadialPoint ε a h hε ha hh hb q k hq) +
          (Pot m g κ) (rawPotentialPoint ε a h hε ha hh hb q k hq m g κ)) := by
  have heq : hamiltonianOutput ε a h hε ha hh hb q k m g κ t =
      FullH m g κ t (rawHamiltonianPoint ε a h hε ha hh hb q k hq m g κ t) :=
    (FullH m g κ t).mem_graph_snd_inj'
      (hamiltonian_graph ε a h hε ha hh hb q k hq m g κ t)
      ((FullH m g κ t).mem_graph (rawHamiltonianPoint ε a h hε ha hh hb q k hq m g κ t)) rfl
  rw [heq]
  exact rawState_three_operator_decomposition ε a h hε ha hh hb q k hq m g κ t

theorem rawState_two_time_hamiltonian_growing_difference (m g κ t s : ℝ) :
    FullH m g κ t (rawHamiltonianPoint ε a h hε ha hh hb q k hq m g κ t) -
      FullH m g κ s (rawHamiltonianPoint ε a h hε ha hh hb q k hq m g κ s) =
      ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) •
        Grow m g κ (rawGrowingPoint ε a h hε ha hh hb q k hq m g κ) :=
  unconditional_two_time_hamiltonian_growing_difference ε hε h hh hb m g κ t s
    (rawState ε a h hε ha hh q k)
    (rawState_mem_commonOperatorDomain ε a h hε ha hh hb q k hq m g κ)

theorem rawState_two_time_hamiltonian_three_operator_difference (m g κ t s : ℝ) :
    FullH m g κ t (rawHamiltonianPoint ε a h hε ha hh hb q k hq m g κ t) -
      FullH m g κ s (rawHamiltonianPoint ε a h hε ha hh hb q k hq m g κ s) =
      ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) •
        ((Kr) (rawRadialPoint ε a h hε ha hh hb q k hq) +
          (Pot m g κ) (rawPotentialPoint ε a h hε ha hh hb q k hq m g κ)) :=
  unconditional_two_time_hamiltonian_three_operator_difference ε hε h hh hb m g κ t s
    (rawState ε a h hε ha hh q k)
    (rawState_mem_commonOperatorDomain ε a h hε ha hh hb q k hq m g κ)

theorem rawState_two_time_residual_difference (m g κ t s : ℝ) :
    Res m g κ t (rawResidualPoint ε a h hε ha hh hb q k hq m g κ t) -
      Res m g κ s (rawResidualPoint ε a h hε ha hh hb q k hq m g κ s) =
      ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) •
        (Pot m g κ) (rawPotentialPoint ε a h hε ha hh hb q k hq m g κ) :=
  unconditional_two_time_residual_difference ε hε h hh hb m g κ t s
    (rawState ε a h hε ha hh q k)
    (rawState_mem_commonOperatorDomain ε a h hε ha hh hb q k hq m g κ)

include hq in
theorem state_mem_commonOperatorDomain (m g κ : ℝ) :
    state ε a h hε ha hh q k ∈ commonOperatorDomain ε hε h hh hb m g κ := by
  rw [state_normalization]
  exact ((commonOperatorDomain ε hε h hh hb m g κ).restrictScalars ℝ).smul_mem _
    (rawState_mem_commonOperatorDomain ε a h hε ha hh hb q k hq m g κ)

include hb hq in
theorem state_clockHalf_domain :
    state ε a h hε ha hh q k ∈ (clockHalf ε).domain :=
  (commonEnergyDomain_iff ε hε h modelDirections pointField _).mp
    (state_commonEnergyDomain ε a h hε ha hh hw q k hq modelDirections pointField) 0

theorem state_three_operator_decomposition (m g κ t : ℝ) :
    let hmem := state_mem_commonOperatorDomain ε a h hε ha hh hb q k hq m g κ
    FullH m g κ t ⟨state ε a h hε ha hh q k,
      common_domain_subset_hamiltonian ε hε h hh hb m g κ t hmem⟩ =
      (T) ⟨state ε a h hε ha hh q k, hmem.1.1.1⟩ +
      (Real.exp (2 * t) : ℂ) •
        ((Kr) ⟨state ε a h hε ha hh q k, hmem.1.1.2⟩ +
          (Pot m g κ) ⟨state ε a h hε ha hh q k, hmem.1.2⟩) := by
  let hmem := state_mem_commonOperatorDomain ε a h hε ha hh hb q k hq m g κ
  exact (FullH m g κ t).mem_graph_snd_inj'
    ((FullH m g κ t).mem_graph ⟨state ε a h hε ha hh q k,
      common_domain_subset_hamiltonian ε hε h hh hb m g κ t hmem⟩)
    (unconditional_three_operator_hamiltonian_graph ε hε h hh hb m g κ t
      (state ε a h hε ha hh q k)
      ((T) ⟨state ε a h hε ha hh q k, hmem.1.1.1⟩)
      ((Kr) ⟨state ε a h hε ha hh q k, hmem.1.1.2⟩)
      ((Pot m g κ) ⟨state ε a h hε ha hh q k, hmem.1.2⟩)
      ((T).mem_graph ⟨state ε a h hε ha hh q k, hmem.1.1.1⟩)
      ((Kr).mem_graph ⟨state ε a h hε ha hh q k, hmem.1.1.2⟩)
      ((Pot m g κ).mem_graph ⟨state ε a h hε ha hh q k, hmem.1.2⟩)
      hmem.2) rfl

theorem state_two_time_hamiltonian_three_operator_difference (m g κ t s : ℝ) :
    let hmem := state_mem_commonOperatorDomain ε a h hε ha hh hb q k hq m g κ
    FullH m g κ t ⟨state ε a h hε ha hh q k,
      common_domain_subset_hamiltonian ε hε h hh hb m g κ t hmem⟩ -
      FullH m g κ s ⟨state ε a h hε ha hh q k,
        common_domain_subset_hamiltonian ε hε h hh hb m g κ s hmem⟩ =
      ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) •
        ((Kr) ⟨state ε a h hε ha hh q k, hmem.1.1.2⟩ +
          (Pot m g κ) ⟨state ε a h hε ha hh q k, hmem.1.2⟩) :=
  unconditional_two_time_hamiltonian_three_operator_difference ε hε h hh hb m g κ t s
    (state ε a h hε ha hh q k)
    (state_mem_commonOperatorDomain ε a h hε ha hh hb q k hq m g κ)

theorem state_two_time_residual_difference (m g κ t s : ℝ) :
    let hmem := state_mem_commonOperatorDomain ε a h hε ha hh hb q k hq m g κ
    Res m g κ t ⟨state ε a h hε ha hh q k,
      common_domain_subset_residual ε hε h hh hb m g κ t hmem⟩ -
      Res m g κ s ⟨state ε a h hε ha hh q k,
        common_domain_subset_residual ε hε h hh hb m g κ s hmem⟩ =
      ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) •
        (Pot m g κ) ⟨state ε a h hε ha hh q k, hmem.1.2⟩ :=
  unconditional_two_time_residual_difference ε hε h hh hb m g κ t s
    (state ε a h hε ha hh q k)
    (state_mem_commonOperatorDomain ε a h hε ha hh hb q k hq m g κ)

#print axioms mem_commonOperatorDomain_of_mem_hamiltonian_and_growing
#print axioms rawState_mem_commonOperatorDomain
#print axioms rawState_static_domain
#print axioms rawState_radial_domain
#print axioms rawState_potential_domain
#print axioms rawState_residual_form_domain
#print axioms rawState_residual_domain
#print axioms rawState_clockHalf_domain
#print axioms rawState_growing_decomposition
#print axioms rawState_residual_decomposition
#print axioms rawState_hamiltonian_growing_decomposition
#print axioms rawState_three_operator_decomposition
#print axioms hamiltonianOutput_three_operator_decomposition
#print axioms rawState_two_time_hamiltonian_growing_difference
#print axioms rawState_two_time_hamiltonian_three_operator_difference
#print axioms rawState_two_time_residual_difference
#print axioms state_mem_commonOperatorDomain
#print axioms state_clockHalf_domain
#print axioms state_three_operator_decomposition
#print axioms state_two_time_hamiltonian_three_operator_difference
#print axioms state_two_time_residual_difference
end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedMultiOperatorDomain
