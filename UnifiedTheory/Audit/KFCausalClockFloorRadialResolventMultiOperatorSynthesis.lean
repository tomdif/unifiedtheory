/- Multi-Operator Radial-Resolvent Synthesis across T, K_rad, P, G, S(t), H(t),
and clockHalf ε:
1. Unconditional domain identity
     unconditionalCore := Dom(G) ∩ Dom(T) ∩ Dom(P) = Dom(T) ∩ Dom(K_rad) ∩ Dom(P)
                        = Dom(T) ∩ Dom(G),
   absorption of Dom(clockHalf ε), and the unconditional equivalence on Dom(T):
     J_N x ∈ unconditionalCore ↔ J_N x ∈ Dom(P) ↔ J_N x ∈ Dom(G),
   together with the corresponding equivalence on commonOperatorDomain.
2. Full 7-operator radial-resolvent invariance, explicit operator evaluation
   identities, and simultaneous strong convergence as n → ∞ across all seven
   operators T, K_rad, P, G, S(t), H(t), and clockHalf ε (both in the pointwise
   shifted-potential graph formulation and under the uniform shifted potential
   form hypothesis).
3. Positive-vacuum (k > 0) radial-resolvent regularization smoothing vectors
   from Dom(T) ∩ Dom(P) and Dom(S(t)) ∩ Dom(P) = Dom(S(t)) ∩ Dom(T) into
   unconditionalCore = Dom(H(t)) ∩ Dom(G) ⊆ Dom(H(t)) ∩ Dom(S(t)), with strong
   convergence S(t)(J_{n+1} x) → S(t) x as n → ∞. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventStaticRadialCore
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventGrowingDomain

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialResolventMultiOperatorSynthesis
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialYosidaDomain (operator)
open KFCausalClockFloorRadialResolventRegularizer (action radial_domain radial_graph sequence_tendsto)
open KFCausalClockFloorRadialResolventOperator (operator_commute operator_sequence_tendsto)
open KFCausalClockFloorRadialResolventShifted (shifted_sequence_tendsto)
open KFCausalClockFloorRadialResolventSections (outputActionLp)
open KFCausalClockFloorRadialResolventShiftedPairing (neg_shift_bound)
open KFCausalClockFloorRadialResolventShiftedOrderedTransport
  (shiftedResolvent narrow_half_shift_bound)
open KFCausalClockFloorRadialResolventClockCommutation
  (resolvent_clockHalf_domain resolvent_clockHalf_commute resolvent_clockHalf_tendsto)
open KFCausalClockFloorRadialResolventStaticDomain
  (domainFormLift commutatorVector staticOperator_resolvent_apply)
open KFCausalClockFloorRadialResolventStaticRadialCore
  (static_domain_subset_clockHalf_domain static_resolvent_domain
    static_yosida_domain static_resolvent_tendsto
    yosida_radial_domain_of_radial_domain)
open KFCausalClockFloorRadialResolventPotentialDomain
  (potentialHamiltonian_resolvent_graph potentialHamiltonian_resolvent_domain
    potentialHamiltonian_yosida_domain)
open KFCausalClockFloorRadialResolventGrowingDomain
  (growingHamiltonian_domain_iff growingHamiltonian_eq_radial_add_potential
    growingHamiltonian_resolvent_domain_iff_potential
    growingHamiltonian_resolvent_graph_of_potential
    growingHamiltonian_resolvent_graph growingHamiltonian_resolvent_domain
    growingHamiltonian_yosida_domain
    potentialHamiltonian_and_radial_to_growingHamiltonian_graph)
open KFCausalClockFloorUnconditionalTwoTimeEvolution
  (commonOperatorDomain common_domain_subset_hamiltonian
    common_domain_subset_residual common_domain_subset_growing)
open KFCausalClockFloorUnconditionalThreeOperatorDecomposition
  (residual_hamiltonian_domain_subset_residual_form
    unconditional_three_operator_residual_graph
    unconditional_three_operator_hamiltonian_graph)
open KFCausalClockFloorPositiveVacuumThreeOperatorDomain
  (three_operator_hamiltonian_graph three_operator_residual_graph)
open KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain
  (three_operator_domain_le_clockHalf_domain
    positive_vacuum_common_domain_eq_three_operator
    positive_vacuum_hamiltonian_inter_growing_domain_eq
    positive_vacuum_hamiltonian_inter_static_domain_eq
    positive_vacuum_hamiltonian_inter_potential_domain_eq
    positive_vacuum_residual_inter_growing_domain_eq)

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
  (hb : |h| ≤ Real.pi * ε / 3) (hh : h ≠ 0) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "Kr" => operator ε hε h
local notation "TD" => KFCausalClockFloorStaticHamiltonian.formData ε hε h hh hw m g k 0
local notation "TB" => KFCausalClosedGraphForm.energyOutput TD
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "PV" => KFCausalClockFloorPotentialHamiltonian.PotentialForm ε hε h hh hw m g k
local notation "PJ" => KFCausalClosedGraphForm.embedding PD
local notation "PB" => KFCausalClosedGraphForm.energyOutput PD
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "J" => action ε hε h N hN
local notation "M" => KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN

/-! ### 1. Unconditional Domain Identities and Equivalence of J_N-Invariance -/

def unconditionalCore : Submodule ℂ Hilbert :=
  (G).domain ⊓ (T).domain ⊓ (P).domain

theorem unconditionalCore_mem_iff (f : Hilbert) :
    f ∈ unconditionalCore ε hε h hb hh m g k ↔
      (f ∈ (T).domain ∧ f ∈ (Kr).domain) ∧ f ∈ (P).domain := by
  change (f ∈ (G).domain ∧ f ∈ (T).domain) ∧ f ∈ (P).domain ↔
    (f ∈ (T).domain ∧ f ∈ (Kr).domain) ∧ f ∈ (P).domain
  rw [growingHamiltonian_domain_iff ε hε h hb hh m g k f]
  tauto

theorem unconditionalCore_eq_three_operator_domain :
    unconditionalCore ε hε h hb hh m g k =
      (T).domain ⊓ (Kr).domain ⊓ (P).domain := by
  ext f
  exact unconditionalCore_mem_iff ε hε h hb hh m g k f

theorem unconditionalCore_eq_static_inter_growing :
    unconditionalCore ε hε h hb hh m g k =
      (T).domain ⊓ (G).domain := by
  ext f
  rw [unconditionalCore_mem_iff ε hε h hb hh m g k f]
  change ((f ∈ (T).domain ∧ f ∈ (Kr).domain) ∧ f ∈ (P).domain) ↔
    (f ∈ (T).domain ∧ f ∈ (G).domain)
  rw [growingHamiltonian_domain_iff ε hε h hb hh m g k f]
  tauto

theorem unconditionalCore_le_clockHalf_domain :
    unconditionalCore ε hε h hb hh m g k ≤ (clockHalf ε).domain := by
  rw [unconditionalCore_eq_three_operator_domain ε hε h hb hh m g k]
  exact three_operator_domain_le_clockHalf_domain ε hε h hh hb m g k

theorem unconditionalCore_inf_clockHalf_eq :
    unconditionalCore ε hε h hb hh m g k ⊓ (clockHalf ε).domain =
      unconditionalCore ε hε h hb hh m g k :=
  inf_of_le_left (unconditionalCore_le_clockHalf_domain ε hε h hb hh m g k)

theorem commonOperatorDomain_eq_unconditionalCore_inf_residualForm :
    commonOperatorDomain ε hε h hh hb m g k =
      unconditionalCore ε hε h hb hh m g k ⊓ (Tres 0).domain := by
  unfold commonOperatorDomain
  rw [unconditionalCore_eq_three_operator_domain ε hε h hb hh m g k]

theorem resolvent_mem_unconditionalCore_iff_potential (f : Hilbert)
    (hf : f ∈ (T).domain) :
    J f ∈ unconditionalCore ε hε h hb hh m g k ↔ J f ∈ (P).domain := by
  rw [unconditionalCore_mem_iff ε hε h hb hh m g k (J f)]
  have hT : J f ∈ (T).domain := static_resolvent_domain ε hε h N hN hb hh f hf
  have hK : J f ∈ (Kr).domain := radial_domain ε hε h N hN f
  exact ⟨And.right, fun hP => ⟨⟨hT, hK⟩, hP⟩⟩

theorem resolvent_mem_unconditionalCore_iff_growing (f : Hilbert)
    (hf : f ∈ (T).domain) :
    J f ∈ unconditionalCore ε hε h hb hh m g k ↔ J f ∈ (G).domain :=
  (resolvent_mem_unconditionalCore_iff_potential ε hε h N hN hb hh m g k f hf).trans
    (growingHamiltonian_resolvent_domain_iff_potential ε hε h N hN hb hh m g k f).symm

theorem resolvent_mem_unconditionalCore_equiv (f : Hilbert)
    (hf : f ∈ (T).domain) :
    (J f ∈ unconditionalCore ε hε h hb hh m g k ↔ J f ∈ (P).domain) ∧
      (J f ∈ (P).domain ↔ J f ∈ (G).domain) ∧
      (J f ∈ unconditionalCore ε hε h hb hh m g k ↔ J f ∈ (G).domain) :=
  ⟨resolvent_mem_unconditionalCore_iff_potential ε hε h N hN hb hh m g k f hf,
    (growingHamiltonian_resolvent_domain_iff_potential ε hε h N hN hb hh m g k f).symm,
    resolvent_mem_unconditionalCore_iff_growing ε hε h N hN hb hh m g k f hf⟩

theorem resolvent_mem_commonOperatorDomain_iff_potential (f : Hilbert)
    (hf : f ∈ (T).domain) (hres : f ∈ (Tres 0).domain) :
    J f ∈ commonOperatorDomain ε hε h hh hb m g k ↔ J f ∈ (P).domain := by
  rw [commonOperatorDomain_eq_unconditionalCore_inf_residualForm ε hε h hb hh m g k]
  change (J f ∈ unconditionalCore ε hε h hb hh m g k ∧ J f ∈ (Tres 0).domain) ↔
    J f ∈ (P).domain
  rw [resolvent_mem_unconditionalCore_iff_potential ε hε h N hN hb hh m g k f hf]
  have hJres : J f ∈ (Tres 0).domain :=
    KFCausalClockFloorRadialResolventResidual.domain_action ε hε h N hN hb hh m g k 0 f hres
  exact ⟨And.left, fun hP => ⟨hP, hJres⟩⟩

theorem resolvent_mem_commonOperatorDomain_iff_growing (f : Hilbert)
    (hf : f ∈ (T).domain) (hres : f ∈ (Tres 0).domain) :
    J f ∈ commonOperatorDomain ε hε h hh hb m g k ↔ J f ∈ (G).domain :=
  (resolvent_mem_commonOperatorDomain_iff_potential ε hε h N hN hb hh m g k f hf hres).trans
    (growingHamiltonian_resolvent_domain_iff_potential ε hε h N hN hb hh m g k f).symm

/-! ### 2. Full 7-Operator Invariance and Simultaneous Strong Convergence -/

theorem resolvent_mem_unconditionalCore_of_potential_graph
    {f w : Hilbert} (hfT : f ∈ (T).domain) (hpw : (J f, w) ∈ (P).graph) :
    J f ∈ unconditionalCore ε hε h hb hh m g k :=
  (resolvent_mem_unconditionalCore_iff_potential ε hε h N hN hb hh m g k f hfT).mpr
    (LinearPMap.mem_domain_of_mem_graph hpw)

theorem resolvent_mem_commonOperatorDomain_of_potential_graph
    {f w : Hilbert} (hfT : f ∈ (T).domain) (hres : f ∈ (Tres 0).domain)
    (hpw : (J f, w) ∈ (P).graph) :
    J f ∈ commonOperatorDomain ε hε h hh hb m g k :=
  (resolvent_mem_commonOperatorDomain_iff_potential ε hε h N hN hb hh m g k f hfT hres).mpr
    (LinearPMap.mem_domain_of_mem_graph hpw)

theorem resolvent_five_operator_eval_of_potential_graph
    {f w : Hilbert} (hfT : f ∈ (T).domain) (hfK : f ∈ (Kr).domain)
    (hpw : (J f, w) ∈ (P).graph) :
    let hJT := static_resolvent_domain ε hε h N hN hb hh f hfT
    let hJK := radial_domain ε hε h N hN f
    let hJP := LinearPMap.mem_domain_of_mem_graph hpw
    let hJG := (growingHamiltonian_resolvent_domain_iff_potential
      ε hε h N hN hb hh m g k f).mpr hJP
    let hC := static_domain_subset_clockHalf_domain ε hε h f hfT
    let hJC := resolvent_clockHalf_domain ε hε h N hN f hC
    J f ∈ unconditionalCore ε hε h hb hh m g k ∧
      T ⟨J f, hJT⟩ =
        J (T ⟨f, hfT⟩) +
          commutatorVector ε hε h N hN hh m g k f
            (TB (domainFormLift ε hε h hb hh m g k ⟨f, hfT⟩)) ∧
      Kr ⟨J f, hJK⟩ = J (Kr ⟨f, hfK⟩) ∧
      P ⟨J f, hJP⟩ = w ∧
      G ⟨J f, hJG⟩ = J (Kr ⟨f, hfK⟩) + w ∧
      clockHalf ε ⟨J f, hJC⟩ = J (clockHalf ε ⟨f, hC⟩) := by
  let hJT := static_resolvent_domain ε hε h N hN hb hh f hfT
  let hJK := radial_domain ε hε h N hN f
  let hJP := LinearPMap.mem_domain_of_mem_graph hpw
  let hJG := (growingHamiltonian_resolvent_domain_iff_potential
    ε hε h N hN hb hh m g k f).mpr hJP
  let hC := static_domain_subset_clockHalf_domain ε hε h f hfT
  let hJC := resolvent_clockHalf_domain ε hε h N hN f hC
  have hP_eq : P ⟨J f, hJP⟩ = w :=
    (P).mem_graph_snd_inj' ((P).mem_graph ⟨J f, hJP⟩) hpw rfl
  have hG_graph := growingHamiltonian_resolvent_graph_of_potential
    ε hε h N hN hb hh m g k f (Kr ⟨f, hfK⟩) w ((Kr).mem_graph ⟨f, hfK⟩) hpw
  have hG_eq : G ⟨J f, hJG⟩ = J (Kr ⟨f, hfK⟩) + w :=
    (G).mem_graph_snd_inj' ((G).mem_graph ⟨J f, hJG⟩) hG_graph rfl
  exact ⟨resolvent_mem_unconditionalCore_of_potential_graph ε hε h N hN hb hh m g k hfT hpw,
    staticOperator_resolvent_apply ε hε h N hN hb hh m g k ⟨f, hfT⟩,
    operator_commute ε hε h N hN ⟨f, hfK⟩,
    hP_eq,
    hG_eq,
    resolvent_clockHalf_commute ε hε h N hN f hC⟩

theorem resolvent_seven_operator_eval_on_common_of_potential_graph (t : ℝ)
    {f w : Hilbert} (hf : f ∈ commonOperatorDomain ε hε h hh hb m g k)
    (hpw : (J f, w) ∈ (P).graph) :
    let hfT : f ∈ (T).domain := hf.1.1.1
    let hfK : f ∈ (Kr).domain := hf.1.1.2
    let hJcom := resolvent_mem_commonOperatorDomain_of_potential_graph
      ε hε h N hN hb hh m g k hfT hf.2 hpw
    let hJT := hJcom.1.1.1
    let hJK := hJcom.1.1.2
    let hJP := hJcom.1.2
    let hJG := common_domain_subset_growing ε hε h hh hb m g k hJcom
    let hJS := common_domain_subset_residual ε hε h hh hb m g k t hJcom
    let hJH := common_domain_subset_hamiltonian ε hε h hh hb m g k t hJcom
    let hC := static_domain_subset_clockHalf_domain ε hε h f hfT
    let hJC := resolvent_clockHalf_domain ε hε h N hN f hC
    J f ∈ commonOperatorDomain ε hε h hh hb m g k ∧
      T ⟨J f, hJT⟩ =
        J (T ⟨f, hfT⟩) +
          commutatorVector ε hε h N hN hh m g k f
            (TB (domainFormLift ε hε h hb hh m g k ⟨f, hfT⟩)) ∧
      Kr ⟨J f, hJK⟩ = J (Kr ⟨f, hfK⟩) ∧
      P ⟨J f, hJP⟩ = w ∧
      G ⟨J f, hJG⟩ = J (Kr ⟨f, hfK⟩) + w ∧
      S t ⟨J f, hJS⟩ = T ⟨J f, hJT⟩ + (Real.exp (2 * t) : ℂ) • w ∧
      H t ⟨J f, hJH⟩ =
        T ⟨J f, hJT⟩ + (Real.exp (2 * t) : ℂ) • (J (Kr ⟨f, hfK⟩) + w) ∧
      clockHalf ε ⟨J f, hJC⟩ = J (clockHalf ε ⟨f, hC⟩) := by
  let hfT : f ∈ (T).domain := hf.1.1.1
  let hfK : f ∈ (Kr).domain := hf.1.1.2
  let hJcom := resolvent_mem_commonOperatorDomain_of_potential_graph
    ε hε h N hN hb hh m g k hfT hf.2 hpw
  let hJT := hJcom.1.1.1
  let hJK := hJcom.1.1.2
  let hJP := hJcom.1.2
  let hJG := common_domain_subset_growing ε hε h hh hb m g k hJcom
  let hJS := common_domain_subset_residual ε hε h hh hb m g k t hJcom
  let hJH := common_domain_subset_hamiltonian ε hε h hh hb m g k t hJcom
  let hC := static_domain_subset_clockHalf_domain ε hε h f hfT
  let hJC := resolvent_clockHalf_domain ε hε h N hN f hC
  have h5 := resolvent_five_operator_eval_of_potential_graph
    ε hε h N hN hb hh m g k hfT hfK hpw
  have hKr_graph : (J f, J (Kr ⟨f, hfK⟩)) ∈ (Kr).graph := by
    rw [← h5.2.2.1]
    exact (Kr).mem_graph ⟨J f, hJK⟩
  have hS_graph := unconditional_three_operator_residual_graph
    ε hε h hh hb m g k t (J f) (T ⟨J f, hJT⟩) w
    ((T).mem_graph ⟨J f, hJT⟩) hpw hJcom.2
  have hH_graph := unconditional_three_operator_hamiltonian_graph
    ε hε h hh hb m g k t (J f) (T ⟨J f, hJT⟩) (J (Kr ⟨f, hfK⟩)) w
    ((T).mem_graph ⟨J f, hJT⟩) hKr_graph hpw hJcom.2
  have hS_eq : S t ⟨J f, hJS⟩ = T ⟨J f, hJT⟩ + (Real.exp (2 * t) : ℂ) • w :=
    (S t).mem_graph_snd_inj' ((S t).mem_graph ⟨J f, hJS⟩) hS_graph rfl
  have hH_eq : H t ⟨J f, hJH⟩ =
      T ⟨J f, hJT⟩ + (Real.exp (2 * t) : ℂ) • (J (Kr ⟨f, hfK⟩) + w) :=
    (H t).mem_graph_snd_inj' ((H t).mem_graph ⟨J f, hJH⟩) hH_graph rfl
  exact ⟨hJcom, h5.2.1, h5.2.2.1, h5.2.2.2.1, h5.2.2.2.2.1, hS_eq, hH_eq, h5.2.2.2.2.2⟩

theorem unconditionalCore_resolvent_invariant
    (hbn : |h| ≤ Real.pi * ε / 6)
    (hshift : ∀ v : PV, ∃ w : PV,
      PJ w = shiftedResolvent ε hε h N hN h hbn (PJ v) ∧
      PB w = outputActionLp ε hε h N hN (h / 2) (narrow_half_shift_bound ε h hbn) (PB v))
    (f : Hilbert) (hf : f ∈ unconditionalCore ε hε h hb hh m g k) :
    J f ∈ unconditionalCore ε hε h hb hh m g k := by
  have hmem := (unconditionalCore_mem_iff ε hε h hb hh m g k f).mp hf
  exact (resolvent_mem_unconditionalCore_iff_potential ε hε h N hN hb hh m g k f hmem.1.1).mpr
    (potentialHamiltonian_resolvent_domain ε hε h N hN hb hh m g k hbn hshift f hmem.2)

theorem unconditionalCore_yosida_invariant
    (hbn : |h| ≤ Real.pi * ε / 6)
    (hshift : ∀ v : PV, ∃ w : PV,
      PJ w = shiftedResolvent ε hε h N hN h hbn (PJ v) ∧
      PB w = outputActionLp ε hε h N hN (h / 2) (narrow_half_shift_bound ε h hbn) (PB v))
    (f : Hilbert) (hf : f ∈ unconditionalCore ε hε h hb hh m g k) :
    M f ∈ unconditionalCore ε hε h hb hh m g k := by
  have hmem := (unconditionalCore_mem_iff ε hε h hb hh m g k f).mp hf
  exact (unconditionalCore_mem_iff ε hε h hb hh m g k (M f)).mpr
    ⟨⟨static_yosida_domain ε hε h N hN hb hh f hmem.1.1,
      yosida_radial_domain_of_radial_domain ε hε h N hN f hmem.1.2⟩,
      potentialHamiltonian_yosida_domain ε hε h N hN hb hh m g k hbn hshift f hmem.2⟩

theorem commonOperatorDomain_resolvent_invariant
    (hbn : |h| ≤ Real.pi * ε / 6)
    (hshift : ∀ v : PV, ∃ w : PV,
      PJ w = shiftedResolvent ε hε h N hN h hbn (PJ v) ∧
      PB w = outputActionLp ε hε h N hN (h / 2) (narrow_half_shift_bound ε h hbn) (PB v))
    (f : Hilbert) (hf : f ∈ commonOperatorDomain ε hε h hh hb m g k) :
    J f ∈ commonOperatorDomain ε hε h hh hb m g k :=
  (resolvent_mem_commonOperatorDomain_iff_potential
    ε hε h N hN hb hh m g k f hf.1.1.1 hf.2).mpr
    (potentialHamiltonian_resolvent_domain ε hε h N hN hb hh m g k hbn hshift f hf.1.2)

theorem commonOperatorDomain_yosida_invariant
    (hbn : |h| ≤ Real.pi * ε / 6)
    (hshift : ∀ v : PV, ∃ w : PV,
      PJ w = shiftedResolvent ε hε h N hN h hbn (PJ v) ∧
      PB w = outputActionLp ε hε h N hN (h / 2) (narrow_half_shift_bound ε h hbn) (PB v))
    (f : Hilbert) (hf : f ∈ commonOperatorDomain ε hε h hh hb m g k) :
    M f ∈ commonOperatorDomain ε hε h hh hb m g k := by
  have hj := commonOperatorDomain_resolvent_invariant ε hε h N hN hb hh m g k hbn hshift f hf
  have hsub := (commonOperatorDomain ε hε h hh hb m g k).sub_mem hf hj
  have hsmul := (commonOperatorDomain ε hε h hh hb m g k).smul_mem (N : ℂ) hsub
  have heq : (N : ℂ) • (f - J f) = M f := by
    change (N : ℂ) • (f - (f - (N⁻¹ : ℂ) • M f)) = M f
    rw [sub_sub_cancel, smul_smul]
    have hNne : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
    rw [mul_inv_cancel₀ hNne, one_smul]
  exact (congrArg (fun z : Hilbert => z ∈ commonOperatorDomain ε hε h hh hb m g k) heq).mp hsmul

theorem seven_operator_resolvent_invariance_and_eval
    (hbn : |h| ≤ Real.pi * ε / 6)
    (hshift : ∀ v : PV, ∃ w : PV,
      PJ w = shiftedResolvent ε hε h N hN h hbn (PJ v) ∧
      PB w = outputActionLp ε hε h N hN (h / 2) (narrow_half_shift_bound ε h hbn) (PB v))
    (t : ℝ) (f : Hilbert) (hf : f ∈ commonOperatorDomain ε hε h hh hb m g k) :
    let hfT : f ∈ (T).domain := hf.1.1.1
    let hfK : f ∈ (Kr).domain := hf.1.1.2
    let hfP : f ∈ (P).domain := hf.1.2
    let w := shiftedResolvent ε hε h N hN (-h) (neg_shift_bound ε h hbn) (P ⟨f, hfP⟩)
    let hpw := potentialHamiltonian_resolvent_graph ε hε h N hN hb hh m g k hbn hshift ⟨f, hfP⟩
    let hJcom := resolvent_mem_commonOperatorDomain_of_potential_graph
      ε hε h N hN hb hh m g k hfT hf.2 hpw
    let hJT := hJcom.1.1.1
    let hJK := hJcom.1.1.2
    let hJP := hJcom.1.2
    let hJG := common_domain_subset_growing ε hε h hh hb m g k hJcom
    let hJS := common_domain_subset_residual ε hε h hh hb m g k t hJcom
    let hJH := common_domain_subset_hamiltonian ε hε h hh hb m g k t hJcom
    let hC := static_domain_subset_clockHalf_domain ε hε h f hfT
    let hJC := resolvent_clockHalf_domain ε hε h N hN f hC
    J f ∈ commonOperatorDomain ε hε h hh hb m g k ∧
      T ⟨J f, hJT⟩ =
        J (T ⟨f, hfT⟩) +
          commutatorVector ε hε h N hN hh m g k f
            (TB (domainFormLift ε hε h hb hh m g k ⟨f, hfT⟩)) ∧
      Kr ⟨J f, hJK⟩ = J (Kr ⟨f, hfK⟩) ∧
      P ⟨J f, hJP⟩ = w ∧
      G ⟨J f, hJG⟩ = J (Kr ⟨f, hfK⟩) + w ∧
      S t ⟨J f, hJS⟩ = T ⟨J f, hJT⟩ + (Real.exp (2 * t) : ℂ) • w ∧
      H t ⟨J f, hJH⟩ =
        T ⟨J f, hJT⟩ + (Real.exp (2 * t) : ℂ) • (J (Kr ⟨f, hfK⟩) + w) ∧
      clockHalf ε ⟨J f, hJC⟩ = J (clockHalf ε ⟨f, hC⟩) :=
  resolvent_seven_operator_eval_on_common_of_potential_graph
    ε hε h N hN hb hh m g k t hf
    (potentialHamiltonian_resolvent_graph ε hε h N hN hb hh m g k hbn hshift ⟨f, hf.1.2⟩)

private theorem common_residual_eq (t : ℝ) (f : Hilbert)
    (hf : f ∈ commonOperatorDomain ε hε h hh hb m g k) :
    S t ⟨f, common_domain_subset_residual ε hε h hh hb m g k t hf⟩ =
      T ⟨f, hf.1.1.1⟩ + (Real.exp (2 * t) : ℂ) • P ⟨f, hf.1.2⟩ :=
  (S t).mem_graph_snd_inj'
    ((S t).mem_graph ⟨f, common_domain_subset_residual ε hε h hh hb m g k t hf⟩)
    (unconditional_three_operator_residual_graph ε hε h hh hb m g k t
      f (T ⟨f, hf.1.1.1⟩) (P ⟨f, hf.1.2⟩)
      ((T).mem_graph ⟨f, hf.1.1.1⟩) ((P).mem_graph ⟨f, hf.1.2⟩) hf.2) rfl

private theorem common_hamiltonian_eq (t : ℝ) (f : Hilbert)
    (hf : f ∈ commonOperatorDomain ε hε h hh hb m g k) :
    H t ⟨f, common_domain_subset_hamiltonian ε hε h hh hb m g k t hf⟩ =
      T ⟨f, hf.1.1.1⟩ +
        (Real.exp (2 * t) : ℂ) • (Kr ⟨f, hf.1.1.2⟩ + P ⟨f, hf.1.2⟩) :=
  (H t).mem_graph_snd_inj'
    ((H t).mem_graph ⟨f, common_domain_subset_hamiltonian ε hε h hh hb m g k t hf⟩)
    (unconditional_three_operator_hamiltonian_graph ε hε h hh hb m g k t
      f (T ⟨f, hf.1.1.1⟩) (Kr ⟨f, hf.1.1.2⟩) (P ⟨f, hf.1.2⟩)
      ((T).mem_graph ⟨f, hf.1.1.1⟩) ((Kr).mem_graph ⟨f, hf.1.1.2⟩)
      ((P).mem_graph ⟨f, hf.1.2⟩) hf.2) rfl

private theorem common_growing_eq (f : Hilbert)
    (hf : f ∈ commonOperatorDomain ε hε h hh hb m g k) :
    G ⟨f, common_domain_subset_growing ε hε h hh hb m g k hf⟩ =
      Kr ⟨f, hf.1.1.2⟩ + P ⟨f, hf.1.2⟩ :=
  (G).mem_graph_snd_inj'
    ((G).mem_graph ⟨f, common_domain_subset_growing ε hε h hh hb m g k hf⟩)
    (potentialHamiltonian_and_radial_to_growingHamiltonian_graph ε hε h hb hh m g k
      f (Kr ⟨f, hf.1.1.2⟩) (P ⟨f, hf.1.2⟩)
      ((Kr).mem_graph ⟨f, hf.1.1.2⟩) ((P).mem_graph ⟨f, hf.1.2⟩)) rfl

theorem seven_operator_simultaneous_strong_convergence_of_potential_graph
    (hbn : |h| ≤ Real.pi * ε / 6) (t : ℝ)
    (f : Hilbert) (hf : f ∈ commonOperatorDomain ε hε h hh hb m g k)
    (hpSeq : ∀ n : ℕ,
      (action ε hε h ((n : ℝ) + 1) (by positivity) f,
        shiftedResolvent ε hε h ((n : ℝ) + 1) (by positivity) (-h)
          (neg_shift_bound ε h hbn) (P ⟨f, hf.1.2⟩)) ∈ (P).graph) :
    let hfT : f ∈ (T).domain := hf.1.1.1
    let hfK : f ∈ (Kr).domain := hf.1.1.2
    let hfP : f ∈ (P).domain := hf.1.2
    let hfG : f ∈ (G).domain := common_domain_subset_growing ε hε h hh hb m g k hf
    let hfS : f ∈ (S t).domain := common_domain_subset_residual ε hε h hh hb m g k t hf
    let hfH : f ∈ (H t).domain := common_domain_subset_hamiltonian ε hε h hh hb m g k t hf
    let hfC : f ∈ (clockHalf ε).domain := static_domain_subset_clockHalf_domain ε hε h f hfT
    let hJcom := fun n : ℕ =>
      resolvent_mem_commonOperatorDomain_of_potential_graph
        ε hε h ((n : ℝ) + 1) (by positivity) hb hh m g k hfT hf.2 (hpSeq n)
    Tendsto (fun n : ℕ => action ε hε h ((n : ℝ) + 1) (by positivity) f)
      atTop (𝓝 f) ∧
    Tendsto (fun n : ℕ =>
      T ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f, (hJcom n).1.1.1⟩)
      atTop (𝓝 (T ⟨f, hfT⟩)) ∧
    Tendsto (fun n : ℕ =>
      Kr ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f, (hJcom n).1.1.2⟩)
      atTop (𝓝 (Kr ⟨f, hfK⟩)) ∧
    Tendsto (fun n : ℕ =>
      P ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f, (hJcom n).1.2⟩)
      atTop (𝓝 (P ⟨f, hfP⟩)) ∧
    Tendsto (fun n : ℕ =>
      G ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        common_domain_subset_growing ε hε h hh hb m g k (hJcom n)⟩)
      atTop (𝓝 (G ⟨f, hfG⟩)) ∧
    Tendsto (fun n : ℕ =>
      S t ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        common_domain_subset_residual ε hε h hh hb m g k t (hJcom n)⟩)
      atTop (𝓝 (S t ⟨f, hfS⟩)) ∧
    Tendsto (fun n : ℕ =>
      H t ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        common_domain_subset_hamiltonian ε hε h hh hb m g k t (hJcom n)⟩)
      atTop (𝓝 (H t ⟨f, hfH⟩)) ∧
    Tendsto (fun n : ℕ =>
      clockHalf ε ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        resolvent_clockHalf_domain ε hε h ((n : ℝ) + 1) (by positivity) f hfC⟩)
      atTop (𝓝 (clockHalf ε ⟨f, hfC⟩)) := by
  let hfT : f ∈ (T).domain := hf.1.1.1
  let hfK : f ∈ (Kr).domain := hf.1.1.2
  let hfP : f ∈ (P).domain := hf.1.2
  let hfG : f ∈ (G).domain := common_domain_subset_growing ε hε h hh hb m g k hf
  let hfS : f ∈ (S t).domain := common_domain_subset_residual ε hε h hh hb m g k t hf
  let hfH : f ∈ (H t).domain := common_domain_subset_hamiltonian ε hε h hh hb m g k t hf
  let hfC : f ∈ (clockHalf ε).domain := static_domain_subset_clockHalf_domain ε hε h f hfT
  let hJcom := fun n : ℕ =>
    resolvent_mem_commonOperatorDomain_of_potential_graph
      ε hε h ((n : ℝ) + 1) (by positivity) hb hh m g k hfT hf.2 (hpSeq n)
  have hT_lim : Tendsto (fun n : ℕ =>
      T ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f, (hJcom n).1.1.1⟩)
      atTop (𝓝 (T ⟨f, hfT⟩)) :=
    static_resolvent_tendsto ε hε h hb hh ⟨f, hfT⟩
  have hK_lim : Tendsto (fun n : ℕ =>
      Kr ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f, (hJcom n).1.1.2⟩)
      atTop (𝓝 (Kr ⟨f, hfK⟩)) :=
    operator_sequence_tendsto ε hε h ⟨f, hfK⟩
  have hP_lim : Tendsto (fun n : ℕ =>
      P ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f, (hJcom n).1.2⟩)
      atTop (𝓝 (P ⟨f, hfP⟩)) :=
    (shifted_sequence_tendsto ε hε h (-h) (neg_shift_bound ε h hbn) (P ⟨f, hfP⟩)).congr
      (fun n => ((P).mem_graph_snd_inj'
        ((P).mem_graph ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f, (hJcom n).1.2⟩)
        (hpSeq n) rfl).symm)
  have hG_lim : Tendsto (fun n : ℕ =>
      G ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        common_domain_subset_growing ε hε h hh hb m g k (hJcom n)⟩)
      atTop (𝓝 (G ⟨f, hfG⟩)) := by
    rw [common_growing_eq ε hε h hb hh m g k f hf]
    exact (hK_lim.add hP_lim).congr (fun n => by
      have hev := resolvent_seven_operator_eval_on_common_of_potential_graph
        ε hε h ((n : ℝ) + 1) (by positivity) hb hh m g k t hf (hpSeq n)
      have hK_eq := hev.2.2.1
      have hP_eq := hev.2.2.2.1
      have hG_eq := hev.2.2.2.2.1
      rw [hK_eq, hP_eq, hG_eq])
  have hS_lim : Tendsto (fun n : ℕ =>
      S t ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        common_domain_subset_residual ε hε h hh hb m g k t (hJcom n)⟩)
      atTop (𝓝 (S t ⟨f, hfS⟩)) := by
    rw [common_residual_eq ε hε h hb hh m g k t f hf]
    exact (hT_lim.add (hP_lim.const_smul (Real.exp (2 * t) : ℂ))).congr (fun n => by
      have hev := resolvent_seven_operator_eval_on_common_of_potential_graph
        ε hε h ((n : ℝ) + 1) (by positivity) hb hh m g k t hf (hpSeq n)
      have hP_eq := hev.2.2.2.1
      have hS_eq := hev.2.2.2.2.2.1
      rw [hP_eq, hS_eq])
  have hH_lim : Tendsto (fun n : ℕ =>
      H t ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        common_domain_subset_hamiltonian ε hε h hh hb m g k t (hJcom n)⟩)
      atTop (𝓝 (H t ⟨f, hfH⟩)) := by
    rw [common_hamiltonian_eq ε hε h hb hh m g k t f hf]
    exact (hT_lim.add ((hK_lim.add hP_lim).const_smul (Real.exp (2 * t) : ℂ))).congr (fun n => by
      have hev := resolvent_seven_operator_eval_on_common_of_potential_graph
        ε hε h ((n : ℝ) + 1) (by positivity) hb hh m g k t hf (hpSeq n)
      have hK_eq := hev.2.2.1
      have hP_eq := hev.2.2.2.1
      have hH_eq := hev.2.2.2.2.2.2.1
      rw [hK_eq, hP_eq, hH_eq])
  exact ⟨sequence_tendsto ε hε h f,
    hT_lim, hK_lim, hP_lim, hG_lim, hS_lim, hH_lim,
    resolvent_clockHalf_tendsto ε hε h f hfC⟩

theorem seven_operator_simultaneous_strong_convergence
    (hbn : |h| ≤ Real.pi * ε / 6)
    (hshiftSeq : ∀ (n : ℕ) (v : PV), ∃ w : PV,
      PJ w = shiftedResolvent ε hε h ((n : ℝ) + 1) (by positivity) h hbn (PJ v) ∧
      PB w = outputActionLp ε hε h ((n : ℝ) + 1) (by positivity) (h / 2)
        (narrow_half_shift_bound ε h hbn) (PB v))
    (t : ℝ) (f : Hilbert) (hf : f ∈ commonOperatorDomain ε hε h hh hb m g k) :
    let hfT : f ∈ (T).domain := hf.1.1.1
    let hfK : f ∈ (Kr).domain := hf.1.1.2
    let hfP : f ∈ (P).domain := hf.1.2
    let hfG : f ∈ (G).domain := common_domain_subset_growing ε hε h hh hb m g k hf
    let hfS : f ∈ (S t).domain := common_domain_subset_residual ε hε h hh hb m g k t hf
    let hfH : f ∈ (H t).domain := common_domain_subset_hamiltonian ε hε h hh hb m g k t hf
    let hfC : f ∈ (clockHalf ε).domain := static_domain_subset_clockHalf_domain ε hε h f hfT
    let hpSeq := fun n : ℕ =>
      potentialHamiltonian_resolvent_graph ε hε h ((n : ℝ) + 1) (by positivity)
        hb hh m g k hbn (hshiftSeq n) ⟨f, hfP⟩
    let hJcom := fun n : ℕ =>
      resolvent_mem_commonOperatorDomain_of_potential_graph
        ε hε h ((n : ℝ) + 1) (by positivity) hb hh m g k hfT hf.2 (hpSeq n)
    Tendsto (fun n : ℕ => action ε hε h ((n : ℝ) + 1) (by positivity) f)
      atTop (𝓝 f) ∧
    Tendsto (fun n : ℕ =>
      T ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f, (hJcom n).1.1.1⟩)
      atTop (𝓝 (T ⟨f, hfT⟩)) ∧
    Tendsto (fun n : ℕ =>
      Kr ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f, (hJcom n).1.1.2⟩)
      atTop (𝓝 (Kr ⟨f, hfK⟩)) ∧
    Tendsto (fun n : ℕ =>
      P ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f, (hJcom n).1.2⟩)
      atTop (𝓝 (P ⟨f, hfP⟩)) ∧
    Tendsto (fun n : ℕ =>
      G ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        common_domain_subset_growing ε hε h hh hb m g k (hJcom n)⟩)
      atTop (𝓝 (G ⟨f, hfG⟩)) ∧
    Tendsto (fun n : ℕ =>
      S t ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        common_domain_subset_residual ε hε h hh hb m g k t (hJcom n)⟩)
      atTop (𝓝 (S t ⟨f, hfS⟩)) ∧
    Tendsto (fun n : ℕ =>
      H t ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        common_domain_subset_hamiltonian ε hε h hh hb m g k t (hJcom n)⟩)
      atTop (𝓝 (H t ⟨f, hfH⟩)) ∧
    Tendsto (fun n : ℕ =>
      clockHalf ε ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        resolvent_clockHalf_domain ε hε h ((n : ℝ) + 1) (by positivity) f hfC⟩)
      atTop (𝓝 (clockHalf ε ⟨f, hfC⟩)) :=
  seven_operator_simultaneous_strong_convergence_of_potential_graph
    ε hε h hb hh m g k hbn t f hf
    (fun n => potentialHamiltonian_resolvent_graph ε hε h ((n : ℝ) + 1) (by positivity)
      hb hh m g k hbn (hshiftSeq n) ⟨f, hf.1.2⟩)

/-! ### 3. Positive-Vacuum (k > 0) Radial-Resolvent Regularization from Dom(S(t)) into Dom(H(t)) = unconditionalCore -/

theorem positive_vacuum_unconditionalCore_eq_commonOperatorDomain (hk : 0 < k) :
    unconditionalCore ε hε h hb hh m g k =
      commonOperatorDomain ε hε h hh hb m g k :=
  (unconditionalCore_eq_three_operator_domain ε hε h hb hh m g k).trans
    (positive_vacuum_common_domain_eq_three_operator ε hε h hh hb m g k hk).symm

theorem positive_vacuum_hamiltonian_growing_domain_eq_unconditionalCore
    (hk : 0 < k) (t : ℝ) :
    (H t).domain ⊓ (G).domain = unconditionalCore ε hε h hb hh m g k :=
  (positive_vacuum_hamiltonian_inter_growing_domain_eq ε hε h hh hb m g k hk t).trans
    (unconditionalCore_eq_three_operator_domain ε hε h hb hh m g k).symm

theorem positive_vacuum_hamiltonian_static_domain_eq_unconditionalCore
    (hk : 0 < k) (t : ℝ) :
    (H t).domain ⊓ (T).domain = unconditionalCore ε hε h hb hh m g k :=
  (positive_vacuum_hamiltonian_inter_static_domain_eq ε hε h hh hb m g k hk t).trans
    (unconditionalCore_eq_three_operator_domain ε hε h hb hh m g k).symm

theorem positive_vacuum_hamiltonian_potential_domain_eq_unconditionalCore
    (hk : 0 < k) (t : ℝ) :
    (H t).domain ⊓ (P).domain = unconditionalCore ε hε h hb hh m g k :=
  (positive_vacuum_hamiltonian_inter_potential_domain_eq ε hε h hh hb m g k hk t).trans
    (unconditionalCore_eq_three_operator_domain ε hε h hb hh m g k).symm

theorem positive_vacuum_residual_growing_domain_eq_unconditionalCore
    (hk : 0 < k) (t : ℝ) :
    (S t).domain ⊓ (G).domain = unconditionalCore ε hε h hb hh m g k :=
  (positive_vacuum_residual_inter_growing_domain_eq ε hε h hh hb m g k hk t).trans
    (unconditionalCore_eq_three_operator_domain ε hε h hb hh m g k).symm

theorem positive_vacuum_unconditionalCore_le_hamiltonian_domain
    (hk : 0 < k) (t : ℝ) :
    unconditionalCore ε hε h hb hh m g k ≤ (H t).domain := by
  rw [positive_vacuum_unconditionalCore_eq_commonOperatorDomain ε hε h hb hh m g k hk]
  exact common_domain_subset_hamiltonian ε hε h hh hb m g k t

theorem positive_vacuum_unconditionalCore_le_residual_domain
    (hk : 0 < k) (t : ℝ) :
    unconditionalCore ε hε h hb hh m g k ≤ (S t).domain := by
  rw [positive_vacuum_unconditionalCore_eq_commonOperatorDomain ε hε h hb hh m g k hk]
  exact common_domain_subset_residual ε hε h hh hb m g k t

theorem positive_vacuum_resolvent_regularizes_static_potential_into_hamiltonian
    (hk : 0 < k) (t : ℝ) {f w : Hilbert}
    (hfT : f ∈ (T).domain) (_hfP : f ∈ (P).domain)
    (hpw : (J f, w) ∈ (P).graph) :
    let hJT := static_resolvent_domain ε hε h N hN hb hh f hfT
    let hJK := radial_domain ε hε h N hN f
    let hJP := LinearPMap.mem_domain_of_mem_graph hpw
    let hJG := (growingHamiltonian_resolvent_domain_iff_potential
      ε hε h N hN hb hh m g k f).mpr hJP
    let hJcore := resolvent_mem_unconditionalCore_of_potential_graph
      ε hε h N hN hb hh m g k hfT hpw
    let hJS := positive_vacuum_unconditionalCore_le_residual_domain
      ε hε h hb hh m g k hk t hJcore
    let hJH := positive_vacuum_unconditionalCore_le_hamiltonian_domain
      ε hε h hb hh m g k hk t hJcore
    let hC := static_domain_subset_clockHalf_domain ε hε h f hfT
    let hJC := resolvent_clockHalf_domain ε hε h N hN f hC
    J f ∈ unconditionalCore ε hε h hb hh m g k ∧
      J f ∈ (H t).domain ⊓ (G).domain ∧
      Kr ⟨J f, hJK⟩ = M f ∧
      P ⟨J f, hJP⟩ = w ∧
      G ⟨J f, hJG⟩ = M f + w ∧
      S t ⟨J f, hJS⟩ = T ⟨J f, hJT⟩ + (Real.exp (2 * t) : ℂ) • w ∧
      H t ⟨J f, hJH⟩ =
        T ⟨J f, hJT⟩ + (Real.exp (2 * t) : ℂ) • (M f + w) ∧
      clockHalf ε ⟨J f, hJC⟩ = J (clockHalf ε ⟨f, hC⟩) := by
  let hJT := static_resolvent_domain ε hε h N hN hb hh f hfT
  let hJK := radial_domain ε hε h N hN f
  let hJP := LinearPMap.mem_domain_of_mem_graph hpw
  let hJG := (growingHamiltonian_resolvent_domain_iff_potential
    ε hε h N hN hb hh m g k f).mpr hJP
  let hJcore := resolvent_mem_unconditionalCore_of_potential_graph
    ε hε h N hN hb hh m g k hfT hpw
  let hJS := positive_vacuum_unconditionalCore_le_residual_domain
    ε hε h hb hh m g k hk t hJcore
  let hJH := positive_vacuum_unconditionalCore_le_hamiltonian_domain
    ε hε h hb hh m g k hk t hJcore
  let hC := static_domain_subset_clockHalf_domain ε hε h f hfT
  let hJC := resolvent_clockHalf_domain ε hε h N hN f hC
  have hHG : J f ∈ (H t).domain ⊓ (G).domain := by
    rw [positive_vacuum_hamiltonian_growing_domain_eq_unconditionalCore ε hε h hb hh m g k hk t]
    exact hJcore
  have hKr_eq : Kr ⟨J f, hJK⟩ = M f :=
    (Kr).mem_graph_snd_inj' ((Kr).mem_graph ⟨J f, hJK⟩) (radial_graph ε hε h N hN f) rfl
  have hP_eq : P ⟨J f, hJP⟩ = w :=
    (P).mem_graph_snd_inj' ((P).mem_graph ⟨J f, hJP⟩) hpw rfl
  have hG_graph := potentialHamiltonian_and_radial_to_growingHamiltonian_graph
    ε hε h hb hh m g k (J f) (M f) w (radial_graph ε hε h N hN f) hpw
  have hG_eq : G ⟨J f, hJG⟩ = M f + w :=
    (G).mem_graph_snd_inj' ((G).mem_graph ⟨J f, hJG⟩) hG_graph rfl
  have hS_graph := three_operator_residual_graph ε hε h hh hb m g k t hk
    (J f) (T ⟨J f, hJT⟩) (M f) w
    ((T).mem_graph ⟨J f, hJT⟩) (radial_graph ε hε h N hN f) hpw
  have hH_graph := three_operator_hamiltonian_graph ε hε h hh hb m g k t hk
    (J f) (T ⟨J f, hJT⟩) (M f) w
    ((T).mem_graph ⟨J f, hJT⟩) (radial_graph ε hε h N hN f) hpw
  have hS_eq : S t ⟨J f, hJS⟩ = T ⟨J f, hJT⟩ + (Real.exp (2 * t) : ℂ) • w :=
    (S t).mem_graph_snd_inj' ((S t).mem_graph ⟨J f, hJS⟩) hS_graph rfl
  have hH_eq : H t ⟨J f, hJH⟩ =
      T ⟨J f, hJT⟩ + (Real.exp (2 * t) : ℂ) • (M f + w) :=
    (H t).mem_graph_snd_inj' ((H t).mem_graph ⟨J f, hJH⟩) hH_graph rfl
  exact ⟨hJcore, hHG, hKr_eq, hP_eq, hG_eq, hS_eq, hH_eq,
    resolvent_clockHalf_commute ε hε h N hN f hC⟩

theorem residual_inter_potential_domain_eq_static_potential_residualForm (t : ℝ) :
    (S t).domain ⊓ (P).domain =
      ((T).domain ⊓ (P).domain) ⊓ (Tres 0).domain := by
  ext f
  change (f ∈ (S t).domain ∧ f ∈ (P).domain) ↔
    ((f ∈ (T).domain ∧ f ∈ (P).domain) ∧ f ∈ (Tres 0).domain)
  have hc := Set.ext_iff.mp (congrArg SetLike.coe
    (KFCausalClockFloorResidualStaticPotentialDecomposition.common_domain_eq
      ε hε h hh hw m g k t)) f
  change (f ∈ (S t).domain ∧ f ∈ (P).domain) ↔
    (f ∈ (S t).domain ∧ f ∈ (T).domain) at hc
  constructor
  · rintro ⟨hS, hP⟩
    have hT : f ∈ (T).domain := (hc.mp ⟨hS, hP⟩).2
    have hres : f ∈ (Tres 0).domain :=
      residual_hamiltonian_domain_subset_residual_form ε hε h hh hb m g k t f hS
    exact ⟨⟨hT, hP⟩, hres⟩
  · rintro ⟨⟨hT, hP⟩, hres⟩
    have hS : f ∈ (S t).domain := LinearPMap.mem_domain_of_mem_graph
      (unconditional_three_operator_residual_graph ε hε h hh hb m g k t
        f (T ⟨f, hT⟩) (P ⟨f, hP⟩)
        ((T).mem_graph ⟨f, hT⟩) ((P).mem_graph ⟨f, hP⟩) hres)
    exact ⟨hS, hP⟩

theorem positive_vacuum_residual_resolvent_regularization_and_tendsto
    (hk : 0 < k) (hbn : |h| ≤ Real.pi * ε / 6) (t : ℝ)
    (f : Hilbert) (hfS : f ∈ (S t).domain) (hfP : f ∈ (P).domain)
    (hpSeq : ∀ n : ℕ,
      (action ε hε h ((n : ℝ) + 1) (by positivity) f,
        shiftedResolvent ε hε h ((n : ℝ) + 1) (by positivity) (-h)
          (neg_shift_bound ε h hbn) (P ⟨f, hfP⟩)) ∈ (P).graph) :
    let hmem : f ∈ ((T).domain ⊓ (P).domain) ⊓ (Tres 0).domain := by
      rw [← residual_inter_potential_domain_eq_static_potential_residualForm
        ε hε h hb hh m g k t]
      exact ⟨hfS, hfP⟩
    let hfT : f ∈ (T).domain := hmem.1.1
    let hfC : f ∈ (clockHalf ε).domain := static_domain_subset_clockHalf_domain ε hε h f hfT
    let hJcore := fun n : ℕ =>
      resolvent_mem_unconditionalCore_of_potential_graph
        ε hε h ((n : ℝ) + 1) (by positivity) hb hh m g k hfT (hpSeq n)
    let hJS := fun n : ℕ =>
      positive_vacuum_unconditionalCore_le_residual_domain
        ε hε h hb hh m g k hk t (hJcore n)
    (∀ n : ℕ,
      action ε hε h ((n : ℝ) + 1) (by positivity) f ∈
        unconditionalCore ε hε h hb hh m g k ∧
      action ε hε h ((n : ℝ) + 1) (by positivity) f ∈ (H t).domain ∧
      action ε hε h ((n : ℝ) + 1) (by positivity) f ∈ (G).domain ∧
      action ε hε h ((n : ℝ) + 1) (by positivity) f ∈ (S t).domain) ∧
    Tendsto (fun n : ℕ => action ε hε h ((n : ℝ) + 1) (by positivity) f)
      atTop (𝓝 f) ∧
    Tendsto (fun n : ℕ =>
      T ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        static_resolvent_domain ε hε h ((n : ℝ) + 1) (by positivity) hb hh f hfT⟩)
      atTop (𝓝 (T ⟨f, hfT⟩)) ∧
    Tendsto (fun n : ℕ =>
      P ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        LinearPMap.mem_domain_of_mem_graph (hpSeq n)⟩)
      atTop (𝓝 (P ⟨f, hfP⟩)) ∧
    Tendsto (fun n : ℕ =>
      S t ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f, hJS n⟩)
      atTop (𝓝 (S t ⟨f, hfS⟩)) ∧
    Tendsto (fun n : ℕ =>
      clockHalf ε ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        resolvent_clockHalf_domain ε hε h ((n : ℝ) + 1) (by positivity) f hfC⟩)
      atTop (𝓝 (clockHalf ε ⟨f, hfC⟩)) := by
  have hmem : f ∈ ((T).domain ⊓ (P).domain) ⊓ (Tres 0).domain := by
    rw [← residual_inter_potential_domain_eq_static_potential_residualForm
      ε hε h hb hh m g k t]
    exact ⟨hfS, hfP⟩
  let hfT : f ∈ (T).domain := hmem.1.1
  let hfC : f ∈ (clockHalf ε).domain := static_domain_subset_clockHalf_domain ε hε h f hfT
  let hJcore := fun n : ℕ =>
    resolvent_mem_unconditionalCore_of_potential_graph
      ε hε h ((n : ℝ) + 1) (by positivity) hb hh m g k hfT (hpSeq n)
  let hJS := fun n : ℕ =>
    positive_vacuum_unconditionalCore_le_residual_domain
      ε hε h hb hh m g k hk t (hJcore n)
  have hdom : ∀ n : ℕ,
      action ε hε h ((n : ℝ) + 1) (by positivity) f ∈
        unconditionalCore ε hε h hb hh m g k ∧
      action ε hε h ((n : ℝ) + 1) (by positivity) f ∈ (H t).domain ∧
      action ε hε h ((n : ℝ) + 1) (by positivity) f ∈ (G).domain ∧
      action ε hε h ((n : ℝ) + 1) (by positivity) f ∈ (S t).domain := fun n =>
    ⟨hJcore n,
      positive_vacuum_unconditionalCore_le_hamiltonian_domain
        ε hε h hb hh m g k hk t (hJcore n),
      (hJcore n).1.1,
      hJS n⟩
  have hT_lim : Tendsto (fun n : ℕ =>
      T ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        static_resolvent_domain ε hε h ((n : ℝ) + 1) (by positivity) hb hh f hfT⟩)
      atTop (𝓝 (T ⟨f, hfT⟩)) :=
    static_resolvent_tendsto ε hε h hb hh ⟨f, hfT⟩
  have hP_lim : Tendsto (fun n : ℕ =>
      P ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        LinearPMap.mem_domain_of_mem_graph (hpSeq n)⟩)
      atTop (𝓝 (P ⟨f, hfP⟩)) :=
    (shifted_sequence_tendsto ε hε h (-h) (neg_shift_bound ε h hbn) (P ⟨f, hfP⟩)).congr
      (fun n => ((P).mem_graph_snd_inj'
        ((P).mem_graph ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
          LinearPMap.mem_domain_of_mem_graph (hpSeq n)⟩)
        (hpSeq n) rfl).symm)
  have hS_f : S t ⟨f, hfS⟩ = T ⟨f, hfT⟩ + (Real.exp (2 * t) : ℂ) • P ⟨f, hfP⟩ :=
    (S t).mem_graph_snd_inj' ((S t).mem_graph ⟨f, hfS⟩)
      (unconditional_three_operator_residual_graph ε hε h hh hb m g k t
        f (T ⟨f, hfT⟩) (P ⟨f, hfP⟩)
        ((T).mem_graph ⟨f, hfT⟩) ((P).mem_graph ⟨f, hfP⟩) hmem.2) rfl
  have hS_lim : Tendsto (fun n : ℕ =>
      S t ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f, hJS n⟩)
      atTop (𝓝 (S t ⟨f, hfS⟩)) := by
    rw [hS_f]
    exact (hT_lim.add (hP_lim.const_smul (Real.exp (2 * t) : ℂ))).congr (fun n => by
      have hreg := positive_vacuum_resolvent_regularizes_static_potential_into_hamiltonian
        ε hε h ((n : ℝ) + 1) (by positivity) hb hh m g k hk t hfT hfP (hpSeq n)
      have hP_eq := hreg.2.2.2.1
      have hS_eq := hreg.2.2.2.2.2.1
      rw [hP_eq, hS_eq])
  exact ⟨hdom,
    sequence_tendsto ε hε h f,
    hT_lim,
    hP_lim,
    hS_lim,
    resolvent_clockHalf_tendsto ε hε h f hfC⟩

#print axioms unconditionalCore_mem_iff
#print axioms unconditionalCore_eq_three_operator_domain
#print axioms unconditionalCore_eq_static_inter_growing
#print axioms unconditionalCore_le_clockHalf_domain
#print axioms unconditionalCore_inf_clockHalf_eq
#print axioms commonOperatorDomain_eq_unconditionalCore_inf_residualForm
#print axioms resolvent_mem_unconditionalCore_iff_potential
#print axioms resolvent_mem_unconditionalCore_iff_growing
#print axioms resolvent_mem_unconditionalCore_equiv
#print axioms resolvent_mem_commonOperatorDomain_iff_potential
#print axioms resolvent_mem_commonOperatorDomain_iff_growing
#print axioms resolvent_mem_unconditionalCore_of_potential_graph
#print axioms resolvent_mem_commonOperatorDomain_of_potential_graph
#print axioms resolvent_five_operator_eval_of_potential_graph
#print axioms resolvent_seven_operator_eval_on_common_of_potential_graph
#print axioms unconditionalCore_resolvent_invariant
#print axioms unconditionalCore_yosida_invariant
#print axioms commonOperatorDomain_resolvent_invariant
#print axioms commonOperatorDomain_yosida_invariant
#print axioms seven_operator_resolvent_invariance_and_eval
#print axioms seven_operator_simultaneous_strong_convergence_of_potential_graph
#print axioms seven_operator_simultaneous_strong_convergence
#print axioms positive_vacuum_unconditionalCore_eq_commonOperatorDomain
#print axioms positive_vacuum_hamiltonian_growing_domain_eq_unconditionalCore
#print axioms positive_vacuum_hamiltonian_static_domain_eq_unconditionalCore
#print axioms positive_vacuum_hamiltonian_potential_domain_eq_unconditionalCore
#print axioms positive_vacuum_residual_growing_domain_eq_unconditionalCore
#print axioms positive_vacuum_unconditionalCore_le_hamiltonian_domain
#print axioms positive_vacuum_unconditionalCore_le_residual_domain
#print axioms positive_vacuum_resolvent_regularizes_static_potential_into_hamiltonian
#print axioms residual_inter_potential_domain_eq_static_potential_residualForm
#print axioms positive_vacuum_residual_resolvent_regularization_and_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialResolventMultiOperatorSynthesis
