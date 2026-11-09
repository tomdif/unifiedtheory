/- Finite-superposition operator-domain closure, finite-sum linearity, and evolved
trajectory domination on the three-operator domain `Dom T ∩ Dom K ∩ Dom P`, on the
unconditional common operator domain `commonOperatorDomain`, and on the reference
form space `RV` under the nonautonomous quantum evolution `U(s, t)`. -/
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain
import UnifiedTheory.Audit.KFCausalClockFloorEvolvedFormEnergyRegularity

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalFiniteThreeOperatorEvolvedDomination
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorAveragedTimeControl (timeEnergy)
open KFCausalClockFloorAveragedFormFlow (formFlow)
open KFCausalClockFloorAveragedEvolution (evolution evolution_embedding)
open KFCausalClockFloorUnconditionalTwoTimeEvolution
  (commonOperatorDomain
   common_domain_subset_hamiltonian
   common_domain_subset_residual
   common_domain_subset_growing
   unconditional_two_time_residual_difference
   unconditional_two_time_hamiltonian_growing_difference
   unconditional_two_time_hamiltonian_three_operator_difference)
open KFCausalClockFloorTwoTimeResolventDifference
  (hamiltonian_resolvent_two_time_action_sub
   hamiltonian_resolvent_two_time_three_operator_sub
   hamiltonian_resolvent_two_time_norm_bound
   hamiltonian_resolvent_two_time_component_norm_bound
   residual_resolvent_two_time_action_sub
   residual_resolvent_two_time_norm_bound)
open KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain
  (static_root_subset_clockHalf_domain
   static_root_clockHalf_norm_le
   static_domain_le_clockHalf_domain
   unconditional_two_operator_growing_eval
   positive_vacuum_three_operator_hamiltonian_eval
   positive_vacuum_three_operator_residual_eval
   positive_vacuum_three_operator_in_averaged_domain
   positive_vacuum_three_operator_in_residual_domain
   positive_vacuum_common_domain_eq_three_operator)
open KFCausalClockFloorEvolvedFormEnergyRegularity
  (evolved_mem_averaged_domain
   evolved_mem_staticRoot_domain
   evolved_mem_radialRoot_domain
   evolved_mem_potentialForm_domain
   evolved_mem_growingForm_domain
   evolved_mem_residualForm_domain
   instantFormEnergy
   evolved_instantFormEnergy_eq_three_channel
   evolved_instantFormEnergy_le_max_initial
   evolved_dynamical_energy_le
   evolved_staticRoot_norm_sq_le
   evolved_growingForm_norm_sq_le
   evolved_radialRoot_norm_sq_le
   evolved_potentialForm_norm_sq_le
   evolved_residualForm_norm_sq_le_max_initial)

private theorem prod_mk_sum {ι α β : Type*} [AddCommMonoid α] [AddCommMonoid β]
    (S : Finset ι) (f : ι → α) (g : ι → β) :
    (∑ i ∈ S, f i, ∑ i ∈ S, g i) = ∑ i ∈ S, (f i, g i) := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

private theorem linearPMap_sum_mem_of_mem {ι Y : Type*}
    [AddCommGroup Y] [Module ℂ Y]
    (A : Hilbert →ₗ.[ℂ] Y) (S : Finset ι) (c : ι → ℂ) (u : ι → Hilbert)
    (hu : ∀ i ∈ S, u i ∈ A.domain) :
    (∑ i ∈ S, c i • u i) ∈ A.domain :=
  A.domain.sum_mem (fun i hi => A.domain.smul_mem (c i) (hu i hi))

private theorem linearPMap_sum_mem {ι Y : Type*}
    [AddCommGroup Y] [Module ℂ Y]
    (A : Hilbert →ₗ.[ℂ] Y) (S : Finset ι) (c : ι → ℂ) (u : ι → Hilbert)
    (hu : ∀ i, u i ∈ A.domain) :
    (∑ i ∈ S, c i • u i) ∈ A.domain :=
  A.domain.sum_mem (fun i _ => A.domain.smul_mem (c i) (hu i))

private theorem linearPMap_sum_eval {ι Y : Type*}
    [AddCommGroup Y] [Module ℂ Y]
    (A : Hilbert →ₗ.[ℂ] Y) (S : Finset ι) (c : ι → ℂ) (u : ι → Hilbert)
    (hu : ∀ i, u i ∈ A.domain)
    (hsum : (∑ i ∈ S, c i • u i) ∈ A.domain) :
    A ⟨∑ i ∈ S, c i • u i, hsum⟩ = ∑ i ∈ S, c i • A ⟨u i, hu i⟩ := by
  have hs := A.graph.sum_mem (fun i (_ : i ∈ S) =>
    A.graph.smul_mem (c i) (A.mem_graph ⟨u i, hu i⟩))
  have hg : (∑ i ∈ S, c i • u i, ∑ i ∈ S, c i • A ⟨u i, hu i⟩) ∈ A.graph := by
    rwa [prod_mk_sum]
  exact A.mem_graph_snd_inj' (A.mem_graph ⟨∑ i ∈ S, c i • u i, hsum⟩) hg rfl

private theorem linearPMap_sum_norm_le {ι Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (A : Hilbert →ₗ.[ℂ] Y) (S : Finset ι) (c : ι → ℂ) (u : ι → Hilbert)
    (hu : ∀ i, u i ∈ A.domain)
    (hsum : (∑ i ∈ S, c i • u i) ∈ A.domain) :
    ‖A ⟨∑ i ∈ S, c i • u i, hsum⟩‖ ≤ ∑ i ∈ S, ‖c i‖ * ‖A ⟨u i, hu i⟩‖ := by
  rw [linearPMap_sum_eval A S c u hu hsum]
  refine (norm_sum_le S _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [norm_smul]

private theorem linearPMap_congr_eval {Y : Type*}
    [AddCommGroup Y] [Module ℂ Y]
    (A : Hilbert →ₗ.[ℂ] Y) {x y : Hilbert} (hxy : x = y)
    (hx : x ∈ A.domain) (hy : y ∈ A.domain) :
    A ⟨x, hx⟩ = A ⟨y, hy⟩ := by
  have hsub : (⟨x, hx⟩ : A.domain) = ⟨y, hy⟩ := Subtype.ext hxy
  exact congrArg A hsub

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "RV" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hw m g k 0
local notation "RJ" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hw m g k 0
local notation "U" => evolution ε hε h hh hw m g k
local notation "E" => timeEnergy ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (hamiltonian_bound ε h hw) hh m g k
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "S_op" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k

/-! ### 1. Finite-Superposition Domain Closure and Linearity on `Dom T ∩ Dom K ∩ Dom P` -/

abbrev finiteCombo {ι : Type*} (S : Finset ι) (c : ι → ℂ) (u : ι → Hilbert) : Hilbert :=
  ∑ i ∈ S, c i • u i

theorem finiteCombo_mem_three_operator_and_clockHalf {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (u : ι → Hilbert)
    (hu : ∀ i ∈ S, u i ∈ (T).domain ⊓ (K).domain ⊓ (P).domain) :
    finiteCombo S c u ∈
      (T).domain ⊓ (K).domain ⊓ (P).domain ⊓ (G).domain ⊓ (clockHalf ε).domain := by
  have h3 : finiteCombo S c u ∈ (T).domain ⊓ (K).domain ⊓ (P).domain :=
    ((T).domain ⊓ (K).domain ⊓ (P).domain).sum_mem
      (fun i hi => ((T).domain ⊓ (K).domain ⊓ (P).domain).smul_mem (c i) (hu i hi))
  have hG : finiteCombo S c u ∈ (G).domain :=
    (unconditional_two_operator_growing_eval ε hε h hh hb m g k h3.1.2 h3.2).choose
  have hC : finiteCombo S c u ∈ (clockHalf ε).domain :=
    static_domain_le_clockHalf_domain ε hε h h3.1.1
  exact ⟨⟨h3, hG⟩, hC⟩

theorem finiteCombo_mem_commonOperatorDomain {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (u : ι → Hilbert)
    (hu : ∀ i ∈ S, u i ∈ commonOperatorDomain ε hε h hh hb m g k) :
    finiteCombo S c u ∈ commonOperatorDomain ε hε h hh hb m g k :=
  (commonOperatorDomain ε hε h hh hb m g k).sum_mem
    (fun i hi => (commonOperatorDomain ε hε h hh hb m g k).smul_mem (c i) (hu i hi))

theorem finiteCombo_common_mem_hamiltonian_and_residual {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (u : ι → Hilbert)
    (hu : ∀ i ∈ S, u i ∈ commonOperatorDomain ε hε h hh hb m g k) (t : ℝ) :
    finiteCombo S c u ∈ (H t).domain ∧
    finiteCombo S c u ∈ (S_op t).domain ∧
    finiteCombo S c u ∈ (G).domain ∧
    finiteCombo S c u ∈ (clockHalf ε).domain := by
  have hc := finiteCombo_mem_commonOperatorDomain ε hε h hh hb m g k S c u hu
  exact ⟨common_domain_subset_hamiltonian ε hε h hh hb m g k t hc,
    common_domain_subset_residual ε hε h hh hb m g k t hc,
    common_domain_subset_growing ε hε h hh hb m g k hc,
    static_domain_le_clockHalf_domain ε hε h hc.1.1.1⟩

theorem positive_vacuum_finiteCombo_mem_all_domains (hk : 0 < k) {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (u : ι → Hilbert)
    (hu : ∀ i ∈ S, u i ∈ (T).domain ⊓ (K).domain ⊓ (P).domain) (t : ℝ) :
    finiteCombo S c u ∈ (H t).domain ∧
    finiteCombo S c u ∈ (S_op t).domain ∧
    finiteCombo S c u ∈ (G).domain ∧
    finiteCombo S c u ∈ (Eavg t).domain ∧
    finiteCombo S c u ∈ (Tres t).domain ∧
    finiteCombo S c u ∈ (clockHalf ε).domain := by
  have h5 := finiteCombo_mem_three_operator_and_clockHalf ε hε h hh hb m g k S c u hu
  have hT := h5.1.1.1.1
  have hK := h5.1.1.1.2
  have hP := h5.1.1.2
  exact ⟨(positive_vacuum_three_operator_hamiltonian_eval ε hε h hh hb m g k hk t hT hK hP).choose,
    (positive_vacuum_three_operator_residual_eval ε hε h hh hb m g k hk t hT hK hP).choose,
    h5.1.2,
    positive_vacuum_three_operator_in_averaged_domain ε hε h hh hb m g k hk t hT hK hP,
    positive_vacuum_three_operator_in_residual_domain ε hε h hh hb m g k hk t hT hK hP,
    h5.2⟩

theorem finiteCombo_static_eval {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (u : ι → Hilbert) (huT : ∀ i, u i ∈ (T).domain) :
    T ⟨finiteCombo S c u, linearPMap_sum_mem T S c u huT⟩ =
      ∑ i ∈ S, c i • T ⟨u i, huT i⟩ :=
  linearPMap_sum_eval T S c u huT (linearPMap_sum_mem T S c u huT)

theorem finiteCombo_radial_eval {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (u : ι → Hilbert) (huK : ∀ i, u i ∈ (K).domain) :
    K ⟨finiteCombo S c u, linearPMap_sum_mem K S c u huK⟩ =
      ∑ i ∈ S, c i • K ⟨u i, huK i⟩ :=
  linearPMap_sum_eval K S c u huK (linearPMap_sum_mem K S c u huK)

theorem finiteCombo_potential_eval {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (u : ι → Hilbert) (huP : ∀ i, u i ∈ (P).domain) :
    P ⟨finiteCombo S c u, linearPMap_sum_mem P S c u huP⟩ =
      ∑ i ∈ S, c i • P ⟨u i, huP i⟩ :=
  linearPMap_sum_eval P S c u huP (linearPMap_sum_mem P S c u huP)

theorem finiteCombo_clockHalf_eval {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (u : ι → Hilbert) (huC : ∀ i, u i ∈ (clockHalf ε).domain) :
    clockHalf ε ⟨finiteCombo S c u, linearPMap_sum_mem (clockHalf ε) S c u huC⟩ =
      ∑ i ∈ S, c i • clockHalf ε ⟨u i, huC i⟩ :=
  linearPMap_sum_eval (clockHalf ε) S c u huC (linearPMap_sum_mem (clockHalf ε) S c u huC)

theorem finiteCombo_growing_two_operator_eval {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (u : ι → Hilbert)
    (huK : ∀ i, u i ∈ (K).domain) (huP : ∀ i, u i ∈ (P).domain) :
    ∃ hG : finiteCombo S c u ∈ (G).domain,
      G ⟨finiteCombo S c u, hG⟩ =
        (∑ i ∈ S, c i • K ⟨u i, huK i⟩) + (∑ i ∈ S, c i • P ⟨u i, huP i⟩) ∧
      G ⟨finiteCombo S c u, hG⟩ =
        ∑ i ∈ S, c i • (K ⟨u i, huK i⟩ + P ⟨u i, huP i⟩) := by
  have hK : finiteCombo S c u ∈ (K).domain := linearPMap_sum_mem K S c u huK
  have hP : finiteCombo S c u ∈ (P).domain := linearPMap_sum_mem P S c u huP
  have hgev := unconditional_two_operator_growing_eval ε hε h hh hb m g k hK hP
  refine ⟨hgev.choose, ?_, ?_⟩
  · rw [hgev.choose_spec,
      linearPMap_sum_eval K S c u huK hK,
      linearPMap_sum_eval P S c u huP hP]
  · rw [hgev.choose_spec,
      linearPMap_sum_eval K S c u huK hK,
      linearPMap_sum_eval P S c u huP hP,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => (smul_add (c i) _ _).symm)

theorem positive_vacuum_finiteCombo_hamiltonian_eval (hk : 0 < k) (t : ℝ) {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (u : ι → Hilbert)
    (huT : ∀ i, u i ∈ (T).domain) (huK : ∀ i, u i ∈ (K).domain) (huP : ∀ i, u i ∈ (P).domain) :
    ∃ hH : finiteCombo S c u ∈ (H t).domain,
      H t ⟨finiteCombo S c u, hH⟩ =
        (∑ i ∈ S, c i • T ⟨u i, huT i⟩) +
          (Real.exp (2 * t) : ℂ) •
            ((∑ i ∈ S, c i • K ⟨u i, huK i⟩) + (∑ i ∈ S, c i • P ⟨u i, huP i⟩)) ∧
      H t ⟨finiteCombo S c u, hH⟩ =
        ∑ i ∈ S, c i •
          (T ⟨u i, huT i⟩ + (Real.exp (2 * t) : ℂ) • (K ⟨u i, huK i⟩ + P ⟨u i, huP i⟩)) := by
  have hT : finiteCombo S c u ∈ (T).domain := linearPMap_sum_mem T S c u huT
  have hK : finiteCombo S c u ∈ (K).domain := linearPMap_sum_mem K S c u huK
  have hP : finiteCombo S c u ∈ (P).domain := linearPMap_sum_mem P S c u huP
  have hhev := positive_vacuum_three_operator_hamiltonian_eval ε hε h hh hb m g k hk t hT hK hP
  have h1 : H t ⟨finiteCombo S c u, hhev.choose⟩ =
      (∑ i ∈ S, c i • T ⟨u i, huT i⟩) +
        (Real.exp (2 * t) : ℂ) •
          ((∑ i ∈ S, c i • K ⟨u i, huK i⟩) + (∑ i ∈ S, c i • P ⟨u i, huP i⟩)) := by
    rw [hhev.choose_spec,
      linearPMap_sum_eval T S c u huT hT,
      linearPMap_sum_eval K S c u huK hK,
      linearPMap_sum_eval P S c u huP hP]
  refine ⟨hhev.choose, h1, ?_⟩
  rw [h1, ← Finset.sum_add_distrib, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← smul_add (c i), smul_comm ((Real.exp (2 * t) : ℂ)) (c i), ← smul_add (c i)]

theorem positive_vacuum_finiteCombo_residual_eval (hk : 0 < k) (t : ℝ) {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (u : ι → Hilbert)
    (huT : ∀ i, u i ∈ (T).domain) (huK : ∀ i, u i ∈ (K).domain) (huP : ∀ i, u i ∈ (P).domain) :
    ∃ hS : finiteCombo S c u ∈ (S_op t).domain,
      S_op t ⟨finiteCombo S c u, hS⟩ =
        (∑ i ∈ S, c i • T ⟨u i, huT i⟩) +
          (Real.exp (2 * t) : ℂ) • (∑ i ∈ S, c i • P ⟨u i, huP i⟩) ∧
      S_op t ⟨finiteCombo S c u, hS⟩ =
        ∑ i ∈ S, c i • (T ⟨u i, huT i⟩ + (Real.exp (2 * t) : ℂ) • P ⟨u i, huP i⟩) := by
  have hT : finiteCombo S c u ∈ (T).domain := linearPMap_sum_mem T S c u huT
  have hK : finiteCombo S c u ∈ (K).domain := linearPMap_sum_mem K S c u huK
  have hP : finiteCombo S c u ∈ (P).domain := linearPMap_sum_mem P S c u huP
  have hsev := positive_vacuum_three_operator_residual_eval ε hε h hh hb m g k hk t hT hK hP
  have h1 : S_op t ⟨finiteCombo S c u, hsev.choose⟩ =
      (∑ i ∈ S, c i • T ⟨u i, huT i⟩) +
        (Real.exp (2 * t) : ℂ) • (∑ i ∈ S, c i • P ⟨u i, huP i⟩) := by
    rw [hsev.choose_spec,
      linearPMap_sum_eval T S c u huT hT,
      linearPMap_sum_eval P S c u huP hP]
  refine ⟨hsev.choose, h1, ?_⟩
  rw [h1, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [smul_comm ((Real.exp (2 * t) : ℂ)) (c i), ← smul_add (c i)]

theorem finiteCombo_common_two_time_hamiltonian_difference (t s : ℝ) {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (u : ι → Hilbert)
    (hu : ∀ i, u i ∈ commonOperatorDomain ε hε h hh hb m g k) :
    let hc := finiteCombo_mem_commonOperatorDomain ε hε h hh hb m g k S c u (fun i _ => hu i);
    H t ⟨finiteCombo S c u, common_domain_subset_hamiltonian ε hε h hh hb m g k t hc⟩ -
      H s ⟨finiteCombo S c u, common_domain_subset_hamiltonian ε hε h hh hb m g k s hc⟩ =
      ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) •
        ∑ i ∈ S, c i • (K ⟨u i, (hu i).1.1.2⟩ + P ⟨u i, (hu i).1.2⟩) := by
  intro hc
  rw [unconditional_two_time_hamiltonian_three_operator_difference ε hε h hh hb m g k t s
      (finiteCombo S c u) hc,
    linearPMap_sum_eval K S c u (fun i => (hu i).1.1.2) hc.1.1.2,
    linearPMap_sum_eval P S c u (fun i => (hu i).1.2) hc.1.2,
    ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => (smul_add (c i) _ _).symm)

theorem finiteCombo_common_two_time_resolvent_sub (t s a : ℝ) (ha : 0 < a) {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (u : ι → Hilbert)
    (hu : ∀ i, u i ∈ commonOperatorDomain ε hε h hh hb m g k) :
    let hc := finiteCombo_mem_commonOperatorDomain ε hε h hh hb m g k S c u (fun i _ => hu i);
    finiteCombo S c u -
      RH t a (H s ⟨finiteCombo S c u, common_domain_subset_hamiltonian ε hε h hh hb m g k s hc⟩ +
        a • finiteCombo S c u) =
      ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) •
        ∑ i ∈ S, c i • RH t a (K ⟨u i, (hu i).1.1.2⟩ + P ⟨u i, (hu i).1.2⟩) := by
  intro hc
  rw [hamiltonian_resolvent_two_time_three_operator_sub ε hε h hh hb m g k t s a ha
      (finiteCombo S c u) hc,
    linearPMap_sum_eval K S c u (fun i => (hu i).1.1.2) hc.1.1.2,
    linearPMap_sum_eval P S c u (fun i => (hu i).1.2) hc.1.2,
    ← Finset.sum_add_distrib, map_sum]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← smul_add (c i), map_smul]

theorem finiteCombo_common_two_time_resolvent_norm_bound (t s a : ℝ) (ha : 0 < a) {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (u : ι → Hilbert)
    (hu : ∀ i, u i ∈ commonOperatorDomain ε hε h hh hb m g k) :
    let hc := finiteCombo_mem_commonOperatorDomain ε hε h hh hb m g k S c u (fun i _ => hu i);
    ‖finiteCombo S c u -
      RH t a (H s ⟨finiteCombo S c u, common_domain_subset_hamiltonian ε hε h hh hb m g k s hc⟩ +
        a • finiteCombo S c u)‖ ≤
      a⁻¹ * |Real.exp (2 * t) - Real.exp (2 * s)| *
        ∑ i ∈ S, ‖c i‖ * (‖K ⟨u i, (hu i).1.1.2⟩‖ + ‖P ⟨u i, (hu i).1.2⟩‖) := by
  intro hc
  have h1 := hamiltonian_resolvent_two_time_component_norm_bound ε hε h hh hb m g k t s a ha
    (finiteCombo S c u) hc
  have hK := linearPMap_sum_norm_le K S c u (fun i => (hu i).1.1.2) hc.1.1.2
  have hP := linearPMap_sum_norm_le P S c u (fun i => (hu i).1.2) hc.1.2
  have hsum : ‖K ⟨finiteCombo S c u, hc.1.1.2⟩‖ + ‖P ⟨finiteCombo S c u, hc.1.2⟩‖ ≤
      ∑ i ∈ S, ‖c i‖ * (‖K ⟨u i, (hu i).1.1.2⟩‖ + ‖P ⟨u i, (hu i).1.2⟩‖) := by
    calc
      ‖K ⟨finiteCombo S c u, hc.1.1.2⟩‖ + ‖P ⟨finiteCombo S c u, hc.1.2⟩‖ ≤
          (∑ i ∈ S, ‖c i‖ * ‖K ⟨u i, (hu i).1.1.2⟩‖) +
            (∑ i ∈ S, ‖c i‖ * ‖P ⟨u i, (hu i).1.2⟩‖) := add_le_add hK hP
      _ = ∑ i ∈ S, (‖c i‖ * ‖K ⟨u i, (hu i).1.1.2⟩‖ + ‖c i‖ * ‖P ⟨u i, (hu i).1.2⟩‖) :=
          (Finset.sum_add_distrib).symm
      _ = ∑ i ∈ S, ‖c i‖ * (‖K ⟨u i, (hu i).1.1.2⟩‖ + ‖P ⟨u i, (hu i).1.2⟩‖) :=
          Finset.sum_congr rfl (fun i _ => (mul_add _ _ _).symm)
  exact h1.trans (mul_le_mul_of_nonneg_left hsum
    (mul_nonneg (inv_nonneg.mpr ha.le) (abs_nonneg _)))

/-! ### 2. Evolved Finite Superpositions on `RV` Along `U(s, t)` -/

def finiteFormCombo {ι : Type*} (S : Finset ι) (c : ι → ℂ) (v : ι → RV) : RV :=
  ∑ i ∈ S, c i • v i

theorem finiteFormCombo_embedding {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (v : ι → RV) :
    RJ (finiteFormCombo ε hε h hh hb m g k S c v) =
      ∑ i ∈ S, c i • RJ (v i) := by
  unfold finiteFormCombo
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => map_smul _ (c i) (v i))

theorem evolved_finiteFormCombo_eq_sum (s t : ℝ) {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (v : ι → RV) :
    U s t (RJ (finiteFormCombo ε hε h hh hb m g k S c v)) =
      ∑ i ∈ S, c i • U s t (RJ (v i)) := by
  rw [finiteFormCombo_embedding, map_sum]
  exact Finset.sum_congr rfl (fun i _ => map_smul _ (c i) (RJ (v i)))

theorem evolved_finiteFormCombo_mem_all_domains (s t r : ℝ) {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (v : ι → RV) :
    let u := finiteFormCombo ε hε h hh hb m g k S c v;
    U s t (RJ u) ∈ (Eavg r).domain ∧
    U s t (RJ u) ∈ (Tstat).domain ∧
    U s t (RJ u) ∈ (Kroot).domain ∧
    U s t (RJ u) ∈ (Tpot).domain ∧
    U s t (RJ u) ∈ (Tgrow).domain ∧
    U s t (RJ u) ∈ (Tres r).domain ∧
    U s t (RJ u) ∈ (clockHalf ε).domain := by
  intro u
  exact ⟨evolved_mem_averaged_domain ε hε h hh hb m g k s t r u,
    evolved_mem_staticRoot_domain ε hε h hh hb m g k s t u,
    evolved_mem_radialRoot_domain ε hε h hh hb m g k s t u,
    evolved_mem_potentialForm_domain ε hε h hh hb m g k s t u,
    evolved_mem_growingForm_domain ε hε h hh hb m g k s t u,
    evolved_mem_residualForm_domain ε hε h hh hb m g k s t r u,
    static_root_subset_clockHalf_domain ε hε h (U s t (RJ u))
      (evolved_mem_staticRoot_domain ε hε h hh hb m g k s t u)⟩

theorem evolved_finiteFormCombo_staticRoot_eval (s t : ℝ) {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (v : ι → RV) :
    Tstat ⟨U s t (RJ (finiteFormCombo ε hε h hh hb m g k S c v)),
        evolved_mem_staticRoot_domain ε hε h hh hb m g k s t
          (finiteFormCombo ε hε h hh hb m g k S c v)⟩ =
      ∑ i ∈ S, c i • Tstat ⟨U s t (RJ (v i)),
        evolved_mem_staticRoot_domain ε hε h hh hb m g k s t (v i)⟩ := by
  have heq := evolved_finiteFormCombo_eq_sum ε hε h hh hb m g k s t S c v
  have hmem := fun i => evolved_mem_staticRoot_domain ε hε h hh hb m g k s t (v i)
  exact (linearPMap_congr_eval Tstat heq
    (evolved_mem_staticRoot_domain ε hε h hh hb m g k s t
      (finiteFormCombo ε hε h hh hb m g k S c v))
    (linearPMap_sum_mem Tstat S c (fun i => U s t (RJ (v i))) hmem)).trans
    (linearPMap_sum_eval Tstat S c (fun i => U s t (RJ (v i))) hmem
      (linearPMap_sum_mem Tstat S c (fun i => U s t (RJ (v i))) hmem))

theorem evolved_finiteFormCombo_radialRoot_eval (s t : ℝ) {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (v : ι → RV) :
    Kroot ⟨U s t (RJ (finiteFormCombo ε hε h hh hb m g k S c v)),
        evolved_mem_radialRoot_domain ε hε h hh hb m g k s t
          (finiteFormCombo ε hε h hh hb m g k S c v)⟩ =
      ∑ i ∈ S, c i • Kroot ⟨U s t (RJ (v i)),
        evolved_mem_radialRoot_domain ε hε h hh hb m g k s t (v i)⟩ := by
  have heq := evolved_finiteFormCombo_eq_sum ε hε h hh hb m g k s t S c v
  have hmem := fun i => evolved_mem_radialRoot_domain ε hε h hh hb m g k s t (v i)
  exact (linearPMap_congr_eval Kroot heq
    (evolved_mem_radialRoot_domain ε hε h hh hb m g k s t
      (finiteFormCombo ε hε h hh hb m g k S c v))
    (linearPMap_sum_mem Kroot S c (fun i => U s t (RJ (v i))) hmem)).trans
    (linearPMap_sum_eval Kroot S c (fun i => U s t (RJ (v i))) hmem
      (linearPMap_sum_mem Kroot S c (fun i => U s t (RJ (v i))) hmem))

theorem evolved_finiteFormCombo_potentialForm_eval (s t : ℝ) {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (v : ι → RV) :
    Tpot ⟨U s t (RJ (finiteFormCombo ε hε h hh hb m g k S c v)),
        evolved_mem_potentialForm_domain ε hε h hh hb m g k s t
          (finiteFormCombo ε hε h hh hb m g k S c v)⟩ =
      ∑ i ∈ S, c i • Tpot ⟨U s t (RJ (v i)),
        evolved_mem_potentialForm_domain ε hε h hh hb m g k s t (v i)⟩ := by
  have heq := evolved_finiteFormCombo_eq_sum ε hε h hh hb m g k s t S c v
  have hmem := fun i => evolved_mem_potentialForm_domain ε hε h hh hb m g k s t (v i)
  exact (linearPMap_congr_eval Tpot heq
    (evolved_mem_potentialForm_domain ε hε h hh hb m g k s t
      (finiteFormCombo ε hε h hh hb m g k S c v))
    (linearPMap_sum_mem Tpot S c (fun i => U s t (RJ (v i))) hmem)).trans
    (linearPMap_sum_eval Tpot S c (fun i => U s t (RJ (v i))) hmem
      (linearPMap_sum_mem Tpot S c (fun i => U s t (RJ (v i))) hmem))

theorem evolved_finiteFormCombo_growingForm_eval (s t : ℝ) {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (v : ι → RV) :
    Tgrow ⟨U s t (RJ (finiteFormCombo ε hε h hh hb m g k S c v)),
        evolved_mem_growingForm_domain ε hε h hh hb m g k s t
          (finiteFormCombo ε hε h hh hb m g k S c v)⟩ =
      ∑ i ∈ S, c i • Tgrow ⟨U s t (RJ (v i)),
        evolved_mem_growingForm_domain ε hε h hh hb m g k s t (v i)⟩ := by
  have heq := evolved_finiteFormCombo_eq_sum ε hε h hh hb m g k s t S c v
  have hmem := fun i => evolved_mem_growingForm_domain ε hε h hh hb m g k s t (v i)
  exact (linearPMap_congr_eval Tgrow heq
    (evolved_mem_growingForm_domain ε hε h hh hb m g k s t
      (finiteFormCombo ε hε h hh hb m g k S c v))
    (linearPMap_sum_mem Tgrow S c (fun i => U s t (RJ (v i))) hmem)).trans
    (linearPMap_sum_eval Tgrow S c (fun i => U s t (RJ (v i))) hmem
      (linearPMap_sum_mem Tgrow S c (fun i => U s t (RJ (v i))) hmem))

theorem evolved_finiteFormCombo_residualForm_eval (s t r : ℝ) {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (v : ι → RV) :
    Tres r ⟨U s t (RJ (finiteFormCombo ε hε h hh hb m g k S c v)),
        evolved_mem_residualForm_domain ε hε h hh hb m g k s t r
          (finiteFormCombo ε hε h hh hb m g k S c v)⟩ =
      ∑ i ∈ S, c i • Tres r ⟨U s t (RJ (v i)),
        evolved_mem_residualForm_domain ε hε h hh hb m g k s t r (v i)⟩ := by
  have heq := evolved_finiteFormCombo_eq_sum ε hε h hh hb m g k s t S c v
  have hmem := fun i => evolved_mem_residualForm_domain ε hε h hh hb m g k s t r (v i)
  exact (linearPMap_congr_eval (Tres r) heq
    (evolved_mem_residualForm_domain ε hε h hh hb m g k s t r
      (finiteFormCombo ε hε h hh hb m g k S c v))
    (linearPMap_sum_mem (Tres r) S c (fun i => U s t (RJ (v i))) hmem)).trans
    (linearPMap_sum_eval (Tres r) S c (fun i => U s t (RJ (v i))) hmem
      (linearPMap_sum_mem (Tres r) S c (fun i => U s t (RJ (v i))) hmem))

theorem evolved_finiteFormCombo_clockHalf_eval (s t : ℝ) {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (v : ι → RV) :
    clockHalf ε ⟨U s t (RJ (finiteFormCombo ε hε h hh hb m g k S c v)),
        static_root_subset_clockHalf_domain ε hε h _
          (evolved_mem_staticRoot_domain ε hε h hh hb m g k s t
            (finiteFormCombo ε hε h hh hb m g k S c v))⟩ =
      ∑ i ∈ S, c i • clockHalf ε ⟨U s t (RJ (v i)),
        static_root_subset_clockHalf_domain ε hε h _
          (evolved_mem_staticRoot_domain ε hε h hh hb m g k s t (v i))⟩ := by
  have heq := evolved_finiteFormCombo_eq_sum ε hε h hh hb m g k s t S c v
  have hmem := fun i => static_root_subset_clockHalf_domain ε hε h (U s t (RJ (v i)))
    (evolved_mem_staticRoot_domain ε hε h hh hb m g k s t (v i))
  exact (linearPMap_congr_eval (clockHalf ε) heq
    (static_root_subset_clockHalf_domain ε hε h _
      (evolved_mem_staticRoot_domain ε hε h hh hb m g k s t
        (finiteFormCombo ε hε h hh hb m g k S c v)))
    (linearPMap_sum_mem (clockHalf ε) S c (fun i => U s t (RJ (v i))) hmem)).trans
    (linearPMap_sum_eval (clockHalf ε) S c (fun i => U s t (RJ (v i))) hmem
      (linearPMap_sum_mem (clockHalf ε) S c (fun i => U s t (RJ (v i))) hmem))

/-! ### 3. Evolved Finite-Superposition Norm Domination and Energy Bounds -/

theorem evolved_finiteFormCombo_staticRoot_norm_le (s t : ℝ) {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (v : ι → RV) :
    ‖Tstat ⟨U s t (RJ (finiteFormCombo ε hε h hh hb m g k S c v)),
        evolved_mem_staticRoot_domain ε hε h hh hb m g k s t
          (finiteFormCombo ε hε h hh hb m g k S c v)⟩‖ ≤
      ∑ i ∈ S, ‖c i‖ * ‖Tstat ⟨U s t (RJ (v i)),
        evolved_mem_staticRoot_domain ε hε h hh hb m g k s t (v i)⟩‖ := by
  rw [evolved_finiteFormCombo_staticRoot_eval]
  refine (norm_sum_le S _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [norm_smul]

theorem evolved_finiteFormCombo_radialRoot_norm_le (s t : ℝ) {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (v : ι → RV) :
    ‖Kroot ⟨U s t (RJ (finiteFormCombo ε hε h hh hb m g k S c v)),
        evolved_mem_radialRoot_domain ε hε h hh hb m g k s t
          (finiteFormCombo ε hε h hh hb m g k S c v)⟩‖ ≤
      ∑ i ∈ S, ‖c i‖ * ‖Kroot ⟨U s t (RJ (v i)),
        evolved_mem_radialRoot_domain ε hε h hh hb m g k s t (v i)⟩‖ := by
  rw [evolved_finiteFormCombo_radialRoot_eval]
  refine (norm_sum_le S _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [norm_smul]

theorem evolved_finiteFormCombo_potentialForm_norm_le (s t : ℝ) {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (v : ι → RV) :
    ‖Tpot ⟨U s t (RJ (finiteFormCombo ε hε h hh hb m g k S c v)),
        evolved_mem_potentialForm_domain ε hε h hh hb m g k s t
          (finiteFormCombo ε hε h hh hb m g k S c v)⟩‖ ≤
      ∑ i ∈ S, ‖c i‖ * ‖Tpot ⟨U s t (RJ (v i)),
        evolved_mem_potentialForm_domain ε hε h hh hb m g k s t (v i)⟩‖ := by
  rw [evolved_finiteFormCombo_potentialForm_eval]
  refine (norm_sum_le S _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [norm_smul]

theorem evolved_finiteFormCombo_growingForm_norm_le (s t : ℝ) {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (v : ι → RV) :
    ‖Tgrow ⟨U s t (RJ (finiteFormCombo ε hε h hh hb m g k S c v)),
        evolved_mem_growingForm_domain ε hε h hh hb m g k s t
          (finiteFormCombo ε hε h hh hb m g k S c v)⟩‖ ≤
      ∑ i ∈ S, ‖c i‖ * ‖Tgrow ⟨U s t (RJ (v i)),
        evolved_mem_growingForm_domain ε hε h hh hb m g k s t (v i)⟩‖ := by
  rw [evolved_finiteFormCombo_growingForm_eval]
  refine (norm_sum_le S _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [norm_smul]

theorem evolved_finiteFormCombo_residualForm_norm_le (s t r : ℝ) {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (v : ι → RV) :
    ‖Tres r ⟨U s t (RJ (finiteFormCombo ε hε h hh hb m g k S c v)),
        evolved_mem_residualForm_domain ε hε h hh hb m g k s t r
          (finiteFormCombo ε hε h hh hb m g k S c v)⟩‖ ≤
      ∑ i ∈ S, ‖c i‖ * ‖Tres r ⟨U s t (RJ (v i)),
        evolved_mem_residualForm_domain ε hε h hh hb m g k s t r (v i)⟩‖ := by
  rw [evolved_finiteFormCombo_residualForm_eval]
  refine (norm_sum_le S _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [norm_smul]

theorem evolved_finiteFormCombo_clockHalf_norm_le_staticRoot (s t : ℝ) {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (v : ι → RV) :
    ‖clockHalf ε ⟨U s t (RJ (finiteFormCombo ε hε h hh hb m g k S c v)),
        static_root_subset_clockHalf_domain ε hε h _
          (evolved_mem_staticRoot_domain ε hε h hh hb m g k s t
            (finiteFormCombo ε hε h hh hb m g k S c v))⟩‖ ≤
      Real.sqrt 2 *
        ∑ i ∈ S, ‖c i‖ * ‖Tstat ⟨U s t (RJ (v i)),
          evolved_mem_staticRoot_domain ε hε h hh hb m g k s t (v i)⟩‖ := by
  have h1 := static_root_clockHalf_norm_le ε hε h
    (U s t (RJ (finiteFormCombo ε hε h hh hb m g k S c v)))
    (evolved_mem_staticRoot_domain ε hε h hh hb m g k s t
      (finiteFormCombo ε hε h hh hb m g k S c v))
  have h2 := evolved_finiteFormCombo_staticRoot_norm_le ε hε h hh hb m g k s t S c v
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg 2))

theorem evolved_finiteFormCombo_instantFormEnergy_le_max_initial (s t r : ℝ) {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (v : ι → RV) :
    instantFormEnergy ε hε h hh hb m g k s t r
        (finiteFormCombo ε hε h hh hb m g k S c v) ≤
      max 1 (Real.exp (2 * (r - t))) * Real.exp (2 * |t - s|) *
        E s (finiteFormCombo ε hε h hh hb m g k S c v) :=
  evolved_instantFormEnergy_le_max_initial ε hε h hh hb m g k s t r
    (finiteFormCombo ε hε h hh hb m g k S c v)

#print axioms finiteCombo_mem_three_operator_and_clockHalf
#print axioms finiteCombo_mem_commonOperatorDomain
#print axioms finiteCombo_common_mem_hamiltonian_and_residual
#print axioms positive_vacuum_finiteCombo_mem_all_domains
#print axioms finiteCombo_static_eval
#print axioms finiteCombo_radial_eval
#print axioms finiteCombo_potential_eval
#print axioms finiteCombo_clockHalf_eval
#print axioms finiteCombo_growing_two_operator_eval
#print axioms positive_vacuum_finiteCombo_hamiltonian_eval
#print axioms positive_vacuum_finiteCombo_residual_eval
#print axioms finiteCombo_common_two_time_hamiltonian_difference
#print axioms finiteCombo_common_two_time_resolvent_sub
#print axioms finiteCombo_common_two_time_resolvent_norm_bound
#print axioms finiteFormCombo_embedding
#print axioms evolved_finiteFormCombo_eq_sum
#print axioms evolved_finiteFormCombo_mem_all_domains
#print axioms evolved_finiteFormCombo_staticRoot_eval
#print axioms evolved_finiteFormCombo_radialRoot_eval
#print axioms evolved_finiteFormCombo_potentialForm_eval
#print axioms evolved_finiteFormCombo_growingForm_eval
#print axioms evolved_finiteFormCombo_residualForm_eval
#print axioms evolved_finiteFormCombo_clockHalf_eval
#print axioms evolved_finiteFormCombo_staticRoot_norm_le
#print axioms evolved_finiteFormCombo_radialRoot_norm_le
#print axioms evolved_finiteFormCombo_potentialForm_norm_le
#print axioms evolved_finiteFormCombo_growingForm_norm_le
#print axioms evolved_finiteFormCombo_residualForm_norm_le
#print axioms evolved_finiteFormCombo_clockHalf_norm_le_staticRoot
#print axioms evolved_finiteFormCombo_instantFormEnergy_le_max_initial
end
end UnifiedTheory.Audit.KFCausalFiniteThreeOperatorEvolvedDomination
