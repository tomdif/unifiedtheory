/- Positive-vacuum and unconditional Gaussian smoothing, clock-domain
regularization, and simultaneous multi-operator graph approximation on the
time-dependent Hamiltonian and residual operator domains. -/
import UnifiedTheory.Audit.KFCausalClockFloorGaussianClockCommutation
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumHamiltonianGaussianCore

noncomputable section

open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorClockOperator (clockOperator)
open KFCausalClockFloorGaussianGrowingTransport (action)
open KFCausalClockFloorGaussianGrowingApproximation (sequence_tendsto)
open KFCausalClockFloorGaussianMultiOperatorApproximation
  (component_graphs growing_sum_graph)
open KFCausalClockFloorGaussianUnconditionalMultiOperatorApproximation
  (unconditional_graphs unconditional_sequence_multi_operator_approximation
    residual_form_domain_action averaged_form_domain_action)
open KFCausalClockFloorGaussianClockCommutation
  (gaussian_clockHalf_graph gaussian_clockHalf_domain gaussian_clockHalf_commute
    gaussian_clockHalf_sequence_tendsto
    gaussian_clockOperator_graph gaussian_clockOperator_domain gaussian_clockOperator_commute
    gaussian_clockOperator_sequence_tendsto
    gaussian_mem_clockOperator_domain_of_pos gaussian_mem_clockHalf_domain_of_pos
    unconditionalDomain unconditional_clock_domain_action
    unconditional_clock_sequence_multi_operator_approximation)
open KFCausalClockFloorUnconditionalThreeOperatorDecomposition
  (residual_growing_common_domain_eq hamiltonian_residual_common_domain_eq
    hamiltonian_growing_common_domain_eq hamiltonian_static_common_domain_eq)
open KFCausalClockFloorUnconditionalTwoTimeEvolution (commonOperatorDomain)
open KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3)
  (m g k : ℝ)

local notation "hw" => KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hw) hh m g k

/-- The smooth positive-vacuum three-operator clock core: vectors in
`Dom(T) ∩ Dom(K) ∩ Dom(P)` that also lie in `Dom(clockOperator ε)` and `Dom(clockHalf ε)`. -/
def positiveVacuumClockCore : Submodule ℂ Hilbert :=
  ((T).domain ⊓ (K).domain ⊓ (P).domain) ⊓
    (clockOperator ε hε).domain ⊓ (clockHalf ε).domain

/-- The smooth unconditional common clock core: vectors in `commonOperatorDomain`
that also lie in `Dom(clockOperator ε)` and `Dom(clockHalf ε)`. -/
def unconditionalClockCore : Submodule ℂ Hilbert :=
  commonOperatorDomain ε hε h hh hb m g k ⊓
    (clockOperator ε hε).domain ⊓ (clockHalf ε).domain

/-- `unconditionalDomain` in `KFCausalClockFloorGaussianClockCommutation` is identical to
`commonOperatorDomain` in `KFCausalClockFloorUnconditionalTwoTimeEvolution`. -/
theorem unconditionalDomain_eq_commonOperatorDomain :
    unconditionalDomain ε hε h hh hb m g k =
      commonOperatorDomain ε hε h hh hb m g k := rfl

/-- Because `commonOperatorDomain ≤ (clockHalf ε).domain`, the `(clockHalf ε).domain`
factor in `unconditionalClockCore` is redundant. -/
theorem unconditionalClockCore_eq_inf_clockOperator :
    unconditionalClockCore ε hε h hh hb m g k =
      commonOperatorDomain ε hε h hh hb m g k ⊓ (clockOperator ε hε).domain := by
  unfold unconditionalClockCore
  have hle :
      commonOperatorDomain ε hε h hh hb m g k ⊓ (clockOperator ε hε).domain ≤
        (clockHalf ε).domain :=
    inf_le_left.trans (commonOperatorDomain_le_clockHalf_domain ε hε h hh hb m g k)
  exact inf_of_le_left hle

/-- Because `(T).domain ⊓ (K).domain ⊓ (P).domain ≤ (clockHalf ε).domain`, the
`(clockHalf ε).domain` factor in `positiveVacuumClockCore` is redundant. -/
theorem positiveVacuumClockCore_eq_inf_clockOperator :
    positiveVacuumClockCore ε hε h hh hb m g k =
      ((T).domain ⊓ (K).domain ⊓ (P).domain) ⊓ (clockOperator ε hε).domain := by
  unfold positiveVacuumClockCore
  have hle :
      ((T).domain ⊓ (K).domain ⊓ (P).domain) ⊓ (clockOperator ε hε).domain ≤
        (clockHalf ε).domain :=
    inf_le_left.trans (three_operator_domain_le_clockHalf_domain ε hε h hh hb m g k)
  exact inf_of_le_left hle

/-- Under positive vacuum `0 < k`, `positiveVacuumClockCore` coincides with
`unconditionalClockCore`. -/
theorem positive_vacuum_clock_core_eq_unconditional
    (hk : 0 < k) :
    positiveVacuumClockCore ε hε h hh hb m g k =
      unconditionalClockCore ε hε h hh hb m g k := by
  unfold positiveVacuumClockCore unconditionalClockCore
  rw [positive_vacuum_common_domain_eq_three_operator ε hε h hh hb m g k hk]

/-- Unconditionally for all real couplings `m, g, k`, the intersections of `(H t).domain`
with `(P).domain`, `(T).domain`, and `(G).domain`, and of `(S t).domain` with `(G).domain`,
all equal `commonOperatorDomain` once intersected with `(clockOperator ε hε).domain ⊓ (clockHalf ε).domain`. -/
theorem unconditional_two_operator_clock_core_eq (t : ℝ) :
    ((H t).domain ⊓ (P).domain) ⊓ (clockOperator ε hε).domain ⊓ (clockHalf ε).domain =
      unconditionalClockCore ε hε h hh hb m g k ∧
    ((H t).domain ⊓ (T).domain) ⊓ (clockOperator ε hε).domain ⊓ (clockHalf ε).domain =
      unconditionalClockCore ε hε h hh hb m g k ∧
    ((H t).domain ⊓ (G).domain) ⊓ (clockOperator ε hε).domain ⊓ (clockHalf ε).domain =
      unconditionalClockCore ε hε h hh hb m g k ∧
    ((S t).domain ⊓ (G).domain) ⊓ (clockOperator ε hε).domain ⊓ (clockHalf ε).domain =
      unconditionalClockCore ε hε h hh hb m g k := by
  unfold unconditionalClockCore commonOperatorDomain
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hamiltonian_residual_common_domain_eq ε hε h hh hb m g k t]
  · rw [hamiltonian_static_common_domain_eq ε hε h hh hb m g k t]
  · rw [hamiltonian_growing_common_domain_eq ε hε h hh hb m g k t]
  · rw [residual_growing_common_domain_eq ε hε h hh hb m g k t]

/-- Any vector in `unconditionalClockCore` lies simultaneously in `(H t).domain`,
`(S t).domain`, `(T).domain`, `(K).domain`, `(P).domain`, `(G).domain`, `(Eavg t).domain`,
`(Tres t).domain`, `(clockOperator ε hε).domain`, and `(clockHalf ε).domain` at every time `t : ℝ`. -/
theorem unconditional_clock_core_mem_all_domains
    (t : ℝ) {x : Hilbert}
    (hx : x ∈ unconditionalClockCore ε hε h hh hb m g k) :
    x ∈ (H t).domain ∧ x ∈ (S t).domain ∧
      x ∈ (T).domain ∧ x ∈ (K).domain ∧ x ∈ (P).domain ∧ x ∈ (G).domain ∧
      x ∈ (Eavg t).domain ∧ x ∈ (Tres t).domain ∧
      x ∈ (clockOperator ε hε).domain ∧ x ∈ (clockHalf ε).domain := by
  rcases hx with ⟨⟨hxC, hxClock⟩, hxHalf⟩
  have hxH : x ∈ (H t).domain :=
    KFCausalClockFloorUnconditionalTwoTimeEvolution.common_domain_subset_hamiltonian
      ε hε h hh hb m g k t hxC
  have hxS : x ∈ (S t).domain :=
    KFCausalClockFloorUnconditionalTwoTimeEvolution.common_domain_subset_residual
      ε hε h hh hb m g k t hxC
  have hxG : x ∈ (G).domain :=
    KFCausalClockFloorUnconditionalTwoTimeEvolution.common_domain_subset_growing
      ε hε h hh hb m g k hxC
  have hxE : x ∈ (Eavg t).domain :=
    KFCausalClockFloorUnconditionalOperatorFormEnergy.hamiltonian_mem_averaged_domain
      ε hε h hh hb m g k t ⟨x, hxH⟩
  have hxR : x ∈ (Tres t).domain :=
    (residual_form_domain_time_iff ε hε h hh hb m g k 0 t x).mp hxC.2
  exact ⟨hxH, hxS, hxC.1.1.1, hxC.1.1.2, hxC.1.2, hxG, hxE, hxR, hxClock, hxHalf⟩

/-- Under positive vacuum `0 < k`, any vector in `positiveVacuumClockCore` lies in
all ten operator and form domains at every time `t : ℝ`. -/
theorem positive_vacuum_clock_core_mem_all_domains
    (hk : 0 < k) (t : ℝ) {x : Hilbert}
    (hx : x ∈ positiveVacuumClockCore ε hε h hh hb m g k) :
    x ∈ (H t).domain ∧ x ∈ (S t).domain ∧
      x ∈ (T).domain ∧ x ∈ (K).domain ∧ x ∈ (P).domain ∧ x ∈ (G).domain ∧
      x ∈ (Eavg t).domain ∧ x ∈ (Tres t).domain ∧
      x ∈ (clockOperator ε hε).domain ∧ x ∈ (clockHalf ε).domain := by
  rw [positive_vacuum_clock_core_eq_unconditional ε hε h hh hb m g k hk] at hx
  exact unconditional_clock_core_mem_all_domains ε hε h hh hb m g k t hx

/-- Unconditionally for all real couplings `m, g, k`, Gaussian smoothing at strictly positive
width `a > 0` maps any vector in `commonOperatorDomain` into `unconditionalClockCore`, and
provides simultaneous graph memberships for `clockHalf ε`, `T`, `K`, `P`, `G`, `S s`, and `H s`
at every target time `s : ℝ`. -/
theorem unconditional_gaussian_mem_clock_core_of_pos
    (s a : ℝ) (ha : 0 < a) {f : Hilbert}
    (hf : f ∈ commonOperatorDomain ε hε h hh hb m g k) :
    action ε a ha.le 0 f ∈ unconditionalClockCore ε hε h hh hb m g k ∧
    (action ε a ha.le 0 f,
      action ε a ha.le 0
        (clockHalf ε ⟨f, commonOperatorDomain_le_clockHalf_domain ε hε h hh hb m g k hf⟩)) ∈
      (clockHalf ε).graph ∧
    (action ε a ha.le 0 f, action ε a ha.le 0 (T ⟨f, hf.1.1.1⟩)) ∈ (T).graph ∧
    (action ε a ha.le 0 f, action ε a ha.le 0 (K ⟨f, hf.1.1.2⟩)) ∈ (K).graph ∧
    (action ε a ha.le 0 f, action ε a ha.le (-h) (P ⟨f, hf.1.2⟩)) ∈ (P).graph ∧
    (action ε a ha.le 0 f,
      action ε a ha.le 0 (K ⟨f, hf.1.1.2⟩) + action ε a ha.le (-h) (P ⟨f, hf.1.2⟩)) ∈
      (G).graph ∧
    (action ε a ha.le 0 f,
      action ε a ha.le 0 (T ⟨f, hf.1.1.1⟩) +
        (Real.exp (2 * s) : ℂ) • action ε a ha.le (-h) (P ⟨f, hf.1.2⟩)) ∈ (S s).graph ∧
    (action ε a ha.le 0 f,
      action ε a ha.le 0 (T ⟨f, hf.1.1.1⟩) +
        (Real.exp (2 * s) : ℂ) •
          (action ε a ha.le 0 (K ⟨f, hf.1.1.2⟩) + action ε a ha.le (-h) (P ⟨f, hf.1.2⟩))) ∈
      (H s).graph := by
  have hc_mem : f ∈ (clockHalf ε).domain :=
    commonOperatorDomain_le_clockHalf_domain ε hε h hh hb m g k hf
  have hact :=
    unconditional_clock_domain_action ε hε h hh hb m g k a ha.le f hf hc_mem
  have hclockOp : action ε a ha.le 0 f ∈ (clockOperator ε hε).domain :=
    gaussian_mem_clockOperator_domain_of_pos ε hε a ha 0 f
  have hcore : action ε a ha.le 0 f ∈ unconditionalClockCore ε hε h hh hb m g k :=
    ⟨⟨hact.1, hclockOp⟩, hact.2⟩
  have ht : (f, T ⟨f, hf.1.1.1⟩) ∈ (T).graph := (T).mem_graph ⟨f, hf.1.1.1⟩
  have hr : (f, K ⟨f, hf.1.1.2⟩) ∈ (K).graph := (K).mem_graph ⟨f, hf.1.1.2⟩
  have hp : (f, P ⟨f, hf.1.2⟩) ∈ (P).graph := (P).mem_graph ⟨f, hf.1.2⟩
  have hc : (f, clockHalf ε ⟨f, hc_mem⟩) ∈ (clockHalf ε).graph :=
    (clockHalf ε).mem_graph ⟨f, hc_mem⟩
  have hcomp :=
    component_graphs ε hε h hh hb m g k a ha.le f
      (T ⟨f, hf.1.1.1⟩) (K ⟨f, hf.1.1.2⟩) (P ⟨f, hf.1.2⟩) ht hr hp
  have hg :=
    growing_sum_graph ε hε h hh hb m g k a ha.le f
      (K ⟨f, hf.1.1.2⟩) (P ⟨f, hf.1.2⟩) hr hp
  have hSH :=
    unconditional_graphs ε hε a ha.le h hh m g k hb s f
      (T ⟨f, hf.1.1.1⟩) (K ⟨f, hf.1.1.2⟩) (P ⟨f, hf.1.2⟩) ht hr hp hf.2
  have hc' := gaussian_clockHalf_graph ε hε a ha.le 0 f (clockHalf ε ⟨f, hc_mem⟩) hc
  exact ⟨hcore, hc', hcomp.1, hcomp.2.1, hcomp.2.2, hg, hSH.1, hSH.2⟩

/-- Under positive vacuum `0 < k`, Gaussian smoothing at strictly positive width `a > 0`
maps any vector in `(T).domain ⊓ (K).domain ⊓ (P).domain` into `positiveVacuumClockCore`,
with simultaneous graph memberships in `clockHalf ε`, `T`, `K`, `P`, `G`, `S s`, and `H s`
at every time `s : ℝ`. -/
theorem positive_vacuum_gaussian_mem_clock_core_of_pos
    (hk : 0 < k) (s a : ℝ) (ha : 0 < a) {f : Hilbert}
    (hf : f ∈ (T).domain ⊓ (K).domain ⊓ (P).domain) :
    action ε a ha.le 0 f ∈ positiveVacuumClockCore ε hε h hh hb m g k ∧
    (action ε a ha.le 0 f,
      action ε a ha.le 0
        (clockHalf ε ⟨f, three_operator_domain_le_clockHalf_domain ε hε h hh hb m g k hf⟩)) ∈
      (clockHalf ε).graph ∧
    (action ε a ha.le 0 f, action ε a ha.le 0 (T ⟨f, hf.1.1⟩)) ∈ (T).graph ∧
    (action ε a ha.le 0 f, action ε a ha.le 0 (K ⟨f, hf.1.2⟩)) ∈ (K).graph ∧
    (action ε a ha.le 0 f, action ε a ha.le (-h) (P ⟨f, hf.2⟩)) ∈ (P).graph ∧
    (action ε a ha.le 0 f,
      action ε a ha.le 0 (K ⟨f, hf.1.2⟩) + action ε a ha.le (-h) (P ⟨f, hf.2⟩)) ∈
      (G).graph ∧
    (action ε a ha.le 0 f,
      action ε a ha.le 0 (T ⟨f, hf.1.1⟩) +
        (Real.exp (2 * s) : ℂ) • action ε a ha.le (-h) (P ⟨f, hf.2⟩)) ∈ (S s).graph ∧
    (action ε a ha.le 0 f,
      action ε a ha.le 0 (T ⟨f, hf.1.1⟩) +
        (Real.exp (2 * s) : ℂ) •
          (action ε a ha.le 0 (K ⟨f, hf.1.2⟩) + action ε a ha.le (-h) (P ⟨f, hf.2⟩))) ∈
      (H s).graph := by
  have hfC : f ∈ commonOperatorDomain ε hε h hh hb m g k := by
    rwa [positive_vacuum_common_domain_eq_three_operator ε hε h hh hb m g k hk]
  rw [positive_vacuum_clock_core_eq_unconditional ε hε h hh hb m g k hk]
  exact unconditional_gaussian_mem_clock_core_of_pos ε hε h hh hb m g k s a ha hfC

/-- Under positive vacuum `0 < k`, Gaussian smoothing at width `a > 0` maps any vector in
`(H t).domain ⊓ (G).domain`, `(H t).domain ⊓ (T).domain`, `(H t).domain ⊓ (P).domain`,
or `(S t).domain ⊓ (G).domain` into `positiveVacuumClockCore`. -/
theorem positive_vacuum_two_operator_gaussian_mem_clock_core
    (hk : 0 < k) (t a : ℝ) (ha : 0 < a) {f : Hilbert} :
    (f ∈ (H t).domain ⊓ (G).domain →
      action ε a ha.le 0 f ∈ positiveVacuumClockCore ε hε h hh hb m g k) ∧
    (f ∈ (H t).domain ⊓ (T).domain →
      action ε a ha.le 0 f ∈ positiveVacuumClockCore ε hε h hh hb m g k) ∧
    (f ∈ (H t).domain ⊓ (P).domain →
      action ε a ha.le 0 f ∈ positiveVacuumClockCore ε hε h hh hb m g k) ∧
    (f ∈ (S t).domain ⊓ (G).domain →
      action ε a ha.le 0 f ∈ positiveVacuumClockCore ε hε h hh hb m g k) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hf
    rw [positive_vacuum_hamiltonian_inter_growing_domain_eq ε hε h hh hb m g k hk t] at hf
    exact (positive_vacuum_gaussian_mem_clock_core_of_pos ε hε h hh hb m g k hk t a ha hf).1
  · intro hf
    rw [positive_vacuum_hamiltonian_inter_static_domain_eq ε hε h hh hb m g k hk t] at hf
    exact (positive_vacuum_gaussian_mem_clock_core_of_pos ε hε h hh hb m g k hk t a ha hf).1
  · intro hf
    rw [positive_vacuum_hamiltonian_inter_potential_domain_eq ε hε h hh hb m g k hk t] at hf
    exact (positive_vacuum_gaussian_mem_clock_core_of_pos ε hε h hh hb m g k hk t a ha hf).1
  · intro hf
    rw [positive_vacuum_residual_inter_growing_domain_eq ε hε h hh hb m g k hk t] at hf
    exact (positive_vacuum_gaussian_mem_clock_core_of_pos ε hε h hh hb m g k hk t a ha hf).1

/-- Under positive vacuum `0 < k`, for every `f ∈ (T).domain ⊓ (K).domain ⊓ (P).domain` and
every pair of times `(s, t)`, the canonical centered Gaussian sequence
`f_n := action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f` lies in `positiveVacuumClockCore`
for all `n : ℕ` and converges simultaneously in `(clockHalf ε).graph`, `(T).graph`,
`(K).graph`, `(P).graph`, `(G).graph`, `(S s).graph`, `(S t).graph`, `(H s).graph`,
and `(H t).graph`. -/
theorem positive_vacuum_two_time_clock_core_sequence_approximation
    (hk : 0 < k) (s t : ℝ) {f : Hilbert}
    (hf : f ∈ (T).domain ⊓ (K).domain ⊓ (P).domain) :
    let c := clockHalf ε ⟨f, three_operator_domain_le_clockHalf_domain ε hε h hh hb m g k hf⟩
    let y := T ⟨f, hf.1.1⟩
    let r := K ⟨f, hf.1.2⟩
    let z := P ⟨f, hf.2⟩
    (∀ n : ℕ,
      action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f ∈
        positiveVacuumClockCore ε hε h hh hb m g k ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 c) ∈ (clockHalf ε).graph ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y) ∈ (T).graph ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r) ∈ (K).graph ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z) ∈ (P).graph ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r +
          action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z) ∈ (G).graph ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y +
          (Real.exp (2 * s) : ℂ) • action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z) ∈
        (S s).graph ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y +
          (Real.exp (2 * t) : ℂ) • action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z) ∈
        (S t).graph ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y +
          (Real.exp (2 * s) : ℂ) •
            (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r +
              action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z)) ∈ (H s).graph ∧
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y +
          (Real.exp (2 * t) : ℂ) •
            (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r +
              action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z)) ∈ (H t).graph) ∧
    Tendsto (fun n : ℕ =>
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 c,
          (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y,
            (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r,
              (action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z,
                (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r +
                  action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z,
                  (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y +
                    (Real.exp (2 * s) : ℂ) • action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z,
                    action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y +
                      (Real.exp (2 * s) : ℂ) •
                        (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r +
                          action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z))))))))) atTop
      (𝓝 (f, (c, (y, (r, (z, (r + z, (y + (Real.exp (2 * s) : ℂ) • z,
        y + (Real.exp (2 * s) : ℂ) • (r + z))))))))) ∧
    Tendsto (fun n : ℕ =>
      (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
        (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 c,
          (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y,
            (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r,
              (action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z,
                (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r +
                  action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z,
                  (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y +
                    (Real.exp (2 * t) : ℂ) • action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z,
                    action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y +
                      (Real.exp (2 * t) : ℂ) •
                        (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 r +
                          action ε (((n : ℝ) + 1)⁻¹) (by positivity) (-h) z))))))))) atTop
      (𝓝 (f, (c, (y, (r, (z, (r + z, (y + (Real.exp (2 * t) : ℂ) • z,
        y + (Real.exp (2 * t) : ℂ) • (r + z))))))))) := by
  intro c y r z
  have hfC : f ∈ commonOperatorDomain ε hε h hh hb m g k := by
    rwa [positive_vacuum_common_domain_eq_three_operator ε hε h hh hb m g k hk]
  have hc : (f, c) ∈ (clockHalf ε).graph :=
    (clockHalf ε).mem_graph ⟨f, three_operator_domain_le_clockHalf_domain ε hε h hh hb m g k hf⟩
  have ht : (f, y) ∈ (T).graph := (T).mem_graph ⟨f, hf.1.1⟩
  have hr : (f, r) ∈ (K).graph := (K).mem_graph ⟨f, hf.1.2⟩
  have hp : (f, z) ∈ (P).graph := (P).mem_graph ⟨f, hf.2⟩
  have hs_app :=
    unconditional_clock_sequence_multi_operator_approximation
      ε hε h hh hb m g k s f c y r z hc ht hr hp hfC.2
  have ht_app :=
    unconditional_clock_sequence_multi_operator_approximation
      ε hε h hh hb m g k t f c y r z hc ht hr hp hfC.2
  refine ⟨fun n => ?_, hs_app.2, ht_app.2⟩
  have hpos : 0 < (((n : ℝ) + 1)⁻¹) := by positivity
  have hcore :=
    (positive_vacuum_gaussian_mem_clock_core_of_pos ε hε h hh hb m g k hk s
      (((n : ℝ) + 1)⁻¹) hpos hf).1
  have hgs := hs_app.1 n
  have hgt := ht_app.1 n
  exact ⟨hcore, hgs.1, hgs.2.1, hgs.2.2.1, hgs.2.2.2.1, hgs.2.2.2.2.1,
    hgs.2.2.2.2.2.1, hgt.2.2.2.2.2.1, hgs.2.2.2.2.2.2, hgt.2.2.2.2.2.2⟩

/-- The static operator graph restricted to `unconditionalClockCore` is dense in `(T).graph`. -/
theorem unconditional_clock_core_static_graph_core :
    ((T).graph ⊓ (unconditionalClockCore ε hε h hh hb m g k).comap
      (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure = (T).graph := by
  let K₁ :=
    (T).graph ⊓ (unconditionalClockCore ε hε h hh hb m g k).comap
      (LinearMap.fst ℂ Hilbert Hilbert)
  let K₀ :=
    KFCausalClockFloorStaticThreeOperatorCore.commonOperatorStaticGraph ε hε h hh hb m g k
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ inf_le_left
      (KFCausalRealMultiplierSelfAdjoint.realPullback_selfAdjoint
        KFCausalChargeTransverseSplit.dualPhysical
        (KFCausalClockFloorStaticMultiplierForm.symbol ε h)
        (KFCausalClockFloorStaticMultiplierForm.symbol_continuous ε hε h).measurable).isClosed
  · have hle : K₀ ≤ K₁.topologicalClosure := by
      rintro ⟨f, y⟩ ⟨hfy, hfC⟩
      change f ∈ commonOperatorDomain ε hε h hh hb m g k at hfC
      have hseq :
          ∀ n : ℕ,
            (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
              action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y) ∈ K₁ := by
        intro n
        have hpos : 0 < (((n : ℝ) + 1)⁻¹) := by positivity
        have hcore :=
          (unconditional_gaussian_mem_clock_core_of_pos ε hε h hh hb m g k 0
            (((n : ℝ) + 1)⁻¹) hpos hfC).1
        have hr : (f, K ⟨f, hfC.1.1.2⟩) ∈ (K).graph := (K).mem_graph ⟨f, hfC.1.1.2⟩
        have hp : (f, P ⟨f, hfC.1.2⟩) ∈ (P).graph := (P).mem_graph ⟨f, hfC.1.2⟩
        have hT :=
          (component_graphs ε hε h hh hb m g k (((n : ℝ) + 1)⁻¹) (by positivity)
            f y (K ⟨f, hfC.1.1.2⟩) (P ⟨f, hfC.1.2⟩) hfy hr hp).1
        exact ⟨hT, hcore⟩
      have hlim :
          Tendsto (fun n : ℕ =>
            (action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 f,
              action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 y))
            atTop (𝓝 (f, y)) :=
        (sequence_tendsto ε 0 f).prodMk_nhds (sequence_tendsto ε 0 y)
      exact mem_closure_iff_seq_limit.mpr ⟨_, hseq, hlim⟩
    have hcl := Submodule.topologicalClosure_minimal _ hle K₁.isClosed_topologicalClosure
    rwa [KFCausalClockFloorStaticThreeOperatorCore.common_operator_static_graph_core
      ε hε h hh hb m g k] at hcl

/-- Under positive vacuum `0 < k`, the static operator graph restricted to
`positiveVacuumClockCore` is an operator graph core for `T`. -/
theorem positive_vacuum_clock_core_static_graph_core (hk : 0 < k) :
    ((T).graph ⊓ (positiveVacuumClockCore ε hε h hh hb m g k).comap
      (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure = (T).graph := by
  rw [positive_vacuum_clock_core_eq_unconditional ε hε h hh hb m g k hk]
  exact unconditional_clock_core_static_graph_core ε hε h hh hb m g k

#print axioms unconditionalDomain_eq_commonOperatorDomain
#print axioms unconditionalClockCore_eq_inf_clockOperator
#print axioms positiveVacuumClockCore_eq_inf_clockOperator
#print axioms positive_vacuum_clock_core_eq_unconditional
#print axioms unconditional_two_operator_clock_core_eq
#print axioms unconditional_clock_core_mem_all_domains
#print axioms positive_vacuum_clock_core_mem_all_domains
#print axioms unconditional_gaussian_mem_clock_core_of_pos
#print axioms positive_vacuum_gaussian_mem_clock_core_of_pos
#print axioms positive_vacuum_two_operator_gaussian_mem_clock_core
#print axioms positive_vacuum_two_time_clock_core_sequence_approximation
#print axioms unconditional_clock_core_static_graph_core
#print axioms positive_vacuum_clock_core_static_graph_core

end

end UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumHamiltonianGaussianCore
