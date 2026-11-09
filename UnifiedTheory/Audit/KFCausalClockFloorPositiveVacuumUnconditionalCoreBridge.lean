/- Positive-Vacuum Unconditional 5-Operator Core Bridge:
bridges the positive-vacuum and unconditional Gaussian clock cores
(`positiveVacuumClockCore`, `unconditionalClockCore`) and the growing-potential
Gaussian clock core (`growingClockCore`) with the five-operator second
resolvent identities and two-time resolvent continuity. Under `0 < k`,
`positiveVacuumClockCore = unconditionalClockCore`, and both equal the
intersections `(T).domain ⊓ growingClockCore`, `(H t).domain ⊓ growingClockCore`,
and `(S t).domain ⊓ growingClockCore`; every vector in the core belongs
simultaneously to all ten operator, form, and clock domains across all real
times and satisfies all five-operator resolvent defect identities and norm
bounds; and every vector in `Dom(T) ∩ Dom(K) ∩ Dom(P)` possesses an explicit
centered clock-Gaussian sequence in the core converging simultaneously across
all nine operator and clock graphs while satisfying the exact three-operator
and five-operator resolvent identities at every term. -/
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumResolventRegularity
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumHamiltonianGaussianCore
import UnifiedTheory.Audit.KFCausalClockFloorGrowingPotentialGaussianClockCore

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumUnconditionalCoreBridge
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockOperator (clockOperator)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorGaussianGrowingTransport (action)
open KFCausalClockFloorGaussianGrowingApproximation (sequence_tendsto)
open KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain
  (positive_vacuum_common_domain_eq_three_operator
   positive_vacuum_hamiltonian_inter_growing_domain_eq
   positive_vacuum_residual_inter_growing_domain_eq
   positive_vacuum_static_inter_growing_domain_eq
   positive_vacuum_three_operator_hamiltonian_eval
   positive_vacuum_three_operator_residual_eval
   three_operator_domain_le_clockHalf_domain)
open KFCausalClockFloorPositiveVacuumHamiltonianGaussianCore
  (positiveVacuumClockCore unconditionalClockCore
   unconditionalClockCore_eq_inf_clockOperator
   positiveVacuumClockCore_eq_inf_clockOperator
   positive_vacuum_clock_core_eq_unconditional
   unconditional_two_operator_clock_core_eq
   unconditional_clock_core_mem_all_domains
   positive_vacuum_clock_core_mem_all_domains
   unconditional_gaussian_mem_clock_core_of_pos
   positive_vacuum_gaussian_mem_clock_core_of_pos
   positive_vacuum_two_operator_gaussian_mem_clock_core
   positive_vacuum_two_time_clock_core_sequence_approximation
   unconditional_clock_core_static_graph_core
   positive_vacuum_clock_core_static_graph_core)
open KFCausalClockFloorGrowingPotentialGaussianClockCore
  (growingClockCore
   growing_domain_eq_radial_inf_potential
   growingClockCore_eq_radial_inf_potential_clock
   unconditionalClockCore_le_growingClockCore
   positiveVacuumClockCore_le_growingClockCore
   growingClockCore_mem_all_domains
   growing_apply_eq_radial_add_potential
   gaussian_mem_growingClockCore_of_pos
   growing_clock_core_sequence_approximation
   growing_clock_core_graph_core
   potential_growing_clock_core_graph_core
   growing_and_potential_simultaneous_clock_core
   growingClockCore_dense)
open KFCausalClockFloorPositiveVacuumResolventRegularity
  (threeOperatorDomain
   positive_vacuum_three_operator_left_inverse_cancel
   positive_vacuum_residual_two_operator_left_inverse_cancel
   positive_vacuum_hamiltonian_static_shifted_resolvent_defect
   positive_vacuum_residual_static_shifted_resolvent_defect
   positive_vacuum_hamiltonian_residual_shifted_resolvent_defect
   positive_vacuum_hamiltonian_static_shifted_resolvent_defect_norm_le
   positive_vacuum_residual_static_shifted_resolvent_defect_norm_le
   positive_vacuum_hamiltonian_residual_shifted_resolvent_defect_norm_le
   positive_vacuum_two_time_shifted_resolvent_package
   positive_vacuum_two_time_residual_shifted_resolvent_package
   unconditional_potential_growing_second_resolvent_package
   unconditional_residual_hamiltonian_second_resolvent_package)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k
local notation "RG" => KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw m g k
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hw) hh m g k

/-- Alias for the unconditional clock core `unconditionalClockCore`. -/
def unconditionalCoreDomain : Submodule ℂ Hilbert :=
  unconditionalClockCore ε hε h hh hb m g k

/-- Alias for the positive-vacuum clock core `positiveVacuumClockCore`. -/
def positiveVacuumCoreDomain : Submodule ℂ Hilbert :=
  positiveVacuumClockCore ε hε h hh hb m g k

/-- Alias for the growing-potential clock core `growingClockCore`. -/
def growingClockCoreDomain : Submodule ℂ Hilbert :=
  growingClockCore ε hε h hh hb m g k

/-- The canonical centered clock-Gaussian approximation sequence at width
`((n : ℝ) + 1)⁻¹`. -/
def coreApproxSeq (x : Hilbert) (n : ℕ) : Hilbert :=
  action ε (((n : ℝ) + 1)⁻¹) (by positivity) 0 x

/-- 1. Under `0 < k`, `positiveVacuumCoreDomain` equals `unconditionalCoreDomain`. -/
theorem positiveVacuumCoreDomain_eq_unconditionalCoreDomain (hk : 0 < k) :
    positiveVacuumCoreDomain ε hε h hh hb m g k =
      unconditionalCoreDomain ε hε h hh hb m g k :=
  positive_vacuum_clock_core_eq_unconditional ε hε h hh hb m g k hk

/-- 2. The positive-vacuum clock core equals the intersection of `Dom(T)` with
`growingClockCoreDomain`. -/
theorem positiveVacuumCoreDomain_eq_static_inf_growingClockCoreDomain :
    positiveVacuumCoreDomain ε hε h hh hb m g k =
      (T).domain ⊓ growingClockCoreDomain ε hε h hh hb m g k := by
  ext x
  simp only [positiveVacuumCoreDomain, positiveVacuumClockCore,
    growingClockCoreDomain, growingClockCore, Submodule.mem_inf]
  have hTG := Set.ext_iff.mp (congrArg SetLike.coe
    (positive_vacuum_static_inter_growing_domain_eq ε hε h hh hb m g k)) x
  change (x ∈ (T).domain ∧ x ∈ (G).domain) ↔
    ((x ∈ (T).domain ∧ x ∈ (K).domain) ∧ x ∈ (P).domain) at hTG
  tauto

/-- 3. Under `0 < k`, `unconditionalCoreDomain` equals the intersection of
`Dom(T)` with `growingClockCoreDomain`. -/
theorem unconditionalCoreDomain_eq_static_inf_growingClockCoreDomain (hk : 0 < k) :
    unconditionalCoreDomain ε hε h hh hb m g k =
      (T).domain ⊓ growingClockCoreDomain ε hε h hh hb m g k := by
  rw [← positiveVacuumCoreDomain_eq_unconditionalCoreDomain ε hε h hh hb m g k hk,
    positiveVacuumCoreDomain_eq_static_inf_growingClockCoreDomain ε hε h hh hb m g k]

/-- 4. Under `0 < k`, for every time `t : ℝ`, `unconditionalCoreDomain` equals
the intersection of `Dom(H(t))` with `growingClockCoreDomain`. -/
theorem unconditionalCoreDomain_eq_hamiltonian_inf_growingClockCoreDomain
    (hk : 0 < k) (t : ℝ) :
    unconditionalCoreDomain ε hε h hh hb m g k =
      (H t).domain ⊓ growingClockCoreDomain ε hε h hh hb m g k := by
  rw [← positiveVacuumCoreDomain_eq_unconditionalCoreDomain ε hε h hh hb m g k hk]
  ext x
  simp only [positiveVacuumCoreDomain, positiveVacuumClockCore,
    growingClockCoreDomain, growingClockCore, Submodule.mem_inf]
  have hHG := Set.ext_iff.mp (congrArg SetLike.coe
    (positive_vacuum_hamiltonian_inter_growing_domain_eq ε hε h hh hb m g k hk t)) x
  change (x ∈ (H t).domain ∧ x ∈ (G).domain) ↔
    ((x ∈ (T).domain ∧ x ∈ (K).domain) ∧ x ∈ (P).domain) at hHG
  tauto

/-- 5. Under `0 < k`, for every time `t : ℝ`, `unconditionalCoreDomain` equals
the intersection of `Dom(S(t))` with `growingClockCoreDomain`. -/
theorem unconditionalCoreDomain_eq_residual_inf_growingClockCoreDomain
    (hk : 0 < k) (t : ℝ) :
    unconditionalCoreDomain ε hε h hh hb m g k =
      (S t).domain ⊓ growingClockCoreDomain ε hε h hh hb m g k := by
  rw [← positiveVacuumCoreDomain_eq_unconditionalCoreDomain ε hε h hh hb m g k hk]
  ext x
  simp only [positiveVacuumCoreDomain, positiveVacuumClockCore,
    growingClockCoreDomain, growingClockCore, Submodule.mem_inf]
  have hSG := Set.ext_iff.mp (congrArg SetLike.coe
    (positive_vacuum_residual_inter_growing_domain_eq ε hε h hh hb m g k hk t)) x
  change (x ∈ (S t).domain ∧ x ∈ (G).domain) ↔
    ((x ∈ (T).domain ∧ x ∈ (K).domain) ∧ x ∈ (P).domain) at hSG
  tauto

/-- 6. Both `unconditionalCoreDomain` and `positiveVacuumCoreDomain` are
submodules of `growingClockCoreDomain`. -/
theorem coreDomains_le_growingClockCoreDomain :
    unconditionalCoreDomain ε hε h hh hb m g k ≤
        growingClockCoreDomain ε hε h hh hb m g k ∧
      positiveVacuumCoreDomain ε hε h hh hb m g k ≤
        growingClockCoreDomain ε hε h hh hb m g k :=
  ⟨unconditionalClockCore_le_growingClockCore ε hε h hh hb m g k,
   positiveVacuumClockCore_le_growingClockCore ε hε h hh hb m g k⟩

/-- 7. Under `0 < k`, every vector in `positiveVacuumCoreDomain` belongs
simultaneously to all ten operator, form, and clock domains `Dom(H(t))`,
`Dom(S(t))`, `Dom(T)`, `Dom(K)`, `Dom(P)`, `Dom(G)`, `Dom(Eavg(t))`,
`Dom(Tres(t))`, `Dom(clockOperator ε hε)`, and `Dom(clockHalf ε)` for all `t : ℝ`. -/
theorem positiveVacuumCoreDomain_mem_all_ten_domains
    (hk : 0 < k) (t : ℝ) (x : Hilbert)
    (hx : x ∈ positiveVacuumCoreDomain ε hε h hh hb m g k) :
    x ∈ (H t).domain ∧ x ∈ (S t).domain ∧
      x ∈ (T).domain ∧ x ∈ (K).domain ∧ x ∈ (P).domain ∧ x ∈ (G).domain ∧
      x ∈ (Eavg t).domain ∧ x ∈ (Tres t).domain ∧
      x ∈ (clockOperator ε hε).domain ∧ x ∈ (clockHalf ε).domain :=
  positive_vacuum_clock_core_mem_all_domains ε hε h hh hb m g k hk t hx

/-- 8. Under `0 < k`, for every `f ∈ threeOperatorDomain = Dom(T) ∩ Dom(K) ∩ Dom(P)`
and every width `a > 0`, the centered clock-Gaussian state `action ε a ha.le 0 f`
lies simultaneously in `positiveVacuumCoreDomain`, `unconditionalCoreDomain`,
and `growingClockCoreDomain`. -/
theorem gaussian_mem_all_three_coreDomains_of_pos
    (hk : 0 < k) (a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ threeOperatorDomain ε hε h hh hb m g k) :
    action ε a ha.le 0 f ∈ positiveVacuumCoreDomain ε hε h hh hb m g k ∧
      action ε a ha.le 0 f ∈ unconditionalCoreDomain ε hε h hh hb m g k ∧
      action ε a ha.le 0 f ∈ growingClockCoreDomain ε hε h hh hb m g k := by
  have hpv : action ε a ha.le 0 f ∈ positiveVacuumCoreDomain ε hε h hh hb m g k :=
    (positive_vacuum_gaussian_mem_clock_core_of_pos ε hε h hh hb m g k hk 0 a ha hf).1
  have hunc : action ε a ha.le 0 f ∈ unconditionalCoreDomain ε hε h hh hb m g k := by
    rw [← positiveVacuumCoreDomain_eq_unconditionalCoreDomain ε hε h hh hb m g k hk]
    exact hpv
  exact ⟨hpv, hunc, positiveVacuumClockCore_le_growingClockCore ε hε h hh hb m g k hpv⟩

/-- 9. Under `0 < k`, for every `x ∈ positiveVacuumCoreDomain`, the three-operator
shifted left-inverse identity holds:
`RH t a (T x + e^{2t} (K x + P x) + a • x) = x`. -/
theorem core_three_operator_left_inverse_cancel
    (hk : 0 < k) (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ positiveVacuumCoreDomain ε hε h hh hb m g k) :
    RH t a (T ⟨x, hx.1.1.1.1⟩ +
      (Real.exp (2 * t) : ℂ) • (K ⟨x, hx.1.1.1.2⟩ + P ⟨x, hx.1.1.2⟩) + a • x) = x :=
  positive_vacuum_three_operator_left_inverse_cancel
    ε hε h hh hb m g k hk t a ha x hx.1.1

/-- 10. Under `0 < k`, for every `x ∈ positiveVacuumCoreDomain`, the residual
two-operator shifted left-inverse identity holds:
`RS t a (T x + e^{2t} P x + a • x) = x`. -/
theorem core_residual_two_operator_left_inverse_cancel
    (hk : 0 < k) (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ positiveVacuumCoreDomain ε hε h hh hb m g k) :
    RS t a (T ⟨x, hx.1.1.1.1⟩ +
      (Real.exp (2 * t) : ℂ) • P ⟨x, hx.1.1.2⟩ + a • x) = x :=
  positive_vacuum_residual_two_operator_left_inverse_cancel
    ε hε h hh hb m g k hk t a ha x hx.1.1

/-- 11. Under `0 < k`, for every `x ∈ positiveVacuumCoreDomain`, the full
Hamiltonian resolvent applied to the static-shifted vector `T x + a • x`
satisfies `x - RH t a (T x + a • x) = e^{2t} • RH t a (K x + P x)`. -/
theorem core_hamiltonian_static_shifted_resolvent_defect
    (hk : 0 < k) (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ positiveVacuumCoreDomain ε hε h hh hb m g k) :
    x - RH t a (T ⟨x, hx.1.1.1.1⟩ + a • x) =
      (Real.exp (2 * t) : ℂ) •
        RH t a (K ⟨x, hx.1.1.1.2⟩ + P ⟨x, hx.1.1.2⟩) :=
  positive_vacuum_hamiltonian_static_shifted_resolvent_defect
    ε hε h hh hb m g k hk t a ha x hx.1.1

/-- 12. Under `0 < k`, for every `x ∈ positiveVacuumCoreDomain`, the residual
Hamiltonian resolvent applied to the static-shifted vector `T x + a • x`
satisfies `x - RS t a (T x + a • x) = e^{2t} • RS t a (P x)`. -/
theorem core_residual_static_shifted_resolvent_defect
    (hk : 0 < k) (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ positiveVacuumCoreDomain ε hε h hh hb m g k) :
    x - RS t a (T ⟨x, hx.1.1.1.1⟩ + a • x) =
      (Real.exp (2 * t) : ℂ) • RS t a (P ⟨x, hx.1.1.2⟩) :=
  positive_vacuum_residual_static_shifted_resolvent_defect
    ε hε h hh hb m g k hk t a ha x hx.1.1

/-- 13. Under `0 < k`, for every `x ∈ positiveVacuumCoreDomain`, the full
Hamiltonian resolvent applied to the residual-shifted vector
`T x + e^{2t} P x + a • x` satisfies
`x - RH t a (T x + e^{2t} P x + a • x) = e^{2t} • RH t a (K x)`. -/
theorem core_hamiltonian_residual_shifted_resolvent_defect
    (hk : 0 < k) (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ positiveVacuumCoreDomain ε hε h hh hb m g k) :
    x - RH t a (T ⟨x, hx.1.1.1.1⟩ +
      (Real.exp (2 * t) : ℂ) • P ⟨x, hx.1.1.2⟩ + a • x) =
      (Real.exp (2 * t) : ℂ) • RH t a (K ⟨x, hx.1.1.1.2⟩) :=
  positive_vacuum_hamiltonian_residual_shifted_resolvent_defect
    ε hε h hh hb m g k hk t a ha x hx.1.1

/-- 14. Under `0 < k`, for every `x ∈ positiveVacuumCoreDomain`,
`‖x - RH t a (T x + a • x)‖ ≤ a⁻¹ * e^{2t} * (‖K x‖ + ‖P x‖)`. -/
theorem core_hamiltonian_static_shifted_resolvent_defect_norm_le
    (hk : 0 < k) (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ positiveVacuumCoreDomain ε hε h hh hb m g k) :
    ‖x - RH t a (T ⟨x, hx.1.1.1.1⟩ + a • x)‖ ≤
      a⁻¹ * Real.exp (2 * t) * (‖K ⟨x, hx.1.1.1.2⟩‖ + ‖P ⟨x, hx.1.1.2⟩‖) :=
  positive_vacuum_hamiltonian_static_shifted_resolvent_defect_norm_le
    ε hε h hh hb m g k hk t a ha x hx.1.1

/-- 15. Under `0 < k`, for every `x ∈ positiveVacuumCoreDomain`,
`‖x - RS t a (T x + a • x)‖ ≤ a⁻¹ * e^{2t} * ‖P x‖`. -/
theorem core_residual_static_shifted_resolvent_defect_norm_le
    (hk : 0 < k) (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ positiveVacuumCoreDomain ε hε h hh hb m g k) :
    ‖x - RS t a (T ⟨x, hx.1.1.1.1⟩ + a • x)‖ ≤
      a⁻¹ * Real.exp (2 * t) * ‖P ⟨x, hx.1.1.2⟩‖ :=
  positive_vacuum_residual_static_shifted_resolvent_defect_norm_le
    ε hε h hh hb m g k hk t a ha x hx.1.1

/-- 16. Under `0 < k`, for every `x ∈ positiveVacuumCoreDomain`,
`‖x - RH t a (T x + e^{2t} P x + a • x)‖ ≤ a⁻¹ * e^{2t} * ‖K x‖`. -/
theorem core_hamiltonian_residual_shifted_resolvent_defect_norm_le
    (hk : 0 < k) (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ positiveVacuumCoreDomain ε hε h hh hb m g k) :
    ‖x - RH t a (T ⟨x, hx.1.1.1.1⟩ +
      (Real.exp (2 * t) : ℂ) • P ⟨x, hx.1.1.2⟩ + a • x)‖ ≤
      a⁻¹ * Real.exp (2 * t) * ‖K ⟨x, hx.1.1.1.2⟩‖ :=
  positive_vacuum_hamiltonian_residual_shifted_resolvent_defect_norm_le
    ε hε h hh hb m g k hk t a ha x hx.1.1

/-- 17. On `growingClockCoreDomain` (and hence on `positiveVacuumCoreDomain`
and `unconditionalCoreDomain`), the exact potential vs growing second resolvent
identity `RP a x - RG a x = RP a (K (RG a x))` and norm bound `≤ a⁻¹ * ‖x‖`
hold for every `x`. -/
theorem core_potential_growing_second_resolvent_package
    (a : ℝ) (ha : 0 < a) (x : Hilbert)
    (_hx : x ∈ growingClockCoreDomain ε hε h hh hb m g k) :
    RP a x - RG a x =
        RP a (K ⟨RG a x,
          KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
            ε hε h hh hb m g k a ha x⟩) ∧
      ‖RP a x - RG a x‖ ≤
        a⁻¹ * ‖K ⟨RG a x,
          KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
            ε hε h hh hb m g k a ha x⟩‖ ∧
      ‖RP a x - RG a x‖ ≤ a⁻¹ * ‖x‖ :=
  unconditional_potential_growing_second_resolvent_package ε hε h hh hb m g k a ha x

/-- 18. On `positiveVacuumCoreDomain`, the exact residual vs full Hamiltonian
second resolvent identity `RS t a x - RH t a x = e^{2t} • RS t a (K (RH t a x))`
and its radial norm bound hold at every time `t`. -/
theorem core_residual_hamiltonian_second_resolvent_package
    (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (_hx : x ∈ positiveVacuumCoreDomain ε hε h hh hb m g k) :
    RS t a x - RH t a x =
        (Real.exp (2 * t) : ℂ) •
          RS t a (K ⟨RH t a x,
            KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
              ε hε h hh hb m g k t a ha x⟩) ∧
      ‖RS t a x - RH t a x‖ ≤
        a⁻¹ * Real.exp (2 * t) *
          ‖K ⟨RH t a x,
            KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
              ε hε h hh hb m g k t a ha x⟩‖ ∧
      ‖RS t a x - RH t a x‖ ^ 2 ≤
        (a⁻¹) ^ 2 * (1 + 2 * Real.exp (2 * t) * (h ^ 2 / ε ^ 2) * (a⁻¹) ^ 2) * ‖x‖ ^ 2 :=
  unconditional_residual_hamiltonian_second_resolvent_package ε hε h hh hb m g k t a ha x

/-- 19. Under `0 < k`, for every `x ∈ positiveVacuumCoreDomain`, the two-time
full Hamiltonian shifted resolvent defect `x - RH t a (H s x + a • x)` obeys
the Lipschitz bound `≤ |e^{2t} - e^{2s}| * (a⁻¹ * (‖K x‖ + ‖P x‖))` and
converges to `x` as `s → t`. -/
theorem core_two_time_shifted_resolvent_package
    (hk : 0 < k) (s t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ positiveVacuumCoreDomain ε hε h hh hb m g k) :
    let hxs := (positive_vacuum_three_operator_hamiltonian_eval
      ε hε h hh hb m g k hk s hx.1.1.1.1 hx.1.1.1.2 hx.1.1.2).choose
    ‖x - RH t a (H s ⟨x, hxs⟩ + a • x)‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| *
        (a⁻¹ * (‖K ⟨x, hx.1.1.1.2⟩‖ + ‖P ⟨x, hx.1.1.2⟩‖)) ∧
    Tendsto (fun s' : ℝ =>
      RH t a (H s' ⟨x, (positive_vacuum_three_operator_hamiltonian_eval
        ε hε h hh hb m g k hk s' hx.1.1.1.1 hx.1.1.1.2 hx.1.1.2).choose⟩ + a • x))
      (𝓝 t) (𝓝 x) :=
  positive_vacuum_two_time_shifted_resolvent_package
    ε hε h hh hb m g k hk s t a ha x hx.1.1

/-- 20. Under `0 < k`, for every `x ∈ positiveVacuumCoreDomain`, the two-time
residual shifted resolvent defect `x - RS t a (S s x + a • x)` obeys the
Lipschitz bound `≤ |e^{2t} - e^{2s}| * (a⁻¹ * ‖P x‖)` and converges to `x`
as `s → t`. -/
theorem core_two_time_residual_shifted_resolvent_package
    (hk : 0 < k) (s t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ positiveVacuumCoreDomain ε hε h hh hb m g k) :
    let hxs := (positive_vacuum_three_operator_residual_eval
      ε hε h hh hb m g k hk s hx.1.1.1.1 hx.1.1.1.2 hx.1.1.2).choose
    ‖x - RS t a (S s ⟨x, hxs⟩ + a • x)‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| * (a⁻¹ * ‖P ⟨x, hx.1.1.2⟩‖) ∧
    Tendsto (fun s' : ℝ =>
      RS t a (S s' ⟨x, (positive_vacuum_three_operator_residual_eval
        ε hε h hh hb m g k hk s' hx.1.1.1.1 hx.1.1.1.2 hx.1.1.2).choose⟩ + a • x))
      (𝓝 t) (𝓝 x) :=
  positive_vacuum_two_time_residual_shifted_resolvent_package
    ε hε h hh hb m g k hk s t a ha x hx.1.1

/-- 21. For every `x ∈ positiveVacuumCoreDomain` and `a > 0`, all four shifted
resolvent outputs `RH t a x`, `RS t a x`, `RG a x`, and `RP a x` remain in
`Dom(clockHalf ε)` alongside `x`. -/
theorem core_resolvents_preserve_clockHalf
    (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ positiveVacuumCoreDomain ε hε h hh hb m g k) :
    x ∈ (clockHalf ε).domain ∧
      RH t a x ∈ (clockHalf ε).domain ∧
      RS t a x ∈ (clockHalf ε).domain ∧
      RG a x ∈ (clockHalf ε).domain ∧
      RP a x ∈ (clockHalf ε).domain :=
  ⟨hx.2,
   KFCausalClockFloorHamiltonianClockCore.resolvent_half_domain
     ε hε h hh hw m g k t a ha x hx.2,
   KFCausalClockFloorResidualClockCore.resolvent_half_domain
     ε hε h hh hw m g k t a ha x hx.2,
   KFCausalClockFloorGrowingClockResolvent.resolvent_half_domain
     ε hε h hh hw m g k a ha x hx.2,
   KFCausalClockFloorPotentialClockResolvent.resolvent_half_domain
     ε hε h hh hw m g k a ha x hx.2⟩

/-- 22. Under `0 < k`, for any `t, s : ℝ`, `a > 0`, and `x ∈ threeOperatorDomain`,
the canonical sequence `coreApproxSeq ε x` lies in `positiveVacuumCoreDomain`,
`unconditionalCoreDomain`, and `growingClockCoreDomain` for every `j : ℕ`,
converges to `x` in `Hilbert`, and satisfies the three-operator shifted
resolvent defect identities at time `s` for every `j : ℕ`. -/
theorem positive_vacuum_coreApproxSeq_with_resolvent_identities
    (hk : 0 < k) (s a : ℝ) (ha : 0 < a)
    (x : Hilbert) (hx : x ∈ threeOperatorDomain ε hε h hh hb m g k) :
    (∀ j, coreApproxSeq ε x j ∈ positiveVacuumCoreDomain ε hε h hh hb m g k) ∧
      (∀ j, coreApproxSeq ε x j ∈ unconditionalCoreDomain ε hε h hh hb m g k) ∧
      (∀ j, coreApproxSeq ε x j ∈ growingClockCoreDomain ε hε h hh hb m g k) ∧
      (∀ j, ∃ hTj : coreApproxSeq ε x j ∈ (T).domain,
        ∃ hKj : coreApproxSeq ε x j ∈ (K).domain,
        ∃ hPj : coreApproxSeq ε x j ∈ (P).domain,
          coreApproxSeq ε x j - RH s a (T ⟨coreApproxSeq ε x j, hTj⟩ + a • coreApproxSeq ε x j) =
            (Real.exp (2 * s) : ℂ) •
              RH s a (K ⟨coreApproxSeq ε x j, hKj⟩ + P ⟨coreApproxSeq ε x j, hPj⟩) ∧
          coreApproxSeq ε x j - RS s a (T ⟨coreApproxSeq ε x j, hTj⟩ + a • coreApproxSeq ε x j) =
            (Real.exp (2 * s) : ℂ) • RS s a (P ⟨coreApproxSeq ε x j, hPj⟩) ∧
          coreApproxSeq ε x j - RH s a (T ⟨coreApproxSeq ε x j, hTj⟩ +
              (Real.exp (2 * s) : ℂ) • P ⟨coreApproxSeq ε x j, hPj⟩ + a • coreApproxSeq ε x j) =
            (Real.exp (2 * s) : ℂ) • RH s a (K ⟨coreApproxSeq ε x j, hKj⟩)) ∧
      Tendsto (coreApproxSeq ε x) atTop (𝓝 x) := by
  have hmem : ∀ j, coreApproxSeq ε x j ∈ positiveVacuumCoreDomain ε hε h hh hb m g k ∧
      coreApproxSeq ε x j ∈ unconditionalCoreDomain ε hε h hh hb m g k ∧
      coreApproxSeq ε x j ∈ growingClockCoreDomain ε hε h hh hb m g k :=
    fun j => gaussian_mem_all_three_coreDomains_of_pos
      ε hε h hh hb m g k hk (((j : ℝ) + 1)⁻¹) (by positivity) x hx
  refine ⟨fun j => (hmem j).1, fun j => (hmem j).2.1, fun j => (hmem j).2.2, ?_,
    sequence_tendsto ε 0 x⟩
  intro j
  have hj := (hmem j).1
  refine ⟨hj.1.1.1.1, hj.1.1.1.2, hj.1.1.2, ?_, ?_, ?_⟩
  · exact core_hamiltonian_static_shifted_resolvent_defect
      ε hε h hh hb m g k hk s a ha (coreApproxSeq ε x j) hj
  · exact core_residual_static_shifted_resolvent_defect
      ε hε h hh hb m g k hk s a ha (coreApproxSeq ε x j) hj
  · exact core_hamiltonian_residual_shifted_resolvent_defect
      ε hε h hh hb m g k hk s a ha (coreApproxSeq ε x j) hj

/-- 23. Under `0 < k`, for every `x ∈ threeOperatorDomain`, the canonical
sequence `coreApproxSeq ε x` obeys the quantitative shifted resolvent defect
norm bounds at every index `j : ℕ`. -/
theorem positive_vacuum_coreApproxSeq_resolvent_norm_bounds
    (hk : 0 < k) (s a : ℝ) (ha : 0 < a)
    (x : Hilbert) (hx : x ∈ threeOperatorDomain ε hε h hh hb m g k) :
    (∀ j, coreApproxSeq ε x j ∈ positiveVacuumCoreDomain ε hε h hh hb m g k) ∧
      (∀ j, ∃ hTj : coreApproxSeq ε x j ∈ (T).domain,
        ∃ hKj : coreApproxSeq ε x j ∈ (K).domain,
        ∃ hPj : coreApproxSeq ε x j ∈ (P).domain,
          ‖coreApproxSeq ε x j - RH s a (T ⟨coreApproxSeq ε x j, hTj⟩ + a • coreApproxSeq ε x j)‖ ≤
            a⁻¹ * Real.exp (2 * s) *
              (‖K ⟨coreApproxSeq ε x j, hKj⟩‖ + ‖P ⟨coreApproxSeq ε x j, hPj⟩‖) ∧
          ‖coreApproxSeq ε x j - RS s a (T ⟨coreApproxSeq ε x j, hTj⟩ + a • coreApproxSeq ε x j)‖ ≤
            a⁻¹ * Real.exp (2 * s) * ‖P ⟨coreApproxSeq ε x j, hPj⟩‖) ∧
      Tendsto (coreApproxSeq ε x) atTop (𝓝 x) := by
  have hmem : ∀ j, coreApproxSeq ε x j ∈ positiveVacuumCoreDomain ε hε h hh hb m g k :=
    fun j => (gaussian_mem_all_three_coreDomains_of_pos
      ε hε h hh hb m g k hk (((j : ℝ) + 1)⁻¹) (by positivity) x hx).1
  refine ⟨hmem, ?_, sequence_tendsto ε 0 x⟩
  intro j
  have hj := hmem j
  refine ⟨hj.1.1.1.1, hj.1.1.1.2, hj.1.1.2, ?_, ?_⟩
  · exact core_hamiltonian_static_shifted_resolvent_defect_norm_le
      ε hε h hh hb m g k hk s a ha (coreApproxSeq ε x j) hj
  · exact core_residual_static_shifted_resolvent_defect_norm_le
      ε hε h hh hb m g k hk s a ha (coreApproxSeq ε x j) hj

/-- 24. Under `0 < k`, `positiveVacuumCoreDomain` is an operator graph core for
the static kinetic generator `T` on the full strip `|h| ≤ π * ε / 3`. -/
theorem positiveVacuumCoreDomain_static_graph_core (hk : 0 < k) :
    ((T).graph ⊓
      (positiveVacuumCoreDomain ε hε h hh hb m g k).comap
        (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure = (T).graph :=
  positive_vacuum_clock_core_static_graph_core ε hε h hh hb m g k hk

/-- 25. Unconditionally for all real couplings `m, g, k`, `unconditionalCoreDomain`
is an operator graph core for the static kinetic generator `T` on `|h| ≤ π * ε / 3`. -/
theorem unconditionalCoreDomain_static_graph_core :
    ((T).graph ⊓
      (unconditionalCoreDomain ε hε h hh hb m g k).comap
        (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure = (T).graph :=
  unconditional_clock_core_static_graph_core ε hε h hh hb m g k

/-- 26. Unconditionally for all real couplings `m, g, k`, `growingClockCoreDomain`
is an operator graph core for the growing Hamiltonian `G = K + P` on `|h| ≤ π * ε / 3`. -/
theorem growingClockCoreDomain_growing_graph_core :
    ((G).graph ⊓
      (growingClockCoreDomain ε hε h hh hb m g k).comap
        (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure = (G).graph :=
  growing_clock_core_graph_core ε hε h hh hb m g k

/-- 27. On the quarter-strip `|h| ≤ π * ε / 4`, `growingClockCoreDomain` is
simultaneously an unconditional operator graph core for both `G = K + P` and
the ordered-potential generator `P` for all real couplings `m, g, k`. -/
theorem growingClockCoreDomain_simultaneous_growing_and_potential_core
    (hq : |h| ≤ Real.pi * ε / 4) :
    ((G).graph ⊓
      (growingClockCoreDomain ε hε h hh hb m g k).comap
        (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure = (G).graph ∧
    ((P).graph ⊓
      (growingClockCoreDomain ε hε h hh hb m g k).comap
        (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure = (P).graph :=
  growing_and_potential_simultaneous_clock_core ε hε h hh hb m g k hq

/-- 28. On the quarter-strip `|h| ≤ π * ε / 4`, `growingClockCoreDomain` is
dense in `Hilbert` for all real couplings `m, g, k`. -/
theorem growingClockCoreDomain_dense_quarter (hq : |h| ≤ Real.pi * ε / 4) :
    Dense (growingClockCoreDomain ε hε h hh hb m g k : Set Hilbert) :=
  growingClockCore_dense ε hε h hh hb m g k hq

/-- 29. Every vector `x ∈ growingClockCoreDomain` belongs simultaneously to
`Dom(G)`, `Dom(K)`, `Dom(P)`, `Dom(clockOperator ε hε)`, and `Dom(clockHalf ε)`
and satisfies `RG a (K x + P x + a • x) = x` for all `a > 0`. -/
theorem growingClockCoreDomain_mem_and_left_inverse
    (a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ growingClockCoreDomain ε hε h hh hb m g k) :
    ∃ hGx : x ∈ (G).domain,
      ∃ hKx : x ∈ (K).domain,
      ∃ hPx : x ∈ (P).domain,
        RG a (K ⟨x, hKx⟩ + P ⟨x, hPx⟩ + a • x) = x ∧
        G ⟨x, hGx⟩ = K ⟨x, hKx⟩ + P ⟨x, hPx⟩ := by
  have hall := growingClockCore_mem_all_domains ε hε h hh hb m g k hx
  have hGeq : G ⟨x, hall.1⟩ = K ⟨x, hall.2.1⟩ + P ⟨x, hall.2.2.1⟩ :=
    growing_apply_eq_radial_add_potential ε hε h hh hb m g k hall.1
  refine ⟨hall.1, hall.2.1, hall.2.2.1, ?_, hGeq⟩
  rw [← hGeq]
  exact KFCausalClockFloorGrowingYosida.left_inverse
    ε hε h hh hw m g k a ha ⟨x, hall.1⟩

/-- 30. Master Positive-Vacuum Unconditional 5-Operator Core Synthesis (`0 < k`):
simultaneously packages the equality `positiveVacuumCoreDomain = unconditionalCoreDomain`,
its identification with `(T).domain ⊓ growingClockCoreDomain` and
`(H t).domain ⊓ growingClockCoreDomain`, the static graph core property for `T`,
and the growing graph core property for `G = K + P` on `|h| ≤ π * ε / 3`. -/
theorem positive_vacuum_five_operator_core_bridge_master
    (hk : 0 < k) (t : ℝ) :
    positiveVacuumCoreDomain ε hε h hh hb m g k =
        unconditionalCoreDomain ε hε h hh hb m g k ∧
      positiveVacuumCoreDomain ε hε h hh hb m g k =
        (T).domain ⊓ growingClockCoreDomain ε hε h hh hb m g k ∧
      unconditionalCoreDomain ε hε h hh hb m g k =
        (H t).domain ⊓ growingClockCoreDomain ε hε h hh hb m g k ∧
      ((T).graph ⊓
        (positiveVacuumCoreDomain ε hε h hh hb m g k).comap
          (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure = (T).graph ∧
      ((G).graph ⊓
        (growingClockCoreDomain ε hε h hh hb m g k).comap
          (LinearMap.fst ℂ Hilbert Hilbert)).topologicalClosure = (G).graph :=
  ⟨positiveVacuumCoreDomain_eq_unconditionalCoreDomain ε hε h hh hb m g k hk,
   positiveVacuumCoreDomain_eq_static_inf_growingClockCoreDomain ε hε h hh hb m g k,
   unconditionalCoreDomain_eq_hamiltonian_inf_growingClockCoreDomain ε hε h hh hb m g k hk t,
   positiveVacuumCoreDomain_static_graph_core ε hε h hh hb m g k hk,
   growingClockCoreDomain_growing_graph_core ε hε h hh hb m g k⟩

#print axioms positiveVacuumCoreDomain_eq_unconditionalCoreDomain
#print axioms positiveVacuumCoreDomain_eq_static_inf_growingClockCoreDomain
#print axioms unconditionalCoreDomain_eq_static_inf_growingClockCoreDomain
#print axioms unconditionalCoreDomain_eq_hamiltonian_inf_growingClockCoreDomain
#print axioms unconditionalCoreDomain_eq_residual_inf_growingClockCoreDomain
#print axioms coreDomains_le_growingClockCoreDomain
#print axioms positiveVacuumCoreDomain_mem_all_ten_domains
#print axioms gaussian_mem_all_three_coreDomains_of_pos
#print axioms core_three_operator_left_inverse_cancel
#print axioms core_residual_two_operator_left_inverse_cancel
#print axioms core_hamiltonian_static_shifted_resolvent_defect
#print axioms core_residual_static_shifted_resolvent_defect
#print axioms core_hamiltonian_residual_shifted_resolvent_defect
#print axioms core_hamiltonian_static_shifted_resolvent_defect_norm_le
#print axioms core_residual_static_shifted_resolvent_defect_norm_le
#print axioms core_hamiltonian_residual_shifted_resolvent_defect_norm_le
#print axioms core_potential_growing_second_resolvent_package
#print axioms core_residual_hamiltonian_second_resolvent_package
#print axioms core_two_time_shifted_resolvent_package
#print axioms core_two_time_residual_shifted_resolvent_package
#print axioms core_resolvents_preserve_clockHalf
#print axioms positive_vacuum_coreApproxSeq_with_resolvent_identities
#print axioms positive_vacuum_coreApproxSeq_resolvent_norm_bounds
#print axioms positiveVacuumCoreDomain_static_graph_core
#print axioms unconditionalCoreDomain_static_graph_core
#print axioms growingClockCoreDomain_growing_graph_core
#print axioms growingClockCoreDomain_simultaneous_growing_and_potential_core
#print axioms growingClockCoreDomain_dense_quarter
#print axioms growingClockCoreDomain_mem_and_left_inverse
#print axioms positive_vacuum_five_operator_core_bridge_master

end
end UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumUnconditionalCoreBridge
