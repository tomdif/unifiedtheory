/- Positive-Vacuum Unconditional Resolvent Regularity:
under strictly positive vacuum coupling 0 < k, the completed averaged
full-energy form domain and residual form domain split unconditionally into
static, radial-root, and potential form domains across all real times t;
the unconditional common operator domain equals Dom(T) ∩ Dom(K) ∩ Dom(P)
and coincides with Dom(H(t)) ∩ Dom(P), Dom(H(t)) ∩ Dom(T), Dom(H(t)) ∩ Dom(G),
and Dom(S(t)) ∩ Dom(G); all five shifted resolvents preserve their respective
operator, form, and half-clock domains; the unconditional 5-way operator-domain
equivalence for RH(t, a) f extends to a 6-way equivalence with
Dom(T) ∩ Dom(K) ∩ Dom(P); and the exact second resolvent identities and
two-time resolvent continuity estimates hold across all channels. -/
import UnifiedTheory.Audit.KFCausalClockFloorGrowingPotentialSecondResolventIdentity
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianResidualSecondResolventIdentity
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianResolventThreeOperatorSynthesis
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumTwoTimeResolventContinuity
import UnifiedTheory.Audit.KFCausalClockFloorUnconditionalFormDomainSynthesis
import UnifiedTheory.Audit.KFCausalClockFloorStaticClockCore

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumResolventRegularity
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorUnconditionalTwoTimeEvolution
  (commonOperatorDomain common_domain_subset_hamiltonian common_domain_subset_residual
   common_domain_subset_growing)
open KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain
  (positive_vacuum_common_domain_eq_three_operator
   positive_vacuum_hamiltonian_inter_growing_domain_eq
   positive_vacuum_hamiltonian_inter_static_domain_eq
   positive_vacuum_hamiltonian_inter_potential_domain_eq
   positive_vacuum_residual_inter_growing_domain_eq
   positive_vacuum_static_inter_growing_domain_eq
   positive_vacuum_averaged_form_domain_eq
   positive_vacuum_averaged_form_domain_eq_static_inter_growing
   positive_vacuum_three_operator_hamiltonian_eval
   positive_vacuum_three_operator_residual_eval
   unconditional_two_operator_growing_eval)
open KFCausalClockFloorHamiltonianComponentResolventBounds
  (resolvent_mem_hamiltonian_domain resolvent_mem_radial_domain resolvent_mem_residual_domain)
open KFCausalClockFloorGrowingComponentResolventBounds
  (resolvent_mem_growing_domain resolvent_mem_potential_domain)
open KFCausalClockFloorGrowingPotentialSecondResolventIdentity
  (potential_domain_subset_potentialForm_domain
   potential_resolvent_mem_potential_domain
   potential_resolvent_mem_potentialForm_domain
   growing_resolvent_second_resolvent_identity
   potential_sub_growing_resolvent_eq
   potential_sub_growing_resolvent_norm_le_radial
   potential_sub_growing_resolvent_norm_le_source
   potential_sub_growing_resolvent_potentialForm_norm_sq_le_source)
open KFCausalClockFloorHamiltonianResidualSecondResolventIdentity
  (hamiltonian_resolvent_second_resolvent_identity
   residual_sub_hamiltonian_resolvent_eq
   residual_sub_hamiltonian_resolvent_norm_le_radial
   residual_sub_hamiltonian_resolvent_norm_sq_le_source
   residual_sub_hamiltonian_resolvent_two_channel_norm_sq_le_radial
   residual_sub_hamiltonian_resolvent_clockHalf_norm_sq_le_source)
open KFCausalClockFloorHamiltonianResolventThreeOperatorSynthesis
  (hamiltonian_resolvent_mem_potential_iff_common
   hamiltonian_resolvent_mem_static_iff_common
   hamiltonian_resolvent_mem_growing_iff_common
   hamiltonian_resolvent_five_way_domain_iff
   hamiltonian_resolvent_eq_static_add_growing_of_potential
   hamiltonian_resolvent_eq_three_operator_of_potential
   residual_on_hamiltonian_resolvent_eq_static_add_potential
   growing_on_hamiltonian_resolvent_eq_radial_add_potential
   growing_on_hamiltonian_resolvent_split_norm_sq_le
   hamiltonian_resolvent_potential_norm_le_static_add_residual
   hamiltonian_resolvent_static_norm_le_potential_add_residual
   hamiltonian_resolvent_growing_norm_le_static_add_source)
open KFCausalClockFloorPositiveVacuumTwoTimeResolventContinuity
  (resolvent_in_clockHalf_domain
   resolvent_clockHalf_norm_bound
   residual_resolvent_in_clockHalf_domain
   residual_resolvent_clockHalf_norm_bound
   positive_vacuum_two_time_shifted_resolvent_hilbert_bound
   positive_vacuum_two_time_shifted_resolvent_tendsto
   positive_vacuum_two_time_residual_shifted_resolvent_bound
   positive_vacuum_two_time_residual_shifted_resolvent_tendsto
   two_time_resolvent_weak_diff_bound
   two_time_resolvent_weak_continuous
   positive_vacuum_two_time_second_resolvent_bounds_on_growing_domain)

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
local notation "RT" => KFCausalClockFloorStaticClockCore.resolvent ε hε h hh hw m g k
local notation "RG" => KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw m g k
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hw) hh m g k

/-- The potential form domain `Dom(Tpot)`. -/
def potentialDomain : Submodule ℂ Hilbert := (Tpot).domain

/-- The potential self-adjoint generator domain `Dom(P)`. -/
def potentialGeneratorDomain : Submodule ℂ Hilbert := (P).domain

/-- The three-operator generator intersection `Dom(T) ∩ Dom(K) ∩ Dom(P)`. -/
def threeOperatorDomain : Submodule ℂ Hilbert := (T).domain ⊓ (K).domain ⊓ (P).domain

/-- 1. Every vector in the completed full-energy form domain `Dom(Eavg(t))` lies
in the potential form domain `potentialDomain = Dom(Tpot)`. -/
theorem averaged_form_domain_le_potentialDomain (t : ℝ) :
    (Eavg t).domain ≤ potentialDomain ε hε h hh hb m g k := by
  intro f hf
  exact (KFCausalClockFloorUnconditionalFormDomainSynthesis.averaged_domain_subset_three_forms
    ε hε h hh hb m g k t f hf).2.2

/-- 2. Every vector in the completed residual form domain `Dom(Tres(t))` lies
in the potential form domain `potentialDomain = Dom(Tpot)`. -/
theorem residual_form_domain_le_potentialDomain (t : ℝ) :
    (Tres t).domain ≤ potentialDomain ε hε h hh hb m g k := by
  intro f hf
  exact (KFCausalClockFloorUnconditionalFormDomainSynthesis.residual_domain_subset_static_inter_potential
    ε hε h hh hb m g k t f hf).2

/-- 3. Every vector in the completed growing form domain `Dom(Tgrow)` lies in
the potential form domain `potentialDomain = Dom(Tpot)`. -/
theorem growing_form_domain_le_potentialDomain :
    (Tgrow).domain ≤ potentialDomain ε hε h hh hb m g k := by
  intro f hf
  exact ((KFCausalClockFloorGrowingFormReconstruction.growing_domain_iff
    ε hε h hh hb m g k f).mp hf).2

/-- 4. Under `0 < k`, the completed averaged full-energy form domain at time `t`
equals `Dom(Tstat) ∩ Dom(Kroot) ∩ potentialDomain`. -/
theorem positive_vacuum_averaged_form_domain_eq_potentialDomain (hk : 0 < k) (t : ℝ) :
    (Eavg t).domain =
      (Tstat).domain ⊓ (Kroot).domain ⊓ potentialDomain ε hε h hh hb m g k :=
  positive_vacuum_averaged_form_domain_eq ε hε h hh hb m g k hk t

/-- 5. Under `0 < k`, the completed averaged full-energy form domain is
time-invariant across all real times `t, s` and equals
`Dom(Tstat) ∩ Dom(Tgrow)`. -/
theorem positive_vacuum_averaged_form_domain_time_invariant (hk : 0 < k) (t s : ℝ) :
    (Eavg t).domain = (Eavg s).domain ∧
      (Eavg t).domain = (Tstat).domain ⊓ (Tgrow).domain := by
  refine ⟨?_, positive_vacuum_averaged_form_domain_eq_static_inter_growing ε hε h hh hb m g k hk t⟩
  rw [positive_vacuum_averaged_form_domain_eq ε hε h hh hb m g k hk t,
    positive_vacuum_averaged_form_domain_eq ε hε h hh hb m g k hk s]

/-- 6. Every vector in the potential generator domain `potentialGeneratorDomain = Dom(P)`
lies in the potential form domain `potentialDomain = Dom(Tpot)`. -/
theorem potentialGeneratorDomain_le_potentialDomain :
    potentialGeneratorDomain ε hε h hh hb m g k ≤ potentialDomain ε hε h hh hb m g k :=
  fun f hf => potential_domain_subset_potentialForm_domain ε hε h hh hb m g k ⟨f, hf⟩

/-- 7. For every `a > 0` and `f : Hilbert`, the full Hamiltonian resolvent
`RH t a f` lies in `Dom(H(t))`, `Dom(K)`, `Dom(S(t))`, and `potentialDomain = Dom(Tpot)`. -/
theorem hamiltonian_resolvent_mem_domains (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RH t a f ∈ (H t).domain ∧
      RH t a f ∈ (K).domain ∧
      RH t a f ∈ (S t).domain ∧
      RH t a f ∈ potentialDomain ε hε h hh hb m g k :=
  ⟨resolvent_mem_hamiltonian_domain ε hε h hh hb m g k t a ha f,
   resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f,
   resolvent_mem_residual_domain ε hε h hh hb m g k t a ha f,
   KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_potentialForm_domain
     ε hε h hh hb m g k t a ha f⟩

/-- 8. For every `a > 0` and `f : Hilbert`, the growing Hamiltonian resolvent
`RG a f` lies in `Dom(G)`, `Dom(K)`, and `potentialGeneratorDomain = Dom(P)`. -/
theorem growing_resolvent_mem_domains (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RG a f ∈ (G).domain ∧
      RG a f ∈ (K).domain ∧
      RG a f ∈ potentialGeneratorDomain ε hε h hh hb m g k :=
  ⟨resolvent_mem_growing_domain ε hε h hh hb m g k a ha f,
   KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
     ε hε h hh hb m g k a ha f,
   resolvent_mem_potential_domain ε hε h hh hb m g k a ha f⟩

/-- 9. For every `a > 0` and `f : Hilbert`, the potential resolvent `RP a f`
lies in `potentialGeneratorDomain = Dom(P)` and in `potentialDomain = Dom(Tpot)`. -/
theorem potential_resolvent_mem_domains (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RP a f ∈ potentialGeneratorDomain ε hε h hh hb m g k ∧
      RP a f ∈ potentialDomain ε hε h hh hb m g k :=
  ⟨potential_resolvent_mem_potential_domain ε hε h hh hb m g k a ha f,
   potential_resolvent_mem_potentialForm_domain ε hε h hh hb m g k a ha f⟩

/-- 10. Under `0 < k`, a full Hamiltonian resolvent output `RH t a f` (`a > 0`)
belongs to `potentialGeneratorDomain = Dom(P)` if and only if it belongs to
`threeOperatorDomain = Dom(T) ∩ Dom(K) ∩ Dom(P)`. -/
theorem positive_vacuum_hamiltonian_resolvent_mem_potential_iff (hk : 0 < k)
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RH t a f ∈ potentialGeneratorDomain ε hε h hh hb m g k ↔
      RH t a f ∈ threeOperatorDomain ε hε h hh hb m g k := by
  have h1 := hamiltonian_resolvent_mem_potential_iff_common ε hε h hh hb m g k t a ha f
  rw [positive_vacuum_common_domain_eq_three_operator ε hε h hh hb m g k hk] at h1
  exact h1

/-- 11. Under `0 < k`, a full Hamiltonian resolvent output `RH t a f` (`a > 0`)
belongs to `Dom(T)` if and only if it belongs to
`threeOperatorDomain = Dom(T) ∩ Dom(K) ∩ Dom(P)`. -/
theorem positive_vacuum_hamiltonian_resolvent_mem_static_iff (hk : 0 < k)
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RH t a f ∈ (T).domain ↔
      RH t a f ∈ threeOperatorDomain ε hε h hh hb m g k := by
  have h1 := hamiltonian_resolvent_mem_static_iff_common ε hε h hh hb m g k t a ha f
  rw [positive_vacuum_common_domain_eq_three_operator ε hε h hh hb m g k hk] at h1
  exact h1

/-- 12. Under `0 < k`, a full Hamiltonian resolvent output `RH t a f` (`a > 0`)
belongs to `Dom(G)` if and only if it belongs to
`threeOperatorDomain = Dom(T) ∩ Dom(K) ∩ Dom(P)`. -/
theorem positive_vacuum_hamiltonian_resolvent_mem_growing_iff (hk : 0 < k)
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RH t a f ∈ (G).domain ↔
      RH t a f ∈ threeOperatorDomain ε hε h hh hb m g k := by
  have h1 := hamiltonian_resolvent_mem_growing_iff_common ε hε h hh hb m g k t a ha f
  rw [positive_vacuum_common_domain_eq_three_operator ε hε h hh hb m g k hk] at h1
  exact h1

/-- 13. Under `0 < k`, a residual Hamiltonian resolvent output `RS t a f` (`a > 0`)
belongs to `Dom(G)` if and only if it belongs to
`threeOperatorDomain = Dom(T) ∩ Dom(K) ∩ Dom(P)`. -/
theorem positive_vacuum_residual_resolvent_mem_growing_iff (hk : 0 < k)
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RS t a f ∈ (G).domain ↔
      RS t a f ∈ threeOperatorDomain ε hε h hh hb m g k := by
  have hS : RS t a f ∈ (S t).domain :=
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha f).1
  constructor
  · intro hG
    have hSG : RS t a f ∈ (S t).domain ⊓ (G).domain := ⟨hS, hG⟩
    rw [positive_vacuum_residual_inter_growing_domain_eq ε hε h hh hb m g k hk t] at hSG
    exact hSG
  · intro h3
    exact (unconditional_two_operator_growing_eval ε hε h hh hb m g k h3.1.2 h3.2).choose

/-- 14. Under `0 < k`, the 5-way operator-domain equivalence for `RH t a f`
extends to a 6-way equivalence including `threeOperatorDomain`. -/
theorem positive_vacuum_hamiltonian_resolvent_six_way_domain_iff (hk : 0 < k)
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    (RH t a f ∈ (P).domain ↔ RH t a f ∈ (T).domain) ∧
    (RH t a f ∈ (T).domain ↔ RH t a f ∈ (G).domain) ∧
    (RH t a f ∈ (G).domain ↔ RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k) ∧
    (RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k ↔
      RH t a f ∈ threeOperatorDomain ε hε h hh hb m g k) ∧
    (RH t a f ∈ commonOperatorDomain ε hε h hh hb m g k ↔
      RS t a (f - (Real.exp (2 * t) : ℂ) •
        K ⟨RH t a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩) ∈ (P).domain) := by
  have h5 := hamiltonian_resolvent_five_way_domain_iff ε hε h hh hb m g k t a ha f
  refine ⟨h5.1, h5.2.1, h5.2.2.1, ?_, h5.2.2.2⟩
  exact iff_of_eq (congrArg (fun D : Submodule ℂ Hilbert => RH t a f ∈ D)
    (positive_vacuum_common_domain_eq_three_operator ε hε h hh hb m g k hk))

/-- 15. All five shifted resolvents `RH t a`, `RS t a`, `RT t a`, `RG a`, and
`RP a` preserve the unbounded half-clock domain `Dom(clockHalf ε)` for `a > 0`. -/
theorem all_five_resolvents_preserve_clockHalf_domain (t a : ℝ) (ha : 0 < a)
    (f : Hilbert) (hf : f ∈ (clockHalf ε).domain) :
    RH t a f ∈ (clockHalf ε).domain ∧
      RS t a f ∈ (clockHalf ε).domain ∧
      RT t a f ∈ (clockHalf ε).domain ∧
      RG a f ∈ (clockHalf ε).domain ∧
      RP a f ∈ (clockHalf ε).domain :=
  ⟨KFCausalClockFloorHamiltonianClockCore.resolvent_half_domain ε hε h hh hw m g k t a ha f hf,
   KFCausalClockFloorResidualClockCore.resolvent_half_domain ε hε h hh hw m g k t a ha f hf,
   KFCausalClockFloorStaticClockCore.resolvent_half_domain ε hε h hh hw m g k t a ha f hf,
   KFCausalClockFloorGrowingClockResolvent.resolvent_half_domain ε hε h hh hw m g k a ha f hf,
   KFCausalClockFloorPotentialClockResolvent.resolvent_half_domain ε hε h hh hw m g k a ha f hf⟩

/-- 16. Unconditional half-clock smoothing for `RH t a` and `RS t a` on every
`f : Hilbert` (without domain assumptions on `f`):
`‖clockHalf (RH t a f)‖ ≤ √2 √(a⁻¹) ‖f‖` and `‖clockHalf (RS t a f)‖ ≤ √2 √(a⁻¹) ‖f‖`. -/
theorem hamiltonian_and_residual_resolvent_unconditional_clockHalf_bounds
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖clockHalf ε ⟨RH t a f, resolvent_in_clockHalf_domain ε hε h hh hb m g k t a ha f⟩‖ ≤
        Real.sqrt 2 * Real.sqrt (a⁻¹) * ‖f‖ ∧
      ‖clockHalf ε ⟨RS t a f, residual_resolvent_in_clockHalf_domain ε hε h hh hb m g k t a ha f⟩‖ ≤
        Real.sqrt 2 * Real.sqrt (a⁻¹) * ‖f‖ :=
  ⟨resolvent_clockHalf_norm_bound ε hε h hh hb m g k t a ha f,
   residual_resolvent_clockHalf_norm_bound ε hε h hh hb m g k t a ha f⟩

/-- 17. Unconditional exact second resolvent identity between `RP a` and `RG a`
on all of `Hilbert`:
`RP a f - RG a f = RP a (K (RG a f))` and `‖RP a f - RG a f‖ ≤ a⁻¹ * ‖f‖`. -/
theorem unconditional_potential_growing_second_resolvent_package
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RP a f - RG a f =
        RP a (K ⟨RG a f,
          KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
            ε hε h hh hb m g k a ha f⟩) ∧
      ‖RP a f - RG a f‖ ≤
        a⁻¹ * ‖K ⟨RG a f,
          KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
            ε hε h hh hb m g k a ha f⟩‖ ∧
      ‖RP a f - RG a f‖ ≤ a⁻¹ * ‖f‖ :=
  ⟨potential_sub_growing_resolvent_eq ε hε h hh hb m g k a ha f,
   potential_sub_growing_resolvent_norm_le_radial ε hε h hh hb m g k a ha f,
   potential_sub_growing_resolvent_norm_le_source ε hε h hh hb m g k a ha f⟩

/-- 18. Unconditional exact second resolvent identity between `RS t a` and `RH t a`
on all of `Hilbert`:
`RS t a f - RH t a f = e^{2t} • RS t a (K (RH t a f))` and radial norm bound. -/
theorem unconditional_residual_hamiltonian_second_resolvent_package
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RS t a f - RH t a f =
        (Real.exp (2 * t) : ℂ) •
          RS t a (K ⟨RH t a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩) ∧
      ‖RS t a f - RH t a f‖ ≤
        a⁻¹ * Real.exp (2 * t) *
          ‖K ⟨RH t a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩‖ ∧
      ‖RS t a f - RH t a f‖ ^ 2 ≤
        (a⁻¹) ^ 2 * (1 + 2 * Real.exp (2 * t) * (h ^ 2 / ε ^ 2) * (a⁻¹) ^ 2) * ‖f‖ ^ 2 :=
  ⟨residual_sub_hamiltonian_resolvent_eq ε hε h hh hb m g k t a ha f,
   residual_sub_hamiltonian_resolvent_norm_le_radial ε hε h hh hb m g k t a ha f,
   residual_sub_hamiltonian_resolvent_norm_sq_le_source ε hε h hh hb m g k t a ha f⟩

/-- 19. Unconditional multi-channel form and half-clock bounds on the resolvent
difference `RS t a f - RH t a f` for all `f : Hilbert`. -/
theorem unconditional_residual_hamiltonian_form_and_clockHalf_bounds
    (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Tstat ⟨RS t a f - RH t a f,
      KFCausalClockFloorHamiltonianResidualSecondResolventIdentity.residual_sub_hamiltonian_resolvent_mem_staticRoot_domain
        ε hε h hh hb m g k t a ha f⟩‖ ^ 2 +
      Real.exp (2 * t) *
        ‖Tpot ⟨RS t a f - RH t a f,
          KFCausalClockFloorHamiltonianResidualSecondResolventIdentity.residual_sub_hamiltonian_resolvent_mem_potentialForm_domain
            ε hε h hh hb m g k t a ha f⟩‖ ^ 2 ≤
      a⁻¹ * Real.exp (4 * t) *
        ‖K ⟨RH t a f, resolvent_mem_radial_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 ∧
    ‖clockHalf ε ⟨RS t a f - RH t a f,
      KFCausalClockFloorHamiltonianResidualSecondResolventIdentity.residual_sub_hamiltonian_resolvent_mem_clockHalf_domain
        ε hε h hh hb m g k t a ha f⟩‖ ^ 2 ≤
      2 * a⁻¹ * (1 + 2 * Real.exp (2 * t) * (h ^ 2 / ε ^ 2) * (a⁻¹) ^ 2) * ‖f‖ ^ 2 :=
  ⟨residual_sub_hamiltonian_resolvent_two_channel_norm_sq_le_radial ε hε h hh hb m g k t a ha f,
   residual_sub_hamiltonian_resolvent_clockHalf_norm_sq_le_source ε hε h hh hb m g k t a ha f⟩

/-- 20. Under `0 < k`, for every `x ∈ threeOperatorDomain = Dom(T) ∩ Dom(K) ∩ Dom(P)`,
the full Hamiltonian vs static resolvent defect on `x` satisfies
`RT t a (T x + a • x) = x` and `RH t a (T x + e^{2t} (K x + P x) + a • x) = x`. -/
theorem positive_vacuum_three_operator_left_inverse_cancel (hk : 0 < k)
    (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ threeOperatorDomain ε hε h hh hb m g k) :
    RH t a (T ⟨x, hx.1.1⟩ +
      (Real.exp (2 * t) : ℂ) • (K ⟨x, hx.1.2⟩ + P ⟨x, hx.2⟩) + a • x) = x := by
  have hc : x ∈ commonOperatorDomain ε hε h hh hb m g k := by
    rw [positive_vacuum_common_domain_eq_three_operator ε hε h hh hb m g k hk]
    exact hx
  let xH : (H t).domain := ⟨x, common_domain_subset_hamiltonian ε hε h hh hb m g k t hc⟩
  have hH : H t xH = T ⟨x, hx.1.1⟩ +
      (Real.exp (2 * t) : ℂ) • (K ⟨x, hx.1.2⟩ + P ⟨x, hx.2⟩) :=
    (H t).mem_graph_snd_inj' ((H t).mem_graph xH)
      (KFCausalClockFloorUnconditionalThreeOperatorDecomposition.unconditional_three_operator_hamiltonian_graph
        ε hε h hh hb m g k t x (T ⟨x, hx.1.1⟩) (K ⟨x, hx.1.2⟩) (P ⟨x, hx.2⟩)
        ((T).mem_graph ⟨x, hx.1.1⟩) ((K).mem_graph ⟨x, hx.1.2⟩)
        ((P).mem_graph ⟨x, hx.2⟩) hc.2) rfl
  rw [← hH]
  exact KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha xH

/-- 21. Under `0 < k`, for every `x ∈ threeOperatorDomain = Dom(T) ∩ Dom(K) ∩ Dom(P)`,
the residual Hamiltonian left-inverse identity holds on the two-operator split:
`RS t a (T x + e^{2t} P x + a • x) = x`. -/
theorem positive_vacuum_residual_two_operator_left_inverse_cancel (hk : 0 < k)
    (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ threeOperatorDomain ε hε h hh hb m g k) :
    RS t a (T ⟨x, hx.1.1⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hx.2⟩ + a • x) = x := by
  have hc : x ∈ commonOperatorDomain ε hε h hh hb m g k := by
    rw [positive_vacuum_common_domain_eq_three_operator ε hε h hh hb m g k hk]
    exact hx
  let xS : (S t).domain := ⟨x, common_domain_subset_residual ε hε h hh hb m g k t hc⟩
  have hS : S t xS = T ⟨x, hx.1.1⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hx.2⟩ :=
    (S t).mem_graph_snd_inj' ((S t).mem_graph xS)
      (KFCausalClockFloorUnconditionalThreeOperatorDecomposition.unconditional_three_operator_residual_graph
        ε hε h hh hb m g k t x (T ⟨x, hx.1.1⟩) (P ⟨x, hx.2⟩)
        ((T).mem_graph ⟨x, hx.1.1⟩) ((P).mem_graph ⟨x, hx.2⟩) hc.2) rfl
  rw [← hS]
  exact KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t a ha xS

/-- 22. Under `0 < k`, for every `x ∈ threeOperatorDomain = Dom(T) ∩ Dom(K) ∩ Dom(P)`,
the full Hamiltonian resolvent applied to the static-shifted vector `T x + a • x`
satisfies `x - RH t a (T x + a • x) = e^{2t} • RH t a (K x + P x)`. -/
theorem positive_vacuum_hamiltonian_static_shifted_resolvent_defect (hk : 0 < k)
    (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ threeOperatorDomain ε hε h hh hb m g k) :
    x - RH t a (T ⟨x, hx.1.1⟩ + a • x) =
      (Real.exp (2 * t) : ℂ) • RH t a (K ⟨x, hx.1.2⟩ + P ⟨x, hx.2⟩) := by
  have hleft := positive_vacuum_three_operator_left_inverse_cancel
    ε hε h hh hb m g k hk t a ha x hx
  have hsub : (T ⟨x, hx.1.1⟩ +
      (Real.exp (2 * t) : ℂ) • (K ⟨x, hx.1.2⟩ + P ⟨x, hx.2⟩) + a • x) -
      (T ⟨x, hx.1.1⟩ + a • x) =
      (Real.exp (2 * t) : ℂ) • (K ⟨x, hx.1.2⟩ + P ⟨x, hx.2⟩) := by abel
  calc
    x - RH t a (T ⟨x, hx.1.1⟩ + a • x) =
        RH t a (T ⟨x, hx.1.1⟩ +
          (Real.exp (2 * t) : ℂ) • (K ⟨x, hx.1.2⟩ + P ⟨x, hx.2⟩) + a • x) -
          RH t a (T ⟨x, hx.1.1⟩ + a • x) := by rw [hleft]
    _ = RH t a ((T ⟨x, hx.1.1⟩ +
          (Real.exp (2 * t) : ℂ) • (K ⟨x, hx.1.2⟩ + P ⟨x, hx.2⟩) + a • x) -
          (T ⟨x, hx.1.1⟩ + a • x)) := (map_sub (RH t a) _ _).symm
    _ = RH t a ((Real.exp (2 * t) : ℂ) • (K ⟨x, hx.1.2⟩ + P ⟨x, hx.2⟩)) := by rw [hsub]
    _ = (Real.exp (2 * t) : ℂ) • RH t a (K ⟨x, hx.1.2⟩ + P ⟨x, hx.2⟩) :=
        map_smul (RH t a) _ _

/-- 23. Under `0 < k`, for every `x ∈ threeOperatorDomain = Dom(T) ∩ Dom(K) ∩ Dom(P)`,
the residual Hamiltonian resolvent applied to the static-shifted vector `T x + a • x`
satisfies `x - RS t a (T x + a • x) = e^{2t} • RS t a (P x)`. -/
theorem positive_vacuum_residual_static_shifted_resolvent_defect (hk : 0 < k)
    (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ threeOperatorDomain ε hε h hh hb m g k) :
    x - RS t a (T ⟨x, hx.1.1⟩ + a • x) =
      (Real.exp (2 * t) : ℂ) • RS t a (P ⟨x, hx.2⟩) := by
  have hleft := positive_vacuum_residual_two_operator_left_inverse_cancel
    ε hε h hh hb m g k hk t a ha x hx
  have hsub : (T ⟨x, hx.1.1⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hx.2⟩ + a • x) -
      (T ⟨x, hx.1.1⟩ + a • x) =
      (Real.exp (2 * t) : ℂ) • P ⟨x, hx.2⟩ := by abel
  calc
    x - RS t a (T ⟨x, hx.1.1⟩ + a • x) =
        RS t a (T ⟨x, hx.1.1⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hx.2⟩ + a • x) -
          RS t a (T ⟨x, hx.1.1⟩ + a • x) := by rw [hleft]
    _ = RS t a ((T ⟨x, hx.1.1⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hx.2⟩ + a • x) -
          (T ⟨x, hx.1.1⟩ + a • x)) := (map_sub (RS t a) _ _).symm
    _ = RS t a ((Real.exp (2 * t) : ℂ) • P ⟨x, hx.2⟩) := by rw [hsub]
    _ = (Real.exp (2 * t) : ℂ) • RS t a (P ⟨x, hx.2⟩) := map_smul (RS t a) _ _

/-- 24. Under `0 < k`, for every `x ∈ threeOperatorDomain = Dom(T) ∩ Dom(K) ∩ Dom(P)`,
the full Hamiltonian resolvent applied to the residual-shifted vector
`T x + e^{2t} P x + a • x` satisfies
`x - RH t a (T x + e^{2t} P x + a • x) = e^{2t} • RH t a (K x)`. -/
theorem positive_vacuum_hamiltonian_residual_shifted_resolvent_defect (hk : 0 < k)
    (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ threeOperatorDomain ε hε h hh hb m g k) :
    x - RH t a (T ⟨x, hx.1.1⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hx.2⟩ + a • x) =
      (Real.exp (2 * t) : ℂ) • RH t a (K ⟨x, hx.1.2⟩) := by
  have hleft := positive_vacuum_three_operator_left_inverse_cancel
    ε hε h hh hb m g k hk t a ha x hx
  have hsub : (T ⟨x, hx.1.1⟩ +
      (Real.exp (2 * t) : ℂ) • (K ⟨x, hx.1.2⟩ + P ⟨x, hx.2⟩) + a • x) -
      (T ⟨x, hx.1.1⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hx.2⟩ + a • x) =
      (Real.exp (2 * t) : ℂ) • K ⟨x, hx.1.2⟩ := by
    rw [smul_add]
    abel
  calc
    x - RH t a (T ⟨x, hx.1.1⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hx.2⟩ + a • x) =
        RH t a (T ⟨x, hx.1.1⟩ +
          (Real.exp (2 * t) : ℂ) • (K ⟨x, hx.1.2⟩ + P ⟨x, hx.2⟩) + a • x) -
          RH t a (T ⟨x, hx.1.1⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hx.2⟩ + a • x) := by rw [hleft]
    _ = RH t a ((T ⟨x, hx.1.1⟩ +
          (Real.exp (2 * t) : ℂ) • (K ⟨x, hx.1.2⟩ + P ⟨x, hx.2⟩) + a • x) -
          (T ⟨x, hx.1.1⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hx.2⟩ + a • x)) :=
        (map_sub (RH t a) _ _).symm
    _ = RH t a ((Real.exp (2 * t) : ℂ) • K ⟨x, hx.1.2⟩) := by rw [hsub]
    _ = (Real.exp (2 * t) : ℂ) • RH t a (K ⟨x, hx.1.2⟩) := map_smul (RH t a) _ _

/-- 25. Under `0 < k`, for every `x ∈ threeOperatorDomain = Dom(T) ∩ Dom(K) ∩ Dom(P)`,
`‖x - RH t a (T x + a • x)‖ ≤ a⁻¹ * e^{2t} * (‖K x‖ + ‖P x‖)`. -/
theorem positive_vacuum_hamiltonian_static_shifted_resolvent_defect_norm_le (hk : 0 < k)
    (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ threeOperatorDomain ε hε h hh hb m g k) :
    ‖x - RH t a (T ⟨x, hx.1.1⟩ + a • x)‖ ≤
      a⁻¹ * Real.exp (2 * t) * (‖K ⟨x, hx.1.2⟩‖ + ‖P ⟨x, hx.2⟩‖) := by
  rw [positive_vacuum_hamiltonian_static_shifted_resolvent_defect
      ε hε h hh hb m g k hk t a ha x hx,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (2 * t))]
  have h1 := KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_norm_le
    ε hε h hh hb m g k t a ha (K ⟨x, hx.1.2⟩ + P ⟨x, hx.2⟩)
  have h2 : a⁻¹ * ‖K ⟨x, hx.1.2⟩ + P ⟨x, hx.2⟩‖ ≤
      a⁻¹ * (‖K ⟨x, hx.1.2⟩‖ + ‖P ⟨x, hx.2⟩‖) :=
    mul_le_mul_of_nonneg_left (norm_add_le _ _) (inv_nonneg.mpr ha.le)
  have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) (Real.exp_pos (2 * t)).le
  linarith

/-- 26. Under `0 < k`, for every `x ∈ threeOperatorDomain = Dom(T) ∩ Dom(K) ∩ Dom(P)`,
`‖x - RS t a (T x + a • x)‖ ≤ a⁻¹ * e^{2t} * ‖P x‖`. -/
theorem positive_vacuum_residual_static_shifted_resolvent_defect_norm_le (hk : 0 < k)
    (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ threeOperatorDomain ε hε h hh hb m g k) :
    ‖x - RS t a (T ⟨x, hx.1.1⟩ + a • x)‖ ≤
      a⁻¹ * Real.exp (2 * t) * ‖P ⟨x, hx.2⟩‖ := by
  rw [positive_vacuum_residual_static_shifted_resolvent_defect
      ε hε h hh hb m g k hk t a ha x hx,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (2 * t))]
  have h1 := KFCausalClockFloorResidualResolventRadialRootRegularity.residual_resolvent_norm_le
    ε hε h hh hb m g k t a ha (P ⟨x, hx.2⟩)
  have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (2 * t)).le
  linarith

/-- 27. Under `0 < k`, for every `x ∈ threeOperatorDomain = Dom(T) ∩ Dom(K) ∩ Dom(P)`,
`‖x - RH t a (T x + e^{2t} P x + a • x)‖ ≤ a⁻¹ * e^{2t} * ‖K x‖`. -/
theorem positive_vacuum_hamiltonian_residual_shifted_resolvent_defect_norm_le (hk : 0 < k)
    (t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ threeOperatorDomain ε hε h hh hb m g k) :
    ‖x - RH t a (T ⟨x, hx.1.1⟩ + (Real.exp (2 * t) : ℂ) • P ⟨x, hx.2⟩ + a • x)‖ ≤
      a⁻¹ * Real.exp (2 * t) * ‖K ⟨x, hx.1.2⟩‖ := by
  rw [positive_vacuum_hamiltonian_residual_shifted_resolvent_defect
      ε hε h hh hb m g k hk t a ha x hx,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (2 * t))]
  have h1 := KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_norm_le
    ε hε h hh hb m g k t a ha (K ⟨x, hx.1.2⟩)
  have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (2 * t)).le
  linarith

/-- 28. Under `0 < k`, for every `x ∈ threeOperatorDomain = Dom(T) ∩ Dom(K) ∩ Dom(P)`,
the two-time shifted resolvent defect `x - RH t a (H s x + a • x)` obeys the
Lipschitz bound `≤ |e^{2t} - e^{2s}| * (a⁻¹ * (‖K x‖ + ‖P x‖))` and converges to `x`
as `s → t`. -/
theorem positive_vacuum_two_time_shifted_resolvent_package (hk : 0 < k)
    (s t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ threeOperatorDomain ε hε h hh hb m g k) :
    let hxs := (positive_vacuum_three_operator_hamiltonian_eval
      ε hε h hh hb m g k hk s hx.1.1 hx.1.2 hx.2).choose
    ‖x - RH t a (H s ⟨x, hxs⟩ + a • x)‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| *
        (a⁻¹ * (‖K ⟨x, hx.1.2⟩‖ + ‖P ⟨x, hx.2⟩‖)) ∧
    Tendsto (fun s' : ℝ =>
      RH t a (H s' ⟨x, (positive_vacuum_three_operator_hamiltonian_eval
        ε hε h hh hb m g k hk s' hx.1.1 hx.1.2 hx.2).choose⟩ + a • x))
      (𝓝 t) (𝓝 x) :=
  ⟨(positive_vacuum_two_time_shifted_resolvent_hilbert_bound
      ε hε h hh hb m g k hk s t a ha hx.1.1 hx.1.2 hx.2).2,
   positive_vacuum_two_time_shifted_resolvent_tendsto
      ε hε h hh hb m g k hk t a ha hx.1.1 hx.1.2 hx.2⟩

/-- 29. Under `0 < k`, for every `x ∈ threeOperatorDomain = Dom(T) ∩ Dom(K) ∩ Dom(P)`,
the two-time residual shifted resolvent defect `x - RS t a (S s x + a • x)` obeys
the Lipschitz bound `≤ |e^{2t} - e^{2s}| * (a⁻¹ * ‖P x‖)` and converges to `x` as `s → t`. -/
theorem positive_vacuum_two_time_residual_shifted_resolvent_package (hk : 0 < k)
    (s t a : ℝ) (ha : 0 < a) (x : Hilbert)
    (hx : x ∈ threeOperatorDomain ε hε h hh hb m g k) :
    let hxs := (positive_vacuum_three_operator_residual_eval
      ε hε h hh hb m g k hk s hx.1.1 hx.1.2 hx.2).choose
    ‖x - RS t a (S s ⟨x, hxs⟩ + a • x)‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| * (a⁻¹ * ‖P ⟨x, hx.2⟩‖) ∧
    Tendsto (fun s' : ℝ =>
      RS t a (S s' ⟨x, (positive_vacuum_three_operator_residual_eval
        ε hε h hh hb m g k hk s' hx.1.1 hx.1.2 hx.2).choose⟩ + a • x))
      (𝓝 t) (𝓝 x) :=
  ⟨positive_vacuum_two_time_residual_shifted_resolvent_bound
      ε hε h hh hb m g k hk s t a ha hx.1.1 hx.1.2 hx.2,
   positive_vacuum_two_time_residual_shifted_resolvent_tendsto
      ε hε h hh hb m g k hk t a ha hx.1.1 hx.1.2 hx.2⟩

/-- 30. Unconditional weak two-time resolvent Lipschitz bound and continuity
for all `f1, f2 : Hilbert` and `a > 0`. -/
theorem unconditional_two_time_resolvent_weak_package
    (s t a : ℝ) (ha : 0 < a) (f1 f2 : Hilbert) :
    ‖inner ℂ f1 (RH s a f2 - RH t a f2)‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| *
        (2 * Real.exp (-(t + s)) * a⁻¹ * ‖f1‖ * ‖f2‖) ∧
    Tendsto (fun s' : ℝ => inner ℂ f1 (RH s' a f2)) (𝓝 t) (𝓝 (inner ℂ f1 (RH t a f2))) :=
  ⟨two_time_resolvent_weak_diff_bound ε hε h hh hb m g k s t a ha f1 f2,
   two_time_resolvent_weak_continuous ε hε h hh hb m g k t a ha f1 f2⟩

/-- 31. Under `0 < k`, whenever `RH s a f ∈ Dom(P)` (equivalently `∈ Dom(G)` or
`∈ threeOperatorDomain`), the two-time resolvent difference `RH s a f - RH t a f`
satisfies simultaneous Hilbert, `clockHalf`, and `H(t)` Lipschitz bounds. -/
theorem positive_vacuum_two_time_resolvent_difference_bounds_of_potential (hk : 0 < k)
    (s t a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hp : RH s a f ∈ potentialGeneratorDomain ε hε h hh hb m g k) :
    let hG : RH s a f ∈ (G).domain :=
      (KFCausalClockFloorHamiltonianResolventThreeOperatorSynthesis.hamiltonian_resolvent_mem_potential_iff_growing
        ε hε h hh hb m g k s a ha f).mp hp
    let hHt := (KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain.positive_vacuum_two_time_second_resolvent_on_growing_domain
      ε hε h hh hb m g k hk s t a ha f hG).1
    let hdC : RH s a f - RH t a f ∈ (clockHalf ε).domain :=
      (clockHalf ε).domain.sub_mem
        (resolvent_in_clockHalf_domain ε hε h hh hb m g k s a ha f)
        (resolvent_in_clockHalf_domain ε hε h hh hb m g k t a ha f)
    ‖RH s a f - RH t a f‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| * (a⁻¹ * ‖G ⟨RH s a f, hG⟩‖) ∧
    ‖clockHalf ε ⟨RH s a f - RH t a f, hdC⟩‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| *
        (Real.sqrt 2 * Real.sqrt (a⁻¹) * ‖G ⟨RH s a f, hG⟩‖) ∧
    ‖H t ⟨RH s a f, hHt⟩ -
        H t ⟨RH t a f, (KFCausalClockFloorHamiltonianClockCore.resolves
          ε hε h hh hw m g k t a ha f).1⟩‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| * ‖G ⟨RH s a f, hG⟩‖ := by
  let hG : RH s a f ∈ (G).domain :=
    (KFCausalClockFloorHamiltonianResolventThreeOperatorSynthesis.hamiltonian_resolvent_mem_potential_iff_growing
      ε hε h hh hb m g k s a ha f).mp hp
  exact positive_vacuum_two_time_second_resolvent_bounds_on_growing_domain
    ε hε h hh hb m g k hk s t a ha f hG

#print axioms averaged_form_domain_le_potentialDomain
#print axioms residual_form_domain_le_potentialDomain
#print axioms growing_form_domain_le_potentialDomain
#print axioms positive_vacuum_averaged_form_domain_eq_potentialDomain
#print axioms positive_vacuum_averaged_form_domain_time_invariant
#print axioms potentialGeneratorDomain_le_potentialDomain
#print axioms hamiltonian_resolvent_mem_domains
#print axioms growing_resolvent_mem_domains
#print axioms potential_resolvent_mem_domains
#print axioms positive_vacuum_hamiltonian_resolvent_mem_potential_iff
#print axioms positive_vacuum_hamiltonian_resolvent_mem_static_iff
#print axioms positive_vacuum_hamiltonian_resolvent_mem_growing_iff
#print axioms positive_vacuum_residual_resolvent_mem_growing_iff
#print axioms positive_vacuum_hamiltonian_resolvent_six_way_domain_iff
#print axioms all_five_resolvents_preserve_clockHalf_domain
#print axioms hamiltonian_and_residual_resolvent_unconditional_clockHalf_bounds
#print axioms unconditional_potential_growing_second_resolvent_package
#print axioms unconditional_residual_hamiltonian_second_resolvent_package
#print axioms unconditional_residual_hamiltonian_form_and_clockHalf_bounds
#print axioms positive_vacuum_three_operator_left_inverse_cancel
#print axioms positive_vacuum_residual_two_operator_left_inverse_cancel
#print axioms positive_vacuum_hamiltonian_static_shifted_resolvent_defect
#print axioms positive_vacuum_residual_static_shifted_resolvent_defect
#print axioms positive_vacuum_hamiltonian_residual_shifted_resolvent_defect
#print axioms positive_vacuum_hamiltonian_static_shifted_resolvent_defect_norm_le
#print axioms positive_vacuum_residual_static_shifted_resolvent_defect_norm_le
#print axioms positive_vacuum_hamiltonian_residual_shifted_resolvent_defect_norm_le
#print axioms positive_vacuum_two_time_shifted_resolvent_package
#print axioms positive_vacuum_two_time_residual_shifted_resolvent_package
#print axioms unconditional_two_time_resolvent_weak_package
#print axioms positive_vacuum_two_time_resolvent_difference_bounds_of_potential

end
end UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumResolventRegularity
