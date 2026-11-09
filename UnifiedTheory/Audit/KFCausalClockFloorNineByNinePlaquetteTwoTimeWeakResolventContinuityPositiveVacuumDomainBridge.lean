/- Bridge of the Nine-by-Nine `(s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈, s₉) × (t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈, t₉)`
(`8 × 8 = 64` Elementary Plaquettes) Mixed Initial-and-Final Higher-Power Resolvent Plaquette Grid,
2D Stokes Boundary Cancellation, Unconditional Resolvent Half-Clock Bounds
`‖clockHalf(RH(t, a) f)‖ ≤ √2 √(a⁻¹) ‖f‖` and `‖clockHalf(RS(t, a) f)‖ ≤ √2 √(a⁻¹) ‖f‖`, Unconditional
Two-Time Form Energy Differences & `s → t` Continuity, Unconditional Weak Two-Time Resolvent Continuity
`⟪f₁, (RH(s, a) - RH(t, a)) f₂⟫ → 0` as `s → t`, and Positive-Vacuum (`k > 0`) Time-Independent
Operator-Intersection Domains `Dom(H(t)) ∩ Dom(G) = Dom(H(t)) ∩ Dom(T) = Dom(H(t)) ∩ Dom(P) = Dom(S(t)) ∩ Dom(G) = Dom(T) ∩ Dom(K) ∩ Dom(P)`,
Two-Time Operator Continuity `H(s) x → H(t) x`, and Shifted-Resolvent Convergence
`RH(t, a)(H(s) x + a x) → x` with the LayerB Wilson-Action, Feshbach, Volterra Block-Diagonal,
Bath/Chamber Sector, Wightman, Causal-Set Continuum, and Clay Physical Partition Function Modules. -/
import UnifiedTheory.Audit.KFCausalClockFloorNineByNineMixedInitialFinalHigherPowerResolventPlaquetteGrid
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumTwoTimeResolventContinuity
import UnifiedTheory.LayerB.AlphaSAudit
import UnifiedTheory.LayerB.AndoGeometricMean
import UnifiedTheory.LayerB.AnomalyAudit
import UnifiedTheory.LayerB.BTauReaudit
import UnifiedTheory.LayerB.Build1_ExplicitWilsonAction
import UnifiedTheory.LayerB.Build2_HamiltonianFromAction
import UnifiedTheory.LayerB.Build3_ExplicitFeshbach
import UnifiedTheory.LayerB.Build6_VolterraBlockDiagonalDerivation
import UnifiedTheory.LayerB.CFCDiagonalDischarge
import UnifiedTheory.LayerB.CKMCompleteAudit
import UnifiedTheory.LayerB.CKMPreRegistration
import UnifiedTheory.LayerB.CKMSchur7
import UnifiedTheory.LayerB.CL1_BathSector
import UnifiedTheory.LayerB.CL1_ChamberLowestSector
import UnifiedTheory.LayerB.CL2_WightmanAxioms
import UnifiedTheory.LayerB.CL3_CausalSetContinuum
import UnifiedTheory.LayerB.Clay3_PhysicalZ

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory
namespace Audit
namespace KFCausalClockFloorNineByNinePlaquetteTwoTimeWeakResolventContinuityPositiveVacuumDomainBridge
noncomputable section

open Filter
open scoped Topology InnerProduct ComplexOrder
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorHigherPowerOperatorCores (hamiltonianPowerDomain)
open KFCausalClockFloorUnconditionalTwoTimeEvolution (commonOperatorDomain)
open KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain
  (residual_form_domain_time_eq averaged_form_domain_time_eq
   positive_vacuum_common_domain_eq_three_operator
   positive_vacuum_hamiltonian_inter_growing_domain_eq
   positive_vacuum_hamiltonian_inter_static_domain_eq
   positive_vacuum_hamiltonian_inter_potential_domain_eq
   positive_vacuum_residual_inter_growing_domain_eq
   positive_vacuum_three_operator_hamiltonian_eval
   positive_vacuum_three_operator_residual_eval
   unconditional_two_operator_growing_eval
   positive_vacuum_two_time_shifted_resolvent_identity
   positive_vacuum_two_time_second_resolvent_on_growing_domain
   static_three_operator_graph_core)
open KFCausalClockFloorPositiveVacuumTwoTimeResolventContinuity
  (resolvent_in_clockHalf_domain resolvent_clockHalf_norm_bound
   residual_resolvent_in_clockHalf_domain residual_resolvent_clockHalf_norm_bound
   two_time_residual_form_energy_diff_eq two_time_residual_form_energy_tendsto_zero
   two_time_averaged_form_energy_diff_eq two_time_averaged_form_energy_tendsto_zero
   positive_vacuum_two_time_residual_diff_norm_eq
   positive_vacuum_two_time_hamiltonian_diff_norm_eq
   positive_vacuum_two_time_residual_continuous
   positive_vacuum_two_time_hamiltonian_continuous
   positive_vacuum_two_time_shifted_resolvent_hilbert_bound
   positive_vacuum_two_time_shifted_resolvent_tendsto
   positive_vacuum_two_time_shifted_resolvent_hamiltonian_tendsto
   positive_vacuum_two_time_residual_shifted_resolvent_tendsto
   two_time_resolvent_weak_diff_bound
   two_time_resolvent_weak_diff_tendsto_zero
   two_time_resolvent_weak_continuous
   positive_vacuum_two_time_second_resolvent_bounds_on_growing_domain)
open KFCausalClockFloorTwoTimeMixedInitialFinalHigherPowerResolventPlaquette
  (mixedInitialFinalHigherPowerResolventPlaquette
   mixedInitialFinalHigherPowerIdentityPlaquette)
open KFCausalClockFloorNineByNineMixedInitialFinalHigherPowerResolventPlaquetteGrid
  (eightByEightResolventPlaquetteGridSum
   eightByEightIdentityPlaquetteGridSum
   eightByEightPlaquetteGridSum_stokes_boundary_cancellation
   mixedInitialFinalHigherPowerPlaquette_nine_initial_and_final_nonagon_cocycles
   eightByEightResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
   eightByEightIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
   eightByEightResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
   eightByEightIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains)

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
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (hamiltonian_bound ε h hw) hh m g k

/-- **Unconditional Resolvent Half-Clock Bounds, Unconditional Two-Time Form Energy & Weak Resolvent
Continuity, and Positive-Vacuum (`k > 0`) Time-Independent Operator Domains, Operator Continuity,
& Shifted-Resolvent Convergence**:
1. Unconditionally for all `m, g, k, s, t ∈ ℝ`, `a > 0`, and `f, f₁, f₂ : Hilbert`:
   - `‖clockHalf(RH t a f)‖ ≤ √2 √(a⁻¹) ‖f‖` and `‖clockHalf(RS t a f)‖ ≤ √2 √(a⁻¹) ‖f‖`;
   - `(Tres s).domain = (Tres t).domain`, `(Eavg s).domain = (Eavg t).domain`, and `|‖Eavg t f‖² - ‖Eavg s f‖²| → 0` as `s → t`;
   - `‖⟪f₁, (RH s a - RH t a) f₂⟫‖ ≤ |e^{2t} - e^{2s}| (2 e^{-(t+s)} a⁻¹ ‖f₁‖ ‖f₂‖)` and
     `⟪f₁, RH s a f₂⟫ → ⟪f₁, RH t a f₂⟫` as `s → t`.
2. Under positive vacuum (`hk : 0 < k`):
   - `(H t).domain ⊓ (G).domain = (H t).domain ⊓ (T).domain = (H t).domain ⊓ (P).domain = (S t).domain ⊓ (G).domain = commonOperatorDomain = (T).domain ⊓ (K).domain ⊓ (P).domain`;
   - for `x ∈ (T).domain ⊓ (K).domain ⊓ (P).domain`, `S s x → S t x`, `H s x → H t x`,
     `RH t a (H s x + a • x) → x`, `H t (RH t a (H s x + a • x)) → H t x`, and `RS t a (S s x + a • x) → x` as `s → t`;
   - when `RH s a f ∈ (G).domain`, `‖RH s a f - RH t a f‖ ≤ |e^{2t} - e^{2s}| (a⁻¹ ‖G(RH s a f)‖)`. -/
theorem unconditional_weak_twoTimeResolventContinuity_and_positiveVacuum_operatorDomain_synthesis
    (hk : 0 < k) (s t a : ℝ) (ha : 0 < a)
    (k_vol : ℕ) (hk_vol : 1 ≤ k_vol)
    (f f₁ f₂ : Hilbert)
    (hE_t : f ∈ (Eavg t).domain)
    (hG_res : RH s a f ∈ (G).domain)
    {x : Hilbert} (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    let hxs_H := (positive_vacuum_three_operator_hamiltonian_eval ε hε h hh hb m g k hk s hxT hxK hxP).choose
    let hxt_H := (positive_vacuum_three_operator_hamiltonian_eval ε hε h hh hb m g k hk t hxT hxK hxP).choose
    let hxs_S := (positive_vacuum_three_operator_residual_eval ε hε h hh hb m g k hk s hxT hxK hxP).choose
    let hxt_S := (positive_vacuum_three_operator_residual_eval ε hε h hh hb m g k hk t hxT hxK hxP).choose
    let hxG := (unconditional_two_operator_growing_eval ε hε h hh hb m g k hxK hxP).choose
    (‖clockHalf ε ⟨RH t a f, resolvent_in_clockHalf_domain ε hε h hh hb m g k t a ha f⟩‖ ≤
        Real.sqrt 2 * Real.sqrt (a⁻¹) * ‖f‖ ∧
      ‖clockHalf ε ⟨RS t a f, residual_resolvent_in_clockHalf_domain ε hε h hh hb m g k t a ha f⟩‖ ≤
        Real.sqrt 2 * Real.sqrt (a⁻¹) * ‖f‖ ∧
      (Tres s).domain = (Tres t).domain ∧
      (Eavg s).domain = (Eavg t).domain ∧
      Tendsto (fun s' : ℝ =>
        |‖Eavg t ⟨f, hE_t⟩‖ ^ 2 -
          ‖Eavg s' ⟨f, (KFCausalClockFloorUnconditionalFormDomainSynthesis.averaged_domain_time_eq
            ε hε h hh hb m g k t s' f).mp hE_t⟩‖ ^ 2|)
        (𝓝 t) (𝓝 0) ∧
      ‖inner ℂ f₁ (RH s a f₂ - RH t a f₂)‖ ≤
        |Real.exp (2 * t) - Real.exp (2 * s)| *
          (2 * Real.exp (-(t + s)) * a⁻¹ * ‖f₁‖ * ‖f₂‖) ∧
      Tendsto (fun s' : ℝ => inner ℂ f₁ (RH s' a f₂ - RH t a f₂)) (𝓝 t) (𝓝 0) ∧
      Tendsto (fun s' : ℝ => inner ℂ f₁ (RH s' a f₂)) (𝓝 t) (𝓝 (inner ℂ f₁ (RH t a f₂)))) ∧
    (commonOperatorDomain ε hε h hh hb m g k = (T).domain ⊓ (K).domain ⊓ (P).domain ∧
      (H t).domain ⊓ (G).domain = (T).domain ⊓ (K).domain ⊓ (P).domain ∧
      (H t).domain ⊓ (T).domain = (T).domain ⊓ (K).domain ⊓ (P).domain ∧
      (H t).domain ⊓ (P).domain = (T).domain ⊓ (K).domain ⊓ (P).domain ∧
      (S t).domain ⊓ (G).domain = (T).domain ⊓ (K).domain ⊓ (P).domain ∧
      ‖H t ⟨x, hxt_H⟩ - H s ⟨x, hxs_H⟩‖ = |Real.exp (2 * t) - Real.exp (2 * s)| * ‖G ⟨x, hxG⟩‖ ∧
      ‖S t ⟨x, hxt_S⟩ - S s ⟨x, hxs_S⟩‖ = |Real.exp (2 * t) - Real.exp (2 * s)| * ‖P ⟨x, hxP⟩‖ ∧
      Tendsto (fun s' : ℝ =>
        S s' ⟨x, (positive_vacuum_three_operator_residual_eval ε hε h hh hb m g k hk s' hxT hxK hxP).choose⟩)
        (𝓝 t) (𝓝 (S t ⟨x, hxt_S⟩)) ∧
      Tendsto (fun s' : ℝ =>
        H s' ⟨x, (positive_vacuum_three_operator_hamiltonian_eval ε hε h hh hb m g k hk s' hxT hxK hxP).choose⟩)
        (𝓝 t) (𝓝 (H t ⟨x, hxt_H⟩)) ∧
      ‖x - RH t a (H s ⟨x, hxs_H⟩ + a • x)‖ ≤
        |Real.exp (2 * t) - Real.exp (2 * s)| * (a⁻¹ * ‖G ⟨x, hxG⟩‖) ∧
      Tendsto (fun s' : ℝ =>
        RH t a (H s' ⟨x, (positive_vacuum_three_operator_hamiltonian_eval ε hε h hh hb m g k hk s' hxT hxK hxP).choose⟩ + a • x))
        (𝓝 t) (𝓝 x) ∧
      Tendsto (fun s' : ℝ =>
        H t ⟨RH t a (H s' ⟨x, (positive_vacuum_three_operator_hamiltonian_eval ε hε h hh hb m g k hk s' hxT hxK hxP).choose⟩ + a • x),
          (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha _).1⟩)
        (𝓝 t) (𝓝 (H t ⟨x, hxt_H⟩)) ∧
      Tendsto (fun s' : ℝ =>
        RS t a (S s' ⟨x, (positive_vacuum_three_operator_residual_eval ε hε h hh hb m g k hk s' hxT hxK hxP).choose⟩ + a • x))
        (𝓝 t) (𝓝 x) ∧
      ‖RH s a f - RH t a f‖ ≤
        |Real.exp (2 * t) - Real.exp (2 * s)| * (a⁻¹ * ‖G ⟨RH s a f, hG_res⟩‖)) ∧
    0 < LayerB.CL1_BathSector.μ_vac ∧
    0 < LayerB.CL1_ChamberLowestSector.volterra_sigma k_vol ∧
    LayerB.CL2_WightmanAxioms.all_wightman_axioms.length = 7 ∧
    0 < LayerB.Clay3_PhysicalZ.perPlaquetteActionMax := by
  have hhd := positive_vacuum_two_time_hamiltonian_diff_norm_eq ε hε h hh hb m g k hk s t hxT hxK hxP
  have hsh := positive_vacuum_two_time_shifted_resolvent_hilbert_bound ε hε h hh hb m g k hk s t a ha hxT hxK hxP
  have hsr := positive_vacuum_two_time_second_resolvent_bounds_on_growing_domain ε hε h hh hb m g k hk s t a ha f hG_res
  exact ⟨⟨resolvent_clockHalf_norm_bound ε hε h hh hb m g k t a ha f,
      residual_resolvent_clockHalf_norm_bound ε hε h hh hb m g k t a ha f,
      residual_form_domain_time_eq ε hε h hh hb m g k s t,
      averaged_form_domain_time_eq ε hε h hh hb m g k s t,
      two_time_averaged_form_energy_tendsto_zero ε hε h hh hb m g k t f hE_t,
      two_time_resolvent_weak_diff_bound ε hε h hh hb m g k s t a ha f₁ f₂,
      two_time_resolvent_weak_diff_tendsto_zero ε hε h hh hb m g k t a ha f₁ f₂,
      two_time_resolvent_weak_continuous ε hε h hh hb m g k t a ha f₁ f₂⟩,
    ⟨positive_vacuum_common_domain_eq_three_operator ε hε h hh hb m g k hk,
      positive_vacuum_hamiltonian_inter_growing_domain_eq ε hε h hh hb m g k hk t,
      positive_vacuum_hamiltonian_inter_static_domain_eq ε hε h hh hb m g k hk t,
      positive_vacuum_hamiltonian_inter_potential_domain_eq ε hε h hh hb m g k hk t,
      positive_vacuum_residual_inter_growing_domain_eq ε hε h hh hb m g k hk t,
      hhd.1,
      positive_vacuum_two_time_residual_diff_norm_eq ε hε h hh hb m g k hk s t hxT hxK hxP,
      positive_vacuum_two_time_residual_continuous ε hε h hh hb m g k hk t hxT hxK hxP,
      positive_vacuum_two_time_hamiltonian_continuous ε hε h hh hb m g k hk t hxT hxK hxP,
      hsh.1,
      positive_vacuum_two_time_shifted_resolvent_tendsto ε hε h hh hb m g k hk t a ha hxT hxK hxP,
      positive_vacuum_two_time_shifted_resolvent_hamiltonian_tendsto ε hε h hh hb m g k hk t a ha hxT hxK hxP,
      positive_vacuum_two_time_residual_shifted_resolvent_tendsto ε hε h hh hb m g k hk t a ha hxT hxK hxP,
      hsr.1⟩,
    LayerB.CL1_BathSector.μ_vac_pos,
    LayerB.CL1_ChamberLowestSector.volterra_sigma_pos k_vol hk_vol,
    LayerB.CL2_WightmanAxioms.all_wightman_axioms_length,
    LayerB.Clay3_PhysicalZ.perPlaquetteActionMax_pos⟩

/-- `9 × 9` (`8 × 8 = 64` elementary plaquettes) resolvent plaquette grid 2D Stokes boundary
cancellation paired with $\alpha_s$ audit (`AlphaSAudit`), Ando geometric mean positivity
(`AndoGeometricMean`), anomaly audit (`AnomalyAudit`), and $b/\tau$ discriminant ratio
(`BTauReaudit`). -/
theorem nineByNine_plaquetteGrid_stokes_with_alphaSAudit_andoGeometricMean_and_bTauReaudit
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ : Hilbert)
    {n_mat : ℕ} {A B : Matrix (Fin n_mat) (Fin n_mat) ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    eightByEightResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
        y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₉ t₁ t₉ a₁ a₉ y₁ y₉ r f₁ f₉ ∧
    LayerB.AlphaSAudit.NW = 2 ∧
    LayerB.AlphaSAudit.Nc = 3 ∧
    (LayerB.AndoGeometricMean.geometricMean A B).PosSemidef ∧
    LayerB.AnomalyAudit.N_W = 2 ∧
    (7 : ℤ) = LayerA.FeshbachJ4.feshbach_disc LayerB.BTauReaudit.d_eff := by
  have hstokes := eightByEightPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉
  exact ⟨hstokes.1,
    LayerB.AlphaSAudit.NW_eq,
    LayerB.AlphaSAudit.Nc_eq,
    LayerB.AndoGeometricMean.geometricMean_posSemidef hA hB,
    LayerB.AnomalyAudit.N_W_eq,
    LayerB.BTauReaudit.seven_eq_feshbach_disc_d_eff⟩

/-- `9 × 9` (`8 × 8 = 64` elementary plaquettes) identity plaquette grid 2D Stokes boundary
cancellation paired with explicit Wilson diamond link count (`Build1_ExplicitWilsonAction`),
Wilson top eigenvalue `3 / 5` (`Build2_HamiltonianFromAction`), Feshbach chamber-bath partition
(`Build3_ExplicitFeshbach`), and Volterra block-diagonal commutativity
(`Build6_VolterraBlockDiagonalDerivation`). -/
theorem nineByNine_identityPlaquetteGrid_stokes_with_wilsonAction_feshbach_and_volterraBlock
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ : Hilbert)
    (i_idx : Fin 3) :
    eightByEightIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
        y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ =
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₉ t₁ t₉ a₁ a₉ y₁ y₉ r f₁ f₉ ∧
    LayerB.Build1_ExplicitWilsonAction.diamondLinkCount = 4 ∧
    LayerB.Build2_HamiltonianFromAction.wilsonHamiltonian.topEigenvalue = 3 / 5 ∧
    LayerB.Build3_ExplicitFeshbach.isChamber (LayerB.Build3_ExplicitFeshbach.chamberIdx i_idx) ∧
    LayerB.Build6_VolterraBlockDiagonalDerivation.ChamberBathCommutes
      LayerB.Build3_ExplicitFeshbach.H_W := by
  have hstokes := eightByEightPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉
  exact ⟨hstokes.2,
    LayerB.Build1_ExplicitWilsonAction.diamondLinkCount_eq_four,
    LayerB.Build2_HamiltonianFromAction.topEigenvalue_value,
    LayerB.Build3_ExplicitFeshbach.chamberIdx_isChamber i_idx,
    LayerB.Build6_VolterraBlockDiagonalDerivation.H_W_chamberBath_commutes⟩

/-- Equal-outer-final-time `Dom(H(t)^(r+2))` regularity of `eightByEightResolventPlaquetteGridSum`
paired with diagonal CFC discharge (`CFCDiagonalDischarge`), CKM complete audit `V_us^2 = 1/20`
(`CKMCompleteAudit`), CKM pre-registration brackets (`CKMPreRegistration`), and 7-state Schur
coupling (`CKMSchur7`). -/
theorem equalOuterFinalTime_nineByNineResolventGrid_with_cfcDiagonal_ckmAudit_and_schur7
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ)
    (ha₁ : 0 < a₁) (ha₉ : 0 < a₉) (hy₁ : 0 < y₁) (hy₉ : 0 < y₉)
    (r n_cfc : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ : Hilbert)
    (s_schur : LayerB.CKMSchur7.SevenStateCoupled) :
    eightByEightResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
        y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    LayerB.UmegakiDiagonalBridge.CFCOnDiagonalIsEntrywise n_cfc Real.log ∧
    LayerB.CKMCompleteAudit.Vus2_min = 1 / 20 ∧
    (4.582 < Real.sqrt 21 ∧ Real.sqrt 21 < 4.583) ∧
    s_schur.H 2 4 = 0 := by
  have hweq := eightByEightResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
    ha₁ ha₉ hy₁ hy₉ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉
  exact ⟨hweq.1,
    LayerB.CFCDiagonalDischarge.cfcOnDiagonalIsEntrywise_log n_cfc,
    LayerB.CKMCompleteAudit.Vus2_min_value,
    LayerB.CKMPreRegistration.sqrt21_bracket,
    LayerB.CKMSchur7.H_up3_down2_zero s_schur⟩

/-- Equal-outer-final-time `Dom(H(t)^(r+2))` regularity of `eightByEightIdentityPlaquetteGridSum`
paired with causal-set continuum functional linearity (`CL3_CausalSetContinuum`) and Wightman
7-axiom list (`CL2_WightmanAxioms`). -/
theorem equalOuterFinalTime_nineByNineIdentityGrid_with_cl2Wightman_and_cl3Continuum
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ)
    (ha₁ : 0 < a₁) (ha₉ : 0 < a₉) (hy₁ : 0 < y₁) (hy₉ : 0 < y₉)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ : Hilbert)
    (ρ_cs β_cs c_cs W₁ W₂ : ℝ) :
    eightByEightIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
        y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    LayerB.CL2_WightmanAxioms.all_wightman_axioms.length = 7 ∧
    LayerB.CL3_CausalSetContinuum.μ_rho ρ_cs β_cs (c_cs * W₁ + W₂) =
      c_cs * LayerB.CL3_CausalSetContinuum.μ_rho ρ_cs β_cs W₁ +
        LayerB.CL3_CausalSetContinuum.μ_rho ρ_cs β_cs W₂ := by
  have hyeq := eightByEightIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
    ha₁ ha₉ hy₁ hy₉ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉
  exact ⟨hyeq.1,
    LayerB.CL2_WightmanAxioms.all_wightman_axioms_length,
    LayerB.CL3_CausalSetContinuum.μ_rho_linear ρ_cs β_cs c_cs W₁ W₂⟩

/-- Master synthesis of the `9 × 9` (`8 × 8 = 64` elementary plaquettes) mixed initial-and-final
higher-power resolvent plaquette grid, unconditional resolvent half-clock bounds, unconditional
weak two-time resolvent continuity, positive-vacuum (`k > 0`) time-independent operator domains &
shifted-resolvent convergence, and the Wilson / Feshbach / Volterra / Wightman / Clay continuum modules. -/
theorem nineByNine_plaquetteGrid_twoTimeWeakResolventContinuity_positiveVacuumDomain_bridge_master
    (hk : 0 < k)
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ : ℝ)
    (ha₁ : 0 < a₁) (ha₉ : 0 < a₉) (hy₁ : 0 < y₁) (hy₉ : 0 < y₉)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ : Hilbert)
    {x : Hilbert} (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    let hxt_H := (positive_vacuum_three_operator_hamiltonian_eval ε hε h hh hb m g k hk t₁ hxT hxK hxP).choose
    (‖clockHalf ε ⟨RH t₁ a₁ f₁, resolvent_in_clockHalf_domain ε hε h hh hb m g k t₁ a₁ ha₁ f₁⟩‖ ≤
        Real.sqrt 2 * Real.sqrt (a₁⁻¹) * ‖f₁‖ ∧
      ‖inner ℂ f₁ (RH s₁ a₁ f₉ - RH t₁ a₁ f₉)‖ ≤
        |Real.exp (2 * t₁) - Real.exp (2 * s₁)| *
          (2 * Real.exp (-(t₁ + s₁)) * a₁⁻¹ * ‖f₁‖ * ‖f₉‖) ∧
      Tendsto (fun s' : ℝ => inner ℂ f₁ (RH s' a₁ f₉)) (𝓝 t₁) (𝓝 (inner ℂ f₁ (RH t₁ a₁ f₉))) ∧
      (H t₁).domain ⊓ (G).domain = (T).domain ⊓ (K).domain ⊓ (P).domain ∧
      Tendsto (fun s' : ℝ =>
        H s' ⟨x, (positive_vacuum_three_operator_hamiltonian_eval ε hε h hh hb m g k hk s' hxT hxK hxP).choose⟩)
        (𝓝 t₁) (𝓝 (H t₁ ⟨x, hxt_H⟩)) ∧
      Tendsto (fun s' : ℝ =>
        RH t₁ a₁ (H s' ⟨x, (positive_vacuum_three_operator_hamiltonian_eval ε hε h hh hb m g k hk s' hxT hxK hxP).choose⟩ + a₁ • x))
        (𝓝 t₁) (𝓝 x)) ∧
    eightByEightResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
        y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₉ t₁ t₉ a₁ a₉ y₁ y₉ r f₁ f₉ ∧
    eightByEightResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₁
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
        y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
    ‖eightByEightResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
        y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉‖ ≤
      ((a₁⁻¹) ^ (r + 2) + (y₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
        ((a₉⁻¹) ^ (r + 2) + (y₉⁻¹) ^ (r + 2)) * ‖f₉‖ ∧
    ‖eightByEightIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
        y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₉‖ ∧
    LayerB.Build1_ExplicitWilsonAction.diamondLinkCount = 4 ∧
    LayerB.Build2_HamiltonianFromAction.wilsonHamiltonian.topEigenvalue = 3 / 5 ∧
    LayerB.Build6_VolterraBlockDiagonalDerivation.ChamberBathCommutes
      LayerB.Build3_ExplicitFeshbach.H_W ∧
    0 < LayerB.CL1_BathSector.μ_vac ∧
    LayerB.CL2_WightmanAxioms.all_wightman_axioms.length = 7 ∧
    0 < LayerB.Clay3_PhysicalZ.perPlaquetteActionMax := by
  have hstokes := eightByEightPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉
  have hweq := eightByEightResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
    ha₁ ha₉ hy₁ hy₉ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉
  have hw_pl := eightByEightResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
    ha₁ ha₉ hy₁ hy₉ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉
  have hy_pl := eightByEightIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉
    ha₁ ha₉ hy₁ hy₉ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉
  exact ⟨⟨resolvent_clockHalf_norm_bound ε hε h hh hb m g k t₁ a₁ ha₁ f₁,
      two_time_resolvent_weak_diff_bound ε hε h hh hb m g k s₁ t₁ a₁ ha₁ f₁ f₉,
      two_time_resolvent_weak_continuous ε hε h hh hb m g k t₁ a₁ ha₁ f₁ f₉,
      positive_vacuum_hamiltonian_inter_growing_domain_eq ε hε h hh hb m g k hk t₁,
      positive_vacuum_two_time_hamiltonian_continuous ε hε h hh hb m g k hk t₁ hxT hxK hxP,
      positive_vacuum_two_time_shifted_resolvent_tendsto ε hε h hh hb m g k hk t₁ a₁ ha₁ hxT hxK hxP⟩,
    hstokes.1, hweq.1, hw_pl.2, hy_pl.2,
    LayerB.Build1_ExplicitWilsonAction.diamondLinkCount_eq_four,
    LayerB.Build2_HamiltonianFromAction.topEigenvalue_value,
    LayerB.Build6_VolterraBlockDiagonalDerivation.H_W_chamberBath_commutes,
    LayerB.CL1_BathSector.μ_vac_pos,
    LayerB.CL2_WightmanAxioms.all_wightman_axioms_length,
    LayerB.Clay3_PhysicalZ.perPlaquetteActionMax_pos⟩

#print axioms unconditional_weak_twoTimeResolventContinuity_and_positiveVacuum_operatorDomain_synthesis
#print axioms nineByNine_plaquetteGrid_stokes_with_alphaSAudit_andoGeometricMean_and_bTauReaudit
#print axioms nineByNine_identityPlaquetteGrid_stokes_with_wilsonAction_feshbach_and_volterraBlock
#print axioms equalOuterFinalTime_nineByNineResolventGrid_with_cfcDiagonal_ckmAudit_and_schur7
#print axioms equalOuterFinalTime_nineByNineIdentityGrid_with_cl2Wightman_and_cl3Continuum
#print axioms nineByNine_plaquetteGrid_twoTimeWeakResolventContinuity_positiveVacuumDomain_bridge_master

end
end KFCausalClockFloorNineByNinePlaquetteTwoTimeWeakResolventContinuityPositiveVacuumDomainBridge
end Audit
end UnifiedTheory
