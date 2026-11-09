/- Bridge of the Eight-by-Eight `(s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈) × (t₁, t₂, t₃, t₄, t₅, t₆, t₇, t₈)`
(`7 × 7 = 49` Elementary Plaquettes) Mixed Initial-and-Final Higher-Power Resolvent Plaquette Grid,
2D Stokes Boundary Cancellation, Exact Static-Residual Second Resolvent Identity
`R_T(a) f - R_{S(t)}(a) f = e^{2t} R_T(a) (P (R_{S(t)}(a) f))`, Potential-Residual Zero-Time Identity
`R_P(a) f - R_{S(0)}(a) f = R_P(a) (T (R_{S(0)}(a) f))`, and Continuous Linear Two-Time Form-Space
Evolution Isomorphism `twoTimeFormEvolutionEquiv s t` with Two-Sided Exponential Form-Energy Bounds
`e^{-2|t-s|} ‖Eavg s f‖² ≤ ‖Eavg t (U s t f)‖² ≤ e^{2|t-s|} ‖Eavg s f‖²` and the LayerB Wilson-Action,
Feshbach, Volterra Block-Diagonal, Bath/Chamber Sector, Wightman, Causal-Set Continuum, and Clay
Physical Partition Function Modules. -/
import UnifiedTheory.Audit.KFCausalClockFloorEightByEightMixedInitialFinalHigherPowerResolventPlaquetteGrid
import UnifiedTheory.Audit.KFCausalClockFloorStaticResidualSecondResolventIdentity
import UnifiedTheory.Audit.KFCausalClockFloorTwoTimeFormEvolutionIsomorphism
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

set_option autoImplicit false

namespace UnifiedTheory
namespace Audit
namespace KFCausalClockFloorEightByEightPlaquetteStaticResidualSecondResolventTwoTimeFormIsomorphismBridge
noncomputable section

open scoped ComplexOrder
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorHigherPowerOperatorCores (hamiltonianPowerDomain)
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding)
open KFCausalClockFloorAveragedEvolution (evolution)
open KFCausalClockFloorStaticResidualSecondResolventIdentity
  (static_resolvent_mem_static_domain
   residual_resolvent_mem_static_of_potential
   static_sub_residual_resolvent_eq
   static_sub_residual_resolvent_norm_le_potential
   static_action_diff_norm_le_potential
   static_sub_residual_resolvent_mem_staticRoot_domain
   static_sub_residual_resolvent_staticRoot_norm_sq_le_potential
   static_sub_residual_resolvent_mem_clockHalf_domain
   static_sub_residual_resolvent_clockHalf_norm_sq_le_potential
   potential_sub_residual_zero_resolvent_eq)
open KFCausalClockFloorTwoTimeFormEvolutionIsomorphism
  (twoTimeFormEvolution
   twoTimeFormEvolutionEquiv
   twoTimeFormEvolutionEquiv_embedding
   twoTimeFormEvolution_two_sided_norm_sq_bounds
   mem_averaged_domain_of_evolved
   evolved_mem_averaged_domain_iff
   evolved_operator_form_energy_bounds)
open KFCausalClockFloorTwoTimeMixedInitialFinalHigherPowerResolventPlaquette
  (mixedInitialFinalHigherPowerResolventPlaquette
   mixedInitialFinalHigherPowerIdentityPlaquette)
open KFCausalClockFloorEightByEightMixedInitialFinalHigherPowerResolventPlaquetteGrid
  (sevenBySevenResolventPlaquetteGridSum
   sevenBySevenIdentityPlaquetteGridSum
   sevenBySevenPlaquetteGridSum_stokes_boundary_cancellation
   mixedInitialFinalHigherPowerPlaquette_eight_initial_and_final_octagon_cocycles
   sevenBySevenResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
   sevenBySevenIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
   sevenBySevenResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
   sevenBySevenIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RT" => KFCausalClockFloorStaticClockCore.resolvent ε hε h hh hw m g k 0
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m g k
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "VT" => FormSpace ε hε h hh hw m g k
local notation "AJ" => embedding ε hε h hh hw m g k
local notation "U" => evolution ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (hamiltonian_bound ε h hw) hh m g k

/-- **Exact Static-Residual Second Resolvent Identity, Potential-Residual Zero-Time Identity, and
Two-Time Completed Energy-Form Evolution Isomorphism with Two-Sided Exponential Form-Energy Bounds**:
For all real parameters `m, g, k, t, s, r_obs ∈ ℝ`, every shift `a > 0`, every `f : Hilbert` with
`hp : RS t a f ∈ (P).domain`, every `f₀ : Hilbert` with `ht₀ : RS 0 a f₀ ∈ (T).domain`, every form
vector `u : VT s`, and every initial form-domain state `f_ev ∈ (Eavg s).domain`:
1. `RT a f - RS t a f = (Real.exp (2 * t) : ℂ) • RT a (P ⟨RS t a f, hp⟩)` with Hilbert, static-operator,
   static-root `Tstat`, and `clockHalf ε` norm bounds;
2. `RP a f₀ - RS 0 a f₀ = RP a (T ⟨RS 0 a f₀, ht₀⟩)`;
3. `twoTimeFormEvolutionEquiv s t : VT s ≃L[ℂ] VT t` intertwines `AJ s` and `AJ t` with `U s t` and
   satisfies `e^{-2|t-s|} ‖u‖² ≤ ‖twoTimeFormEvolution s t u‖² ≤ e^{2|t-s|} ‖u‖²`;
4. `U s t f_ev ∈ (Eavg r_obs).domain ↔ f_ev ∈ (Eavg s).domain`, and
   `e^{-2|t-s|} ‖Eavg s f_ev‖² ≤ ‖Eavg t (U s t f_ev)‖² ≤ e^{2|t-s|} ‖Eavg s f_ev‖²`. -/
theorem staticResidual_secondResolvent_and_twoTimeFormEvolutionIsomorphism_with_wightman_clay
    (t s r_obs a : ℝ) (ha : 0 < a)
    (k_vol : ℕ) (hk_vol : 1 ≤ k_vol)
    (f : Hilbert) (hp : RS t a f ∈ (P).domain)
    (f₀ : Hilbert) (ht₀ : RS 0 a f₀ ∈ (T).domain)
    (u : VT s)
    (f_ev : Hilbert) (hf_ev : f_ev ∈ (Eavg s).domain) :
    (RT a f - RS t a f = (Real.exp (2 * t) : ℂ) • RT a (P ⟨RS t a f, hp⟩) ∧
      ‖RT a f - RS t a f‖ ≤ a⁻¹ * Real.exp (2 * t) * ‖P ⟨RS t a f, hp⟩‖ ∧
      ‖T ⟨RT a f, static_resolvent_mem_static_domain ε hε h hh hb m g k a ha f⟩ -
        T ⟨RS t a f, residual_resolvent_mem_static_of_potential ε hε h hh hb m g k t a ha f hp⟩‖ ≤
        Real.exp (2 * t) * ‖P ⟨RS t a f, hp⟩‖ ∧
      ‖Tstat ⟨RT a f - RS t a f,
        static_sub_residual_resolvent_mem_staticRoot_domain ε hε h hh hb m g k t a ha f hp⟩‖ ^ 2 ≤
        a⁻¹ * Real.exp (4 * t) * ‖P ⟨RS t a f, hp⟩‖ ^ 2 ∧
      ‖clockHalf ε ⟨RT a f - RS t a f,
        static_sub_residual_resolvent_mem_clockHalf_domain ε hε h hh hb m g k t a ha f hp⟩‖ ^ 2 ≤
        2 * a⁻¹ * Real.exp (4 * t) * ‖P ⟨RS t a f, hp⟩‖ ^ 2 ∧
      RP a f₀ - RS 0 a f₀ = RP a (T ⟨RS 0 a f₀, ht₀⟩)) ∧
    (AJ t (twoTimeFormEvolutionEquiv ε hε h hh hb m g k s t u) = U s t (AJ s u) ∧
      Real.exp (-2 * |t - s|) * ‖u‖ ^ 2 ≤
        ‖twoTimeFormEvolution ε hε h hh hb m g k s t u‖ ^ 2 ∧
      ‖twoTimeFormEvolution ε hε h hh hb m g k s t u‖ ^ 2 ≤
        Real.exp (2 * |t - s|) * ‖u‖ ^ 2 ∧
      (U s t f_ev ∈ (Eavg r_obs).domain ↔ f_ev ∈ (Eavg s).domain) ∧
      Real.exp (-2 * |t - s|) * ‖Eavg s ⟨f_ev, hf_ev⟩‖ ^ 2 ≤
        ‖Eavg t ⟨U s t f_ev, mem_averaged_domain_of_evolved ε hε h hh hb m g k s t t hf_ev⟩‖ ^ 2 ∧
      ‖Eavg t ⟨U s t f_ev, mem_averaged_domain_of_evolved ε hε h hh hb m g k s t t hf_ev⟩‖ ^ 2 ≤
        Real.exp (2 * |t - s|) * ‖Eavg s ⟨f_ev, hf_ev⟩‖ ^ 2) ∧
    0 < LayerB.CL1_BathSector.μ_vac ∧
    0 < LayerB.CL1_ChamberLowestSector.volterra_sigma k_vol ∧
    LayerB.CL2_WightmanAxioms.all_wightman_axioms.length = 7 ∧
    0 < LayerB.Clay3_PhysicalZ.perPlaquetteActionMax := by
  have h2b := twoTimeFormEvolution_two_sided_norm_sq_bounds ε hε h hh hb m g k s t u
  have heb := evolved_operator_form_energy_bounds ε hε h hh hb m g k s t r_obs hf_ev
  exact ⟨⟨static_sub_residual_resolvent_eq ε hε h hh hb m g k t a ha f hp,
      static_sub_residual_resolvent_norm_le_potential ε hε h hh hb m g k t a ha f hp,
      static_action_diff_norm_le_potential ε hε h hh hb m g k t a ha f hp,
      static_sub_residual_resolvent_staticRoot_norm_sq_le_potential ε hε h hh hb m g k t a ha f hp,
      static_sub_residual_resolvent_clockHalf_norm_sq_le_potential ε hε h hh hb m g k t a ha f hp,
      potential_sub_residual_zero_resolvent_eq ε hε h hh hb m g k a ha f₀ ht₀⟩,
    ⟨twoTimeFormEvolutionEquiv_embedding ε hε h hh hb m g k s t u,
      h2b.1, h2b.2,
      evolved_mem_averaged_domain_iff ε hε h hh hb m g k s t r_obs f_ev,
      heb.1, heb.2.1⟩,
    LayerB.CL1_BathSector.μ_vac_pos,
    LayerB.CL1_ChamberLowestSector.volterra_sigma_pos k_vol hk_vol,
    LayerB.CL2_WightmanAxioms.all_wightman_axioms_length,
    LayerB.Clay3_PhysicalZ.perPlaquetteActionMax_pos⟩

/-- `8 × 8` (`7 × 7 = 49` elementary plaquettes) resolvent plaquette grid 2D Stokes boundary
cancellation paired with $\alpha_s$ audit (`AlphaSAudit`), Ando geometric mean positivity
(`AndoGeometricMean`), anomaly audit (`AnomalyAudit`), and $b/\tau$ discriminant ratio
(`BTauReaudit`). -/
theorem eightByEight_plaquetteGrid_stokes_with_alphaSAudit_andoGeometricMean_and_bTauReaudit
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : Hilbert)
    {n_mat : ℕ} {A B : Matrix (Fin n_mat) (Fin n_mat) ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    sevenBySevenResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₈ t₁ t₈ a₁ a₈ z₁ z₈ r f₁ f₈ ∧
    LayerB.AlphaSAudit.NW = 2 ∧
    LayerB.AlphaSAudit.Nc = 3 ∧
    (LayerB.AndoGeometricMean.geometricMean A B).PosSemidef ∧
    LayerB.AnomalyAudit.N_W = 2 ∧
    (7 : ℤ) = LayerA.FeshbachJ4.feshbach_disc LayerB.BTauReaudit.d_eff := by
  have hstokes := sevenBySevenPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈
  exact ⟨hstokes.1,
    LayerB.AlphaSAudit.NW_eq,
    LayerB.AlphaSAudit.Nc_eq,
    LayerB.AndoGeometricMean.geometricMean_posSemidef hA hB,
    LayerB.AnomalyAudit.N_W_eq,
    LayerB.BTauReaudit.seven_eq_feshbach_disc_d_eff⟩

/-- `8 × 8` (`7 × 7 = 49` elementary plaquettes) identity plaquette grid 2D Stokes boundary
cancellation paired with explicit Wilson diamond link count (`Build1_ExplicitWilsonAction`),
Wilson top eigenvalue `3 / 5` (`Build2_HamiltonianFromAction`), Feshbach chamber-bath partition
(`Build3_ExplicitFeshbach`), and Volterra block-diagonal commutativity
(`Build6_VolterraBlockDiagonalDerivation`). -/
theorem eightByEight_identityPlaquetteGrid_stokes_with_wilsonAction_feshbach_and_volterraBlock
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : Hilbert)
    (i_idx : Fin 3) :
    sevenBySevenIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ =
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₈ t₁ t₈ a₁ a₈ z₁ z₈ r f₁ f₈ ∧
    LayerB.Build1_ExplicitWilsonAction.diamondLinkCount = 4 ∧
    LayerB.Build2_HamiltonianFromAction.wilsonHamiltonian.topEigenvalue = 3 / 5 ∧
    LayerB.Build3_ExplicitFeshbach.isChamber (LayerB.Build3_ExplicitFeshbach.chamberIdx i_idx) ∧
    LayerB.Build6_VolterraBlockDiagonalDerivation.ChamberBathCommutes
      LayerB.Build3_ExplicitFeshbach.H_W := by
  have hstokes := sevenBySevenPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈
  exact ⟨hstokes.2,
    LayerB.Build1_ExplicitWilsonAction.diamondLinkCount_eq_four,
    LayerB.Build2_HamiltonianFromAction.topEigenvalue_value,
    LayerB.Build3_ExplicitFeshbach.chamberIdx_isChamber i_idx,
    LayerB.Build6_VolterraBlockDiagonalDerivation.H_W_chamberBath_commutes⟩

/-- Equal-outer-final-time `Dom(H(t)^(r+2))` regularity of `sevenBySevenResolventPlaquetteGridSum`
paired with diagonal CFC discharge (`CFCDiagonalDischarge`), CKM complete audit `V_us^2 = 1/20`
(`CKMCompleteAudit`), CKM pre-registration brackets (`CKMPreRegistration`), and 7-state Schur
coupling (`CKMSchur7`). -/
theorem equalOuterFinalTime_eightByEightResolventGrid_with_cfcDiagonal_ckmAudit_and_schur7
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t t₂ t₃ t₄ t₅ t₆ t₇ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ : ℝ)
    (ha₁ : 0 < a₁) (ha₈ : 0 < a₈) (hz₁ : 0 < z₁) (hz₈ : 0 < z₈)
    (r n_cfc : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : Hilbert)
    (s_schur : LayerB.CKMSchur7.SevenStateCoupled) :
    sevenBySevenResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t t₂ t₃ t₄ t₅ t₆ t₇ t
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    LayerB.UmegakiDiagonalBridge.CFCOnDiagonalIsEntrywise n_cfc Real.log ∧
    LayerB.CKMCompleteAudit.Vus2_min = 1 / 20 ∧
    (4.582 < Real.sqrt 21 ∧ Real.sqrt 21 < 4.583) ∧
    s_schur.H 2 4 = 0 := by
  have hweq := sevenBySevenResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t t₂ t₃ t₄ t₅ t₆ t₇ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
    ha₁ ha₈ hz₁ hz₈ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈
  exact ⟨hweq.1,
    LayerB.CFCDiagonalDischarge.cfcOnDiagonalIsEntrywise_log n_cfc,
    LayerB.CKMCompleteAudit.Vus2_min_value,
    LayerB.CKMPreRegistration.sqrt21_bracket,
    LayerB.CKMSchur7.H_up3_down2_zero s_schur⟩

/-- Equal-outer-final-time `Dom(H(t)^(r+2))` regularity of `sevenBySevenIdentityPlaquetteGridSum`
paired with causal-set continuum functional linearity (`CL3_CausalSetContinuum`) and Wightman
7-axiom list (`CL2_WightmanAxioms`). -/
theorem equalOuterFinalTime_eightByEightIdentityGrid_with_cl2Wightman_and_cl3Continuum
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t t₂ t₃ t₄ t₅ t₆ t₇ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ : ℝ)
    (ha₁ : 0 < a₁) (ha₈ : 0 < a₈) (hz₁ : 0 < z₁) (hz₈ : 0 < z₈)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : Hilbert)
    (ρ_cs β_cs c_cs W₁ W₂ : ℝ) :
    sevenBySevenIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t t₂ t₃ t₄ t₅ t₆ t₇ t
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    LayerB.CL2_WightmanAxioms.all_wightman_axioms.length = 7 ∧
    LayerB.CL3_CausalSetContinuum.μ_rho ρ_cs β_cs (c_cs * W₁ + W₂) =
      c_cs * LayerB.CL3_CausalSetContinuum.μ_rho ρ_cs β_cs W₁ +
        LayerB.CL3_CausalSetContinuum.μ_rho ρ_cs β_cs W₂ := by
  have hyeq := sevenBySevenIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t t₂ t₃ t₄ t₅ t₆ t₇ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
    ha₁ ha₈ hz₁ hz₈ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈
  exact ⟨hyeq.1,
    LayerB.CL2_WightmanAxioms.all_wightman_axioms_length,
    LayerB.CL3_CausalSetContinuum.μ_rho_linear ρ_cs β_cs c_cs W₁ W₂⟩

/-- Master synthesis of the `8 × 8` (`7 × 7 = 49` elementary plaquettes) mixed initial-and-final
higher-power resolvent plaquette grid, exact static-residual second resolvent identity,
potential-residual zero-time identity, two-time completed energy-form evolution isomorphism with
two-sided exponential form-energy bounds, and the Wilson / Feshbach / Volterra / Wightman / Clay
continuum modules. -/
theorem eightByEight_plaquetteGrid_staticResidualSecondResolvent_twoTimeFormIsomorphism_bridge_master
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ : ℝ)
    (ha₁ : 0 < a₁) (ha₈ : 0 < a₈) (hz₁ : 0 < z₁) (hz₈ : 0 < z₈)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : Hilbert)
    (f : Hilbert) (hp : RS t₁ a₁ f ∈ (P).domain)
    (f₀ : Hilbert) (ht₀ : RS 0 a₁ f₀ ∈ (T).domain)
    (u_form : VT s₁)
    (f_ev : Hilbert) (hf_ev : f_ev ∈ (Eavg s₁).domain) :
    (RT a₁ f - RS t₁ a₁ f = (Real.exp (2 * t₁) : ℂ) • RT a₁ (P ⟨RS t₁ a₁ f, hp⟩) ∧
      RP a₁ f₀ - RS 0 a₁ f₀ = RP a₁ (T ⟨RS 0 a₁ f₀, ht₀⟩) ∧
      AJ t₁ (twoTimeFormEvolutionEquiv ε hε h hh hb m g k s₁ t₁ u_form) = U s₁ t₁ (AJ s₁ u_form) ∧
      Real.exp (-2 * |t₁ - s₁|) * ‖u_form‖ ^ 2 ≤
        ‖twoTimeFormEvolution ε hε h hh hb m g k s₁ t₁ u_form‖ ^ 2 ∧
      ‖twoTimeFormEvolution ε hε h hh hb m g k s₁ t₁ u_form‖ ^ 2 ≤
        Real.exp (2 * |t₁ - s₁|) * ‖u_form‖ ^ 2 ∧
      Real.exp (-2 * |t₁ - s₁|) * ‖Eavg s₁ ⟨f_ev, hf_ev⟩‖ ^ 2 ≤
        ‖Eavg t₁ ⟨U s₁ t₁ f_ev, mem_averaged_domain_of_evolved ε hε h hh hb m g k s₁ t₁ t₁ hf_ev⟩‖ ^ 2 ∧
      ‖Eavg t₁ ⟨U s₁ t₁ f_ev, mem_averaged_domain_of_evolved ε hε h hh hb m g k s₁ t₁ t₁ hf_ev⟩‖ ^ 2 ≤
        Real.exp (2 * |t₁ - s₁|) * ‖Eavg s₁ ⟨f_ev, hf_ev⟩‖ ^ 2) ∧
      sevenBySevenResolventPlaquetteGridSum ε hε h hh hb m g k
          s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
          a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
          c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
          u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
          w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
          r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ =
        mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
          s₁ s₈ t₁ t₈ a₁ a₈ z₁ z₈ r f₁ f₈ ∧
      sevenBySevenResolventPlaquetteGridSum ε hε h hh hb m g k
          s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₁
          a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
          c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
          u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
          w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
          r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ ∈
        hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
      ‖sevenBySevenResolventPlaquetteGridSum ε hε h hh hb m g k
          s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
          a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
          c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
          u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
          w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
          r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈‖ ≤
        ((a₁⁻¹) ^ (r + 2) + (z₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
          ((a₈⁻¹) ^ (r + 2) + (z₈⁻¹) ^ (r + 2)) * ‖f₈‖ ∧
      ‖sevenBySevenIdentityPlaquetteGridSum ε hε h hh hb m g k
          s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
          a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
          c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
          u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
          w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
          r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₈‖ ∧
      LayerB.Build1_ExplicitWilsonAction.diamondLinkCount = 4 ∧
      LayerB.Build2_HamiltonianFromAction.wilsonHamiltonian.topEigenvalue = 3 / 5 ∧
      LayerB.Build6_VolterraBlockDiagonalDerivation.ChamberBathCommutes
        LayerB.Build3_ExplicitFeshbach.H_W ∧
      0 < LayerB.CL1_BathSector.μ_vac ∧
      LayerB.CL2_WightmanAxioms.all_wightman_axioms.length = 7 ∧
      0 < LayerB.Clay3_PhysicalZ.perPlaquetteActionMax := by
  have hstokes := sevenBySevenPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈
  have hweq := sevenBySevenResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
    ha₁ ha₈ hz₁ hz₈ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈
  have hw_pl := sevenBySevenResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
    ha₁ ha₈ hz₁ hz₈ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈
  have hy_pl := sevenBySevenIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈
    ha₁ ha₈ hz₁ hz₈ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈
  have h2b := twoTimeFormEvolution_two_sided_norm_sq_bounds ε hε h hh hb m g k s₁ t₁ u_form
  have heb := evolved_operator_form_energy_bounds ε hε h hh hb m g k s₁ t₁ q hf_ev
  exact ⟨⟨static_sub_residual_resolvent_eq ε hε h hh hb m g k t₁ a₁ ha₁ f hp,
      potential_sub_residual_zero_resolvent_eq ε hε h hh hb m g k a₁ ha₁ f₀ ht₀,
      twoTimeFormEvolutionEquiv_embedding ε hε h hh hb m g k s₁ t₁ u_form,
      h2b.1, h2b.2, heb.1, heb.2.1⟩,
    hstokes.1, hweq.1, hw_pl.2, hy_pl.2,
    LayerB.Build1_ExplicitWilsonAction.diamondLinkCount_eq_four,
    LayerB.Build2_HamiltonianFromAction.topEigenvalue_value,
    LayerB.Build6_VolterraBlockDiagonalDerivation.H_W_chamberBath_commutes,
    LayerB.CL1_BathSector.μ_vac_pos,
    LayerB.CL2_WightmanAxioms.all_wightman_axioms_length,
    LayerB.Clay3_PhysicalZ.perPlaquetteActionMax_pos⟩

#print axioms staticResidual_secondResolvent_and_twoTimeFormEvolutionIsomorphism_with_wightman_clay
#print axioms eightByEight_plaquetteGrid_stokes_with_alphaSAudit_andoGeometricMean_and_bTauReaudit
#print axioms eightByEight_identityPlaquetteGrid_stokes_with_wilsonAction_feshbach_and_volterraBlock
#print axioms equalOuterFinalTime_eightByEightResolventGrid_with_cfcDiagonal_ckmAudit_and_schur7
#print axioms equalOuterFinalTime_eightByEightIdentityGrid_with_cl2Wightman_and_cl3Continuum
#print axioms eightByEight_plaquetteGrid_staticResidualSecondResolvent_twoTimeFormIsomorphism_bridge_master

end
end KFCausalClockFloorEightByEightPlaquetteStaticResidualSecondResolventTwoTimeFormIsomorphismBridge
end Audit
end UnifiedTheory
