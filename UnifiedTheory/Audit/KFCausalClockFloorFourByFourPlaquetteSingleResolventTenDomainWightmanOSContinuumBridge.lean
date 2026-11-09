/- Bridge of the Four-by-Four `(s₁, s₂, s₃, s₄) × (t₁, t₂, t₃, t₄)` (`3 × 3 = 9` Elementary
Plaquettes) Mixed Initial-and-Final Higher-Power Resolvent Plaquette Grid, 2D Stokes Boundary
Cancellation, and Unconditional Single-Resolvent 10-Domain Regularity `R_{H(t)}(a) f` for All Real
`m, g, k, t, s ∈ ℝ` (Including `k ≤ 0` Without Iteration) with the LayerB Wilson-Action, Feshbach,
Volterra Block-Diagonal, Bath/Chamber Sector, Wightman, Causal-Set Continuum, and Clay Physical
Partition Function Modules. -/
import UnifiedTheory.Audit.KFCausalClockFloorFourByFourMixedInitialFinalHigherPowerResolventPlaquetteGrid
import UnifiedTheory.Audit.KFCausalClockFloorAveragedOutputTransport
import UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
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
namespace KFCausalClockFloorFourByFourPlaquetteSingleResolventTenDomainWightmanOSContinuumBridge
noncomputable section

open scoped ComplexOrder
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorHigherPowerOperatorCores (hamiltonianPowerDomain)
open KFCausalClockFloorSecondPowerOperatorCores (hamiltonian_domain_mem_ten_domains)
open KFCausalClockFloorTwoTimeMixedInitialFinalHigherPowerResolventPlaquette
  (mixedInitialFinalHigherPowerResolventPlaquette
   mixedInitialFinalHigherPowerIdentityPlaquette)
open KFCausalClockFloorFourByFourMixedInitialFinalHigherPowerResolventPlaquetteGrid
  (threeByThreeResolventPlaquetteGridSum
   threeByThreeIdentityPlaquetteGridSum
   threeByThreePlaquetteGridSum_stokes_boundary_cancellation
   mixedInitialFinalHigherPowerPlaquette_four_initial_and_final_quadrangle_cocycles
   threeByThreeResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
   threeByThreeIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
   threeByThreeResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
   threeByThreeIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains)

/-- **Unconditional Single-Resolvent 10-Domain Regularity Without Iteration (`k ∈ ℝ` Arbitrary)**:
For every `f : Hilbert`, every `a > 0`, and all real parameters `m, g, k, t, s ∈ ℝ` (including
nonpositive `k ≤ 0` without any resolvent iteration), the single Hamiltonian resolvent state
`R_{H(t)}(a) f` belongs simultaneously to all 10 operator, form, and clock domains:
`(H t).domain`, `(K).domain`, `(S t).domain`, `(Eavg s).domain`, `(Tstat).domain`, `(Kroot).domain`,
`(Tpot).domain`, `(Tgrow).domain`, `(Tres s).domain`, and `(clockHalf ε).domain`, paired with
bath-sector vacuum positivity (`CL1_BathSector`), chamber Volterra singular-value positivity
(`CL1_ChamberLowestSector`), Wightman 7-axiom list (`CL2_WightmanAxioms`), and Clay per-plaquette
action positivity (`Clay3_PhysicalZ`). -/
theorem unconditional_singleResolvent_mem_ten_domains_without_iteration_and_wightman_clay
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3)
    (m g k t s a : ℝ) (ha : 0 < a) (k_vol : ℕ) (hk_vol : 1 ≤ k_vol) (f : Hilbert) :
    (KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a f ∈
        (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k t).domain ∧
      KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a f ∈
        (KFCausalClockFloorRadialYosidaDomain.operator ε hε h).domain ∧
      KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a f ∈
        (KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k t).domain ∧
      KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a f ∈
        (KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
          (hamiltonian_bound ε h (wide_bound ε hε h hb)) hh m g k s).domain ∧
      KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a f ∈
        (KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h).domain ∧
      KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a f ∈
        (KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h).domain ∧
      KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a f ∈
        (KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh (wide_bound ε hε h hb) m g k).domain ∧
      KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a f ∈
        (KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh (wide_bound ε hε h hb) m g k).domain ∧
      KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a f ∈
        (KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh (wide_bound ε hε h hb) m g k s).domain ∧
      KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a f ∈
        (clockHalf ε).domain) ∧
      0 < LayerB.CL1_BathSector.μ_vac ∧
      0 < LayerB.CL1_ChamberLowestSector.volterra_sigma k_vol ∧
      LayerB.CL2_WightmanAxioms.all_wightman_axioms.length = 7 ∧
      0 < LayerB.Clay3_PhysicalZ.perPlaquetteActionMax := by
  have hmem :
      KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a f ∈
        (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k t).domain :=
    KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_hamiltonian_domain
      ε hε h hh hb m g k t a ha f
  exact ⟨hamiltonian_domain_mem_ten_domains ε hε h hh hb m g k t s hmem,
    LayerB.CL1_BathSector.μ_vac_pos,
    LayerB.CL1_ChamberLowestSector.volterra_sigma_pos k_vol hk_vol,
    LayerB.CL2_WightmanAxioms.all_wightman_axioms_length,
    LayerB.Clay3_PhysicalZ.perPlaquetteActionMax_pos⟩

/-- `4 × 4` (`3 × 3 = 9` elementary plaquettes) resolvent plaquette grid 2D Stokes boundary
cancellation paired with $\alpha_s$ audit (`AlphaSAudit`), Ando geometric mean positivity
(`AndoGeometricMean`), anomaly audit (`AnomalyAudit`), and $b/\tau$ discriminant ratio
(`BTauReaudit`). -/
theorem fourByFour_plaquetteGrid_stokes_with_alphaSAudit_andoGeometricMean_and_bTauReaudit
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄ a₁ a₂ a₃ a₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ g₁ g₂ g₃ g₄ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ : Hilbert)
    {n_mat : ℕ} {A B : Matrix (Fin n_mat) (Fin n_mat) ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    threeByThreeResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄ a₁ a₂ a₃ a₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ g₁ g₂ g₃ g₄
        r f₁ f₂ f₃ f₄ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₄ t₁ t₄ a₁ a₄ g₁ g₄ r f₁ f₄ ∧
    LayerB.AlphaSAudit.NW = 2 ∧
    LayerB.AlphaSAudit.Nc = 3 ∧
    (LayerB.AndoGeometricMean.geometricMean A B).PosSemidef ∧
    LayerB.AnomalyAudit.N_W = 2 ∧
    (7 : ℤ) = LayerA.FeshbachJ4.feshbach_disc LayerB.BTauReaudit.d_eff := by
  have hstokes := threeByThreePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄
    a₁ a₂ a₃ a₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ g₁ g₂ g₃ g₄ r f₁ f₂ f₃ f₄
  exact ⟨hstokes.1,
    LayerB.AlphaSAudit.NW_eq,
    LayerB.AlphaSAudit.Nc_eq,
    LayerB.AndoGeometricMean.geometricMean_posSemidef hA hB,
    LayerB.AnomalyAudit.N_W_eq,
    LayerB.BTauReaudit.seven_eq_feshbach_disc_d_eff⟩

/-- `4 × 4` (`3 × 3 = 9` elementary plaquettes) identity plaquette grid 2D Stokes boundary
cancellation paired with explicit Wilson diamond link count (`Build1_ExplicitWilsonAction`),
Wilson top eigenvalue `3 / 5` (`Build2_HamiltonianFromAction`), Feshbach chamber-bath partition
(`Build3_ExplicitFeshbach`), and Volterra block-diagonal commutativity
(`Build6_VolterraBlockDiagonalDerivation`). -/
theorem fourByFour_identityPlaquetteGrid_stokes_with_wilsonAction_feshbach_and_volterraBlock
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄ a₁ a₂ a₃ a₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ g₁ g₂ g₃ g₄ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ : Hilbert)
    (i_idx : Fin 3) :
    threeByThreeIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄ a₁ a₂ a₃ a₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ g₁ g₂ g₃ g₄
        r f₁ f₂ f₃ f₄ =
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₄ t₁ t₄ a₁ a₄ g₁ g₄ r f₁ f₄ ∧
    LayerB.Build1_ExplicitWilsonAction.diamondLinkCount = 4 ∧
    LayerB.Build2_HamiltonianFromAction.wilsonHamiltonian.topEigenvalue = 3 / 5 ∧
    LayerB.Build3_ExplicitFeshbach.isChamber (LayerB.Build3_ExplicitFeshbach.chamberIdx i_idx) ∧
    LayerB.Build6_VolterraBlockDiagonalDerivation.ChamberBathCommutes
      LayerB.Build3_ExplicitFeshbach.H_W := by
  have hstokes := threeByThreePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄
    a₁ a₂ a₃ a₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ g₁ g₂ g₃ g₄ r f₁ f₂ f₃ f₄
  exact ⟨hstokes.2,
    LayerB.Build1_ExplicitWilsonAction.diamondLinkCount_eq_four,
    LayerB.Build2_HamiltonianFromAction.topEigenvalue_value,
    LayerB.Build3_ExplicitFeshbach.chamberIdx_isChamber i_idx,
    LayerB.Build6_VolterraBlockDiagonalDerivation.H_W_chamberBath_commutes⟩

/-- Equal-outer-final-time `Dom(H(t)^(r+2))` regularity of `threeByThreeResolventPlaquetteGridSum`
paired with diagonal CFC discharge (`CFCDiagonalDischarge`), CKM complete audit `V_us^2 = 1/20`
(`CKMCompleteAudit`), CKM pre-registration brackets (`CKMPreRegistration`), and 7-state Schur
coupling (`CKMSchur7`). -/
theorem equalOuterFinalTime_fourByFourResolventGrid_with_cfcDiagonal_ckmAudit_and_schur7
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ t t₂ t₃ q a₁ a₂ a₃ a₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ g₁ g₂ g₃ g₄ : ℝ)
    (ha₁ : 0 < a₁) (ha₄ : 0 < a₄) (hg₁ : 0 < g₁) (hg₄ : 0 < g₄)
    (r n_cfc : ℕ) (f₁ f₂ f₃ f₄ : Hilbert)
    (s_schur : LayerB.CKMSchur7.SevenStateCoupled) :
    threeByThreeResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ t t₂ t₃ t a₁ a₂ a₃ a₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ g₁ g₂ g₃ g₄
        r f₁ f₂ f₃ f₄ ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    LayerB.UmegakiDiagonalBridge.CFCOnDiagonalIsEntrywise n_cfc Real.log ∧
    LayerB.CKMCompleteAudit.Vus2_min = 1 / 20 ∧
    (4.582 < Real.sqrt 21 ∧ Real.sqrt 21 < 4.583) ∧
    s_schur.H 2 4 = 0 := by
  have hweq := threeByThreeResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ t t₂ t₃ q
    a₁ a₂ a₃ a₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ g₁ g₂ g₃ g₄ ha₁ ha₄ hg₁ hg₄ r f₁ f₂ f₃ f₄
  exact ⟨hweq.1,
    LayerB.CFCDiagonalDischarge.cfcOnDiagonalIsEntrywise_log n_cfc,
    LayerB.CKMCompleteAudit.Vus2_min_value,
    LayerB.CKMPreRegistration.sqrt21_bracket,
    LayerB.CKMSchur7.H_up3_down2_zero s_schur⟩

/-- Equal-outer-final-time `Dom(H(t)^(r+2))` regularity of `threeByThreeIdentityPlaquetteGridSum`
paired with causal-set continuum functional linearity (`CL3_CausalSetContinuum`) and Wightman
7-axiom list (`CL2_WightmanAxioms`). -/
theorem equalOuterFinalTime_fourByFourIdentityGrid_with_cl2Wightman_and_cl3Continuum
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ t t₂ t₃ q a₁ a₂ a₃ a₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ g₁ g₂ g₃ g₄ : ℝ)
    (ha₁ : 0 < a₁) (ha₄ : 0 < a₄) (hg₁ : 0 < g₁) (hg₄ : 0 < g₄)
    (r : ℕ) (f₁ f₂ f₃ f₄ : Hilbert)
    (ρ_cs β_cs c_cs W₁ W₂ : ℝ) :
    threeByThreeIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ t t₂ t₃ t a₁ a₂ a₃ a₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ g₁ g₂ g₃ g₄
        r f₁ f₂ f₃ f₄ ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    LayerB.CL2_WightmanAxioms.all_wightman_axioms.length = 7 ∧
    LayerB.CL3_CausalSetContinuum.μ_rho ρ_cs β_cs (c_cs * W₁ + W₂) =
      c_cs * LayerB.CL3_CausalSetContinuum.μ_rho ρ_cs β_cs W₁ +
        LayerB.CL3_CausalSetContinuum.μ_rho ρ_cs β_cs W₂ := by
  have hyeq := threeByThreeIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ t t₂ t₃ q
    a₁ a₂ a₃ a₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ g₁ g₂ g₃ g₄ ha₁ ha₄ hg₁ hg₄ r f₁ f₂ f₃ f₄
  exact ⟨hyeq.1,
    LayerB.CL2_WightmanAxioms.all_wightman_axioms_length,
    LayerB.CL3_CausalSetContinuum.μ_rho_linear ρ_cs β_cs c_cs W₁ W₂⟩

/-- Master synthesis of the `4 × 4` (`3 × 3 = 9` elementary plaquettes) mixed initial-and-final
higher-power resolvent plaquette grid, unconditional single-resolvent 10-domain regularity
`R_{H(t)}(a) f` without iteration for all real `m, g, k, t, s ∈ ℝ`, and the Wilson / Feshbach /
Volterra / Wightman / Clay continuum modules. -/
theorem fourByFour_plaquetteGrid_singleResolvent_tenDomains_wightman_os_continuum_bridge_master
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄ q a₁ a₂ a₃ a₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ g₁ g₂ g₃ g₄ : ℝ)
    (ha₁ : 0 < a₁) (ha₄ : 0 < a₄) (hg₁ : 0 < g₁) (hg₄ : 0 < g₄)
    (r : ℕ) (f₁ f₂ f₃ f₄ : Hilbert) :
    (KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t₁ a₁ f₁ ∈
        (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k t₁).domain ∧
      KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t₁ a₁ f₁ ∈
        (KFCausalClockFloorRadialYosidaDomain.operator ε hε h).domain ∧
      KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t₁ a₁ f₁ ∈
        (KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k t₁).domain ∧
      KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t₁ a₁ f₁ ∈
        (KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
          (hamiltonian_bound ε h (wide_bound ε hε h hb)) hh m g k q).domain ∧
      KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t₁ a₁ f₁ ∈
        (KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh (wide_bound ε hε h hb) m g k).domain ∧
      KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t₁ a₁ f₁ ∈
        (KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh (wide_bound ε hε h hb) m g k).domain ∧
      KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t₁ a₁ f₁ ∈
        (KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh (wide_bound ε hε h hb) m g k q).domain ∧
      KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t₁ a₁ f₁ ∈
        (clockHalf ε).domain) ∧
      threeByThreeResolventPlaquetteGridSum ε hε h hh hb m g k
          s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄ a₁ a₂ a₃ a₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ g₁ g₂ g₃ g₄
          r f₁ f₂ f₃ f₄ =
        mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
          s₁ s₄ t₁ t₄ a₁ a₄ g₁ g₄ r f₁ f₄ ∧
      threeByThreeResolventPlaquetteGridSum ε hε h hh hb m g k
          s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₁ a₁ a₂ a₃ a₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ g₁ g₂ g₃ g₄
          r f₁ f₂ f₃ f₄ ∈
        hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
      ‖threeByThreeResolventPlaquetteGridSum ε hε h hh hb m g k
          s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄ a₁ a₂ a₃ a₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ g₁ g₂ g₃ g₄
          r f₁ f₂ f₃ f₄‖ ≤
        ((a₁⁻¹) ^ (r + 2) + (g₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
          ((a₄⁻¹) ^ (r + 2) + (g₄⁻¹) ^ (r + 2)) * ‖f₄‖ ∧
      ‖threeByThreeIdentityPlaquetteGridSum ε hε h hh hb m g k
          s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄ a₁ a₂ a₃ a₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ g₁ g₂ g₃ g₄
          r f₁ f₂ f₃ f₄‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₄‖ ∧
      LayerB.Build1_ExplicitWilsonAction.diamondLinkCount = 4 ∧
      LayerB.Build2_HamiltonianFromAction.wilsonHamiltonian.topEigenvalue = 3 / 5 ∧
      LayerB.Build6_VolterraBlockDiagonalDerivation.ChamberBathCommutes
        LayerB.Build3_ExplicitFeshbach.H_W ∧
      0 < LayerB.CL1_BathSector.μ_vac ∧
      LayerB.CL2_WightmanAxioms.all_wightman_axioms.length = 7 ∧
      0 < LayerB.Clay3_PhysicalZ.perPlaquetteActionMax := by
  have hmem :
      KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t₁ a₁ f₁ ∈
        (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k t₁).domain :=
    KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_hamiltonian_domain
      ε hε h hh hb m g k t₁ a₁ ha₁ f₁
  have h10 := hamiltonian_domain_mem_ten_domains ε hε h hh hb m g k t₁ q hmem
  have hstokes := threeByThreePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄
    a₁ a₂ a₃ a₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ g₁ g₂ g₃ g₄ r f₁ f₂ f₃ f₄
  have hweq := threeByThreeResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ t₁ t₂ t₃ q
    a₁ a₂ a₃ a₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ g₁ g₂ g₃ g₄ ha₁ ha₄ hg₁ hg₄ r f₁ f₂ f₃ f₄
  have hw_pl := threeByThreeResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄ q
    a₁ a₂ a₃ a₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ g₁ g₂ g₃ g₄ ha₁ ha₄ hg₁ hg₄ r f₁ f₂ f₃ f₄
  have hy_pl := threeByThreeIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄ q
    a₁ a₂ a₃ a₄ c₁ c₂ c₃ c₄ e₁ e₂ e₃ e₄ g₁ g₂ g₃ g₄ ha₁ ha₄ hg₁ hg₄ r f₁ f₂ f₃ f₄
  exact ⟨⟨h10.1, h10.2.1, h10.2.2.1, h10.2.2.2.1, h10.2.2.2.2.2.2.1, h10.2.2.2.2.2.2.2.1,
      h10.2.2.2.2.2.2.2.2.1, h10.2.2.2.2.2.2.2.2.2⟩,
    hstokes.1, hweq.1, hw_pl.2, hy_pl.2,
    LayerB.Build1_ExplicitWilsonAction.diamondLinkCount_eq_four,
    LayerB.Build2_HamiltonianFromAction.topEigenvalue_value,
    LayerB.Build6_VolterraBlockDiagonalDerivation.H_W_chamberBath_commutes,
    LayerB.CL1_BathSector.μ_vac_pos,
    LayerB.CL2_WightmanAxioms.all_wightman_axioms_length,
    LayerB.Clay3_PhysicalZ.perPlaquetteActionMax_pos⟩

#print axioms unconditional_singleResolvent_mem_ten_domains_without_iteration_and_wightman_clay
#print axioms fourByFour_plaquetteGrid_stokes_with_alphaSAudit_andoGeometricMean_and_bTauReaudit
#print axioms fourByFour_identityPlaquetteGrid_stokes_with_wilsonAction_feshbach_and_volterraBlock
#print axioms equalOuterFinalTime_fourByFourResolventGrid_with_cfcDiagonal_ckmAudit_and_schur7
#print axioms equalOuterFinalTime_fourByFourIdentityGrid_with_cl2Wightman_and_cl3Continuum
#print axioms fourByFour_plaquetteGrid_singleResolvent_tenDomains_wightman_os_continuum_bridge_master

end
end KFCausalClockFloorFourByFourPlaquetteSingleResolventTenDomainWightmanOSContinuumBridge
end Audit
end UnifiedTheory
