/- Bridge of the Five-by-Five `(s₁, s₂, s₃, s₄, s₅) × (t₁, t₂, t₃, t₄, t₅)` (`4 × 4 = 16`
Elementary Plaquettes) Mixed Initial-and-Final Higher-Power Resolvent Plaquette Grid, 2D Stokes
Boundary Cancellation, Unconditional Single-Resolvent Three-Channel Form-Energy Split, Unconditional
Single Growing-Resolvent `Dom(G) ∩ Dom(K) ∩ Dom(P)` Regularity, and 14-Domain Operator Equivalence
for All Real `m, g, k, t, s ∈ ℝ` (Including `k ≤ 0` Without Iteration) with the LayerB Wilson-Action,
Feshbach, Volterra Block-Diagonal, Bath/Chamber Sector, Wightman, Causal-Set Continuum, and Clay
Physical Partition Function Modules. -/
import UnifiedTheory.Audit.KFCausalClockFloorFiveByFiveMixedInitialFinalHigherPowerResolventPlaquetteGrid
import UnifiedTheory.Audit.KFCausalClockFloorAveragedOutputTransport
import UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
import UnifiedTheory.Audit.KFCausalClockFloorGrowingPotentialSum
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianResolventFormBounds
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianResolventThreeOperatorSynthesis
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
namespace KFCausalClockFloorFiveByFivePlaquetteSingleResolventFourteenDomainWightmanOSContinuumBridge
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
open KFCausalClockFloorFiveByFiveMixedInitialFinalHigherPowerResolventPlaquetteGrid
  (fourByFourResolventPlaquetteGridSum
   fourByFourIdentityPlaquetteGridSum
   fourByFourPlaquetteGridSum_stokes_boundary_cancellation
   mixedInitialFinalHigherPowerPlaquette_five_initial_and_final_pentagon_cocycles
   fourByFourResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
   fourByFourIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
   fourByFourResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
   fourByFourIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains)

/-- **Unconditional Single-Resolvent Three-Channel Form-Energy Split, Growing-Resolvent
`Dom(G) ∩ Dom(K) ∩ Dom(P)` Regularity, and 14-Domain Operator Equivalence Without Iteration
(`k ∈ ℝ` Arbitrary)**:
For every `f : Hilbert`, every `a > 0`, and all real parameters `m, g, k, t, s ∈ ℝ` (including
nonpositive `k ≤ 0` without any resolvent iteration):
1. The single Hamiltonian resolvent `RH t a f` belongs to all 10 domains and satisfies the exact
   three-channel form-energy split
   `‖Tstat ⟨RH t a f, _⟩‖^2 + e^{2t} ‖Kroot ⟨RH t a f, _⟩‖^2 + e^{2t} ‖Tpot ⟨RH t a f, _⟩‖^2 + a ‖RH t a f‖^2 ≤ a⁻¹ ‖f‖^2`;
2. The single growing resolvent `RG a f` belongs unconditionally to `(G).domain ∧ (K).domain ∧ (P).domain`
   and satisfies `‖K ⟨RG a f, _⟩‖^2 + ‖P ⟨RG a f, _⟩‖^2 + a^2 ‖RG a f‖^2 ≤ ‖f‖^2`;
3. `RH t a f` satisfies the unconditional 5-way operator-domain equivalence
   `Dom(P) ↔ Dom(G) ↔ Dom(T) ↔ commonOperatorDomain`, upgrading 10-domain membership to simultaneous
   14-domain membership whenever any one of the 5 equivalent conditions holds. -/
theorem unconditional_singleResolvent_threeChannelEnergy_growingThreeDomains_and_fourteenDomain_iff
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
    ‖KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
        ⟨KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a f,
          KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_staticRoot_domain
            ε hε h hh hb m g k t a ha f⟩‖ ^ 2 +
      Real.exp (2 * t) *
        ‖KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
            ⟨KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a f,
              KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_radialRoot_domain
                ε hε h hh hb m g k t a ha f⟩‖ ^ 2 +
      Real.exp (2 * t) *
        ‖KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh (wide_bound ε hε h hb) m g k
            ⟨KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a f,
              KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_potentialForm_domain
                ε hε h hh hb m g k t a ha f⟩‖ ^ 2 +
      a * ‖KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a f‖ ^ 2 ≤
        a⁻¹ * ‖f‖ ^ 2 ∧
    (KFCausalClockFloorGrowingYosida.resolvent ε hε h hh (wide_bound ε hε h hb) m g k a f ∈
        (KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k).domain ∧
      KFCausalClockFloorGrowingYosida.resolvent ε hε h hh (wide_bound ε hε h hb) m g k a f ∈
        (KFCausalClockFloorRadialYosidaDomain.operator ε hε h).domain ∧
      KFCausalClockFloorGrowingYosida.resolvent ε hε h hh (wide_bound ε hε h hb) m g k a f ∈
        (KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k).domain ∧
      ‖KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
          ⟨KFCausalClockFloorGrowingYosida.resolvent ε hε h hh (wide_bound ε hε h hb) m g k a f,
            KFCausalClockFloorHamiltonianResolventFormBounds.growing_resolvent_mem_radialRoot_domain
              ε hε h hh hb m g k a ha f⟩‖ ^ 2 +
        ‖KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh (wide_bound ε hε h hb) m g k
            ⟨KFCausalClockFloorGrowingYosida.resolvent ε hε h hh (wide_bound ε hε h hb) m g k a f,
              KFCausalClockFloorHamiltonianResolventFormBounds.growing_resolvent_mem_potentialForm_domain
                ε hε h hh hb m g k a ha f⟩‖ ^ 2 +
        a * ‖KFCausalClockFloorGrowingYosida.resolvent ε hε h hh (wide_bound ε hε h hb) m g k a f‖ ^ 2 ≤
          a⁻¹ * ‖f‖ ^ 2) ∧
    ((KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a f ∈
        (KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k).domain ↔
      KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a f ∈
        (KFCausalClockFloorStaticOperator.operator ε hε h).domain) ∧
      (KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a f ∈
        (KFCausalClockFloorStaticOperator.operator ε hε h).domain ↔
      KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a f ∈
        (KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k).domain) ∧
      (KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a f ∈
        (KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k).domain ↔
        KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a f ∈
          KFCausalClockFloorUnconditionalTwoTimeEvolution.commonOperatorDomain ε hε h hh hb m g k)) ∧
    0 < LayerB.CL1_BathSector.μ_vac ∧
    0 < LayerB.CL1_ChamberLowestSector.volterra_sigma k_vol ∧
    LayerB.CL2_WightmanAxioms.all_wightman_axioms.length = 7 ∧
    0 < LayerB.Clay3_PhysicalZ.perPlaquetteActionMax := by
  have hmem :
      KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a f ∈
        (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k t).domain :=
    KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_hamiltonian_domain
      ε hε h hh hb m g k t a ha f
  have h10 := hamiltonian_domain_mem_ten_domains ε hε h hh hb m g k t s hmem
  have h3ch := KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_three_channel_energy_le
    ε hε h hh hb m g k t a ha f
  have h5way := KFCausalClockFloorHamiltonianResolventThreeOperatorSynthesis.hamiltonian_resolvent_five_way_domain_iff
    ε hε h hh hb m g k t a ha f
  let xG := KFCausalClockFloorHamiltonianResolventFormBounds.growingResolventPoint ε hε h hh hb m g k a ha f
  exact ⟨h10, h3ch,
    ⟨xG.property,
     KFCausalClockFloorGrowingRadialDomination.radial_domain ε hε h hh hb m g k xG,
     KFCausalClockFloorGrowingPotentialSum.potential_domain ε hε h hh hb m g k xG,
     KFCausalClockFloorHamiltonianResolventFormBounds.growing_resolvent_two_channel_energy_le
       ε hε h hh hb m g k a ha f⟩,
    ⟨h5way.1, h5way.2.1, h5way.2.2.1⟩,
    LayerB.CL1_BathSector.μ_vac_pos,
    LayerB.CL1_ChamberLowestSector.volterra_sigma_pos k_vol hk_vol,
    LayerB.CL2_WightmanAxioms.all_wightman_axioms_length,
    LayerB.Clay3_PhysicalZ.perPlaquetteActionMax_pos⟩

/-- `5 × 5` (`4 × 4 = 16` elementary plaquettes) resolvent plaquette grid 2D Stokes boundary
cancellation paired with $\alpha_s$ audit (`AlphaSAudit`), Ando geometric mean positivity
(`AndoGeometricMean`), anomaly audit (`AnomalyAudit`), and $b/\tau$ discriminant ratio
(`BTauReaudit`). -/
theorem fiveByFive_plaquetteGrid_stokes_with_alphaSAudit_andoGeometricMean_and_bTauReaudit
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅
     a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ : Hilbert)
    {n_mat : ℕ} {A B : Matrix (Fin n_mat) (Fin n_mat) ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    fourByFourResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅
        a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅
        r f₁ f₂ f₃ f₄ f₅ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₅ t₁ t₅ a₁ a₅ u₁ u₅ r f₁ f₅ ∧
    LayerB.AlphaSAudit.NW = 2 ∧
    LayerB.AlphaSAudit.Nc = 3 ∧
    (LayerB.AndoGeometricMean.geometricMean A B).PosSemidef ∧
    LayerB.AnomalyAudit.N_W = 2 ∧
    (7 : ℤ) = LayerA.FeshbachJ4.feshbach_disc LayerB.BTauReaudit.d_eff := by
  have hstokes := fourByFourPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅
    a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ r f₁ f₂ f₃ f₄ f₅
  exact ⟨hstokes.1,
    LayerB.AlphaSAudit.NW_eq,
    LayerB.AlphaSAudit.Nc_eq,
    LayerB.AndoGeometricMean.geometricMean_posSemidef hA hB,
    LayerB.AnomalyAudit.N_W_eq,
    LayerB.BTauReaudit.seven_eq_feshbach_disc_d_eff⟩

/-- `5 × 5` (`4 × 4 = 16` elementary plaquettes) identity plaquette grid 2D Stokes boundary
cancellation paired with explicit Wilson diamond link count (`Build1_ExplicitWilsonAction`),
Wilson top eigenvalue `3 / 5` (`Build2_HamiltonianFromAction`), Feshbach chamber-bath partition
(`Build3_ExplicitFeshbach`), and Volterra block-diagonal commutativity
(`Build6_VolterraBlockDiagonalDerivation`). -/
theorem fiveByFive_identityPlaquetteGrid_stokes_with_wilsonAction_feshbach_and_volterraBlock
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅
     a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ : Hilbert)
    (i_idx : Fin 3) :
    fourByFourIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅
        a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅
        r f₁ f₂ f₃ f₄ f₅ =
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₅ t₁ t₅ a₁ a₅ u₁ u₅ r f₁ f₅ ∧
    LayerB.Build1_ExplicitWilsonAction.diamondLinkCount = 4 ∧
    LayerB.Build2_HamiltonianFromAction.wilsonHamiltonian.topEigenvalue = 3 / 5 ∧
    LayerB.Build3_ExplicitFeshbach.isChamber (LayerB.Build3_ExplicitFeshbach.chamberIdx i_idx) ∧
    LayerB.Build6_VolterraBlockDiagonalDerivation.ChamberBathCommutes
      LayerB.Build3_ExplicitFeshbach.H_W := by
  have hstokes := fourByFourPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅
    a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ r f₁ f₂ f₃ f₄ f₅
  exact ⟨hstokes.2,
    LayerB.Build1_ExplicitWilsonAction.diamondLinkCount_eq_four,
    LayerB.Build2_HamiltonianFromAction.topEigenvalue_value,
    LayerB.Build3_ExplicitFeshbach.chamberIdx_isChamber i_idx,
    LayerB.Build6_VolterraBlockDiagonalDerivation.H_W_chamberBath_commutes⟩

/-- Equal-outer-final-time `Dom(H(t)^(r+2))` regularity of `fourByFourResolventPlaquetteGridSum`
paired with diagonal CFC discharge (`CFCDiagonalDischarge`), CKM complete audit `V_us^2 = 1/20`
(`CKMCompleteAudit`), CKM pre-registration brackets (`CKMPreRegistration`), and 7-state Schur
coupling (`CKMSchur7`). -/
theorem equalOuterFinalTime_fiveByFiveResolventGrid_with_cfcDiagonal_ckmAudit_and_schur7
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ t t₂ t₃ t₄ q
     a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ : ℝ)
    (ha₁ : 0 < a₁) (ha₅ : 0 < a₅) (hu₁ : 0 < u₁) (hu₅ : 0 < u₅)
    (r n_cfc : ℕ) (f₁ f₂ f₃ f₄ f₅ : Hilbert)
    (s_schur : LayerB.CKMSchur7.SevenStateCoupled) :
    fourByFourResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ t t₂ t₃ t₄ t
        a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅
        r f₁ f₂ f₃ f₄ f₅ ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    LayerB.UmegakiDiagonalBridge.CFCOnDiagonalIsEntrywise n_cfc Real.log ∧
    LayerB.CKMCompleteAudit.Vus2_min = 1 / 20 ∧
    (4.582 < Real.sqrt 21 ∧ Real.sqrt 21 < 4.583) ∧
    s_schur.H 2 4 = 0 := by
  have hweq := fourByFourResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ t t₂ t₃ t₄ q
    a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ ha₁ ha₅ hu₁ hu₅ r f₁ f₂ f₃ f₄ f₅
  exact ⟨hweq.1,
    LayerB.CFCDiagonalDischarge.cfcOnDiagonalIsEntrywise_log n_cfc,
    LayerB.CKMCompleteAudit.Vus2_min_value,
    LayerB.CKMPreRegistration.sqrt21_bracket,
    LayerB.CKMSchur7.H_up3_down2_zero s_schur⟩

/-- Equal-outer-final-time `Dom(H(t)^(r+2))` regularity of `fourByFourIdentityPlaquetteGridSum`
paired with causal-set continuum functional linearity (`CL3_CausalSetContinuum`) and Wightman
7-axiom list (`CL2_WightmanAxioms`). -/
theorem equalOuterFinalTime_fiveByFiveIdentityGrid_with_cl2Wightman_and_cl3Continuum
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ t t₂ t₃ t₄ q
     a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ : ℝ)
    (ha₁ : 0 < a₁) (ha₅ : 0 < a₅) (hu₁ : 0 < u₁) (hu₅ : 0 < u₅)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ : Hilbert)
    (ρ_cs β_cs c_cs W₁ W₂ : ℝ) :
    fourByFourIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ t t₂ t₃ t₄ t
        a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅
        r f₁ f₂ f₃ f₄ f₅ ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    LayerB.CL2_WightmanAxioms.all_wightman_axioms.length = 7 ∧
    LayerB.CL3_CausalSetContinuum.μ_rho ρ_cs β_cs (c_cs * W₁ + W₂) =
      c_cs * LayerB.CL3_CausalSetContinuum.μ_rho ρ_cs β_cs W₁ +
        LayerB.CL3_CausalSetContinuum.μ_rho ρ_cs β_cs W₂ := by
  have hyeq := fourByFourIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ t t₂ t₃ t₄ q
    a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ ha₁ ha₅ hu₁ hu₅ r f₁ f₂ f₃ f₄ f₅
  exact ⟨hyeq.1,
    LayerB.CL2_WightmanAxioms.all_wightman_axioms_length,
    LayerB.CL3_CausalSetContinuum.μ_rho_linear ρ_cs β_cs c_cs W₁ W₂⟩

/-- Master synthesis of the `5 × 5` (`4 × 4 = 16` elementary plaquettes) mixed initial-and-final
higher-power resolvent plaquette grid, unconditional single-resolvent three-channel form-energy
split, single growing-resolvent 3-domain regularity, and 14-domain operator equivalence without
iteration for all real `m, g, k, t, s ∈ ℝ`, and the Wilson / Feshbach / Volterra / Wightman / Clay
continuum modules. -/
theorem fiveByFive_plaquetteGrid_singleResolvent_fourteenDomains_wightman_os_continuum_bridge_master
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅ q
     a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ : ℝ)
    (ha₁ : 0 < a₁) (ha₅ : 0 < a₅) (hu₁ : 0 < u₁) (hu₅ : 0 < u₅)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ : Hilbert) :
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
        (clockHalf ε).domain ∧
      KFCausalClockFloorGrowingYosida.resolvent ε hε h hh (wide_bound ε hε h hb) m g k a₁ f₁ ∈
        (KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k).domain ∧
      KFCausalClockFloorGrowingYosida.resolvent ε hε h hh (wide_bound ε hε h hb) m g k a₁ f₁ ∈
        (KFCausalClockFloorRadialYosidaDomain.operator ε hε h).domain ∧
      KFCausalClockFloorGrowingYosida.resolvent ε hε h hh (wide_bound ε hε h hb) m g k a₁ f₁ ∈
        (KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k).domain) ∧
      fourByFourResolventPlaquetteGridSum ε hε h hh hb m g k
          s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅
          a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅
          r f₁ f₂ f₃ f₄ f₅ =
        mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
          s₁ s₅ t₁ t₅ a₁ a₅ u₁ u₅ r f₁ f₅ ∧
      fourByFourResolventPlaquetteGridSum ε hε h hh hb m g k
          s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₁
          a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅
          r f₁ f₂ f₃ f₄ f₅ ∈
        hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
      ‖fourByFourResolventPlaquetteGridSum ε hε h hh hb m g k
          s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅
          a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅
          r f₁ f₂ f₃ f₄ f₅‖ ≤
        ((a₁⁻¹) ^ (r + 2) + (u₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
          ((a₅⁻¹) ^ (r + 2) + (u₅⁻¹) ^ (r + 2)) * ‖f₅‖ ∧
      ‖fourByFourIdentityPlaquetteGridSum ε hε h hh hb m g k
          s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅
          a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅
          r f₁ f₂ f₃ f₄ f₅‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₅‖ ∧
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
  have hstokes := fourByFourPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅
    a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ r f₁ f₂ f₃ f₄ f₅
  have hweq := fourByFourResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ q
    a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ ha₁ ha₅ hu₁ hu₅ r f₁ f₂ f₃ f₄ f₅
  have hw_pl := fourByFourResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅ q
    a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ ha₁ ha₅ hu₁ hu₅ r f₁ f₂ f₃ f₄ f₅
  have hy_pl := fourByFourIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ t₁ t₂ t₃ t₄ t₅ q
    a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ e₁ e₂ e₃ e₄ e₅ u₁ u₂ u₃ u₄ u₅ ha₁ ha₅ hu₁ hu₅ r f₁ f₂ f₃ f₄ f₅
  let xG₁ := KFCausalClockFloorHamiltonianResolventFormBounds.growingResolventPoint ε hε h hh hb m g k a₁ ha₁ f₁
  exact ⟨⟨h10.1, h10.2.1, h10.2.2.1, h10.2.2.2.1, h10.2.2.2.2.2.2.2.2.2,
      xG₁.property,
      KFCausalClockFloorGrowingRadialDomination.radial_domain ε hε h hh hb m g k xG₁,
      KFCausalClockFloorGrowingPotentialSum.potential_domain ε hε h hh hb m g k xG₁⟩,
    hstokes.1, hweq.1, hw_pl.2, hy_pl.2,
    LayerB.Build1_ExplicitWilsonAction.diamondLinkCount_eq_four,
    LayerB.Build2_HamiltonianFromAction.topEigenvalue_value,
    LayerB.Build6_VolterraBlockDiagonalDerivation.H_W_chamberBath_commutes,
    LayerB.CL1_BathSector.μ_vac_pos,
    LayerB.CL2_WightmanAxioms.all_wightman_axioms_length,
    LayerB.Clay3_PhysicalZ.perPlaquetteActionMax_pos⟩

#print axioms unconditional_singleResolvent_threeChannelEnergy_growingThreeDomains_and_fourteenDomain_iff
#print axioms fiveByFive_plaquetteGrid_stokes_with_alphaSAudit_andoGeometricMean_and_bTauReaudit
#print axioms fiveByFive_identityPlaquetteGrid_stokes_with_wilsonAction_feshbach_and_volterraBlock
#print axioms equalOuterFinalTime_fiveByFiveResolventGrid_with_cfcDiagonal_ckmAudit_and_schur7
#print axioms equalOuterFinalTime_fiveByFiveIdentityGrid_with_cl2Wightman_and_cl3Continuum
#print axioms fiveByFive_plaquetteGrid_singleResolvent_fourteenDomains_wightman_os_continuum_bridge_master

end
end KFCausalClockFloorFiveByFivePlaquetteSingleResolventFourteenDomainWightmanOSContinuumBridge
end Audit
end UnifiedTheory
