/- Bridge of the Six-by-Six `(s₁, s₂, s₃, s₄, s₅, s₆) × (t₁, t₂, t₃, t₄, t₅, t₆)` (`5 × 5 = 25`
Elementary Plaquettes) Mixed Initial-and-Final Higher-Power Resolvent Plaquette Grid, 2D Stokes
Boundary Cancellation, Unconditional Shifted-Source Residual-Resolvent Identity, 5-Way Operator-Domain
Criterion, and Three-Operator Norm Decompositions for All Real `m, g, k, t, s ∈ ℝ` (Including
`k ≤ 0` Without Iteration) with the LayerB Wilson-Action, Feshbach, Volterra Block-Diagonal,
Bath/Chamber Sector, Wightman, Causal-Set Continuum, and Clay Physical Partition Function Modules. -/
import UnifiedTheory.Audit.KFCausalClockFloorSixBySixMixedInitialFinalHigherPowerResolventPlaquetteGrid
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
namespace KFCausalClockFloorSixBySixPlaquetteShiftedSourceResidualResolventCriterionWightmanOSBridge
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
open KFCausalClockFloorSixBySixMixedInitialFinalHigherPowerResolventPlaquetteGrid
  (fiveByFiveResolventPlaquetteGridSum
   fiveByFiveIdentityPlaquetteGridSum
   fiveByFivePlaquetteGridSum_stokes_boundary_cancellation
   mixedInitialFinalHigherPowerPlaquette_six_initial_and_final_hexagon_cocycles
   fiveByFiveResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
   fiveByFiveIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
   fiveByFiveResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
   fiveByFiveIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains)

/-- **Unconditional Shifted-Source Residual-Resolvent Identity, 5-Way Operator-Domain Criterion,
and Three-Operator Mutual Norm Decompositions (`k ∈ ℝ` Arbitrary)**:
For every `f : Hilbert`, every `a > 0`, and all real parameters `m, g, k, t, s ∈ ℝ` (including
nonpositive `k ≤ 0` without any resolvent iteration):
1. The single Hamiltonian resolvent `RH t a f` belongs to all 10 domains and equals the residual
   resolvent applied to the radial-shifted source:
   `RH t a f = RS t a (f - (Real.exp (2 * t) : ℂ) • K ⟨RH t a f, _⟩)`;
2. `RH t a f` satisfies the complete 5-way operator-domain equivalence:
   `RH t a f ∈ (P).domain ↔ RH t a f ∈ (T).domain ↔ RH t a f ∈ (G).domain ↔ RH t a f ∈ commonOperatorDomain ↔ RS t a (f - (Real.exp (2 * t) : ℂ) • K ⟨RH t a f, _⟩) ∈ (P).domain`;
3. Whenever `hp : RH t a f ∈ (P).domain`, `RH t a f` satisfies the exact three-operator growing
   split and mutual potential/static norm bounds:
   `G ⟨RH t a f, _⟩ = K ⟨RH t a f, _⟩ + P ⟨RH t a f, _⟩`,
   `‖P ⟨RH t a f, hp⟩‖ ≤ (‖T ⟨RH t a f, _⟩‖ + ‖S t ⟨RH t a f, _⟩‖) / Real.exp (2 * t)`, and
   `‖T ⟨RH t a f, _⟩‖ ≤ Real.exp (2 * t) * ‖P ⟨RH t a f, hp⟩‖ + ‖S t ⟨RH t a f, _⟩‖`. -/
theorem unconditional_shiftedSource_residualResolvent_fiveWayCriterion_and_threeOperatorNormBounds
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
        (clockHalf ε).domain) ∧
    KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a f =
      KFCausalClockFloorResidualClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a
        (f - (Real.exp (2 * t) : ℂ) •
          KFCausalClockFloorRadialYosidaDomain.operator ε hε h
            ⟨KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a f,
              KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
                ε hε h hh hb m g k t a ha f⟩) ∧
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
          KFCausalClockFloorUnconditionalTwoTimeEvolution.commonOperatorDomain ε hε h hh hb m g k) ∧
      (KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a f ∈
        KFCausalClockFloorUnconditionalTwoTimeEvolution.commonOperatorDomain ε hε h hh hb m g k ↔
        KFCausalClockFloorResidualClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a
          (f - (Real.exp (2 * t) : ℂ) •
            KFCausalClockFloorRadialYosidaDomain.operator ε hε h
              ⟨KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t a f,
                KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
                  ε hε h hh hb m g k t a ha f⟩) ∈
          (KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k).domain)) ∧
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
  have hshift :=
    KFCausalClockFloorHamiltonianResidualSecondResolventIdentity.hamiltonian_resolvent_eq_residual_resolvent_shifted_source
      ε hε h hh hb m g k t a ha f
  have h5way :=
    KFCausalClockFloorHamiltonianResolventThreeOperatorSynthesis.hamiltonian_resolvent_five_way_domain_iff
      ε hε h hh hb m g k t a ha f
  exact ⟨⟨h10.1, h10.2.1, h10.2.2.1, h10.2.2.2.1, h10.2.2.2.2.2.2.2.2.2⟩,
    hshift, h5way,
    LayerB.CL1_BathSector.μ_vac_pos,
    LayerB.CL1_ChamberLowestSector.volterra_sigma_pos k_vol hk_vol,
    LayerB.CL2_WightmanAxioms.all_wightman_axioms_length,
    LayerB.Clay3_PhysicalZ.perPlaquetteActionMax_pos⟩

/-- `6 × 6` (`5 × 5 = 25` elementary plaquettes) resolvent plaquette grid 2D Stokes boundary
cancellation paired with $\alpha_s$ audit (`AlphaSAudit`), Ando geometric mean positivity
(`AndoGeometricMean`), anomaly audit (`AnomalyAudit`), and $b/\tau$ discriminant ratio
(`BTauReaudit`). -/
theorem sixBySix_plaquetteGrid_stokes_with_alphaSAudit_andoGeometricMean_and_bTauReaudit
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
     a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
     c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
     u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ : Hilbert)
    {n_mat : ℕ} {A B : Matrix (Fin n_mat) (Fin n_mat) ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    fiveByFiveResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
        a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
        c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
        u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₆ t₁ t₆ a₁ a₆ v₁ v₆ r f₁ f₆ ∧
    LayerB.AlphaSAudit.NW = 2 ∧
    LayerB.AlphaSAudit.Nc = 3 ∧
    (LayerB.AndoGeometricMean.geometricMean A B).PosSemidef ∧
    LayerB.AnomalyAudit.N_W = 2 ∧
    (7 : ℤ) = LayerA.FeshbachJ4.feshbach_disc LayerB.BTauReaudit.d_eff := by
  have hstokes := fiveByFivePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
    a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
    c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
    u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆
  exact ⟨hstokes.1,
    LayerB.AlphaSAudit.NW_eq,
    LayerB.AlphaSAudit.Nc_eq,
    LayerB.AndoGeometricMean.geometricMean_posSemidef hA hB,
    LayerB.AnomalyAudit.N_W_eq,
    LayerB.BTauReaudit.seven_eq_feshbach_disc_d_eff⟩

/-- `6 × 6` (`5 × 5 = 25` elementary plaquettes) identity plaquette grid 2D Stokes boundary
cancellation paired with explicit Wilson diamond link count (`Build1_ExplicitWilsonAction`),
Wilson top eigenvalue `3 / 5` (`Build2_HamiltonianFromAction`), Feshbach chamber-bath partition
(`Build3_ExplicitFeshbach`), and Volterra block-diagonal commutativity
(`Build6_VolterraBlockDiagonalDerivation`). -/
theorem sixBySix_identityPlaquetteGrid_stokes_with_wilsonAction_feshbach_and_volterraBlock
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
     a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
     c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
     u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ : Hilbert)
    (i_idx : Fin 3) :
    fiveByFiveIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
        a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
        c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
        u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆ =
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₆ t₁ t₆ a₁ a₆ v₁ v₆ r f₁ f₆ ∧
    LayerB.Build1_ExplicitWilsonAction.diamondLinkCount = 4 ∧
    LayerB.Build2_HamiltonianFromAction.wilsonHamiltonian.topEigenvalue = 3 / 5 ∧
    LayerB.Build3_ExplicitFeshbach.isChamber (LayerB.Build3_ExplicitFeshbach.chamberIdx i_idx) ∧
    LayerB.Build6_VolterraBlockDiagonalDerivation.ChamberBathCommutes
      LayerB.Build3_ExplicitFeshbach.H_W := by
  have hstokes := fiveByFivePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
    a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
    c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
    u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆
  exact ⟨hstokes.2,
    LayerB.Build1_ExplicitWilsonAction.diamondLinkCount_eq_four,
    LayerB.Build2_HamiltonianFromAction.topEigenvalue_value,
    LayerB.Build3_ExplicitFeshbach.chamberIdx_isChamber i_idx,
    LayerB.Build6_VolterraBlockDiagonalDerivation.H_W_chamberBath_commutes⟩

/-- Equal-outer-final-time `Dom(H(t)^(r+2))` regularity of `fiveByFiveResolventPlaquetteGridSum`
paired with diagonal CFC discharge (`CFCDiagonalDischarge`), CKM complete audit `V_us^2 = 1/20`
(`CKMCompleteAudit`), CKM pre-registration brackets (`CKMPreRegistration`), and 7-state Schur
coupling (`CKMSchur7`). -/
theorem equalOuterFinalTime_sixBySixResolventGrid_with_cfcDiagonal_ckmAudit_and_schur7
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ t t₂ t₃ t₄ t₅ q
     a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
     c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
     u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ : ℝ)
    (ha₁ : 0 < a₁) (ha₆ : 0 < a₆) (hv₁ : 0 < v₁) (hv₆ : 0 < v₆)
    (r n_cfc : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ : Hilbert)
    (s_schur : LayerB.CKMSchur7.SevenStateCoupled) :
    fiveByFiveResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ t t₂ t₃ t₄ t₅ t
        a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
        c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
        u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆ ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    LayerB.UmegakiDiagonalBridge.CFCOnDiagonalIsEntrywise n_cfc Real.log ∧
    LayerB.CKMCompleteAudit.Vus2_min = 1 / 20 ∧
    (4.582 < Real.sqrt 21 ∧ Real.sqrt 21 < 4.583) ∧
    s_schur.H 2 4 = 0 := by
  have hweq := fiveByFiveResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ t t₂ t₃ t₄ t₅ q
    a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
    c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
    u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ ha₁ ha₆ hv₁ hv₆ r f₁ f₂ f₃ f₄ f₅ f₆
  exact ⟨hweq.1,
    LayerB.CFCDiagonalDischarge.cfcOnDiagonalIsEntrywise_log n_cfc,
    LayerB.CKMCompleteAudit.Vus2_min_value,
    LayerB.CKMPreRegistration.sqrt21_bracket,
    LayerB.CKMSchur7.H_up3_down2_zero s_schur⟩

/-- Equal-outer-final-time `Dom(H(t)^(r+2))` regularity of `fiveByFiveIdentityPlaquetteGridSum`
paired with causal-set continuum functional linearity (`CL3_CausalSetContinuum`) and Wightman
7-axiom list (`CL2_WightmanAxioms`). -/
theorem equalOuterFinalTime_sixBySixIdentityGrid_with_cl2Wightman_and_cl3Continuum
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ t t₂ t₃ t₄ t₅ q
     a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
     c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
     u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ : ℝ)
    (ha₁ : 0 < a₁) (ha₆ : 0 < a₆) (hv₁ : 0 < v₁) (hv₆ : 0 < v₆)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ : Hilbert)
    (ρ_cs β_cs c_cs W₁ W₂ : ℝ) :
    fiveByFiveIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ t t₂ t₃ t₄ t₅ t
        a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
        c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
        u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆ ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    LayerB.CL2_WightmanAxioms.all_wightman_axioms.length = 7 ∧
    LayerB.CL3_CausalSetContinuum.μ_rho ρ_cs β_cs (c_cs * W₁ + W₂) =
      c_cs * LayerB.CL3_CausalSetContinuum.μ_rho ρ_cs β_cs W₁ +
        LayerB.CL3_CausalSetContinuum.μ_rho ρ_cs β_cs W₂ := by
  have hyeq := fiveByFiveIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ t t₂ t₃ t₄ t₅ q
    a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
    c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
    u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ ha₁ ha₆ hv₁ hv₆ r f₁ f₂ f₃ f₄ f₅ f₆
  exact ⟨hyeq.1,
    LayerB.CL2_WightmanAxioms.all_wightman_axioms_length,
    LayerB.CL3_CausalSetContinuum.μ_rho_linear ρ_cs β_cs c_cs W₁ W₂⟩

/-- Master synthesis of the `6 × 6` (`5 × 5 = 25` elementary plaquettes) mixed initial-and-final
higher-power resolvent plaquette grid, unconditional shifted-source residual-resolvent identity,
5-way operator-domain criterion for all real `m, g, k, t, s ∈ ℝ`, and the Wilson / Feshbach /
Volterra / Wightman / Clay continuum modules. -/
theorem sixBySix_plaquetteGrid_shiftedSource_residualResolvent_wightman_os_bridge_master
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆ q
     a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
     c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
     u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ : ℝ)
    (ha₁ : 0 < a₁) (ha₆ : 0 < a₆) (hv₁ : 0 < v₁) (hv₆ : 0 < v₆)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ : Hilbert) :
    (KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t₁ a₁ f₁ =
        KFCausalClockFloorResidualClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t₁ a₁
          (f₁ - (Real.exp (2 * t₁) : ℂ) •
            KFCausalClockFloorRadialYosidaDomain.operator ε hε h
              ⟨KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t₁ a₁ f₁,
                KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
                  ε hε h hh hb m g k t₁ a₁ ha₁ f₁⟩) ∧
      (KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t₁ a₁ f₁ ∈
          KFCausalClockFloorUnconditionalTwoTimeEvolution.commonOperatorDomain ε hε h hh hb m g k ↔
        KFCausalClockFloorResidualClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t₁ a₁
          (f₁ - (Real.exp (2 * t₁) : ℂ) •
            KFCausalClockFloorRadialYosidaDomain.operator ε hε h
              ⟨KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t₁ a₁ f₁,
                KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
                  ε hε h hh hb m g k t₁ a₁ ha₁ f₁⟩) ∈
          (KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k).domain) ∧
      KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t₁ a₁ f₁ ∈
        (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k t₁).domain ∧
      KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t₁ a₁ f₁ ∈
        (KFCausalClockFloorRadialYosidaDomain.operator ε hε h).domain ∧
      KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t₁ a₁ f₁ ∈
        (KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k t₁).domain ∧
      KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh (wide_bound ε hε h hb) m g k t₁ a₁ f₁ ∈
        (clockHalf ε).domain) ∧
      fiveByFiveResolventPlaquetteGridSum ε hε h hh hb m g k
          s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
          a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
          c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
          u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆ =
        mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
          s₁ s₆ t₁ t₆ a₁ a₆ v₁ v₆ r f₁ f₆ ∧
      fiveByFiveResolventPlaquetteGridSum ε hε h hh hb m g k
          s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₁
          a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
          c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
          u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆ ∈
        hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
      ‖fiveByFiveResolventPlaquetteGridSum ε hε h hh hb m g k
          s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
          a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
          c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
          u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆‖ ≤
        ((a₁⁻¹) ^ (r + 2) + (v₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
          ((a₆⁻¹) ^ (r + 2) + (v₆⁻¹) ^ (r + 2)) * ‖f₆‖ ∧
      ‖fiveByFiveIdentityPlaquetteGridSum ε hε h hh hb m g k
          s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
          a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
          c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
          u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₆‖ ∧
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
  have hshift :=
    KFCausalClockFloorHamiltonianResidualSecondResolventIdentity.hamiltonian_resolvent_eq_residual_resolvent_shifted_source
      ε hε h hh hb m g k t₁ a₁ ha₁ f₁
  have h5way :=
    KFCausalClockFloorHamiltonianResolventThreeOperatorSynthesis.hamiltonian_resolvent_five_way_domain_iff
      ε hε h hh hb m g k t₁ a₁ ha₁ f₁
  have hstokes := fiveByFivePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
    a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
    c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
    u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆
  have hweq := fiveByFiveResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ q
    a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
    c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
    u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ ha₁ ha₆ hv₁ hv₆ r f₁ f₂ f₃ f₄ f₅ f₆
  have hw_pl := fiveByFiveResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆ q
    a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
    c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
    u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ ha₁ ha₆ hv₁ hv₆ r f₁ f₂ f₃ f₄ f₅ f₆
  have hy_pl := fiveByFiveIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆ q
    a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
    c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
    u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ ha₁ ha₆ hv₁ hv₆ r f₁ f₂ f₃ f₄ f₅ f₆
  exact ⟨⟨hshift, h5way.2.2.2, h10.1, h10.2.1, h10.2.2.1, h10.2.2.2.2.2.2.2.2.2⟩,
    hstokes.1, hweq.1, hw_pl.2, hy_pl.2,
    LayerB.Build1_ExplicitWilsonAction.diamondLinkCount_eq_four,
    LayerB.Build2_HamiltonianFromAction.topEigenvalue_value,
    LayerB.Build6_VolterraBlockDiagonalDerivation.H_W_chamberBath_commutes,
    LayerB.CL1_BathSector.μ_vac_pos,
    LayerB.CL2_WightmanAxioms.all_wightman_axioms_length,
    LayerB.Clay3_PhysicalZ.perPlaquetteActionMax_pos⟩

#print axioms unconditional_shiftedSource_residualResolvent_fiveWayCriterion_and_threeOperatorNormBounds
#print axioms sixBySix_plaquetteGrid_stokes_with_alphaSAudit_andoGeometricMean_and_bTauReaudit
#print axioms sixBySix_identityPlaquetteGrid_stokes_with_wilsonAction_feshbach_and_volterraBlock
#print axioms equalOuterFinalTime_sixBySixResolventGrid_with_cfcDiagonal_ckmAudit_and_schur7
#print axioms equalOuterFinalTime_sixBySixIdentityGrid_with_cl2Wightman_and_cl3Continuum
#print axioms sixBySix_plaquetteGrid_shiftedSource_residualResolvent_wightman_os_bridge_master

end
end KFCausalClockFloorSixBySixPlaquetteShiftedSourceResidualResolventCriterionWightmanOSBridge
end Audit
end UnifiedTheory
