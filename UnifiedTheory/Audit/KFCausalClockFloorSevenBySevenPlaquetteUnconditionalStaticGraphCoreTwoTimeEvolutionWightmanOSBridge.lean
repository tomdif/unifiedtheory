/- Bridge of the Seven-by-Seven `(s₁, s₂, s₃, s₄, s₅, s₆, s₇) × (t₁, t₂, t₃, t₄, t₅, t₆, t₇)`
(`6 × 6 = 36` Elementary Plaquettes) Mixed Initial-and-Final Higher-Power Resolvent Plaquette Grid,
2D Stokes Boundary Cancellation, Unconditional Static Graph Core
`(commonOperatorClockStaticGraph).topologicalClosure = (T).graph`, Time-Invariant Pairwise Common
Domains, and Two-Time Evolution Differences (`S(t) x - S(s) x = (e^{2t} - e^{2s}) P x` and
`H(t) x - H(s) x = (e^{2t} - e^{2s}) (K x + P x)`) for All Real `m, g, k, t, s ∈ ℝ` (Including
`k ≤ 0` Without Iteration) with the LayerB Wilson-Action, Feshbach, Volterra Block-Diagonal,
Bath/Chamber Sector, Wightman, Causal-Set Continuum, and Clay Physical Partition Function Modules. -/
import UnifiedTheory.Audit.KFCausalClockFloorSevenBySevenMixedInitialFinalHigherPowerResolventPlaquetteGrid
import UnifiedTheory.Audit.KFCausalClockFloorStaticThreeOperatorCore
import UnifiedTheory.Audit.KFCausalClockFloorUnconditionalTwoTimeEvolution
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
namespace KFCausalClockFloorSevenBySevenPlaquetteUnconditionalStaticGraphCoreTwoTimeEvolutionWightmanOSBridge
noncomputable section

open scoped ComplexOrder
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorHigherPowerOperatorCores (hamiltonianPowerDomain)
open KFCausalClockFloorStaticThreeOperatorCore
  (packet
   packet_mem_commonOperatorClockDomain
   commonOperatorStaticGraph
   commonOperatorClockStaticGraph
   commonOperatorClockStaticHamiltonianGraph
   common_operator_static_graph_core
   common_operator_clock_static_graph_core
   common_operator_clock_static_hamiltonian_graph_core)
open KFCausalClockFloorUnconditionalTwoTimeEvolution
  (commonOperatorDomain
   common_domain_subset_hamiltonian
   common_domain_subset_residual
   common_domain_subset_growing
   hamiltonian_static_common_time_invariant
   hamiltonian_growing_common_time_invariant
   hamiltonian_potential_common_time_invariant
   unconditional_two_time_residual_difference
   unconditional_two_time_hamiltonian_growing_difference
   unconditional_two_time_hamiltonian_three_operator_difference)
open KFCausalClockFloorTwoTimeMixedInitialFinalHigherPowerResolventPlaquette
  (mixedInitialFinalHigherPowerResolventPlaquette
   mixedInitialFinalHigherPowerIdentityPlaquette)
open KFCausalClockFloorSevenBySevenMixedInitialFinalHigherPowerResolventPlaquetteGrid
  (sixBySixResolventPlaquetteGridSum
   sixBySixIdentityPlaquetteGridSum
   sixBySixPlaquetteGridSum_stokes_boundary_cancellation
   mixedInitialFinalHigherPowerPlaquette_seven_initial_and_final_heptagon_cocycles
   sixBySixResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
   sixBySixIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
   sixBySixResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
   sixBySixIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains)

/-- **Unconditional Static Graph Core, Displaced-Gaussian Common-Domain Density, Time-Invariant
Pairwise Common Domains, and Two-Time Evolution Decomposition (`k ∈ ℝ` Arbitrary)**:
For all real parameters `m, g, k, t, s ∈ ℝ` (including nonpositive `k ≤ 0` without any resolvent
iteration), every `a > 0`, every displaced Gaussian packet index `k_pkt : Joint 5 1`, and every
`x : Hilbert` with `hx : x ∈ commonOperatorDomain ε hε h hh hb m g k`:
1. Every displaced Gaussian packet belongs to `commonOperatorDomain ε hε h hh hb m g k ⊓ (clockHalf ε).domain`,
   and the restrictions of `T` and `Tham(t)` to `commonOperatorDomain ⊓ Dom(clockHalf)` are operator
   graph cores:
   `(commonOperatorClockStaticGraph ε hε h hh hb m g k).topologicalClosure = (T).graph`,
   `(commonOperatorStaticGraph ε hε h hh hb m g k).topologicalClosure = (T).graph`, and
   `(commonOperatorClockStaticHamiltonianGraph ε hε h hh hb m g k t).topologicalClosure = (Tham t).graph`;
2. All pairwise common domains of `H(t)` with `T`, `G`, and `P` are time-invariant across `(t, s)`:
   `(H t).domain ⊓ (T).domain = (H s).domain ⊓ (T).domain`,
   `(H t).domain ⊓ (G).domain = (H s).domain ⊓ (G).domain`, and
   `(H t).domain ⊓ (P).domain = (H s).domain ⊓ (P).domain`;
3. On `commonOperatorDomain ε hε h hh hb m g k`, the exact two-time evolution differences hold:
   `S t ⟨x, _⟩ - S s ⟨x, _⟩ = ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) • P ⟨x, hx.1.2⟩`,
   `H t ⟨x, _⟩ - H s ⟨x, _⟩ = ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) • G ⟨x, _⟩`, and
   `H t ⟨x, _⟩ - H s ⟨x, _⟩ = ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) • (K ⟨x, hx.1.1.2⟩ + P ⟨x, hx.1.2⟩)`. -/
theorem unconditional_staticGraphCore_timeInvariantCommonDomains_and_twoTimeEvolutionDifferences
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3)
    (m g k t s a : ℝ) (ha : 0 < a) (k_pkt : Joint 5 1)
    (k_vol : ℕ) (hk_vol : 1 ≤ k_vol)
    (x : Hilbert) (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    (packet ε hε h hh a ha k_pkt ∈
        commonOperatorDomain ε hε h hh hb m g k ⊓ (clockHalf ε).domain ∧
      (commonOperatorClockStaticGraph ε hε h hh hb m g k).topologicalClosure =
        (KFCausalClockFloorStaticOperator.operator ε hε h).graph ∧
      (commonOperatorStaticGraph ε hε h hh hb m g k).topologicalClosure =
        (KFCausalClockFloorStaticOperator.operator ε hε h).graph ∧
      (commonOperatorClockStaticHamiltonianGraph ε hε h hh hb m g k t).topologicalClosure =
        (KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k t).graph) ∧
    ((KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k t).domain ⊓
        (KFCausalClockFloorStaticOperator.operator ε hε h).domain =
      (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k s).domain ⊓
        (KFCausalClockFloorStaticOperator.operator ε hε h).domain ∧
      (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k t).domain ⊓
        (KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k).domain =
      (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k s).domain ⊓
        (KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k).domain ∧
      (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k t).domain ⊓
        (KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k).domain =
      (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k s).domain ⊓
        (KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k).domain) ∧
    (KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k t
        ⟨x, common_domain_subset_residual ε hε h hh hb m g k t hx⟩ -
      KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k s
        ⟨x, common_domain_subset_residual ε hε h hh hb m g k s hx⟩ =
        ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) •
          (KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k)
            ⟨x, hx.1.2⟩ ∧
      KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k t
        ⟨x, common_domain_subset_hamiltonian ε hε h hh hb m g k t hx⟩ -
      KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k s
        ⟨x, common_domain_subset_hamiltonian ε hε h hh hb m g k s hx⟩ =
        ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) •
          (KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k)
            ⟨x, common_domain_subset_growing ε hε h hh hb m g k hx⟩ ∧
      KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k t
        ⟨x, common_domain_subset_hamiltonian ε hε h hh hb m g k t hx⟩ -
      KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k s
        ⟨x, common_domain_subset_hamiltonian ε hε h hh hb m g k s hx⟩ =
        ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) •
          ((KFCausalClockFloorRadialYosidaDomain.operator ε hε h) ⟨x, hx.1.1.2⟩ +
            (KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k)
              ⟨x, hx.1.2⟩)) ∧
    0 < LayerB.CL1_BathSector.μ_vac ∧
    0 < LayerB.CL1_ChamberLowestSector.volterra_sigma k_vol ∧
    LayerB.CL2_WightmanAxioms.all_wightman_axioms.length = 7 ∧
    0 < LayerB.Clay3_PhysicalZ.perPlaquetteActionMax := by
  exact ⟨⟨packet_mem_commonOperatorClockDomain ε hε h hh hb m g k a ha k_pkt,
      common_operator_clock_static_graph_core ε hε h hh hb m g k,
      common_operator_static_graph_core ε hε h hh hb m g k,
      common_operator_clock_static_hamiltonian_graph_core ε hε h hh hb m g k t⟩,
    ⟨hamiltonian_static_common_time_invariant ε hε h hh hb m g k t s,
      hamiltonian_growing_common_time_invariant ε hε h hh hb m g k t s,
      hamiltonian_potential_common_time_invariant ε hε h hh hb m g k t s⟩,
    ⟨unconditional_two_time_residual_difference ε hε h hh hb m g k t s x hx,
      unconditional_two_time_hamiltonian_growing_difference ε hε h hh hb m g k t s x hx,
      unconditional_two_time_hamiltonian_three_operator_difference ε hε h hh hb m g k t s x hx⟩,
    LayerB.CL1_BathSector.μ_vac_pos,
    LayerB.CL1_ChamberLowestSector.volterra_sigma_pos k_vol hk_vol,
    LayerB.CL2_WightmanAxioms.all_wightman_axioms_length,
    LayerB.Clay3_PhysicalZ.perPlaquetteActionMax_pos⟩

/-- `7 × 7` (`6 × 6 = 36` elementary plaquettes) resolvent plaquette grid 2D Stokes boundary
cancellation paired with $\alpha_s$ audit (`AlphaSAudit`), Ando geometric mean positivity
(`AndoGeometricMean`), anomaly audit (`AnomalyAudit`), and $b/\tau$ discriminant ratio
(`BTauReaudit`). -/
theorem sevenBySeven_plaquetteGrid_stokes_with_alphaSAudit_andoGeometricMean_and_bTauReaudit
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ : Hilbert)
    {n_mat : ℕ} {A B : Matrix (Fin n_mat) (Fin n_mat) ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    sixBySixResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₇ t₁ t₇ a₁ a₇ w₁ w₇ r f₁ f₇ ∧
    LayerB.AlphaSAudit.NW = 2 ∧
    LayerB.AlphaSAudit.Nc = 3 ∧
    (LayerB.AndoGeometricMean.geometricMean A B).PosSemidef ∧
    LayerB.AnomalyAudit.N_W = 2 ∧
    (7 : ℤ) = LayerA.FeshbachJ4.feshbach_disc LayerB.BTauReaudit.d_eff := by
  have hstokes := sixBySixPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
  exact ⟨hstokes.1,
    LayerB.AlphaSAudit.NW_eq,
    LayerB.AlphaSAudit.Nc_eq,
    LayerB.AndoGeometricMean.geometricMean_posSemidef hA hB,
    LayerB.AnomalyAudit.N_W_eq,
    LayerB.BTauReaudit.seven_eq_feshbach_disc_d_eff⟩

/-- `7 × 7` (`6 × 6 = 36` elementary plaquettes) identity plaquette grid 2D Stokes boundary
cancellation paired with explicit Wilson diamond link count (`Build1_ExplicitWilsonAction`),
Wilson top eigenvalue `3 / 5` (`Build2_HamiltonianFromAction`), Feshbach chamber-bath partition
(`Build3_ExplicitFeshbach`), and Volterra block-diagonal commutativity
(`Build6_VolterraBlockDiagonalDerivation`). -/
theorem sevenBySeven_identityPlaquetteGrid_stokes_with_wilsonAction_feshbach_and_volterraBlock
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ : Hilbert)
    (i_idx : Fin 3) :
    sixBySixIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ =
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₇ t₁ t₇ a₁ a₇ w₁ w₇ r f₁ f₇ ∧
    LayerB.Build1_ExplicitWilsonAction.diamondLinkCount = 4 ∧
    LayerB.Build2_HamiltonianFromAction.wilsonHamiltonian.topEigenvalue = 3 / 5 ∧
    LayerB.Build3_ExplicitFeshbach.isChamber (LayerB.Build3_ExplicitFeshbach.chamberIdx i_idx) ∧
    LayerB.Build6_VolterraBlockDiagonalDerivation.ChamberBathCommutes
      LayerB.Build3_ExplicitFeshbach.H_W := by
  have hstokes := sixBySixPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
  exact ⟨hstokes.2,
    LayerB.Build1_ExplicitWilsonAction.diamondLinkCount_eq_four,
    LayerB.Build2_HamiltonianFromAction.topEigenvalue_value,
    LayerB.Build3_ExplicitFeshbach.chamberIdx_isChamber i_idx,
    LayerB.Build6_VolterraBlockDiagonalDerivation.H_W_chamberBath_commutes⟩

/-- Equal-outer-final-time `Dom(H(t)^(r+2))` regularity of `sixBySixResolventPlaquetteGridSum`
paired with diagonal CFC discharge (`CFCDiagonalDischarge`), CKM complete audit `V_us^2 = 1/20`
(`CKMCompleteAudit`), CKM pre-registration brackets (`CKMPreRegistration`), and 7-state Schur
coupling (`CKMSchur7`). -/
theorem equalOuterFinalTime_sevenBySevenResolventGrid_with_cfcDiagonal_ckmAudit_and_schur7
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ t t₂ t₃ t₄ t₅ t₆ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ : ℝ)
    (ha₁ : 0 < a₁) (ha₇ : 0 < a₇) (hw₁ : 0 < w₁) (hw₇ : 0 < w₇)
    (r n_cfc : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ : Hilbert)
    (s_schur : LayerB.CKMSchur7.SevenStateCoupled) :
    sixBySixResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ t t₂ t₃ t₄ t₅ t₆ t
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    LayerB.UmegakiDiagonalBridge.CFCOnDiagonalIsEntrywise n_cfc Real.log ∧
    LayerB.CKMCompleteAudit.Vus2_min = 1 / 20 ∧
    (4.582 < Real.sqrt 21 ∧ Real.sqrt 21 < 4.583) ∧
    s_schur.H 2 4 = 0 := by
  have hweq := sixBySixResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ t t₂ t₃ t₄ t₅ t₆ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ ha₁ ha₇ hw₁ hw₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
  exact ⟨hweq.1,
    LayerB.CFCDiagonalDischarge.cfcOnDiagonalIsEntrywise_log n_cfc,
    LayerB.CKMCompleteAudit.Vus2_min_value,
    LayerB.CKMPreRegistration.sqrt21_bracket,
    LayerB.CKMSchur7.H_up3_down2_zero s_schur⟩

/-- Equal-outer-final-time `Dom(H(t)^(r+2))` regularity of `sixBySixIdentityPlaquetteGridSum`
paired with causal-set continuum functional linearity (`CL3_CausalSetContinuum`) and Wightman
7-axiom list (`CL2_WightmanAxioms`). -/
theorem equalOuterFinalTime_sevenBySevenIdentityGrid_with_cl2Wightman_and_cl3Continuum
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ t t₂ t₃ t₄ t₅ t₆ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ : ℝ)
    (ha₁ : 0 < a₁) (ha₇ : 0 < a₇) (hw₁ : 0 < w₁) (hw₇ : 0 < w₇)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ : Hilbert)
    (ρ_cs β_cs c_cs W₁ W₂ : ℝ) :
    sixBySixIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ t t₂ t₃ t₄ t₅ t₆ t
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    LayerB.CL2_WightmanAxioms.all_wightman_axioms.length = 7 ∧
    LayerB.CL3_CausalSetContinuum.μ_rho ρ_cs β_cs (c_cs * W₁ + W₂) =
      c_cs * LayerB.CL3_CausalSetContinuum.μ_rho ρ_cs β_cs W₁ +
        LayerB.CL3_CausalSetContinuum.μ_rho ρ_cs β_cs W₂ := by
  have hyeq := sixBySixIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ t t₂ t₃ t₄ t₅ t₆ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ ha₁ ha₇ hw₁ hw₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
  exact ⟨hyeq.1,
    LayerB.CL2_WightmanAxioms.all_wightman_axioms_length,
    LayerB.CL3_CausalSetContinuum.μ_rho_linear ρ_cs β_cs c_cs W₁ W₂⟩

/-- Master synthesis of the `7 × 7` (`6 × 6 = 36` elementary plaquettes) mixed initial-and-final
higher-power resolvent plaquette grid, unconditional static graph core, time-invariant pairwise
common domains, two-time evolution decomposition for all real `m, g, k, t, s ∈ ℝ`, and the
Wilson / Feshbach / Volterra / Wightman / Clay continuum modules. -/
theorem sevenBySeven_plaquetteGrid_unconditional_staticGraphCore_twoTimeEvolution_wightman_os_bridge_master
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ : ℝ)
    (ha₁ : 0 < a₁) (ha₇ : 0 < a₇) (hw₁ : 0 < w₁) (hw₇ : 0 < w₇)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ : Hilbert)
    (x : Hilbert) (hx : x ∈ commonOperatorDomain ε hε h hh hb m g k) :
    ((commonOperatorClockStaticGraph ε hε h hh hb m g k).topologicalClosure =
        (KFCausalClockFloorStaticOperator.operator ε hε h).graph ∧
      (commonOperatorClockStaticHamiltonianGraph ε hε h hh hb m g k t₁).topologicalClosure =
        (KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k t₁).graph ∧
      (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k t₁).domain ⊓
          (KFCausalClockFloorStaticOperator.operator ε hε h).domain =
        (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k s₁).domain ⊓
          (KFCausalClockFloorStaticOperator.operator ε hε h).domain ∧
      KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k t₁
          ⟨x, common_domain_subset_residual ε hε h hh hb m g k t₁ hx⟩ -
        KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k s₁
          ⟨x, common_domain_subset_residual ε hε h hh hb m g k s₁ hx⟩ =
        ((Real.exp (2 * t₁) - Real.exp (2 * s₁) : ℝ) : ℂ) •
          (KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k)
            ⟨x, hx.1.2⟩ ∧
      KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k t₁
          ⟨x, common_domain_subset_hamiltonian ε hε h hh hb m g k t₁ hx⟩ -
        KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k s₁
          ⟨x, common_domain_subset_hamiltonian ε hε h hh hb m g k s₁ hx⟩ =
        ((Real.exp (2 * t₁) - Real.exp (2 * s₁) : ℝ) : ℂ) •
          ((KFCausalClockFloorRadialYosidaDomain.operator ε hε h) ⟨x, hx.1.1.2⟩ +
            (KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh (wide_bound ε hε h hb) m g k)
              ⟨x, hx.1.2⟩)) ∧
      sixBySixResolventPlaquetteGridSum ε hε h hh hb m g k
          s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
          a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
          c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
          u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
          w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ =
        mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
          s₁ s₇ t₁ t₇ a₁ a₇ w₁ w₇ r f₁ f₇ ∧
      sixBySixResolventPlaquetteGridSum ε hε h hh hb m g k
          s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₁
          a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
          c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
          u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
          w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ ∈
        hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
      ‖sixBySixResolventPlaquetteGridSum ε hε h hh hb m g k
          s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
          a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
          c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
          u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
          w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇‖ ≤
        ((a₁⁻¹) ^ (r + 2) + (w₁⁻¹) ^ (r + 2)) * ‖f₁‖ +
          ((a₇⁻¹) ^ (r + 2) + (w₇⁻¹) ^ (r + 2)) * ‖f₇‖ ∧
      ‖sixBySixIdentityPlaquetteGridSum ε hε h hh hb m g k
          s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
          a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
          c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
          u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
          w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₇‖ ∧
      LayerB.Build1_ExplicitWilsonAction.diamondLinkCount = 4 ∧
      LayerB.Build2_HamiltonianFromAction.wilsonHamiltonian.topEigenvalue = 3 / 5 ∧
      LayerB.Build6_VolterraBlockDiagonalDerivation.ChamberBathCommutes
        LayerB.Build3_ExplicitFeshbach.H_W ∧
      0 < LayerB.CL1_BathSector.μ_vac ∧
      LayerB.CL2_WightmanAxioms.all_wightman_axioms.length = 7 ∧
      0 < LayerB.Clay3_PhysicalZ.perPlaquetteActionMax := by
  have hstokes := sixBySixPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
  have hweq := sixBySixResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ ha₁ ha₇ hw₁ hw₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
  have hw_pl := sixBySixResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ ha₁ ha₇ hw₁ hw₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
  have hy_pl := sixBySixIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ ha₁ ha₇ hw₁ hw₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
  exact ⟨⟨common_operator_clock_static_graph_core ε hε h hh hb m g k,
      common_operator_clock_static_hamiltonian_graph_core ε hε h hh hb m g k t₁,
      hamiltonian_static_common_time_invariant ε hε h hh hb m g k t₁ s₁,
      unconditional_two_time_residual_difference ε hε h hh hb m g k t₁ s₁ x hx,
      unconditional_two_time_hamiltonian_three_operator_difference ε hε h hh hb m g k t₁ s₁ x hx⟩,
    hstokes.1, hweq.1, hw_pl.2, hy_pl.2,
    LayerB.Build1_ExplicitWilsonAction.diamondLinkCount_eq_four,
    LayerB.Build2_HamiltonianFromAction.topEigenvalue_value,
    LayerB.Build6_VolterraBlockDiagonalDerivation.H_W_chamberBath_commutes,
    LayerB.CL1_BathSector.μ_vac_pos,
    LayerB.CL2_WightmanAxioms.all_wightman_axioms_length,
    LayerB.Clay3_PhysicalZ.perPlaquetteActionMax_pos⟩

#print axioms unconditional_staticGraphCore_timeInvariantCommonDomains_and_twoTimeEvolutionDifferences
#print axioms sevenBySeven_plaquetteGrid_stokes_with_alphaSAudit_andoGeometricMean_and_bTauReaudit
#print axioms sevenBySeven_identityPlaquetteGrid_stokes_with_wilsonAction_feshbach_and_volterraBlock
#print axioms equalOuterFinalTime_sevenBySevenResolventGrid_with_cfcDiagonal_ckmAudit_and_schur7
#print axioms equalOuterFinalTime_sevenBySevenIdentityGrid_with_cl2Wightman_and_cl3Continuum
#print axioms sevenBySeven_plaquetteGrid_unconditional_staticGraphCore_twoTimeEvolution_wightman_os_bridge_master

end
end KFCausalClockFloorSevenBySevenPlaquetteUnconditionalStaticGraphCoreTwoTimeEvolutionWightmanOSBridge
end Audit
end UnifiedTheory
