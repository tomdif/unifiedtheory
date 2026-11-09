/- Bridge of the Six-by-Six `(s₁, s₂, s₃, s₄, s₅, s₆) × (t₁, t₂, t₃, t₄, t₅, t₆)` (`5 × 5 = 25`
Elementary Plaquettes) Mixed Initial-and-Final Higher-Power Resolvent Plaquette Grid and 2D Stokes
Boundary Cancellation with the LayerB Multi-Link Hilbert, Matrix-Element Matching, Volterra Link
Search, Cluster Expansion, Interacting Wilson Measure, DLR Character Expansion, Pirogov-Sinai
Contours, Glimm-Jaffe Kotecký-Preiss Strategy, Higher Weingartens, KP5–KP7, Row-Permutation Symmetry,
Off-Diagonal Weingarten, and Volterra $SO(10)$ Embedding Modules. -/
import UnifiedTheory.Audit.KFCausalClockFloorSixBySixMixedInitialFinalHigherPowerResolventPlaquetteGrid
import UnifiedTheory.LayerB.Phase_A1_MultiLinkHilbert
import UnifiedTheory.LayerB.Phase_A4_MatrixElementMatching
import UnifiedTheory.LayerB.Phase_A6_VolterraLinkSearch
import UnifiedTheory.LayerB.Phase_C1_ClusterExpansion
import UnifiedTheory.LayerB.Phase_E2_InteractingWilsonMeasure
import UnifiedTheory.LayerB.Phase_E3_DLR_CharacterExpansion
import UnifiedTheory.LayerB.Phase_E3_DLR_PirogovSinai
import UnifiedTheory.LayerB.Phase_E3_GJConvergenceStrategy
import UnifiedTheory.LayerB.Phase_E3_HigherWeingartens
import UnifiedTheory.LayerB.Phase_E3_KP5
import UnifiedTheory.LayerB.Phase_E3_KP6
import UnifiedTheory.LayerB.Phase_E3_KP7
import UnifiedTheory.LayerB.Phase_E3_RowPermutationSymmetry_Proof
import UnifiedTheory.LayerB.Phase_E3_Weingarten_OffDiagonal_Proof
import UnifiedTheory.LayerB.R1_ChamberBathCommutes_FullYM
import UnifiedTheory.LayerB.R1_CharacterOrthogonality
import UnifiedTheory.LayerB.R1_VolterraSO10Embedding
import UnifiedTheory.LayerB.R1_VolterraSO10Embedding_Dim4Chamber
import UnifiedTheory.LayerB.R1_VolterraSO10Embedding_Dim6Full
import UnifiedTheory.LayerB.R1_VolterraSO10Embedding_DimExtension
import UnifiedTheory.LayerB.R2_SO10HaarIntegral

set_option autoImplicit false

namespace UnifiedTheory
namespace Audit
namespace KFCausalClockFloorSixBySixPlaquettePolymerBorgsImbrieKoteckyPreissWeingartenVolterraBridge

open scoped InnerProduct BigOperators
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorHigherPowerOperatorCores (hamiltonianPowerDomain)
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

/-- `6 × 6` resolvent plaquette grid 2D Stokes boundary cancellation paired with multi-link $L^2$
embedding isometry (`Phase_A1_MultiLinkHilbert`), chamber-to-$\iota_6$ injectivity
(`Phase_A4_MatrixElementMatching`), and $J_4$ target trace `14 / 15`
(`Phase_A6_VolterraLinkSearch`). -/
theorem sixBySix_plaquetteGrid_stokes_with_multiLinkHilbert_matrixMatching_and_volterraLinkSearch
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
     a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
     c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
     u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ : ℝ)
    (r L_link : ℕ) (i_link : Fin L_link) (f₁ f₂ f₃ f₄ f₅ f₆ : Hilbert)
    (f_lp : MeasureTheory.Lp ℝ 2 LayerB.R2b_SO10HaarConcreteConstruction.haarMeasureSO10) :
    fiveByFiveResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
        a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
        c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
        u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₆ t₁ t₆ a₁ a₆ v₁ v₆ r f₁ f₆ ∧
    ‖LayerB.Phase_A1_MultiLinkHilbert.embedAtLink L_link i_link f_lp‖ = ‖f_lp‖ ∧
    Function.Injective LayerB.Phase_A4_MatrixElementMatching.chamberToIota6 ∧
    LayerB.Phase_A6_VolterraLinkSearch.J4target ⟨0, by decide⟩ ⟨0, by decide⟩ +
      LayerB.Phase_A6_VolterraLinkSearch.J4target ⟨1, by decide⟩ ⟨1, by decide⟩ +
      LayerB.Phase_A6_VolterraLinkSearch.J4target ⟨2, by decide⟩ ⟨2, by decide⟩ = 14 / 15 := by
  have hstokes := fiveByFivePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
    a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
    c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
    u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆
  exact ⟨hstokes.1,
    LayerB.Phase_A1_MultiLinkHilbert.embedAtLink_norm L_link i_link f_lp,
    LayerB.Phase_A4_MatrixElementMatching.chamberToIota6_injective,
    LayerB.Phase_A6_VolterraLinkSearch.J4target_trace_eq⟩

/-- `6 × 6` identity plaquette grid 2D Stokes boundary cancellation paired with polymer size
positivity (`Phase_C1_ClusterExpansion`), trivial character coefficient at $\beta = 0$
(`Phase_E3_DLR_CharacterExpansion`), Pirogov-Sinai contour size positivity
(`Phase_E3_DLR_PirogovSinai`), and zero-activity Kotecký-Preiss condition
(`Phase_E3_GJConvergenceStrategy`). -/
theorem sixBySix_identityPlaquetteGrid_stokes_with_clusterExpansion_dlr_pirogovSinai_and_gjKP
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
     a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
     c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
     u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ : Hilbert)
    {L_lat : LayerB.Phase_C1_ClusterExpansion.LatticeSide}
    (P_poly : LayerB.Phase_C1_ClusterExpansion.Polymer L_lat)
    (γ_cnt : LayerB.Phase_E3_DLR_PirogovSinai.WilsonContour L_lat)
    (sys : LayerB.Phase_E3_GJConvergenceStrategy.AbstractPolymerSystem)
    (h_zero : ∀ γ : sys.Poly, sys.activity γ = 0) :
    fiveByFiveIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
        a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
        c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
        u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆ =
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₆ t₁ t₆ a₁ a₆ v₁ v₆ r f₁ f₆ ∧
    1 ≤ LayerB.Phase_C1_ClusterExpansion.polymerSize P_poly ∧
    LayerB.Phase_E3_DLR_CharacterExpansion.cCoef 0
      LayerB.Phase_A3_CasimirSpectrum.SO10Irrep.trivial = 1 ∧
    1 ≤ LayerB.Phase_E3_DLR_PirogovSinai.contourSize γ_cnt ∧
    LayerB.Phase_E3_GJConvergenceStrategy.KoteckyPreissCondition sys
      (fun _ => 0) (fun _ => 0) := by
  have hstokes := fiveByFivePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
    a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
    c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
    u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆
  exact ⟨hstokes.2,
    LayerB.Phase_C1_ClusterExpansion.polymerSize_pos P_poly,
    LayerB.Phase_E3_DLR_CharacterExpansion.c_trivial_at_zero,
    LayerB.Phase_E3_DLR_PirogovSinai.contourSize_pos γ_cnt,
    LayerB.Phase_E3_GJConvergenceStrategy.KP_holds_at_zero_activity sys h_zero⟩

/-- Equal-outer-final-time `Dom(H(t)^(r+2))` regularity of `fiveByFiveResolventPlaquetteGridSum`
paired with cubic $SO(10)$ Haar integral vanishing (`Phase_E3_HigherWeingartens`), KP5 activity
density nonnegativity (`Phase_E3_KP5`), KP6 action-to-projective consistency (`Phase_E3_KP6`), and
4D coordination number positivity (`Phase_E3_KP7`). -/
theorem equalOuterFinalTime_sixBySixResolventGrid_with_higherWeingartens_kp56_and_kp7Coord4D
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ t t₂ t₃ t₄ t₅ q
     a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
     c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
     u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ : ℝ)
    (ha₁ : 0 < a₁) (ha₆ : 0 < a₆) (hv₁ : 0 < v₁) (hv₆ : 0 < v₆)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ : Hilbert)
    (sys : LayerB.Phase_E3_GJConvergenceStrategy.AbstractPolymerSystem)
    (a_kp b_kp : sys.Poly → ℝ) (Λ_kp : Finset sys.Poly)
    (β_w : ℝ) (S_act : LayerB.Phase_E2_InteractingWilsonMeasure.WilsonActionAssignment) :
    fiveByFiveResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ t t₂ t₃ t₄ t₅ t
        a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
        c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
        u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆ ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    (∫ U : LayerB.R2b_SO10HaarConcreteConstruction.G_SO10,
      LayerB.Phase_E3_HigherWeingartens.traceCube U
        ∂LayerB.R2b_SO10HaarConcreteConstruction.haarMeasureSO10 = 0) ∧
    0 ≤ LayerB.Phase_E3_KP5.activitySum sys a_kp b_kp Λ_kp ∧
    0 ≤ LayerB.Phase_E3_KP5.activityDensity sys a_kp b_kp Λ_kp ∧
    (LayerB.Phase_E3_KP6.WilsonActionConsistency β_w S_act ↔
      LayerB.Phase_E2_InteractingWilsonMeasure.InteractingWilsonProjectiveConsistency β_w S_act) ∧
    0 < LayerB.Phase_E3_KP7.coord4D := by
  have hweq := fiveByFiveResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ t t₂ t₃ t₄ t₅ q
    a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
    c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
    u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ ha₁ ha₆ hv₁ hv₆ r f₁ f₂ f₃ f₄ f₅ f₆
  exact ⟨hweq.1,
    LayerB.Phase_E3_HigherWeingartens.trace_cubed_integral_zero,
    LayerB.Phase_E3_KP5.activitySum_nonneg sys a_kp b_kp Λ_kp,
    LayerB.Phase_E3_KP5.KP5_density_nonneg sys a_kp b_kp Λ_kp,
    LayerB.Phase_E3_KP6.wilsonActionConsistency_iff_projectiveConsistency β_w S_act,
    LayerB.Phase_E3_KP7.coord4D_pos⟩

/-- Equal-outer-final-time `Dom(H(t)^(r+2))` regularity of `fiveByFiveIdentityPlaquetteGridSum`
paired with unconditional $SO(10)$ row-permutation symmetry (`Phase_E3_RowPermutationSymmetry_Proof`),
unconditional off-diagonal Weingarten vanishing (`Phase_E3_Weingarten_OffDiagonal_Proof`), and
Wilson-Haar interface normalization (`R2_SO10HaarIntegral`). -/
theorem equalOuterFinalTime_sixBySixIdentityGrid_with_rowPermSymmetry_offDiagWeingarten_and_r2Haar
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ t t₂ t₃ t₄ t₅ q
     a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
     c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
     u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ : ℝ)
    (ha₁ : 0 < a₁) (ha₆ : 0 < a₆) (hv₁ : 0 < v₁) (hv₆ : 0 < v₆)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ : Hilbert)
    (I_haar : LayerB.R2_SO10HaarIntegral.WilsonHaarInterface) :
    fiveByFiveIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ t t₂ t₃ t₄ t₅ t
        a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
        c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
        u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆ ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    LayerB.Phase_E3_Weingarten_Diagonal.RowPermutationSymmetrySO10 ∧
    LayerB.Phase_E3_Weingarten_Diagonal.OffDiagonalDiagSquaredCorrelation 0 ∧
    (∫ _x, (1 : ℝ) ∂I_haar.μ = 1) := by
  have hyeq := fiveByFiveIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ t t₂ t₃ t₄ t₅ q
    a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
    c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
    u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ ha₁ ha₆ hv₁ hv₆ r f₁ f₂ f₃ f₄ f₅ f₆
  exact ⟨hyeq.1,
    LayerB.Phase_E3_RowPermutationSymmetry_Proof.rowPermutationSymmetrySO10_proved,
    LayerB.Phase_E3_Weingarten_OffDiagonal_Proof.offDiagonalDiagSquaredCorrelation_zero_proved,
    LayerB.R2_SO10HaarIntegral.interface_normalization I_haar⟩

/-- Cyclic 6-step initial-and-final plaquette hexagon cocycles paired with R1 chamber-bath label
vanishing (`R1_ChamberBathCommutes_FullYM`), $\mathbb{Z}_2$ central-character sign product
(`R1_CharacterOrthogonality`), Volterra $SO(10)$ $L^2$ orthogonality (`R1_VolterraSO10Embedding`),
and dim-4/dim-6 central-character parity (`R1_VolterraSO10Embedding_Dim4Chamber`,
`R1_VolterraSO10Embedding_Dim6Full`, `R1_VolterraSO10Embedding_DimExtension`). -/
theorem sixStepPlaquetteHexagonCocycles_with_r1ChamberBath_charOrthog_and_volterraSO10Embeddings
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
     a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆ c₁ c₂ e₁ e₂ u₁ u₂ v₁ v₂ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ : Hilbert) (i_ch : Fin 3) :
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ b₂ b₃ r f₂ f₃ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₃ s₄ t₁ t₂ a₃ a₄ b₃ b₄ r f₃ f₄ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₄ s₅ t₁ t₂ a₄ a₅ b₄ b₅ r f₄ f₅ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₅ s₆ t₁ t₂ a₅ a₆ b₅ b₆ r f₅ f₆ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₆ s₁ t₁ t₂ a₆ a₁ b₆ b₁ r f₆ f₁ = 0 ∧
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ b₁ b₂ c₁ c₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₃ t₄ c₁ c₂ e₁ e₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₄ t₅ e₁ e₂ u₁ u₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₅ t₆ u₁ u₂ v₁ v₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₆ t₁ v₁ v₂ a₁ a₂ r f₁ f₂ = 0 ∧
    LayerB.R1_ChamberBathCommutes_FullYM.chamberLabel
      (LayerB.Build3_ExplicitFeshbach.chamberIdx i_ch) = 0 ∧
    LayerB.R1_CharacterOrthogonality.IrrepZ2Class.signAtNegI .even *
      LayerB.R1_CharacterOrthogonality.IrrepZ2Class.signAtNegI .odd = -1 ∧
    (inner ℝ LayerB.R1_VolterraSO10Embedding.oneLp
      LayerB.R1_VolterraSO10Embedding.traceLp : ℝ) = 0 ∧
    LayerB.R1_CharacterOrthogonality.CarriesZ2CentralChar
      LayerB.R1_CharacterOrthogonality.IrrepZ2Class.even
      LayerB.R1_VolterraSO10Embedding_Dim4Chamber.f4 ∧
    LayerB.R1_CharacterOrthogonality.CarriesZ2CentralChar
      LayerB.R1_CharacterOrthogonality.IrrepZ2Class.odd
      LayerB.R1_VolterraSO10Embedding_Dim6Full.h1 ∧
    LayerB.R1_CharacterOrthogonality.CarriesZ2CentralChar
      LayerB.R1_CharacterOrthogonality.IrrepZ2Class.even
      LayerB.R1_VolterraSO10Embedding_DimExtension.f3 := by
  have hcoc := mixedInitialFinalHigherPowerPlaquette_six_initial_and_final_hexagon_cocycles
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
    a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆ c₁ c₂ e₁ e₂ u₁ u₂ v₁ v₂ r f₁ f₂ f₃ f₄ f₅ f₆
  exact ⟨hcoc.1, hcoc.2.2.1,
    LayerB.R1_ChamberBathCommutes_FullYM.chamberLabel_chamber_eq i_ch,
    LayerB.R1_CharacterOrthogonality.signAtNegI_even_times_odd,
    LayerB.R1_VolterraSO10Embedding.oneLp_traceLp_inner,
    LayerB.R1_VolterraSO10Embedding_Dim4Chamber.f4_carries_even,
    LayerB.R1_VolterraSO10Embedding_Dim6Full.h1_carries_odd,
    LayerB.R1_VolterraSO10Embedding_DimExtension.f3_carries_even⟩

/-- Master synthesis of the `6 × 6` (`5 × 5 = 25` elementary plaquettes) mixed initial-and-final
higher-power resolvent plaquette grid with the Polymer / Borgs-Imbrie / Kotecký-Preiss /
Weingarten / Volterra $SO(10)$ embedding modules. -/
theorem sixBySix_plaquetteGrid_polymer_borgsImbrie_koteckyPreiss_weingarten_volterra_bridge_master
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆ q
     a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
     c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
     u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ : ℝ)
    (ha₁ : 0 < a₁) (ha₆ : 0 < a₆) (hv₁ : 0 < v₁) (hv₆ : 0 < v₆)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ : Hilbert) :
    let w_grid := fiveByFiveResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
      a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
      c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
      u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆
    let w_grid_eq := fiveByFiveResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₁
      a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
      c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
      u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆
    w_grid = mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₆ t₁ t₆ a₁ a₆ v₁ v₆ r f₁ f₆ ∧
      w_grid_eq ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
      Function.Injective LayerB.Phase_A4_MatrixElementMatching.chamberToIota6 ∧
      LayerB.Phase_E3_DLR_CharacterExpansion.cCoef 0
        LayerB.Phase_A3_CasimirSpectrum.SO10Irrep.trivial = 1 ∧
      0 < LayerB.Phase_E3_KP7.coord4D ∧
      LayerB.Phase_E3_Weingarten_Diagonal.RowPermutationSymmetrySO10 ∧
      LayerB.Phase_E3_Weingarten_Diagonal.OffDiagonalDiagSquaredCorrelation 0 ∧
      LayerB.R1_CharacterOrthogonality.IrrepZ2Class.signAtNegI .even *
        LayerB.R1_CharacterOrthogonality.IrrepZ2Class.signAtNegI .odd = -1 ∧
      (inner ℝ LayerB.R1_VolterraSO10Embedding.oneLp
        LayerB.R1_VolterraSO10Embedding.traceLp : ℝ) = 0 := by
  intro w_grid w_grid_eq
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
  exact ⟨hstokes.1, hweq.1,
    LayerB.Phase_A4_MatrixElementMatching.chamberToIota6_injective,
    LayerB.Phase_E3_DLR_CharacterExpansion.c_trivial_at_zero,
    LayerB.Phase_E3_KP7.coord4D_pos,
    LayerB.Phase_E3_RowPermutationSymmetry_Proof.rowPermutationSymmetrySO10_proved,
    LayerB.Phase_E3_Weingarten_OffDiagonal_Proof.offDiagonalDiagSquaredCorrelation_zero_proved,
    LayerB.R1_CharacterOrthogonality.signAtNegI_even_times_odd,
    LayerB.R1_VolterraSO10Embedding.oneLp_traceLp_inner⟩

#print axioms sixBySix_plaquetteGrid_stokes_with_multiLinkHilbert_matrixMatching_and_volterraLinkSearch
#print axioms sixBySix_identityPlaquetteGrid_stokes_with_clusterExpansion_dlr_pirogovSinai_and_gjKP
#print axioms equalOuterFinalTime_sixBySixResolventGrid_with_higherWeingartens_kp56_and_kp7Coord4D
#print axioms equalOuterFinalTime_sixBySixIdentityGrid_with_rowPermSymmetry_offDiagWeingarten_and_r2Haar
#print axioms sixStepPlaquetteHexagonCocycles_with_r1ChamberBath_charOrthog_and_volterraSO10Embeddings
#print axioms sixBySix_plaquetteGrid_polymer_borgsImbrie_koteckyPreiss_weingarten_volterra_bridge_master

end KFCausalClockFloorSixBySixPlaquettePolymerBorgsImbrieKoteckyPreissWeingartenVolterraBridge
end Audit
end UnifiedTheory
