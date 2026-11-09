/- Bridge of the Thirteen-by-Thirteen `(s₁..s₁₃) × (t₁..t₁₃)` (`12 × 12 = 144` Elementary Plaquettes)
Mixed Initial-and-Final Higher-Power Resolvent Plaquette Grid and 2D Stokes Boundary Cancellation
with the LayerB Multi-Link Hilbert, Matrix-Element Matching, Volterra Link Search, Cluster Expansion,
Interacting Wilson Measure, DLR Character Expansion, Pirogov-Sinai Contours, Glimm-Jaffe Kotecký-Preiss
Strategy, Higher Weingartens, KP5–KP7, Row-Permutation Symmetry, Off-Diagonal Weingarten, and Volterra
$SO(10)$ Embedding Modules. -/
import UnifiedTheory.Audit.KFCausalClockFloorThirteenByThirteenMixedInitialFinalHigherPowerResolventPlaquetteGrid
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

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory
namespace Audit
namespace KFCausalClockFloorThirteenByThirteenPlaquettePolymerBorgsImbrieKoteckyPreissWeingartenVolterraBridge

open scoped InnerProduct BigOperators
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorHigherPowerOperatorCores (hamiltonianPowerDomain)
open KFCausalClockFloorTwoTimeMixedInitialFinalHigherPowerResolventPlaquette
  (mixedInitialFinalHigherPowerResolventPlaquette
   mixedInitialFinalHigherPowerIdentityPlaquette)
open KFCausalClockFloorThirteenByThirteenMixedInitialFinalHigherPowerResolventPlaquetteGrid
  (twelveByTwelveResolventPlaquetteGridSum
   twelveByTwelveIdentityPlaquetteGridSum
   twelveByTwelvePlaquetteGridSum_stokes_boundary_cancellation
   mixedInitialFinalHigherPowerPlaquette_thirteen_initial_and_final_tridecagon_cocycles
   twelveByTwelveResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
   twelveByTwelveIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
   twelveByTwelveResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
   twelveByTwelveIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains)

/-- `13 × 13` resolvent plaquette grid 2D Stokes boundary cancellation paired with multi-link $L^2$
embedding isometry (`Phase_A1_MultiLinkHilbert`), chamber-to-$\iota_6$ injectivity
(`Phase_A4_MatrixElementMatching`), and $J_4$ target trace `14 / 15`
(`Phase_A6_VolterraLinkSearch`). -/
theorem thirteenByThirteen_plaquetteGrid_stokes_with_multiLinkHilbert_matrixMatching_and_volterraLinkSearch
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
     p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
     l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃ : ℝ)
    (r L_link : ℕ) (i_link : Fin L_link) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ : Hilbert)
    (f_lp : MeasureTheory.Lp ℝ 2 LayerB.R2b_SO10HaarConcreteConstruction.haarMeasureSO10) :
    twelveByTwelveResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
        y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
        p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
        l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₁₃ t₁ t₁₃ a₁ a₁₃ l₁ l₁₃ r f₁ f₁₃ ∧
    ‖LayerB.Phase_A1_MultiLinkHilbert.embedAtLink L_link i_link f_lp‖ = ‖f_lp‖ ∧
    Function.Injective LayerB.Phase_A4_MatrixElementMatching.chamberToIota6 ∧
    LayerB.Phase_A6_VolterraLinkSearch.J4target ⟨0, by decide⟩ ⟨0, by decide⟩ +
      LayerB.Phase_A6_VolterraLinkSearch.J4target ⟨1, by decide⟩ ⟨1, by decide⟩ +
      LayerB.Phase_A6_VolterraLinkSearch.J4target ⟨2, by decide⟩ ⟨2, by decide⟩ = 14 / 15 := by
  have hstokes := twelveByTwelvePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
    l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
  exact ⟨hstokes.1,
    LayerB.Phase_A1_MultiLinkHilbert.embedAtLink_norm L_link i_link f_lp,
    LayerB.Phase_A4_MatrixElementMatching.chamberToIota6_injective,
    LayerB.Phase_A6_VolterraLinkSearch.J4target_trace_eq⟩

/-- `13 × 13` identity plaquette grid 2D Stokes boundary cancellation paired with polymer size
positivity (`Phase_C1_ClusterExpansion`), trivial character coefficient at $\beta = 0$
(`Phase_E3_DLR_CharacterExpansion`), Pirogov-Sinai contour size positivity
(`Phase_E3_DLR_PirogovSinai`), and zero-activity Kotecký-Preiss condition
(`Phase_E3_GJConvergenceStrategy`). -/
theorem thirteenByThirteen_identityPlaquetteGrid_stokes_with_clusterExpansion_dlr_pirogovSinai_and_gjKP
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
     p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
     l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ : Hilbert)
    {L_lat : LayerB.Phase_C1_ClusterExpansion.LatticeSide}
    (P_poly : LayerB.Phase_C1_ClusterExpansion.Polymer L_lat)
    (γ_cnt : LayerB.Phase_E3_DLR_PirogovSinai.WilsonContour L_lat)
    (sys : LayerB.Phase_E3_GJConvergenceStrategy.AbstractPolymerSystem)
    (h_zero : ∀ γ : sys.Poly, sys.activity γ = 0) :
    twelveByTwelveIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
        y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
        p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
        l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ =
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₁₃ t₁ t₁₃ a₁ a₁₃ l₁ l₁₃ r f₁ f₁₃ ∧
    1 ≤ LayerB.Phase_C1_ClusterExpansion.polymerSize P_poly ∧
    LayerB.Phase_E3_DLR_CharacterExpansion.cCoef 0
      LayerB.Phase_A3_CasimirSpectrum.SO10Irrep.trivial = 1 ∧
    1 ≤ LayerB.Phase_E3_DLR_PirogovSinai.contourSize γ_cnt ∧
    LayerB.Phase_E3_GJConvergenceStrategy.KoteckyPreissCondition sys
      (fun _ => 0) (fun _ => 0) := by
  have hstokes := twelveByTwelvePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
    l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
  exact ⟨hstokes.2,
    LayerB.Phase_C1_ClusterExpansion.polymerSize_pos P_poly,
    LayerB.Phase_E3_DLR_CharacterExpansion.c_trivial_at_zero,
    LayerB.Phase_E3_DLR_PirogovSinai.contourSize_pos γ_cnt,
    LayerB.Phase_E3_GJConvergenceStrategy.KP_holds_at_zero_activity sys h_zero⟩

/-- Equal-outer-final-time `Dom(H(t)^(r+2))` regularity of `twelveByTwelveResolventPlaquetteGridSum`
paired with cubic $SO(10)$ Haar integral vanishing (`Phase_E3_HigherWeingartens`), KP5 activity
density nonnegativity (`Phase_E3_KP5`), KP6 action-to-projective consistency (`Phase_E3_KP6`), and
4D coordination number positivity (`Phase_E3_KP7`). -/
theorem equalOuterFinalTime_thirteenByThirteenResolventGrid_with_higherWeingartens_kp56_and_kp7Coord4D
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
     p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
     l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃ : ℝ)
    (ha₁ : 0 < a₁) (ha₁₃ : 0 < a₁₃) (hl₁ : 0 < l₁) (hl₁₃ : 0 < l₁₃)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ : Hilbert)
    (sys : LayerB.Phase_E3_GJConvergenceStrategy.AbstractPolymerSystem)
    (a_kp b_kp : sys.Poly → ℝ) (Λ_kp : Finset sys.Poly)
    (β_w : ℝ) (S_act : LayerB.Phase_E2_InteractingWilsonMeasure.WilsonActionAssignment) :
    twelveByTwelveResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
        y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
        p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
        l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    (∫ U : LayerB.R2b_SO10HaarConcreteConstruction.G_SO10,
      LayerB.Phase_E3_HigherWeingartens.traceCube U
        ∂LayerB.R2b_SO10HaarConcreteConstruction.haarMeasureSO10 = 0) ∧
    0 ≤ LayerB.Phase_E3_KP5.activitySum sys a_kp b_kp Λ_kp ∧
    0 ≤ LayerB.Phase_E3_KP5.activityDensity sys a_kp b_kp Λ_kp ∧
    (LayerB.Phase_E3_KP6.WilsonActionConsistency β_w S_act ↔
      LayerB.Phase_E2_InteractingWilsonMeasure.InteractingWilsonProjectiveConsistency β_w S_act) ∧
    0 < LayerB.Phase_E3_KP7.coord4D := by
  have hweq := twelveByTwelveResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
    l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
    ha₁ ha₁₃ hl₁ hl₁₃ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
  exact ⟨hweq.1,
    LayerB.Phase_E3_HigherWeingartens.trace_cubed_integral_zero,
    LayerB.Phase_E3_KP5.activitySum_nonneg sys a_kp b_kp Λ_kp,
    LayerB.Phase_E3_KP5.KP5_density_nonneg sys a_kp b_kp Λ_kp,
    LayerB.Phase_E3_KP6.wilsonActionConsistency_iff_projectiveConsistency β_w S_act,
    LayerB.Phase_E3_KP7.coord4D_pos⟩

/-- Equal-outer-final-time `Dom(H(t)^(r+2))` regularity of `twelveByTwelveIdentityPlaquetteGridSum`
paired with unconditional $SO(10)$ row-permutation symmetry (`Phase_E3_RowPermutationSymmetry_Proof`),
unconditional off-diagonal Weingarten vanishing (`Phase_E3_Weingarten_OffDiagonal_Proof`), and
Wilson-Haar interface normalization (`R2_SO10HaarIntegral`). -/
theorem equalOuterFinalTime_thirteenByThirteenIdentityGrid_with_rowPermSymmetry_offDiagWeingarten_and_r2Haar
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
     p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
     l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃ : ℝ)
    (ha₁ : 0 < a₁) (ha₁₃ : 0 < a₁₃) (hl₁ : 0 < l₁) (hl₁₃ : 0 < l₁₃)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ : Hilbert)
    (I_haar : LayerB.R2_SO10HaarIntegral.WilsonHaarInterface) :
    twelveByTwelveIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
        y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
        p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
        l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
        r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    LayerB.Phase_E3_Weingarten_Diagonal.RowPermutationSymmetrySO10 ∧
    LayerB.Phase_E3_Weingarten_Diagonal.OffDiagonalDiagSquaredCorrelation 0 ∧
    (∫ _x, (1 : ℝ) ∂I_haar.μ = 1) := by
  have hyeq := twelveByTwelveIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
    l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
    ha₁ ha₁₃ hl₁ hl₁₃ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
  exact ⟨hyeq.1,
    LayerB.Phase_E3_RowPermutationSymmetry_Proof.rowPermutationSymmetrySO10_proved,
    LayerB.Phase_E3_Weingarten_OffDiagonal_Proof.offDiagonalDiagSquaredCorrelation_zero_proved,
    LayerB.R2_SO10HaarIntegral.interface_normalization I_haar⟩

/-- Cyclic 13-step initial-and-final plaquette tridecagon cocycles paired with R1 chamber-bath label
vanishing (`R1_ChamberBathCommutes_FullYM`), $\mathbb{Z}_2$ central-character sign product
(`R1_CharacterOrthogonality`), Volterra $SO(10)$ $L^2$ orthogonality (`R1_VolterraSO10Embedding`),
and dim-4/dim-6 central-character parity (`R1_VolterraSO10Embedding_Dim4Chamber`,
`R1_VolterraSO10Embedding_Dim6Full`, `R1_VolterraSO10Embedding_DimExtension`). -/
theorem thirteenStepPlaquetteTridecagonCocycles_with_r1ChamberBath_charOrthog_and_volterraSO10Embeddings
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
     c₁ c₂ e₁ e₂ u₁ u₂ v₁ v₂ w₁ w₂ z₁ z₂ y₁ y₂ x₁ x₂ p₁ p₂ d₁ d₂ l₁ l₂ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ : Hilbert) (i_ch : Fin 3) :
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ b₂ b₃ r f₂ f₃ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₃ s₄ t₁ t₂ a₃ a₄ b₃ b₄ r f₃ f₄ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₄ s₅ t₁ t₂ a₄ a₅ b₄ b₅ r f₄ f₅ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₅ s₆ t₁ t₂ a₅ a₆ b₅ b₆ r f₅ f₆ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₆ s₇ t₁ t₂ a₆ a₇ b₆ b₇ r f₆ f₇ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₇ s₈ t₁ t₂ a₇ a₈ b₇ b₈ r f₇ f₈ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₈ s₉ t₁ t₂ a₈ a₉ b₈ b₉ r f₈ f₉ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₉ s₁₀ t₁ t₂ a₉ a₁₀ b₉ b₁₀ r f₉ f₁₀ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁₀ s₁₁ t₁ t₂ a₁₀ a₁₁ b₁₀ b₁₁ r f₁₀ f₁₁ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁₁ s₁₂ t₁ t₂ a₁₁ a₁₂ b₁₁ b₁₂ r f₁₁ f₁₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁₂ s₁₃ t₁ t₂ a₁₂ a₁₃ b₁₂ b₁₃ r f₁₂ f₁₃ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁₃ s₁ t₁ t₂ a₁₃ a₁ b₁₃ b₁ r f₁₃ f₁ = 0 ∧
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ b₁ b₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₂ t₃ b₁ b₂ c₁ c₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₃ t₄ c₁ c₂ e₁ e₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₄ t₅ e₁ e₂ u₁ u₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₅ t₆ u₁ u₂ v₁ v₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₆ t₇ v₁ v₂ w₁ w₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₇ t₈ w₁ w₂ z₁ z₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₈ t₉ z₁ z₂ y₁ y₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₉ t₁₀ y₁ y₂ x₁ x₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁₀ t₁₁ x₁ x₂ p₁ p₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁₁ t₁₂ p₁ p₂ d₁ d₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁₂ t₁₃ d₁ d₂ l₁ l₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁₃ t₁ l₁ l₂ a₁ a₂ r f₁ f₂ = 0 ∧
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
  have hcoc := mixedInitialFinalHigherPowerPlaquette_thirteen_initial_and_final_tridecagon_cocycles
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
    c₁ c₂ e₁ e₂ u₁ u₂ v₁ v₂ w₁ w₂ z₁ z₂ y₁ y₂ x₁ x₂ p₁ p₂ d₁ d₂ l₁ l₂ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
  exact ⟨hcoc.1, hcoc.2.2.1,
    LayerB.R1_ChamberBathCommutes_FullYM.chamberLabel_chamber_eq i_ch,
    LayerB.R1_CharacterOrthogonality.signAtNegI_even_times_odd,
    LayerB.R1_VolterraSO10Embedding.oneLp_traceLp_inner,
    LayerB.R1_VolterraSO10Embedding_Dim4Chamber.f4_carries_even,
    LayerB.R1_VolterraSO10Embedding_Dim6Full.h1_carries_odd,
    LayerB.R1_VolterraSO10Embedding_DimExtension.f3_carries_even⟩

/-- Master synthesis of the `13 × 13` (`12 × 12 = 144` elementary plaquettes) mixed initial-and-final
higher-power resolvent plaquette grid with the Polymer / Borgs-Imbrie / Kotecký-Preiss /
Weingarten / Volterra $SO(10)$ embedding modules. -/
theorem thirteenByThirteen_plaquetteGrid_polymer_borgsImbrie_koteckyPreiss_weingarten_volterra_bridge_master
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
     y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
     p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
     l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃ : ℝ)
    (ha₁ : 0 < a₁) (ha₁₃ : 0 < a₁₃) (hl₁ : 0 < l₁) (hl₁₃ : 0 < l₁₃)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃ : Hilbert) :
    let w_grid := twelveByTwelveResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
      p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
      l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
    let w_grid_eq := twelveByTwelveResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
      y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
      p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
      l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
      r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
    w_grid = mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₁₃ t₁ t₁₃ a₁ a₁₃ l₁ l₁₃ r f₁ f₁₃ ∧
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
  have hstokes := twelveByTwelvePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ t₁₃
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
    l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
    r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
  have hweq := twelveByTwelveResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂ s₁₃ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ b₁₂ b₁₃
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ z₁ z₂ z₃ z₄ z₅ z₆ z₇ z₈ z₉ z₁₀ z₁₁ z₁₂ z₁₃
    y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y₁₃ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃
    p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ p₁₃ d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈ d₉ d₁₀ d₁₁ d₁₂ d₁₃
    l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃
    ha₁ ha₁₃ hl₁ hl₁₃ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ f₁₀ f₁₁ f₁₂ f₁₃
  exact ⟨hstokes.1, hweq.1,
    LayerB.Phase_A4_MatrixElementMatching.chamberToIota6_injective,
    LayerB.Phase_E3_DLR_CharacterExpansion.c_trivial_at_zero,
    LayerB.Phase_E3_KP7.coord4D_pos,
    LayerB.Phase_E3_RowPermutationSymmetry_Proof.rowPermutationSymmetrySO10_proved,
    LayerB.Phase_E3_Weingarten_OffDiagonal_Proof.offDiagonalDiagSquaredCorrelation_zero_proved,
    LayerB.R1_CharacterOrthogonality.signAtNegI_even_times_odd,
    LayerB.R1_VolterraSO10Embedding.oneLp_traceLp_inner⟩

#print axioms thirteenByThirteen_plaquetteGrid_stokes_with_multiLinkHilbert_matrixMatching_and_volterraLinkSearch
#print axioms thirteenByThirteen_identityPlaquetteGrid_stokes_with_clusterExpansion_dlr_pirogovSinai_and_gjKP
#print axioms equalOuterFinalTime_thirteenByThirteenResolventGrid_with_higherWeingartens_kp56_and_kp7Coord4D
#print axioms equalOuterFinalTime_thirteenByThirteenIdentityGrid_with_rowPermSymmetry_offDiagWeingarten_and_r2Haar
#print axioms thirteenStepPlaquetteTridecagonCocycles_with_r1ChamberBath_charOrthog_and_volterraSO10Embeddings
#print axioms thirteenByThirteen_plaquetteGrid_polymer_borgsImbrie_koteckyPreiss_weingarten_volterra_bridge_master

end KFCausalClockFloorThirteenByThirteenPlaquettePolymerBorgsImbrieKoteckyPreissWeingartenVolterraBridge
end Audit
end UnifiedTheory
