/- Bridge of the Seven-by-Seven `(s₁, s₂, s₃, s₄, s₅, s₆, s₇) × (t₁, t₂, t₃, t₄, t₅, t₆, t₇)`
(`6 × 6 = 36` Elementary Plaquettes) Mixed Initial-and-Final Higher-Power Resolvent Plaquette Grid
and Finite `Q`-Channel Three-Profile $3 \times 3$ Sylvester-Jacobi Spectral Covariance Gram
Determinant with the Curved 4D Causal Bridge, Census Identities, Exact Non-Perturbative K/P Regime,
Contracted Bianchi Identity, 4D Linearized Einstein Trace Reversal, 4D Gauss-Bonnet Expansion,
Substrate Poisson Counting, and Lohmiller-Slotine Sech Soliton Ricci Curvature Modules. -/
import UnifiedTheory.Audit.KFCausalClockFloorSevenBySevenMixedInitialFinalHigherPowerResolventPlaquetteGrid
import UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelThreeProfileSylvesterGramDeterminantAndHadamardInequality
import UnifiedTheory.Audit.KFCausalCurved4DCausalBridgeCensusExactRegimePhysicalSelectionSubstrateBridge
import UnifiedTheory.Audit.KFCausalCurved4DCapstoneConditionalEinsteinMatterBranchPredictionsTOERankingBridge

set_option autoImplicit false

namespace UnifiedTheory
namespace Audit
namespace KFCausalCurved4DSevenBySevenPlaquetteLohmillerSlotineConformalLaplacianBianchiEinsteinBridge

open scoped InnerProduct BigOperators
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorHigherPowerOperatorCores (hamiltonianPowerDomain)
open KFCausalClockFloorTwoTimeMixedInitialFinalHigherPowerResolventPlaquette
  (mixedInitialFinalHigherPowerResolventPlaquette
   mixedInitialFinalHigherPowerIdentityPlaquette)
open KFCausalClockFloorSevenBySevenMixedInitialFinalHigherPowerResolventPlaquetteGrid
  (sixBySixResolventPlaquetteGridSum
   sixBySixIdentityPlaquetteGridSum
   sixBySixPlaquetteGridSum_stokes_boundary_cancellation
   mixedInitialFinalHigherPowerPlaquette_seven_initial_and_final_heptagon_cocycles
   sixBySixResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains)
open KFCausalArbitrarySourceMultiChannelCenteredProjectorVarianceAndPopoviciuBound
  (multiChannelProjectedEnergy
   multiChannelSpectralVarianceFunctional)
open KFCausalArbitrarySourceMultiChannelThreeProfileSylvesterGramDeterminantAndHadamardInequality
  (multiChannelThreeByThreeSpectralGramDeterminant
   multiChannelThreeByThreeSpectralGramDeterminant_nonneg_and_hadamard_inequality
   multiChannelThreeByThreeSpectralGramDeterminant_shift_invariance_and_popoviciu_bounds)
open KFCausalCurved4DCausalBridgeCensusExactRegimePhysicalSelectionSubstrateBridge
open KFCausalCurved4DCapstoneConditionalEinsteinMatterBranchPredictionsTOERankingBridge

/-- Equal-outer-final-time `Dom(H(t)^(r+2))` regularity and 2D Stokes cancellation of
`sixBySixResolventPlaquetteGridSum` paired with causal-bridge dense-link null-cone recovery
(`CausalBridge`), poset past/future census cancellation (`CensusIdentities`), and 4D trace-reversal
involution (`LinearizedEinstein`). -/
theorem equalOuterFinalTime_sevenBySevenResolventGrid_with_causalBridge_census_and_traceReversal4D
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ t t₂ t₃ t₄ t₅ t₆ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ : ℝ)
    (ha₁ : 0 < a₁) (ha₇ : 0 < a₇) (hw₁ : 0 < w₁) (hw₇ : 0 < w₇)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ : Hilbert)
    {α : Type*} [Fintype α] [DecidableEq α] (rel : α → α → Prop) [DecidableRel rel]
    (c_d : ℝ) (d_dim : ℕ) (hd_dim : 0 < d_dim)
    (h4 : Matrix (Fin 4) (Fin 4) ℝ) :
    let w_grid_eq := sixBySixResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ t t₂ t₃ t₄ t₅ t₆ t
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
    w_grid_eq ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
      LayerA.LinearizedEinstein.traceReversal 4
        (LayerA.LinearizedEinstein.traceReversal 4 h4) = h4 ∧
      LayerA.CausalBridge.alexandrov_vol c_d 0 d_dim = 0 ∧
      (∑ j : α, LayerA.CensusIdentities.pastCard rel j =
        ∑ i : α, LayerA.CensusIdentities.futureCard rel i) ∧
      (∑ j : α, LayerA.CensusIdentities.orientationSource rel j = 0) := by
  intro w_grid_eq
  have hweq := sixBySixResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ t t₂ t₃ t₄ t₅ t₆ q
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ ha₁ ha₇ hw₁ hw₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
  have hcausal := causalBridge_and_censusIdentities_with_traceReversal4D rel c_d d_dim hd_dim h4
  exact ⟨hweq.1, hcausal.1, hcausal.2.1, hcausal.2.2.1, hcausal.2.2.2⟩

/-- `Q`-channel $3 \times 3$ Sylvester-Jacobi spectral covariance Gram determinant nonnegativity
and $3 \times 3$ Popoviciu bound paired with exact non-perturbative K/P regime, unconditional
contracted Bianchi superposition (`ExactRegime`), and parameter-free volume-ratio normalization
(`NormalizationTheorem`). -/
theorem multiChannel_threeByThreeGramDeterminant_with_exactRegime_contractedBianchi_and_normalizationTheorem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q_ch : ℕ} (P : Fin Q_ch → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q_ch → ℝ)
    (w₁_min w₁_max w₂_min w₂_max w₃_min w₃_max : ℝ)
    (hmin₁ : ∀ q, w₁_min ≤ w₁ q) (hmax₁ : ∀ q, w₁ q ≤ w₁_max)
    (hmin₂ : ∀ q, w₂_min ≤ w₂ q) (hmax₂ : ∀ q, w₂ q ≤ w₂_max)
    (hmin₃ : ∀ q, w₃_min ≤ w₃ q) (hmax₃ : ∀ q, w₃ q ≤ w₃_max) (x : E)
    {n : ℕ} (hn : 0 < n) (h_pert h₁ h₂ : LayerA.ExactRegime.Pert n)
    (md₁ md₂ : LayerA.MetricConstruction.MetricDerivs n) (b : Fin n)
    (ρ v₁ v₂ : ℝ) (hρ : ρ ≠ 0) (hv₂ : v₂ ≠ 0) :
    0 ≤ multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ∧
      multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ≤
        ((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
          ((w₃_max - w₃_min) / 2) ^ 2 * (multiChannelProjectedEnergy P x) ^ 6 ∧
      h_pert = LayerA.ExactRegime.πK n hn h_pert + LayerA.ExactRegime.πP n hn h_pert ∧
      LayerA.ExactRegime.tr n hn (LayerA.ExactRegime.πP n hn h_pert) = 0 ∧
      LayerA.Bianchi.divRic
          (LayerA.MetricConstruction.riemannFromMetric
            (LayerA.LinearizedFieldEqs.mdAdd md₁ md₂)) b -
        LayerA.Bianchi.dScalar
          (LayerA.MetricConstruction.riemannFromMetric
            (LayerA.LinearizedFieldEqs.mdAdd md₁ md₂)) b / 2 = 0 ∧
      (ρ * v₁) / (ρ * v₂) = v₁ / v₂ ∧
      0 < 8 * Real.pi := by
  have hhad := multiChannelThreeByThreeSpectralGramDeterminant_nonneg_and_hadamard_inequality
    P w₁ w₂ w₃ x
  have hpop := multiChannelThreeByThreeSpectralGramDeterminant_shift_invariance_and_popoviciu_bounds
    P w₁ w₂ w₃ 0 0 0 w₁_min w₁_max w₂_min w₂_max w₃_min w₃_max
    hmin₁ hmax₁ hmin₂ hmax₂ hmin₃ hmax₃ x
  have hex := exactRegime_and_normalizationTheorem_package hn h_pert h₁ h₂ md₁ md₂ b ρ v₁ v₂ hρ hv₂
  exact ⟨hhad.1, hpop.2.2, hex.1, hex.2.2.1, hex.2.2.2.2.1, hex.2.2.2.2.2.1, hex.2.2.2.2.2.2⟩

/-- `7 × 7` plaquette grid 2D Stokes cancellation paired with variational physical solution
selection (`PhysicalSelection`), primitive necessity (`PrimitivesForced`), $SO(2)$ rotation
invariance (`RotationInvariance`), and Lohmiller-Slotine Phase E sech soliton Ricci curvature
$R = 2/\sigma^2$. -/
theorem sevenBySeven_plaquetteGrid_stokes_with_physicalSelection_rotation_and_lohmillerSlotineSech
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ : Hilbert)
    {n : ℕ} (md : LayerA.MetricConstruction.MetricDerivs n)
    (θ₁ θ₂ Q P σ x_sol : ℝ) (hσ : σ ≠ 0) :
    sixBySixResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
        a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
        c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
        u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
        w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₇ t₁ t₇ a₁ a₇ w₁ w₇ r f₁ f₇ ∧
      (LayerA.PhysicalSelection.IsPhysical md ↔
        LayerA.PhysicalSelection.IsPhysicalWithLambda md 0) ∧
      LayerA.PrimitivesForced.trivialNullCone LayerA.PrimitivesForced.euclidQuad ∧
      (LayerA.RotationInvariance.rotateVec θ₁ Q P).1 ^ 2 +
          (LayerA.RotationInvariance.rotateVec θ₁ Q P).2 ^ 2 = Q ^ 2 + P ^ 2 ∧
      LayerB.LohmillerSlotinePredictionEFamily.derivedRicci
        (LayerB.LohmillerSlotinePredictionE3.sechProfile σ x_sol)
        (LayerB.LohmillerSlotinePredictionE3.sechProfile_x σ x_sol)
        (LayerB.LohmillerSlotinePredictionE3.sechProfile_xx σ x_sol) = 2 / σ ^ 2 := by
  have hstokes := sixBySixPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
    a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
    c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
    u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
    w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
  have hphys := physicalSelection_primitivesForced_and_rotationInvariance_package md θ₁ θ₂ Q P
  have hmc := masterCapstone_predictions_and_lohmillerSlotineSech_package σ x_sol hσ
  exact ⟨hstokes.1, hphys.1, hphys.2.2.1, hphys.2.2.2.2.1, hmc.2.2.2.2.2.2.2⟩

/-- `Q`-channel $3 \times 3$ Sylvester-Jacobi spectral covariance Gram determinant Hadamard and
Popoviciu bounds paired with Poisson counting substrate bridge (`SubstrateBridge`), Sorkin
cosmological constant count $N(\Lambda) = 1/\Lambda^2$, and 4D Gauss-Bonnet scalar expansion. -/
theorem multiChannel_threeByThreeGramDeterminant_with_substrateBridge_sorkinLambda_and_gaussBonnet4D
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q_ch : ℕ} (P : Fin Q_ch → (E →L[ℂ] E)) (w₁ w₂ w₃ : Fin Q_ch → ℝ)
    (w₁_min w₁_max w₂_min w₂_max w₃_min w₃_max : ℝ)
    (hmin₁ : ∀ q, w₁_min ≤ w₁ q) (hmax₁ : ∀ q, w₁ q ≤ w₁_max)
    (hmin₂ : ∀ q, w₂_min ≤ w₂ q) (hmax₂ : ∀ q, w₂ q ≤ w₂_max)
    (hmin₃ : ∀ q, w₃_min ≤ w₃ q) (hmax₃ : ∀ q, w₃ q ≤ w₃_max) (x : E)
    (pc₁ pc₂ : LayerA.SubstrateBridge.PoissonCounting) (v₁ v₂ : ℝ) (hv₂ : v₂ ≠ 0)
    (md : LayerA.MetricConstruction.MetricDerivs 4) :
    multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ≤
      multiChannelSpectralVarianceFunctional P w₁ x *
        multiChannelSpectralVarianceFunctional P w₂ x *
        multiChannelSpectralVarianceFunctional P w₃ x ∧
      multiChannelThreeByThreeSpectralGramDeterminant P w₁ w₂ w₃ x ≤
        ((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
          ((w₃_max - w₃_min) / 2) ^ 2 * (multiChannelProjectedEnergy P x) ^ 6 ∧
      pc₁.count v₁ / pc₁.count v₂ = v₁ / v₂ ∧
      pc₁.count v₁ / pc₁.count v₂ = pc₂.count v₁ / pc₂.count v₂ ∧
      LayerA.CosmologicalConstantN.Nsub ((1 : ℝ) / (10 : ℝ) ^ (122 : ℕ)) =
        (10 : ℝ) ^ (244 : ℕ) ∧
      4 * LayerA.GaussBonnetExpansion.gbStandard
          (LayerA.MetricConstruction.riemannFromMetric md) =
        4 * LayerA.GaussBonnetExpansion.kretschner
            (LayerA.MetricConstruction.riemannFromMetric md) -
          16 * LayerA.GaussBonnetExpansion.ricciNorm
            (LayerA.MetricConstruction.riemannFromMetric md) +
          4 * LayerA.GaussBonnetExpansion.scalarR
            (LayerA.MetricConstruction.riemannFromMetric md) ^ 2 := by
  have hhad := multiChannelThreeByThreeSpectralGramDeterminant_nonneg_and_hadamard_inequality
    P w₁ w₂ w₃ x
  have hpop := multiChannelThreeByThreeSpectralGramDeterminant_shift_invariance_and_popoviciu_bounds
    P w₁ w₂ w₃ 0 0 0 w₁_min w₁_max w₂_min w₂_max w₃_min w₃_max
    hmin₁ hmax₁ hmin₂ hmax₂ hmin₃ hmax₃ x
  have hsub := substrateBridge_with_sorkinLambda_and_gaussBonnet4D pc₁ pc₂ v₁ v₂ hv₂ md
  exact ⟨hhad.2.2, hpop.2.2, hsub.1, hsub.2.2.1, hsub.2.2.2.1, hsub.2.2.2.2⟩

/-- Master synthesis of the `7 × 7` (`6 × 6 = 36` elementary plaquettes) mixed initial-and-final
higher-power resolvent plaquette grid and finite `Q`-channel $3 \times 3$ Sylvester-Jacobi spectral
covariance Gram determinant with the curved 4D Causal Bridge, Census Identities, Exact Regime,
Bianchi, Linearized Einstein, Substrate Bridge, and Lohmiller-Slotine Sech Soliton modules. -/
theorem sevenBySeven_plaquetteGrid_multiChannelThreeByThreeGramDeterminant_lohmillerSlotine_bianchi_einstein_bridge_master
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇ q
     a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
     c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
     u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
     w₁ w₂ w₃ w₄ w₅ w₆ w₇ : ℝ)
    (ha₁ : 0 < a₁) (ha₇ : 0 < a₇) (hw₁ : 0 < w₁) (hw₇ : 0 < w₇)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ f₇ : Hilbert)
    {Q_ch : ℕ} (P : Fin Q_ch → (Hilbert →L[ℂ] Hilbert)) (w₁_ch w₂_ch w₃_ch : Fin Q_ch → ℝ)
    (w₁_min w₁_max w₂_min w₂_max w₃_min w₃_max : ℝ)
    (hmin₁ : ∀ q_idx, w₁_min ≤ w₁_ch q_idx) (hmax₁ : ∀ q_idx, w₁_ch q_idx ≤ w₁_max)
    (hmin₂ : ∀ q_idx, w₂_min ≤ w₂_ch q_idx) (hmax₂ : ∀ q_idx, w₂_ch q_idx ≤ w₂_max)
    (hmin₃ : ∀ q_idx, w₃_min ≤ w₃_ch q_idx) (hmax₃ : ∀ q_idx, w₃_ch q_idx ≤ w₃_max)
    (σ x_sol : ℝ) (hσ : σ ≠ 0)
    (h4 : Matrix (Fin 4) (Fin 4) ℝ) :
    let w_grid := sixBySixResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
    let w_grid_eq := sixBySixResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ s₇ t₁ t₂ t₃ t₄ t₅ t₆ t₁
      a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇
      c₁ c₂ c₃ c₄ c₅ c₆ c₇ e₁ e₂ e₃ e₄ e₅ e₆ e₇
      u₁ u₂ u₃ u₄ u₅ u₆ u₇ v₁ v₂ v₃ v₄ v₅ v₆ v₇
      w₁ w₂ w₃ w₄ w₅ w₆ w₇ r f₁ f₂ f₃ f₄ f₅ f₆ f₇
    w_grid = mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₇ t₁ t₇ a₁ a₇ w₁ w₇ r f₁ f₇ ∧
      w_grid_eq ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
      0 ≤ multiChannelThreeByThreeSpectralGramDeterminant P w₁_ch w₂_ch w₃_ch f₁ ∧
      multiChannelThreeByThreeSpectralGramDeterminant P w₁_ch w₂_ch w₃_ch f₁ ≤
        multiChannelSpectralVarianceFunctional P w₁_ch f₁ *
          multiChannelSpectralVarianceFunctional P w₂_ch f₁ *
          multiChannelSpectralVarianceFunctional P w₃_ch f₁ ∧
      multiChannelThreeByThreeSpectralGramDeterminant P w₁_ch w₂_ch w₃_ch f₁ ≤
        ((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
          ((w₃_max - w₃_min) / 2) ^ 2 * (multiChannelProjectedEnergy P f₁) ^ 6 ∧
      LayerA.ExactRegime.tr 4 (by decide)
        (LayerA.ExactRegime.πP 4 (by decide) h4) = 0 ∧
      LayerA.LinearizedEinstein.traceReversal 4
        (LayerA.LinearizedEinstein.traceReversal 4 h4) = h4 ∧
      LayerB.LohmillerSlotinePredictionEFamily.derivedRicci
        (LayerB.LohmillerSlotinePredictionE3.sechProfile σ x_sol)
        (LayerB.LohmillerSlotinePredictionE3.sechProfile_x σ x_sol)
        (LayerB.LohmillerSlotinePredictionE3.sechProfile_xx σ x_sol) = 2 / σ ^ 2 := by
  intro w_grid w_grid_eq
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
  have hhad := multiChannelThreeByThreeSpectralGramDeterminant_nonneg_and_hadamard_inequality
    P w₁_ch w₂_ch w₃_ch f₁
  have hpop := multiChannelThreeByThreeSpectralGramDeterminant_shift_invariance_and_popoviciu_bounds
    P w₁_ch w₂_ch w₃_ch 0 0 0 w₁_min w₁_max w₂_min w₂_max w₃_min w₃_max
    hmin₁ hmax₁ hmin₂ hmax₂ hmin₃ hmax₃ f₁
  have hmc := masterCapstone_predictions_and_lohmillerSlotineSech_package σ x_sol hσ
  exact ⟨hstokes.1, hweq.1, hhad.1, hhad.2.2, hpop.2.2,
    LayerA.ExactRegime.exact_neutrality (by decide) h4,
    LayerA.LinearizedEinstein.traceReversal_involutive_4d h4,
    hmc.2.2.2.2.2.2.2⟩

#print axioms equalOuterFinalTime_sevenBySevenResolventGrid_with_causalBridge_census_and_traceReversal4D
#print axioms multiChannel_threeByThreeGramDeterminant_with_exactRegime_contractedBianchi_and_normalizationTheorem
#print axioms sevenBySeven_plaquetteGrid_stokes_with_physicalSelection_rotation_and_lohmillerSlotineSech
#print axioms multiChannel_threeByThreeGramDeterminant_with_substrateBridge_sorkinLambda_and_gaussBonnet4D
#print axioms sevenBySeven_plaquetteGrid_multiChannelThreeByThreeGramDeterminant_lohmillerSlotine_bianchi_einstein_bridge_master

end KFCausalCurved4DSevenBySevenPlaquetteLohmillerSlotineConformalLaplacianBianchiEinsteinBridge
end Audit
end UnifiedTheory
