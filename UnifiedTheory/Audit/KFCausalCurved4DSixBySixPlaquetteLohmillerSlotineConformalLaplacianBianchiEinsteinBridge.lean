/- Bridge of the Six-by-Six `(s₁, s₂, s₃, s₄, s₅, s₆) × (t₁, t₂, t₃, t₄, t₅, t₆)` (`5 × 5 = 25`
Elementary Plaquettes) Mixed Initial-and-Final Higher-Power Resolvent Plaquette Grid and Finite
`Q`-Channel $2 \times 2$ Spectral Covariance Gram Determinant with the Curved 4D Causal Bridge,
Census Identities, Exact Non-Perturbative K/P Regime, Contracted Bianchi Identity, 4D Linearized
Einstein Trace Reversal, 4D Gauss-Bonnet Expansion, Substrate Poisson Counting, and
Lohmiller-Slotine Sech Soliton Ricci Curvature Modules. -/
import UnifiedTheory.Audit.KFCausalClockFloorSixBySixMixedInitialFinalHigherPowerResolventPlaquetteGrid
import UnifiedTheory.Audit.KFCausalArbitrarySourceMultiChannelSpectralCovarianceGramDeterminantAndCauchySchwarzInequality
import UnifiedTheory.Audit.KFCausalCurved4DCausalBridgeCensusExactRegimePhysicalSelectionSubstrateBridge
import UnifiedTheory.Audit.KFCausalCurved4DCapstoneConditionalEinsteinMatterBranchPredictionsTOERankingBridge

set_option autoImplicit false

namespace UnifiedTheory
namespace Audit
namespace KFCausalCurved4DSixBySixPlaquetteLohmillerSlotineConformalLaplacianBianchiEinsteinBridge

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
   fiveByFiveResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains)
open KFCausalArbitrarySourceMultiChannelCenteredProjectorVarianceAndPopoviciuBound
  (multiChannelProjectedEnergy
   multiChannelSpectralVarianceFunctional)
open KFCausalArbitrarySourceMultiChannelCenteredProjectorCovarianceAndCauchySchwarzBound
  (multiChannelSpectralCovarianceFunctional)
open KFCausalArbitrarySourceMultiChannelSpectralCovarianceGramDeterminantAndCauchySchwarzInequality
  (multiChannelSpectralCovarianceGramDeterminant
   multiChannelSpectralCovarianceGramDeterminant_nonneg_and_cauchy_schwarz_sq
   multiChannelSpectralCovarianceGramDeterminant_multiplicative_popoviciu_bounds)
open KFCausalCurved4DCausalBridgeCensusExactRegimePhysicalSelectionSubstrateBridge
open KFCausalCurved4DCapstoneConditionalEinsteinMatterBranchPredictionsTOERankingBridge

/-- Equal-outer-final-time `Dom(H(t)^(r+2))` regularity and 2D Stokes cancellation of
`fiveByFiveResolventPlaquetteGridSum` paired with causal-bridge dense-link null-cone recovery
(`CausalBridge`), poset past/future census cancellation (`CensusIdentities`), and 4D trace-reversal
involution (`LinearizedEinstein`). -/
theorem equalOuterFinalTime_sixBySixResolventGrid_with_causalBridge_census_and_traceReversal4D
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ t t₂ t₃ t₄ t₅ q
     a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
     c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
     u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ : ℝ)
    (ha₁ : 0 < a₁) (ha₆ : 0 < a₆) (hv₁ : 0 < v₁) (hv₆ : 0 < v₆)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ : Hilbert)
    {α : Type*} [Fintype α] [DecidableEq α] (rel : α → α → Prop) [DecidableRel rel]
    (c_d : ℝ) (d_dim : ℕ) (hd_dim : 0 < d_dim)
    (h4 : Matrix (Fin 4) (Fin 4) ℝ) :
    let w_grid_eq := fiveByFiveResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ s₄ s₅ s₆ t t₂ t₃ t₄ t₅ t
      a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
      c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
      u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆
    w_grid_eq ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
      LayerA.LinearizedEinstein.traceReversal 4
        (LayerA.LinearizedEinstein.traceReversal 4 h4) = h4 ∧
      LayerA.CausalBridge.alexandrov_vol c_d 0 d_dim = 0 ∧
      (∑ j : α, LayerA.CensusIdentities.pastCard rel j =
        ∑ i : α, LayerA.CensusIdentities.futureCard rel i) ∧
      (∑ j : α, LayerA.CensusIdentities.orientationSource rel j = 0) := by
  intro w_grid_eq
  have hweq := fiveByFiveResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ t t₂ t₃ t₄ t₅ q
    a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
    c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
    u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆
    ha₁ ha₆ hv₁ hv₆ r f₁ f₂ f₃ f₄ f₅ f₆
  have hcausal := causalBridge_and_censusIdentities_with_traceReversal4D rel c_d d_dim hd_dim h4
  exact ⟨hweq.1, hcausal.1, hcausal.2.1, hcausal.2.2.1, hcausal.2.2.2⟩

/-- `Q`-channel $2 \times 2$ spectral covariance Gram determinant nonnegativity and multiplicative
Popoviciu covariance-squared bound paired with exact non-perturbative K/P regime, unconditional
contracted Bianchi superposition (`ExactRegime`), and parameter-free volume-ratio normalization
(`NormalizationTheorem`). -/
theorem multiChannel_gramDeterminant_with_exactRegime_contractedBianchi_and_normalizationTheorem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q_ch : ℕ} (P : Fin Q_ch → (E →L[ℂ] E)) (w₁ w₂ : Fin Q_ch → ℝ)
    (w₁_min w₁_max w₂_min w₂_max : ℝ)
    (hmin₁ : ∀ q, w₁_min ≤ w₁ q) (hmax₁ : ∀ q, w₁ q ≤ w₁_max)
    (hmin₂ : ∀ q, w₂_min ≤ w₂ q) (hmax₂ : ∀ q, w₂ q ≤ w₂_max) (x : E)
    {n : ℕ} (hn : 0 < n) (h_pert h₁ h₂ : LayerA.ExactRegime.Pert n)
    (md₁ md₂ : LayerA.MetricConstruction.MetricDerivs n) (b : Fin n)
    (ρ v₁ v₂ : ℝ) (hρ : ρ ≠ 0) (hv₂ : v₂ ≠ 0) :
    0 ≤ multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ x ∧
      (multiChannelSpectralCovarianceFunctional P w₁ w₂ x) ^ 2 ≤
        ((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
          (multiChannelProjectedEnergy P x) ^ 4 ∧
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
  have hcs := multiChannelSpectralCovarianceGramDeterminant_nonneg_and_cauchy_schwarz_sq P w₁ w₂ x
  have hpop := multiChannelSpectralCovarianceGramDeterminant_multiplicative_popoviciu_bounds
    P w₁ w₂ w₁_min w₁_max w₂_min w₂_max hmin₁ hmax₁ hmin₂ hmax₂ x
  have hex := exactRegime_and_normalizationTheorem_package hn h_pert h₁ h₂ md₁ md₂ b ρ v₁ v₂ hρ hv₂
  exact ⟨hcs.2.1, hpop.2.2.2, hex.1, hex.2.2.1, hex.2.2.2.2.1, hex.2.2.2.2.2.1, hex.2.2.2.2.2.2⟩

/-- `6 × 6` plaquette grid 2D Stokes cancellation paired with variational physical solution
selection (`PhysicalSelection`), primitive necessity (`PrimitivesForced`), $SO(2)$ rotation
invariance (`RotationInvariance`), and Lohmiller-Slotine Phase E sech soliton Ricci curvature
$R = 2/\sigma^2$. -/
theorem sixBySix_plaquetteGrid_stokes_with_physicalSelection_rotation_and_lohmillerSlotineSech
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
     a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
     c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
     u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ : Hilbert)
    {n : ℕ} (md : LayerA.MetricConstruction.MetricDerivs n)
    (θ₁ θ₂ Q P σ x_sol : ℝ) (hσ : σ ≠ 0) :
    fiveByFiveResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
        a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
        c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
        u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₆ t₁ t₆ a₁ a₆ v₁ v₆ r f₁ f₆ ∧
      (LayerA.PhysicalSelection.IsPhysical md ↔
        LayerA.PhysicalSelection.IsPhysicalWithLambda md 0) ∧
      LayerA.PrimitivesForced.trivialNullCone LayerA.PrimitivesForced.euclidQuad ∧
      (LayerA.RotationInvariance.rotateVec θ₁ Q P).1 ^ 2 +
          (LayerA.RotationInvariance.rotateVec θ₁ Q P).2 ^ 2 = Q ^ 2 + P ^ 2 ∧
      LayerB.LohmillerSlotinePredictionEFamily.derivedRicci
        (LayerB.LohmillerSlotinePredictionE3.sechProfile σ x_sol)
        (LayerB.LohmillerSlotinePredictionE3.sechProfile_x σ x_sol)
        (LayerB.LohmillerSlotinePredictionE3.sechProfile_xx σ x_sol) = 2 / σ ^ 2 := by
  have hstokes := fiveByFivePlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆
    a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
    c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
    u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ r f₁ f₂ f₃ f₄ f₅ f₆
  have hphys := physicalSelection_primitivesForced_and_rotationInvariance_package md θ₁ θ₂ Q P
  have hmc := masterCapstone_predictions_and_lohmillerSlotineSech_package σ x_sol hσ
  exact ⟨hstokes.1, hphys.1, hphys.2.2.1, hphys.2.2.2.2.1, hmc.2.2.2.2.2.2.2⟩

/-- `Q`-channel $2 \times 2$ spectral covariance Gram determinant multiplicative Cauchy-Schwarz and
Popoviciu bounds paired with Poisson counting substrate bridge (`SubstrateBridge`), Sorkin
cosmological constant count $N(\Lambda) = 1/\Lambda^2$, and 4D Gauss-Bonnet scalar expansion. -/
theorem multiChannel_gramDeterminant_with_substrateBridge_sorkinLambda_and_gaussBonnet4D
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q_ch : ℕ} (P : Fin Q_ch → (E →L[ℂ] E)) (w₁ w₂ : Fin Q_ch → ℝ)
    (w₁_min w₁_max w₂_min w₂_max : ℝ)
    (hmin₁ : ∀ q, w₁_min ≤ w₁ q) (hmax₁ : ∀ q, w₁ q ≤ w₁_max)
    (hmin₂ : ∀ q, w₂_min ≤ w₂ q) (hmax₂ : ∀ q, w₂ q ≤ w₂_max) (x : E)
    (pc₁ pc₂ : LayerA.SubstrateBridge.PoissonCounting) (v₁ v₂ : ℝ) (hv₂ : v₂ ≠ 0)
    (md : LayerA.MetricConstruction.MetricDerivs 4) :
    (multiChannelSpectralCovarianceFunctional P w₁ w₂ x) ^ 2 ≤
        multiChannelSpectralVarianceFunctional P w₁ x *
          multiChannelSpectralVarianceFunctional P w₂ x ∧
      (multiChannelSpectralCovarianceFunctional P w₁ w₂ x) ^ 2 ≤
        ((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
          (multiChannelProjectedEnergy P x) ^ 4 ∧
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
  have hpop := multiChannelSpectralCovarianceGramDeterminant_multiplicative_popoviciu_bounds
    P w₁ w₂ w₁_min w₁_max w₂_min w₂_max hmin₁ hmax₁ hmin₂ hmax₂ x
  have hsub := substrateBridge_with_sorkinLambda_and_gaussBonnet4D pc₁ pc₂ v₁ v₂ hv₂ md
  exact ⟨hpop.1, hpop.2.2.2, hsub.1, hsub.2.2.1, hsub.2.2.2.1, hsub.2.2.2.2⟩

/-- Master synthesis of the `6 × 6` mixed initial-and-final higher-power resolvent plaquette grid
and finite `Q`-channel $2 \times 2$ spectral covariance Gram determinant with the curved 4D Causal
Bridge, Census Identities, Exact Regime, Bianchi, Linearized Einstein, Substrate Bridge, and
Lohmiller-Slotine Sech Soliton modules. -/
theorem sixBySix_plaquetteGrid_multiChannelGramDeterminant_lohmillerSlotine_bianchi_einstein_bridge_master
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ s₄ s₅ s₆ t₁ t₂ t₃ t₄ t₅ t₆ q
     a₁ a₂ a₃ a₄ a₅ a₆ b₁ b₂ b₃ b₄ b₅ b₆
     c₁ c₂ c₃ c₄ c₅ c₆ e₁ e₂ e₃ e₄ e₅ e₆
     u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆ : ℝ)
    (ha₁ : 0 < a₁) (ha₆ : 0 < a₆) (hv₁ : 0 < v₁) (hv₆ : 0 < v₆)
    (r : ℕ) (f₁ f₂ f₃ f₄ f₅ f₆ : Hilbert)
    {Q_ch : ℕ} (P : Fin Q_ch → (Hilbert →L[ℂ] Hilbert)) (w₁ w₂ : Fin Q_ch → ℝ)
    (w₁_min w₁_max w₂_min w₂_max : ℝ)
    (hmin₁ : ∀ q_idx, w₁_min ≤ w₁ q_idx) (hmax₁ : ∀ q_idx, w₁ q_idx ≤ w₁_max)
    (hmin₂ : ∀ q_idx, w₂_min ≤ w₂ q_idx) (hmax₂ : ∀ q_idx, w₂ q_idx ≤ w₂_max)
    (σ x_sol : ℝ) (hσ : σ ≠ 0)
    (h4 : Matrix (Fin 4) (Fin 4) ℝ) :
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
      0 ≤ multiChannelSpectralCovarianceGramDeterminant P w₁ w₂ f₁ ∧
      (multiChannelSpectralCovarianceFunctional P w₁ w₂ f₁) ^ 2 ≤
        multiChannelSpectralVarianceFunctional P w₁ f₁ *
          multiChannelSpectralVarianceFunctional P w₂ f₁ ∧
      (multiChannelSpectralCovarianceFunctional P w₁ w₂ f₁) ^ 2 ≤
        ((w₁_max - w₁_min) / 2) ^ 2 * ((w₂_max - w₂_min) / 2) ^ 2 *
          (multiChannelProjectedEnergy P f₁) ^ 4 ∧
      LayerA.ExactRegime.tr 4 (by decide)
        (LayerA.ExactRegime.πP 4 (by decide) h4) = 0 ∧
      LayerA.LinearizedEinstein.traceReversal 4
        (LayerA.LinearizedEinstein.traceReversal 4 h4) = h4 ∧
      LayerB.LohmillerSlotinePredictionEFamily.derivedRicci
        (LayerB.LohmillerSlotinePredictionE3.sechProfile σ x_sol)
        (LayerB.LohmillerSlotinePredictionE3.sechProfile_x σ x_sol)
        (LayerB.LohmillerSlotinePredictionE3.sechProfile_xx σ x_sol) = 2 / σ ^ 2 := by
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
  have hcs := multiChannelSpectralCovarianceGramDeterminant_nonneg_and_cauchy_schwarz_sq P w₁ w₂ f₁
  have hpop := multiChannelSpectralCovarianceGramDeterminant_multiplicative_popoviciu_bounds
    P w₁ w₂ w₁_min w₁_max w₂_min w₂_max hmin₁ hmax₁ hmin₂ hmax₂ f₁
  have hmc := masterCapstone_predictions_and_lohmillerSlotineSech_package σ x_sol hσ
  exact ⟨hstokes.1, hweq.1, hcs.2.1, hcs.2.2, hpop.2.2.2,
    LayerA.ExactRegime.exact_neutrality (by decide) h4,
    LayerA.LinearizedEinstein.traceReversal_involutive_4d h4,
    hmc.2.2.2.2.2.2.2⟩

#print axioms equalOuterFinalTime_sixBySixResolventGrid_with_causalBridge_census_and_traceReversal4D
#print axioms multiChannel_gramDeterminant_with_exactRegime_contractedBianchi_and_normalizationTheorem
#print axioms sixBySix_plaquetteGrid_stokes_with_physicalSelection_rotation_and_lohmillerSlotineSech
#print axioms multiChannel_gramDeterminant_with_substrateBridge_sorkinLambda_and_gaussBonnet4D
#print axioms sixBySix_plaquetteGrid_multiChannelGramDeterminant_lohmillerSlotine_bianchi_einstein_bridge_master

end KFCausalCurved4DSixBySixPlaquetteLohmillerSlotineConformalLaplacianBianchiEinsteinBridge
end Audit
end UnifiedTheory
