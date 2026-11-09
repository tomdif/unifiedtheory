/- Bridge of the Three-by-Three `(s₁, s₂, s₃) × (t₁, t₂, t₃)` Mixed Initial-and-Final Higher-Power
Resolvent Plaquette Grid and Normalized Three-Channel Spectral Variance Functional with the 15
LayerB/LayerC Spectral Relative Entropy, Stinespring Measurement DPI, Top-Yukawa Reaudit, Trace
Resolvent Convexity / Joint Convexity, Umegaki Diagonal / Tensor Additivity, Unitary Invariance,
Universal Principle Search, Vec-Unvec Isomorphism, Yang-Mills Causal Attack, Bekenstein Bound, and
Bipartite No-Signalling / Qubit CHSH Modules
(`SpectralRelativeEntropy`..`BipartiteQubitCHSH`). -/
import UnifiedTheory.Audit.KFCausalClockFloorThreeByThreeMixedInitialFinalHigherPowerResolventPlaquetteGrid
import UnifiedTheory.Audit.KFCausalArbitrarySourceCenteredProjectorVarianceAndSpectralSpreadDecomposition
import UnifiedTheory.LayerB.SpectralRelativeEntropy
import UnifiedTheory.LayerB.StinespringMeasurementDPI
import UnifiedTheory.LayerB.TopYukawaReaudit
import UnifiedTheory.LayerB.TraceResolventConvexity
import UnifiedTheory.LayerB.TraceResolventJointConvexity
import UnifiedTheory.LayerB.UmegakiDiagonalBridge
import UnifiedTheory.LayerB.UmegakiTensorAdditivity
import UnifiedTheory.LayerB.UnitaryInvariance
import UnifiedTheory.LayerB.UniversalPrincipleSearch
import UnifiedTheory.LayerB.VecUnvec
import UnifiedTheory.LayerB.YangMillsCausalAttack
import UnifiedTheory.LayerC.BekensteinBound
import UnifiedTheory.LayerC.BipartiteFullPostulatesQubit
import UnifiedTheory.LayerC.BipartiteNoSignallingAnalyticCoreDischarge
import UnifiedTheory.LayerC.BipartiteQubitCHSH

set_option autoImplicit false

namespace UnifiedTheory
namespace Audit
namespace KFCausalCurved4DThreeByThreePlaquetteSpectralRelTraceResolventUmegakiYMBekensteinBipartiteBridge

open scoped InnerProduct BigOperators Matrix ComplexOrder
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorHigherPowerOperatorCores (hamiltonianPowerDomain)
open KFCausalClockFloorTwoTimeMixedInitialFinalHigherPowerResolventPlaquette
  (mixedInitialFinalHigherPowerResolventPlaquette
   mixedInitialFinalHigherPowerIdentityPlaquette)
open KFCausalClockFloorThreeByThreeMixedInitialFinalHigherPowerResolventPlaquetteGrid
  (twoByTwoResolventPlaquetteGridSum
   twoByTwoIdentityPlaquetteGridSum
   twoByTwoPlaquetteGridSum_stokes_boundary_cancellation
   twoByTwoResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
   twoByTwoResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains)
open KFCausalArbitrarySourceOrthogonalProjectionResidualEnergyDecomposition (hilbertEnergy)
open KFCausalArbitrarySourceMutuallyOrthogonalProjectorParsevalDecomposition
  (AreMutuallyOrthogonalProjections)
open KFCausalArbitrarySourceCenteredProjectorVarianceAndSpectralSpreadDecomposition
  (threeChannelSpectralVarianceFunctional
   threeChannelLagrangePairwiseSpread
   threeChannelSpectralVarianceFunctional_eq_lagrangeSpread_and_nonneg
   threeChannelSpectralVarianceFunctional_le_bhatiaDavis_and_popoviciu_sq_bound)

/-- Exact 2D Stokes / Green boundary cancellation for `twoByTwoResolventPlaquetteGridSum` paired
with spectral relative entropy self-vanishing (`SpectralRelativeEntropy`), Stinespring dilation
Hermiticity and unit trace (`StinespringMeasurementDPI`), and solar complement
`cos^2 \theta_{12} = 7 / 10` (`TopYukawaReaudit`). -/
theorem plaquetteGrid_stokes_with_spectralRelEntropy_stinespringDPI_and_topYukawaReaudit
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ : ℝ)
    (r : ℕ) (f₁ f₂ f₃ : Hilbert)
    {n_sp k_st : ℕ}
    (ρ_sp : LayerB.Spectral.SpectralDensityMatrix n_sp)
    (V_st : Matrix (Fin n_sp × Fin k_st) (Fin n_sp) ℂ)
    (hV : LayerB.StinespringDilation.IsIsometry V_st)
    (ρ_st : LayerB.RobertsonSchrodinger.ComplexDensityMatrix n_sp) :
    twoByTwoResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₃ t₁ t₃ a₁ a₃ e₁ e₃ r f₁ f₃ ∧
      LayerB.SpectralRelativeEntropy.relativeEntropySpectral
        (LayerB.SpectralRelativeEntropy.selfPair ρ_sp) = 0 ∧
      (LayerB.StinespringMeasurementDPI.stinespringConjMatrix V_st ρ_st).IsHermitian ∧
      Matrix.trace (LayerB.StinespringMeasurementDPI.stinespringConjMatrix V_st ρ_st) = 1 ∧
      LayerB.TopYukawaReaudit.cosSq_theta12 = 7 / 10 := by
  have hstokes := twoByTwoPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃
  exact ⟨hstokes.1,
    LayerB.SpectralRelativeEntropy.spectralRelativeEntropy_self_eq_zero ρ_sp,
    LayerB.StinespringMeasurementDPI.stinespringConjMatrix_isHermitian V_st ρ_st,
    LayerB.StinespringMeasurementDPI.stinespringConjMatrix_trace V_st hV ρ_st,
    LayerB.TopYukawaReaudit.cosSq_theta12_eq_seven_tenths⟩

/-- Equal-outer-final-time `hamiltonianPowerDomain t₁ (r + 2)` regularity of
`twoByTwoResolventPlaquetteGridSum` paired with shifted positive-definiteness
(`TraceResolventConvexity`), Kraus Schur-complement block PSD (`TraceResolventJointConvexity`),
Kronecker density Hermiticity and unit trace (`UmegakiTensorAdditivity`), and unitary log-CFC
equivariance (`UnitaryInvariance`). -/
theorem equalOuterFinalTime_resolventGrid_with_traceResolvent_umegakiTensor_and_unitaryInvariance
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ t₁ t₂ q a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ : ℝ)
    (ha₁ : 0 < a₁) (ha₃ : 0 < a₃) (he₁ : 0 < e₁) (he₃ : 0 < e₃)
    (r : ℕ) (f₁ f₂ f₃ : Hilbert)
    {n_tr m_tr : ℕ}
    (K_mat B_mat : Matrix (Fin n_tr) (Fin n_tr) ℂ) (hB : B_mat.PosDef)
    (ρ_kr : LayerB.RobertsonSchrodinger.ComplexDensityMatrix n_tr)
    (τ_kr : LayerB.RobertsonSchrodinger.ComplexDensityMatrix m_tr)
    (U_un : Matrix.unitaryGroup (Fin n_tr) ℂ) (M_sa : Matrix (Fin n_tr) (Fin n_tr) ℂ)
    (hM : IsSelfAdjoint M_sa) :
    twoByTwoResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ t₁ t₂ t₁ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃ ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
      (Matrix.fromBlocks B_mat K_mat K_matᴴ (K_matᴴ * B_mat⁻¹ * K_mat)).PosSemidef ∧
      (LayerB.UmegakiTensorAdditivity.kroneckerMatrix ρ_kr τ_kr).IsHermitian ∧
      (LayerB.UmegakiTensorAdditivity.kroneckerMatrix ρ_kr τ_kr).trace = 1 ∧
      cfc Real.log (U_un.val * M_sa * star U_un.val) =
        U_un.val * cfc Real.log M_sa * star U_un.val := by
  have hweq := twoByTwoResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ t₁ t₂ q a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ ha₁ ha₃ he₁ he₃ r f₁ f₂ f₃
  exact ⟨hweq.1,
    LayerB.TraceResolventJointConvexity.block_psd_kraus K_mat B_mat hB,
    LayerB.UmegakiTensorAdditivity.kroneckerMatrix_isHermitian ρ_kr τ_kr,
    LayerB.UmegakiTensorAdditivity.kroneckerMatrix_trace ρ_kr τ_kr,
    LayerB.UnitaryInvariance.cfc_log_unitary_conj U_un M_sa hM⟩

/-- Normalized three-channel spectral variance Lagrange identity paired with universal-principle
discriminant decompositions (`UniversalPrincipleSearch`), `vec`/`unvec` involution (`VecUnvec`),
and Yang-Mills causal discriminant decomposition `disc = N_c + d_eff = N_W + N_total`
(`YangMillsCausalAttack`). -/
theorem centeredProjectorVariance_with_universalPrinciple_vecUnvec_and_yangMillsCausalAttack
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res : ℝ) (x : E)
    {m_v n_v : ℕ} (v_vec : Fin m_v × Fin n_v → ℂ) :
    threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x =
      threeChannelLagrangePairwiseSpread P₁ P₂ w₁ w₂ w_res x ∧
      LayerB.UniversalPrincipleSearch.UPS_disc =
        LayerB.UniversalPrincipleSearch.UPS_Nc + LayerB.UniversalPrincipleSearch.UPS_d ∧
      LayerB.UniversalPrincipleSearch.UPS_disc =
        LayerB.UniversalPrincipleSearch.UPS_NW + LayerB.UniversalPrincipleSearch.UPS_Nt ∧
      LayerB.Kraus.vec (LayerB.Kraus.unvec v_vec) = v_vec ∧
      LayerB.YangMillsCausalAttack.disc =
        LayerB.YangMillsCausalAttack.N_c + LayerB.YangMillsCausalAttack.d_eff ∧
      LayerB.YangMillsCausalAttack.disc =
        LayerB.YangMillsCausalAttack.N_W + LayerB.YangMillsCausalAttack.N_total := by
  have hlag := threeChannelSpectralVarianceFunctional_eq_lagrangeSpread_and_nonneg
    hP w₁ w₂ w_res x
  exact ⟨hlag.1,
    LayerB.UniversalPrincipleSearch.UPS_disc_decomp_1,
    LayerB.UniversalPrincipleSearch.UPS_disc_decomp_2,
    LayerB.Kraus.vec_unvec v_vec,
    LayerB.YangMillsCausalAttack.disc_is_gauge_plus_spacetime,
    LayerB.YangMillsCausalAttack.disc_is_W_plus_total⟩

/-- Spectral variance Popoviciu bound paired with Bekenstein entropy bound nonnegativity
(`BekensteinBound`), bipartite no-signalling separation postulate (`BipartiteFullPostulatesQubit`),
and Pauli $\sigma_x, \sigma_z$ Hermiticity (`BipartiteQubitCHSH`). -/
theorem centeredProjectorVariance_popoviciu_with_bekensteinBound_bipartiteSeparation_and_bipartiteQubitCHSH
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res w_min w_max R_bek E_bek : ℝ)
    (hmin₁ : w_min ≤ w₁) (hmin₂ : w_min ≤ w₂) (hmin_r : w_min ≤ w_res)
    (hmax₁ : w₁ ≤ w_max) (hmax₂ : w₂ ≤ w_max) (hmax_r : w_res ≤ w_max)
    (hR : 0 ≤ R_bek) (hE : 0 ≤ E_bek) (x : E)
    (n_A n_B : ℕ) [NeZero n_A] [NeZero n_B]
    (hCore : LayerC.LocalRealisticAxioms.BipartiteNoSignallingAnalyticCore n_A n_B) :
    threeChannelSpectralVarianceFunctional P₁ P₂ w₁ w₂ w_res x ≤
      ((w_max - w_min) / 2) ^ 2 * (hilbertEnergy x) ^ 2 ∧
      0 ≤ LayerC.BekensteinBound.bekensteinBound R_bek E_bek ∧
      (LayerC.LocalRealisticAxioms.bipartiteUnitaryQuantumNoSignalling n_A n_B hCore).SeparationPostulate ∧
      LayerC.BipartiteQubitCHSH.σx.IsHermitian ∧
      LayerC.BipartiteQubitCHSH.σz.IsHermitian := by
  have hbd := threeChannelSpectralVarianceFunctional_le_bhatiaDavis_and_popoviciu_sq_bound
    hP w₁ w₂ w_res w_min w_max hmin₁ hmin₂ hmin_r hmax₁ hmax₂ hmax_r x
  exact ⟨hbd.2.2,
    LayerC.BekensteinBound.bekensteinBound_nonneg R_bek E_bek hR hE,
    LayerC.LocalRealisticAxioms.bipartite_separationPostulate n_A n_B hCore,
    LayerC.BipartiteQubitCHSH.σx_isHermitian,
    LayerC.BipartiteQubitCHSH.σz_isHermitian⟩

/-- Master synthesis of the $3 \times 3$ mixed initial-and-final higher-power resolvent plaquette
grid and normalized three-channel spectral variance functional with all 15
SpectralRelEntropy/Stinespring/TopYukawa/TraceResolvent/Umegaki/YangMills/Bekenstein/Bipartite
modules. -/
theorem threeByThree_plaquetteGrid_spectralVariance_traceResolvent_umegaki_ym_bekenstein_bipartite_bridge_master
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ t₁ t₂ t₃ q a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ R_bek E_bek : ℝ)
    (ha₁ : 0 < a₁) (ha₃ : 0 < a₃) (he₁ : 0 < e₁) (he₃ : 0 < e₃)
    (hR : 0 ≤ R_bek) (hE : 0 ≤ E_bek)
    (r : ℕ) (f₁ f₂ f₃ : Hilbert)
    {P₁ P₂ : Hilbert →L[ℂ] Hilbert} (hP : AreMutuallyOrthogonalProjections P₁ P₂) :
    let w_grid := twoByTwoResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃
    let w_grid_eq := twoByTwoResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ t₁ t₂ t₁ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃
    w_grid = mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₃ t₁ t₃ a₁ a₃ e₁ e₃ r f₁ f₃ ∧
      w_grid_eq ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
      threeChannelSpectralVarianceFunctional P₁ P₂ 0 1 1 f₁ =
        threeChannelLagrangePairwiseSpread P₁ P₂ 0 1 1 f₁ ∧
      0 ≤ threeChannelSpectralVarianceFunctional P₁ P₂ 0 1 1 f₁ ∧
      LayerB.TopYukawaReaudit.cosSq_theta12 = 7 / 10 ∧
      LayerB.YangMillsCausalAttack.disc =
        LayerB.YangMillsCausalAttack.N_c + LayerB.YangMillsCausalAttack.d_eff ∧
      0 ≤ LayerC.BekensteinBound.bekensteinBound R_bek E_bek ∧
      LayerC.BipartiteQubitCHSH.σx.IsHermitian := by
  intro w_grid w_grid_eq
  have hstokes := twoByTwoPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃
  have hweq := twoByTwoResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ t₁ t₂ q a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ ha₁ ha₃ he₁ he₃ r f₁ f₂ f₃
  have hlag := threeChannelSpectralVarianceFunctional_eq_lagrangeSpread_and_nonneg
    hP 0 1 1 f₁
  exact ⟨hstokes.1, hweq.1, hlag.1, hlag.2.1,
    LayerB.TopYukawaReaudit.cosSq_theta12_eq_seven_tenths,
    LayerB.YangMillsCausalAttack.disc_is_gauge_plus_spacetime,
    LayerC.BekensteinBound.bekensteinBound_nonneg R_bek E_bek hR hE,
    LayerC.BipartiteQubitCHSH.σx_isHermitian⟩

#print axioms plaquetteGrid_stokes_with_spectralRelEntropy_stinespringDPI_and_topYukawaReaudit
#print axioms equalOuterFinalTime_resolventGrid_with_traceResolvent_umegakiTensor_and_unitaryInvariance
#print axioms centeredProjectorVariance_with_universalPrinciple_vecUnvec_and_yangMillsCausalAttack
#print axioms centeredProjectorVariance_popoviciu_with_bekensteinBound_bipartiteSeparation_and_bipartiteQubitCHSH
#print axioms threeByThree_plaquetteGrid_spectralVariance_traceResolvent_umegaki_ym_bekenstein_bipartite_bridge_master

end KFCausalCurved4DThreeByThreePlaquetteSpectralRelTraceResolventUmegakiYMBekensteinBipartiteBridge
end Audit
end UnifiedTheory
