/- Bridge of the Three-by-Three `(s₁, s₂, s₃) × (t₁, t₂, t₃)` Mixed Initial-and-Final
Higher-Power Resolvent Plaquette Grid with the 24 LayerB Choi-Matrix, Classical/Diagonal
Relative Entropy & DPI, Clay Physical Partition Function, Complex Uniqueness, Dark Matter,
Defect Algebra, and Honest Density Matrix Modules (`ChoiMatrix`..`DiagonalVonNeumannEntropy`). -/
import UnifiedTheory.Audit.KFCausalClockFloorThreeByThreeMixedInitialFinalHigherPowerResolventPlaquetteGrid
import UnifiedTheory.LayerB.ChoiMatrix
import UnifiedTheory.LayerB.ClassicalChannelDPI
import UnifiedTheory.LayerB.ClassicalEnsemble
import UnifiedTheory.LayerB.ClassicalEntropy
import UnifiedTheory.LayerB.ClassicalRelativeEntropy
import UnifiedTheory.LayerB.Clay1_ColorDressingVerification
import UnifiedTheory.LayerB.Clay3_PhysicalZ
import UnifiedTheory.LayerB.Clay3_StructureInputsDerivation
import UnifiedTheory.LayerB.ComplexFromDressing
import UnifiedTheory.LayerB.ComplexUniqueness
import UnifiedTheory.LayerB.CouplingConstantAudit
import UnifiedTheory.LayerB.CrossSectorIdentitySearch
import UnifiedTheory.LayerB.DarkMatter
import UnifiedTheory.LayerB.Decoherence
import UnifiedTheory.LayerB.DefectBridge
import UnifiedTheory.LayerB.DefectComposition
import UnifiedTheory.LayerB.DefectEquivalence
import UnifiedTheory.LayerB.DefectSector
import UnifiedTheory.LayerB.DensityMatrix
import UnifiedTheory.LayerB.DensityMatrixHonest
import UnifiedTheory.LayerB.DiagonalDensityMatrix
import UnifiedTheory.LayerB.DiagonalQuantumDPI
import UnifiedTheory.LayerB.DiagonalRelativeEntropy
import UnifiedTheory.LayerB.DiagonalVonNeumannEntropy

set_option autoImplicit false

namespace UnifiedTheory
namespace Audit
namespace KFCausalClockFloorThreeByThreePlaquetteChoiClassicalDPIClayPhysicalZDarkMatterDiagonalEntropyBridge

open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorHigherPowerOperatorCores (hamiltonianPowerDomain)
open KFCausalClockFloorTwoTimeMixedInitialFinalHigherPowerResolventPlaquette
  (mixedInitialFinalHigherPowerResolventPlaquette
   mixedInitialFinalHigherPowerIdentityPlaquette)
open KFCausalClockFloorThreeByThreeMixedInitialFinalHigherPowerResolventPlaquetteGrid
  (twoByTwoResolventPlaquetteGridSum
   twoByTwoIdentityPlaquetteGridSum
   twoByTwoPlaquetteGridSum_stokes_boundary_cancellation
   mixedInitialFinalHigherPowerPlaquette_three_initial_and_final_cyclic_cocycles
   twoByTwoResolventPlaquetteGridSum_mem_eight_domains_and_norm_le
   twoByTwoIdentityPlaquetteGridSum_mem_eight_domains_and_norm_le
   twoByTwoResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
   twoByTwoIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains)

/-- `3 × 3` resolvent plaquette grid 2D Stokes cancellation paired with Choi matrix linearity
(`ChoiMatrix`), classical stochastic pushforward identity (`ClassicalChannelDPI`), probability
bounds (`ClassicalEntropy`), and self-KL vanishing (`ClassicalRelativeEntropy`). -/
theorem plaquetteGrid_stokes_with_choiMatrix_classicalDPI_entropy_and_klSelf
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ : ℝ) (r : ℕ) (f₁ f₂ f₃ : Hilbert)
    {m_ch n_ch : ℕ}
    (L₁ L₂ : Matrix (Fin m_ch) (Fin m_ch) ℂ →ₗ[ℂ] Matrix (Fin n_ch) (Fin n_ch) ℂ)
    {α : Type*} [Fintype α] [DecidableEq α] (P_prob : LayerB.ClassicalEntropy.ProbabilityVector α)
    (a_idx : α) :
    twoByTwoResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₃ t₁ t₃ a₁ a₃ e₁ e₃ r f₁ f₃ ∧
    LayerB.Kraus.choi (L₁ + L₂) = LayerB.Kraus.choi L₁ + LayerB.Kraus.choi L₂ ∧
    ((LayerB.ClassicalChannelDPI.StochasticMatrix.id α).push P_prob).p a_idx = P_prob.p a_idx ∧
    P_prob.p a_idx ≤ 1 ∧
    LayerB.ClassicalRelativeEntropy.klDivergence P_prob P_prob = 0 := by
  have hstokes := twoByTwoPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃
  exact ⟨hstokes.1,
    LayerB.Kraus.choi_add L₁ L₂,
    LayerB.ClassicalChannelDPI.StochasticMatrix.id_push P_prob a_idx,
    LayerB.ClassicalEntropy.ProbabilityVector.le_one P_prob a_idx,
    LayerB.ClassicalRelativeEntropy.klDivergence_self_eq_zero P_prob⟩

/-- `3 × 3` identity plaquette grid 2D Stokes cancellation paired with Clay per-plaquette
action positivity (`Clay3_PhysicalZ`, `Clay3_StructureInputsDerivation`), K/P amplitude
observable `Q^2 + P^2` (`ComplexFromDressing`), coupling-constant audit (`CouplingConstantAudit`),
and cross-sector identity (`CrossSectorIdentitySearch`). -/
theorem identityPlaquetteGrid_stokes_with_clayPhysicalZ_complexFromDressing_and_couplingAudit
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ : ℝ) (r : ℕ) (f₁ f₂ f₃ : Hilbert)
    (Q_amp P_amp : ℝ) :
    twoByTwoIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃ =
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k
        s₁ s₃ t₁ t₃ a₁ a₃ e₁ e₃ r f₁ f₃ ∧
    0 < LayerB.Clay3_PhysicalZ.perPlaquetteActionMax ∧
    LayerB.obs (LayerB.amplitudeFromKP Q_amp P_amp) = Q_amp ^ 2 + P_amp ^ 2 ∧
    LayerB.CouplingConstantAudit.N_total = 5 ∧
    LayerB.CouplingConstantAudit.disc = 7 ∧
    LayerB.CrossSectorIdentitySearch.atom_disc =
      LayerB.CrossSectorIdentitySearch.atom_N_c + LayerB.CrossSectorIdentitySearch.atom_d_eff := by
  have hstokes := twoByTwoPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃
  exact ⟨hstokes.2,
    LayerB.Clay3_PhysicalZ.perPlaquetteActionMax_pos,
    LayerB.obs_from_KP Q_amp P_amp,
    LayerB.CouplingConstantAudit.N_total_eq,
    LayerB.CouplingConstantAudit.disc_eq,
    LayerB.CrossSectorIdentitySearch.disc_eq_Nc_plus_d⟩

/-- Equal-outer-final-time `Dom(H(t)^(r+2))` regularity of `twoByTwoResolventPlaquetteGridSum`
paired with P-sector dark-matter zero charge and positive energy (`DarkMatter`), phase-rotation
invariance (`Decoherence`), and composable defect charge additivity (`DefectComposition`). -/
theorem equalOuterFinalTime_resolventGrid_with_darkMatter_decoherence_and_defectComposition
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ t t₂ q a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ : ℝ)
    (ha₁ : 0 < a₁) (ha₃ : 0 < a₃) (he₁ : 0 < e₁) (he₃ : 0 < e₃)
    (r : ℕ) (f₁ f₂ f₃ : Hilbert)
    (P_dm θ : ℝ) (z_amp : ℂ)
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (db : LayerB.ComposableDefectBlock V) (d₁ d₂ : db.Defect) :
    twoByTwoResolventPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ t t₂ t a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃ ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    (LayerB.amplitudeFromKP 0 P_dm).re = 0 ∧
    LayerB.obs (LayerB.amplitudeFromKP 0 P_dm) = P_dm ^ 2 ∧
    LayerB.obs (LayerB.phaseRotate θ z_amp) = LayerB.obs z_amp ∧
    LayerB.charge db (db.compose d₁ d₂) = LayerB.charge db d₁ + LayerB.charge db d₂ := by
  have hweq := twoByTwoResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ t t₂ q a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ ha₁ ha₃ he₁ he₃ r f₁ f₂ f₃
  exact ⟨hweq.1,
    LayerB.DarkMatter.psector_zero_charge P_dm,
    LayerB.DarkMatter.psector_energy P_dm,
    LayerB.phase_rotate_obs z_amp θ,
    LayerB.charge_additive db d₁ d₂⟩

/-- Equal-outer-final-time `Dom(H(t)^(r+2))` regularity of `twoByTwoIdentityPlaquetteGridSum`
paired with two-state density matrix Born rule (`DensityMatrix`), PSD rejection of pathological
coherence (`DensityMatrixHonest`), diagonal density matrix entries (`DiagonalDensityMatrix`),
and diagonal relative/von Neumann entropy (`DiagonalRelativeEntropy`, `DiagonalVonNeumannEntropy`). -/
theorem equalOuterFinalTime_identityGrid_with_densityMatrixHonest_and_diagonalEntropy
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ t t₂ q a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ : ℝ)
    (ha₁ : 0 < a₁) (ha₃ : 0 < a₃) (he₁ : 0 < e₁) (he₃ : 0 < e₃)
    (r n_diag : ℕ) (f₁ f₂ f₃ : Hilbert) (z₁ z₂ : ℂ)
    (P_prob : LayerB.ClassicalEntropy.ProbabilityVector (Fin n_diag)) (i_idx : Fin n_diag) :
    twoByTwoIdentityPlaquetteGridSum ε hε h hh hb m g k
        s₁ s₂ s₃ t t₂ t a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃ ∈
      hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
    LayerB.DensityMatrix.totalObs (LayerB.DensityMatrix.fromAmplitudes z₁ z₂) =
      LayerB.obs (z₁ + z₂) ∧
    (¬ ∃ ρ : LayerB.DensityMatrixHonest.DensityMatrix2Honest, ρ.p₁ = 0 ∧ ρ.coh_re = 5) ∧
    (LayerB.DiagonalDensityMatrix.diagonalDensityMatrix P_prob).M i_idx i_idx =
      (P_prob.p i_idx : ℂ) ∧
    LayerB.DiagonalRelativeEntropy.relativeEntropyDiagonal P_prob P_prob = 0 ∧
    0 ≤ LayerB.DiagonalVonNeumannEntropy.vonNeumannEntropyDiagonal P_prob := by
  have hyeq := twoByTwoIdentityPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ t t₂ q a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ ha₁ ha₃ he₁ he₃ r f₁ f₂ f₃
  exact ⟨hyeq.1,
    LayerB.DensityMatrix.totalObs_eq_born z₁ z₂,
    LayerB.DensityMatrixHonest.pathological_rejected_by_PSD_alone,
    LayerB.DiagonalDensityMatrix.diagonalDensityMatrix_apply_eq P_prob i_idx,
    LayerB.DiagonalRelativeEntropy.relativeEntropyDiagonal_self_eq_zero P_prob,
    LayerB.DiagonalVonNeumannEntropy.vonNeumannEntropyDiagonal_nonneg P_prob⟩

/-- Cyclic 3-step initial-and-final plaquette cocycles paired with diagonal von Neumann / Shannon
entropy equality (`DiagonalVonNeumannEntropy`) and diagonal relative / KL divergence equality
(`DiagonalRelativeEntropy`). -/
theorem cyclicPlaquetteCocycles_with_diagonalVonNeumann_and_diagonalRelativeEntropy_eq_shannon_kl
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ : ℝ) (r : ℕ) (f₁ f₂ f₃ : Hilbert)
    {α : Type*} [Fintype α] (P_prob Q_prob : LayerB.ClassicalEntropy.ProbabilityVector α) :
    mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ c₁ c₂ r f₁ f₂ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ c₂ c₃ r f₂ f₃ +
      mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₃ s₁ t₁ t₂ a₃ a₁ c₃ c₁ r f₃ f₁ = 0 ∧
    LayerB.DiagonalVonNeumannEntropy.vonNeumannEntropyDiagonal P_prob =
      LayerB.ClassicalEntropy.ProbabilityVector.shannonEntropy P_prob ∧
    LayerB.DiagonalRelativeEntropy.relativeEntropyDiagonal P_prob Q_prob =
      LayerB.ClassicalRelativeEntropy.klDivergence P_prob Q_prob := by
  have hcoc := mixedInitialFinalHigherPowerPlaquette_three_initial_and_final_cyclic_cocycles
    ε hε h hh hb m g k s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ r f₁ f₂ f₃
  exact ⟨hcoc.2.1,
    LayerB.DiagonalVonNeumannEntropy.vonNeumannEntropyDiagonal_eq_shannon P_prob,
    LayerB.DiagonalRelativeEntropy.relativeEntropyDiagonal_eq_kl P_prob Q_prob⟩

/-- Master synthesis of the `3 × 3` mixed initial-and-final higher-power resolvent plaquette
grid with all 24 Choi/ClassicalDPI/ClayPhysicalZ/Complex/DarkMatter/Defect/DiagonalEntropy modules. -/
theorem threeByThree_plaquetteGrid_choi_classicalDPI_clayPhysicalZ_darkMatter_diagonalEntropy_bridge_master
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ t₁ t₂ t₃ q a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ : ℝ)
    (ha₁ : 0 < a₁) (ha₃ : 0 < a₃) (he₁ : 0 < e₁) (he₃ : 0 < e₃)
    (r : ℕ) (f₁ f₂ f₃ : Hilbert) (P_dm : ℝ)
    {α : Type*} [Fintype α] (P_prob : LayerB.ClassicalEntropy.ProbabilityVector α) :
    let w_grid := twoByTwoResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃
    let w_grid_eq := twoByTwoResolventPlaquetteGridSum ε hε h hh hb m g k
      s₁ s₂ s₃ t₁ t₂ t₁ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃
    w_grid = mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k
        s₁ s₃ t₁ t₃ a₁ a₃ e₁ e₃ r f₁ f₃ ∧
      w_grid_eq ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
      0 < LayerB.Clay3_PhysicalZ.perPlaquetteActionMax ∧
      LayerB.CouplingConstantAudit.disc = 7 ∧
      (LayerB.amplitudeFromKP 0 P_dm).re = 0 ∧
      LayerB.obs (LayerB.amplitudeFromKP 0 P_dm) = P_dm ^ 2 ∧
      (¬ ∃ ρ : LayerB.DensityMatrixHonest.DensityMatrix2Honest, ρ.p₁ = 0 ∧ ρ.coh_re = 5) ∧
      LayerB.DiagonalRelativeEntropy.relativeEntropyDiagonal P_prob P_prob = 0 ∧
      0 ≤ LayerB.DiagonalVonNeumannEntropy.vonNeumannEntropyDiagonal P_prob := by
  intro w_grid w_grid_eq
  have hstokes := twoByTwoPlaquetteGridSum_stokes_boundary_cancellation
    ε hε h hh hb m g k s₁ s₂ s₃ t₁ t₂ t₃ a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ r f₁ f₂ f₃
  have hweq := twoByTwoResolventPlaquetteGridSum_equal_outer_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ t₁ t₂ q a₁ a₂ a₃ c₁ c₂ c₃ e₁ e₂ e₃ ha₁ ha₃ he₁ he₃ r f₁ f₂ f₃
  exact ⟨hstokes.1, hweq.1,
    LayerB.Clay3_PhysicalZ.perPlaquetteActionMax_pos,
    LayerB.CouplingConstantAudit.disc_eq,
    LayerB.DarkMatter.psector_zero_charge P_dm,
    LayerB.DarkMatter.psector_energy P_dm,
    LayerB.DensityMatrixHonest.pathological_rejected_by_PSD_alone,
    LayerB.DiagonalRelativeEntropy.relativeEntropyDiagonal_self_eq_zero P_prob,
    LayerB.DiagonalVonNeumannEntropy.vonNeumannEntropyDiagonal_nonneg P_prob⟩

#print axioms plaquetteGrid_stokes_with_choiMatrix_classicalDPI_entropy_and_klSelf
#print axioms identityPlaquetteGrid_stokes_with_clayPhysicalZ_complexFromDressing_and_couplingAudit
#print axioms equalOuterFinalTime_resolventGrid_with_darkMatter_decoherence_and_defectComposition
#print axioms equalOuterFinalTime_identityGrid_with_densityMatrixHonest_and_diagonalEntropy
#print axioms cyclicPlaquetteCocycles_with_diagonalVonNeumann_and_diagonalRelativeEntropy_eq_shannon_kl
#print axioms threeByThree_plaquetteGrid_choi_classicalDPI_clayPhysicalZ_darkMatter_diagonalEntropy_bridge_master

end KFCausalClockFloorThreeByThreePlaquetteChoiClassicalDPIClayPhysicalZDarkMatterDiagonalEntropyBridge
end Audit
end UnifiedTheory
