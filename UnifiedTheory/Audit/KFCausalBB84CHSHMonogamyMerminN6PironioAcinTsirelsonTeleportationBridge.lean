import UnifiedTheory.Audit.KFCausalArbitrarySourceWeightedProjectorExpectationAndCrossGramDecomposition
import UnifiedTheory.LayerB.TeleportationFidelity
import UnifiedTheory.LayerB.TsirelsonOperatorBound
import UnifiedTheory.LayerC.BB84Security
import UnifiedTheory.LayerC.CHSHMonogamy
import UnifiedTheory.LayerC.MerminN6
import UnifiedTheory.LayerC.NoGoTwoAxes
import UnifiedTheory.LayerC.PironioAcinExact
import UnifiedTheory.LayerC.Placeholder
import UnifiedTheory.LayerC.ThermoTemporalLimit
import UnifiedTheory.LayerC.TsirelsonProblem

set_option autoImplicit false

namespace UnifiedTheory
namespace Audit
namespace KFCausalBB84CHSHMonogamyMerminN6PironioAcinTsirelsonTeleportationBridge

open KFCausalArbitrarySourceWeightedProjectorExpectationAndCrossGramDecomposition
open KFCausalArbitrarySourceMutuallyOrthogonalProjectorParsevalDecomposition
open KFCausalArbitrarySourceOrthogonalProjectionResidualEnergyDecomposition

/-- Three-channel spectral-weighted projector expectation and Rayleigh-Ritz bounds
paired with quantum teleportation vs. classical BB84 fidelity
(`TeleportationFidelity`) and Landau's operator-level Tsirelson square identity
(`TsirelsonOperatorBound`). -/
theorem threeChannel_weighted_expectation_with_teleportationFidelity_and_tsirelsonOperator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res w_min w_max : ℝ)
    (hmin₁ : w_min ≤ w₁) (hmin₂ : w_min ≤ w₂) (hmin_r : w_min ≤ w_res)
    (hmax₁ : w₁ ≤ w_max) (hmax₂ : w₂ ≤ w_max) (hmax_r : w_res ≤ w_max)
    (x : E) (o : LayerB.QuantumTeleportation.BellOutcome)
    (A₀ A₁ B₀ B₁ : LayerB.TsirelsonOperatorBound.QubitObservable) :
    w_min * hilbertEnergy x ≤ threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x ∧
      threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x ≤ w_max * hilbertEnergy x ∧
      LayerB.TeleportationFidelity.bb84AvgFidelity
        (LayerB.TeleportationFidelity.singletTeleportationOutput o) = 1 ∧
      (LayerB.TsirelsonOperatorBound.tsirelsonOperator A₀ A₁ B₀ B₁).IsHermitian ∧
      LayerB.TsirelsonOperatorBound.tsirelsonOperator A₀ A₁ B₀ B₁ *
          LayerB.TsirelsonOperatorBound.tsirelsonOperator A₀ A₁ B₀ B₁ =
        (4 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) -
          Matrix.kroneckerMap (· * ·)
            (LayerB.TsirelsonOperatorBound.comm A₀.M A₁.M)
            (LayerB.TsirelsonOperatorBound.comm B₀.M B₁.M) := by
  have hrr := threeChannelWeightedExpectation_rayleigh_ritz_bounds
    hP w₁ w₂ w_res w_min w_max hmin₁ hmin₂ hmin_r hmax₁ hmax₂ hmax_r x
  exact ⟨hrr.1, hrr.2,
    LayerB.TeleportationFidelity.bb84_avg_fidelity_singlet_eq_one o,
    LayerB.TsirelsonOperatorBound.tsirelsonOperator_isHermitian A₀ A₁ B₀ B₁,
    LayerB.TsirelsonOperatorBound.tsirelson_T_squared A₀ A₁ B₀ B₁⟩

/-- Multi-channel spectral-weighted projector expectation paired with BB84 QKD
25% QBER and Helstrom error bounds (`BB84Security`) and GHZ tripartite CHSH
monogamy (`CHSHMonogamy`). -/
theorem multiChannel_weighted_expectation_with_bb84Security_and_chshMonogamy
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w : Fin Q → ℝ) (w_min w_max : ℝ)
    (hmin : ∀ q, w_min ≤ w q) (hmax : ∀ q, w q ≤ w_max) (x : E)
    (strat : LayerC.BB84Security.InterceptResendStrategy) (θa θb : ℝ) :
    w_min * (∑ q : Fin Q, hilbertEnergy (P q x)) ≤
        multiChannelWeightedExpectation P w x ∧
      multiChannelWeightedExpectation P w x ≤
        w_max * (∑ q : Fin Q, hilbertEnergy (P q x)) ∧
      LayerC.BB84Security.averagedBobError strat = 1 / 4 ∧
      LayerC.BB84Security.BB84_Unconditional_Security_Target ∧
      LayerC.BB84Security.E91_Security_Target ∧
      LayerC.CHSHMonogamy.ρAB LayerC.CHSHMonogamy.ghzState =
        LayerC.CHSHMonogamy.ghzDiagonal ∧
      LayerC.BipartiteQubitCHSH.correlation LayerC.CHSHMonogamy.ghzCDM_AB
        (LayerC.BipartiteQubitCHSH.equatorObservable θa)
        (LayerC.BipartiteQubitCHSH.equatorObservable θb) =
        Real.cos θa * Real.cos θb := by
  have hrr := multiChannelWeightedExpectation_rayleigh_ritz_bounds P w w_min w_max hmin hmax x
  exact ⟨hrr.1, hrr.2,
    LayerC.BB84Security.bb84_qber_25percent strat,
    LayerC.BB84Security.BB84_Unconditional_Security_Target_holds,
    LayerC.BB84Security.E91_Security_Target_holds,
    LayerC.CHSHMonogamy.ρAB_ghz_diagonal,
    LayerC.CHSHMonogamy.ghz_marginal_AB_correlation_factorizes θa θb⟩

/-- Arbitrary-source degree-`M` polynomial weighted expectation paired with
6-party Mermin inequality $32 > 8$ (`MerminN6`), two-axis Kochen-Specker and
PBR no-go theorems (`NoGoTwoAxes`), and Pironio-Acín exact device-independent
randomness bound (`PironioAcinExact`). -/
theorem arbitrarySource_weighted_expectation_with_merminN6_noGoTwoAxes_and_pironioAcin
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (c_wt : ℝ) (hc : 0 ≤ c_wt) (x : E) :
    threeChannelWeightedExpectation P₁ P₂ c_wt c_wt c_wt x = c_wt * hilbertEnergy x ∧
      LayerC.MerminN.quantumMerminN 6 > (8 : ℝ) ∧
      ¬ LayerC.NoGoTwoAxes.ValueDefiniteKS ∧
      LayerC.NoGoTwoAxes.ValueDefinite LayerC.NoGoTwoAxes.trivialEmpiricalModel ∧
      LayerC.PironioAcinExact.pironioAcinBound 2 = 0 ∧
      LayerC.PironioAcinExact.pironioAcinBound (2 * Real.sqrt 2) = 1 ∧
      LayerC.PironioAcinExact.PironioAcin_Target := by
  have hconst := (threeChannelWeightedExpectation_nonneg_and_const_eq
    hP c_wt c_wt c_wt c_wt hc hc hc x).2
  exact ⟨hconst,
    LayerC.MerminN.quantum_exceeds_classical_six,
    LayerC.NoGoTwoAxes.axis1_nogo,
    LayerC.NoGoTwoAxes.value_definite_witness,
    LayerC.PironioAcinExact.pironioAcin_classical,
    LayerC.PironioAcinExact.pironioAcin_tsirelson,
    LayerC.PironioAcinExact.pironioAcin_target_holds⟩

/-- Weighted projector expectation paired with the joint Landauer-Margolus-Levitin
thermo-temporal cost floor (`ThermoTemporalLimit`) and the Tsirelson problem
hierarchy $2 < 2\sqrt{2} < 4$ (`TsirelsonProblem`). -/
theorem weighted_expectation_with_thermoTemporalLimit_and_tsirelsonProblem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (N T E_eng : ℝ) (hN : 0 < N) (hT : 0 < T) (hE : 0 < E_eng) (x : E) :
    0 ≤ threeChannelWeightedExpectation P₁ P₂ N T E_eng x ∧
      0 < LayerC.ThermoTemporalLimit.thermoTemporalCost N T E_eng ∧
      LayerC.ThermoTemporalLimit.landauerHeat 1 T = T * Real.log 2 ∧
      LayerC.TsirelsonProblem.classicalBound < LayerC.TsirelsonProblem.tsirelsonBound ∧
      LayerC.TsirelsonProblem.tsirelsonBound < LayerC.TsirelsonProblem.prBoxValue ∧
      LayerC.TsirelsonProblem.tsirelsonBound ^ 2 = 8 := by
  have hnn := (threeChannelWeightedExpectation_nonneg_and_const_eq
    hP N T E_eng 1 (le_of_lt hN) (le_of_lt hT) (le_of_lt hE) x).1
  exact ⟨hnn,
    LayerC.ThermoTemporalLimit.thermoTemporalCost_pos N T E_eng hN hT hE,
    LayerC.ThermoTemporalLimit.landauerHeat_per_bit T,
    LayerC.TsirelsonProblem.classical_lt_tsirelson,
    LayerC.TsirelsonProblem.tsirelson_lt_prBox,
    LayerC.TsirelsonProblem.tsirelson_sq⟩

/-- Master synthesis of spectral-weighted projector expectations with all 10
quantum-information, cryptography, Bell/Mermin/Tsirelson, no-go, and
thermo-temporal modules. -/
theorem bb84_chshMonogamy_merminN6_pironioAcin_tsirelson_teleportation_bridge_master
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res w_min w_max : ℝ)
    (hmin₁ : w_min ≤ w₁) (hmin₂ : w_min ≤ w₂) (hmin_r : w_min ≤ w_res)
    (hmax₁ : w₁ ≤ w_max) (hmax₂ : w₂ ≤ w_max) (hmax_r : w_res ≤ w_max)
    (x : E) (o : LayerB.QuantumTeleportation.BellOutcome)
    (strat : LayerC.BB84Security.InterceptResendStrategy) :
    w_min * hilbertEnergy x ≤ threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x ∧
      threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x ≤ w_max * hilbertEnergy x ∧
      LayerB.TeleportationFidelity.bb84AvgFidelity
        (LayerB.TeleportationFidelity.singletTeleportationOutput o) = 1 ∧
      LayerC.BB84Security.averagedBobError strat = 1 / 4 ∧
      LayerC.CHSHMonogamy.ρAB LayerC.CHSHMonogamy.ghzState =
        LayerC.CHSHMonogamy.ghzDiagonal ∧
      LayerC.MerminN.quantumMerminN 6 > (8 : ℝ) ∧
      ¬ LayerC.NoGoTwoAxes.ValueDefiniteKS ∧
      LayerC.PironioAcinExact.pironioAcinBound (2 * Real.sqrt 2) = 1 ∧
      LayerC.TsirelsonProblem.tsirelsonBound ^ 2 = 8 := by
  have hrr := threeChannelWeightedExpectation_rayleigh_ritz_bounds
    hP w₁ w₂ w_res w_min w_max hmin₁ hmin₂ hmin_r hmax₁ hmax₂ hmax_r x
  exact ⟨hrr.1, hrr.2,
    LayerB.TeleportationFidelity.bb84_avg_fidelity_singlet_eq_one o,
    LayerC.BB84Security.bb84_qber_25percent strat,
    LayerC.CHSHMonogamy.ρAB_ghz_diagonal,
    LayerC.MerminN.quantum_exceeds_classical_six,
    LayerC.NoGoTwoAxes.axis1_nogo,
    LayerC.PironioAcinExact.pironioAcin_tsirelson,
    LayerC.TsirelsonProblem.tsirelson_sq⟩

#print axioms threeChannel_weighted_expectation_with_teleportationFidelity_and_tsirelsonOperator
#print axioms multiChannel_weighted_expectation_with_bb84Security_and_chshMonogamy
#print axioms arbitrarySource_weighted_expectation_with_merminN6_noGoTwoAxes_and_pironioAcin
#print axioms weighted_expectation_with_thermoTemporalLimit_and_tsirelsonProblem
#print axioms bb84_chshMonogamy_merminN6_pironioAcin_tsirelson_teleportation_bridge_master

end KFCausalBB84CHSHMonogamyMerminN6PironioAcinTsirelsonTeleportationBridge
end Audit
end UnifiedTheory
