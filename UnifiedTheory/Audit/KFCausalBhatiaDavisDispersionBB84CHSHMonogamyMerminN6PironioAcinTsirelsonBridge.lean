import UnifiedTheory.Audit.KFCausalArbitrarySourceWeightedProjectorVarianceAndBhatiaDavisInequality
import UnifiedTheory.Audit.KFCausalBB84CHSHMonogamyMerminN6PironioAcinTsirelsonTeleportationBridge

set_option autoImplicit false

namespace UnifiedTheory
namespace Audit
namespace KFCausalBhatiaDavisDispersionBB84CHSHMonogamyMerminN6PironioAcinTsirelsonBridge

open KFCausalArbitrarySourceWeightedProjectorVarianceAndBhatiaDavisInequality
open KFCausalBB84CHSHMonogamyMerminN6PironioAcinTsirelsonTeleportationBridge
open KFCausalArbitrarySourceMutuallyOrthogonalProjectorParsevalDecomposition
open KFCausalArbitrarySourceOrthogonalProjectionResidualEnergyDecomposition
open scoped BigOperators

/-- Three-channel Bhatia-Davis / Popoviciu spectral dispersion inequality paired
with quantum teleportation vs. classical BB84 fidelity (`TeleportationFidelity`)
and Landau's operator-level Tsirelson square identity (`TsirelsonOperatorBound`). -/
theorem threeChannel_bhatiaDavis_with_teleportationFidelity_and_tsirelsonOperator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res w_min w_max : ℝ)
    (hmin₁ : w_min ≤ w₁) (hmin₂ : w_min ≤ w₂) (hmin_r : w_min ≤ w_res)
    (hmax₁ : w₁ ≤ w_max) (hmax₂ : w₂ ≤ w_max) (hmax_r : w_res ≤ w_max)
    (x : E) (o : LayerB.QuantumTeleportation.BellOutcome)
    (A₀ A₁ B₀ B₁ : LayerB.TsirelsonOperatorBound.QubitObservable) :
    0 ≤ threeChannelBhatiaDavisFunctional P₁ P₂ w₁ w₂ w_res w_min w_max x ∧
      threeChannelBhatiaDavisFunctional P₁ P₂ w₁ w₂ w_res w_min w_max x ≤
        ((w_max - w_min) / 2) ^ 2 * hilbertEnergy x ∧
      LayerB.TeleportationFidelity.bb84AvgFidelity
        (LayerB.TeleportationFidelity.singletTeleportationOutput o) = 1 ∧
      (LayerB.TsirelsonOperatorBound.tsirelsonOperator A₀ A₁ B₀ B₁).IsHermitian ∧
      LayerB.TsirelsonOperatorBound.tsirelsonOperator A₀ A₁ B₀ B₁ *
          LayerB.TsirelsonOperatorBound.tsirelsonOperator A₀ A₁ B₀ B₁ =
        (4 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) -
          Matrix.kroneckerMap (· * ·)
            (LayerB.TsirelsonOperatorBound.comm A₀.M A₁.M)
            (LayerB.TsirelsonOperatorBound.comm B₀.M B₁.M) := by
  have hbd := threeChannelBhatiaDavisFunctional_nonneg_and_popoviciu_bound
    hP w₁ w₂ w_res w_min w_max hmin₁ hmin₂ hmin_r hmax₁ hmax₂ hmax_r x
  exact ⟨hbd.1, hbd.2,
    LayerB.TeleportationFidelity.bb84_avg_fidelity_singlet_eq_one o,
    LayerB.TsirelsonOperatorBound.tsirelsonOperator_isHermitian A₀ A₁ B₀ B₁,
    LayerB.TsirelsonOperatorBound.tsirelson_T_squared A₀ A₁ B₀ B₁⟩

/-- Multi-channel Bhatia-Davis / Popoviciu spectral dispersion inequality paired
with BB84 QKD 25% QBER (`BB84Security`) and GHZ tripartite CHSH monogamy (`CHSHMonogamy`). -/
theorem multiChannel_bhatiaDavis_with_bb84Security_and_chshMonogamy
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w : Fin Q → ℝ) (w_min w_max : ℝ)
    (hmin : ∀ q, w_min ≤ w q) (hmax : ∀ q, w q ≤ w_max) (x : E)
    (strat : LayerC.BB84Security.InterceptResendStrategy) (θa θb : ℝ) :
    0 ≤ multiChannelBhatiaDavisFunctional P w w_min w_max x ∧
      multiChannelBhatiaDavisFunctional P w w_min w_max x ≤
        ((w_max - w_min) / 2) ^ 2 * (∑ q : Fin Q, hilbertEnergy (P q x)) ∧
      LayerC.BB84Security.averagedBobError strat = 1 / 4 ∧
      LayerC.BB84Security.BB84_Unconditional_Security_Target ∧
      LayerC.BB84Security.E91_Security_Target ∧
      LayerC.CHSHMonogamy.ρAB LayerC.CHSHMonogamy.ghzState =
        LayerC.CHSHMonogamy.ghzDiagonal ∧
      LayerC.BipartiteQubitCHSH.correlation LayerC.CHSHMonogamy.ghzCDM_AB
        (LayerC.BipartiteQubitCHSH.equatorObservable θa)
        (LayerC.BipartiteQubitCHSH.equatorObservable θb) =
        Real.cos θa * Real.cos θb := by
  have hbd := multiChannelBhatiaDavisFunctional_nonneg_and_popoviciu_bound
    P w w_min w_max hmin hmax x
  exact ⟨hbd.1, hbd.2,
    LayerC.BB84Security.bb84_qber_25percent strat,
    LayerC.BB84Security.BB84_Unconditional_Security_Target_holds,
    LayerC.BB84Security.E91_Security_Target_holds,
    LayerC.CHSHMonogamy.ρAB_ghz_diagonal,
    LayerC.CHSHMonogamy.ghz_marginal_AB_correlation_factorizes θa θb⟩

/-- Factored three-channel Bhatia-Davis identity and second-moment nonnegativity
paired with 6-party Mermin inequality $32 > 8$ (`MerminN6`), two-axis Kochen-Specker
no-go (`NoGoTwoAxes`), and Pironio-Acín device-independent randomness (`PironioAcinExact`). -/
theorem threeChannel_secondMoment_with_merminN6_noGoTwoAxes_and_pironioAcin
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res w_min w_max : ℝ) (x : E) :
    0 ≤ threeChannelWeightedSecondMoment P₁ P₂ w₁ w₂ w_res x ∧
      threeChannelBhatiaDavisFunctional P₁ P₂ w₁ w₂ w_res w_min w_max x =
        (w_max - w₁) * (w₁ - w_min) * hilbertEnergy (P₁ x) +
        (w_max - w₂) * (w₂ - w_min) * hilbertEnergy (P₂ x) +
        (w_max - w_res) * (w_res - w_min) * hilbertEnergy (residualTwoProjector P₁ P₂ x) ∧
      LayerC.MerminN.quantumMerminN 6 > (8 : ℝ) ∧
      ¬ LayerC.NoGoTwoAxes.ValueDefiniteKS ∧
      LayerC.PironioAcinExact.pironioAcinBound 2 = 0 ∧
      LayerC.PironioAcinExact.pironioAcinBound (2 * Real.sqrt 2) = 1 ∧
      LayerC.PironioAcinExact.PironioAcin_Target := by
  have hfac := threeChannelBhatiaDavisFunctional_factored_eq_and_secondMoment_nonneg
    hP w₁ w₂ w_res w_min w_max x
  exact ⟨hfac.1, hfac.2,
    LayerC.MerminN.quantum_exceeds_classical_six,
    LayerC.NoGoTwoAxes.axis1_nogo,
    LayerC.PironioAcinExact.pironioAcin_classical,
    LayerC.PironioAcinExact.pironioAcin_tsirelson,
    LayerC.PironioAcinExact.pironioAcin_target_holds⟩

/-- Three-channel spectral second moment nonnegativity paired with the joint
Landauer-Margolus-Levitin thermo-temporal cost floor (`ThermoTemporalLimit`) and
the Tsirelson problem hierarchy $2 < 2\sqrt{2} < 4$ (`TsirelsonProblem`). -/
theorem threeChannel_secondMoment_with_thermoTemporalLimit_and_tsirelsonProblem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (N T E_eng : ℝ) (hN : 0 < N) (hT : 0 < T) (hE : 0 < E_eng) (x : E) :
    0 ≤ threeChannelWeightedSecondMoment P₁ P₂ N T E_eng x ∧
      0 < LayerC.ThermoTemporalLimit.thermoTemporalCost N T E_eng ∧
      LayerC.ThermoTemporalLimit.landauerHeat 1 T = T * Real.log 2 ∧
      LayerC.TsirelsonProblem.classicalBound < LayerC.TsirelsonProblem.tsirelsonBound ∧
      LayerC.TsirelsonProblem.tsirelsonBound < LayerC.TsirelsonProblem.prBoxValue ∧
      LayerC.TsirelsonProblem.tsirelsonBound ^ 2 = 8 := by
  have hnn := (threeChannelBhatiaDavisFunctional_factored_eq_and_secondMoment_nonneg
    hP N T E_eng 0 1 x).1
  exact ⟨hnn,
    LayerC.ThermoTemporalLimit.thermoTemporalCost_pos N T E_eng hN hT hE,
    LayerC.ThermoTemporalLimit.landauerHeat_per_bit T,
    LayerC.TsirelsonProblem.classical_lt_tsirelson,
    LayerC.TsirelsonProblem.tsirelson_lt_prBox,
    LayerC.TsirelsonProblem.tsirelson_sq⟩

/-- Master synthesis of Bhatia-Davis / Popoviciu spectral dispersion inequalities
with all 10 quantum-information, cryptography, Bell/Mermin/Tsirelson, no-go, and
thermo-temporal modules. -/
theorem bhatiaDavis_bb84_chshMonogamy_merminN6_pironioAcin_tsirelson_bridge_master
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res w_min w_max : ℝ)
    (hmin₁ : w_min ≤ w₁) (hmin₂ : w_min ≤ w₂) (hmin_r : w_min ≤ w_res)
    (hmax₁ : w₁ ≤ w_max) (hmax₂ : w₂ ≤ w_max) (hmax_r : w_res ≤ w_max)
    (x : E) (o : LayerB.QuantumTeleportation.BellOutcome)
    (strat : LayerC.BB84Security.InterceptResendStrategy) :
    0 ≤ threeChannelBhatiaDavisFunctional P₁ P₂ w₁ w₂ w_res w_min w_max x ∧
      threeChannelBhatiaDavisFunctional P₁ P₂ w₁ w₂ w_res w_min w_max x ≤
        ((w_max - w_min) / 2) ^ 2 * hilbertEnergy x ∧
      LayerB.TeleportationFidelity.bb84AvgFidelity
        (LayerB.TeleportationFidelity.singletTeleportationOutput o) = 1 ∧
      LayerC.BB84Security.averagedBobError strat = 1 / 4 ∧
      LayerC.CHSHMonogamy.ρAB LayerC.CHSHMonogamy.ghzState =
        LayerC.CHSHMonogamy.ghzDiagonal ∧
      LayerC.MerminN.quantumMerminN 6 > (8 : ℝ) ∧
      ¬ LayerC.NoGoTwoAxes.ValueDefiniteKS ∧
      LayerC.PironioAcinExact.pironioAcinBound (2 * Real.sqrt 2) = 1 ∧
      LayerC.TsirelsonProblem.tsirelsonBound ^ 2 = 8 := by
  have hbd := threeChannelBhatiaDavisFunctional_nonneg_and_popoviciu_bound
    hP w₁ w₂ w_res w_min w_max hmin₁ hmin₂ hmin_r hmax₁ hmax₂ hmax_r x
  exact ⟨hbd.1, hbd.2,
    LayerB.TeleportationFidelity.bb84_avg_fidelity_singlet_eq_one o,
    LayerC.BB84Security.bb84_qber_25percent strat,
    LayerC.CHSHMonogamy.ρAB_ghz_diagonal,
    LayerC.MerminN.quantum_exceeds_classical_six,
    LayerC.NoGoTwoAxes.axis1_nogo,
    LayerC.PironioAcinExact.pironioAcin_tsirelson,
    LayerC.TsirelsonProblem.tsirelson_sq⟩

#print axioms threeChannel_bhatiaDavis_with_teleportationFidelity_and_tsirelsonOperator
#print axioms multiChannel_bhatiaDavis_with_bb84Security_and_chshMonogamy
#print axioms threeChannel_secondMoment_with_merminN6_noGoTwoAxes_and_pironioAcin
#print axioms threeChannel_secondMoment_with_thermoTemporalLimit_and_tsirelsonProblem
#print axioms bhatiaDavis_bb84_chshMonogamy_merminN6_pironioAcin_tsirelson_bridge_master

end KFCausalBhatiaDavisDispersionBB84CHSHMonogamyMerminN6PironioAcinTsirelsonBridge
end Audit
end UnifiedTheory
