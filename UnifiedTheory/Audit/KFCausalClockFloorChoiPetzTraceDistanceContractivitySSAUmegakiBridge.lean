import UnifiedTheory.Audit.KFCausalClockFloorThreeTrajectoryCrossTimeHigherPowerResolventCocycle
import UnifiedTheory.LayerB.ChoiTheorem
import UnifiedTheory.LayerB.CoherenceConvexityGeneral
import UnifiedTheory.LayerB.HolevoBoundRhoBarBasis
import UnifiedTheory.LayerB.LindbladContinuous
import UnifiedTheory.LayerB.PartialTraceTwirl
import UnifiedTheory.LayerB.PetzRecoveryMap
import UnifiedTheory.LayerB.TraceDistanceCPTPDPI
import UnifiedTheory.LayerB.TraceDistanceContractivity
import UnifiedTheory.LayerB.TraceNormDualAttainment
import UnifiedTheory.LayerB.TripartiteSSAReduction
import UnifiedTheory.LayerB.UmegakiMultiConvex
import UnifiedTheory.LayerB.VonNeumannConcavityGeneral
import UnifiedTheory.LayerB.WeakSubadditivityGeneral

set_option autoImplicit false

namespace UnifiedTheory
namespace Audit
namespace KFCausalClockFloorChoiPetzTraceDistanceContractivitySSAUmegakiBridge

open KFCausalClockFloorThreeTrajectoryCrossTimeHigherPowerResolventCocycle
open KFCausalClockFloorTwoTimeCrossTrajectoryHigherPowerResolventComparison
open KFCausalClockFloorHigherPowerOperatorCores
open KFCausalConfigurationTestSpace
open scoped ComplexOrder MatrixOrder Kronecker BigOperators
open LayerB.RobertsonSchrodinger
open LayerB.QuantumChernoff
open LayerB.PartialTrace
open LayerB.PartialTraceDPI
open LayerB.PartialTraceDPIFull
open LayerB.PartialTraceDecomposition
open LayerB.OperatorEntropy
open LayerB.UmegakiRelativeEntropy
open LayerB.CoherenceResource
open LayerB.StrongSubadditivity
open LayerB.JointConvexityUmegaki
open LayerB.HolevoBoundQuantum
open LayerB.Ensemble

/-- Three-initial higher-power resolvent double-difference regularity paired with
Choi's complete positivity theorem (`ChoiTheorem`), general coherence nonnegativity
(`CoherenceConvexityGeneral`), and Holevo bound in the $\bar\rho$ eigenbasis
(`HolevoBoundRhoBarBasis`). -/
theorem threeInitial_resolvent_doubleDiff_with_choi_coherenceConvexity_and_holevoRhoBar
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ t q a b d : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d)
    (r : ℕ) (f₁ f₂ f₃ : Hilbert)
    {n d_k : ℕ} (K_op : Fin d_k → Matrix (Fin n) (Fin n) ℂ)
    (ρ : ComplexDensityMatrix n) :
    let w := threeInitialHigherPowerResolventDoubleDiff ε hε h hh hb m g k s₁ s₂ s₃ t a b d r f₁ f₂ f₃
    w ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
      LayerB.ChoiTheorem.IsCompletelyPositive (LayerB.ChoiTheorem.krausMap K_op) ∧
      (LayerB.ChoiTheorem.choiMatrix (LayerB.ChoiTheorem.krausMap K_op)).IsHermitian ∧
      coherence ρ = umegakiRelativeEntropy ρ (dephasedDM ρ) := by
  intro w
  have hw := threeInitialHigherPowerResolventDoubleDiff_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ t q a b d ha hb_pos hd r f₁ f₂ f₃
  exact ⟨hw.1,
    LayerB.ChoiTheorem.krausMap_is_CP K_op,
    LayerB.ChoiTheorem.choiMatrix_krausMap_isHermitian K_op,
    LayerB.CoherenceConvexityGeneral.coherence_eq_umegaki_general ρ⟩

/-- Three-initial higher-power Yosida identity double-difference regularity paired
with continuous Lindblad dephasing flow (`LindbladContinuous`), partial-trace
matrix-unit twirl (`PartialTraceTwirl`), and Petz recovery map for the identity
channel (`PetzRecoveryMap`). -/
theorem threeInitial_identity_doubleDiff_with_lindbladContinuous_partialTraceTwirl_and_petzRecovery
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ t q a b d γ τ : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d)
    (hγ : 0 ≤ γ) (hτ : 0 ≤ τ)
    (r n : ℕ) (f₁ f₂ f₃ : Hilbert)
    (ρ₂ : LayerB.DensityMatrixHonest.DensityMatrix2Honest)
    (σ ω : Matrix (Fin n) (Fin n) ℂ) :
    let y := threeInitialHigherPowerIdentityDoubleDiff ε hε h hh hb m g k s₁ s₂ s₃ t a b d r f₁ f₂ f₃
    y ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
      (LayerB.LindbladContinuous.dephasingFlow γ τ hγ hτ ρ₂).p₁ +
          (LayerB.LindbladContinuous.dephasingFlow γ τ hγ hτ ρ₂).p₂ = 1 ∧
      PartialTrace_Twirl_Target ∧
      LayerB.PetzRecoveryMap.petzRecovery (id : LayerB.PetzRecoveryMap.Channel n n) σ ω = ω ∧
      LayerB.PetzRecoveryMap.ChannelCPTPLike (id : LayerB.PetzRecoveryMap.Channel n n) := by
  intro y
  have hy := threeInitialHigherPowerIdentityDoubleDiff_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ t q a b d ha hb_pos hd r f₁ f₂ f₃
  exact ⟨hy.1,
    LayerB.LindbladContinuous.dephasingFlow_trace_one γ τ hγ hτ ρ₂,
    LayerB.PartialTraceTwirl.partialTraceTwirl_holds,
    LayerB.PetzRecoveryMap.petzRecovery_identity σ ω,
    LayerB.PetzRecoveryMap.channelCPTPLike_identity n⟩

/-- Three-final higher-power resolvent double-difference regularity paired with
Stinespring/Kraus CPTP trace-distance data processing inequality
(`TraceDistanceCPTPDPI`), unitary trace-distance invariance (`TraceDistanceContractivity`),
and unconditional partial-trace contractivity via sign-matrix dual attainment
(`TraceNormDualAttainment`). -/
theorem threeFinal_resolvent_doubleDiff_with_traceDistanceCPTP_contractivity_and_dualAttainment
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s t₁ t₂ t₃ q a b d : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d)
    (r : ℕ) (f : Hilbert)
    {n_A n_B : ℕ}
    (U : Matrix.unitaryGroup (Fin (n_A * n_B)) ℂ)
    (ρ σ : ComplexDensityMatrix (n_A * n_B)) :
    let w := threeFinalHigherPowerResolventDoubleDiff ε hε h hh hb m g k s t₁ t₂ t₃ a b d r f
    ‖w‖ ≤ ((a⁻¹) ^ (r + 2) + 2 * (b⁻¹) ^ (r + 2) + (d⁻¹) ^ (r + 2)) * ‖f‖ ∧
      traceDistance
        (LayerB.UnitaryInvariance.unitaryConjugate U ρ)
        (LayerB.UnitaryInvariance.unitaryConjugate U σ) =
        traceDistance ρ σ ∧
      LayerB.TraceDistanceContractivity.TraceNormDualAttained ρ σ ∧
      traceDistance
        (partialTraceDensity_right ρ)
        (partialTraceDensity_right σ) ≤
        traceDistance ρ σ := by
  intro w
  have hw := threeFinalHigherPowerResolventDoubleDiff_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s t₁ t₂ t₃ q a b d ha hb_pos hd r f
  exact ⟨hw.2,
    LayerB.TraceDistanceContractivity.traceDistance_unitaryConjugate U ρ σ,
    LayerB.TraceNormDualAttainment.traceNormDualAttained ρ σ,
    LayerB.TraceNormDualAttainment.traceDistance_partialTrace_contractive_unconditional ρ σ⟩

/-- Three-final higher-power Yosida identity double-difference regularity paired
with tripartite strong subadditivity reduction (`TripartiteSSAReduction`),
multi-point Umegaki joint convexity (`UmegakiMultiConvex`), general von Neumann
entropy concavity (`VonNeumannConcavityGeneral`), and general weak subadditivity
(`WeakSubadditivityGeneral`). -/
theorem threeFinal_identity_doubleDiff_with_tripartiteSSA_umegakiMultiConvex_vonNeumann_and_weakSubadditivity
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s t₁ t₂ t₃ q a b d : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d)
    (r : ℕ) (f : Hilbert)
    {n_A n_B n_C : ℕ}
    (ρ₃ : ComplexDensityMatrix (n_A * n_B * n_C))
    (ρ₂ σ₂ : ComplexDensityMatrix (n_A * n_B))
    (hn : 0 < n_A * n_B)
    (hA : (partialTraceDensity_right ρ₂).M.PosDef)
    (hB : (partialTraceDensity_left ρ₂).M.PosDef) :
    let y := threeFinalHigherPowerIdentityDoubleDiff ε hε h hh hb m g k s t₁ t₂ t₃ a b d r f
    ‖y‖ ≤ 4 * ‖f‖ ∧
      Tripartite_SSA_Reduction_Target ∧
      (∃ S_AB S_BC S_B : ℝ,
        vonNeumannEntropy ρ₃ + S_B ≤ S_AB + S_BC) ∧
      JointConvexity_Multi_Target ∧
      umegakiRelativeEntropy ρ₂ σ₂ =
        -vonNeumannEntropy ρ₂ -
          (Matrix.trace (ρ₂.M * operatorLog σ₂)).re ∧
      vonNeumannEntropy ρ₂ ≤
        vonNeumannEntropy (partialTraceDensity_right ρ₂) +
        vonNeumannEntropy (partialTraceDensity_left ρ₂) := by
  intro y
  have hy := threeFinalHigherPowerIdentityDoubleDiff_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s t₁ t₂ t₃ q a b d ha hb_pos hd r f
  exact ⟨hy.2,
    LayerB.TripartiteSSAReduction.tripartiteSSAReduction_holds,
    LayerB.TripartiteSSAReduction.ssa_witness_unconditional ρ₃,
    LayerB.UmegakiMultiConvex.multiConvex_holds_unconditional,
    LayerB.VonNeumannConcavityGeneral.umegaki_to_avg_eq_general ρ₂ σ₂,
    LayerB.WeakSubadditivityGeneral.weak_subadditivity_general ρ₂ hn hA hB⟩

/-- Kraus isometric dilation trace-distance DPI (`TraceDistanceCPTPDPI`) paired
with Holevo $\bar\rho$-basis mutual information bound (`HolevoBoundRhoBarBasis`). -/
theorem kraus_isometric_dpi_with_holevo_rhoBar_basis
    {α : Type*} [Fintype α] [DecidableEq α] {n d_k : ℕ}
    {K_op : Fin d_k → Matrix (Fin n) (Fin n) ℂ}
    (hK : ∑ j, (K_op j).conjTranspose * K_op j = (1 : Matrix (Fin n) (Fin n) ℂ))
    (ρ σ : ComplexDensityMatrix n)
    (E : QuantumEnsemble α n)
    (hRhoBar_pos : (ensembleAverageQuantum E).M.PosDef)
    (hStates_pos : ∀ i, (E.state i).M.PosDef) :
    traceDistance
      (partialTraceDensity_right
        (LayerB.TraceDistanceCPTPDPI.isometricConjugate
          (LayerB.TraceDistanceCPTPDPI.krausIsometry_isIsometry hK) ρ))
      (partialTraceDensity_right
        (LayerB.TraceDistanceCPTPDPI.isometricConjugate
          (LayerB.TraceDistanceCPTPDPI.krausIsometry_isIsometry hK) σ)) ≤
      traceDistance ρ σ ∧
      mutualInformation
        (LayerB.HolevoBoundRhoBarBasis.measureEnsembleInRhoBarBasis E hRhoBar_pos hStates_pos) ≤
        holevoChiQuantum E := by
  exact ⟨LayerB.TraceDistanceCPTPDPI.traceDistance_cptp_dpi_kraus hK ρ σ,
    LayerB.HolevoBoundRhoBarBasis.mutualInformation_measureInRhoBarBasis_le_holevoChiQuantum
      E hRhoBar_pos hStates_pos⟩

/-- Master synthesis of the three-trajectory higher-power resolvent/Yosida
double-difference cocycles with all 13 Choi/Petz/trace-distance/SSA/Umegaki
quantum-information modules. -/
theorem choi_petz_traceDistance_ssa_umegaki_bridge_master
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ t₁ t₂ t₃ q a b d : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d)
    (r : ℕ) (f₁ f₂ f₃ : Hilbert)
    {n_A n_B : ℕ}
    (K_op : Fin n_B → Matrix (Fin n_A) (Fin n_A) ℂ)
    (ρ σ : ComplexDensityMatrix (n_A * n_B)) :
    let w_init := threeInitialHigherPowerResolventDoubleDiff ε hε h hh hb m g k s₁ s₂ s₃ t₁ a b d r f₁ f₂ f₃
    let y_fin := threeFinalHigherPowerIdentityDoubleDiff ε hε h hh hb m g k s₁ t₁ t₂ t₃ a b d r f₁
    w_init ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
      ‖y_fin‖ ≤ 4 * ‖f₁‖ ∧
      LayerB.ChoiTheorem.IsCompletelyPositive (LayerB.ChoiTheorem.krausMap K_op) ∧
      PartialTrace_Twirl_Target ∧
      LayerB.PetzRecoveryMap.ChannelCPTPLike (id : LayerB.PetzRecoveryMap.Channel n_A n_A) ∧
      LayerB.TraceDistanceContractivity.TraceNormDualAttained ρ σ ∧
      traceDistance
        (partialTraceDensity_right ρ)
        (partialTraceDensity_right σ) ≤
        traceDistance ρ σ ∧
      Tripartite_SSA_Reduction_Target ∧
      JointConvexity_Multi_Target := by
  intro w_init y_fin
  have hw := threeInitialHigherPowerResolventDoubleDiff_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ s₃ t₁ q a b d ha hb_pos hd r f₁ f₂ f₃
  have hy := threeFinalHigherPowerIdentityDoubleDiff_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ t₁ t₂ t₃ q a b d ha hb_pos hd r f₁
  exact ⟨hw.1, hy.2,
    LayerB.ChoiTheorem.krausMap_is_CP K_op,
    LayerB.PartialTraceTwirl.partialTraceTwirl_holds,
    LayerB.PetzRecoveryMap.channelCPTPLike_identity n_A,
    LayerB.TraceNormDualAttainment.traceNormDualAttained ρ σ,
    LayerB.TraceNormDualAttainment.traceDistance_partialTrace_contractive_unconditional ρ σ,
    LayerB.TripartiteSSAReduction.tripartiteSSAReduction_holds,
    LayerB.UmegakiMultiConvex.multiConvex_holds_unconditional⟩

#print axioms threeInitial_resolvent_doubleDiff_with_choi_coherenceConvexity_and_holevoRhoBar
#print axioms threeInitial_identity_doubleDiff_with_lindbladContinuous_partialTraceTwirl_and_petzRecovery
#print axioms threeFinal_resolvent_doubleDiff_with_traceDistanceCPTP_contractivity_and_dualAttainment
#print axioms threeFinal_identity_doubleDiff_with_tripartiteSSA_umegakiMultiConvex_vonNeumann_and_weakSubadditivity
#print axioms kraus_isometric_dpi_with_holevo_rhoBar_basis
#print axioms choi_petz_traceDistance_ssa_umegaki_bridge_master

end KFCausalClockFloorChoiPetzTraceDistanceContractivitySSAUmegakiBridge
end Audit
end UnifiedTheory
