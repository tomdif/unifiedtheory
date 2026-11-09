import UnifiedTheory.Audit.KFCausalClockFloorTwoTimeMixedInitialFinalHigherPowerResolventPlaquette
import UnifiedTheory.Audit.KFCausalClockFloorChoiPetzTraceDistanceContractivitySSAUmegakiBridge

set_option autoImplicit false

namespace UnifiedTheory
namespace Audit
namespace KFCausalClockFloorTwoTimeMixedPlaquetteChoiPetzTraceDistanceSSAUmegakiBridge

open KFCausalClockFloorTwoTimeMixedInitialFinalHigherPowerResolventPlaquette
open KFCausalClockFloorChoiPetzTraceDistanceContractivitySSAUmegakiBridge
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

/-- Equal-final-time `t₁ = t₂ = t` mixed resolvent plaquette `hamiltonianPowerDomain t (r + 2)`
regularity paired with Choi's complete positivity theorem (`ChoiTheorem`) and
general coherence relative-entropy identity (`CoherenceConvexityGeneral`). -/
theorem equalFinalTime_resolventPlaquette_with_choi_and_coherenceConvexity
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ t q a b c d : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (r : ℕ) (f₁ f₂ : Hilbert)
    {n d_k : ℕ} (K_op : Fin d_k → Matrix (Fin n) (Fin n) ℂ)
    (ρ : ComplexDensityMatrix n) :
    let w := mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t t a b c d r f₁ f₂
    w ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
      LayerB.ChoiTheorem.IsCompletelyPositive (LayerB.ChoiTheorem.krausMap K_op) ∧
      (LayerB.ChoiTheorem.choiMatrix (LayerB.ChoiTheorem.krausMap K_op)).IsHermitian ∧
      coherence ρ = umegakiRelativeEntropy ρ (dephasedDM ρ) := by
  intro w
  have hw := mixedInitialFinalHigherPowerResolventPlaquette_equal_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ t q a b c d ha hb_pos hc hd r f₁ f₂
  exact ⟨hw.1,
    LayerB.ChoiTheorem.krausMap_is_CP K_op,
    LayerB.ChoiTheorem.choiMatrix_krausMap_isHermitian K_op,
    LayerB.CoherenceConvexityGeneral.coherence_eq_umegaki_general ρ⟩

/-- Equal-final-time `t₁ = t₂ = t` mixed Yosida identity plaquette `hamiltonianPowerDomain t (r + 2)`
regularity paired with continuous Lindblad dephasing flow (`LindbladContinuous`),
partial-trace matrix-unit twirl (`PartialTraceTwirl`), and Petz recovery map
(`PetzRecoveryMap`). -/
theorem equalFinalTime_identityPlaquette_with_lindblad_partialTraceTwirl_and_petzRecovery
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ t q a b c d γ τ : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hγ : 0 ≤ γ) (hτ : 0 ≤ τ)
    (r n : ℕ) (f₁ f₂ : Hilbert)
    (ρ₂ : LayerB.DensityMatrixHonest.DensityMatrix2Honest)
    (σ ω : Matrix (Fin n) (Fin n) ℂ) :
    let y := mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t t a b c d r f₁ f₂
    y ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (r + 2) ∧
      (LayerB.LindbladContinuous.dephasingFlow γ τ hγ hτ ρ₂).p₁ +
          (LayerB.LindbladContinuous.dephasingFlow γ τ hγ hτ ρ₂).p₂ = 1 ∧
      PartialTrace_Twirl_Target ∧
      LayerB.PetzRecoveryMap.petzRecovery (id : LayerB.PetzRecoveryMap.Channel n n) σ ω = ω ∧
      LayerB.PetzRecoveryMap.ChannelCPTPLike (id : LayerB.PetzRecoveryMap.Channel n n) := by
  intro y
  have hy := mixedInitialFinalHigherPowerIdentityPlaquette_equal_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ t q a b c d ha hb_pos hc hd r f₁ f₂
  exact ⟨hy.1,
    LayerB.LindbladContinuous.dephasingFlow_trace_one γ τ hγ hτ ρ₂,
    LayerB.PartialTraceTwirl.partialTraceTwirl_holds,
    LayerB.PetzRecoveryMap.petzRecovery_identity σ ω,
    LayerB.PetzRecoveryMap.channelCPTPLike_identity n⟩

/-- Mixed initial-and-final higher-power resolvent plaquette 8-domain regularity and
4-corner geometric norm bound paired with unitary trace-distance invariance
(`TraceDistanceContractivity`) and unconditional partial-trace contractivity via
sign-matrix dual attainment (`TraceNormDualAttainment`). -/
theorem mixedInitialFinal_resolventPlaquette_with_traceDistanceContractivity_and_dualAttainment
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ t₁ t₂ q a b c d : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (r : ℕ) (f₁ f₂ : Hilbert)
    {n_A n_B : ℕ}
    (U : Matrix.unitaryGroup (Fin (n_A * n_B)) ℂ)
    (ρ σ : ComplexDensityMatrix (n_A * n_B)) :
    let w := mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a b c d r f₁ f₂
    ‖w‖ ≤ ((a⁻¹) ^ (r + 2) + (c⁻¹) ^ (r + 2)) * ‖f₁‖ +
        ((b⁻¹) ^ (r + 2) + (d⁻¹) ^ (r + 2)) * ‖f₂‖ ∧
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
  have hw := mixedInitialFinalHigherPowerResolventPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ t₁ t₂ q a b c d ha hb_pos hc hd r f₁ f₂
  exact ⟨hw.2,
    LayerB.TraceDistanceContractivity.traceDistance_unitaryConjugate U ρ σ,
    LayerB.TraceNormDualAttainment.traceNormDualAttained ρ σ,
    LayerB.TraceNormDualAttainment.traceDistance_partialTrace_contractive_unconditional ρ σ⟩

/-- Mixed initial-and-final higher-power Yosida identity plaquette 8-domain regularity
paired with tripartite strong subadditivity reduction (`TripartiteSSAReduction`),
multi-point Umegaki joint convexity (`UmegakiMultiConvex`), general von Neumann
entropy concavity (`VonNeumannConcavityGeneral`), and general weak subadditivity
(`WeakSubadditivityGeneral`). -/
theorem mixedInitialFinal_identityPlaquette_with_tripartiteSSA_umegaki_vonNeumann_and_weakSubadditivity
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ t₁ t₂ q a b c d : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (r : ℕ) (f₁ f₂ : Hilbert)
    {n_A n_B n_C : ℕ}
    (ρ₃ : ComplexDensityMatrix (n_A * n_B * n_C))
    (ρ₂ σ₂ : ComplexDensityMatrix (n_A * n_B))
    (hn : 0 < n_A * n_B)
    (hA : (partialTraceDensity_right ρ₂).M.PosDef)
    (hB : (partialTraceDensity_left ρ₂).M.PosDef) :
    let y := mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a b c d r f₁ f₂
    ‖y‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₂‖ ∧
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
  have hy := mixedInitialFinalHigherPowerIdentityPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ t₁ t₂ q a b c d ha hb_pos hc hd r f₁ f₂
  exact ⟨hy.2,
    LayerB.TripartiteSSAReduction.tripartiteSSAReduction_holds,
    LayerB.TripartiteSSAReduction.ssa_witness_unconditional ρ₃,
    LayerB.UmegakiMultiConvex.multiConvex_holds_unconditional,
    LayerB.VonNeumannConcavityGeneral.umegaki_to_avg_eq_general ρ₂ σ₂,
    LayerB.WeakSubadditivityGeneral.weak_subadditivity_general ρ₂ hn hA hB⟩

/-- Horizontal 3-initial `(s₁, s₂, s₃)` plaquette stacking cocycle paired with Kraus
isometric dilation trace-distance DPI (`TraceDistanceCPTPDPI`) and Holevo
$\bar\rho$-basis mutual information bound (`HolevoBoundRhoBarBasis`). -/
theorem horizontalPlaquette_stacking_with_krausIsometricDPI_and_holevoRhoBar
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ s₃ t₁ t₂ a₁ a₂ a₃ c₁ c₂ c₃ : ℝ) (r : ℕ) (f₁ f₂ f₃ : Hilbert)
    {α : Type*} [Fintype α] [DecidableEq α] {n d_k : ℕ}
    {K_op : Fin d_k → Matrix (Fin n) (Fin n) ℂ}
    (hK : ∑ j, (K_op j).conjTranspose * K_op j = (1 : Matrix (Fin n) (Fin n) ℂ))
    (ρ σ : ComplexDensityMatrix n)
    (E : QuantumEnsemble α n)
    (hRhoBar_pos : (ensembleAverageQuantum E).M.PosDef)
    (hStates_pos : ∀ i, (E.state i).M.PosDef) :
    mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a₁ a₂ c₁ c₂ r f₁ f₂ +
        mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₂ s₃ t₁ t₂ a₂ a₃ c₂ c₃ r f₂ f₃ =
      mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₃ t₁ t₂ a₁ a₃ c₁ c₃ r f₁ f₃ ∧
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
  have hhor := mixedInitialFinalHigherPowerPlaquette_horizontal_stacking
    ε hε h hh hb m g k s₁ s₂ s₃ t₁ t₂ a₁ a₂ a₃ c₁ c₂ c₃ r f₁ f₂ f₃
  have hdpi := kraus_isometric_dpi_with_holevo_rhoBar_basis hK ρ σ E hRhoBar_pos hStates_pos
  exact ⟨hhor.1, hdpi.1, hdpi.2⟩

/-- Master synthesis of the two-time mixed initial-and-final higher-power resolvent
plaquette calculus with all 13 Choi/Petz/trace-distance/DPI/SSA/Umegaki/Holevo
quantum-information modules. -/
theorem twoTime_mixedPlaquette_choi_petz_traceDistance_ssa_umegaki_bridge_master
    (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)
    (s₁ s₂ t₁ t₂ q a b c d : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (r : ℕ) (f₁ f₂ : Hilbert)
    {n_A n_B : ℕ}
    (K_op : Fin n_B → Matrix (Fin n_A) (Fin n_A) ℂ)
    (ρ σ : ComplexDensityMatrix (n_A * n_B)) :
    let w := mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a b c d r f₁ f₂
    let y := mixedInitialFinalHigherPowerIdentityPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₂ a b c d r f₁ f₂
    let w_eq := mixedInitialFinalHigherPowerResolventPlaquette ε hε h hh hb m g k s₁ s₂ t₁ t₁ a b c d r f₁ f₂
    w_eq ∈ hamiltonianPowerDomain ε hε h hh hb m g k t₁ (r + 2) ∧
      ‖w‖ ≤ ((a⁻¹) ^ (r + 2) + (c⁻¹) ^ (r + 2)) * ‖f₁‖ +
        ((b⁻¹) ^ (r + 2) + (d⁻¹) ^ (r + 2)) * ‖f₂‖ ∧
      ‖y‖ ≤ 2 * ‖f₁‖ + 2 * ‖f₂‖ ∧
      LayerB.ChoiTheorem.IsCompletelyPositive (LayerB.ChoiTheorem.krausMap K_op) ∧
      traceDistance
        (partialTraceDensity_right ρ)
        (partialTraceDensity_right σ) ≤
        traceDistance ρ σ ∧
      Tripartite_SSA_Reduction_Target ∧
      JointConvexity_Multi_Target := by
  intro w y w_eq
  have hweq := mixedInitialFinalHigherPowerResolventPlaquette_equal_final_time_mem_power_and_ten_domains
    ε hε h hh hb m g k s₁ s₂ t₁ q a b c d ha hb_pos hc hd r f₁ f₂
  have hw := mixedInitialFinalHigherPowerResolventPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ t₁ t₂ q a b c d ha hb_pos hc hd r f₁ f₂
  have hy := mixedInitialFinalHigherPowerIdentityPlaquette_mem_eight_domains_and_norm_le
    ε hε h hh hb m g k s₁ s₂ t₁ t₂ q a b c d ha hb_pos hc hd r f₁ f₂
  exact ⟨hweq.1, hw.2, hy.2,
    LayerB.ChoiTheorem.krausMap_is_CP K_op,
    LayerB.TraceNormDualAttainment.traceDistance_partialTrace_contractive_unconditional ρ σ,
    LayerB.TripartiteSSAReduction.tripartiteSSAReduction_holds,
    LayerB.UmegakiMultiConvex.multiConvex_holds_unconditional⟩

#print axioms equalFinalTime_resolventPlaquette_with_choi_and_coherenceConvexity
#print axioms equalFinalTime_identityPlaquette_with_lindblad_partialTraceTwirl_and_petzRecovery
#print axioms mixedInitialFinal_resolventPlaquette_with_traceDistanceContractivity_and_dualAttainment
#print axioms mixedInitialFinal_identityPlaquette_with_tripartiteSSA_umegaki_vonNeumann_and_weakSubadditivity
#print axioms horizontalPlaquette_stacking_with_krausIsometricDPI_and_holevoRhoBar
#print axioms twoTime_mixedPlaquette_choi_petz_traceDistance_ssa_umegaki_bridge_master

end KFCausalClockFloorTwoTimeMixedPlaquetteChoiPetzTraceDistanceSSAUmegakiBridge
end Audit
end UnifiedTheory
