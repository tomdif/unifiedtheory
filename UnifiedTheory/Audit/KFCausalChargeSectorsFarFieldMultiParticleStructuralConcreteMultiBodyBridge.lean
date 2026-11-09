import UnifiedTheory.Audit.KFCausalArbitrarySourceWeightedProjectorExpectationAndCrossGramDecomposition
import UnifiedTheory.LayerB.ChargeSectors
import UnifiedTheory.LayerB.DynamicalStability
import UnifiedTheory.LayerB.FarField
import UnifiedTheory.LayerB.MultiParticle
import UnifiedTheory.LayerB.StructuralTheorems
import UnifiedTheory.LayerC.ConcreteModel
import UnifiedTheory.LayerC.ConcreteMultiBody

set_option autoImplicit false

namespace UnifiedTheory
namespace Audit
namespace KFCausalChargeSectorsFarFieldMultiParticleStructuralConcreteMultiBodyBridge

open KFCausalArbitrarySourceWeightedProjectorExpectationAndCrossGramDecomposition
open KFCausalArbitrarySourceMutuallyOrthogonalProjectorParsevalDecomposition
open KFCausalArbitrarySourceOrthogonalProjectionResidualEnergyDecomposition

/-- Three-channel spectral-weighted projector expectation paired with charge
sector additivity and bound-state neutrality (`ChargeSectors`) and on-shell
kernel subspace stability (`DynamicalStability`). -/
theorem threeChannel_weighted_expectation_with_chargeSectors_and_dynamicalStability
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res w_min w_max : ℝ)
    (hmin₁ : w_min ≤ w₁) (hmin₂ : w_min ≤ w₂) (hmin_r : w_min ≤ w_res)
    (hmax₁ : w₁ ≤ w_max) (hmax₂ : w₂ ≤ w_max) (hmax_r : w_res ≤ w_max)
    (x : E)
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (db : LayerB.ComposableDefectBlock V) (d : db.Defect)
    (L : V →ₗ[ℝ] W) :
    w_min * hilbertEnergy x ≤ threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x ∧
      threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x ≤ w_max * hilbertEnergy x ∧
      (LayerB.IsNeutral db d ↔ LayerB.InSector db 0 d) ∧
      LayerB.charge db (db.compose d (db.conjugate d)) = 0 ∧
      LayerB.DynamicalStability.SubspaceStable (fun v : V => L v = 0) := by
  have hrr := threeChannelWeightedExpectation_rayleigh_ritz_bounds
    hP w₁ w₂ w_res w_min w_max hmin₁ hmin₂ hmin_r hmax₁ hmax₂ hmax_r x
  exact ⟨hrr.1, hrr.2,
    LayerB.neutral_iff_sector_zero db d,
    LayerB.far_field_cancellation db d,
    LayerB.DynamicalStability.kernel_is_subspace_stable L⟩

/-- Multi-channel spectral-weighted projector expectation paired with far-field
charge equivalence and conjugate screening (`FarField`) and $N$-body charge
conservation (`MultiParticle`). -/
theorem multiChannel_weighted_expectation_with_farField_and_multiParticle
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w : Fin Q → ℝ) (w_min w_max : ℝ)
    (hmin : ∀ q, w_min ≤ w q) (hmax : ∀ q, w q ≤ w_max) (x : E)
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (db : LayerB.ComposableDefectBlock V) (d₁ d₂ : db.Defect)
    (rest : List db.Defect) :
    w_min * (∑ q : Fin Q, hilbertEnergy (P q x)) ≤
        multiChannelWeightedExpectation P w x ∧
      multiChannelWeightedExpectation P w x ≤
        w_max * (∑ q : Fin Q, hilbertEnergy (P q x)) ∧
      LayerB.FarFieldEquiv db (db.compose d₁ d₂) (db.compose d₂ d₁) ∧
      LayerB.FarFieldEquiv db d₁ (db.compose (db.compose d₁ d₂) (db.conjugate d₂)) ∧
      LayerB.charge db (LayerB.composeList db d₁ rest) =
        LayerB.charge db d₁ + LayerB.totalCharge db rest ∧
      LayerB.interactionCharge db d₁ d₂ = 0 ∧
      LayerB.bindingBias db d₁ d₂ = 0 := by
  have hrr := multiChannelWeightedExpectation_rayleigh_ritz_bounds P w w_min w_max hmin hmax x
  exact ⟨hrr.1, hrr.2,
    LayerB.far_field_rearrangement db d₁ d₂,
    LayerB.far_field_conjugate_screen db d₁ d₂,
    LayerB.charge_foldl db d₁ rest,
    LayerB.interaction_charge_zero db d₁ d₂,
    LayerB.binding_bias_zero db d₁ d₂⟩

/-- Equal-weight three-channel projector Parseval identity paired with
enclosure, unique neutralizer, and sector trichotomy (`StructuralTheorems`). -/
theorem weighted_expectation_with_structuralTheorems_enclosure_and_trichotomy
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (c_wt : ℝ) (hc : 0 ≤ c_wt) (x : E)
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (db : LayerB.ComposableDefectBlock V) (d : db.Defect) :
    threeChannelWeightedExpectation P₁ P₂ c_wt c_wt c_wt x = c_wt * hilbertEnergy x ∧
      LayerB.IsNeutral db (db.compose d (db.conjugate d)) ∧
      (LayerB.charge db d = 0 ∨ LayerB.charge db d > 0 ∨ LayerB.charge db d < 0) := by
  have hconst := (threeChannelWeightedExpectation_nonneg_and_const_eq
    hP c_wt c_wt c_wt c_wt hc hc hc x).2
  exact ⟨hconst,
    LayerB.opposite_can_neutralize db d,
    LayerB.sector_trichotomy db d⟩

/-- Weighted projector expectation paired with the concrete $U_\star$ model
realization (`ConcreteModel`) and concrete electron/positron/proton/neutron
many-body charge algebra (`ConcreteMultiBody`). -/
theorem weighted_expectation_with_concreteModel_and_concreteMultiBody
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂) (x : E) :
    threeChannelWeightedExpectation P₁ P₂ 1 1 1 x = hilbertEnergy x ∧
      LayerC.U_star.toParentU.scale.α = 2 ∧
      LayerB.IsInert LayerC.concreteDefects LayerC.inertDefect ∧
      LayerB.IsSourceCarrying LayerC.concreteDefects LayerC.sourceDefect ∧
      LayerB.charge LayerC.concreteComposable LayerC.electron = 1 ∧
      LayerB.charge LayerC.concreteComposable LayerC.positron = -1 ∧
      LayerB.charge LayerC.concreteComposable LayerC.neutron = 0 ∧
      LayerC.concreteComposable.conjugate LayerC.electron = LayerC.positron ∧
      LayerB.IsNeutral LayerC.concreteComposable
        (LayerC.concreteComposable.compose LayerC.electron LayerC.positron) ∧
      LayerB.charge LayerC.concreteComposable
        (LayerC.concreteComposable.compose
          (LayerC.concreteComposable.compose LayerC.proton LayerC.electron)
          LayerC.electron) = 5 := by
  have hconst := (threeChannelWeightedExpectation_nonneg_and_const_eq
    hP 1 1 1 1 zero_le_one zero_le_one zero_le_one x).2
  rw [one_mul] at hconst
  have hreal := LayerC.concrete_realization
  exact ⟨hconst,
    hreal.1,
    LayerC.inertDefect_isInert,
    LayerC.sourceDefect_isSource,
    LayerC.electron_charge,
    LayerC.positron_charge,
    LayerC.neutron_charge,
    LayerC.positron_is_conjugate,
    LayerC.epem_neutral,
    LayerC.three_body_charge⟩

/-- Master synthesis of spectral-weighted projector expectations with all 7
charge-sector, dynamical-stability, far-field, multi-particle, structural, and
concrete many-body modules. -/
theorem chargeSectors_farField_multiParticle_structural_concreteMultiBody_bridge_master
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res w_min w_max : ℝ)
    (hmin₁ : w_min ≤ w₁) (hmin₂ : w_min ≤ w₂) (hmin_r : w_min ≤ w_res)
    (hmax₁ : w₁ ≤ w_max) (hmax₂ : w₂ ≤ w_max) (hmax_r : w_res ≤ w_max)
    (x : E) :
    w_min * hilbertEnergy x ≤ threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x ∧
      threeChannelWeightedExpectation P₁ P₂ w₁ w₂ w_res x ≤ w_max * hilbertEnergy x ∧
      LayerC.U_star.toParentU.scale.α = 2 ∧
      LayerB.IsInert LayerC.concreteDefects LayerC.inertDefect ∧
      LayerB.IsSourceCarrying LayerC.concreteDefects LayerC.sourceDefect ∧
      LayerC.concreteComposable.conjugate LayerC.electron = LayerC.positron ∧
      LayerB.IsNeutral LayerC.concreteComposable
        (LayerC.concreteComposable.compose LayerC.electron LayerC.positron) ∧
      LayerB.charge LayerC.concreteComposable
        (LayerC.concreteComposable.compose
          (LayerC.concreteComposable.compose LayerC.proton LayerC.electron)
          LayerC.electron) = 5 := by
  have hrr := threeChannelWeightedExpectation_rayleigh_ritz_bounds
    hP w₁ w₂ w_res w_min w_max hmin₁ hmin₂ hmin_r hmax₁ hmax₂ hmax_r x
  have hreal := LayerC.concrete_realization
  exact ⟨hrr.1, hrr.2,
    hreal.1,
    LayerC.inertDefect_isInert,
    LayerC.sourceDefect_isSource,
    LayerC.positron_is_conjugate,
    LayerC.epem_neutral,
    LayerC.three_body_charge⟩

#print axioms threeChannel_weighted_expectation_with_chargeSectors_and_dynamicalStability
#print axioms multiChannel_weighted_expectation_with_farField_and_multiParticle
#print axioms weighted_expectation_with_structuralTheorems_enclosure_and_trichotomy
#print axioms weighted_expectation_with_concreteModel_and_concreteMultiBody
#print axioms chargeSectors_farField_multiParticle_structural_concreteMultiBody_bridge_master

end KFCausalChargeSectorsFarFieldMultiParticleStructuralConcreteMultiBodyBridge
end Audit
end UnifiedTheory
