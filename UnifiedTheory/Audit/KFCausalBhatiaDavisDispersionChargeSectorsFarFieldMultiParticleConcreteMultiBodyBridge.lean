import UnifiedTheory.Audit.KFCausalArbitrarySourceWeightedProjectorVarianceAndBhatiaDavisInequality
import UnifiedTheory.Audit.KFCausalChargeSectorsFarFieldMultiParticleStructuralConcreteMultiBodyBridge

set_option autoImplicit false

namespace UnifiedTheory
namespace Audit
namespace KFCausalBhatiaDavisDispersionChargeSectorsFarFieldMultiParticleConcreteMultiBodyBridge

open KFCausalArbitrarySourceWeightedProjectorVarianceAndBhatiaDavisInequality
open KFCausalChargeSectorsFarFieldMultiParticleStructuralConcreteMultiBodyBridge
open KFCausalArbitrarySourceMutuallyOrthogonalProjectorParsevalDecomposition
open KFCausalArbitrarySourceOrthogonalProjectionResidualEnergyDecomposition
open scoped BigOperators

/-- Three-channel Bhatia-Davis / Popoviciu spectral dispersion inequality paired
with charge sector additivity and bound-state neutrality (`ChargeSectors`) and
on-shell kernel subspace stability (`DynamicalStability`). -/
theorem threeChannel_bhatiaDavis_with_chargeSectors_and_dynamicalStability
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res w_min w_max : ℝ)
    (hmin₁ : w_min ≤ w₁) (hmin₂ : w_min ≤ w₂) (hmin_r : w_min ≤ w_res)
    (hmax₁ : w₁ ≤ w_max) (hmax₂ : w₂ ≤ w_max) (hmax_r : w_res ≤ w_max)
    (x : E)
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (db : LayerB.ComposableDefectBlock V) (d : db.Defect)
    (L : V →ₗ[ℝ] W) :
    0 ≤ threeChannelBhatiaDavisFunctional P₁ P₂ w₁ w₂ w_res w_min w_max x ∧
      threeChannelBhatiaDavisFunctional P₁ P₂ w₁ w₂ w_res w_min w_max x ≤
        ((w_max - w_min) / 2) ^ 2 * hilbertEnergy x ∧
      (LayerB.IsNeutral db d ↔ LayerB.InSector db 0 d) ∧
      LayerB.charge db (db.compose d (db.conjugate d)) = 0 ∧
      LayerB.DynamicalStability.SubspaceStable (fun v : V => L v = 0) := by
  have hbd := threeChannelBhatiaDavisFunctional_nonneg_and_popoviciu_bound
    hP w₁ w₂ w_res w_min w_max hmin₁ hmin₂ hmin_r hmax₁ hmax₂ hmax_r x
  exact ⟨hbd.1, hbd.2,
    LayerB.neutral_iff_sector_zero db d,
    LayerB.far_field_cancellation db d,
    LayerB.DynamicalStability.kernel_is_subspace_stable L⟩

/-- Multi-channel Bhatia-Davis / Popoviciu spectral dispersion inequality paired
with far-field charge equivalence and conjugate screening (`FarField`) and
$N$-body charge conservation (`MultiParticle`). -/
theorem multiChannel_bhatiaDavis_with_farField_and_multiParticle
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Q : ℕ} (P : Fin Q → (E →L[ℂ] E)) (w : Fin Q → ℝ) (w_min w_max : ℝ)
    (hmin : ∀ q, w_min ≤ w q) (hmax : ∀ q, w q ≤ w_max) (x : E)
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (db : LayerB.ComposableDefectBlock V) (d₁ d₂ : db.Defect)
    (rest : List db.Defect) :
    0 ≤ multiChannelBhatiaDavisFunctional P w w_min w_max x ∧
      multiChannelBhatiaDavisFunctional P w w_min w_max x ≤
        ((w_max - w_min) / 2) ^ 2 * (∑ q : Fin Q, hilbertEnergy (P q x)) ∧
      LayerB.FarFieldEquiv db (db.compose d₁ d₂) (db.compose d₂ d₁) ∧
      LayerB.FarFieldEquiv db d₁ (db.compose (db.compose d₁ d₂) (db.conjugate d₂)) ∧
      LayerB.charge db (LayerB.composeList db d₁ rest) =
        LayerB.charge db d₁ + LayerB.totalCharge db rest ∧
      LayerB.interactionCharge db d₁ d₂ = 0 ∧
      LayerB.bindingBias db d₁ d₂ = 0 := by
  have hbd := multiChannelBhatiaDavisFunctional_nonneg_and_popoviciu_bound
    P w w_min w_max hmin hmax x
  exact ⟨hbd.1, hbd.2,
    LayerB.far_field_rearrangement db d₁ d₂,
    LayerB.far_field_conjugate_screen db d₁ d₂,
    LayerB.charge_foldl db d₁ rest,
    LayerB.interaction_charge_zero db d₁ d₂,
    LayerB.binding_bias_zero db d₁ d₂⟩

/-- Three-channel spectral second-moment nonnegativity paired with enclosure,
unique neutralizer, and sector trichotomy (`StructuralTheorems`). -/
theorem threeChannel_secondMoment_with_structuralTheorems_enclosure_and_trichotomy
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res : ℝ) (x : E)
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (db : LayerB.ComposableDefectBlock V) (d : db.Defect) :
    0 ≤ threeChannelWeightedSecondMoment P₁ P₂ w₁ w₂ w_res x ∧
      LayerB.IsNeutral db (db.compose d (db.conjugate d)) ∧
      (LayerB.charge db d = 0 ∨ LayerB.charge db d > 0 ∨ LayerB.charge db d < 0) := by
  have hnn := (threeChannelBhatiaDavisFunctional_factored_eq_and_secondMoment_nonneg
    hP w₁ w₂ w_res 0 1 x).1
  exact ⟨hnn,
    LayerB.opposite_can_neutralize db d,
    LayerB.sector_trichotomy db d⟩

/-- Three-channel Bhatia-Davis dispersion functional paired with the concrete
$U_\star$ model realization (`ConcreteModel`) and concrete electron/positron/proton/neutron
many-body charge algebra (`ConcreteMultiBody`). -/
theorem threeChannel_bhatiaDavis_with_concreteModel_and_concreteMultiBody
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res w_min w_max : ℝ)
    (hmin₁ : w_min ≤ w₁) (hmin₂ : w_min ≤ w₂) (hmin_r : w_min ≤ w_res)
    (hmax₁ : w₁ ≤ w_max) (hmax₂ : w₂ ≤ w_max) (hmax_r : w_res ≤ w_max)
    (x : E) :
    threeChannelBhatiaDavisFunctional P₁ P₂ w₁ w₂ w_res w_min w_max x ≤
        ((w_max - w_min) / 2) ^ 2 * hilbertEnergy x ∧
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
  have hbd := threeChannelBhatiaDavisFunctional_nonneg_and_popoviciu_bound
    hP w₁ w₂ w_res w_min w_max hmin₁ hmin₂ hmin_r hmax₁ hmax₂ hmax_r x
  have hreal := LayerC.concrete_realization
  exact ⟨hbd.2,
    hreal.1,
    LayerC.inertDefect_isInert,
    LayerC.sourceDefect_isSource,
    LayerC.electron_charge,
    LayerC.positron_charge,
    LayerC.neutron_charge,
    LayerC.positron_is_conjugate,
    LayerC.epem_neutral,
    LayerC.three_body_charge⟩

/-- Master synthesis of Bhatia-Davis / Popoviciu spectral dispersion inequalities
with all 7 charge-sector, dynamical-stability, far-field, multi-particle,
structural, and concrete many-body modules. -/
theorem bhatiaDavis_chargeSectors_farField_multiParticle_concreteMultiBody_bridge_master
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {P₁ P₂ : E →L[ℂ] E} (hP : AreMutuallyOrthogonalProjections P₁ P₂)
    (w₁ w₂ w_res w_min w_max : ℝ)
    (hmin₁ : w_min ≤ w₁) (hmin₂ : w_min ≤ w₂) (hmin_r : w_min ≤ w_res)
    (hmax₁ : w₁ ≤ w_max) (hmax₂ : w₂ ≤ w_max) (hmax_r : w_res ≤ w_max)
    (x : E) :
    0 ≤ threeChannelBhatiaDavisFunctional P₁ P₂ w₁ w₂ w_res w_min w_max x ∧
      threeChannelBhatiaDavisFunctional P₁ P₂ w₁ w₂ w_res w_min w_max x ≤
        ((w_max - w_min) / 2) ^ 2 * hilbertEnergy x ∧
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
  have hbd := threeChannelBhatiaDavisFunctional_nonneg_and_popoviciu_bound
    hP w₁ w₂ w_res w_min w_max hmin₁ hmin₂ hmin_r hmax₁ hmax₂ hmax_r x
  have hreal := LayerC.concrete_realization
  exact ⟨hbd.1, hbd.2,
    hreal.1,
    LayerC.inertDefect_isInert,
    LayerC.sourceDefect_isSource,
    LayerC.positron_is_conjugate,
    LayerC.epem_neutral,
    LayerC.three_body_charge⟩

#print axioms threeChannel_bhatiaDavis_with_chargeSectors_and_dynamicalStability
#print axioms multiChannel_bhatiaDavis_with_farField_and_multiParticle
#print axioms threeChannel_secondMoment_with_structuralTheorems_enclosure_and_trichotomy
#print axioms threeChannel_bhatiaDavis_with_concreteModel_and_concreteMultiBody
#print axioms bhatiaDavis_chargeSectors_farField_multiParticle_concreteMultiBody_bridge_master

end KFCausalBhatiaDavisDispersionChargeSectorsFarFieldMultiParticleConcreteMultiBodyBridge
end Audit
end UnifiedTheory
