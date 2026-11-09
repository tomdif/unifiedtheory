/- Additive energy floors for the completed tensor sum and two-boson form. -/
import UnifiedTheory.Audit.KFCausalTensorEnergyEstimate
import UnifiedTheory.Audit.KFCausalEnergyCoreFloor
import UnifiedTheory.Audit.KFCausalTwoBosonHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalTensorSumEnergyFloor
noncomputable section
open KFCausalClosedGraphForm KFCausalCompletedTensor KFCausalTensorSumHamiltonian

variable {H K X Y : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

def LowerBound (D : Data H K) (δ : ℝ) : Prop :=
  ∀ x : (hamiltonian D).domain, δ * ‖(x : H)‖ ^ 2 ≤ (inner ℂ (hamiltonian D x) (x : H)).re

theorem domainEnergy_lower (D : Data H K) (δ : ℝ) (hD : LowerBound D δ)
    (x : (hamiltonian D).domain) : δ * ‖(x : H)‖ ^ 2 ≤ ‖domainEnergy D x‖ ^ 2 := by
  change δ * ‖(x : H)‖ ^ 2 ≤ ‖energyOutput D (formLift D x)‖ ^ 2
  rw [← hamiltonian_energy]
  exact hD x

theorem core_lower (D : Data H K) (F : Data X Y) (δ η : ℝ)
    (hD : LowerBound D δ) (hF : LowerBound F η) (u : Core D F) :
    (δ + η) * ‖input D F u‖ ^ 2 ≤ ‖output D F u‖ ^ 2 := by
  have hl := KFCausalTensorEnergyEstimate.right_lower (hamiltonian D).domain.subtype
    (domainEnergy D) (hamiltonian F).domain.subtypeₗᵢ δ (domainEnergy_lower D δ hD) u
  have hr := KFCausalTensorEnergyEstimate.left_lower (hamiltonian D).domain.subtypeₗᵢ
    (hamiltonian F).domain.subtype (domainEnergy F) η (domainEnergy_lower F η hF) u
  have hi : ‖input D F u‖ = ‖TensorProduct.map
      (hamiltonian D).domain.subtype (hamiltonian F).domain.subtype u‖ :=
    (includeTensor H X).norm_map _
  have ho : ‖output D F u‖ ^ 2 =
      ‖TensorProduct.map (domainEnergy D) (hamiltonian F).domain.subtype u‖ ^ 2 +
      ‖TensorProduct.map (hamiltonian D).domain.subtype (domainEnergy F) u‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖includeTensor K X _‖ ^ 2 + ‖includeTensor H Y _‖ ^ 2 = _
    rw [(includeTensor K X).norm_map, (includeTensor H Y).norm_map]
  rw [hi, ho]
  change δ * ‖TensorProduct.map (hamiltonian D).domain.subtype
    (hamiltonian F).domain.subtype u‖ ^ 2 ≤
      ‖TensorProduct.map (domainEnergy D) (hamiltonian F).domain.subtype u‖ ^ 2 at hl
  change η * ‖TensorProduct.map (hamiltonian D).domain.subtype
    (hamiltonian F).domain.subtype u‖ ^ 2 ≤
      ‖TensorProduct.map (hamiltonian D).domain.subtype (domainEnergy F) u‖ ^ 2 at hr
  nlinarith

theorem tensor_lower (D : Data H K) (F : Data X Y) (δ η : ℝ)
    (hD : LowerBound D δ) (hF : LowerBound F η) : LowerBound (tensorForm D F) (δ + η) :=
  KFCausalEnergyCoreFloor.hamiltonian_lower _ _ _ _ _ _ (core_lower D F δ η hD hF)

theorem tensor_form_lower (D : Data H K) (F : Data X Y) (δ η : ℝ)
    (hD : LowerBound D δ) (hF : LowerBound F η) (u : FormSpace (tensorForm D F)) :
    (δ + η) * ‖embedding (tensorForm D F) u‖ ^ 2 ≤ ‖energyOutput (tensorForm D F) u‖ ^ 2 :=
  KFCausalEnergyCoreFloor.form_lower _ _ _ _ _ _ (core_lower D F δ η hD hF) u

theorem boson_core_lower (D : Data H K) (δ : ℝ) (hD : LowerBound D δ)
    (u : Core D D) :
    (δ + δ) * ‖KFCausalTwoBosonHamiltonian.bosonInput D u‖ ^ 2 ≤
      ‖KFCausalTwoBosonHamiltonian.bosonOutput D u‖ ^ 2 := by
  have h := core_lower D D δ δ hD hD (KFCausalTwoBosonHamiltonian.coreSym D u)
  change (δ + δ) * ‖(KFCausalTwoBosonHamiltonian.bosonInput D u : Space H H)‖ ^ 2 ≤ _
  rw [KFCausalTwoBosonHamiltonian.bosonInput_coe]
  exact h

theorem boson_lower (D : Data H K) (δ : ℝ) (hD : LowerBound D δ) :
    LowerBound (KFCausalTwoBosonHamiltonian.bosonForm D) (δ + δ) :=
  KFCausalEnergyCoreFloor.hamiltonian_lower _ _ _ _ _ _ (boson_core_lower D δ hD)

end
end UnifiedTheory.Audit.KFCausalTensorSumEnergyFloor
