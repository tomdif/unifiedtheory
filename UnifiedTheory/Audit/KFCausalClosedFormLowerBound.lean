/- A lower bound on a represented Hamiltonian extends to every vector
of its closed energy form, by density in the form norm. -/
import UnifiedTheory.Audit.KFCausalTensorSumEnergyFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalClosedFormLowerBound
noncomputable section
open KFCausalClosedGraphForm KFCausalTensorSumEnergyFloor

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem formLift_dense (D : Data H K) : DenseRange (formLift D) :=
  KFCausalFormHamiltonian.operator_domain_form_dense _ _ _

theorem lower_bound (D : Data H K) (δ : ℝ) (hD : LowerBound D δ)
    (u : FormSpace D) : δ * ‖embedding D u‖ ^ 2 ≤ ‖energyOutput D u‖ ^ 2 := by
  have hc : IsClosed {v : FormSpace D | δ * ‖embedding D v‖ ^ 2 ≤ ‖energyOutput D v‖ ^ 2} :=
    isClosed_le (continuous_const.mul ((embedding D).continuous.norm.pow 2))
      ((energyOutput D).continuous.norm.pow 2)
  refine (formLift_dense D).induction_on u hc ?_
  intro x
  change δ * ‖embedding D (formLift D x)‖ ^ 2 ≤ ‖energyOutput D (formLift D x)‖ ^ 2
  rw [embedding_formLift, ← hamiltonian_energy]
  exact hD x

end
end UnifiedTheory.Audit.KFCausalClosedFormLowerBound
