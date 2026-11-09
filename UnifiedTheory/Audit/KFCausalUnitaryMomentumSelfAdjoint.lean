/- Self-adjointness of -i*hbar times the maximal strong derivative.
The adjoint domain is proved equal to the actual derivative domain by
the weak-to-strong orbit argument. Nonzero hbar is explicit. -/
import UnifiedTheory.Audit.KFCausalUnitaryWeakGenerator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalUnitaryMomentumSelfAdjoint
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage
open UnifiedTheory.Audit.KFCausalStrongUnitaryGenerator
open UnifiedTheory.Audit.KFCausalUnitaryWeakGenerator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (U : StrongUnitaryGroup H)

def momentum (hbar : ℝ) : H →ₗ.[ℂ] H := (-Complex.I*(hbar:ℂ)) • generator U

theorem momentum_apply (hbar : ℝ) (x : (momentum U hbar).domain) :
    momentum U hbar x = (-Complex.I*(hbar:ℂ)) • generator U x := rfl

theorem momentum_symmetric (hbar : ℝ) :
    (momentum U hbar).IsFormalAdjoint (momentum U hbar) := by
  intro x y
  have hh := generator_skew_symmetric U x y
  have he : inner ℂ (generator U x) (y:H) = -inner ℂ (x:H) (generator U y) :=
    eq_neg_of_add_eq_zero_right hh
  rw [momentum_apply,momentum_apply,inner_smul_left,inner_smul_right,he]
  simp

variable [CompleteSpace H]

theorem momentum_dense (hbar : ℝ) : Dense ((momentum U hbar).domain : Set H) := generator_dense U

theorem adjoint_weak_derivative (hbar : ℝ) (hh : hbar ≠ 0)
    (x : (momentum U hbar).adjoint.domain) :
    ∀ y : (generator U).domain,
      inner ℂ (generator U y) (x:H) =
        -inner ℂ (y:H) ((Complex.I/(hbar:ℂ)) • (momentum U hbar).adjoint x) := by
  intro y
  have hp := LinearPMap.adjoint_isFormalAdjoint (momentum_dense U hbar) x y
  rw [momentum_apply,inner_smul_right] at hp
  have hc := congrArg (starRingEnd ℂ) hp
  simp only [map_mul,map_neg,Complex.conj_I,Complex.conj_ofReal,neg_neg,inner_conj_symm] at hc
  rw [inner_smul_right,hc]
  have hn : (hbar:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  field_simp
  ring_nf
  norm_num [Complex.I_sq]

theorem adjoint_domain_subset (hbar : ℝ) (hh : hbar ≠ 0) :
    (momentum U hbar).adjoint.domain ≤ (momentum U hbar).domain := by
  intro x hx
  exact (weak_implies_strong U x ((Complex.I/(hbar:ℂ)) • (momentum U hbar).adjoint ⟨x,hx⟩)
    (adjoint_weak_derivative U hbar hh ⟨x,hx⟩)).differentiableAt

theorem momentum_selfAdjoint (hbar : ℝ) (hh : hbar ≠ 0) : IsSelfAdjoint (momentum U hbar) := by
  have hf : momentum U hbar ≤ (momentum U hbar).adjoint :=
    (momentum_symmetric U hbar).le_adjoint (momentum_dense U hbar)
  exact LinearPMap.isSelfAdjoint_def.mpr
    (LinearPMap.eq_of_le_of_domain_eq hf
      (le_antisymm hf.1 (adjoint_domain_subset U hbar hh))).symm

theorem momentum_closed (hbar : ℝ) (hh : hbar ≠ 0) : (momentum U hbar).IsClosed :=
  (momentum_selfAdjoint U hbar hh).isClosed

#print axioms momentum_symmetric
#print axioms momentum_dense
#print axioms adjoint_weak_derivative
#print axioms adjoint_domain_subset
#print axioms momentum_selfAdjoint
#print axioms momentum_closed

end
end UnifiedTheory.Audit.KFCausalUnitaryMomentumSelfAdjoint
