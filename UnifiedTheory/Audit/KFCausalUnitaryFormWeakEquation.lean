/- The lifted unitary form group satisfies the weak Schrodinger equation
for every finite-energy initial vector. Operator-domain approximation is
uniform in the form norm, including the weak derivatives. -/
import UnifiedTheory.Audit.KFCausalUnitaryFormLift
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalUnitaryFormWeakEquation
noncomputable section
open Filter
open scoped Topology
open KFCausalFormHamiltonian KFCausalUnitaryFormLift
variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (J : V →L[ℂ] H) (hi : Function.Injective J) (hd : DenseRange J)
  (D : Data J hi hd)
local notation "T" => hamiltonian J hi hd
local notation "L" => formLift J hi hd
local notation "E" => evolution J hi hd D

def formFunctional (z : V) : V →L⋆[ℂ] ℂ :=
  innerSLFlip ℂ z-(innerSLFlip ℂ (J z)).comp J

omit [CompleteSpace V] [CompleteSpace H] in
theorem formFunctional_apply (z v : V) :
    formFunctional J z v=inner ℂ v z-inner ℂ (J v) (J z) := rfl

theorem uniform_form_inputs (v : ℕ → V) (w : V) (hv : Tendsto v atTop (𝓝 w)) :
    TendstoUniformly (fun n t => E t (v n)) (fun t => E t w) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  filter_upwards [(Metric.tendsto_nhds.mp hv) δ hδ] with n hn t
  simpa only [(E t).isometry.dist_eq,dist_comm] using hn

theorem weak_equation (c : ℂ)
    (hder : ∀ x : (T).domain, ∀ t,
      HasDerivAt (fun u => D.physical u (x:H)) (c • T (D.domainMap t x)) t)
    (v z : V) (t : ℝ) :
    HasDerivAt (fun u => inner ℂ (D.physical u (J v)) (J z))
      (star c*(inner ℂ (E t v) z-inner ℂ (J (E t v)) (J z))) t := by
  obtain ⟨v',hv',ht⟩ := mem_closure_iff_seq_limit.mp (lift_dense J hi hd v)
  choose x hx using hv'
  have hx' : Tendsto (fun n => L (x n)) atTop (𝓝 v) :=
    ht.congr' (Eventually.of_forall (fun n => (hx n).symm))
  have hu := ((star c) • formFunctional J z).uniformContinuous.comp_tendstoUniformly
    (uniform_form_inputs J hi hd D (fun n => L (x n)) v hx')
  apply hasDerivAt_of_tendstoUniformly (f := fun n u => inner ℂ (D.physical u (J (L (x n)))) (J z)) hu
  · apply Eventually.of_forall
    intro n u
    have he : formFunctional J z (E u (L (x n)))=inner ℂ (T (D.domainMap u (x n))) (J z) := by
      rw [formFunctional_apply,evolution_lift,embedding_formLift]
      exact hamiltonian_form_pairing J hi hd (D.domainMap u (x n)) z
    have hh := (hder (x n) u).inner ℂ (hasDerivAt_const u (J z))
    simpa only [Function.comp_def,embedding_formLift,ContinuousLinearMap.smul_apply,smul_eq_mul,he,
      inner_zero_right,add_zero,zero_add,inner_smul_left,starRingEnd_apply] using hh
  · intro u
    exact (((innerSLFlip ℂ (J z)).continuous.comp (D.physical u).continuous).comp J.continuous).tendsto v |>.comp hx'

#print axioms formFunctional_apply
#print axioms uniform_form_inputs
#print axioms weak_equation
end
end UnifiedTheory.Audit.KFCausalUnitaryFormWeakEquation
