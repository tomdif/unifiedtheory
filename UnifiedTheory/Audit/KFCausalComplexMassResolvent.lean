/- The inverse complex mass pencil resolves the actual mass/form graph,
with both inverse identities. No operator-domain surjectivity is assumed. -/
import UnifiedTheory.Audit.KFCausalComplexMassPencil

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalComplexMassResolvent
noncomputable section
open UnifiedTheory.Audit.KFCausalComplexMassPencil
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def resolvent (M Q : V →L[ℂ] V) (h b : ℝ) : V →L[ℂ] V := Ring.inverse (pencil M Q h b)*M

def output (M Q : V →L[ℂ] V) (h b : ℝ) (f : V) : V :=
  (phase h)⁻¹ • (b • resolvent M Q h b f-f)

theorem pencil_equation (M Q : V →L[ℂ] V) (h b : ℝ)
    (hu : IsUnit (pencil M Q h b)) (f : V) :
    pencil M Q h b (resolvent M Q h b f) = M f :=
  KFCausalCoerciveInverse.inverse_apply_right _ hu _

theorem output_equation (M Q : V →L[ℂ] V) (h b : ℝ) (hh : h ≠ 0)
    (hu : IsUnit (pencil M Q h b)) (f : V) :
    Q (resolvent M Q h b f) = M (output M Q h b f) := by
  have he := pencil_equation M Q h b hu f
  change b • M (resolvent M Q h b f)-phase h • Q (resolvent M Q h b f) = M f at he
  apply smul_right_injective V (phase_ne_zero h hh)
  change phase h • Q (resolvent M Q h b f) = phase h • M (output M Q h b f)
  rw [output,map_smul,smul_smul,mul_inv_cancel₀ (phase_ne_zero h hh),one_smul,
    map_sub,ContinuousLinearMap.map_smul_of_tower]
  exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (sub_eq_iff_eq_add.mp he).symm)

theorem resolvent_graph (M Q : V →L[ℂ] V) (hi : Function.Injective M) (h b : ℝ)
    (hh : h ≠ 0) (hu : IsUnit (pencil M Q h b)) (f : V) :
    (resolvent M Q h b f,output M Q h b f) ∈ (KFCausalMassFormOperator.operator M Q).graph :=
  (KFCausalMassFormOperator.graph_iff M Q hi _ _).mpr (output_equation M Q h b hh hu f)

theorem resolvent_right (M Q : V →L[ℂ] V) (h b : ℝ) (hh : h ≠ 0) (f : V) :
    b • resolvent M Q h b f-phase h • output M Q h b f = f := by
  rw [output,smul_smul,mul_inv_cancel₀ (phase_ne_zero h hh),one_smul]
  abel

theorem resolvent_left (M Q : V →L[ℂ] V) (h b : ℝ)
    (hu : IsUnit (pencil M Q h b)) (w v : V) (hw : Q w = M v) :
    resolvent M Q h b (b • w-phase h • v) = w := by
  have he : M (b • w-phase h • v) = pencil M Q h b w := by
    simp only [map_sub,ContinuousLinearMap.map_smul_of_tower,map_smul,
      pencil,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,hw]
  exact (congrArg (fun z : V => Ring.inverse (pencil M Q h b) z) he).trans
    (KFCausalCoerciveInverse.inverse_apply_left _ hu w)

#print axioms pencil_equation
#print axioms output_equation
#print axioms resolvent_graph
#print axioms resolvent_right
#print axioms resolvent_left
end
end UnifiedTheory.Audit.KFCausalComplexMassResolvent
