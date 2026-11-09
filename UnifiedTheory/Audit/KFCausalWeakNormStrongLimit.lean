/- Weak convergence plus convergence of norms gives strong convergence in
a complex Hilbert space. The filter formulation also applies to continuity
of a weakly continuous norm-preserving trajectory. -/
import UnifiedTheory.Audit.KFCausalHilbertWeakSubsequence
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalWeakNormStrongLimit
open Filter
open scoped Topology

variable {H α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem strong_of_weak_and_norm {u : α → H} {x : H} {l : Filter α}
    (hw : ∀ y, Tendsto (fun n => inner ℂ (u n) y) l (𝓝 (inner ℂ x y)))
    (hn : Tendsto (fun n => ‖u n‖) l (𝓝 ‖x‖)) : Tendsto u l (𝓝 x) := by
  have hr := Complex.continuous_re.continuousAt.tendsto.comp (hw x)
  have hs : Tendsto (fun n => ‖u n-x‖^2) l (𝓝 0) := by
    have hh := ((hn.pow 2).sub (hr.const_mul 2)).add_const (‖x‖^2)
    have hself : (inner ℂ x x).re = ‖x‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
    have hsq (n : α) : ‖u n-x‖^2 = ‖u n‖^2-2*(inner ℂ (u n) x).re+‖x‖^2 :=
      norm_sub_sq (𝕜 := ℂ) (u n) x
    simpa only [Function.comp_apply,hself,← hsq,show ‖x‖^2-2*‖x‖^2+‖x‖^2 = 0 by ring] using hh
  have hnorm : Tendsto (fun n => ‖u n-x‖) l (𝓝 0) := by
    have hh := (Real.continuous_sqrt.tendsto 0).comp hs
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hh
  have hd : Tendsto (fun n => u n-x) l (𝓝 (0:H)) := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  simpa only [sub_add_cancel,zero_add] using hd.add_const x

#print axioms strong_of_weak_and_norm

end UnifiedTheory.Audit.KFCausalWeakNormStrongLimit
