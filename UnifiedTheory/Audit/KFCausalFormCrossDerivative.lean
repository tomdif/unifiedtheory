/- Product rule for two form-continuous curves whose mass-dual curves
are differentiable. Physical strong differentiability is not required. -/
import UnifiedTheory.Audit.KFCausalMassGram
import UnifiedTheory.Audit.KFCausalStrongResidualCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalFormCrossDerivative
noncomputable section
open Filter
open scoped Topology
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem symmetric_pairing_derivative (G : V →L[ℂ] V)
    (hs : ∀ a b, inner ℂ (G a) b=inner ℂ a (G b))
    (u v : ℝ → V) (p q : V) (x : ℝ) (hv : ContinuousAt v x)
    (hu' : HasDerivAt (fun t => G (u t)) p x)
    (hv' : HasDerivAt (fun t => G (v t)) q x) :
    HasDerivAt (fun t => inner ℂ (G (u t)) (v t))
      (inner ℂ p (v x)+inner ℂ (u x) q) x := by
  have ht : Tendsto (fun h : ℝ => x+h) (𝓝[≠] 0) (𝓝 x) := by
    have hi : Tendsto (fun h : ℝ => h) (𝓝[≠] 0) (𝓝 0) :=
      tendsto_id.mono_right nhdsWithin_le_nhds
    simpa only [add_zero] using hi.const_add x
  have h₁ := hu'.tendsto_slope_zero.inner (𝕜 := ℂ) (hv.tendsto.comp ht)
  have h₂ := (tendsto_const_nhds (x := u x)).inner (𝕜 := ℂ) hv'.tendsto_slope_zero
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  convert h₁.add h₂ using 1
  funext h
  simp only [Function.comp_def,inner_smul_left_eq_smul,inner_smul_right_eq_smul]
  rw [← smul_add]
  congr 1
  rw [inner_sub_left,inner_sub_right,← hs,← hs]
  ring

theorem physical_pairing_derivative [CompleteSpace V] [CompleteSpace H]
    (J : V →L[ℂ] H) (u v : ℝ → V) (p q : V) (x : ℝ) (hv : ContinuousAt v x)
    (hu' : HasDerivAt (fun t => KFCausalBoundedFormCurve.gram J (u t)) p x)
    (hv' : HasDerivAt (fun t => KFCausalBoundedFormCurve.gram J (v t)) q x) :
    HasDerivAt (fun t => inner ℂ (J (u t)) (J (v t)))
      (inner ℂ p (v x)+inner ℂ (u x) q) x := by
  simpa only [KFCausalMassGram.gram_left_pairing] using
    symmetric_pairing_derivative (KFCausalBoundedFormCurve.gram J)
      (KFCausalMassGram.gram_inner_symm J) u v p q x hv hu' hv'

theorem mass_derivative [CompleteSpace V] [CompleteSpace H]
    (J : V →L[ℂ] H) (Q : V →L[ℂ] V)
    (hs : ∀ a b, inner ℂ (Q a) b=inner ℂ a (Q b))
    (a : ℝ) (v : ℝ → V) (hv : Continuous v)
    (hw : ∀ t z, HasDerivAt (fun r => inner ℂ (J (v r)) (J z))
      ((Complex.I*(a:ℂ))*inner ℂ (v t) (Q z)) t) (t : ℝ) :
    HasDerivAt (fun r => KFCausalBoundedFormCurve.gram J (v r))
      ((-Complex.I*(a:ℂ)) • Q (v t)) t := by
  apply KFCausalStrongResidualCalculus.strong_of_continuous_weak_derivative
    (fun r => KFCausalBoundedFormCurve.gram J (v r))
    (fun r => (-Complex.I*(a:ℂ)) • Q (v r))
    ((Q.continuous.comp hv).const_smul _) _ t
  intro r z
  have hc : starRingEnd ℂ (-Complex.I*(a:ℂ))=Complex.I*(a:ℂ) := by simp
  simpa only [KFCausalMassGram.gram_left_pairing,inner_smul_left,hc,hs] using hw r z

#print axioms symmetric_pairing_derivative
#print axioms physical_pairing_derivative
#print axioms mass_derivative
end
end UnifiedTheory.Audit.KFCausalFormCrossDerivative
