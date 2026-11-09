/- A complex expectation chain rule for a bounded observable and its
adjoint, both preserving a form space. Strong form continuity and the
weak mass-dual derivative suffice; no physical strong derivative or
Hamiltonian operator-domain invariance is assumed. -/
import UnifiedTheory.Audit.KFCausalFormObservableDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalComplexFormObservableDerivative
noncomputable section
open Filter
open scoped Topology ComplexConjugate

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def expectation (J : V →L[ℂ] H) (D : H →L[ℂ] H) (x : V) : ℂ :=
  inner ℂ (J x) (D (J x))

theorem mixed_increment (J : V →L[ℂ] H) (D D' : H →L[ℂ] H)
    (G A B : V →L[ℂ] V)
    (hG : ∀ x y, inner ℂ (G x) y = inner ℂ (J x) (J y))
    (hA : ∀ x, J (A x) = D (J x)) (hB : ∀ x, J (B x) = D' (J x))
    (hD : ∀ x y, inner ℂ (D x) y = inner ℂ x (D' y)) (x d : V) :
    expectation J D (x+d)-expectation J D x =
      inner ℂ (G d) (A x)+conj (inner ℂ (G d) (B x))+inner ℂ (G d) (A d) := by
  simp only [hG,hA,hB,← hD,inner_conj_symm,expectation,map_add,inner_add_left,inner_add_right]
  ring

theorem mixed_remainder_bound (G A : V →L[ℂ] V) (d : V) (h C : ℝ) (hC : 0 ≤ C)
    (hd : ‖G d‖ ≤ C*|h|) :
    ‖h⁻¹ • inner ℂ (G d) (A d)‖ ≤ (C*‖A‖)*‖d‖ := by
  by_cases hz : h = 0
  · simp only [hz,inv_zero,zero_smul,norm_zero]
    positivity
  · have hp := norm_inner_le_norm (𝕜 := ℂ) (G d) (A d)
    have hn := mul_le_mul hd (A.le_opNorm d) (norm_nonneg _) (by positivity : 0 ≤ C*|h|)
    rw [norm_smul,Real.norm_eq_abs,abs_inv]
    calc
      _ ≤ |h|⁻¹*((C*|h|)*(‖A‖*‖d‖)) :=
        mul_le_mul_of_nonneg_left (hp.trans hn) (by positivity)
      _ = (C*‖A‖)*‖d‖ := by field_simp

theorem expectation_derivative (J : V →L[ℂ] H) (D D' : H →L[ℂ] H)
    (G A B : V →L[ℂ] V)
    (hG : ∀ x y, inner ℂ (G x) y = inner ℂ (J x) (J y))
    (hA : ∀ x, J (A x) = D (J x)) (hB : ∀ x, J (B x) = D' (J x))
    (hD : ∀ x y, inner ℂ (D x) y = inner ℂ x (D' y))
    (u : ℝ → V) (v : V) (x C : ℝ) (hC : 0 ≤ C)
    (hu : ContinuousAt u x)
    (hl : ∀ᶠ h in 𝓝[≠] (0:ℝ), ‖G (u (x+h))-G (u x)‖ ≤ C*|h|)
    (hd : ∀ y, HasDerivAt (fun z => inner ℂ (G (u z)) y) (inner ℂ v y) x) :
    HasDerivAt (fun z => expectation J D (u z))
      (inner ℂ v (A (u x))+conj (inner ℂ v (B (u x)))) x := by
  have hconj := Complex.conjCLE.hasFDerivAt.comp_hasDerivAt x (hd (B (u x)))
  have hlin : Tendsto (fun h : ℝ => h⁻¹ •
      (inner ℂ (G (u (x+h)-u x)) (A (u x))+conj (inner ℂ (G (u (x+h)-u x)) (B (u x)))))
      (𝓝[≠] 0) (𝓝 (inner ℂ v (A (u x))+conj (inner ℂ v (B (u x))))) := by
    have hs := ((hd (A (u x))).add hconj).tendsto_slope_zero
    simp only [Function.comp_def,Complex.conjCLE_apply,Pi.add_apply,map_sub,inner_sub_left] at hs ⊢
    convert hs using 1
    funext h
    congr 1
    ring
  have hzero : Tendsto (fun h : ℝ => ‖u (x+h)-u x‖) (𝓝[≠] 0) (𝓝 0) := by
    have ht : Tendsto (fun h : ℝ => x+h) (𝓝[≠] 0) (𝓝 x) := by
      have hi : Tendsto (fun h : ℝ => h) (𝓝[≠] 0) (𝓝 0) :=
        tendsto_id.mono_right nhdsWithin_le_nhds
      simpa only [add_zero] using hi.const_add x
    simpa only [sub_self,norm_zero] using ((hu.tendsto.comp ht).sub_const (u x)).norm
  have hrem : Tendsto (fun h : ℝ => h⁻¹ • inner ℂ (G (u (x+h)-u x)) (A (u (x+h)-u x)))
      (𝓝[≠] 0) (𝓝 0) := by
    apply squeeze_zero_norm' (hl.mono (fun h hh => mixed_remainder_bound G A _ h C hC (by simpa only [map_sub] using hh)))
    simpa only [mul_zero] using hzero.const_mul (C*‖A‖)
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have he (h : ℝ) : expectation J D (u (x+h))-expectation J D (u x) =
      inner ℂ (G (u (x+h)-u x)) (A (u x))+
        conj (inner ℂ (G (u (x+h)-u x)) (B (u x)))+
        inner ℂ (G (u (x+h)-u x)) (A (u (x+h)-u x)) := by
    have hsum : u x+(u (x+h)-u x) = u (x+h) := by abel
    simpa only [hsum] using mixed_increment J D D' G A B hG hA hB hD (u x) (u (x+h)-u x)
  simpa only [he,smul_add,add_zero] using hlin.add hrem

#print axioms mixed_increment
#print axioms mixed_remainder_bound
#print axioms expectation_derivative

end
end UnifiedTheory.Audit.KFCausalComplexFormObservableDerivative
