/- Energy differentiation along a bounded Schrodinger trajectory and
the scalar integrating-factor estimate used for uniform energy bounds. -/
import UnifiedTheory.Audit.KFCausalHilbertStateEvolution
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSchrodingerEnergyEstimate
noncomputable section
open UnifiedTheory.Audit.KFCausalHilbertStateEvolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def expectation (K : H →L[ℂ] H) (f : H) : ℝ := (inner ℂ (K f) f).re

theorem energy_derivative [CompleteSpace H] (K : ℝ → H →L[ℂ] H) (K' : H →L[ℂ] H)
    (v : ℝ → H) (hbar t : ℝ) (hk : HasDerivAt K K' t) (hs : IsSelfAdjoint (K t))
    (hv : HasDerivAt v ((-Complex.I*((1/hbar:ℝ):ℂ)) • K t (v t)) t) :
    HasDerivAt (fun z => expectation (K z) (v z)) (expectation K' (v t)) t := by
  let c : ℂ := -Complex.I*((1/hbar:ℝ):ℂ)
  have hc : star c = -c := by simp [c]
  have hm : inner ℂ (K t (K t (v t))) (v t) = inner ℂ (K t (v t)) (K t (v t)) :=
    hs.isSymmetric _ _
  have he : inner ℂ (K t (v t)) (c • K t (v t)) +
      inner ℂ (K' (v t)+K t (c • K t (v t))) (v t) = inner ℂ (K' (v t)) (v t) := by
    rw [inner_add_left,map_smul,inner_smul_right,inner_smul_left,hm]
    change c*inner ℂ (K t (v t)) (K t (v t)) +
      (inner ℂ (K' (v t)) (v t)+star c*inner ℂ (K t (v t)) (K t (v t))) = _
    rw [hc]
    ring
  have hd := (operator_apply_derivative K v K' (c • K t (v t)) t hk hv).inner ℂ hv
  have hi : HasDerivAt (fun z => inner ℂ (K z (v z)) (v z)) (inner ℂ (K' (v t)) (v t)) t := by
    convert hd using 1
    exact he.symm
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hi

theorem energy_comparison (E D : ℝ → ℝ) (hd : ∀ t, HasDerivAt E (D t) t)
    (hb : ∀ t, 0 ≤ D t ∧ D t ≤ 2*E t) (s t : ℝ) (hst : s ≤ t) :
    E s ≤ E t ∧ E t ≤ Real.exp (2*(t-s))*E s := by
  have hm : Monotone E := monotone_of_hasDerivAt_nonneg hd (fun x => (hb x).1)
  refine ⟨hm hst,?_⟩
  have hw : ∀ x, HasDerivAt (fun r => Real.exp (-2*r)*E r)
      (Real.exp (-2*x)*(D x-2*E x)) x := by
    intro x
    have he := (Real.hasDerivAt_exp (-2*x)).comp x ((hasDerivAt_id x).const_mul (-2))
    convert he.mul (hd x) using 1
    simp only [Function.comp_apply]
    ring
  have ha : Antitone (fun r => Real.exp (-2*r)*E r) :=
    antitone_of_hasDerivAt_nonpos hw (fun x => mul_nonpos_of_nonneg_of_nonpos
      (Real.exp_pos _).le (sub_nonpos.mpr (hb x).2))
  have hh := mul_le_mul_of_nonneg_left (ha hst) (Real.exp_pos (2*t)).le
  have hself : Real.exp (2*t)*Real.exp (-2*t) = 1 := by rw [← Real.exp_add]; ring_nf; simp
  have hshift : Real.exp (2*t)*Real.exp (-2*s) = Real.exp (2*(t-s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simpa only [← mul_assoc,hself,one_mul,hshift] using hh

theorem energy_bound_all_times (E D : ℝ → ℝ) (hd : ∀ t, HasDerivAt E (D t) t)
    (hb : ∀ t, 0 ≤ D t ∧ D t ≤ 2*E t) (s t Q : ℝ) (hQ : 0 ≤ Q) (hinit : E s ≤ Q) :
    E t ≤ Real.exp (2*|t-s|)*Q := by
  by_cases hst : s ≤ t
  · rw [abs_of_nonneg (sub_nonneg.mpr hst)]
    exact (energy_comparison E D hd hb s t hst).2.trans
      (mul_le_mul_of_nonneg_left hinit (Real.exp_pos _).le)
  · have hts : t ≤ s := le_of_not_ge hst
    have he : 1 ≤ Real.exp (2*|t-s|) := Real.one_le_exp (by positivity)
    calc
      E t ≤ E s := (energy_comparison E D hd hb t s hts).1
      _ ≤ Q := hinit
      _ ≤ Real.exp (2*|t-s|)*Q := by nlinarith

#print axioms energy_derivative
#print axioms energy_comparison
#print axioms energy_bound_all_times

end
end UnifiedTheory.Audit.KFCausalSchrodingerEnergyEstimate
