/- Whole-line integration by parts for coherent complex quadratic Gaussian
packets. Positive real quadratic coefficients supply every polynomial L2
and L1 premise; no endpoint or derivative hypothesis is imposed on packets. -/
import UnifiedTheory.Audit.KFCausalNeutralLineDomain
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalComplexGaussianLineIBP
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalNeutralLineDomain (Regular polynomial_cross_integrable)

def packet (a b : ℂ) (P : Polynomial ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-a*(x:ℂ)^2+b*(x:ℂ))*P.eval (x:ℂ)
def step (a b : ℂ) (P : Polynomial ℂ) : Polynomial ℂ :=
  P.derivative+(Polynomial.C b-Polynomial.C (2*a)*Polynomial.X)*P

private theorem packet_norm (a b : ℂ) (P : Polynomial ℂ) (x : ℝ) :
    ‖packet a b P x‖=‖KFCausalNeutralLinePackets.packet a.re b P x‖ := by
  simp only [packet,KFCausalNeutralLinePackets.packet,KFCausalNeutralLinePackets.entire,
    norm_mul,Complex.norm_exp]
  congr 2
  simp [Complex.mul_re,Complex.mul_im,pow_two]

theorem packet_regular (a b : ℂ) (ha : 0<a.re) (P : Polynomial ℂ) :
    Regular (packet a b P) := by
  intro Q
  have hi := KFCausalNeutralLineDomain.packet_regular a.re ha b P Q
  apply hi.of_le (by unfold packet; fun_prop)
  filter_upwards [] with x
  rw [norm_mul,norm_mul,packet_norm]

theorem packet_derivative (a b : ℂ) (P : Polynomial ℂ) (x : ℝ) :
    HasDerivAt (packet a b P) (packet a b (step a b P) x) x := by
  have he := ((((hasDerivAt_id x).ofReal_comp.pow 2).const_mul (-a)).add
    ((hasDerivAt_id x).ofReal_comp.const_mul b)).cexp
  convert he.mul ((P.hasDerivAt (x:ℂ)).comp_ofReal) using 1
  dsimp [packet,step]
  simp only [Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X]
  ring

def jet (n : ℕ) (a b c : Fin n→ℂ) (P : Fin n→Polynomial ℂ) (k : ℕ) (x : ℝ) : ℂ :=
  ∑i,c i*packet (a i) (b i) ((step (a i) (b i))^[k] (P i)) x

theorem jet_regular (n : ℕ) (a b c : Fin n→ℂ) (P : Fin n→Polynomial ℂ)
    (ha : ∀i,0<(a i).re) (k : ℕ) : Regular (jet n a b c P k) :=
  KFCausalNeutralLineDomain.regular_sum n _ (fun i =>
    KFCausalNeutralLineDomain.regular_const_mul _
      (packet_regular (a i) (b i) (ha i) _) (c i))

theorem jet_derivative (n : ℕ) (a b c : Fin n→ℂ) (P : Fin n→Polynomial ℂ)
    (k : ℕ) (x : ℝ) : HasDerivAt (jet n a b c P k) (jet n a b c P (k+1) x) x := by
  have hh := HasDerivAt.fun_sum (fun i (_:i∈(Finset.univ:Finset (Fin n))) =>
    (packet_derivative (a i) (b i) ((step (a i) (b i))^[k] (P i)) x).const_mul (c i))
  simpa only [jet,Function.iterate_succ_apply'] using hh

theorem jet_cross_integrable (n : ℕ) (a b c e : Fin n→ℂ)
    (P Q : Fin n→Polynomial ℂ) (ha : ∀i,0<(a i).re) (k l : ℕ) (W : Polynomial ℂ) :
    Integrable (fun x:ℝ=>W.eval (x:ℂ)*(conj (jet n a b c P k x)*jet n a b e Q l x)) :=
  polynomial_cross_integrable _ _ (jet_regular n a b c P ha k)
    (jet_regular n a b e Q ha l) W

theorem weighted_jet_ibp (n : ℕ) (a b c e : Fin n→ℂ)
    (P Q : Fin n→Polynomial ℂ) (ha : ∀i,0<(a i).re) (k l : ℕ) (W : Polynomial ℂ) :
    (∫x:ℝ,W.eval (x:ℂ)*(conj (jet n a b c P k x)*jet n a b e Q (l+1) x))=
      -(∫x:ℝ,W.derivative.eval (x:ℂ)*(conj (jet n a b c P k x)*jet n a b e Q l x))-
       (∫x:ℝ,W.eval (x:ℂ)*(conj (jet n a b c P (k+1) x)*jet n a b e Q l x)) := by
  let u := fun x:ℝ=>W.eval (x:ℂ)*conj (jet n a b c P k x)
  let du := fun x:ℝ=>W.derivative.eval (x:ℂ)*conj (jet n a b c P k x)+
    W.eval (x:ℂ)*conj (jet n a b c P (k+1) x)
  have hu (x:ℝ) : HasDerivAt u (du x) x :=
    ((W.hasDerivAt (x:ℂ)).comp_ofReal).mul (jet_derivative n a b c P k x).star
  have h1 := jet_cross_integrable n a b c e P Q ha k (l+1) W
  have h2 := jet_cross_integrable n a b c e P Q ha k l W.derivative
  have h3 := jet_cross_integrable n a b c e P Q ha (k+1) l W
  have h0 := jet_cross_integrable n a b c e P Q ha k l W
  have hi1 : Integrable (fun x=>u x*jet n a b e Q (l+1) x) := by
    simpa only [u,mul_assoc] using h1
  have hi2 : Integrable (fun x=>du x*jet n a b e Q l x) := by
    simpa only [du,add_mul,mul_assoc] using h2.add h3
  have hi0 : Integrable (fun x=>u x*jet n a b e Q l x) := by
    simpa only [u,mul_assoc] using h0
  have hh := integral_mul_deriv_eq_deriv_mul_of_integrable hu
    (jet_derivative n a b e Q l) hi1 hi2 hi0
  simp only [u,du,add_mul,mul_assoc] at hh
  rw [integral_add h2 h3] at hh
  exact hh.trans (neg_add _ _)

#print axioms packet_regular
#print axioms packet_derivative
#print axioms jet_regular
#print axioms jet_derivative
#print axioms jet_cross_integrable
#print axioms weighted_jet_ibp
end
end UnifiedTheory.Audit.KFCausalComplexGaussianLineIBP
