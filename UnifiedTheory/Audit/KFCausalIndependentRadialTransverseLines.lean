/- Actual real coordinate lines of the complex-sheared sourced Gaussian.
The positive line widths are derived from the normalized physical shear.
Every coherent line jet has polynomial L2 domains and exact whole-line IBP. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialPulledLaplacian
import UnifiedTheory.Audit.KFCausalComplexGaussianLineIBP

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalIndependentRadialTransverseLines
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalComplexShearPerturbation (Space flow)
open KFCausalIndependentRadialEntireLaplacian (profile quadratic radiusLeft radiusRight basis)
open KFCausalIndependentRadialPulledLaplacian (scaledPoint flow_scaled)
open KFCausalPhysicalReciprocalNormalization (coupling coupling_bound)
open KFCausalPairedModeCoordinates (scale)

def totalQuadratic (α wL wR : ℝ) (x : Space) : ℂ :=
  quadratic (α/wL:ℝ) (α*wR:ℝ) x+(α/32:ℝ)*x 4^2
def totalBilinear (α wL wR : ℝ) (x v : Space) : ℂ :=
  (α/wL:ℝ)*(x 0*v 0+x 2*v 2)+(α*wR:ℝ)*(x 1*v 1+x 3*v 3)+
    (α/32:ℝ)*x 4*v 4
def lineWidth (α wL wR : ℝ) (δ : ℂ) (i : Fin 5) : ℂ :=
  totalQuadratic α wL wR (flow (2*scale) δ (basis i))
def lineSource (α wL wR : ℝ) (δ b : ℂ) (x : Space) (i : Fin 5) : ℂ :=
  -2*totalBilinear α wL wR (flow (2*scale) δ x) (flow (2*scale) δ (basis i))+
    b*(flow (2*scale) δ (basis i)) 4
def lineScalar (α wL wR : ℝ) (δ b : ℂ) (x : Space) : ℂ :=
  Complex.exp (-totalQuadratic α wL wR (flow (2*scale) δ x)+b*(flow (2*scale) δ x) 4)
def linePolynomial (δ : ℂ) (P : Polynomial ℂ) (x : Space) (i : Fin 5) : Polynomial ℂ :=
  P.comp (Polynomial.C ((flow (2*scale) δ x) 4)+
    Polynomial.C ((flow (2*scale) δ (basis i)) 4)*Polynomial.X)

private theorem flow_affine (δ : ℂ) (x v : Space) (t : ℂ) :
    flow (2*scale) δ (x+t • v)=flow (2*scale) δ x+t • flow (2*scale) δ v := by
  ext i
  fin_cases i <;> simp [flow] <;> ring

theorem line_packet (α wL wR : ℝ) (δ b : ℂ) (P : Polynomial ℂ)
    (x : Space) (i : Fin 5) (t : ℝ) :
    profile (α/wL:ℝ) (α*wR:ℝ) (α/32) b P (flow (2*scale) δ (x+(t:ℂ) • basis i))=
      lineScalar α wL wR δ b x*KFCausalComplexGaussianLineIBP.packet
        (lineWidth α wL wR δ i) (lineSource α wL wR δ b x i) (linePolynomial δ P x i) t := by
  rw [flow_affine]
  simp only [profile,KFCausalNeutralLinePackets.entire,lineScalar,lineWidth,lineSource,
    linePolynomial,KFCausalComplexGaussianLineIBP.packet,Polynomial.eval_comp,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  simp only [←mul_assoc,←Complex.exp_add]
  congr 2
  · simp [totalQuadratic,totalBilinear,quadratic,radiusLeft,radiusRight]
    ring
  · change (flow (2*scale) δ x) 4+(t:ℂ)*(flow (2*scale) δ (basis i)) 4=_
    ring

private theorem scaled_quadratic (α wL wR : ℝ) (hα : 0<α) (hL : 0<wL)
    (hR : 0<wR) (x : Space) :
    KFCausalComplexQuadraticPerturbation.quadratic (fun i=>scaledPoint α wL wR x i)=
      totalQuadratic α wL wR x := by
  have hs : (Real.sqrt (α/wL):ℂ)^2=(α/wL:ℝ) := by
    exact_mod_cast Real.sq_sqrt (div_nonneg hα.le hL.le)
  have ht : (Real.sqrt (α*wR):ℂ)^2=(α*wR:ℝ) := by
    exact_mod_cast Real.sq_sqrt (mul_nonneg hα.le hR.le)
  have hn : (Real.sqrt (α/32):ℂ)^2=(α/32:ℝ) := by
    exact_mod_cast Real.sq_sqrt (show 0≤α/32 by positivity)
  simp only [KFCausalComplexQuadraticPerturbation.quadratic,scaledPoint,
    Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,
    mul_pow,hs,ht,hn,add_zero,totalQuadratic,quadratic,radiusLeft,radiusRight]
  ring

theorem lineWidth_positive (α wL wR : ℝ) (hα : 0<α) (hL : 0<wL) (hR : 1≤wR)
    (δ : ℂ) (hδ : ‖δ‖≤1/5) (i : Fin 5) : 0<(lineWidth α wL wR δ i).re := by
  let X := scaledPoint α wL wR (basis i)
  let Z := flow (coupling α wR) δ X
  have hx : ∀j,(X j).im=0 := by
    intro j
    fin_cases i <;> fin_cases j <;> simp [X,scaledPoint,basis]
  have hm : 0<KFCausalComplexQuadraticPerturbation.mass (fun j=>X j) := by
    have hs : 0<Real.sqrt (α/wL) := Real.sqrt_pos.mpr (div_pos hα hL)
    have ht : 0<Real.sqrt (α*wR) := Real.sqrt_pos.mpr (mul_pos hα (zero_lt_one.trans_le hR))
    have hn : 0<Real.sqrt (α/32) := Real.sqrt_pos.mpr (by positivity)
    fin_cases i <;> simp [KFCausalComplexQuadraticPerturbation.mass,X,scaledPoint,basis,
      Fin.sum_univ_succ,Complex.norm_real,Real.norm_eq_abs,sq_abs] <;> positivity
  have hd := KFCausalComplexShearPerturbation.flow_difference (coupling α wR)
    (coupling_bound α wR hα hR) δ hδ X
  have hd' : ‖Z-X‖≤(1/6:ℝ)*‖X‖ := by
    change ‖Z-X‖≤(5/6:ℝ)*‖δ‖*‖X‖ at hd
    exact hd.trans (by nlinarith [mul_le_mul_of_nonneg_right hδ (norm_nonneg X)])
  have hs : KFCausalComplexQuadraticPerturbation.mass (fun j=>Z j-X j)≤
      (1/6:ℝ)^2*KFCausalComplexQuadraticPerturbation.mass (fun j=>X j) := by
    have hh := (sq_le_sq₀ (norm_nonneg (Z-X)) (by positivity : 0≤(1/6:ℝ)*‖X‖)).mpr hd'
    simpa only [mul_pow,PiLp.norm_sq_eq_of_L2,KFCausalComplexQuadraticPerturbation.mass,
      PiLp.sub_apply] using hh
  have hp := KFCausalComplexQuadraticPerturbation.perturbation_lower
    (fun j=>X j) (fun j=>Z j) hx (1/6) (by norm_num) hs
  have he : KFCausalComplexQuadraticPerturbation.quadratic (fun j=>Z j)=lineWidth α wL wR δ i := by
    dsimp only [Z,X]
    rw [flow_scaled α wL wR hα (zero_lt_one.trans_le hR)]
    exact scaled_quadratic α wL wR hα hL (zero_lt_one.trans_le hR) _
  rw [he] at hp
  nlinarith

theorem actual_half_increment (ε h q : ℝ) (hε : 0<ε) (hb : |h|≤ε/10) :
    ‖KFCausalComplexClockInverse.complexInverse ε (KFCausalTwoShearClockQuotient.shift (h/2) (q:ℂ))-
      KFCausalComplexClockInverse.complexInverse ε (q:ℂ)‖≤1/20 := by
  have hh : |h/2|≤ε/10 := by rw [abs_div]; norm_num; linarith [abs_nonneg h]
  have hi := KFCausalTwoShearClockQuotient.inverse_increment ε (h/2) hε hh (q:ℂ)
    (by simp only [Complex.ofReal_im,abs_zero]; exact abs_nonneg _)
  rw [norm_sub_rev] at hi
  apply hi.trans
  rw [abs_div,show |(2:ℝ)|=2 by norm_num]
  apply (div_le_iff₀ hε).mpr
  linarith

def lineJet (n : ℕ) (α : ℝ) (wL wR : Fin n→ℝ) (δ : ℂ) (b C : Fin n→ℂ)
    (P : Fin n→Polynomial ℂ) (x : Space) (i : Fin 5) (k : ℕ) : ℝ→ℂ :=
  KFCausalComplexGaussianLineIBP.jet n (fun j=>lineWidth α (wL j) (wR j) δ i)
    (fun j=>lineSource α (wL j) (wR j) δ (b j) x i)
    (fun j=>C j*lineScalar α (wL j) (wR j) δ (b j) x)
    (fun j=>linePolynomial δ (P j) x i) k

theorem lineJet_zero (n : ℕ) (α : ℝ) (wL wR : Fin n→ℝ) (δ : ℂ) (b C : Fin n→ℂ)
    (P : Fin n→Polynomial ℂ) (x : Space) (i : Fin 5) (t : ℝ) :
    lineJet n α wL wR δ b C P x i 0 t=
      ∑j,C j*profile (α/wL j:ℝ) (α*wR j:ℝ) (α/32) (b j) (P j)
        (flow (2*scale) δ (x+(t:ℂ) • basis i)) := by
  simp only [lineJet,KFCausalComplexGaussianLineIBP.jet,Function.iterate_zero_apply,line_packet,
    mul_assoc]

theorem lineJet_regular (n : ℕ) (α : ℝ) (wL wR : Fin n→ℝ) (δ : ℂ) (b C : Fin n→ℂ)
    (P : Fin n→Polynomial ℂ) (hα : 0<α) (hL : ∀j,0<wL j) (hR : ∀j,1≤wR j)
    (hδ : ‖δ‖≤1/5) (x : Space) (i : Fin 5) (k : ℕ) :
    KFCausalNeutralLineDomain.Regular (lineJet n α wL wR δ b C P x i k) :=
  KFCausalComplexGaussianLineIBP.jet_regular n _ _ _ _
    (fun j=>lineWidth_positive α (wL j) (wR j) hα (hL j) (hR j) δ hδ i) k

theorem lineJet_derivative (n : ℕ) (α : ℝ) (wL wR : Fin n→ℝ) (δ : ℂ) (b C : Fin n→ℂ)
    (P : Fin n→Polynomial ℂ) (x : Space) (i : Fin 5) (k : ℕ) (t : ℝ) :
    HasDerivAt (lineJet n α wL wR δ b C P x i k)
      (lineJet n α wL wR δ b C P x i (k+1) t) t :=
  KFCausalComplexGaussianLineIBP.jet_derivative n _ _ _ _ k t

theorem lineJet_ibp (n : ℕ) (α : ℝ) (wL wR : Fin n→ℝ) (δ : ℂ) (b C : Fin n→ℂ)
    (P : Fin n→Polynomial ℂ) (hα : 0<α) (hL : ∀j,0<wL j) (hR : ∀j,1≤wR j)
    (hδ : ‖δ‖≤1/5) (x : Space) (i : Fin 5) (k l : ℕ) (W : Polynomial ℂ) :
    (∫t:ℝ,W.eval (t:ℂ)*(conj (lineJet n α wL wR δ b C P x i k t)*
      lineJet n α wL wR δ b C P x i (l+1) t))=
      -(∫t:ℝ,W.derivative.eval (t:ℂ)*(conj (lineJet n α wL wR δ b C P x i k t)*
        lineJet n α wL wR δ b C P x i l t))-
       (∫t:ℝ,W.eval (t:ℂ)*(conj (lineJet n α wL wR δ b C P x i (k+1) t)*
        lineJet n α wL wR δ b C P x i l t)) :=
  KFCausalComplexGaussianLineIBP.weighted_jet_ibp n _ _ _ _ _ _
    (fun j=>lineWidth_positive α (wL j) (wR j) hα (hL j) (hR j) δ hδ i) k l W

#print axioms line_packet
#print axioms lineWidth_positive
#print axioms actual_half_increment
#print axioms lineJet_zero
#print axioms lineJet_regular
#print axioms lineJet_derivative
#print axioms lineJet_ibp
end
end UnifiedTheory.Audit.KFCausalIndependentRadialTransverseLines
