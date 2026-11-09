/- Five-dimensional polynomial L2 control of the actual small complex
physical shear. The Gaussian margin and all integration hypotheses are
derived from the physical widths, with no derivative-integrability premise. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialTransverseLines
import UnifiedTheory.Audit.KFCausalComplexVectorPolynomialAbsorption

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalIndependentRadialTransverseRegularity
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalComplexShearPerturbation (Space flow)
open KFCausalIndependentRadialPulledLaplacian (scaledPoint)
open KFCausalPhysicalReciprocalNormalization (coupling coupling_bound)
open KFCausalComplexQuadraticPerturbation (mass quadratic perturbation_lower)
open KFCausalComplexVectorPolynomialAbsorption (absorptionCap polynomial_source_bound)

abbrev RealSpace := Fin 5→ℝ
def realPoint (x : RealSpace) : Space := WithLp.toLp 2 (fun i=>(x i:ℂ))
def basePoint (α wL wR : ℝ) (x : RealSpace) : Space := scaledPoint α wL wR (realPoint x)
def target (α wL wR : ℝ) (δ : ℂ) (x : RealSpace) : Space :=
  flow (coupling α wR) δ (basePoint α wL wR x)
def rates (α wL wR : ℝ) : Fin 5→ℝ := ![α/wL,α*wR,α/wL,α*wR,α/32]
def packet (α wL wR : ℝ) (δ : ℂ) (b : Fin 5→ℂ) (P : MvPolynomial (Fin 5) ℂ)
    (x : RealSpace) : ℂ :=
  MvPolynomial.eval (fun i=>target α wL wR δ x i) P*
    Complex.exp ((∑i,b i*target α wL wR δ x i)-quadratic (fun i=>target α wL wR δ x i))

private theorem base_real (α wL wR : ℝ) (x : RealSpace) :
    ∀i,(basePoint α wL wR x i).im=0 := by
  intro i
  fin_cases i <;> simp [basePoint,scaledPoint,realPoint]

private theorem base_mass (α wL wR : ℝ) (hα : 0<α) (hL : 0<wL) (hR : 0<wR)
    (x : RealSpace) : ‖basePoint α wL wR x‖^2=∑i,rates α wL wR i*(x i)^2 := by
  have hs := Real.sq_sqrt (div_nonneg hα.le hL.le)
  have ht := Real.sq_sqrt (mul_nonneg hα.le hR.le)
  have hn := Real.sq_sqrt (show 0≤α/32 by positivity)
  simp only [PiLp.norm_sq_eq_of_L2,basePoint,scaledPoint,realPoint,rates,
    Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,
    norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,hs,ht,hn]
  rfl

private theorem rates_positive (α wL wR : ℝ) (hα : 0<α) (hL : 0<wL) (hR : 0<wR) :
    ∀i,0<rates α wL wR i := by
  intro i
  fin_cases i <;> dsimp [rates] <;> positivity

theorem shear_bounds (α wL wR : ℝ) (hα : 0<α) (hR : 1≤wR)
    (δ : ℂ) (hδ : ‖δ‖≤1/5) (x : RealSpace) :
    (23/36:ℝ)*‖basePoint α wL wR x‖^2≤
        (quadratic (fun i=>target α wL wR δ x i)).re ∧
      ‖target α wL wR δ x‖≤(7/6:ℝ)*‖basePoint α wL wR x‖ := by
  let X := basePoint α wL wR x
  let Y := target α wL wR δ x
  have hd := KFCausalComplexShearPerturbation.flow_difference (coupling α wR)
    (coupling_bound α wR hα hR) δ hδ X
  have hd' : ‖Y-X‖≤(1/6:ℝ)*‖X‖ := by
    exact hd.trans (by nlinarith [mul_le_mul_of_nonneg_right hδ (norm_nonneg X)])
  have hs : mass (fun i=>Y i-X i)≤(1/6:ℝ)^2*mass (fun i=>X i) := by
    have hh := (sq_le_sq₀ (norm_nonneg (Y-X)) (by positivity : 0≤(1/6:ℝ)*‖X‖)).mpr hd'
    simpa only [mul_pow,PiLp.norm_sq_eq_of_L2,mass,PiLp.sub_apply] using hh
  have hp := perturbation_lower (fun i=>X i) (fun i=>Y i) (base_real α wL wR x)
    (1/6) (by norm_num) hs
  have hn := norm_add_le (Y-X) X
  rw [sub_add_cancel] at hn
  constructor
  · norm_num only at hp
    simpa only [mass,←PiLp.norm_sq_eq_of_L2] using hp
  · change ‖Y‖≤(7/6:ℝ)*‖X‖
    linarith

theorem packet_bound (α wL wR : ℝ) (hα : 0<α) (hR : 1≤wR)
    (δ : ℂ) (hδ : ‖δ‖≤1/5) (b : Fin 5→ℂ) (P : MvPolynomial (Fin 5) ℂ) (x : RealSpace) :
    ‖packet α wL wR δ b P x‖≤absorptionCap P b (7/6) (23/72)*
      Real.exp (-(23/72:ℝ)*‖basePoint α wL wR x‖^2) := by
  obtain ⟨hq,hy⟩ := shear_bounds α wL wR hα hR δ hδ x
  have hb := polynomial_source_bound P b (fun i=>target α wL wR δ x i)
    (7/6) ‖basePoint α wL wR x‖ (23/72) (by norm_num) (norm_nonneg _) (by norm_num)
    (fun i=>(PiLp.norm_apply_le _ i).trans hy)
  have he : ‖Complex.exp (-quadratic (fun i=>target α wL wR δ x i))‖≤
      Real.exp (-(23/36:ℝ)*‖basePoint α wL wR x‖^2) := by
    rw [Complex.norm_exp,Complex.neg_re]
    exact Real.exp_le_exp.mpr (by linarith)
  have hs : Real.exp (-(23/36:ℝ)*‖basePoint α wL wR x‖^2)=
      Real.exp (-(23/72:ℝ)*‖basePoint α wL wR x‖^2)*
        Real.exp (-(23/72:ℝ)*‖basePoint α wL wR x‖^2) := by
    rw [←Real.exp_add]
    congr 1
    ring
  unfold packet
  rw [sub_eq_add_neg,Complex.exp_add,←mul_assoc,norm_mul]
  calc
    _ ≤ ‖MvPolynomial.eval (fun i=>target α wL wR δ x i) P*
        Complex.exp (∑i,b i*target α wL wR δ x i)‖*
      Real.exp (-(23/36:ℝ)*‖basePoint α wL wR x‖^2) :=
        mul_le_mul_of_nonneg_left he (norm_nonneg _)
    _ = _ := by rw [hs]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le

private theorem gaussian_integrable (α wL wR : ℝ) (hα : 0<α) (hL : 0<wL) (hR : 0<wR)
    (d : ℝ) (hd : 0<d) : Integrable (fun x:RealSpace=>Real.exp (-d*‖basePoint α wL wR x‖^2)) := by
  have hi := KFCausalPolynomialGaussianIntegrals.moment_integrable 5
    (fun i=>d*rates α wL wR i) (fun i=>mul_pos hd (rates_positive α wL wR hα hL hR i))
    (fun _=>0)
  simp only [pow_zero,Finset.prod_const_one,one_mul] at hi
  convert hi using 1
  funext x
  rw [base_mass α wL wR hα hL hR]
  simp only [KFCausalPolynomialGaussianIntegrals.weight,←Real.exp_sum,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem packet_memLp (α wL wR : ℝ) (hα : 0<α) (hL : 0<wL) (hR : 1≤wR)
    (δ : ℂ) (hδ : ‖δ‖≤1/5) (b : Fin 5→ℂ) (P : MvPolynomial (Fin 5) ℂ) :
    MemLp (packet α wL wR δ b P) 2 volume := by
  have hy (i : Fin 5) : Continuous (fun x : RealSpace => target α wL wR δ x i) := by
    fin_cases i <;> dsimp [target, flow, basePoint, scaledPoint, realPoint] <;> fun_prop
  have hc : Continuous (packet α wL wR δ b P) := by
    unfold packet
    simp only [MvPolynomial.eval_eq', quadratic]
    fun_prop
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have hi := (gaussian_integrable α wL wR hα hL (zero_lt_one.trans_le hR)
    (23/36) (by norm_num)).const_mul ((absorptionCap P b (7/6) (23/72))^2)
  apply hi.mono' (hc.norm.pow 2).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hh := (sq_le_sq₀ (norm_nonneg (packet α wL wR δ b P x))
    (mul_nonneg (KFCausalComplexVectorPolynomialAbsorption.absorptionCap_nonnegative
      P b (7/6) (23/72) (by norm_num)) (Real.exp_pos _).le)).mpr
      (packet_bound α wL wR hα hR δ hδ b P x)
  rw [mul_pow,←Real.exp_nat_mul] at hh
  norm_num only [Nat.cast_ofNat] at hh
  convert hh using 1
  congr 2
  ring

theorem packet_cross_integrable (α wL wR vL vR : ℝ) (hα : 0<α)
    (hL : 0<wL) (hR : 1≤wR) (hvL : 0<vL) (hvR : 1≤vR)
    (δ : ℂ) (hδ : ‖δ‖≤1/5) (b c : Fin 5→ℂ) (P Q : MvPolynomial (Fin 5) ℂ) :
    Integrable (fun x:RealSpace=>conj (packet α wL wR δ b P x)*packet α vL vR δ c Q x) := by
  have hi := (packet_memLp α wL wR hα hL hR δ hδ b P).star.integrable_mul
    (packet_memLp α vL vR hα hvL hvR δ hδ c Q)
  exact hi

#print axioms shear_bounds
#print axioms packet_bound
#print axioms packet_memLp
#print axioms packet_cross_integrable
end
end UnifiedTheory.Audit.KFCausalIndependentRadialTransverseRegularity
