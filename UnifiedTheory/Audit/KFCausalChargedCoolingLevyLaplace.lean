/- Finite Laplace expansions of the actual paired cooling derivative. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingLevyDerivative
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedCoolingLevyLaplace
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
open KFCausalPositiveKernelExponential (phase)
open KFCausalChargedCoolingLevyTruncation
open KFCausalChargedCoolingLevyConvergence
open KFCausalChargedCoolingLevyDerivative

def damping (N : ℕ) (t : ℝ) : ℝ := 1-(Real.exp (-2*Real.pi*t))^N

def oddRate (n : ℕ) : ℝ := (2*(n:ℝ)+1)*Real.pi

theorem damping_mem (N : ℕ) (t : ℝ) (ht : 0 < t) : damping N t ∈ Icc 0 1 := by
  have hq : 0 ≤ Real.exp (-2*Real.pi*t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2*Real.pi*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hp : (Real.exp (-2*Real.pi*t))^N ≤ 1 := pow_le_one₀ hq hq1
  have hn := pow_nonneg hq N
  exact ⟨by dsimp [damping]; linarith, by dsimp [damping]; linarith⟩

theorem damping_tendsto (t : ℝ) (ht : 0 < t) :
    Tendsto (fun N => damping N t) atTop (𝓝 1) := by
  have hq : 0 ≤ Real.exp (-2*Real.pi*t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2*Real.pi*t) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  simpa only [sub_zero] using tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1)

theorem damping_geometric (N : ℕ) (t : ℝ) (ht : 0 < t) :
    damping N t / Real.sinh (Real.pi*t) =
      2*∑ n ∈ Finset.range N, Real.exp (-(oddRate n)*t) := by
  have hs : Real.sinh (Real.pi*t) ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht))
  have hterm (n : ℕ) : Real.exp (-(oddRate n)*t) =
      Real.exp (-Real.pi*t)*(Real.exp (-2*Real.pi*t))^n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    unfold oddRate
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  apply (div_eq_iff hs).mpr
  have hid : 2*Real.exp (-Real.pi*t)*Real.sinh (Real.pi*t) = 1-Real.exp (-2*Real.pi*t) := by
    rw [Real.sinh_eq]
    have h1 : Real.exp (-Real.pi*t)*Real.exp (Real.pi*t) = 1 := by
      rw [← Real.exp_add, show -Real.pi*t+Real.pi*t = 0 by ring, Real.exp_zero]
    have h2 : Real.exp (-Real.pi*t)*Real.exp (-(Real.pi*t)) = Real.exp (-2*Real.pi*t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    nlinarith
  calc
    damping N t = (∑ n ∈ Finset.range N, (Real.exp (-2*Real.pi*t))^n)*
        (1-Real.exp (-2*Real.pi*t)) := (geom_sum_mul_neg _ _).symm
    _ = _ := by rw [← hid]; ring

theorem damped_integral_tendsto (kind : Bool) (θ z : ℝ) (hθ : |θ| < Real.pi/2) :
    Tendsto (fun N => ∫ t in Ioi 0, (damping N t:ℂ)*pairedDerivative kind θ z t)
      atTop (𝓝 (∫ t in Ioi 0, pairedDerivative kind θ z t)) := by
  have hi := (fullExponent_differentiation kind θ z hθ).1
  apply tendsto_integral_of_dominated_convergence (fun t => ‖pairedDerivative kind θ z t‖)
  · intro N
    exact (show Continuous (fun t => (damping N t:ℂ)) by unfold damping; fun_prop).aestronglyMeasurable.mul hi.1
  · exact hi.norm
  · intro N
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (damping_mem N t ht).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (damping_mem N t ht).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa only [Complex.ofReal_one, one_mul] using
      ((Complex.continuous_ofReal.tendsto 1).comp (damping_tendsto t ht)).mul_const
        (pairedDerivative kind θ z t)

def laplacePair (a s z t : ℝ) : ℂ :=
  2*Complex.I*(Complex.exp ((-a-s+2*(z:ℂ)*Complex.I)*(t:ℂ))-
    Complex.exp ((-a+s-2*(z:ℂ)*Complex.I)*(t:ℂ)))

def rationalPair (a s z : ℝ) : ℂ :=
  2*Complex.I*(1/(a+s-2*(z:ℂ)*Complex.I)-1/(a-s+2*(z:ℂ)*Complex.I))

theorem laplacePair_integrable (a s z : ℝ) (ha : |s| < a) :
    IntegrableOn (laplacePair a s z) (Ioi 0) := by
  have hp : (-a-s+2*(z:ℂ)*Complex.I).re < 0 := by
    norm_num [Complex.mul_re, Complex.mul_im]
    linarith [neg_abs_le s]
  have hm : (-a+s-2*(z:ℂ)*Complex.I).re < 0 := by
    norm_num [Complex.mul_re, Complex.mul_im]
    linarith [le_abs_self s]
  exact ((integrableOn_exp_mul_complex_Ioi hp 0).sub
    (integrableOn_exp_mul_complex_Ioi hm 0)).const_mul _

theorem laplacePair_integral (a s z : ℝ) (ha : |s| < a) :
    (∫ t in Ioi 0, laplacePair a s z t) = rationalPair a s z := by
  have hp : (-a-s+2*(z:ℂ)*Complex.I).re < 0 := by
    norm_num [Complex.mul_re, Complex.mul_im]
    linarith [neg_abs_le s]
  have hm : (-a+s-2*(z:ℂ)*Complex.I).re < 0 := by
    norm_num [Complex.mul_re, Complex.mul_im]
    linarith [le_abs_self s]
  unfold laplacePair
  rw [integral_const_mul, integral_sub
    (integrableOn_exp_mul_complex_Ioi hp 0) (integrableOn_exp_mul_complex_Ioi hm 0),
    integral_exp_mul_complex_Ioi hp 0, integral_exp_mul_complex_Ioi hm 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  unfold rationalPair
  rw [show (-a-s+2*(z:ℂ)*Complex.I) = -(a+s-2*(z:ℂ)*Complex.I) by ring,
    show (-a+s-2*(z:ℂ)*Complex.I) = -(a-s+2*(z:ℂ)*Complex.I) by ring,
    neg_div_neg_eq, neg_div_neg_eq]

theorem rationalPair_eq (a s z : ℝ) (ha : |s| < a) :
    rationalPair a s z = -8*((z:ℂ)+(s:ℂ)*Complex.I/2)/
      ((a:ℂ)^2+4*((z:ℂ)+(s:ℂ)*Complex.I/2)^2) := by
  have hp : (a+s-2*(z:ℂ)*Complex.I) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [Complex.mul_re, Complex.mul_im] at hr
    linarith [neg_abs_le s]
  have hm : (a-s+2*(z:ℂ)*Complex.I) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [Complex.mul_re, Complex.mul_im] at hr
    linarith [le_abs_self s]
  have he : (a:ℂ)^2+4*((z:ℂ)+(s:ℂ)*Complex.I/2)^2 =
      (a+s-2*(z:ℂ)*Complex.I)*(a-s+2*(z:ℂ)*Complex.I) := by
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [he]
  unfold rationalPair
  rw [div_sub_div _ _ hp hm, ← mul_div_assoc]
  congr 1
  ring_nf
  simp only [Complex.I_sq]
  ring

def mode (kind : Bool) (j : Fin 3) : ℝ :=
  if j = 0 then 2 else if j = 1 then -2 else if kind then -1 else 1

def coefficient (kind : Bool) (j : Fin 3) : ℝ :=
  if j = 0 then 1/2 else if j = 1 then (if kind then 2 else 1) else -1

private theorem numerator_modes (kind : Bool) (s : ℝ) :
    (numerator kind s:ℂ) = ∑ j : Fin 3,
      (coefficient kind j:ℂ)*Complex.exp ((mode kind j:ℂ)*(s:ℂ)) := by
  cases kind <;> simp [numerator,numeratorB,numeratorC,Fin.sum_univ_three,mode,coefficient,
    ← Complex.ofReal_exp, ← Complex.ofReal_mul] <;> push_cast <;> ring

def component (s z t : ℝ) : ℂ :=
  Complex.I*(Complex.exp (-(s:ℂ)*(t:ℂ))*phase (2*z) t-
    Complex.exp ((s:ℂ)*(t:ℂ))*phase (-2*z) t)/(Real.sinh (Real.pi*t):ℂ)

theorem pairedDerivative_modes (kind : Bool) (θ z t : ℝ) (ht : 0 < t) :
    pairedDerivative kind θ z t = ∑ j : Fin 3,
      (coefficient kind j:ℂ)*component (mode kind j*θ) z t := by
  have hs : Real.sinh (Real.pi*t) ≠ 0 :=
    ne_of_gt (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht))
  have he : pairedDerivative kind θ z t =
      Complex.I*((numerator kind (-θ*t):ℂ)*phase (2*z) t-
        (numerator kind (θ*t):ℂ)*phase (-2*z) t)/(Real.sinh (Real.pi*t):ℂ) := by
    unfold pairedDerivative density
    push_cast
    field_simp [ne_of_gt ht,hs]
  rw [he,numerator_modes,numerator_modes]
  simp only [Finset.sum_mul,Finset.mul_sum,← Finset.sum_sub_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  unfold component
  push_cast
  rw [show (mode kind j:ℂ)*(-(θ:ℂ)*(t:ℂ)) = -((mode kind j:ℂ)*(θ:ℂ))*(t:ℂ) by ring,
    show (mode kind j:ℂ)*((θ:ℂ)*(t:ℂ)) = ((mode kind j:ℂ)*(θ:ℂ))*(t:ℂ) by ring]
  ring

theorem component_damped (N : ℕ) (s z t : ℝ) (ht : 0 < t) :
    (damping N t:ℂ)*component s z t =
      ∑ n ∈ Finset.range N, laplacePair (oddRate n) s z t := by
  have he (n : ℕ) : laplacePair (oddRate n) s z t =
      2*(Real.exp (-(oddRate n)*t):ℂ)*Complex.I*
        (Complex.exp (-(s:ℂ)*(t:ℂ))*phase (2*z) t-
          Complex.exp ((s:ℂ)*(t:ℂ))*phase (-2*z) t) := by
    unfold laplacePair phase
    rw [Complex.ofReal_exp]
    push_cast
    simp only [mul_sub]
    simp only [← mul_assoc]
    rw [show (-((oddRate n):ℂ)-(s:ℂ)+2*(z:ℂ)*Complex.I)*(t:ℂ) =
      (-((oddRate n):ℂ)*(t:ℂ))+(-(s:ℂ)*(t:ℂ))+((2*(z:ℂ)*(t:ℂ))*Complex.I) by ring,
      show (-((oddRate n):ℂ)+(s:ℂ)-2*(z:ℂ)*Complex.I)*(t:ℂ) =
      (-((oddRate n):ℂ)*(t:ℂ))+((s:ℂ)*(t:ℂ))+((-2*(z:ℂ)*(t:ℂ))*Complex.I) by ring]
    simp only [Complex.exp_add]
    ring
  simp_rw [he]
  have hg := congrArg (fun q : ℝ => (q:ℂ)) (damping_geometric N t ht)
  simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_sum] at hg
  unfold component
  rw [show (damping N t:ℂ)*(Complex.I*(Complex.exp (-(s:ℂ)*(t:ℂ))*phase (2*z) t-
      Complex.exp ((s:ℂ)*(t:ℂ))*phase (-2*z) t)/(Real.sinh (Real.pi*t):ℂ)) =
    ((damping N t:ℂ)/(Real.sinh (Real.pi*t):ℂ))*Complex.I*
      (Complex.exp (-(s:ℂ)*(t:ℂ))*phase (2*z) t-
      Complex.exp ((s:ℂ)*(t:ℂ))*phase (-2*z) t) by ring, hg]
  simp only [Finset.mul_sum,Finset.sum_mul]

theorem mode_decay (kind : Bool) (θ : ℝ) (hθ : |θ| < Real.pi/2) (n : ℕ) (j : Fin 3) :
    |mode kind j*θ| < oddRate n := by
  have hn : 0 ≤ (n:ℝ)*Real.pi := mul_nonneg (Nat.cast_nonneg n) Real.pi_pos.le
  fin_cases j <;> cases kind <;> norm_num [mode,oddRate,abs_mul] <;> nlinarith [abs_nonneg θ]

def rationalPartial (kind : Bool) (θ z : ℝ) (N : ℕ) : ℂ :=
  ∑ j : Fin 3, (coefficient kind j:ℂ)*
    ∑ n ∈ Finset.range N, rationalPair (oddRate n) (mode kind j*θ) z

theorem damped_integral_eq (kind : Bool) (θ z : ℝ) (hθ : |θ| < Real.pi/2) (N : ℕ) :
    (∫ t in Ioi 0, (damping N t:ℂ)*pairedDerivative kind θ z t) =
      rationalPartial kind θ z N := by
  have he : (fun t => (damping N t:ℂ)*pairedDerivative kind θ z t) =ᵐ[volume.restrict (Ioi 0)]
      (fun t => ∑ j : Fin 3, (coefficient kind j:ℂ)*
        ∑ n ∈ Finset.range N, laplacePair (oddRate n) (mode kind j*θ) z t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [pairedDerivative_modes kind θ z t ht,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show (damping N t:ℂ)*((coefficient kind j:ℂ)*component (mode kind j*θ) z t) =
      (coefficient kind j:ℂ)*((damping N t:ℂ)*component (mode kind j*θ) z t) by ring,
      component_damped N _ z t ht]
  have hi (j : Fin 3) (n : ℕ) := laplacePair_integrable (oddRate n) (mode kind j*θ) z
    (mode_decay kind θ hθ n j)
  rw [integral_congr_ae he, integral_finset_sum Finset.univ
    (fun j _ => (integrable_finset_sum (Finset.range N) (fun n _ => hi j n)).const_mul _)]
  unfold rationalPartial
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul,integral_finset_sum (Finset.range N) (fun n _ => hi j n)]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  exact laplacePair_integral _ _ z (mode_decay kind θ hθ n j)

theorem rationalPartial_tendsto (kind : Bool) (θ z : ℝ) (hθ : |θ| < Real.pi/2) :
    Tendsto (rationalPartial kind θ z) atTop
      (𝓝 (∫ t in Ioi 0, pairedDerivative kind θ z t)) := by
  simpa only [damped_integral_eq kind θ z hθ] using damped_integral_tendsto kind θ z hθ

#print axioms damping_mem
#print axioms damping_tendsto
#print axioms damping_geometric
#print axioms damped_integral_tendsto
#print axioms laplacePair_integrable
#print axioms laplacePair_integral
#print axioms rationalPair_eq
#print axioms pairedDerivative_modes
#print axioms component_damped
#print axioms mode_decay
#print axioms damped_integral_eq
#print axioms rationalPartial_tendsto
end
end UnifiedTheory.Audit.KFCausalChargedCoolingLevyLaplace
