/- Endpoint control of the actual paired charged cooling exponents.
The cancellation at zero is retained before integration. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingLevyTruncation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedCoolingLevyConvergence
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ComplexOrder
open KFCausalPositiveKernelExponential (phase)
open KFCausalChargedCoolingLevyTruncation

def paired (kind : Bool) (θ z t : ℝ) : ℂ :=
  (density kind (-θ) t:ℂ)*(phase (2*z) t-1)+
  (density kind θ t:ℂ)*(phase (-2*z) t-1)

theorem paired_hyperbolic (kind : Bool) (θ z t : ℝ) :
    paired kind θ z t =
      (((levyA kind (θ*t)*(Real.cos (2*z*t)-1):ℝ):ℂ)-
        ((levyB kind (θ*t)*Real.sin (2*z*t):ℝ):ℂ)*Complex.I)/
          ((t*Real.sinh (Real.pi*t):ℝ):ℂ) := by
  have hn : numerator kind (-θ*t) = levyA kind (θ*t)-levyB kind (θ*t) := by
    rw [show -θ*t = -(θ*t) by ring, reflected_numerator_hyperbolic]
  have hp (q : ℝ) : phase q t = (Real.cos (q*t):ℂ)+(Real.sin (q*t):ℂ)*Complex.I := by
    unfold phase
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [paired, density, hn, numerator_hyperbolic, hp,
    show -2*z*t = -(2*z*t) by ring, Real.cos_neg, Real.sin_neg,
    Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_neg, Complex.ofReal_ofNat, Complex.ofReal_one]
  ring

private theorem dslope_continuous (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    Continuous (dslope f 0) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t = 0
  · subst t
    exact continuousAt_dslope_same.mpr (hf 0)
  · exact (continuousAt_dslope_of_ne ht).mpr (hf t).continuousAt

private theorem mul_sinc (x : ℝ) : x*Real.sinc x = Real.sin x := by
  rw [Real.sinc_eq_dslope]
  simpa only [sub_zero, smul_eq_mul, Real.sin_zero] using sub_smul_dslope Real.sin 0 x

def oddSlope (kind : Bool) (θ t : ℝ) : ℝ := dslope (fun s => levyB kind (θ*s)) 0 t
def sinhSlope (t : ℝ) : ℝ := dslope (fun s => Real.sinh (Real.pi*s)) 0 t

private theorem odd_zero (kind : Bool) : levyB kind 0 = 0 := by
  cases kind <;> simp [levyB]

theorem oddSlope_identity (kind : Bool) (θ t : ℝ) :
    t*oddSlope kind θ t = levyB kind (θ*t) := by
  simpa only [oddSlope, sub_zero, smul_eq_mul, mul_zero, odd_zero] using
    sub_smul_dslope (fun s => levyB kind (θ*s)) 0 t

theorem sinhSlope_identity (t : ℝ) : t*sinhSlope t = Real.sinh (Real.pi*t) := by
  simpa only [sinhSlope, sub_zero, smul_eq_mul, mul_zero, Real.sinh_zero] using
    sub_smul_dslope (fun s => Real.sinh (Real.pi*s)) 0 t

theorem sinhSlope_positive (t : ℝ) (ht : 0 ≤ t) : 0 < sinhSlope t := by
  rcases ht.eq_or_lt with rfl | ht
  · have hd : HasDerivAt (fun s : ℝ => Real.sinh (Real.pi*s)) Real.pi 0 := by
      simpa using (Real.hasDerivAt_sinh (Real.pi*0)).comp 0
        ((hasDerivAt_id (0:ℝ)).const_mul Real.pi)
    simpa only [sinhSlope, dslope_same, hd.deriv] using Real.pi_pos
  · apply (mul_pos_iff_of_pos_left ht).mp
    rw [sinhSlope_identity]
    exact Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht)

def regularized (kind : Bool) (θ z t : ℝ) : ℂ :=
  (((-2*z^2*levyA kind (θ*t)*(Real.sinc (z*t))^2:ℝ):ℂ)-
    ((2*z*oddSlope kind θ t*Real.sinc (2*z*t):ℝ):ℂ)*Complex.I)/(sinhSlope t:ℂ)

theorem paired_regularized (kind : Bool) (θ z t : ℝ) (ht : 0 < t) :
    paired kind θ z t = regularized kind θ z t := by
  rw [paired_hyperbolic]
  have hc : Real.cos (2*z*t)-1 = -2*(Real.sin (z*t))^2 := by
    rw [show 2*z*t = 2*(z*t) by ring, Real.cos_two_mul']
    nlinarith [Real.sin_sq_add_cos_sq (z*t)]
  rw [hc, ← mul_sinc (z*t), ← mul_sinc (2*z*t),
    ← oddSlope_identity kind θ t, ← sinhSlope_identity t]
  unfold regularized
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_ofNat]
  field_simp [ne_of_gt ht, ne_of_gt (sinhSlope_positive t ht.le)]

theorem regularized_continuousOn (kind : Bool) (θ z : ℝ) :
    ContinuousOn (regularized kind θ z) (Ici 0) := by
  have ho : Continuous (oddSlope kind θ) :=
    dslope_continuous _ (by cases kind <;> unfold levyB <;> simp only [Bool.false_eq_true,
      if_false, if_true] <;> fun_prop)
  have hs : Continuous sinhSlope := dslope_continuous _ (by fun_prop)
  unfold regularized
  apply ContinuousOn.div
  · have ha : Continuous (fun t => levyA kind (θ*t)) := by
      cases kind <;> unfold levyA <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop
    fun_prop
  · exact Complex.continuous_ofReal.comp hs |>.continuousOn
  · intro t ht
    exact_mod_cast ne_of_gt (sinhSlope_positive t ht)

theorem paired_integrable_origin (kind : Bool) (θ z : ℝ) :
    IntegrableOn (paired kind θ z) (Ioc 0 1) := by
  have hr : IntegrableOn (regularized kind θ z) (Icc 0 1) :=
    ((regularized_continuousOn kind θ z).mono Icc_subset_Ici_self).integrableOn_Icc
  apply (hr.mono_set Ioc_subset_Icc_self).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact (paired_regularized kind θ z t ht.1).symm

theorem numerator_bound (kind : Bool) (θ t : ℝ) (ht : 0 ≤ t) :
    numerator kind (θ*t) ≤ (5/2)*Real.exp (2*|θ| *t) := by
  have hp : Real.exp (2*(θ*t)) ≤ Real.exp (2*|θ| *t) := by
    apply Real.exp_le_exp.mpr
    nlinarith [le_abs_self θ]
  have hm : Real.exp (-2*(θ*t)) ≤ Real.exp (2*|θ| *t) := by
    apply Real.exp_le_exp.mpr
    nlinarith [neg_abs_le θ]
  cases kind
  · simp only [numerator, Bool.false_eq_true, if_false, numeratorB]
    linarith [Real.exp_pos (θ*t), Real.exp_pos (2*|θ| *t)]
  · simp only [numerator, if_true, numeratorC]
    linarith [Real.exp_pos (-(θ*t))]

theorem sinh_tail_lower (t : ℝ) (ht : 1 ≤ t) :
    Real.exp (Real.pi*t) ≤ 4*Real.sinh (Real.pi*t) := by
  have hx : 1 ≤ Real.pi*t := by nlinarith [Real.two_le_pi]
  have he : 2 ≤ Real.exp (Real.pi*t) := by linarith [Real.add_one_le_exp (Real.pi*t)]
  have hi : Real.exp (-(Real.pi*t)) ≤ Real.exp (Real.pi*t)/2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    nlinarith
  rw [Real.sinh_eq]
  linarith

theorem density_tail_bound (kind : Bool) (θ t : ℝ) (ht : 1 ≤ t) :
    density kind θ t ≤ 5*Real.exp ((2*|θ|-Real.pi)*t) := by
  have ht0 : 0 < t := by linarith
  have hs : 0 < Real.sinh (Real.pi*t) := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht0)
  have hd : Real.exp (Real.pi*t)/2 ≤ 2*t*Real.sinh (Real.pi*t) := by
    nlinarith [sinh_tail_lower t ht]
  have he : Real.exp (2*|θ| *t) = Real.exp ((2*|θ|-Real.pi)*t)*Real.exp (Real.pi*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  apply (div_le_iff₀ (mul_pos (mul_pos (by norm_num) ht0) hs)).mpr
  have hb := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 5*Real.exp ((2*|θ|-Real.pi)*t))
  have hn := numerator_bound kind θ t ht0.le
  rw [he] at hn
  nlinarith

theorem density_integrable_tail (kind : Bool) (θ : ℝ) (hθ : |θ| < Real.pi/2) :
    IntegrableOn (density kind θ) (Ioi 1) := by
  have he : IntegrableOn (fun t : ℝ => 5*Real.exp ((2*|θ|-Real.pi)*t)) (Ioi 1) :=
    (integrableOn_exp_mul_Ioi (by linarith : 2*|θ|-Real.pi < 0) 1).const_mul 5
  have hc : ContinuousOn (density kind θ) (Ioi 1) :=
    (density_continuousOn kind θ).mono (by
      intro t ht
      change (0:ℝ) < t
      exact lt_trans zero_lt_one ht)
  apply he.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_pos (density_positive kind θ t (lt_trans zero_lt_one ht))]
  exact density_tail_bound kind θ t ht.le

private theorem phase_sub_bound (q t : ℝ) : ‖phase q t-1‖ ≤ 2 := by
  calc
    _ ≤ ‖phase q t‖+‖(1:ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [phase, Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num

theorem paired_integrable_tail (kind : Bool) (θ z : ℝ) (hθ : |θ| < Real.pi/2) :
    IntegrableOn (paired kind θ z) (Ioi 1) := by
  apply Integrable.add
  · exact (density_integrable_tail kind (-θ) (by simpa using hθ)).ofReal.mul_bdd
      (by unfold phase; fun_prop) (Filter.Eventually.of_forall (phase_sub_bound (2*z)))
  · exact (density_integrable_tail kind θ hθ).ofReal.mul_bdd
      (by unfold phase; fun_prop) (Filter.Eventually.of_forall (phase_sub_bound (-2*z)))

theorem paired_integrable (kind : Bool) (θ z : ℝ) (hθ : |θ| < Real.pi/2) :
    IntegrableOn (paired kind θ z) (Ioi 0) := by
  apply (integrableOn_union.mpr ⟨paired_integrable_origin kind θ z,
    paired_integrable_tail kind θ z hθ⟩).mono_set
  intro t ht
  by_cases ht1 : t ≤ 1
  · exact Or.inl ⟨ht,ht1⟩
  · exact Or.inr (lt_of_not_ge ht1)

/-- Increasing compact cutoffs remove both endpoints without separating the singular densities. -/
def cutoff (N : ℕ) : Set ℝ := Icc (1/((N:ℝ)+1)) ((N:ℝ)+1)

theorem cutoff_lower_positive (N : ℕ) : 0 < 1/((N:ℝ)+1) := by positivity

theorem cutoff_monotone : Monotone cutoff := by
  intro N M hNM t ht
  have hcast : (N:ℝ) ≤ M := Nat.cast_le.mpr hNM
  exact ⟨le_trans (one_div_le_one_div_of_le (by positivity) (by linarith)) ht.1,
    le_trans ht.2 (by linarith)⟩

theorem cutoff_union : (⋃ N : ℕ, cutoff N) = Ioi 0 := by
  ext t
  constructor
  · intro ht
    rcases mem_iUnion.mp ht with ⟨N,hN⟩
    exact lt_of_lt_of_le (cutoff_lower_positive N) hN.1
  · intro ht
    obtain ⟨N,hN⟩ := exists_nat_gt (max t (1/t))
    have ht0 : 0 < t := ht
    have hNt : t < (N:ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
    have hNi : 1/t < (N:ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
    have hprod : 1 < (N:ℝ)*t := (div_lt_iff₀ ht0).mp hNi
    apply mem_iUnion.mpr
    refine ⟨N, ?_, by change t ≤ (N:ℝ)+1; linarith⟩
    change 1/((N:ℝ)+1) ≤ t
    apply (div_le_iff₀ (by positivity : 0 < (N:ℝ)+1)).mpr
    nlinarith

theorem truncatedExponent_eq_paired (kind : Bool) (θ ε R z : ℝ) (hε : 0 < ε) :
    truncatedExponent kind θ ε R z = ∫ t in Icc ε R, paired kind θ z t := by
  have hp : IntegrableOn (fun t => (density kind (-θ) t:ℂ)*(phase (2*z) t-1))
      (Icc ε R) :=
    (density_integrableOn kind (-θ) ε R hε).ofReal.mul_bdd
      (by unfold phase; fun_prop) (Filter.Eventually.of_forall (phase_sub_bound (2*z)))
  have hm : IntegrableOn (fun t => (density kind θ t:ℂ)*(phase (-2*z) t-1))
      (Icc ε R) :=
    (density_integrableOn kind θ ε R hε).ofReal.mul_bdd
      (by unfold phase; fun_prop) (Filter.Eventually.of_forall (phase_sub_bound (-2*z)))
  exact (integral_add hp hm).symm

def fullExponent (kind : Bool) (θ z : ℝ) : ℂ := ∫ t in Ioi 0, paired kind θ z t

theorem truncatedExponent_tendsto (kind : Bool) (θ z : ℝ) (hθ : |θ| < Real.pi/2) :
    Tendsto (fun N : ℕ => truncatedExponent kind θ (1/((N:ℝ)+1)) ((N:ℝ)+1) z)
      atTop (𝓝 (fullExponent kind θ z)) := by
  have hi : IntegrableOn (paired kind θ z) (⋃ N, cutoff N) := by
    rw [cutoff_union]
    exact paired_integrable kind θ z hθ
  have h := tendsto_setIntegral_of_monotone (s := cutoff) (fun _ => measurableSet_Icc) cutoff_monotone hi
  rw [cutoff_union] at h
  convert h using 1
  funext N
  exact truncatedExponent_eq_paired kind θ _ _ z (cutoff_lower_positive N)

/-- The full B/C paired Lévy exponents yield positive kernels for the actual strip range.
No endpoint convergence or integrability hypothesis is required. -/
theorem full_kernel_positive {n : Type*} [Fintype n]
    (kind : Bool) (θ : ℝ) (hθ : |θ| < Real.pi/2) (x : n → ℝ) :
    Matrix.PosSemidef (fun i j => Complex.exp (fullExponent kind θ (x j-x i))) := by
  apply KFCausalPositiveKernelExponential.pointwise_limit_positive
    (A := fun N : ℕ => fun i j => Complex.exp
      (truncatedExponent kind θ (1/((N:ℝ)+1)) ((N:ℝ)+1) (x j-x i))) (l := atTop)
  · intro N
    exact truncated_kernel_positive kind θ _ _ (cutoff_lower_positive N) x
  · intro i j
    exact Complex.continuous_exp.continuousAt.tendsto.comp
      (truncatedExponent_tendsto kind θ (x j-x i) hθ)

#print axioms paired_hyperbolic
#print axioms oddSlope_identity
#print axioms sinhSlope_identity
#print axioms sinhSlope_positive
#print axioms paired_regularized
#print axioms regularized_continuousOn
#print axioms paired_integrable_origin
#print axioms numerator_bound
#print axioms sinh_tail_lower
#print axioms density_tail_bound
#print axioms density_integrable_tail
#print axioms paired_integrable_tail
#print axioms paired_integrable
#print axioms cutoff_lower_positive
#print axioms cutoff_monotone
#print axioms cutoff_union
#print axioms truncatedExponent_eq_paired
#print axioms truncatedExponent_tendsto
#print axioms full_kernel_positive
end
end UnifiedTheory.Audit.KFCausalChargedCoolingLevyConvergence
