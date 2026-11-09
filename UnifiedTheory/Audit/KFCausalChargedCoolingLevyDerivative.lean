/- Differentiating the actual paired charged cooling exponent with endpoint domination. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingLevyConvergence
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedCoolingLevyDerivative
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
open KFCausalPositiveKernelExponential (phase)
open KFCausalChargedCoolingLevyTruncation
open KFCausalChargedCoolingLevyConvergence

def pairedDerivative (kind : Bool) (θ z t : ℝ) : ℂ :=
  ((2*t:ℝ):ℂ)*Complex.I*((density kind (-θ) t:ℂ)*phase (2*z) t-
    (density kind θ t:ℂ)*phase (-2*z) t)

theorem paired_hasDerivAt (kind : Bool) (θ z t : ℝ) :
    HasDerivAt (fun x => paired kind θ x t) (pairedDerivative kind θ z t) z := by
  have hp := ((((hasDerivAt_id z).const_mul 2).mul_const t).ofReal_comp.mul_const Complex.I).cexp
  have hm := ((((hasDerivAt_id z).const_mul (-2)).mul_const t).ofReal_comp.mul_const Complex.I).cexp
  convert ((hp.sub_const 1).const_mul (density kind (-θ) t:ℂ)).add
    ((hm.sub_const 1).const_mul (density kind θ t:ℂ)) using 1
  dsimp [pairedDerivative, phase]
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat, mul_one]
  ring

theorem pairedDerivative_hyperbolic (kind : Bool) (θ z t : ℝ) :
    pairedDerivative kind θ z t =
      (((-2*levyA kind (θ*t)*Real.sin (2*z*t):ℝ):ℂ)-
        ((2*levyB kind (θ*t)*Real.cos (2*z*t):ℝ):ℂ)*Complex.I)/
          (Real.sinh (Real.pi*t):ℂ) := by
  have hn : numerator kind (-θ*t) = levyA kind (θ*t)-levyB kind (θ*t) := by
    rw [show -θ*t = -(θ*t) by ring, reflected_numerator_hyperbolic]
  have hp (q : ℝ) : phase q t = (Real.cos (q*t):ℂ)+(Real.sin (q*t):ℂ)*Complex.I := by
    unfold phase
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  by_cases ht : t = 0
  · subst t
    simp [pairedDerivative, levyB]
  · unfold pairedDerivative
    rw [density, density, hn, numerator_hyperbolic]
    simp only [hp, show -2*z*t = -(2*z*t) by ring, Real.cos_neg, Real.sin_neg,
      Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add,
      Complex.ofReal_neg, Complex.ofReal_ofNat]
    have hs : Real.sinh (Real.pi*t) ≠ 0 := by
      rw [Real.sinh_ne_zero]
      exact mul_ne_zero Real.pi_ne_zero ht
    field_simp [ht, hs]
    ring_nf
    simp only [Complex.I_sq]
    ring

def regularizedDerivative (kind : Bool) (θ z t : ℝ) : ℂ :=
  (((-4*z*levyA kind (θ*t)*Real.sinc (2*z*t):ℝ):ℂ)-
    ((2*oddSlope kind θ t*Real.cos (2*z*t):ℝ):ℂ)*Complex.I)/(sinhSlope t:ℂ)

private theorem mul_sinc (x : ℝ) : x*Real.sinc x = Real.sin x := by
  rw [Real.sinc_eq_dslope]
  simpa only [sub_zero, smul_eq_mul, Real.sin_zero] using sub_smul_dslope Real.sin 0 x

theorem pairedDerivative_regularized (kind : Bool) (θ z t : ℝ) (ht : 0 < t) :
    pairedDerivative kind θ z t = regularizedDerivative kind θ z t := by
  rw [pairedDerivative_hyperbolic, ← mul_sinc (2*z*t),
    ← oddSlope_identity kind θ t, ← sinhSlope_identity t]
  unfold regularizedDerivative
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
  field_simp [ne_of_gt ht, ne_of_gt (sinhSlope_positive t ht.le)]
  ring

private theorem dslope_continuous (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    Continuous (dslope f 0) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t = 0
  · subst t
    exact continuousAt_dslope_same.mpr (hf 0)
  · exact (continuousAt_dslope_of_ne ht).mpr (hf t).continuousAt

theorem regularizedDerivative_continuousOn (kind : Bool) (θ : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => regularizedDerivative kind θ p.1 p.2)
      (univ ×ˢ Ici 0) := by
  have ho : Continuous (oddSlope kind θ) :=
    dslope_continuous _ (by cases kind <;> unfold levyB <;> simp only [Bool.false_eq_true,
      if_false, if_true] <;> fun_prop)
  have hs : Continuous sinhSlope := dslope_continuous _ (by fun_prop)
  have ha : Continuous (fun t => levyA kind (θ*t)) := by
    cases kind <;> unfold levyA <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop
  unfold regularizedDerivative
  apply ContinuousOn.div
  · have hap : Continuous (fun p : ℝ × ℝ => levyA kind (θ*p.2)) := ha.comp continuous_snd
    have hop : Continuous (fun p : ℝ × ℝ => oddSlope kind θ p.2) := ho.comp continuous_snd
    exact (show Continuous (fun p : ℝ × ℝ =>
      ((-4*p.1*levyA kind (θ*p.2)*Real.sinc (2*p.1*p.2):ℝ):ℂ)-
      ((2*oddSlope kind θ p.2*Real.cos (2*p.1*p.2):ℝ):ℂ)*Complex.I) by fun_prop).continuousOn
  · exact (Complex.continuous_ofReal.comp (hs.comp continuous_snd)).continuousOn
  · intro p hp
    exact_mod_cast ne_of_gt (sinhSlope_positive p.2 hp.2)

theorem density_moment_tail_bound (kind : Bool) (θ t : ℝ) (ht : 1 ≤ t) :
    t*density kind θ t ≤ 5*Real.exp ((2*|θ|-Real.pi)*t) := by
  have ht0 : 0 < t := by linarith
  have hs : 0 < Real.sinh (Real.pi*t) := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht0)
  have hd : Real.exp (Real.pi*t)/2 ≤ 2*Real.sinh (Real.pi*t) := by
    linarith [sinh_tail_lower t ht]
  have he : Real.exp (2*|θ| *t) = Real.exp ((2*|θ|-Real.pi)*t)*Real.exp (Real.pi*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hid : t*density kind θ t = numerator kind (θ*t)/(2*Real.sinh (Real.pi*t)) := by
    unfold density
    field_simp [ne_of_gt ht0, ne_of_gt hs]
  rw [hid]
  apply (div_le_iff₀ (mul_pos (by norm_num) hs)).mpr
  have hb := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 5*Real.exp ((2*|θ|-Real.pi)*t))
  have hn := numerator_bound kind θ t ht0.le
  rw [he] at hn
  nlinarith

theorem pairedDerivative_tail_bound (kind : Bool) (θ z t : ℝ) (ht : 1 ≤ t) :
    ‖pairedDerivative kind θ z t‖ ≤ 20*Real.exp ((2*|θ|-Real.pi)*t) := by
  have ht0 : 0 < t := by linarith
  have hn := density_moment_tail_bound kind (-θ) t ht
  have hp := density_moment_tail_bound kind θ t ht
  rw [abs_neg] at hn
  have hnorm (q : ℝ) : ‖phase q t‖ = 1 := by
    rw [phase, Complex.norm_exp_ofReal_mul_I]
  unfold pairedDerivative
  calc
    _ = (2*t)*‖(density kind (-θ) t:ℂ)*phase (2*z) t-
        (density kind θ t:ℂ)*phase (-2*z) t‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < 2*t), Complex.norm_I, mul_one]
    _ ≤ (2*t)*(density kind (-θ) t+density kind θ t) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (norm_sub_le _ _).trans (by
        simp only [norm_mul, hnorm, Complex.norm_real, Real.norm_eq_abs, mul_one,
          abs_of_pos (density_positive kind (-θ) t ht0),
          abs_of_pos (density_positive kind θ t ht0)]
        exact le_rfl)
    _ ≤ _ := by nlinarith

theorem pairedDerivative_continuousOn (kind : Bool) (θ z : ℝ) :
    ContinuousOn (pairedDerivative kind θ z) (Ioi 0) := by
  have hr : ContinuousOn (regularizedDerivative kind θ z) (Ici 0) :=
    (regularizedDerivative_continuousOn kind θ).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨mem_univ z,ht⟩)
  apply (hr.mono Ioi_subset_Ici_self).congr
  intro t ht
  exact pairedDerivative_regularized kind θ z t ht

/-- One integrable envelope controls the derivative for every real argument in a neighborhood.
The compact piece uses the continuous extension; the tail retains the strip's exponential gap. -/
theorem pairedDerivative_local_envelope (kind : Bool) (θ z : ℝ)
    (hθ : |θ| < Real.pi/2) :
    ∃ B : ℝ → ℝ, Integrable B ∧
      ∀ t ∈ Ioi 0, ∀ x ∈ Icc (z-1) (z+1), ‖pairedDerivative kind θ x t‖ ≤ B t := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => regularizedDerivative kind θ p.1 p.2)
      (Icc (z-1) (z+1) ×ˢ Icc 0 1) :=
    (regularizedDerivative_continuousOn kind θ).mono
      (fun p hp => ⟨mem_univ p.1,hp.2.1⟩)
  obtain ⟨C,hC⟩ := ((isCompact_Icc : IsCompact (Icc (z-1) (z+1))).prod
    (isCompact_Icc : IsCompact (Icc (0:ℝ) 1))).exists_bound_of_continuousOn hc
  let B₀ : ℝ → ℝ := (Ioc 0 1).indicator (fun _ => C)
  let B₁ : ℝ → ℝ := (Ioi 1).indicator (fun t => 20*Real.exp ((2*|θ|-Real.pi)*t))
  have hi₀ : Integrable B₀ :=
    ((continuous_const.integrableOn_Icc : IntegrableOn (fun _ : ℝ => C) (Icc 0 1)).mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
  have hi₁ : Integrable B₁ := by
    dsimp [B₁]
    rw [integrable_indicator_iff measurableSet_Ioi]
    exact (integrableOn_exp_mul_Ioi (by linarith : 2*|θ|-Real.pi < 0) 1).const_mul 20
  refine ⟨fun t => B₀ t+B₁ t, hi₀.add hi₁, ?_⟩
  intro t ht x hx
  by_cases ht1 : t ≤ 1
  · have hmem : t ∈ Ioc (0:ℝ) 1 := ⟨ht,ht1⟩
    have hnmem : t ∉ Ioi (1:ℝ) := not_lt.mpr ht1
    simp only [B₀,B₁,indicator_of_mem hmem,indicator_of_notMem hnmem,add_zero]
    rw [pairedDerivative_regularized kind θ x t ht]
    exact hC (x,t) ⟨hx,ht.le,ht1⟩
  · have hmem : t ∈ Ioi (1:ℝ) := lt_of_not_ge ht1
    have hnmem : t ∉ Ioc (0:ℝ) 1 := fun h => ht1 h.2
    simp only [B₀,B₁,indicator_of_notMem hnmem,indicator_of_mem hmem,zero_add]
    exact pairedDerivative_tail_bound kind θ x t hmem.le

/-- Differentiation of the full actual B/C exponent, with all endpoint and local domination
conditions derived from the strict strip range. -/
theorem fullExponent_differentiation (kind : Bool) (θ z : ℝ) (hθ : |θ| < Real.pi/2) :
    IntegrableOn (pairedDerivative kind θ z) (Ioi 0) ∧
      HasDerivAt (fullExponent kind θ) (∫ t in Ioi 0, pairedDerivative kind θ z t) z := by
  obtain ⟨B,hB,hbound⟩ := pairedDerivative_local_envelope kind θ z hθ
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := paired kind θ) (F' := pairedDerivative kind θ) (μ := volume.restrict (Ioi 0))
    (bound := B) (s := Icc (z-1) (z+1))
    (Icc_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall (fun x => (paired_integrable kind θ x hθ).1))
    (paired_integrable kind θ z hθ)
    ((pairedDerivative_continuousOn kind θ z).aestronglyMeasurable measurableSet_Ioi)
    ?_ hB.integrableOn ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hbound t ht
  · exact Eventually.of_forall (fun t x _ => paired_hasDerivAt kind θ x t)

#print axioms paired_hasDerivAt
#print axioms pairedDerivative_hyperbolic
#print axioms pairedDerivative_regularized
#print axioms regularizedDerivative_continuousOn
#print axioms density_moment_tail_bound
#print axioms pairedDerivative_tail_bound
#print axioms pairedDerivative_continuousOn
#print axioms pairedDerivative_local_envelope
#print axioms fullExponent_differentiation
end
end UnifiedTheory.Audit.KFCausalChargedCoolingLevyDerivative
