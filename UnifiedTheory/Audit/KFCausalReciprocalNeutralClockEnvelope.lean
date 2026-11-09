/- Clock regularity and common transverse L2 bounds for the actual
reciprocal neutral factors. The bound may depend on the packet and degree;
it is a domination theorem, not the missing uniform response estimate. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralSliceIntegrability
import UnifiedTheory.Audit.KFCausalPolynomialKernelJointContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralClockEnvelope
noncomputable section
open MeasureTheory
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalReciprocalSqueezeFlow (squeeze squeezeEquiv)
open KFCausalReciprocalNeutralSliceIntegrability (factor factor_squeeze squeeze_volume)
open KFCausalReciprocalNeutralPackets (rescaledPolynomial)
open KFCausalNeutralExponentialProfiles (neutralSource exponentialProfile_factor)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalPolynomialOrbitEnvelope (clockSlope)

def curve (ε y α β w : ℝ) (b : ℂ) (P : Polynomial ℂ) (n : ℕ)
    (s : ℝ) (q : Transverse) : ℂ := factor α β w (scale ε y s) b P n q

def slope (ε y α β w : ℝ) (b : ℂ) (P : Polynomial ℂ) (n : ℕ)
    (s : ℝ) (q : Transverse) : ℂ := deriv (fun t => curve ε y α β w b P n t q) s

theorem squeeze_real_memLp (t : ℝ) (f : Transverse → ℝ) (hf : MemLp f 2 volume) :
    MemLp (fun q => f (squeeze t q)) 2 volume := by
  have hm : MemLp f 2 (Measure.map (squeeze t) volume) := by
    rw [squeeze_volume]
    exact hf.smul_measure (by finiteness)
  exact hm.comp_of_map (squeezeEquiv t).toContinuousLinearEquiv.continuous.measurable.aemeasurable

theorem curve_squeeze (ε y α β t : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (n : ℕ) (s : ℝ) (q : Transverse) :
    curve ε y α β (Real.exp (2*t)) b P n s q =
      ((Real.exp t:ℂ)^n)⁻¹ * KFCausalPolynomialOrbitEnvelope.factor ε y α
        (β*Real.exp (-2*t)) (neutralSource ((Real.exp (-t):ℂ)*b)) 1
        (rescaledPolynomial t P) pointField n (squeeze t q) s := by
  rw [← exponentialProfile_factor, factor_squeeze]
  exact (inv_mul_cancel_left₀
    (pow_ne_zero n (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t))) _).symm

private theorem squeezed_derivative (ε y α β t : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (n : ℕ) (s : ℝ) (q : Transverse) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    HasDerivAt (fun v => curve ε y α β (Real.exp (2*t)) b P n v q)
      (((Real.exp t:ℂ)^n)⁻¹ * KFCausalPolynomialOrbitEnvelope.factorDerivative ε y α
        (β*Real.exp (-2*t)) (neutralSource ((Real.exp (-t):ℂ)*b)) 1
        (rescaledPolynomial t P) pointField n (squeeze t q) s) s := by
  simpa only [curve_squeeze] using
    (KFCausalPolynomialOrbitEnvelope.factor_derivative ε y α (β*Real.exp (-2*t))
      (neutralSource ((Real.exp (-t):ℂ)*b)) 1 (rescaledPolynomial t P) pointField n
      (squeeze t q) s hε hy).const_mul ((Real.exp t:ℂ)^n)⁻¹

theorem slope_squeeze (ε y α β t : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (n : ℕ) (s : ℝ) (q : Transverse) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    slope ε y α β (Real.exp (2*t)) b P n s q =
      ((Real.exp t:ℂ)^n)⁻¹ * KFCausalPolynomialOrbitEnvelope.factorDerivative ε y α
        (β*Real.exp (-2*t)) (neutralSource ((Real.exp (-t):ℂ)*b)) 1
        (rescaledPolynomial t P) pointField n (squeeze t q) s :=
  (squeezed_derivative ε y α β t b P n s q hε hy).deriv

theorem curve_derivative (ε y α β w : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (n : ℕ) (s : ℝ) (q : Transverse) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (hw : 0 < w) :
    HasDerivAt (fun v => curve ε y α β w b P n v q) (slope ε y α β w b P n s q) s := by
  have he : Real.exp (2*(Real.log w/2)) = w := by rw [mul_div_cancel₀ _ (by norm_num), Real.exp_log hw]
  have hd := squeezed_derivative ε y α β (Real.log w/2) b P n s q hε hy
  rw [he] at hd
  exact hd.differentiableAt.hasDerivAt

theorem curve_continuous (ε y α β w : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (n : ℕ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hw : 0 < w) :
    Continuous (fun x : ℝ × Transverse => curve ε y α β w b P n x.1 x.2) := by
  let t := Real.log w/2
  have he : Real.exp (2*t) = w := by dsimp [t]; rw [mul_div_cancel₀ _ (by norm_num), Real.exp_log hw]
  rw [← he]
  simp_rw [curve_squeeze]
  exact continuous_const.mul (KFCausalPolynomialKernelJointContinuity.factor_continuous
    ε y α (β*Real.exp (-2*t)) hε hy Prod.fst (fun x => squeeze t x.2)
    (fun _ => neutralSource ((Real.exp (-t):ℂ)*b)) (fun _ => 1)
    continuous_fst ((squeezeEquiv t).toContinuousLinearEquiv.continuous.comp continuous_snd)
    continuous_const continuous_const (rescaledPolynomial t P) pointField n)

theorem slope_continuous (ε y α β w : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (n : ℕ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hw : 0 < w) :
    Continuous (fun x : ℝ × Transverse => slope ε y α β w b P n x.1 x.2) := by
  let t := Real.log w/2
  have he : Real.exp (2*t) = w := by dsimp [t]; rw [mul_div_cancel₀ _ (by norm_num), Real.exp_log hw]
  rw [← he]
  simp_rw [slope_squeeze ε y α β t b P n _ _ hε hy]
  exact continuous_const.mul (KFCausalPolynomialKernelJointContinuity.factorDerivative_continuous
    ε y α (β*Real.exp (-2*t)) hε hy Prod.fst (fun x => squeeze t x.2)
    (fun _ => neutralSource ((Real.exp (-t):ℂ)*b)) (fun _ => 1)
    continuous_fst ((squeezeEquiv t).toContinuousLinearEquiv.continuous.comp continuous_snd)
    continuous_const continuous_const (rescaledPolynomial t P) pointField n)

theorem common_envelope (ε y α β w : ℝ) (b : ℂ) (P : Polynomial ℂ) (n : ℕ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hα : 0 < α) (hβ : 0 < β)
    (hwidth : 32*β ≤ α) (hw : 1 ≤ w) :
    ∃ D : Transverse → ℝ, Continuous D ∧ MemLp D 2 volume ∧
      (∀ q, 0 ≤ D q) ∧ ∀ s q,
        ‖curve ε y α β w b P n s q‖ ≤ D q ∧
        ‖slope ε y α β w b P n s q‖ ≤ ‖clockSlope ε y s‖*D q := by
  let t := Real.log w/2
  have ht : 0 ≤ t := div_nonneg (Real.log_nonneg hw) (by norm_num)
  have he : Real.exp (2*t) = w := by
    dsimp [t]; rw [mul_div_cancel₀ _ (by norm_num), Real.exp_log (by linarith)]
  have hβ' : 0 < β*Real.exp (-2*t) := mul_pos hβ (Real.exp_pos _)
  have hwidth' : 32*(β*Real.exp (-2*t)) ≤ α := by
    have hb := mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (by linarith : -2*t ≤ 0)) hβ.le
    nlinarith
  let d := neutralSource ((Real.exp (-t):ℂ)*b)
  let Q := rescaledPolynomial t P
  let A := KFCausalPolynomialOrbitEnvelope.amplitudeEnvelope ε y α (β*Real.exp (-2*t)) d Q pointField n
  let B := KFCausalPolynomialOrbitEnvelope.correctionEnvelope ε y α (β*Real.exp (-2*t)) d Q pointField n
  let k := ‖((Real.exp t:ℂ)^n)⁻¹‖
  have hA := KFCausalPolynomialOrbitEnvelope.amplitudeEnvelope_nonnegative ε y α (β*Real.exp (-2*t)) d Q pointField n
  have hB := KFCausalPolynomialOrbitEnvelope.correctionEnvelope_nonnegative ε y α (β*Real.exp (-2*t)) d Q pointField n
  have hs := (squeezeEquiv t).toContinuousLinearEquiv.continuous
  refine ⟨fun q => k*(A (squeeze t q)+B (squeeze t q)), ?_, ?_, ?_, ?_⟩
  · exact continuous_const.mul
      (((KFCausalPolynomialOrbitEnvelope.amplitudeEnvelope_continuous ε y α (β*Real.exp (-2*t)) d Q pointField n).comp hs).add
        ((KFCausalPolynomialOrbitEnvelope.correctionEnvelope_continuous ε y α (β*Real.exp (-2*t)) d Q pointField n).comp hs))
  · exact ((squeeze_real_memLp t A (KFCausalPolynomialOrbitEnvelope.amplitudeEnvelope_memLp
        ε y α (β*Real.exp (-2*t)) hα hβ' d Q pointField n)).add
      (squeeze_real_memLp t B (KFCausalPolynomialOrbitEnvelope.correctionEnvelope_memLp
        ε y α (β*Real.exp (-2*t)) hα hβ' d Q pointField n))).const_mul k
  · intro q
    exact mul_nonneg (norm_nonneg _) (add_nonneg (hA _) (hB _))
  · intro s q
    rw [← he, curve_squeeze, slope_squeeze ε y α β t b P n s q hε hy]
    simp only [norm_mul]
    have ha := KFCausalPolynomialOrbitEnvelope.factor_bound ε y α (β*Real.exp (-2*t))
      hε hy hα hβ' hwidth' d d le_rfl 1 (by simp) Q pointField n (squeeze t q) s
    have hb := KFCausalPolynomialOrbitEnvelope.factorDerivative_bound ε y α (β*Real.exp (-2*t))
      hε hy hα hβ' hwidth' d d le_rfl 1 (by simp) Q pointField n (squeeze t q) s
    constructor
    · exact mul_le_mul_of_nonneg_left (ha.trans (le_add_of_nonneg_right (hB _))) (norm_nonneg _)
    · calc
        _ ≤ k*(‖clockSlope ε y s‖*B (squeeze t q)) := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ ≤ k*(‖clockSlope ε y s‖*(A (squeeze t q)+B (squeeze t q))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_left (hA _)) (norm_nonneg _)) (norm_nonneg _)
        _ = _ := by ring

#print axioms squeeze_real_memLp
#print axioms curve_squeeze
#print axioms slope_squeeze
#print axioms curve_derivative
#print axioms curve_continuous
#print axioms slope_continuous
#print axioms common_envelope
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralClockEnvelope
