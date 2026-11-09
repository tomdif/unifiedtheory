/- Cross Plancherel and the weighted frequency-field symmetry on the
actual packet domains. These identities retain all interference and
justify cancellation of the adjacent-power imaginary shear term. -/
import UnifiedTheory.Audit.KFCausalNeutralFourierEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNeutralFourierPairing
noncomputable section
open MeasureTheory
open scoped FourierTransform ComplexConjugate
open KFCausalNeutralFourierField
open KFCausalL2FourierIntegral

theorem inner_toLp (f g : ℝ → ℂ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    inner ℂ (hf.toLp f) (hg.toLp g) = ∫ x, conj (f x)*g x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
  simp only [hx,hy,RCLike.inner_apply']

theorem cross_plancherel (f g : ℝ → ℂ) (hf1 : Integrable f) (hg1 : Integrable g)
    (hf2 : MemLp f 2 volume) (hg2 : MemLp g 2 volume) :
    (∫ k, conj ((𝓕 f) k)*(𝓕 g) k) = ∫ x, conj (f x)*g x := by
  rw [← inner_toLp _ _ (integralFourier_memLp f hf1 hf2) (integralFourier_memLp g hg1 hg2),
    ← fourier_toLp_eq f hf1 hf2,← fourier_toLp_eq g hg1 hg2,
    LinearIsometryEquiv.inner_map_map,inner_toLp]

variable (n : ℕ) (β : ℝ) (b c d : Fin n → ℂ) (P Q : Fin n → Polynomial ℂ)

def weightedCross (j l : ℕ) (a y k : ℝ) : ℂ :=
  (Real.exp (-4*Real.pi*k*y):ℂ)*
    (conj (spectrum n β b c P j ((a:ℂ)-(y:ℂ)*Complex.I) k)*
      spectrum n β b d Q l ((a:ℂ)-(y:ℂ)*Complex.I) k)

variable (hβ : 0 < β)
include hβ

theorem weightedCross_identity (j l : ℕ) (a y k : ℝ) :
    weightedCross n β b c d P Q j l a y k =
      conj ((𝓕 (fieldLine n β b c P j a y)) k)*(𝓕 (fieldLine n β b d Q l a y)) k := by
  rw [fieldLine_fourier n β hβ,fieldLine_fourier n β hβ]
  unfold weightedCross
  rw [map_mul,Complex.conj_ofReal]
  have he : (Real.exp (-2*Real.pi*k*y):ℂ)*(Real.exp (-2*Real.pi*k*y):ℂ) =
      (Real.exp (-4*Real.pi*k*y):ℂ) := by
    rw [← Complex.ofReal_mul,← Real.exp_add]
    congr 2
    ring
  rw [← he]
  ring

theorem weightedCross_integrable (j l : ℕ) (a y : ℝ) :
    Integrable (weightedCross n β b c d P Q j l a y) := by
  have hf := integralFourier_memLp _ (fieldLine_integrable n β hβ b c P j a y)
    (fieldLine_memLp n β hβ b c P j a y)
  have hg := integralFourier_memLp _ (fieldLine_integrable n β hβ b d Q l a y)
    (fieldLine_memLp n β hβ b d Q l a y)
  have hi := hf.star.integrable_mul hg
  change Integrable (fun k => weightedCross n β b c d P Q j l a y k)
  simpa only [weightedCross_identity n β b c d P Q hβ,Complex.star_def] using hi

theorem weightedCross_integral (j l : ℕ) (a y : ℝ) :
    (∫ k, weightedCross n β b c d P Q j l a y k) =
      ∫ x, conj (fieldLine n β b c P j a y x)*fieldLine n β b d Q l a y x := by
  simp_rw [weightedCross_identity n β b c d P Q hβ]
  exact cross_plancherel _ _ (fieldLine_integrable n β hβ b c P j a y)
    (fieldLine_integrable n β hβ b d Q l a y) (fieldLine_memLp n β hβ b c P j a y)
    (fieldLine_memLp n β hβ b d Q l a y)

omit hβ in
theorem fieldLine_succ (j : ℕ) (a y x : ℝ) :
    fieldLine n β b c P (j+1) a y x = ((x+a:ℝ):ℂ)*fieldLine n β b c P j a y x := by
  unfold fieldLine
  rw [pow_succ]
  ring

theorem weighted_field_symmetry (j l : ℕ) (a y : ℝ) :
    (∫ k, weightedCross n β b c d P Q j (l+1) a y k) =
      ∫ k, weightedCross n β b c d P Q (j+1) l a y k := by
  rw [weightedCross_integral n β b c d P Q hβ,weightedCross_integral n β b c d P Q hβ]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [fieldLine_succ,fieldLine_succ,map_mul,Complex.conj_ofReal]
  ring

omit d Q in
theorem same_profile_pairing_real (j l : ℕ) (a y : ℝ) :
    (∫ k, weightedCross n β b c c P P j l a y k).im = 0 := by
  rw [weightedCross_integral n β b c c P P hβ]
  have hi := (fieldLine_memLp n β hβ b c P j a y).star.integrable_mul
    (fieldLine_memLp n β hβ b c P l a y)
  change Integrable (fun x => conj (fieldLine n β b c P j a y x)*fieldLine n β b c P l a y x) at hi
  have him : (∫ x, (conj (fieldLine n β b c P j a y x)*fieldLine n β b c P l a y x).im) =
      (∫ x, conj (fieldLine n β b c P j a y x)*fieldLine n β b c P l a y x).im := integral_im hi
  rw [← him]
  have he (x : ℝ) : (conj (fieldLine n β b c P j a y x)*fieldLine n β b c P l a y x).im = 0 := by
    have hh : conj (fieldLine n β b c P j a y x)*fieldLine n β b c P l a y x =
        ((x+a:ℝ):ℂ)^(j+l)*(conj (KFCausalNeutralFourierShift.line n β b c P y x)*
          KFCausalNeutralFourierShift.line n β b c P y x) := by
      simp only [fieldLine,map_mul,map_pow,Complex.conj_ofReal,pow_add]
      ring
    rw [hh,Complex.conj_mul']
    simp only [← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.ofReal_im]
  simp only [he,integral_zero]

omit d Q in
theorem adjacent_pairing_real (j : ℕ) (a y : ℝ) :
    (∫ k, weightedCross n β b c c P P j (j+1) a y k).im = 0 :=
  same_profile_pairing_real n β b c P hβ j (j+1) a y

omit d Q in
theorem imaginary_shear_cancels (j : ℕ) (a y v : ℝ) :
    (∫ k, (-Complex.I*(v:ℂ))*weightedCross n β b c c P P j (j+1) a y k).re = 0 := by
  rw [integral_const_mul]
  simp only [Complex.mul_re,Complex.neg_re,Complex.I_re,neg_zero,Complex.ofReal_re,
    Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,neg_mul,
    adjacent_pairing_real n β b c P hβ,sub_self]

#print axioms inner_toLp
#print axioms cross_plancherel
#print axioms weightedCross_identity
#print axioms weightedCross_integrable
#print axioms weightedCross_integral
#print axioms fieldLine_succ
#print axioms weighted_field_symmetry
#print axioms same_profile_pairing_real
#print axioms adjacent_pairing_real
#print axioms imaginary_shear_cancels
end
end UnifiedTheory.Audit.KFCausalNeutralFourierPairing
