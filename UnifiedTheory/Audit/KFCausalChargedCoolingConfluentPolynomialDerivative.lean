/- Direct integration of the actual degree-five charged cooling polynomial.
No differentiation under an integral or free-moment hypothesis is used. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingConfluentPolynomialMarginal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192

namespace UnifiedTheory.Audit.KFCausalChargedCoolingConfluentPolynomialDerivative
noncomputable section
open MeasureTheory
open scoped ComplexConjugate ComplexOrder
open KFCausalChargedCoolingGramIntegral (planeMeasure)
open KFCausalChargedCoolingConfluentMoments
open KFCausalChargedCoolingConfluentPolynomialMarginal
open KFCausalChargedCoolingConfluentThreeDissipation (fullDissipation)
open KFCausalShiftedComplexGaussianMoments (normalized)

def weightedCross (s : ℝ) (p : ℂ) (i j : ℕ) (m n : Fin 3) (q : ℝ × ℝ) : ℂ :=
  (q.1:ℂ)^(2*i)*(q.2:ℂ)^j*cross s p m n q

def weightedShifted (s : ℝ) (p z : ℂ) (i j : ℕ) (m n : Fin 3) (q : ℝ × ℝ) : ℂ :=
  (q.1:ℂ)^(2*i)*(q.2:ℂ)^j*shiftedCross s p z m n q

theorem weighted_cross_expansion (s : ℝ) (p : ℂ) (i j : ℕ) (m n : Fin 3) (q : ℝ × ℝ) :
    weightedCross s p i j m n q =
      ∑ k ∈ Finset.range (m.val+1), ∑ l ∈ Finset.range (n.val+1),
        coefficient p m.val n.val k l*monomial s (i+k+l) (j+(m.val-k)+(n.val-l)) q := by
  unfold weightedCross
  rw [cross_expansion]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  simp only [monomial,show 2*(i+k+l)=2*i+2*(k+l) by omega,
    show j+(m.val-k)+(n.val-l)=j+((m.val-k)+(n.val-l)) by omega,pow_add]
  ring

theorem weighted_cross_integrable (s : ℝ) (hs : 0 < s) (p : ℂ)
    (i j : ℕ) (m n : Fin 3) : Integrable (weightedCross s p i j m n) planeMeasure := by
  change Integrable (fun q => weightedCross s p i j m n q) planeMeasure
  simp_rw [weighted_cross_expansion]
  exact integrable_finset_sum _ (fun k _ => integrable_finset_sum _ (fun l _ =>
    (monomial_integrable s hs _ _).const_mul _))

theorem weighted_cross_integral (s : ℝ) (hs : 0 < s) (p : ℂ) (i j : ℕ) (m n : Fin 3) :
    (∫ q, weightedCross s p i j m n q ∂planeMeasure) =
      ∑ k ∈ Finset.range (m.val+1), ∑ l ∈ Finset.range (n.val+1),
        coefficient p m.val n.val k l*
          (KFCausalComplexGaussianMoments.gaussianValue (s:ℂ)*normalized (s:ℂ) 0 (2*(i+k+l))*
            (((j+(m.val-k)+(n.val-l)).factorial:ℂ)/(s:ℂ)^(j+(m.val-k)+(n.val-l)+1))) := by
  simp_rw [weighted_cross_expansion]
  rw [integral_finset_sum _ (fun k _ => integrable_finset_sum _ (fun l _ =>
    (monomial_integrable s hs _ _).const_mul _))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_finset_sum _ (fun l _ => (monomial_integrable s hs _ _).const_mul _)]
  apply Finset.sum_congr rfl
  intro l hl
  rw [integral_const_mul,monomial_integral s hs]

theorem weighted_shifted_expansion (s : ℝ) (p z : ℂ) (i j : ℕ) (m n : Fin 3) (q : ℝ × ℝ) :
    weightedShifted s p z i j m n q =
      ∑ k : Fin 3, ∑ l : Fin 3,
        (translation z m k*conj (translation z n l))*weightedCross s p i j k l q := by
  unfold weightedShifted
  rw [shifted_cross_expansion]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  unfold weightedCross
  ring

theorem weighted_shifted_integrable (s : ℝ) (hs : 0 < s) (p z : ℂ)
    (i j : ℕ) (m n : Fin 3) : Integrable (weightedShifted s p z i j m n) planeMeasure := by
  change Integrable (fun q => weightedShifted s p z i j m n q) planeMeasure
  simp_rw [weighted_shifted_expansion]
  exact integrable_finset_sum _ (fun k _ => integrable_finset_sum _ (fun l _ =>
    (weighted_cross_integrable s hs p i j k l).const_mul _))

theorem weighted_shifted_integral (s : ℝ) (hs : 0 < s) (p z : ℂ) (i j : ℕ) (m n : Fin 3) :
    (∫ q, weightedShifted s p z i j m n q ∂planeMeasure) =
      ∑ k : Fin 3, ∑ l : Fin 3,
        (translation z m k*conj (translation z n l))*
          (∑ a ∈ Finset.range (k.val+1), ∑ b ∈ Finset.range (l.val+1),
            coefficient p k.val l.val a b*
              (KFCausalComplexGaussianMoments.gaussianValue (s:ℂ)*normalized (s:ℂ) 0 (2*(i+a+b))*
                (((j+(k.val-a)+(l.val-b)).factorial:ℂ)/(s:ℂ)^(j+(k.val-a)+(l.val-b)+1)))) := by
  simp_rw [weighted_shifted_expansion]
  rw [integral_finset_sum _ (fun k _ => integrable_finset_sum _ (fun l _ =>
    (weighted_cross_integrable s hs p i j k l).const_mul _))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_finset_sum _ (fun l _ => (weighted_cross_integrable s hs p i j k l).const_mul _)]
  apply Finset.sum_congr rfl
  intro l hl
  rw [integral_const_mul,weighted_cross_integral s hs]

def normalizedCooling (s x y v : ℝ) (z : ℂ) (q : ℝ × ℝ) : ℂ :=
  let p := (s:ℂ)*halfParameter x
  2*(weightedShifted s p z 1 0 2 2 q+weightedShifted s p z 0 1 2 2 q+
      (v:ℂ)^2*weightedShifted s p z 0 0 2 2 q)-
    2*(1+(y:ℂ)*Complex.I)*(weightedShifted s p z 1 0 1 2 q+
      (v:ℂ)^2*weightedShifted s p z 0 0 1 2 q)-
    2*(1-(y:ℂ)*Complex.I)*weightedShifted s p z 0 1 1 2 q-
    2*(1-(y:ℂ)*Complex.I)*(weightedShifted s p z 1 0 2 1 q+
      (v:ℂ)^2*weightedShifted s p z 0 0 2 1 q)-
    2*(1+(y:ℂ)*Complex.I)*weightedShifted s p z 0 1 2 1 q

theorem normalized_cooling_integrable (s x y v : ℝ) (hs : 0 < s) (z : ℂ) :
    Integrable (normalizedCooling s x y v z) planeMeasure := by
  unfold normalizedCooling
  exact (((((weighted_shifted_integrable s hs _ z 1 0 2 2).add
    (weighted_shifted_integrable s hs _ z 0 1 2 2)).add
      ((weighted_shifted_integrable s hs _ z 0 0 2 2).const_mul _)).const_mul _).sub
        (((weighted_shifted_integrable s hs _ z 1 0 1 2).add
          ((weighted_shifted_integrable s hs _ z 0 0 1 2).const_mul _)).const_mul _)).sub
        ((weighted_shifted_integrable s hs _ z 0 1 1 2).const_mul _) |>.sub
        (((weighted_shifted_integrable s hs _ z 1 0 2 1).add
          ((weighted_shifted_integrable s hs _ z 0 0 2 1).const_mul _)).const_mul _) |>.sub
        ((weighted_shifted_integrable s hs _ z 0 1 2 1).const_mul _)

def gramDerivative (x : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  KFCausalChargedCoolingConfluentThreeCoercivity.hermitianThree 0 (7*x/2)
    (321*x^3/4+441*x/16) (Complex.I/2)
    ((-7*x/2:ℝ)+(5/4:ℝ)*Complex.I)
    ((49*x/8:ℝ)+(81*x^2/8+35/32:ℝ)*Complex.I)

def rawDissipation (x y v s : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fullDissipation x y v s+((x*(1-y^2)-y)/s:ℝ) • gramDerivative x

theorem normalized_cooling_integral_raw (s x y v : ℝ) (hs : 0 < s) (z : ℂ) :
    (∫ q, normalizedCooling s x y v z q ∂planeMeasure) =
      (KFCausalComplexGaussianMoments.gaussianValue (s:ℂ)/(s:ℂ))*
        (translation z*rawDissipation x y v s*(translation z).conjTranspose) 2 2 := by
  have hi := weighted_shifted_integrable s hs ((s:ℂ)*halfParameter x) z
  have hs0 : (s:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  dsimp only [normalizedCooling]
  have h1 := (((hi 1 0 2 2).add (hi 0 1 2 2)).add ((hi 0 0 2 2).const_mul ((v:ℂ)^2))).const_mul (2:ℂ)
  have h2 := ((hi 1 0 1 2).add ((hi 0 0 1 2).const_mul ((v:ℂ)^2))).const_mul (2*(1+(y:ℂ)*Complex.I))
  have h3 := (hi 0 1 1 2).const_mul (2*(1-(y:ℂ)*Complex.I))
  have h4 := ((hi 1 0 2 1).add ((hi 0 0 2 1).const_mul ((v:ℂ)^2))).const_mul (2*(1-(y:ℂ)*Complex.I))
  have h5 := (hi 0 1 2 1).const_mul (2*(1+(y:ℂ)*Complex.I))
  have e5 := integral_sub (((h1.sub h2).sub h3).sub h4) h5
  have e4 := integral_sub ((h1.sub h2).sub h3) h4
  have e3 := integral_sub (h1.sub h2) h3
  have e2 := integral_sub h1 h2
  simp only [Pi.add_apply,Pi.sub_apply] at e5 e4 e3 e2
  rw [e5,e4,e3,e2]
  simp only [integral_const_mul]
  have a1 := integral_add ((hi 1 0 2 2).add (hi 0 1 2 2)) ((hi 0 0 2 2).const_mul ((v:ℂ)^2))
  have a2 := integral_add (hi 1 0 2 2) (hi 0 1 2 2)
  have a3 := integral_add (hi 1 0 1 2) ((hi 0 0 1 2).const_mul ((v:ℂ)^2))
  have a4 := integral_add (hi 1 0 2 1) ((hi 0 0 2 1).const_mul ((v:ℂ)^2))
  simp only [Pi.add_apply] at a1 a2 a3 a4
  rw [a1,a2,a3,a4]
  simp only [integral_const_mul]
  simp_rw [weighted_shifted_integral s hs]
  norm_num [Fin.sum_univ_three,translation,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,
    Finset.sum_range_succ,coefficient,halfParameter,normalized,
    rawDissipation,gramDerivative,fullDissipation,KFCausalChargedCoolingConfluentThreeDissipation.remainder,
    KFCausalChargedCoolingConfluentThreeDissipation.d1,
    KFCausalChargedCoolingConfluentThreeDissipation.d2,
    KFCausalChargedCoolingConfluentThreeDissipation.z01,
    KFCausalChargedCoolingConfluentThreeDissipation.z02,
    KFCausalChargedCoolingConfluentThreeDissipation.z12,
    KFCausalChargedCoolingConfluentThreeCoercivity.cooling,
    KFCausalChargedCoolingConfluentThreeCoercivity.hermitianThree,
    Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.add_apply,Matrix.smul_apply,
    Complex.star_def,Complex.real_smul,map_add,map_mul,map_pow,map_div₀,
    Complex.conj_ofReal,Complex.conj_I]
  field_simp [hs0]
  ring_nf
  norm_num [Complex.I_sq,Complex.I_pow_three,Complex.I_pow_four,map_ofNat]
  ring_nf

theorem normalized_cooling_integral (s y v : ℝ) (hs : 0 < s) (hy : |y| < 1) (z : ℂ) :
    (∫ q, normalizedCooling s (y/(1-y^2)) y v z q ∂planeMeasure) =
      (KFCausalComplexGaussianMoments.gaussianValue (s:ℂ)/(s:ℂ))*
        (translation z*fullDissipation (y/(1-y^2)) y v s*(translation z).conjTranspose) 2 2 := by
  have hd : 1-y^2 ≠ 0 := by have h := (sq_lt_one_iff_abs_lt_one y).mpr hy; linarith
  rw [normalized_cooling_integral_raw s (y/(1-y^2)) y v hs z]
  simp only [rawDissipation,div_mul_cancel₀ _ hd,sub_self,zero_div,zero_smul,add_zero]

theorem gaussian_mass_real (s : ℝ) (hs : 0 < s) :
    KFCausalComplexGaussianMoments.gaussianValue (s:ℂ)/(s:ℂ) =
      ((Real.sqrt Real.pi/(Real.sqrt s*s):ℝ):ℂ) := by
  rw [KFCausalChargedCoolingGramIntegral.gaussianValue_split (s:ℂ) (by simpa using hs)]
  have h : (s:ℂ)^(1/2:ℂ) = (Real.sqrt s:ℂ) := by
    rw [show (1/2:ℂ)=((1/2:ℝ):ℂ) by norm_num,
      ← Complex.ofReal_cpow hs.le,← Real.sqrt_eq_rpow]
  rw [h]
  push_cast
  ring

theorem normalized_cooling_lower (s y v : ℝ) (hs : 0 < s) (hy : |y| < 1) (z : ℂ) :
    (v^2/16)*(∫ q, quadraticDensity s ((s:ℂ)*halfParameter (y/(1-y^2))) z q ∂planeMeasure) ≤
      ∫ q, (normalizedCooling s (y/(1-y^2)) y v z q).re ∂planeMeasure := by
  have h := (KFCausalChargedCoolingConfluentThreeDissipation.congruent_coercivity
    y v s hy hs (translation z)).diag_nonneg (i := 2)
  have hr := (Complex.nonneg_iff.mp h).1
  simp only [Matrix.sub_apply,Matrix.smul_apply,Complex.real_smul,Complex.sub_re,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hr
  rw [quadratic_density_integral s _ hs z,gaussian_mass_real s hs]
  change _ ≤ ∫ q, RCLike.re (normalizedCooling s (y/(1-y^2)) y v z q) ∂planeMeasure
  rw [integral_re (normalized_cooling_integrable s _ y v hs z),
    normalized_cooling_integral s y v hs hy z,gaussian_mass_real s hs]
  change _ ≤ (((Real.sqrt Real.pi/(Real.sqrt s*s):ℝ):ℂ)*_).re
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hm : 0 ≤ Real.sqrt Real.pi/(Real.sqrt s*s) := by positivity
  nlinarith only [mul_nonneg hm hr]

#print axioms weighted_cross_expansion
#print axioms weighted_cross_integrable
#print axioms weighted_cross_integral
#print axioms weighted_shifted_expansion
#print axioms weighted_shifted_integrable
#print axioms weighted_shifted_integral
#print axioms normalized_cooling_integrable
#print axioms normalized_cooling_integral_raw
#print axioms normalized_cooling_integral
#print axioms gaussian_mass_real
#print axioms normalized_cooling_lower
end
end UnifiedTheory.Audit.KFCausalChargedCoolingConfluentPolynomialDerivative
