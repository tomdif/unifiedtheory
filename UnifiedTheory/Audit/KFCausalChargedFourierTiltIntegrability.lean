/- All charged polynomial moments of the actual Fourier density are
absolutely integrable. In particular the signed exponential-tilt response
has an integrable charged majorant before polar comparison is applied. -/
import UnifiedTheory.Audit.KFCausalJointFourierMomentMatrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalChargedFourierTiltIntegrability
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalChargedFourierGaussianMoments (Charged chargedMeasure density)
open KFCausalChargedFourierPolynomialGram (Index width family)
open KFCausalJointFourierQuadraticJet (jetSlice)
open KFCausalJointFourierMomentMatrix (source channelCoefficients)
open KFCausalReciprocalWedgeGeometry (gamma chart)

theorem density_power (S T c : ℂ) (m n : ℕ) (u v Y : ℝ) :
    (v:ℂ)^m*density S T c n u v Y = density S T c (m+n) u v Y := by
  simp only [KFCausalChargedFourierGaussianMoments.density_expansion,pow_add]
  ring

theorem family_moment_integrable (n : ℕ) (p : ℂ) (w : Fin n → ℝ) (c : ℝ)
    (a : Fin n → Fin 3 → ℂ) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (m : ℕ) :
    Integrable (fun x : Charged => x.1.2^m*‖family n p w c a x.1.1 x.1.2 x.2‖^2)
      chargedMeasure := by
  have hi : Integrable (fun x : Charged => ∑ I : Index n, ∑ J : Index n,
      (conj (a I.1 I.2)*a J.1 J.2)*
        density (width p (w I.1) (w J.1)) (conj (width p (w I.1) (w J.1)))
          (c:ℂ) (m+(I.2.val+J.2.val)) x.1.1 x.1.2 x.2) chargedMeasure := by
    apply integrable_finset_sum
    intro I _
    apply integrable_finset_sum
    intro J _
    have hS := KFCausalChargedFourierPolynomialGram.width_positive p (w I.1) (w J.1) hp (hw _) (hw _)
    exact (KFCausalChargedFourierGaussianMoments.density_integrable _ _ _ hS
      (by simpa only [Complex.conj_re] using hS) _).const_mul _
  have he (x : Charged) :
      ((x.1.2^m*‖family n p w c a x.1.1 x.1.2 x.2‖^2:ℝ):ℂ) =
        ∑ I : Index n, ∑ J : Index n, (conj (a I.1 I.2)*a J.1 J.2)*
          density (width p (w I.1) (w J.1)) (conj (width p (w I.1) (w J.1)))
            (c:ℂ) (m+(I.2.val+J.2.val)) x.1.1 x.1.2 x.2 := by
    rw [Complex.ofReal_mul,Complex.ofReal_pow,KFCausalChargedFourierPolynomialGram.family_square_complex]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I _
    apply Finset.sum_congr rfl
    intro J _
    rw [← density_power _ _ _ m (I.2.val+J.2.val)]
    ring
  have hc : Integrable (fun x : Charged =>
      ((x.1.2^m*‖family n p w c a x.1.1 x.1.2 x.2‖^2:ℝ):ℂ)) chargedMeasure :=
    hi.congr (Filter.Eventually.of_forall fun x => (he x).symm)
  simpa only [Complex.ofReal_re] using hc.re

variable (n : ℕ) (β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)

theorem slice_moment_integrable (α : ℝ) (r : ℂ) (k : ℝ)
    (hp : 0 < (gamma α r).re) (hw : ∀ i, 0 < w i) (m : ℕ) :
    Integrable (fun x : Charged => x.1.2^m*
      jetSlice n β w b c P r (chart α r (x.1.1^2+x.1.2^2) x.2) x.1.2 k) chargedMeasure := by
  simp only [KFCausalJointFourierMomentMatrix.slice_density,mul_add,← mul_div_assoc]
  have hi (h : Fin 3) := family_moment_integrable n (gamma α r) w (source r k)
    (channelCoefficients n β w b c P r k h) hp hw m
  exact ((hi 0).add ((hi 1).div_const 2)).add ((hi 2).div_const 4)

theorem tilt_integrable (α : ℝ) (r : ℂ) (k : ℝ)
    (hp : 0 < (gamma α r).re) (hw : ∀ i, 0 < w i) :
    Integrable (fun x : Charged => (-8*Real.pi*k*r.im*x.1.2)*
      jetSlice n β w b c P r (chart α r (x.1.1^2+x.1.2^2) x.2) x.1.2 k) chargedMeasure := by
  have hi := (slice_moment_integrable n β w b c P α r k hp hw 1).const_mul (-8*Real.pi*k*r.im)
  simpa only [pow_one,mul_assoc] using hi

#print axioms density_power
#print axioms family_moment_integrable
#print axioms slice_moment_integrable
#print axioms tilt_integrable
end
end UnifiedTheory.Audit.KFCausalChargedFourierTiltIntegrability
