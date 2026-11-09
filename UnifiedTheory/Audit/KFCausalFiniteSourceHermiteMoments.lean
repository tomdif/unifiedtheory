/- Hermite uncertainty for a finite correlated sum of neutral sources.
The covariant integration by parts is applied to the complete summed
profile; no cross-source term is discarded or estimated separately. -/
import UnifiedTheory.Audit.KFCausalSingleWidthHermiteMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalFiniteSourceHermiteMoments
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalNeutralLinePackets (packet step)
open KFCausalNeutralLineDomain
open KFCausalSingleWidthHermiteMoments (gaussianMass variance slope covariantStep)

def profile (n : ℕ) (β : ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ) (ξ : ℝ) : ℂ :=
  ∑ i, c i*packet β (b i) (P i) ξ

def polyStep {n : ℕ} (β : ℝ) (b : Fin n → ℂ) (P : Fin n → Polynomial ℂ) : Fin n → Polynomial ℂ :=
  fun i => step β (b i) (P i)

def covariant {n : ℕ} (β : ℝ) (b : Fin n → ℂ) (d : ℝ)
    (P : Fin n → Polynomial ℂ) : Fin n → Polynomial ℂ :=
  fun i => covariantStep β (b i) d (P i)

theorem profile_regular (n : ℕ) (β : ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
    (hβ : 0 < β) : Regular (profile n β b c P) :=
  regular_sum n _ (fun i => regular_const_mul _ (packet_regular β hβ (b i) (P i)) (c i))

theorem profile_derivative (n : ℕ) (β : ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (ξ : ℝ) :
    HasDerivAt (profile n β b c P) (profile n β b c (polyStep β b P) ξ) ξ :=
  HasDerivAt.fun_sum (fun i _ => (KFCausalNeutralLinePackets.packet_derivative β (b i) (P i) ξ).const_mul (c i))

theorem covariant_one (n : ℕ) (β d : ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (ξ : ℝ) :
    profile n β b c (covariant β b d P) ξ =
      Complex.I*profile n β b c (polyStep β b P) ξ-
        (d:ℂ)*(ξ:ℂ)*profile n β b c P ξ := by
  simp only [profile,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [covariant,polyStep,packet,KFCausalNeutralLinePackets.entire,covariantStep,
    Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  ring

theorem covariant_two (n : ℕ) (β d : ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (ξ : ℝ) :
    profile n β b c (covariant β b d (covariant β b d P)) ξ =
      -profile n β b c (polyStep β b (polyStep β b P)) ξ-
        2*Complex.I*(d:ℂ)*(ξ:ℂ)*profile n β b c (polyStep β b P) ξ-
        Complex.I*(d:ℂ)*profile n β b c P ξ+
        (d:ℂ)^2*(ξ:ℂ)^2*profile n β b c P ξ := by
  simp only [profile,Finset.mul_sum,← Finset.sum_neg_distrib,
    ← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [covariant,polyStep,packet,KFCausalNeutralLinePackets.entire,covariantStep,
    step,Polynomial.derivative_add,Polynomial.derivative_sub,Polynomial.derivative_mul,
    Polynomial.derivative_C,Polynomial.derivative_X,Polynomial.eval_add,
    Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
    Polynomial.eval_zero,Polynomial.eval_one]
  ring_nf
  simp [Complex.I_sq]
  ring

private theorem cross_integrable (n : ℕ) (β : ℝ) (b c : Fin n → ℂ)
    (P Q : Fin n → Polynomial ℂ) (hβ : 0 < β) :
    Integrable (fun ξ => conj (profile n β b c P ξ)*profile n β b c Q ξ) := by
  simpa only [Polynomial.eval_one,one_mul] using polynomial_cross_integrable _ _
    (profile_regular n β b c P hβ) (profile_regular n β b c Q hβ) 1

private theorem norm_integrable (n : ℕ) (β : ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (hβ : 0 < β) :
    Integrable (fun ξ => ‖profile n β b c P ξ‖^2) := by
  have hp := regular_memLp _ (profile_regular n β b c P hβ)
  exact (memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mp hp

theorem covariant_symmetric (n : ℕ) (β d : ℝ) (b c : Fin n → ℂ)
    (P Q : Fin n → Polynomial ℂ) (hβ : 0 < β) :
    (∫ ξ, conj (profile n β b c P ξ)*profile n β b c (covariant β b d Q) ξ) =
      ∫ ξ, conj (profile n β b c (covariant β b d P) ξ)*profile n β b c Q ξ := by
  have hi := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun ξ => (profile_derivative n β b c P ξ).star)
    (profile_derivative n β b c Q)
    (cross_integrable n β b c P (polyStep β b Q) hβ)
    (cross_integrable n β b c (polyStep β b P) Q hβ)
    (cross_integrable n β b c P Q hβ)
  have hk : Integrable (fun ξ : ℝ => (ξ:ℂ)*
      (conj (profile n β b c P ξ)*profile n β b c Q ξ)) := by
    simpa only [Polynomial.eval_X] using polynomial_cross_integrable _ _
      (profile_regular n β b c P hβ) (profile_regular n β b c Q hβ) Polynomial.X
  have hl (ξ : ℝ) : conj (profile n β b c P ξ)*profile n β b c (covariant β b d Q) ξ =
      Complex.I*(conj (profile n β b c P ξ)*profile n β b c (polyStep β b Q) ξ)-
        (d:ℂ)*((ξ:ℂ)*(conj (profile n β b c P ξ)*profile n β b c Q ξ)) := by
    rw [covariant_one]
    ring
  have hr (ξ : ℝ) : conj (profile n β b c (covariant β b d P) ξ)*profile n β b c Q ξ =
      -Complex.I*(conj (profile n β b c (polyStep β b P) ξ)*profile n β b c Q ξ)-
        (d:ℂ)*((ξ:ℂ)*(conj (profile n β b c P ξ)*profile n β b c Q ξ)) := by
    rw [covariant_one]
    simp only [map_sub,map_mul,Complex.conj_I,Complex.conj_ofReal]
    ring
  simp_rw [hl,hr]
  rw [integral_sub ((cross_integrable n β b c P (polyStep β b Q) hβ).const_mul Complex.I)
      (hk.const_mul (d:ℂ)),
    integral_sub ((cross_integrable n β b c (polyStep β b P) Q hβ).const_mul (-Complex.I))
      (hk.const_mul (d:ℂ))]
  simp only [integral_const_mul]
  change (∫ ξ, conj (profile n β b c P ξ)*profile n β b c (polyStep β b Q) ξ) =
    -(∫ ξ, conj (profile n β b c (polyStep β b P) ξ)*profile n β b c Q ξ) at hi
  rw [hi]
  ring

def firstEnergy (n : ℕ) (h L η β : ℝ) (b c : Fin n → ℂ) (d : ℝ)
    (P : Fin n → Polynomial ℂ) : ℝ :=
  ∫ ξ, ∫ t : ℝ, Real.exp (-h*t^2)*
    ‖profile n β b c (covariant β b d P) ξ+slope L η*(t:ℂ)*profile n β b c P ξ‖^2

def secondEnergy (n : ℕ) (h L η β : ℝ) (b c : Fin n → ℂ) (d : ℝ)
    (P : Fin n → Polynomial ℂ) : ℝ :=
  ∫ ξ, ∫ t : ℝ, Real.exp (-h*t^2)*
    ‖profile n β b c (covariant β b d (covariant β b d P)) ξ+
      (variance h L η:ℂ)*profile n β b c P ξ+
      2*slope L η*(t:ℂ)*profile n β b c (covariant β b d P) ξ+
      (slope L η)^2*((t:ℂ)^2-(1/(2*h):ℝ))*profile n β b c P ξ‖^2

theorem first_identity (n : ℕ) (h L η β : ℝ) (b c : Fin n → ℂ) (d : ℝ)
    (P : Fin n → Polynomial ℂ) (hh : 0 < h) (hβ : 0 < β) :
    firstEnergy n h L η β b c d P = gaussianMass h*
      ((∫ ξ, ‖profile n β b c (covariant β b d P) ξ‖^2)+
        variance h L η*(∫ ξ, ‖profile n β b c P ξ‖^2)) := by
  unfold firstEnergy
  simp_rw [KFCausalSingleWidthHermiteMoments.first_channel_integral h L η hh]
  rw [integral_const_mul,integral_add (norm_integrable n β b c _ hβ)
    ((norm_integrable n β b c P hβ).const_mul (variance h L η)),integral_const_mul]

theorem second_identity (n : ℕ) (h L η β : ℝ) (b c : Fin n → ℂ) (d : ℝ)
    (P : Fin n → Polynomial ℂ) (hh : 0 < h) (hβ : 0 < β) :
    secondEnergy n h L η β b c d P = gaussianMass h*
      ((∫ ξ, ‖profile n β b c (covariant β b d (covariant β b d P)) ξ‖^2)+
        6*variance h L η*(∫ ξ, ‖profile n β b c (covariant β b d P) ξ‖^2)+
        3*(variance h L η)^2*(∫ ξ, ‖profile n β b c P ξ‖^2)) := by
  let Q := covariant β b d P
  let R := covariant β b d Q
  have hs := covariant_symmetric n β d b c P Q hβ
  have hsre : (∫ ξ, (conj (profile n β b c P ξ)*profile n β b c R ξ).re) =
      ∫ ξ, ‖profile n β b c Q ξ‖^2 := by
    have hr : (∫ ξ, conj (profile n β b c P ξ)*profile n β b c R ξ).re =
        ∫ ξ, (conj (profile n β b c P ξ)*profile n β b c R ξ).re :=
      (integral_re (cross_integrable n β b c P R hβ)).symm
    rw [← hr]
    change (∫ ξ, conj (profile n β b c P ξ)*profile n β b c (covariant β b d Q) ξ).re = _
    rw [hs]
    have hi := integral_re (cross_integrable n β b c Q Q hβ)
    simpa only [Q,Complex.conj_mul',← Complex.ofReal_pow,Complex.ofReal_re] using hi.symm
  have he (ξ : ℝ) : ‖profile n β b c R ξ+(variance h L η:ℂ)*profile n β b c P ξ‖^2 =
      ‖profile n β b c R ξ‖^2+2*variance h L η*(conj (profile n β b c P ξ)*profile n β b c R ξ).re+
        (variance h L η)^2*‖profile n β b c P ξ‖^2 := by
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.conj_re,Complex.conj_im]
    ring
  unfold secondEnergy
  simp_rw [KFCausalSingleWidthHermiteMoments.second_channel_integral h L η hh]
  change (∫ ξ, gaussianMass h*(‖profile n β b c R ξ+(variance h L η:ℂ)*profile n β b c P ξ‖^2+
    4*variance h L η*‖profile n β b c Q ξ‖^2+2*(variance h L η)^2*‖profile n β b c P ξ‖^2)) = _
  simp_rw [he]
  have hi0 := norm_integrable n β b c P hβ
  have hi1 := norm_integrable n β b c Q hβ
  have hi2 := norm_integrable n β b c R hβ
  have hix : Integrable (fun ξ => (conj (profile n β b c P ξ)*profile n β b c R ξ).re) :=
    (cross_integrable n β b c P R hβ).re
  have hs1 := integral_add hi2 (hix.const_mul (2*variance h L η))
  have hs2 := integral_add (hi2.add (hix.const_mul (2*variance h L η)))
    (hi0.const_mul ((variance h L η)^2))
  have hs3 := integral_add ((hi2.add (hix.const_mul (2*variance h L η))).add
    (hi0.const_mul ((variance h L η)^2))) (hi1.const_mul (4*variance h L η))
  have hs4 := integral_add (((hi2.add (hix.const_mul (2*variance h L η))).add
    (hi0.const_mul ((variance h L η)^2))).add (hi1.const_mul (4*variance h L η)))
    (hi0.const_mul (2*(variance h L η)^2))
  simp only [Pi.add_apply] at hs1 hs2 hs3 hs4
  rw [integral_const_mul,hs4,hs3,hs2,hs1]
  simp only [integral_const_mul,hsre]
  dsimp only [Q,R]
  ring

theorem second_lower (n : ℕ) (h L η β : ℝ) (b c : Fin n → ℂ) (d : ℝ)
    (P : Fin n → Polynomial ℂ) (hh : 0 < h) (hβ : 0 < β) :
    3*variance h L η*firstEnergy n h L η β b c d P ≤ secondEnergy n h L η β b c d P := by
  rw [first_identity n h L η β b c d P hh hβ,second_identity n h L η β b c d P hh hβ]
  have h0 : 0 ≤ gaussianMass h := Real.sqrt_nonneg _
  have hv : 0 ≤ variance h L η := by unfold variance; positivity
  have h1 : 0 ≤ ∫ ξ, ‖profile n β b c (covariant β b d P) ξ‖^2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have h2 : 0 ≤ ∫ ξ, ‖profile n β b c (covariant β b d (covariant β b d P)) ξ‖^2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  nlinarith [mul_nonneg h0 h2,mul_nonneg h0 (mul_nonneg hv h1)]

#print axioms profile_regular
#print axioms profile_derivative
#print axioms covariant_one
#print axioms covariant_two
#print axioms covariant_symmetric
#print axioms first_identity
#print axioms second_identity
#print axioms second_lower
end
end UnifiedTheory.Audit.KFCausalFiniteSourceHermiteMoments
