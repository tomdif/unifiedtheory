/- The nonnegative Gaussian series is attached to the actual coherent
charged packet norm. Integrability is derived from the strict charged
width margin, before the series and integral are interchanged. -/
import UnifiedTheory.Audit.KFCausalChargedEvenMomentMonotonicity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedGaussianMomentSeries
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ComplexConjugate
open KFCausalChargedEvenMomentFamily (packet energy)
open KFCausalChargedFourierGaussianMoments (Charged chargedMeasure density)
open KFCausalShiftedComplexGaussianMoments (moment)
open KFCausalChargedCoolingWidthPositive (widthSum)
open KFCausalChargedCoolingFixedV (widthSum_re)

variable {ι : Type*} [Fintype ι]

def weightedEnergy (m : ℕ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ) : ℝ :=
  ∫ x : Charged, Real.exp (d*x.1.2^2)*‖packet m p w c x‖^2 ∂chargedMeasure

theorem packet_add (m n : ℕ) (p : ℂ) (w : ι → ℝ) (c : ι → ℂ) (x : Charged) :
    packet (m+n) p w c x = (x.1.2:ℂ)^n*packet m p w c x := by
  simp only [KFCausalChargedEvenMomentFamily.packet_expansion,pow_add]
  ring

theorem packet_norm_add (m n : ℕ) (p : ℂ) (w : ι → ℝ) (c : ι → ℂ) (x : Charged) :
    ‖packet (m+n) p w c x‖^2 = (x.1.2^2)^n*‖packet m p w c x‖^2 := by
  rw [packet_add,norm_mul,mul_pow,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    ← pow_mul,mul_comm n 2,pow_mul,sq_abs]

private def tiltedDensity (S T : ℂ) (d : ℝ) (n : ℕ) (x : Charged) : ℂ :=
  moment S 0 0 x.1.1*moment (S-(d:ℂ)) 0 n x.1.2*Complex.exp (-T*(x.2:ℂ))

private theorem tiltedDensity_eq (S T : ℂ) (d : ℝ) (n : ℕ) (x : Charged) :
    tiltedDensity S T d n x =
      (Real.exp (d*x.1.2^2):ℂ)*density S T 0 n x.1.1 x.1.2 x.2 := by
  have he : moment (S-(d:ℂ)) 0 n x.1.2 =
      (Real.exp (d*x.1.2^2):ℂ)*moment S 0 n x.1.2 := by
    unfold moment
    simp only [zero_mul,add_zero]
    rw [show -(S-(d:ℂ))*(x.1.2:ℂ)^2 = (d:ℂ)*(x.1.2:ℂ)^2-S*(x.1.2:ℂ)^2 by ring,
      Complex.exp_sub]
    rw [show (d:ℂ)*(x.1.2:ℂ)^2=((d*x.1.2^2:ℝ):ℂ) by push_cast; rfl,
      ← Complex.ofReal_exp]
    rw [neg_mul,Complex.exp_neg]
    ring
  unfold tiltedDensity density
  rw [he]
  ring

private theorem tiltedDensity_integrable (S T : ℂ) (d : ℝ) (n : ℕ)
    (hS : 0 < S.re) (hT : 0 < T.re) (hV : 0 < (S-(d:ℂ)).re) :
    Integrable (tiltedDensity S T d n) chargedMeasure := by
  exact ((KFCausalShiftedComplexGaussianMoments.moment_integrable S 0 hS 0).mul_prod
    (KFCausalShiftedComplexGaussianMoments.moment_integrable (S-(d:ℂ)) 0 hV n)).mul_prod
    (KFCausalReciprocalWedgeLaplace.laplace_integrable T hT)

theorem weighted_square_integrable (m : ℕ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i) :
    Integrable (fun x : Charged => Real.exp (d*x.1.2^2)*‖packet m p w c x‖^2) chargedMeasure := by
  have hc (i j : ι) : Integrable (fun x => (c i*conj (c j))*
      tiltedDensity (widthSum p (w i) (w j)) (widthSum (conj p) (w i) (w j)) d (2*m) x)
      chargedMeasure := by
    have hS : 0 < (widthSum p (w i) (w j)).re := by
      rw [widthSum_re]; exact mul_pos hp (add_pos (hw i) (hw j))
    have hT : 0 < (widthSum (conj p) (w i) (w j)).re := by
      rw [widthSum_re,Complex.conj_re]; exact mul_pos hp (add_pos (hw i) (hw j))
    have hV : 0 < (widthSum p (w i) (w j)-(d:ℂ)).re := by
      rw [Complex.sub_re,Complex.ofReal_re,widthSum_re]
      nlinarith [hd i,hd j]
    exact (tiltedDensity_integrable _ _ d (2*m) hS hT hV).const_mul _
  have hi := integrable_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => hc i j))
  have he (x : Charged) : ((Real.exp (d*x.1.2^2)*‖packet m p w c x‖^2:ℝ):ℂ) =
      ∑ i, ∑ j, (c i*conj (c j))*
        tiltedDensity (widthSum p (w i) (w j)) (widthSum (conj p) (w i) (w j)) d (2*m) x := by
    rw [Complex.ofReal_mul,KFCausalChargedEvenMomentFamily.packet_square]
    simp only [Finset.mul_sum,tiltedDensity_eq]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi' : Integrable (fun x : Charged =>
      ((Real.exp (d*x.1.2^2)*‖packet m p w c x‖^2:ℝ):ℂ)) chargedMeasure :=
    hi.congr (Eventually.of_forall (fun x => (he x).symm))
  simpa only [Complex.ofReal_re] using hi'.re

theorem pointwise_series (m : ℕ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ) (x : Charged) :
    HasSum (fun n : ℕ => d^n/(n.factorial:ℝ)*‖packet (m+n) p w c x‖^2)
      (Real.exp (d*x.1.2^2)*‖packet m p w c x‖^2) := by
  have h : HasSum (fun n : ℕ => (d*x.1.2^2)^n/(n.factorial:ℝ)) (Real.exp (d*x.1.2^2)) := by
    simpa only [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (d*x.1.2^2)
  convert h.mul_right (‖packet m p w c x‖^2) using 1
  funext n
  rw [packet_norm_add,mul_pow]
  ring

theorem moment_series (m : ℕ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd0 : 0 ≤ d) (hd : ∀ i, d < 2*p.re*w i) :
    HasSum (fun n : ℕ => d^n/(n.factorial:ℝ)*energy (m+n) p w c)
      (weightedEnergy m p d w c) := by
  let f : ℕ → Charged → ℝ := fun n x => d^n/(n.factorial:ℝ)*‖packet (m+n) p w c x‖^2
  have hi (n : ℕ) : Integrable (f n) chargedMeasure := by
    have h := (KFCausalChargedEvenMomentFamily.packet_square_integrable (m+n) p w c hp hw).re
    simpa only [f,Complex.ofReal_re] using h.const_mul (d^n/(n.factorial:ℝ))
  have hn (n : ℕ) (x : Charged) : 0 ≤ f n x := by dsimp [f]; positivity
  have hs (x : Charged) : HasSum (fun n => f n x)
      (Real.exp (d*x.1.2^2)*‖packet m p w c x‖^2) := pointwise_series m p d w c x
  have hb : Integrable (fun x : Charged => ∑' n, f n x) chargedMeasure :=
    (weighted_square_integrable m p d w c hp hw hd).congr
      (Eventually.of_forall (fun x => (hs x).tsum_eq.symm))
  have h := hasSum_integral_of_dominated_convergence f (fun n => (hi n).aestronglyMeasurable)
    (fun n => Eventually.of_forall (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hn n x)]))
    (Eventually.of_forall (fun x => (hs x).summable)) hb (Eventually.of_forall hs)
  simpa only [f,integral_const_mul,energy,weightedEnergy] using h

theorem actual_scaled_series (α a β b : ℝ) (hα : 0 < α) (hβ : 0 ≤ β)
    (hb : 0 < b) (hba : b < a) (m : ℕ) (w : ι → ℝ) (hw : ∀ i, 0 < w i) (c : ι → ℂ)
    (hd : ∀ i, 8*β*b^2 < α*(a^2-b^2)*w i) :
    HasSum (fun n : ℕ => (8*β)^n/(n.factorial:ℝ)*b^(2*n+2)*
      KFCausalChargedEvenMomentMonotonicity.lineEnergy α a (m+n) w c b)
      (b^2*weightedEnergy m (KFCausalChargedEvenMomentImaginaryBound.gamma α
        ((a:ℂ)+Complex.I*(b:ℂ))) (8*β*b^2) w c) := by
  let p := KFCausalChargedEvenMomentImaginaryBound.gamma α ((a:ℂ)+Complex.I*(b:ℂ))
  have hp : 0 < p.re := KFCausalChargedCoolingFixedV.actual_gamma_re_positive α _ hα
    (by simpa [abs_of_pos hb] using hba)
  have hre : p.re = α*(a^2-b^2)/2 := by
    simp [p,KFCausalChargedEvenMomentImaginaryBound.gamma,pow_two,Complex.mul_re,Complex.mul_im]
  have hd' : ∀ i, 8*β*b^2 < 2*p.re*w i := by intro i; rw [hre]; nlinarith [hd i]
  have h := (moment_series m p (8*β*b^2) w c hp hw (by positivity) hd').mul_left (b^2)
  convert h using 1
  funext n
  unfold KFCausalChargedEvenMomentMonotonicity.lineEnergy
  dsimp only [p]
  simp only [mul_pow,pow_add,← pow_mul]
  ring

theorem actual_scaled_le (α a β b₁ b₂ : ℝ) (hα : 0 < α) (hβ : 0 ≤ β)
    (hb₁ : 0 < b₁) (hb : b₁ ≤ b₂) (hb₂ : b₂ < a) (m : ℕ) (hm : m ≤ 2)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (c : ι → ℂ)
    (hd : ∀ i, 8*β*b₂^2 < α*(a^2-b₂^2)*w i) :
    b₁^2*weightedEnergy m (KFCausalChargedEvenMomentImaginaryBound.gamma α
        ((a:ℂ)+Complex.I*(b₁:ℂ))) (8*β*b₁^2) w c ≤
    b₂^2*weightedEnergy m (KFCausalChargedEvenMomentImaginaryBound.gamma α
        ((a:ℂ)+Complex.I*(b₂:ℂ))) (8*β*b₂^2) w c := by
  have hpos₂ := lt_of_lt_of_le hb₁ hb
  have hba₁ := lt_of_le_of_lt hb hb₂
  have hs : b₁^2 ≤ b₂^2 := by nlinarith
  have hd₁ : ∀ i, 8*β*b₁^2 < α*(a^2-b₁^2)*w i := by
    intro i
    have hwi := hw i
    have hp : 0 ≤ (8*β+α*w i)*(b₂^2-b₁^2) := mul_nonneg (by positivity) (sub_nonneg.mpr hs)
    nlinarith [hd i]
  apply hasSum_le _ (actual_scaled_series α a β b₁ hα hβ hb₁ hba₁ m w hw c hd₁)
    (actual_scaled_series α a β b₂ hα hβ hpos₂ hb₂ m w hw c hd)
  intro n
  have hmom := KFCausalChargedEvenMomentMonotonicity.scaled_monotone α a hα m n hm w hw c
    ⟨hb₁,hba₁⟩ ⟨hpos₂,hb₂⟩ hb
  have hc : 0 ≤ (8*β)^n/(n.factorial:ℝ) := by positivity
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmom hc

#print axioms packet_add
#print axioms packet_norm_add
#print axioms weighted_square_integrable
#print axioms pointwise_series
#print axioms moment_series
#print axioms actual_scaled_series
#print axioms actual_scaled_le
end
end UnifiedTheory.Audit.KFCausalChargedGaussianMomentSeries
