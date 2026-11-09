/- Positive Gaussian-cosh moment series for the actual coherent charged
packet. Arbitrary linear tilt preserves integrability under the strict
quadratic width margin. The double series retains every cross-width term,
and its actual b-scaling is monotone for the three quartic channels. -/
import UnifiedTheory.Audit.KFCausalChargedGaussianMomentSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedCoshGaussianMomentSeries
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ComplexConjugate
open KFCausalChargedEvenMomentFamily (packet energy)
open KFCausalChargedFourierGaussianMoments (Charged chargedMeasure density)
open KFCausalShiftedComplexGaussianMoments (moment)
open KFCausalChargedCoolingWidthPositive (widthSum)
open KFCausalChargedCoolingFixedV (widthSum_re)
open KFCausalChargedGaussianMomentSeries (packet_norm_add)

variable {ι : Type*} [Fintype ι]

def weightedEnergy (m : ℕ) (p : ℂ) (d q : ℝ) (w : ι → ℝ) (c : ι → ℂ) : ℝ :=
  ∫ x : Charged, Real.exp (d*x.1.2^2)*Real.cosh (q*x.1.2)*‖packet m p w c x‖^2 ∂chargedMeasure

private def tiltedDensity (S T : ℂ) (d q : ℝ) (n : ℕ) (x : Charged) : ℂ :=
  moment S 0 0 x.1.1*moment (S-(d:ℂ)) (q:ℂ) n x.1.2*Complex.exp (-T*(x.2:ℂ))

private theorem tiltedDensity_eq (S T : ℂ) (d q : ℝ) (n : ℕ) (x : Charged) :
    tiltedDensity S T d q n x =
      (Real.exp (d*x.1.2^2+q*x.1.2):ℂ)*density S T 0 n x.1.1 x.1.2 x.2 := by
  have he : moment (S-(d:ℂ)) (q:ℂ) n x.1.2 =
      (Real.exp (d*x.1.2^2+q*x.1.2):ℂ)*moment S 0 n x.1.2 := by
    unfold moment
    simp only [zero_mul,add_zero]
    rw [show -(S-(d:ℂ))*(x.1.2:ℂ)^2+(q:ℂ)*(x.1.2:ℂ) =
      ((d*x.1.2^2+q*x.1.2:ℝ):ℂ)+(-S*(x.1.2:ℂ)^2) by push_cast; ring,
      Complex.exp_add,← Complex.ofReal_exp]
    ring
  unfold tiltedDensity density
  rw [he]
  ring

private theorem tiltedDensity_integrable (S T : ℂ) (d q : ℝ) (n : ℕ)
    (hS : 0 < S.re) (hT : 0 < T.re) (hV : 0 < (S-(d:ℂ)).re) :
    Integrable (tiltedDensity S T d q n) chargedMeasure := by
  exact ((KFCausalShiftedComplexGaussianMoments.moment_integrable S 0 hS 0).mul_prod
    (KFCausalShiftedComplexGaussianMoments.moment_integrable (S-(d:ℂ)) (q:ℂ) hV n)).mul_prod
    (KFCausalReciprocalWedgeLaplace.laplace_integrable T hT)

theorem exponential_square_integrable (m : ℕ) (p : ℂ) (d q : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i) :
    Integrable (fun x : Charged => Real.exp (d*x.1.2^2+q*x.1.2)*‖packet m p w c x‖^2)
      chargedMeasure := by
  have hc (i j : ι) : Integrable (fun x => (c i*conj (c j))*
      tiltedDensity (widthSum p (w i) (w j)) (widthSum (conj p) (w i) (w j)) d q (2*m) x)
      chargedMeasure := by
    have hS : 0 < (widthSum p (w i) (w j)).re := by
      rw [widthSum_re]; exact mul_pos hp (add_pos (hw i) (hw j))
    have hT : 0 < (widthSum (conj p) (w i) (w j)).re := by
      rw [widthSum_re,Complex.conj_re]; exact mul_pos hp (add_pos (hw i) (hw j))
    have hV : 0 < (widthSum p (w i) (w j)-(d:ℂ)).re := by
      rw [Complex.sub_re,Complex.ofReal_re,widthSum_re]
      nlinarith [hd i,hd j]
    exact (tiltedDensity_integrable _ _ d q (2*m) hS hT hV).const_mul _
  have hi := integrable_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => hc i j))
  have he (x : Charged) : ((Real.exp (d*x.1.2^2+q*x.1.2)*‖packet m p w c x‖^2:ℝ):ℂ) =
      ∑ i, ∑ j, (c i*conj (c j))*
        tiltedDensity (widthSum p (w i) (w j)) (widthSum (conj p) (w i) (w j)) d q (2*m) x := by
    rw [Complex.ofReal_mul,KFCausalChargedEvenMomentFamily.packet_square]
    simp only [Finset.mul_sum,tiltedDensity_eq]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi' : Integrable (fun x : Charged =>
      ((Real.exp (d*x.1.2^2+q*x.1.2)*‖packet m p w c x‖^2:ℝ):ℂ)) chargedMeasure :=
    hi.congr (Eventually.of_forall (fun x => (he x).symm))
  simpa only [Complex.ofReal_re] using hi'.re

theorem cosh_square_integrable (m : ℕ) (p : ℂ) (d q : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i) :
    Integrable (fun x : Charged => Real.exp (d*x.1.2^2)*Real.cosh (q*x.1.2)*‖packet m p w c x‖^2)
      chargedMeasure := by
  have hi := ((exponential_square_integrable m p d q w c hp hw hd).add
    (exponential_square_integrable m p d (-q) w c hp hw hd)).div_const 2
  apply hi.congr
  filter_upwards [] with x
  simp only [Pi.add_apply,Real.cosh_eq,Real.exp_add,neg_mul]
  ring

theorem weightedEnergy_nonnegative (m : ℕ) (p : ℂ) (d q : ℝ) (w : ι → ℝ) (c : ι → ℂ) :
    0 ≤ weightedEnergy m p d q w c :=
  integral_nonneg (fun _ => mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le)
    (sq_nonneg _))

theorem pointwise_series (m : ℕ) (p : ℂ) (d q : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hd0 : 0 ≤ d) (x : Charged) :
    HasSum (fun k : ℕ×ℕ => d^k.1*q^(2*k.2)/((k.1.factorial:ℝ)*((2*k.2).factorial:ℝ))*
      ‖packet (m+(k.1+k.2)) p w c x‖^2)
      (Real.exp (d*x.1.2^2)*Real.cosh (q*x.1.2)*‖packet m p w c x‖^2) := by
  have he : HasSum (fun n : ℕ => (d*x.1.2^2)^n/(n.factorial:ℝ))
      (Real.exp (d*x.1.2^2)) := by
    simpa only [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (d*x.1.2^2)
  have hc := Real.hasSum_cosh (q*x.1.2)
  have hn (n : ℕ) : 0 ≤ (d*x.1.2^2)^n/(n.factorial:ℝ) := by positivity
  have hn' (n : ℕ) : 0 ≤ (q*x.1.2)^(2*n)/((2*n).factorial:ℝ) := by
    rw [pow_mul]
    positivity
  have hs := (he.mul hc (he.summable.mul_of_nonneg hc.summable hn hn')).mul_right
    (‖packet m p w c x‖^2)
  convert hs using 1
  funext k
  rw [packet_norm_add,mul_pow,mul_pow,pow_add]
  rw [pow_mul,show (x.1.2^2)^k.2 = x.1.2^(2*k.2) by rw [← pow_mul]]
  ring

theorem moment_series (m : ℕ) (p : ℂ) (d q : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd0 : 0 ≤ d) (hd : ∀ i, d < 2*p.re*w i) :
    HasSum (fun k : ℕ×ℕ => d^k.1*q^(2*k.2)/((k.1.factorial:ℝ)*((2*k.2).factorial:ℝ))*
      energy (m+(k.1+k.2)) p w c) (weightedEnergy m p d q w c) := by
  let f : (ℕ×ℕ) → Charged → ℝ := fun k x =>
    d^k.1*q^(2*k.2)/((k.1.factorial:ℝ)*((2*k.2).factorial:ℝ))*‖packet (m+(k.1+k.2)) p w c x‖^2
  have hi (k : ℕ×ℕ) : Integrable (f k) chargedMeasure := by
    have h := (KFCausalChargedEvenMomentFamily.packet_square_integrable (m+(k.1+k.2)) p w c hp hw).re
    simpa only [f,Complex.ofReal_re] using h.const_mul
      (d^k.1*q^(2*k.2)/((k.1.factorial:ℝ)*((2*k.2).factorial:ℝ)))
  have hn (k : ℕ×ℕ) (x : Charged) : 0 ≤ f k x := by
    have hq : 0 ≤ q^(2*k.2) := by rw [pow_mul]; positivity
    dsimp [f]
    positivity
  have hs (x : Charged) : HasSum (fun k => f k x)
      (Real.exp (d*x.1.2^2)*Real.cosh (q*x.1.2)*‖packet m p w c x‖^2) :=
    pointwise_series m p d q w c hd0 x
  have hb : Integrable (fun x : Charged => ∑' k, f k x) chargedMeasure :=
    (cosh_square_integrable m p d q w c hp hw hd).congr
      (Eventually.of_forall (fun x => (hs x).tsum_eq.symm))
  have h := hasSum_integral_of_dominated_convergence f (fun k => (hi k).aestronglyMeasurable)
    (fun k => Eventually.of_forall (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hn k x)]))
    (Eventually.of_forall (fun x => (hs x).summable)) hb (Eventually.of_forall hs)
  simpa only [f,integral_const_mul,energy,weightedEnergy] using h

theorem actual_scaled_series (α a β D b : ℝ) (hα : 0 < α) (hβ : 0 ≤ β)
    (hb : 0 < b) (hba : b < a) (m : ℕ) (w : ι → ℝ) (hw : ∀ i, 0 < w i) (c : ι → ℂ)
    (hd : ∀ i, 8*β*b^2 < α*(a^2-b^2)*w i) :
    HasSum (fun k : ℕ×ℕ => (8*β)^k.1*(4*D)^(2*k.2)/((k.1.factorial:ℝ)*((2*k.2).factorial:ℝ))*
      b^(2*(k.1+k.2)+2)*KFCausalChargedEvenMomentMonotonicity.lineEnergy α a (m+(k.1+k.2)) w c b)
      (b^2*weightedEnergy m (KFCausalChargedEvenMomentImaginaryBound.gamma α
        ((a:ℂ)+Complex.I*(b:ℂ))) (8*β*b^2) (4*D*b) w c) := by
  let p := KFCausalChargedEvenMomentImaginaryBound.gamma α ((a:ℂ)+Complex.I*(b:ℂ))
  have hp : 0 < p.re := KFCausalChargedCoolingFixedV.actual_gamma_re_positive α _ hα
    (by simpa [abs_of_pos hb] using hba)
  have hre : p.re = α*(a^2-b^2)/2 := by
    simp [p,KFCausalChargedEvenMomentImaginaryBound.gamma,pow_two,Complex.mul_re,Complex.mul_im]
  have hd' : ∀ i, 8*β*b^2 < 2*p.re*w i := by intro i; rw [hre]; nlinarith [hd i]
  have h := (moment_series m p (8*β*b^2) (4*D*b) w c hp hw (by positivity) hd').mul_left (b^2)
  convert h using 1
  funext k
  unfold KFCausalChargedEvenMomentMonotonicity.lineEnergy
  dsimp only [p]
  simp only [mul_pow,pow_add,← pow_mul,Nat.mul_add]
  ring

theorem actual_scaled_le (α a β D b₁ b₂ : ℝ) (hα : 0 < α) (hβ : 0 ≤ β)
    (hb₁ : 0 < b₁) (hb : b₁ ≤ b₂) (hb₂ : b₂ < a) (m : ℕ) (hm : m ≤ 2)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (c : ι → ℂ)
    (hd : ∀ i, 8*β*b₂^2 < α*(a^2-b₂^2)*w i) :
    b₁^2*weightedEnergy m (KFCausalChargedEvenMomentImaginaryBound.gamma α
        ((a:ℂ)+Complex.I*(b₁:ℂ))) (8*β*b₁^2) (4*D*b₁) w c ≤
    b₂^2*weightedEnergy m (KFCausalChargedEvenMomentImaginaryBound.gamma α
        ((a:ℂ)+Complex.I*(b₂:ℂ))) (8*β*b₂^2) (4*D*b₂) w c := by
  have hpos₂ := lt_of_lt_of_le hb₁ hb
  have hba₁ := lt_of_le_of_lt hb hb₂
  have hs : b₁^2 ≤ b₂^2 := by nlinarith
  have hd₁ : ∀ i, 8*β*b₁^2 < α*(a^2-b₁^2)*w i := by
    intro i
    have hwi := hw i
    have hp : 0 ≤ (8*β+α*w i)*(b₂^2-b₁^2) := mul_nonneg (by positivity) (sub_nonneg.mpr hs)
    nlinarith [hd i]
  apply hasSum_le _ (actual_scaled_series α a β D b₁ hα hβ hb₁ hba₁ m w hw c hd₁)
    (actual_scaled_series α a β D b₂ hα hβ hpos₂ hb₂ m w hw c hd)
  intro k
  have hmom := KFCausalChargedEvenMomentMonotonicity.scaled_monotone α a hα m (k.1+k.2) hm w hw c
    ⟨hb₁,hba₁⟩ ⟨hpos₂,hb₂⟩ hb
  have hc : 0 ≤ (8*β)^k.1*(4*D)^(2*k.2)/((k.1.factorial:ℝ)*((2*k.2).factorial:ℝ)) := by
    have hD : 0 ≤ (4*D)^(2*k.2) := by rw [pow_mul]; positivity
    positivity
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmom hc

#print axioms exponential_square_integrable
#print axioms cosh_square_integrable
#print axioms weightedEnergy_nonnegative
#print axioms pointwise_series
#print axioms moment_series
#print axioms actual_scaled_series
#print axioms actual_scaled_le
end
end UnifiedTheory.Audit.KFCausalChargedCoshGaussianMomentSeries
