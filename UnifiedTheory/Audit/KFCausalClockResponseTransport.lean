/- Transport the actual shifted Gaussian clock pairing to a transverse
kernel derivative. Clock frequencies and widths cancel from the response
coefficient. The finite-interval identity retains its boundary term; no
transverse lower bound or improper-integral limit is assumed. -/
import UnifiedTheory.Audit.KFCausalShiftedGaussianLongitudinalDifferential
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalClockResponseTransport
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (argument)
open UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile (clockAmplitude clockAmplitude_smooth)
open UnifiedTheory.Audit.KFCausalShiftedGaussianLongitudinalDifferential
  (inverseClock inverseClock_bound inverseClock_continuous amplitudeSlope clockAmplitude_derivative)
open UnifiedTheory.Audit.KFCausalClockFloorTransportDerivative (amplitudeLogSlope)

def clock (ε s : ℝ) : ℝ := Real.exp s+ε

def weakSlope (ε a p y s : ℝ) : ℂ :=
  ((p:ℂ)*Complex.I-1)*inverseClock ε y s-2*(a:ℂ)*argument ε y s+
    (inverseClock ε y s-(ε:ℂ)*(inverseClock ε y s)^2)/2

def coefficient (ε y s : ℝ) : ℝ :=
  2/clock ε s-(inverseClock ε y s+(ε:ℂ)*(inverseClock ε y s)^2).re

def pair (ε a b p q y s : ℝ) : ℂ :=
  star (clockAmplitude ε a p y s)*clockAmplitude ε b q y s

def weakPair (ε a b p q y s : ℝ) : ℂ :=
  pair ε a b p q y s*(star (weakSlope ε a p y s)+weakSlope ε b q y s)

def reduced (ε a b p q y : ℝ) (K K' : ℝ → ℂ) (s : ℝ) : ℂ :=
  pair ε a b p q y s*((coefficient ε y s:ℂ)*K s-K' s/(clock ε s:ℂ))

theorem slope_decomposition (ε a p y s : ℝ) (hε : 0 < ε) :
    weakSlope ε a p y s = amplitudeSlope ε a p y s/(clock ε s:ℂ)-
      (inverseClock ε y s+(ε:ℂ)*(inverseClock ε y s)^2)/2-
      (amplitudeLogSlope ε s:ℂ)/(clock ε s:ℂ) := by
  have hc : (clock ε s:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by unfold clock; positivity)
  unfold weakSlope amplitudeSlope
  change _ = ((amplitudeLogSlope ε s:ℂ)+(p:ℂ)*Complex.I*(clock ε s:ℂ)*inverseClock ε y s-
    2*(a:ℂ)*argument ε y s*(clock ε s:ℂ))/(clock ε s:ℂ)-_ - _
  field_simp
  ring

theorem pair_slope_split (ε a b p q y s : ℝ) (hε : 0 < ε) :
    star (weakSlope ε a p y s)+weakSlope ε b q y s =
      (star (amplitudeSlope ε a p y s)+amplitudeSlope ε b q y s)/(clock ε s:ℂ)+
      (coefficient ε y s:ℂ)-(Real.exp s:ℂ)/(clock ε s:ℂ)^2 := by
  rw [slope_decomposition ε a p y s hε,slope_decomposition ε b q y s hε]
  simp only [star_sub,star_div₀,Complex.star_def,Complex.conj_ofReal,map_ofNat]
  unfold coefficient
  rw [Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.re_eq_add_conj]
  unfold amplitudeLogSlope
  simp only [Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_add,
    Complex.ofReal_ofNat,Complex.ofReal_one]
  have hc : (clock ε s:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by unfold clock; positivity)
  dsimp only [clock] at *
  simp only [Complex.ofReal_add] at *
  field_simp
  ring

theorem coefficient_lower (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    -(2/ε) ≤ coefficient ε y s := by
  have hi := inverseClock_bound ε y s hε hy
  have hn : ‖inverseClock ε y s+(ε:ℂ)*(inverseClock ε y s)^2‖ ≤ 2/ε := by
    calc
      _ ≤ ‖inverseClock ε y s‖+‖(ε:ℂ)*(inverseClock ε y s)^2‖ := norm_add_le _ _
      _ = ‖inverseClock ε y s‖+ε*‖inverseClock ε y s‖^2 := by
        rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε]
      _ ≤ 1/ε+ε*(1/ε)^2 := add_le_add hi
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hi 2) hε.le)
      _ = 2/ε := by field_simp; ring
  have hr := (Complex.re_le_norm _).trans hn
  have hc : 0 ≤ 2/clock ε s := by unfold clock; positivity
  unfold coefficient
  linarith

theorem pair_derivative (ε a b p q y s : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) :
    HasDerivAt (pair ε a b p q y)
      (pair ε a b p q y s*(star (amplitudeSlope ε a p y s)+amplitudeSlope ε b q y s)) s := by
  convert (clockAmplitude_derivative ε a p y s hε hy).star.mul
    (clockAmplitude_derivative ε b q y s hε hy) using 1
  simp only [pair,star_mul]
  ring

theorem boundary_derivative (ε a b p q y s : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (K : ℝ → ℂ) (d : ℂ) (hK : HasDerivAt K d s) :
    HasDerivAt (fun x => K x*pair ε a b p q y x/(clock ε x:ℂ))
      (K s*weakPair ε a b p q y s-
        pair ε a b p q y s*((coefficient ε y s:ℂ)*K s-d/(clock ε s:ℂ))) s := by
  have hc : (clock ε s:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by unfold clock; positivity)
  have hd := (hK.mul (pair_derivative ε a b p q y s hε hy)).div
    ((Real.hasDerivAt_exp s).add_const ε).ofReal_comp hc
  convert hd using 1
  rw [weakPair,pair_slope_split ε a b p q y s hε]
  simp only [clock,Pi.mul_apply] at *
  field_simp
  ring

private theorem weakPair_continuous (ε a b p q y : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) : Continuous (weakPair ε a b p q y) := by
  have hi := inverseClock_continuous ε y hε hy
  have hz := (UnifiedTheory.Audit.KFCausalClockFloorRelativeShift.argument_smooth ε y).continuous
  have hs (w k : ℝ) : Continuous (weakSlope ε w k y) := by unfold weakSlope; fun_prop
  exact (((clockAmplitude_smooth ε a p y hε hy).continuous.star).mul
    (clockAmplitude_smooth ε b q y hε hy).continuous).mul ((hs a p).star.add (hs b q))

private theorem reduced_continuous (ε a b p q y : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (K K' : ℝ → ℂ) (hK : Continuous K) (hK' : Continuous K') :
    Continuous (reduced ε a b p q y K K') := by
  have hi := inverseClock_continuous ε y hε hy
  have hc : Continuous (clock ε) := by unfold clock; fun_prop
  have hn (s : ℝ) : clock ε s ≠ 0 := by unfold clock; positivity
  have hcoef : Continuous (coefficient ε y) :=
    (continuous_const.div hc hn).sub
      (Complex.continuous_re.comp (hi.add (continuous_const.mul (hi.pow 2))))
  unfold reduced pair
  exact (((clockAmplitude_smooth ε a p y hε hy).continuous.star).mul
    (clockAmplitude_smooth ε b q y hε hy).continuous).mul
      (((Complex.continuous_ofReal.comp hcoef).mul hK).sub (hK'.div (Complex.continuous_ofReal.comp hc) (fun s => Complex.ofReal_ne_zero.mpr (hn s))))

theorem interval_response (ε a b p q y : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (K K' : ℝ → ℂ) (hK : Continuous K) (hK' : Continuous K')
    (hd : ∀ s, HasDerivAt K (K' s) s) (l r : ℝ) :
    (∫ s in l..r, K s*weakPair ε a b p q y s) =
      K r*pair ε a b p q y r/(clock ε r:ℂ)-K l*pair ε a b p q y l/(clock ε l:ℂ)+
      ∫ s in l..r, reduced ε a b p q y K K' s := by
  have hw : IntervalIntegrable (fun s => K s*weakPair ε a b p q y s) volume l r := (hK.mul (weakPair_continuous ε a b p q y hε hy)).intervalIntegrable l r
  have hr : IntervalIntegrable (reduced ε a b p q y K K') volume l r := (reduced_continuous ε a b p q y hε hy K K' hK hK').intervalIntegrable l r
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (_ : s ∈ Set.uIcc l r) => boundary_derivative ε a b p q y s hε hy K (K' s) (hd s))
    (hw.sub hr)
  change (∫ s in l..r, K s*weakPair ε a b p q y s-reduced ε a b p q y K K' s) = _ at he
  rw [intervalIntegral.integral_sub hw hr] at he
  exact sub_eq_iff_eq_add.mp he

#print axioms slope_decomposition
#print axioms pair_slope_split
#print axioms coefficient_lower
#print axioms pair_derivative
#print axioms boundary_derivative
#print axioms interval_response
end
end UnifiedTheory.Audit.KFCausalClockResponseTransport
