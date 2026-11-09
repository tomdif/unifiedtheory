/- Multiplication by a shifted neutral-coordinate power preserves the
entire correlated width sum exactly. No estimate is taken on individual
clustered coefficients. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredPhysicalTransfer
import UnifiedTheory.Audit.KFCausalMixedFieldClockCoefficients

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredNeutralPowers
noncomputable section
open MeasureTheory
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredGlobalEnvelope (reweight)
open KFCausalCorrelatedClusteredPhysicalTransfer (represented)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalRelativeGaussianDifferential (position)
open KFCausalMixedFieldClockBounds (field fieldBound fieldBound_positive actual_field_bound)

variable {m : ℕ}

def neutralPower (f : Family m) (n : ℕ) : Family m :=
  { f with polynomial := fun i => Polynomial.X^n*f.polynomial i }

def weightedCoefficients (c : ℝ → Fin m → ℂ) (ε y z : ℝ) (n : ℕ) (s : ℝ) (i : Fin m) : ℂ :=
  (fieldBound ε y z s:ℂ)^n*c s i

theorem represented_neutralPower (f : Family m) (c : ℝ → Fin m → ℂ) (α β ε y δ : ℝ)
    (n : ℕ) (x : Configuration) :
    represented (neutralPower f n) c α β ε y δ x =
      (position (scale ε y x.1) x.2 4)^n*represented f c α β ε y δ x := by
  unfold represented KFCausalReciprocalNeutralPhysicalSliceNorm.wave
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [KFCausalReciprocalNeutralSliceIntegrability.factor,pow_zero,one_mul,
    KFCausalNeutralExponentialProfiles.exponentialProfile]
  change ((f.amplitude (index f j).1*c x.1 (index f j).1)*
    KFCausalClusteredWidthProfiles.coefficients (f.degree (index f j).1) δ (index f j).2)*
      (Complex.exp _*(Complex.exp _*(Polynomial.X^n*f.polynomial (index f j).1).eval _)) = _
  rw [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X]
  change _ = (position (scale ε y x.1) x.2 4)^n*
    (((f.amplitude (index f j).1*c x.1 (index f j).1)*
      KFCausalClusteredWidthProfiles.coefficients (f.degree (index f j).1) δ (index f j).2)*
      (Complex.exp _*(Complex.exp _*(f.polynomial (index f j).1).eval _)))
  simp only [show widths (neutralPower f n) = widths f from rfl,
    show sources (neutralPower f n) = sources f from rfl]
  ring

theorem represented_weighted (f : Family m) (c : ℝ → Fin m → ℂ) (α β ε y z δ : ℝ)
    (n : ℕ) (x : Configuration) :
    represented f (weightedCoefficients c ε y z n) α β ε y δ x =
      (fieldBound ε y z x.1:ℂ)^n*represented f c α β ε y δ x := by
  unfold represented KFCausalReciprocalNeutralPhysicalSliceNorm.wave
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change ((f.amplitude (index f j).1*((fieldBound ε y z x.1:ℂ)^n*c x.1 (index f j).1))*
    KFCausalClusteredWidthProfiles.coefficients (f.degree (index f j).1) δ (index f j).2)*_ = _
  change _ = (fieldBound ε y z x.1:ℂ)^n*
    (((f.amplitude (index f j).1*c x.1 (index f j).1)*
      KFCausalClusteredWidthProfiles.coefficients (f.degree (index f j).1) δ (index f j).2)*_)
  ring

def fieldProfile (f : Family m) (c : ℝ → Fin m → ℂ) (α β ε y z : ℝ) (n : ℕ)
    (δ : ℝ) (x : Configuration) : ℂ :=
  (field (scale ε z x.1) x.2)^n*represented f c α β ε y δ x

theorem difference_bound (f : Family m) (c : ℝ → Fin m → ℂ) (α β ε y z : ℝ) (n : ℕ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hz : |z| ≤ Real.pi*ε/3) (hy0 : y ≠ 0)
    (δ η : ℝ) (x : Configuration) :
    ‖fieldProfile f c α β ε y z n δ x-fieldProfile f c α β ε y z n η x‖ ≤
      ‖represented (neutralPower f n) (weightedCoefficients c ε y z n) α β ε y δ x-
        represented (neutralPower f n) (weightedCoefficients c ε y z n) α β ε y η x‖ := by
  rw [represented_weighted,represented_weighted,represented_neutralPower,represented_neutralPower]
  simp only [fieldProfile,← mul_sub,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (fieldBound_positive ε y z x.1 hε hy0)]
  have hp := pow_le_pow_left₀ (norm_nonneg (field (scale ε z x.1) x.2))
    (actual_field_bound ε y z x.1 hε hy hz hy0 x.2) n
  rw [mul_pow] at hp
  nlinarith only [mul_le_mul_of_nonneg_right hp
    (norm_nonneg (represented f c α β ε y δ x-represented f c α β ε y η x))]

#print axioms represented_neutralPower
#print axioms represented_weighted
#print axioms difference_bound
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredNeutralPowers
