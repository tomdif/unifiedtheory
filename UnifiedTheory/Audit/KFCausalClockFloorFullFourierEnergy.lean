/- The full six-dimensional Fourier transform of the sheared clock-floor
Gaussian has finite exponential longitudinal energy. This transfers the
clock-fiber estimate without assuming a separated transverse state. -/
import UnifiedTheory.Audit.KFCausalClockFourierEnergyTransfer
import UnifiedTheory.Audit.KFCausalClockFloorGaussianL1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorFullFourierEnergy
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalClockFourierFubini
open UnifiedTheory.Audit.KFCausalClockFourierEnergyTransfer
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian
open UnifiedTheory.Audit.KFCausalClockFloorGaussianEnergy
open UnifiedTheory.Audit.KFCausalClockFloorGaussianL1

theorem euclideanLine_clockFourier (ε a α β y : ℝ) :
    clockFourier (euclideanLine ε a α β y) = fourierLine ε a α β y ∘ pairGrouping := rfl

theorem euclideanLine_clockFourier_memLp (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) :
    MemLp (clockFourier (euclideanLine ε a α β y)) 2 := by
  rw [euclideanLine_clockFourier]
  exact (fourierLine_memLp ε a α β y hε ha hα hβ hw hy).comp_measurePreserving pairGrouping_preserves_volume

theorem euclideanLine_clock_weighted_integrable (ε a α β hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hh : |hbar| ≤ 2*Real.pi*ε/3) :
    Integrable (fun w : ℝ × TailSpace => Real.exp (2*Real.pi*hbar*w.1)*
      ‖clockFourier (euclideanLine ε a α β 0) w‖^2) :=
  pairGrouping_preserves_volume.integrable_comp_of_integrable
    (longitudinal_density_integrable ε a α β hbar hε ha hα hβ hw hh)

theorem full_fourier_integrable (ε a α β hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hh : |hbar| ≤ 2*Real.pi*ε/3) :
    Integrable (fun k : Space => Real.exp (2*Real.pi*hbar*k 0)*
      ‖(𝓕 (euclideanLine ε a α β 0 ∘ euclideanSplit)) k‖^2) := by
  have hy : |(0:ℝ)| ≤ Real.pi*ε/3 := by simp; positivity
  exact euclidean_weighted_integrable _ (euclideanLine_continuous ε a α β 0 hε hy)
    (euclideanLine_integrable ε a α β 0 hε ha hα hβ hw hy)
    (euclideanLine_clockFourier_memLp ε a α β 0 hε ha hα hβ hw hy) (2*Real.pi*hbar)
    (euclideanLine_clock_weighted_integrable ε a α β hbar hε ha hα hβ hw hh)

theorem full_fourier_energy (ε a α β hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hh : |hbar| ≤ 2*Real.pi*ε/3) :
    (∫ k : Space, Real.exp (2*Real.pi*hbar*k 0)*
      ‖(𝓕 (euclideanLine ε a α β 0 ∘ euclideanSplit)) k‖^2) =
      ∫ w : ℝ × Grouped, Real.exp (2*Real.pi*hbar*w.1)*‖fourierLine ε a α β 0 w‖^2 := by
  have hy : |(0:ℝ)| ≤ Real.pi*ε/3 := by simp; positivity
  have ht := weighted_energy_identity _ (euclideanLine_continuous ε a α β 0 hε hy)
    (euclideanLine_integrable ε a α β 0 hε ha hα hβ hw hy)
    (euclideanLine_clockFourier_memLp ε a α β 0 hε ha hα hβ hw hy) (2*Real.pi*hbar)
    (euclideanLine_clock_weighted_integrable ε a α β hbar hε ha hα hβ hw hh)
  exact ht.trans (pairGrouping_preserves_volume.integral_comp'
    (fun w : ℝ × Grouped => Real.exp (2*Real.pi*hbar*w.1)*‖fourierLine ε a α β 0 w‖^2))

theorem exponentialFourier_square (ε a α β hbar : ℝ) (w : ℝ × Grouped) :
    ‖exponentialFourier ε a α β hbar w‖^2 =
      Real.exp (2*Real.pi*hbar*w.1)*‖fourierLine ε a α β 0 w‖^2 := by
  rw [exponentialFourier,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),← Real.exp_nat_mul]
  congr 1
  congr 1
  norm_num only [Nat.cast_ofNat]
  ring

theorem full_fourier_shifted_energy (ε a α β hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hh : |hbar| ≤ 2*Real.pi*ε/3) :
    (∫ k : Space, Real.exp (2*Real.pi*hbar*k 0)*
      ‖(𝓕 (euclideanLine ε a α β 0 ∘ euclideanSplit)) k‖^2) =
      ∫ z : ℝ × Grouped, ‖line ε a α β (-hbar/2) z‖^2 := by
  rw [full_fourier_energy ε a α β hbar hε ha hα hβ hw hh]
  simp_rw [← exponentialFourier_square]
  exact exponential_energy_identity ε a α β hbar hε ha hα hβ hw hh

theorem full_fourier_shift (ε a α β hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hh : |hbar| ≤ 2*Real.pi*ε/3) (k : Space) :
    (Real.exp (Real.pi*hbar*k 0):ℂ)*(𝓕 (euclideanLine ε a α β 0 ∘ euclideanSplit)) k =
      (𝓕 (euclideanLine ε a α β (-hbar/2) ∘ euclideanSplit)) k := by
  have h0 : |(0:ℝ)| ≤ Real.pi*ε/3 := by simp; positivity
  have hs : |-hbar/2| ≤ Real.pi*ε/3 := by
    rw [abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  have hpoint (q : ℝ) (y : TailSpace) :
      (Real.exp (Real.pi*hbar*q):ℂ)*clockFourier (euclideanLine ε a α β 0) (q,y) =
        clockFourier (euclideanLine ε a α β (-hbar/2)) (q,y) :=
    congrFun (exponentialFourier_eq ε a α β hbar hε ha hα.le hβ.le hw hh) (pairGrouping (q,y))
  rw [fourier_iterated _ (euclideanLine_continuous ε a α β 0 hε h0)
      (euclideanLine_integrable ε a α β 0 hε ha hα hβ hw h0),
    fourier_iterated _ (euclideanLine_continuous ε a α β (-hbar/2) hε hs)
      (euclideanLine_integrable ε a α β (-hbar/2) hε ha hα hβ hw hs)]
  simp only [Real.fourier_eq,Circle.smul_def,smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← hpoint]
  ring

#print axioms euclideanLine_clockFourier
#print axioms euclideanLine_clockFourier_memLp
#print axioms euclideanLine_clock_weighted_integrable
#print axioms full_fourier_integrable
#print axioms full_fourier_energy
#print axioms exponentialFourier_square
#print axioms full_fourier_shifted_energy
#print axioms full_fourier_shift

end
end UnifiedTheory.Audit.KFCausalClockFloorFullFourierEnergy
