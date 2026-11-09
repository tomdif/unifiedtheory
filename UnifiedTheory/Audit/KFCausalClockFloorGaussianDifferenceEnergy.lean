/- The squared distance between the actual shifted and unshifted Gaussian
outputs is an exact second difference of Fourier energies. This upgrades
the scalar energy limit to control of the output vector. -/
import UnifiedTheory.Audit.KFCausalClockFloorOrderedEnergyLimit
import UnifiedTheory.Audit.KFCausalAveragedEnergyGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorGaussianDifferenceEnergy
noncomputable section
open MeasureTheory Filter
open scoped Topology FourierTransform
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space)
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit (euclideanSplit)
open UnifiedTheory.Audit.KFCausalClockFloorGaussianL1 (euclideanLine)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput
open UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates (coupledFourier)
open UnifiedTheory.Audit.KFCausalClockFloorFullFourierEnergy
open UnifiedTheory.Audit.KFCausalClockFloorOrderedEnergyLimit
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)

theorem exponential_difference_square (r : ℝ) (z : ℂ) :
    ‖(Real.exp r:ℂ)*z-z‖^2 = (Real.exp (2*r)-2*Real.exp r+1)*‖z‖^2 := by
  have ha : (Real.exp r:ℂ)*z-z = ((Real.exp r-1:ℝ):ℂ)*z := by push_cast; ring
  have he : (Real.exp r)^2 = Real.exp (2*r) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [ha,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,sub_sq,he]
  ring

def differenceEnergy (ε a α β hbar : ℝ) : ℝ :=
  spectralEnergy ε a α β hbar-2*spectralEnergy ε a α β (hbar/2)+spectralEnergy ε a α β 0

theorem differenceEnergy_zero (ε a α β : ℝ) : differenceEnergy ε a α β 0 = 0 := by
  simp only [differenceEnergy,zero_div]
  ring

theorem differenceEnergy_continuousAt_zero (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) :
    ContinuousAt (differenceEnergy ε a α β) 0 := by
  have hc := spectralEnergy_continuousAt_zero ε a α β hε ha hα hβ hw
  have ht : Tendsto (fun h : ℝ => h/2) (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := by
    simpa only [zero_div] using (tendsto_id.div_const (2:ℝ) :
      Tendsto (fun h : ℝ => h/2) (𝓝 (0:ℝ)) (𝓝 ((0:ℝ)/2)))
  have hm : ContinuousAt (fun h : ℝ => spectralEnergy ε a α β (h/2)) 0 := by
    change Tendsto _ (𝓝 0) (𝓝 (spectralEnergy ε a α β ((0:ℝ)/2)))
    rw [zero_div]
    exact hc.tendsto.comp ht
  exact (hc.sub (hm.const_mul 2)).add continuousAt_const

theorem gaussianState_difference_energy (ε a α β hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hb : |hbar| ≤ 2*Real.pi*ε/3) :
    ‖gaussianState ε a α β (-hbar/2) hε ha hα hβ hw (shift_bound ε hbar hb)-
      gaussianState ε a α β 0 hε ha hα hβ hw (by simp; positivity)‖^2 =
        differenceEnergy ε a α β hbar := by
  have hz : |(0:ℝ)| ≤ Real.pi*ε/3 := by simp; positivity
  have hb0 : |(0:ℝ)| ≤ 2*Real.pi*ε/3 := by simp; positivity
  have hbm : |hbar/2| ≤ 2*Real.pi*ε/3 := by
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith [abs_nonneg hbar]
  let f := gaussianState ε a α β 0 hε ha hα hβ hw hz
  let g := gaussianState ε a α β (-hbar/2) hε ha hα hβ hw (shift_bound ε hbar hb)
  let F : Space → ℂ := 𝓕 (euclideanLine ε a α β 0 ∘ euclideanSplit)
  have hi (r : ℝ) (hr : |r| ≤ 2*Real.pi*ε/3) :
      Integrable (fun k : Space => Real.exp (2*Real.pi*r*k 0)*‖F k‖^2) :=
    full_fourier_integrable ε a α β r hε ha hα hβ hw hr
  have he (r : ℝ) (hr : |r| ≤ 2*Real.pi*ε/3) :
      (∫ k : Space, Real.exp (2*Real.pi*r*k 0)*‖F k‖^2) = spectralEnergy ε a α β r :=
    full_fourier_energy ε a α β r hε ha hα hβ hw hr
  have hn : ‖g-f‖^2 = ∫ k : Space, ‖(Real.exp (Real.pi*hbar*k 0):ℂ)*F k-F k‖^2 := by
    rw [← (coupledFourier ε hε).norm_map (g-f),map_sub,l2_norm_square]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (coupledFourier ε hε g) (coupledFourier ε hε f),
      gaussianState_fourier ε a α β (-hbar/2) hε ha hα hβ hw (shift_bound ε hbar hb),
      gaussianState_fourier ε a α β 0 hε ha hα hβ hw hz] with k hs hg hf
    change (coupledFourier ε hε g-coupledFourier ε hε f) k = _ at hs
    change coupledFourier ε hε g k = _ at hg
    change coupledFourier ε hε f k = _ at hf
    rw [hs,Pi.sub_apply,hg,hf,← full_fourier_shift ε a α β hbar hε ha hα hβ hw hb k]
  change ‖g-f‖^2 = _
  rw [hn]
  calc
    _ = ∫ k : Space, (Real.exp (2*Real.pi*hbar*k 0)*‖F k‖^2-
        2*(Real.exp (2*Real.pi*(hbar/2)*k 0)*‖F k‖^2))+
        Real.exp (2*Real.pi*0*k 0)*‖F k‖^2 := by
      apply integral_congr_ae
      filter_upwards [] with k
      rw [exponential_difference_square]
      have h1 : 2*(Real.pi*hbar*k 0) = 2*Real.pi*hbar*k 0 := by ring
      have h2 : 2*Real.pi*(hbar/2)*k 0 = Real.pi*hbar*k 0 := by ring
      rw [h1,h2]
      simp only [mul_zero,zero_mul,Real.exp_zero,one_mul]
      ring
    _ = _ := by
      have hs := integral_add ((hi hbar hb).sub ((hi (hbar/2) hbm).const_mul 2)) (hi 0 hb0)
      dsimp only [Pi.sub_apply] at hs
      rw [hs,integral_sub (hi hbar hb) ((hi (hbar/2) hbm).const_mul 2),integral_const_mul,
        he hbar hb,he (hbar/2) hbm,he 0 hb0]
      rfl

#print axioms exponential_difference_square
#print axioms differenceEnergy_zero
#print axioms differenceEnergy_continuousAt_zero
#print axioms gaussianState_difference_energy

end
end UnifiedTheory.Audit.KFCausalClockFloorGaussianDifferenceEnergy
