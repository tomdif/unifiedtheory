/- Pointwise bridge from the actual physical charge-zero trial to the
previously checked longitudinal Gaussian. The ordered expression first
applies the inverse clock half, then the proposed inverse half-density
coordinate formula. Its unitary/operator realization is still separate. -/
import UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorChargeTrialBridge
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian
open UnifiedTheory.Audit.KFCausalClockFloorGaussianEnergy
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalChargeGaussianIdentities
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial

def amplitude (ε s : ℝ) : ℝ := Real.sqrt (Real.exp s+ε)*Real.exp (-s)

theorem amplitude_positive (ε s : ℝ) (hε : 0 < ε) : 0 < amplitude ε s := by
  unfold amplitude
  positivity

theorem amplitude_square (ε s : ℝ) (hε : 0 < ε) :
    (amplitude ε s)^2 = (Real.exp s+ε)*Real.exp (-2*s) := by
  rw [amplitude,mul_pow,Real.sq_sqrt (by positivity),← Real.exp_nat_mul]
  congr 1
  congr 1
  norm_num only [Nat.cast_ofNat]
  ring

theorem clockFunction_factor (ε a s : ℝ) (hε : 0 < ε) :
    clockFunction ε a s = (amplitude ε s:ℂ)*(Real.sqrt (Real.exp s+ε):ℂ)*
      clockFactor a (chart ε s:ℂ) := by
  have he : Real.exp s*Real.exp (-s)=1 := by rw [← Real.exp_add]; simp
  have hs := Real.sq_sqrt (by positivity : 0 ≤ Real.exp s+ε)
  have hc : 1+ε*Real.exp (-s) = amplitude ε s*Real.sqrt (Real.exp s+ε) := by
    calc
      _ = (Real.exp s+ε)*Real.exp (-s) := by rw [add_mul,he]
      _ = (Real.sqrt (Real.exp s+ε))^2*Real.exp (-s) :=
        congrArg (fun t : ℝ => t*Real.exp (-s)) hs.symm
      _ = _ := by unfold amplitude; ring
  unfold clockFunction realClock
  rw [hc,Complex.ofReal_mul,Complex.ofReal_mul]
  congr 1
  simp [clockFactor,Complex.ofReal_exp]

theorem inverse_clock_factor (ε a s : ℝ) (hε : 0 < ε) :
    (amplitude ε s:ℂ)⁻¹*((Real.sqrt (Real.exp s+ε):ℂ)⁻¹*clockFunction ε a s) =
      clockFactor a (chart ε s:ℂ) := by
  have ha : (amplitude ε s:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (amplitude_positive ε s hε).ne'
  have hs : (Real.sqrt (Real.exp s+ε):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [clockFunction_factor ε a s hε]
  field_simp

def inverseDressed (ε a α β : ℝ) (hε : 0 < ε) (z : ℝ × Grouped) : ℂ :=
  let s := (chartIso ε hε).symm z.1
  (amplitude ε s:ℂ)⁻¹*((Real.sqrt (Real.exp s+ε):ℂ)⁻¹*
    configurationProfile α β (clockFunction ε a)
      (s,flow s ![z.2.1 0,z.2.1 1,z.2.1 2,z.2.1 3,z.2.2]))

theorem inverseDressed_eq (ε a α β : ℝ) (hε : 0 < ε) (z : ℝ × Grouped) :
    inverseDressed ε a α β hε z = line ε a α β 0 z := by
  let s := (chartIso ε hε).symm z.1
  have hc : chart ε s = z.1 := (chartIso ε hε).apply_symm_apply _
  simp only [inverseDressed,configurationProfile,line,trial,Complex.ofReal_zero,zero_mul,
    add_zero,complexInverse_real ε hε]
  change (amplitude ε s:ℂ)⁻¹*((Real.sqrt (Real.exp s+ε):ℂ)⁻¹*
    (clockFunction ε a s*physicalGaussian α β (flow s ![z.2.1 0,z.2.1 1,z.2.1 2,z.2.1 3,z.2.2]))) =
    clockFactor a (z.1:ℂ)*packet α β (s:ℂ) z.2
  rw [← packet_real_flow α β s z.2.1 z.2.2]
  calc
    _ = ((amplitude ε s:ℂ)⁻¹*((Real.sqrt (Real.exp s+ε):ℂ)⁻¹*clockFunction ε a s))*
      packet α β (s:ℂ) z.2 := by ring
    _ = _ := by rw [inverse_clock_factor ε a s hε,hc]

def dressedTrial (ε a hbar : ℝ) (hε : 0 < ε) : ℝ × Grouped → ℂ :=
  inverseDressed ε a (groundWidth hbar) (neutralWidth hbar) hε

theorem dressedTrial_eq (ε a hbar : ℝ) (hε : 0 < ε) :
    dressedTrial ε a hbar hε = line ε a (groundWidth hbar) (neutralWidth hbar) 0 :=
  funext (inverseDressed_eq ε a (groundWidth hbar) (neutralWidth hbar) hε)

theorem dressedTrial_memLp (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0) :
    MemLp (dressedTrial ε a hbar hε) 2 volume := by
  rw [dressedTrial_eq]
  exact line_memLp ε a _ _ 0 hε ha (groundWidth_positive hbar hh)
    (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) (by simp; positivity)

theorem dressedTrial_longitudinal_integrable (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) :
    Integrable (fun w : ℝ × Grouped => Real.exp (2*Real.pi*hbar*w.1)*
      ‖(𝓕 (fun q : ℝ => dressedTrial ε a hbar hε (q,w.2))) w.1‖^2) := by
  rw [dressedTrial_eq]
  exact longitudinal_density_integrable ε a _ _ hbar hε ha (groundWidth_positive hbar hh)
    (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) hbound

#print axioms amplitude_positive
#print axioms amplitude_square
#print axioms clockFunction_factor
#print axioms inverse_clock_factor
#print axioms inverseDressed_eq
#print axioms dressedTrial_eq
#print axioms dressedTrial_memLp
#print axioms dressedTrial_longitudinal_integrable

end
end UnifiedTheory.Audit.KFCausalClockFloorChargeTrialBridge
