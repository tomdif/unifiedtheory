/- Arbitrary directional powers of coherent-source packets are actual
L2 vectors. Uniform Gaussian majorants give continuity along bounded
source curves, including the quadratic moments used by second momenta. -/
import UnifiedTheory.Audit.KFCausalDirectionalGaussianStates
import UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalSourcedDirectionalMoments
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalDirectionalGaussianStates (linearForm linearForm_continuous direction_power_memLp)
open KFCausalClockFloorShearBounds (physicalGaussian)
open KFCausalClockFloorCoherentMoments
open KFCausalClockFloorCoherentBounds
open KFCausalClockFloorCoherentDerivative
open KFCausalClockFloorCoherentOrbitContinuity (physicalProfile_bound)
open KFCausalPhysicalGaussianDerivative (configuration_product_memLp)

theorem packet_power_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (b : Fin 5 → ℂ) (d : Transverse) (n : ℕ) :
    MemLp (fun q => (linearForm d q:ℂ)^n*sourcedPacket α β b q) 2 volume := by
  have hc := ((Complex.continuous_ofReal.comp (linearForm_continuous d)).pow n).mul
    (sourcedPacket_continuous α β b)
  apply ((direction_power_memLp (α/2) (β/2) (by positivity) (by positivity) d n).const_mul
    (Real.exp (sourceConstant α β b/2):ℂ)).of_le hc.aestronglyMeasurable
  filter_upwards [] with q
  have hb := mul_le_mul_of_nonneg_left (sourcedPacket_bound α β hα hβ hw b q)
    (norm_nonneg ((linearForm d q:ℂ)^n))
  simpa only [Pi.mul_apply,Function.comp_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),mul_left_comm] using hb

def profile (C : ℂ) (p α β : ℝ) (b : Fin 5 → ℂ) (g : ℝ → ℂ)
    (d : Transverse) (n : ℕ) (x : Configuration) : ℂ :=
  (linearForm d x.2:ℂ)^n*physicalProfile C p α β b g x

theorem profile_memLp (C : ℂ) (p α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (b : Fin 5 → ℂ) (g : ℝ → ℂ) (hg : MemLp g 2 volume) (d : Transverse) (n : ℕ) :
    MemLp (profile C p α β b g d n) 2 volume := by
  convert configuration_product_memLp _ _ (clockMultiplier_memLp C p g hg)
    (packet_power_memLp α β hα hβ hw b d n) using 1
  funext x
  unfold profile physicalProfile
  ring

def state (C : ℂ) (p α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (b : Fin 5 → ℂ) (g : ℝ → ℂ) (hg : MemLp g 2 volume) (d : Transverse) (n : ℕ) : Hilbert :=
  (profile_memLp C p α β hα hβ hw b g hg d n).toLp (profile C p α β b g d n)

theorem state_coe (C : ℂ) (p α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (b : Fin 5 → ℂ) (g : ℝ → ℂ) (hg : MemLp g 2 volume) (d : Transverse) (n : ℕ) :
    state C p α β hα hβ hw b g hg d n =ᵐ[volume] profile C p α β b g d n :=
  (profile_memLp C p α β hα hβ hw b g hg d n).coeFn_toLp

theorem state_curve_continuous (α β B : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (C : ℝ → ℂ) (p : ℝ → ℝ) (b : ℝ → Fin 5 → ℂ) (g : ℝ → ℂ) (hg : MemLp g 2 volume)
    (hCc : Continuous C) (hpc : Continuous p) (hbc : Continuous b)
    (hC : ∀ θ, ‖C θ‖ ≤ 1) (hb : ∀ θ, sourceSize (b θ) ≤ B) (d : Transverse) (n : ℕ) :
    Continuous (fun θ => state (C θ) (p θ) α β hα hβ hw (b θ) g hg d n) := by
  let G : Configuration → ℂ := fun x => (Real.exp (B*positionConstant α β/2):ℂ)*
    (g x.1*((linearForm d x.2:ℂ)^n*physicalGaussian (α/2) (β/2) x.2))
  have hG : MemLp G 2 volume := (configuration_product_memLp _ _ hg
    (direction_power_memLp (α/2) (β/2) (by positivity) (by positivity) d n)).const_mul _
  apply KFCausalDominatedL2Continuity.continuous_toLp _ _ G hG
  · intro θ
    filter_upwards [] with x
    have ht := mul_le_mul_of_nonneg_left
      (physicalProfile_bound (C θ) (p θ) α β B hα hβ hw (b θ) g (hC θ) (hb θ) x)
      (norm_nonneg ((linearForm d x.2:ℂ)^n))
    simpa only [profile,G,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _),mul_assoc,mul_left_comm,mul_comm] using ht
  · filter_upwards [] with x
    unfold profile physicalProfile clockMultiplier sourcedPacket
      KFCausalClockFloorCoherentSources.linearSource KFCausalClockFloorCoherentStrip.clockPhase
    fun_prop

#print axioms packet_power_memLp
#print axioms profile_memLp
#print axioms state_coe
#print axioms state_curve_continuous
end
end UnifiedTheory.Audit.KFCausalSourcedDirectionalMoments
