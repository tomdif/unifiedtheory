/- The existing totalResponse converges to the derivative of the actual
limiting potential energy. This uses proved clock-neighborhood domination
and retains the exact pi/4 Gram-to-joint-integral normalization. -/
import UnifiedTheory.Audit.KFCausalClusteredClockLeibniz

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalClusteredResponseLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalClusteredWidthProfiles (widths coefficients limitDensity)
open KFCausalReciprocalNeutralPositiveForm (positiveDensity pairing)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalClusteredClockDensity (response limitResponse)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalClockFloorRelativeShift (scale scale_smooth)
open KFCausalChargedPairCompactGeometry (widthFloor widthFloor_positive)
open KFCausalReciprocalNeutralClockDerivative (totalResponse totalEnergy)

variable (n : ℕ) (α β ε y : ℝ) (b : ℂ) (P : Polynomial ℂ)

def limitEnergy (s : ℝ) : ℝ := Real.pi/4*
  ∫ p, limitDensity n α β (scale ε y s) (exponentialProfile b 1 P) p ∂jointMeasure

theorem actual_width_floors (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (s : ℝ) :
    widthFloor α ≤ α*area (scale ε y s) ∧
    widthFloor α ≤ α*area (scale ε y s)-8*β*(scale ε y s).im^2 := by
  have hc := KFCausalChargedPairCompactGeometry.actual_width_floor α β ε y s hα hβ.le hw hε hy
  change widthFloor α ≤ α*area (scale ε y s)-8*β*(scale ε y s).im^2 at hc
  exact ⟨by nlinarith [sq_nonneg (scale ε y s).im],hc⟩

variable (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
  (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
include hα hβ hw hε hy

theorem actual_density_integral_derivative (δ : ℝ) (hδ : 0 < δ) (s : ℝ) :
    HasDerivAt (fun t => ∫ p, positiveDensity (n+1) α β (widths n δ) (scale ε y t)
      (coefficients n δ) (fun _ => exponentialProfile b 1 P) p ∂jointMeasure)
      (∫ p, response n α β δ (scale ε y s) (deriv (scale ε y) s) b P p ∂jointMeasure) s :=
  KFCausalClusteredClockLeibniz.density_integral_derivative n α β δ (widthFloor α) hδ
    (scale ε y) (scale_smooth ε y hε hy) b P hβ (widthFloor_positive α hα)
    (fun t => (actual_width_floors α β ε y hα hβ hw hε hy t).1)
    (fun t => (actual_width_floors α β ε y hα hβ hw hε hy t).2) s

theorem limitEnergy_derivative (s : ℝ) :
    HasDerivAt (limitEnergy n α β ε y b P)
      (Real.pi/4*∫ p, limitResponse n α β (scale ε y s) (deriv (scale ε y) s) b P p ∂jointMeasure) s :=
  (KFCausalClusteredClockLeibniz.limitDensity_integral_derivative n α β (widthFloor α)
    (scale ε y) (scale_smooth ε y hε hy) b P hβ (widthFloor_positive α hα)
    (fun t => (actual_width_floors α β ε y hα hβ hw hε hy t).1)
    (fun t => (actual_width_floors α β ε y hα hβ hw hε hy t).2) s).const_mul (Real.pi/4)

theorem actual_totalResponse_integral (δ : ℝ) (hδ : 0 < δ) (s : ℝ) :
    totalResponse (n+1) ε y α β (widths n δ) (fun _ => b) (fun _ => P) (fun _ => coefficients n δ) s =
      Real.pi/4*∫ p, response n α β δ (scale ε y s) (deriv (scale ε y) s) b P p ∂jointMeasure := by
  have hd := KFCausalReciprocalNeutralKernelDerivative.fixed_pairing_derivative (n+1) ε y α β
    (widths n δ) (fun _ => b) (fun _ => P) hε hy hα hβ hw
    (KFCausalClusteredWidthProfiles.widths_admissible n δ hδ.le) (coefficients n δ) s
  have hi := (actual_density_integral_derivative n α β ε y b P hα hβ hw hε hy δ hδ s).const_mul (Real.pi/4)
  have he : (fun t => (pairing (n+1) α β (widths n δ) (scale ε y t) (coefficients n δ)
      (coefficients n δ) (fun _ => exponentialProfile b 1 P)).re) =
      fun t => Real.pi/4*∫ p, positiveDensity (n+1) α β (widths n δ) (scale ε y t)
        (coefficients n δ) (fun _ => exponentialProfile b 1 P) p ∂jointMeasure := by
    funext t
    exact KFCausalClusteredWidthEnergyLimit.actual_pairing_integral n α β ε y t δ b P hα hβ hw hε hy hδ
  rw [he] at hd
  exact hd.unique hi

theorem actual_totalResponse_tendsto (s : ℝ) :
    Tendsto (fun δ : ℝ => totalResponse (n+1) ε y α β (widths n δ)
      (fun _ => b) (fun _ => P) (fun _ => coefficients n δ) s) (𝓝[>] 0)
      (𝓝 (Real.pi/4*∫ p, limitResponse n α β (scale ε y s) (deriv (scale ε y) s) b P p ∂jointMeasure)) := by
  have hf := actual_width_floors α β ε y hα hβ hw hε hy s
  have hq := widthFloor_positive α hα
  apply Tendsto.congr' _ ((KFCausalClusteredClockDerivativeLimit.response_integral_tendsto
    n α β (scale ε y s) (deriv (scale ε y) s) b P hβ (hq.trans_le hf.1) (hq.trans_le hf.2)).const_mul (Real.pi/4))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (actual_totalResponse_integral n α β ε y b P hα hβ hw hε hy δ hδ s).symm

theorem actual_totalResponse_tendsto_deriv (s : ℝ) :
    Tendsto (fun δ : ℝ => totalResponse (n+1) ε y α β (widths n δ)
      (fun _ => b) (fun _ => P) (fun _ => coefficients n δ) s) (𝓝[>] 0)
      (𝓝 (deriv (limitEnergy n α β ε y b P) s)) := by
  rw [(limitEnergy_derivative n α β ε y b P hα hβ hw hε hy s).deriv]
  exact actual_totalResponse_tendsto n α β ε y b P hα hβ hw hε hy s

theorem relative_bound_passes_to_limit (s M : ℝ)
    (hM : ∀ δ : ℝ, 0 < δ → |totalResponse (n+1) ε y α β (widths n δ)
      (fun _ => b) (fun _ => P) (fun _ => coefficients n δ) s| ≤
        M*totalEnergy (n+1) ε y α β (widths n δ) (fun _ => b) (fun _ => P)
          (fun _ => coefficients n δ) s) :
    |deriv (limitEnergy n α β ε y b P) s| ≤ M*limitEnergy n α β ε y b P s := by
  apply le_of_tendsto_of_tendsto
    (actual_totalResponse_tendsto_deriv n α β ε y b P hα hβ hw hε hy s).abs
    ((KFCausalClusteredWidthEnergyLimit.actual_totalEnergy_tendsto n α β ε y s b P hα hβ hw hε hy).const_mul M)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact hM δ hδ

theorem upper_bound_passes_to_limit (s M : ℝ)
    (hM : ∀ δ : ℝ, 0 < δ → totalResponse (n+1) ε y α β (widths n δ)
      (fun _ => b) (fun _ => P) (fun _ => coefficients n δ) s ≤
        M*totalEnergy (n+1) ε y α β (widths n δ) (fun _ => b) (fun _ => P)
          (fun _ => coefficients n δ) s) :
    deriv (limitEnergy n α β ε y b P) s ≤ M*limitEnergy n α β ε y b P s := by
  apply le_of_tendsto_of_tendsto
    (actual_totalResponse_tendsto_deriv n α β ε y b P hα hβ hw hε hy s)
    ((KFCausalClusteredWidthEnergyLimit.actual_totalEnergy_tendsto n α β ε y s b P hα hβ hw hε hy).const_mul M)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact hM δ hδ

theorem strict_upper_violation_persists (s M : ℝ)
    (hM : M*limitEnergy n α β ε y b P s < deriv (limitEnergy n α β ε y b P) s) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0,
      M*totalEnergy (n+1) ε y α β (widths n δ) (fun _ => b) (fun _ => P)
        (fun _ => coefficients n δ) s <
      totalResponse (n+1) ε y α β (widths n δ) (fun _ => b) (fun _ => P)
        (fun _ => coefficients n δ) s :=
  ((KFCausalClusteredWidthEnergyLimit.actual_totalEnergy_tendsto n α β ε y s b P hα hβ hw hε hy).const_mul M).eventually_lt
    (actual_totalResponse_tendsto_deriv n α β ε y b P hα hβ hw hε hy s) hM

#print axioms actual_width_floors
#print axioms actual_density_integral_derivative
#print axioms limitEnergy_derivative
#print axioms actual_totalResponse_integral
#print axioms actual_totalResponse_tendsto
#print axioms actual_totalResponse_tendsto_deriv
#print axioms relative_bound_passes_to_limit
#print axioms upper_bound_passes_to_limit
#print axioms strict_upper_violation_persists
end
end UnifiedTheory.Audit.KFCausalClusteredResponseLimit
