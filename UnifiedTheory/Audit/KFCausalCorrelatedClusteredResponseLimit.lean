/- Actual energy and response limits for arbitrary finite correlated
charged degrees and neutral exponential-polynomial profiles. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredLeibniz

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredResponseLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalReciprocalNeutralLaplace (jointMeasure)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredDensity
open KFCausalClockFloorRelativeShift (scale scale_smooth)
open KFCausalChargedPairCompactGeometry (widthFloor widthFloor_positive)
open KFCausalClusteredResponseLimit (actual_width_floors)
open KFCausalReciprocalNeutralPositiveForm (pairing)
open KFCausalReciprocalNeutralClockDerivative (totalEnergy totalResponse)

variable {m : ℕ} (f : Family m) (α β ε y : ℝ)

def limitEnergy (s : ℝ) : ℝ := Real.pi/4*∫ p, limitDensity f α β (scale ε y s) p ∂jointMeasure

variable (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
include hα hβ hw hε hy

theorem actual_pairing_integral (δ : ℝ) (hδ : 0 < δ) (s : ℝ) :
    (pairing (count f) α β (widths f δ) (scale ε y s) (coefficients f δ) (coefficients f δ)
      (fun j => exponentialProfile (sources f j) 1 (polynomials f j))).re =
      Real.pi/4*∫ p, density f α β δ (scale ε y s) p ∂jointMeasure := by
  have hwi := widths_admissible f δ hδ.le
  have hf := actual_width_floors α β ε y hα hβ hw hε hy s
  have hq := widthFloor_positive α hα
  have hpos (i j : Fin (count f)) := KFCausalReciprocalCrossGeometry.widths_positive α β
    (widths f δ i) (widths f δ j) (scale ε y s) (hwi i) (hwi j) (hq.trans_le hf.1) (hq.trans_le hf.2) hβ
  rw [KFCausalReciprocalNeutralPositiveForm.pairing_integral (count f) α β _ _ _ _
    (fun i j => (hpos i j).2.1)
    (fun i j => KFCausalReciprocalNeutralPlaneIntegrability.actual_plane_integrable α β ε y s _ _
      hα hβ hw hε hy (hwi i) (hwi j) (sources f i) (sources f j) (polynomials f i) (polynomials f j))
    (fun i => by have := hwi i; linarith) (fun i j => (hpos i j).1),Complex.ofReal_re]
  rfl

theorem actual_totalEnergy_integral (δ : ℝ) (hδ : 0 < δ) (s : ℝ) :
    totalEnergy (count f) ε y α β (widths f δ) (sources f) (polynomials f) (fun _ => coefficients f δ) s =
      Real.pi/4*∫ p, density f α β δ (scale ε y s) p ∂jointMeasure := by
  have he := KFCausalReciprocalNeutralKernelDerivative.pairing_totalEnergy (count f) ε y α β
    (widths f δ) (sources f) (polynomials f) (fun _ => coefficients f δ) hε hy hα hβ hw
    (widths_admissible f δ hδ.le) s
  have hp := actual_pairing_integral f α β ε y hα hβ hw hε hy δ hδ s
  rw [he,Complex.ofReal_re] at hp
  exact hp

theorem actual_density_integral_derivative (δ : ℝ) (hδ : 0 < δ) (s : ℝ) :
    HasDerivAt (fun t => ∫ p, density f α β δ (scale ε y t) p ∂jointMeasure)
      (∫ p, response f α β δ (scale ε y s) (deriv (scale ε y) s) p ∂jointMeasure) s :=
  KFCausalCorrelatedClusteredLeibniz.density_integral_derivative f α β δ (widthFloor α) hδ
    (scale ε y) (scale_smooth ε y hε hy) hβ (widthFloor_positive α hα)
    (fun t => (actual_width_floors α β ε y hα hβ hw hε hy t).1)
    (fun t => (actual_width_floors α β ε y hα hβ hw hε hy t).2) s

theorem limitEnergy_derivative (s : ℝ) :
    HasDerivAt (limitEnergy f α β ε y)
      (Real.pi/4*∫ p, limitResponse f α β (scale ε y s) (deriv (scale ε y) s) p ∂jointMeasure) s :=
  (KFCausalCorrelatedClusteredLeibniz.limitDensity_integral_derivative f α β (widthFloor α)
    (scale ε y) (scale_smooth ε y hε hy) hβ (widthFloor_positive α hα)
    (fun t => (actual_width_floors α β ε y hα hβ hw hε hy t).1)
    (fun t => (actual_width_floors α β ε y hα hβ hw hε hy t).2) s).const_mul (Real.pi/4)

theorem actual_totalResponse_integral (δ : ℝ) (hδ : 0 < δ) (s : ℝ) :
    totalResponse (count f) ε y α β (widths f δ) (sources f) (polynomials f) (fun _ => coefficients f δ) s =
      Real.pi/4*∫ p, response f α β δ (scale ε y s) (deriv (scale ε y) s) p ∂jointMeasure := by
  have hd := KFCausalReciprocalNeutralClockDerivative.total_derivative (count f) ε y α β
    (widths f δ) (sources f) (polynomials f) (fun _ => coefficients f δ) hε hy hα hβ hw
    (widths_admissible f δ hδ.le) (fun _ => contDiff_const) s
  have hi := (actual_density_integral_derivative f α β ε y hα hβ hw hε hy δ hδ s).const_mul (Real.pi/4)
  have he : totalEnergy (count f) ε y α β (widths f δ) (sources f) (polynomials f) (fun _ => coefficients f δ) =
      fun t => Real.pi/4*∫ p, density f α β δ (scale ε y t) p ∂jointMeasure := by
    funext t
    exact actual_totalEnergy_integral f α β ε y hα hβ hw hε hy δ hδ t
  rw [he] at hd
  exact hd.unique hi

theorem actual_totalEnergy_tendsto (s : ℝ) :
    Tendsto (fun δ => totalEnergy (count f) ε y α β (widths f δ) (sources f) (polynomials f)
      (fun _ => coefficients f δ) s) (𝓝[>] 0) (𝓝 (limitEnergy f α β ε y s)) := by
  have hf := actual_width_floors α β ε y hα hβ hw hε hy s
  have hq := widthFloor_positive α hα
  apply Tendsto.congr' _ ((KFCausalCorrelatedClusteredIntegrals.density_integral_tendsto f α β
    (scale ε y s) hβ (hq.trans_le hf.1) (hq.trans_le hf.2)).const_mul (Real.pi/4))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (actual_totalEnergy_integral f α β ε y hα hβ hw hε hy δ hδ s).symm

theorem actual_totalResponse_tendsto_deriv (s : ℝ) :
    Tendsto (fun δ => totalResponse (count f) ε y α β (widths f δ) (sources f) (polynomials f)
      (fun _ => coefficients f δ) s) (𝓝[>] 0) (𝓝 (deriv (limitEnergy f α β ε y) s)) := by
  rw [(limitEnergy_derivative f α β ε y hα hβ hw hε hy s).deriv]
  have hf := actual_width_floors α β ε y hα hβ hw hε hy s
  have hq := widthFloor_positive α hα
  apply Tendsto.congr' _ ((KFCausalCorrelatedClusteredIntegrals.response_integral_tendsto f α β
    (scale ε y s) (deriv (scale ε y) s) hβ (hq.trans_le hf.1) (hq.trans_le hf.2)).const_mul (Real.pi/4))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (actual_totalResponse_integral f α β ε y hα hβ hw hε hy δ hδ s).symm

theorem upper_bound_passes_to_limit (s M : ℝ)
    (hM : ∀ δ : ℝ, 0 < δ → totalResponse (count f) ε y α β (widths f δ) (sources f) (polynomials f)
      (fun _ => coefficients f δ) s ≤ M*totalEnergy (count f) ε y α β (widths f δ) (sources f)
        (polynomials f) (fun _ => coefficients f δ) s) :
    deriv (limitEnergy f α β ε y) s ≤ M*limitEnergy f α β ε y s := by
  apply le_of_tendsto_of_tendsto
    (actual_totalResponse_tendsto_deriv f α β ε y hα hβ hw hε hy s)
    ((actual_totalEnergy_tendsto f α β ε y hα hβ hw hε hy s).const_mul M)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact hM δ hδ

theorem strict_upper_violation_persists (s M : ℝ)
    (hM : M*limitEnergy f α β ε y s < deriv (limitEnergy f α β ε y) s) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0,
      M*totalEnergy (count f) ε y α β (widths f δ) (sources f) (polynomials f) (fun _ => coefficients f δ) s <
      totalResponse (count f) ε y α β (widths f δ) (sources f) (polynomials f) (fun _ => coefficients f δ) s :=
  ((actual_totalEnergy_tendsto f α β ε y hα hβ hw hε hy s).const_mul M).eventually_lt
    (actual_totalResponse_tendsto_deriv f α β ε y hα hβ hw hε hy s) hM

#print axioms actual_pairing_integral
#print axioms actual_totalEnergy_integral
#print axioms actual_density_integral_derivative
#print axioms limitEnergy_derivative
#print axioms actual_totalResponse_integral
#print axioms actual_totalEnergy_tendsto
#print axioms actual_totalResponse_tendsto_deriv
#print axioms upper_bound_passes_to_limit
#print axioms strict_upper_violation_persists
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredResponseLimit
