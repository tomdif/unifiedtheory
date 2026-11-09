/- The actual canonical clock-momentum Born measure is invariant under
the physical charge circle on every L2 state. No momentum-domain or
charge-zero hypothesis is needed for this equality of finite measures. -/
import UnifiedTheory.Audit.KFCausalCanonicalClockChargeGraph
import UnifiedTheory.Audit.KFCausalL2BornLaw
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import UnifiedTheory.Audit.KFCausalUnitIntervalOrbit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCanonicalClockProbability
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space fourierCoordinates clockVector)
open UnifiedTheory.Audit.KFCausalClockFloorFourierMultiplier (symbol)
open UnifiedTheory.Audit.KFCausalConfigurationTranslation (translation)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFourierDiagonalization (fourier_clock_translation clock_phase)
open UnifiedTheory.Audit.KFCausalCanonicalClockChargeGraph (characteristic_charge)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

theorem symbol_continuous (h : ℝ) : Continuous (symbol h) := by
  unfold symbol
  fun_prop

def law (h : ℝ) (f : Hilbert) : Measure ℝ :=
  (KFCausalL2BornLaw.law volume (fourierCoordinates f)).map (symbol h)

theorem law_total (h : ℝ) (f : Hilbert) : law h f Set.univ = ENNReal.ofReal (‖f‖^2) := by
  rw [law,Measure.map_apply (symbol_continuous h).measurable MeasurableSet.univ,
    Set.preimage_univ,KFCausalL2BornLaw.law_total,LinearIsometryEquiv.norm_map]

instance law_finite (h : ℝ) (f : Hilbert) : IsFiniteMeasure (law h f) where
  measure_univ_lt_top := by rw [law_total]; exact ENNReal.ofReal_lt_top

theorem law_probability (h : ℝ) (f : Hilbert) (hf : ‖f‖ = 1) : IsProbabilityMeasure (law h f) where
  measure_univ := by rw [law_total,hf,one_pow,ENNReal.ofReal_one]

theorem translation_fourier_coe (h v : ℝ) (f : Hilbert) :
    fourierCoordinates (translation (h*v) f) =ᵐ[volume]
      fun k => Complex.exp (Complex.I*((v*symbol h k:ℝ):ℂ))*(fourierCoordinates f) k := by
  rw [fourier_clock_translation]
  filter_upwards [KFCausalFourierTranslation.phaseAction_coe ((h*v) • clockVector)
    (fourierCoordinates f)] with k hk
  rw [hk,clock_phase]
  congr 2
  unfold symbol
  push_cast
  ring

theorem law_characteristic (h v : ℝ) (f : Hilbert) :
    charFun (law h f) v = inner ℂ f (translation (h*v) f) := by
  rw [charFun_apply_real,law,integral_map (symbol_continuous h).measurable.aemeasurable (by fun_prop)]
  calc
    _ = ∫ k, Complex.exp (Complex.I*((v*symbol h k:ℝ):ℂ))
        ∂KFCausalL2BornLaw.law volume (fourierCoordinates f) := by
      apply integral_congr_ae
      filter_upwards [] with k
      congr 1
      push_cast
      ring
    _ = inner ℂ (fourierCoordinates f) (fourierCoordinates (translation (h*v) f)) :=
      KFCausalL2BornLaw.integral_eq_inner volume (fourierCoordinates f)
        (fourierCoordinates (translation (h*v) f))
        (fun k => Complex.exp (Complex.I*((v*symbol h k:ℝ):ℂ))) (translation_fourier_coe h v f)
    _ = _ := fourierCoordinates.inner_map_map _ _

theorem law_charge (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f : Hilbert) :
    law h (action h hh θ f) = law h f := by
  apply Measure.ext_of_charFun
  funext v
  rw [law_characteristic,law_characteristic,characteristic_charge]

theorem averaged_law (h : ℝ) (hh : h ≠ 0) (f : Hilbert) (A : Set ℝ) :
    (∫⁻ θ, law h (action h hh (2*Real.pi*θ) f) A ∂angleMeasure) = law h f A := by
  simp only [law_charge,lintegral_const,measure_univ,mul_one]

#print axioms symbol_continuous
#print axioms law_total
#print axioms law_finite
#print axioms law_probability
#print axioms translation_fourier_coe
#print axioms law_characteristic
#print axioms law_charge
#print axioms averaged_law

end
end UnifiedTheory.Audit.KFCausalCanonicalClockProbability
