/- The momentum-boosted trial has an explicit classical initial probability
law at any fixed canonical momentum. Its actual ordered transverse kinetic
energies converge to the corresponding integrals. No positive-time
propagation or full averaged energy-form membership is asserted here. -/
import UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit
import UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics
import UnifiedTheory.Audit.KFCausalClockFloorInitialEnergyIdentification

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClockFloorBoostedInitialLaw
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra
open UnifiedTheory.Audit.KFCausalPhysicalMomentumModulation
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (positionFrequency)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit
open UnifiedTheory.Audit.KFCausalClockFloorInitialCharacteristic
open UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw
open UnifiedTheory.Audit.KFCausalPhysicalGaussianConcentration (dot)
open UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalStates (unitTrial)
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms
open UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy (dampedClockFunction dampedClockFunction_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorInitialEnergyIdentification (dampedClock_square)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem operator_modulation (h : ℝ) (z : Frequency (X := Configuration))
    (l : Configuration →L[ℝ] ℝ) (f : Hilbert) :
    operator volume h z (modulation l f) =
      scalar (h*l z.2) • modulation l (operator volume h z f) := by
  apply Lp.ext
  filter_upwards [operator_coe volume h z (modulation l f),
    (KFCausalLpPhaseTranslation.shift_preserves volume (h • z.2)).quasiMeasurePreserving.ae
      (modulation_coe l f),modulation_coe l (operator volume h z f),
    operator_coe volume h z f,
    Lp.coeFn_smul (scalar (h*l z.2)) (modulation l (operator volume h z f))]
    with x hx hy hm ho hs
  change modulation l f (x+h • z.2) = scalar (l (x+h • z.2))*f (x+h • z.2) at hy
  rw [hx,hy,hs]
  simp only [Pi.smul_apply,smul_eq_mul,hm,ho,map_add,map_smul,smul_eq_mul,scalar_add]
  ring

theorem characteristic_modulation (h : ℝ) (z : Frequency (X := Configuration))
    (l : Configuration →L[ℝ] ℝ) (f : Hilbert) :
    characteristic volume h (modulation l f) z = scalar (h*l z.2)*characteristic volume h f z := by
  rw [characteristic,operator_modulation,inner_smul_right,(modulation l).inner_map_map]
  rfl

theorem characteristic_boost (h : ℝ) (hh : h ≠ 0) (z : Frequency (X := Configuration))
    (l : Configuration →L[ℝ] ℝ) (f : Hilbert) :
    characteristic volume h (modulation (h⁻¹ • l) f) z =
      scalar (l z.2)*characteristic volume h f z := by
  rw [characteristic_modulation,ContinuousLinearMap.smul_apply,smul_eq_mul,
    ← mul_assoc,mul_inv_cancel₀ hh,one_mul]

def boostedAxis (p : Configuration) (s : ℝ) : PhaseSpace := ((s,0),p)

theorem boostedAxis_continuous (p : Configuration) : Continuous (boostedAxis p) := by
  unfold boostedAxis
  fun_prop

def boostedLaw (ε a : ℝ) (p : Configuration) : Measure PhaseSpace :=
  (clockLaw ε a).map (boostedAxis p)

theorem boostedLaw_probability (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration) :
    IsProbabilityMeasure (boostedLaw ε a p) := by
  letI := clockLaw_probability ε a hε ha
  exact Measure.isProbabilityMeasure_map (boostedAxis_continuous p).measurable.aemeasurable

theorem boostedLaw_characteristic (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (p : Configuration) (r u : ℝ) (ξ η : Transverse) :
    ∫ z, classicalPhase r u ξ η z ∂boostedLaw ε a p =
      scalar (positionFrequency p.1 p.2 (u,η))*clockCharacteristic ε a hε ha r := by
  rw [boostedLaw,integral_map (boostedAxis_continuous p).measurable.aemeasurable
    (classicalPhase_continuous r u ξ η).aestronglyMeasurable,clockCharacteristic_law,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with s
  change scalar (r*s+dot ξ 0+u*p.1+dot η p.2) = scalar _*scalar (r*s)
  rw [← scalar_add]
  congr 1
  simp only [positionFrequency,ContinuousLinearMap.coe_mk',LinearMap.coe_mk,AddHom.coe_mk,
    dot,Pi.zero_apply,mul_zero,Finset.sum_const_zero,add_zero]
  simp only [mul_comm (η _) (p.2 _)]
  ring

theorem boosted_characteristic_limit (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hz : Tendsto h atTop (𝓝 0))
    (p : Configuration) (r u : ℝ) (ξ η : Transverse) :
    Tendsto (fun n => inner ℂ (boostedState ε a (h n) hε ha (hh n) (positionFrequency p.1 p.2))
      (observable (h n) r u ξ η (boostedState ε a (h n) hε ha (hh n) (positionFrequency p.1 p.2))))
      atTop (𝓝 (∫ z, classicalPhase r u ξ η z ∂boostedLaw ε a p)) := by
  have he (n : ℕ) : inner ℂ (boostedState ε a (h n) hε ha (hh n) (positionFrequency p.1 p.2))
      (observable (h n) r u ξ η (boostedState ε a (h n) hε ha (hh n) (positionFrequency p.1 p.2))) =
      scalar (positionFrequency p.1 p.2 (u,η))*quantumCharacteristic ε a (h n) hε ha (hh n) r u ξ η :=
    characteristic_boost (h n) (hh n) (positionFrequency r ξ,(u,η))
      (positionFrequency p.1 p.2) (unitTrial ε a (h n) hε ha (hh n))
  simp_rw [he]
  rw [boostedLaw_characteristic ε a hε ha]
  have ht := quantumCharacteristic_tendsto ε a hε ha h hh hz r u ξ η
  rw [classicalLaw_characteristic ε a hε ha] at ht
  exact ht.const_mul _

def kineticSymbol (ε : ℝ) (v : Transverse) (z : PhaseSpace) : ℝ :=
  (dot z.2.2 v)^2/clock ε z.1.1

theorem kineticSymbol_continuous (ε : ℝ) (hε : 0 < ε) (v : Transverse) :
    Continuous (kineticSymbol ε v) := by
  unfold kineticSymbol dot
  apply Continuous.div
  · fun_prop
  · unfold clock
    fun_prop
  · intro z
    exact (clock_positive ε z.1.1 hε.le).ne'

theorem kinetic_density_identity (ε a : ℝ) (hε : 0 < ε) (p : Configuration)
    (v : Transverse) (s : ℝ) :
    kineticSymbol ε v (boostedAxis p s)*clockDensity ε a s =
      (dot p.2 v)^2*‖dampedClockFunction ε a s‖^2/clockMass ε a := by
  rw [dampedClock_square ε a s hε]
  unfold kineticSymbol boostedAxis clockDensity
  ring

theorem boostedLaw_kinetic_integrable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (p : Configuration) (v : Transverse) : Integrable (kineticSymbol ε v) (boostedLaw ε a p) := by
  apply (integrable_map_measure (kineticSymbol_continuous ε hε v).aestronglyMeasurable
    (boostedAxis_continuous p).measurable.aemeasurable).mpr
  rw [clockLaw,integrable_withDensity_iff_integrable_smul'
    (clockDensity_continuous ε a).measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have hm := dampedClockFunction_memLp ε a hε ha
  have hi := (memLp_two_iff_integrable_sq_norm hm.1).mp hm
  apply ((hi.const_mul ((dot p.2 v)^2)).div_const (clockMass ε a)).congr
  filter_upwards [] with s
  rw [ENNReal.toReal_ofReal (clockDensity_nonnegative ε a hε ha s),smul_eq_mul]
  exact (kinetic_density_identity ε a hε p v s).symm.trans (mul_comm _ _)

theorem boostedLaw_kinetic_integral (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (p : Configuration) (v : Transverse) :
    ∫ z, kineticSymbol ε v z ∂boostedLaw ε a p = (dot p.2 v)^2*dampedMass ε a/clockMass ε a := by
  rw [boostedLaw,integral_map (boostedAxis_continuous p).measurable.aemeasurable
    (kineticSymbol_continuous ε hε v).aestronglyMeasurable,clockLaw,
    integral_withDensity_eq_integral_toReal_smul
      (clockDensity_continuous ε a).measurable.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  calc
    _ = ∫ s, (dot p.2 v)^2*‖dampedClockFunction ε a s‖^2/clockMass ε a := by
      apply integral_congr_ae
      filter_upwards [] with s
      rw [ENNReal.toReal_ofReal (clockDensity_nonnegative ε a hε ha s),smul_eq_mul,mul_comm]
      exact kinetic_density_identity ε a hε p v s
    _ = _ := by rw [integral_div,integral_const_mul]; rfl

theorem boosted_kinetic_classical_limit (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hz : Tendsto h atTop (𝓝 0))
    (p : Configuration) (v : Transverse) :
    Tendsto (fun n => ‖boostedOutput ε a (h n) hε ha (hh n) v (positionFrequency p.1 p.2)‖^2)
      atTop (𝓝 (∫ z, kineticSymbol ε v z ∂boostedLaw ε a p)) := by
  rw [boostedLaw_kinetic_integral ε a hε ha]
  simpa only [positionFrequency,ContinuousLinearMap.coe_mk',LinearMap.coe_mk,
    AddHom.coe_mk,mul_zero,zero_add] using
    boostedOutput_energy_limit ε a hε ha h hh hz v (positionFrequency p.1 p.2)

#print axioms operator_modulation
#print axioms characteristic_modulation
#print axioms characteristic_boost
#print axioms boostedAxis_continuous
#print axioms boostedLaw_probability
#print axioms boostedLaw_characteristic
#print axioms boosted_characteristic_limit
#print axioms kineticSymbol_continuous
#print axioms kinetic_density_identity
#print axioms boostedLaw_kinetic_integrable
#print axioms boostedLaw_kinetic_integral
#print axioms boosted_kinetic_classical_limit

end
end UnifiedTheory.Audit.KFCausalClockFloorBoostedInitialLaw
