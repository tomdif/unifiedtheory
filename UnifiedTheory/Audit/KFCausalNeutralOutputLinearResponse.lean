/- Exact linear and quadratic output response of the actual neutral
translation. After division by hbar, the quadratic remainder is bounded
by |hbar| times energy, uniformly over the input output vector. -/
import UnifiedTheory.Audit.KFCausalNeutralReferencePairing
import UnifiedTheory.Audit.KFCausalNeutralWeightTime

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalNeutralOutputLinearResponse
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open UnifiedTheory.Audit.KFCausalNeutralTranslationOutput
open UnifiedTheory.Audit.KFCausalNeutralTranslationBounds
open UnifiedTheory.Audit.KFCausalNeutralTranslationCommutator (translateLp_dual)
open UnifiedTheory.Audit.KFCausalNeutralReferencePairing (coefficient coefficient_norm)

def translated (B : Outputs →L[ℂ] Outputs) (r : ℝ) : Outputs →L[ℂ] Outputs :=
  (translateOutput r).comp B

theorem output_polynomial (w : Fin 8 → ℂ) (hw : ∀ i, w i ≠ 0) (c : ℂ) (r : ℝ) :
    outputAction w c r = translateOutput r+c • translated (weightedLinear w) r+
      c^2 • translated (weightedQuadratic w) r := by
  apply ContinuousLinearMap.ext
  intro y
  change translateOutput r (weightedMix w c y) = _
  rw [weightedMix_polynomial w hw]
  simp only [map_add,map_smul,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    translated,ContinuousLinearMap.comp_apply]

theorem translated_norm (B : Outputs →L[ℂ] Outputs) (r : ℝ) :
    ‖translated B r‖ ≤ ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
  intro y
  change ‖translateOutput r (B y)‖ ≤ _
  rw [translateOutput_norm]
  exact B.le_opNorm y

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

def linearPair (w : Fin 8 → ℂ) (r : ℝ) (y : Lp Outputs 2 μ) : ℂ :=
  inner ℂ y ((translated (weightedLinear w) r).compLp y)+
    inner ℂ ((translated (weightedLinear w) (-r)).compLp y) y

def quadraticPair (w : Fin 8 → ℂ) (r : ℝ) (y : Lp Outputs 2 μ) : ℂ :=
  inner ℂ y ((translated (weightedQuadratic w) r).compLp y)-
    inner ℂ ((translated (weightedQuadratic w) (-r)).compLp y) y

theorem outputLp_polynomial (w : Fin 8 → ℂ) (hw : ∀ i, w i ≠ 0) (r : ℝ)
    (y : Lp Outputs 2 μ) :
    inner ℂ y ((outputAction w (r:ℂ) r).compLp y)-
      inner ℂ ((outputAction w (-r:ℂ) (-r)).compLp y) y =
        (r:ℂ)*linearPair μ w r y+(r:ℂ)^2*quadraticPair μ w r y := by
  rw [output_polynomial w hw,output_polynomial w hw]
  simp only [ContinuousLinearMap.add_compLp,ContinuousLinearMap.smul_compLp,
    inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
    map_pow,map_neg,Complex.conj_ofReal,neg_sq,linearPair,quadraticPair]
  rw [translateLp_dual]
  ring

theorem translatedLp_bound (B : Outputs →L[ℂ] Outputs) (r : ℝ) (y : Lp Outputs 2 μ) :
    ‖(translated B r).compLp y‖ ≤ ‖B‖*‖y‖ :=
  ((translated B r).norm_compLp_le y).trans
    (mul_le_mul_of_nonneg_right (translated_norm B r) (norm_nonneg y))

theorem linearPair_bound (w : Fin 8 → ℂ) (r : ℝ) (y : Lp Outputs 2 μ) :
    ‖linearPair μ w r y‖ ≤ 2*‖weightedLinear w‖*‖y‖^2 := by
  calc
    _ ≤ ‖inner ℂ y ((translated (weightedLinear w) r).compLp y)‖+
        ‖inner ℂ ((translated (weightedLinear w) (-r)).compLp y) y‖ := norm_add_le _ _
    _ ≤ ‖y‖*‖(translated (weightedLinear w) r).compLp y‖+
        ‖(translated (weightedLinear w) (-r)).compLp y‖*‖y‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖y‖*(‖weightedLinear w‖*‖y‖)+(‖weightedLinear w‖*‖y‖)*‖y‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (translatedLp_bound μ _ _ _) (norm_nonneg y))
        (mul_le_mul_of_nonneg_right (translatedLp_bound μ _ _ _) (norm_nonneg y))
    _ = _ := by ring

theorem quadraticPair_bound (w : Fin 8 → ℂ) (r : ℝ) (y : Lp Outputs 2 μ) :
    ‖quadraticPair μ w r y‖ ≤ 2*‖weightedQuadratic w‖*‖y‖^2 := by
  calc
    _ ≤ ‖inner ℂ y ((translated (weightedQuadratic w) r).compLp y)‖+
        ‖inner ℂ ((translated (weightedQuadratic w) (-r)).compLp y) y‖ := norm_sub_le _ _
    _ ≤ ‖y‖*‖(translated (weightedQuadratic w) r).compLp y‖+
        ‖(translated (weightedQuadratic w) (-r)).compLp y‖*‖y‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖y‖*(‖weightedQuadratic w‖*‖y‖)+(‖weightedQuadratic w‖*‖y‖)*‖y‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (translatedLp_bound μ _ _ _) (norm_nonneg y))
        (mul_le_mul_of_nonneg_right (translatedLp_bound μ _ _ _) (norm_nonneg y))
    _ = _ := by ring

def linearRate (w : Fin 8 → ℂ) (h v : ℝ) (y : Lp Outputs 2 μ) : ℂ :=
  Complex.I*(v:ℂ)*linearPair μ w (h*v) y

def quadraticRate (w : Fin 8 → ℂ) (h v : ℝ) (y : Lp Outputs 2 μ) : ℂ :=
  Complex.I*(h:ℂ)*(v:ℂ)^2*quadraticPair μ w (h*v) y

theorem normalized_polynomial (w : Fin 8 → ℂ) (hw : ∀ i, w i ≠ 0)
    (h v : ℝ) (hne : h ≠ 0) (y : Lp Outputs 2 μ) :
    coefficient h*(inner ℂ y ((outputAction w ((h*v:ℝ):ℂ) (h*v)).compLp y)-
      inner ℂ ((outputAction w ((-(h*v):ℝ):ℂ) (-(h*v))).compLp y) y) =
        linearRate μ w h v y+quadraticRate μ w h v y := by
  rw [Complex.ofReal_neg,outputLp_polynomial μ w hw]
  simp only [coefficient,linearRate,quadraticRate,Complex.ofReal_div,Complex.ofReal_one,
    Complex.ofReal_mul]
  field_simp [Complex.ofReal_ne_zero.mpr hne]

theorem linearRate_bound (w : Fin 8 → ℂ) (h v : ℝ) (y : Lp Outputs 2 μ) :
    ‖linearRate μ w h v y‖ ≤ 2*|v| *‖weightedLinear w‖*‖y‖^2 := by
  simp only [linearRate,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ |v| *(2*‖weightedLinear w‖*‖y‖^2) :=
      mul_le_mul_of_nonneg_left (linearPair_bound μ w (h*v) y) (abs_nonneg v)
    _ = _ := by ring

theorem quadraticRate_bound (w : Fin 8 → ℂ) (h v : ℝ) (y : Lp Outputs 2 μ) :
    ‖quadraticRate μ w h v y‖ ≤ 2*|h| *|v|^2*‖weightedQuadratic w‖*‖y‖^2 := by
  simp only [quadraticRate,norm_mul,norm_pow,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ (|h| *|v|^2)*(2*‖weightedQuadratic w‖*‖y‖^2) :=
      mul_le_mul_of_nonneg_left (quadraticPair_bound μ w (h*v) y) (by positivity)
    _ = _ := by ring

theorem linearRate_time (m g k s t h v : ℝ) (y : Lp Outputs 2 μ) :
    linearRate μ (KFCausalPhysicalEnergyFactors.energyWeight m g k t) h v y =
      linearRate μ (KFCausalPhysicalEnergyFactors.energyWeight m g k s) h v y := by
  simp only [linearRate,linearPair,KFCausalNeutralWeightTime.weightedLinear_time m g k s t]

theorem quadraticRate_time (m g k s t h v : ℝ) (y : Lp Outputs 2 μ) :
    quadraticRate μ (KFCausalPhysicalEnergyFactors.energyWeight m g k t) h v y =
      quadraticRate μ (KFCausalPhysicalEnergyFactors.energyWeight m g k s) h v y := by
  simp only [quadraticRate,quadraticPair,KFCausalNeutralWeightTime.weightedQuadratic_time m g k s t]

omit μ in
theorem normalized_energy_polynomial (m g k t h v : ℝ) (hne : h ≠ 0)
    (hw : ∀ i, KFCausalPhysicalEnergyFactors.energyWeight m g k t i ≠ 0)
    (y : KFCausalAveragedOutputRescaling.EnergyOutputSpace) :
    coefficient h*(inner ℂ y (KFCausalNeutralReferenceForm.outputActionLp m g k t (h*v) y)-
      inner ℂ (KFCausalNeutralReferenceForm.outputActionLp m g k t (-(h*v)) y) y) =
      linearRate KFCausalUnitIntervalOrbit.angleMeasure (KFCausalPhysicalEnergyFactors.energyWeight m g k t) h v y+
      quadraticRate KFCausalUnitIntervalOrbit.angleMeasure (KFCausalPhysicalEnergyFactors.energyWeight m g k t) h v y :=
  normalized_polynomial KFCausalUnitIntervalOrbit.angleMeasure
    (KFCausalPhysicalEnergyFactors.energyWeight m g k t) hw h v hne y

theorem linearRate_continuous (w : Fin 8 → ℂ) (h v : ℝ) : Continuous (linearRate μ w h v) := by
  have hp := ((translated (weightedLinear w) (h*v)).compLpL 2 μ).continuous
  have hn := ((translated (weightedLinear w) (-(h*v))).compLpL 2 μ).continuous
  exact continuous_const.mul ((continuous_id.inner (𝕜 := ℂ) hp).add (hn.inner (𝕜 := ℂ) continuous_id))

theorem quadraticRate_continuous (w : Fin 8 → ℂ) (h v : ℝ) : Continuous (quadraticRate μ w h v) := by
  have hp := ((translated (weightedQuadratic w) (h*v)).compLpL 2 μ).continuous
  have hn := ((translated (weightedQuadratic w) (-(h*v))).compLpL 2 μ).continuous
  exact continuous_const.mul ((continuous_id.inner (𝕜 := ℂ) hp).sub (hn.inner (𝕜 := ℂ) continuous_id))

#print axioms linearRate_continuous
#print axioms quadraticRate_continuous

#print axioms normalized_energy_polynomial

#print axioms linearRate_time
#print axioms quadraticRate_time

#print axioms output_polynomial
#print axioms translated_norm
#print axioms outputLp_polynomial
#print axioms translatedLp_bound
#print axioms linearPair_bound
#print axioms quadraticPair_bound
#print axioms normalized_polynomial
#print axioms linearRate_bound
#print axioms quadraticRate_bound
end
end UnifiedTheory.Audit.KFCausalNeutralOutputLinearResponse
