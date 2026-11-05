/- The exact dictionary between positive contraction eigenvalues and physical
energies. The zero eigenvalue is explicitly excluded from this parameter
space: Real.log 0 must never be mistaken for a physical zero energy. No
spectral representation for the full Wilson transfer operator is asserted. -/
import UnifiedTheory.Clay.YangMills.ContinuumSpectralWindow
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.TransferSpectralScale
noncomputable section
open MeasureTheory Filter ContinuumSpectralWindow
open scoped Topology NNReal

abbrev Eigenvalue := Set.Ioc (0 : ℝ) 1

def energy (a : ℝ) (ha : 0 < a) (r : Eigenvalue) : ℝ≥0 :=
  ⟨-Real.log (r : ℝ)/a,
    div_nonneg (neg_nonneg.mpr (Real.log_nonpos r.property.1.le r.property.2)) ha.le⟩

theorem energy_continuous (a : ℝ) (ha : 0 < a) : Continuous (energy a ha) := by
  apply Continuous.subtype_mk
  exact ((continuous_subtype_val.log (fun r => ne_of_gt r.property.1)).neg).div_const a

theorem energy_le_iff (a : ℝ) (ha : 0 < a) (r : Eigenvalue) (R : ℝ≥0) :
    energy a ha r ≤ R ↔ Real.exp (-a*(R : ℝ)) ≤ (r : ℝ) := by
  change -Real.log (r : ℝ)/a ≤ (R : ℝ) ↔ _
  rw [div_le_iff₀ ha]
  have he : Real.exp (-a*(R : ℝ)) ≤ (r : ℝ) ↔ -a*(R : ℝ) ≤ Real.log (r : ℝ) := by
    rw [← Real.exp_log r.property.1, Real.exp_le_exp]
    rw [Real.log_exp]
  rw [he]
  constructor <;> intro h <;> nlinarith

def physicalMeasure (a : ℝ) (ha : 0 < a) (μ : Measure Eigenvalue) : Measure ℝ≥0 :=
  μ.map (energy a ha)

instance physicalMeasure_finite (a : ℝ) (ha : 0 < a) (μ : Measure Eigenvalue)
    [IsFiniteMeasure μ] : IsFiniteMeasure (physicalMeasure a ha μ) :=
  Measure.isFiniteMeasure_map μ _

theorem window_dictionary (a : ℝ) (ha : 0 < a) (μ : Measure Eigenvalue) (R : ℝ≥0) :
    (physicalMeasure a ha μ).real (Set.Iic R) =
      μ.real {r : Eigenvalue | Real.exp (-a*(R : ℝ)) ≤ (r : ℝ)} := by
  change (μ.map (energy a ha) (Set.Iic R)).toReal = _
  rw [Measure.map_apply (energy_continuous a ha).measurable measurableSet_Iic]
  have he : (energy a ha) ⁻¹' Set.Iic R =
      {r : Eigenvalue | Real.exp (-a*(R : ℝ)) ≤ (r : ℝ)} := by
    ext r
    exact energy_le_iff a ha r R
  rw [he]
  rfl

theorem zero_energy_iff (a : ℝ) (ha : 0 < a) (r : Eigenvalue) :
    energy a ha r = 0 ↔ (r : ℝ) = 1 := by
  have hh := energy_le_iff a ha r 0
  simp only [NNReal.coe_zero, mul_zero, Real.exp_zero, le_zero_iff] at hh
  exact hh.trans ⟨fun h => le_antisymm r.property.2 h, fun h => h.ge⟩

/-- At an integer number of steps the continuum Laplace transform is
exactly the original spectral moment, with no limiting approximation. -/
theorem laplace_steps (a : ℝ) (ha : 0 < a) (μ : Measure Eigenvalue)
    [IsFiniteMeasure μ] (n : ℕ) :
    laplace (physicalMeasure a ha μ) (a*(n : ℝ)) = ∫ r : Eigenvalue, (r : ℝ)^n ∂μ := by
  unfold laplace physicalMeasure
  rw [integral_map (f := fun s : ℝ≥0 => Real.exp (-(a*(n : ℝ))*(s : ℝ)))
    (energy_continuous a ha).measurable.aemeasurable
    (Real.continuous_exp.comp (continuous_const.mul NNReal.continuous_coe)).aestronglyMeasurable]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro r
  change Real.exp (-(a*(n : ℝ))*(-Real.log (r : ℝ)/a)) = (r : ℝ)^n
  rw [show -(a*(n : ℝ))*(-Real.log (r : ℝ)/a) = (n : ℝ)*Real.log (r : ℝ) by field_simp]
  rw [Real.exp_nat_mul, Real.exp_log r.property.1]

/-- A fixed amount of spectral weight in this shrinking band is a direct
sufficient condition for a surviving physical-time signal. -/
theorem band_lower (a : ℝ) (ha : 0 < a) (μ : Measure Eigenvalue) [IsFiniteMeasure μ]
    (t : ℝ) (ht : 0 ≤ t) (R : ℝ≥0) (c : ℝ)
    (hband : c ≤ μ.real {r : Eigenvalue | Real.exp (-a*(R : ℝ)) ≤ (r : ℝ)}) :
    c*Real.exp (-t*(R : ℝ)) ≤ laplace (physicalMeasure a ha μ) t := by
  rw [← window_dictionary a ha μ R] at hband
  exact (mul_le_mul_of_nonneg_right hband (Real.exp_pos _).le).trans
    (window_lower (physicalMeasure a ha μ) t ht R)

end
end UnifiedTheory.Clay.YangMills.TransferSpectralScale
