/- An actual positive mass measure from resolvent spectral data.
Weighting the scalar spectral measure by r^2 selects the vector Rz and
removes r=0 before applying the unbounded inverse r |-> (r^-1-1)^2.
This constructs a measure for a resolvent-range seed, without assuming a
projection-valued spectral theorem for an unbounded operator. -/
import UnifiedTheory.Audit.KFCausalResolventSpectralMeasure
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalResolventMassMeasure
noncomputable section
open MeasureTheory
open scoped CompactlySupported
open KFCausalResolventSpectralMeasure
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
variable (R : X →L[ℂ] X) (hs : IsSelfAdjoint R) (z : X)

def weightedLaw : Measure (spectrum ℝ R) :=
  (spectralMeasure R hs z).withDensity (fun x => ENNReal.ofReal ((x : ℝ)^2))

theorem weighted_integral (f : spectrum ℝ R → ℝ) :
    ∫ x, f x ∂weightedLaw R hs z =
      ∫ x, (x : ℝ)^2 * f x ∂spectralMeasure R hs z := by
  rw [weightedLaw, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]

theorem square_integral :
    ∫ x, (x : ℝ)^2 ∂spectralMeasure R hs z = ‖R z‖^2 := by
  rw [moments]
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hs
  have he := hsym z (R z)
  change inner ℂ (R z) (R z) = inner ℂ z (R (R z)) at he
  simpa only [pow_two, ContinuousLinearMap.mul_apply, ← he] using
    (inner_self_eq_norm_sq (𝕜 := ℂ) (R z))

theorem weighted_mass : weightedLaw R hs z Set.univ = ENNReal.ofReal (‖R z‖^2) := by
  let f : C_c(spectrum ℝ R, ℝ) :=
    ⟨⟨fun x => (x : ℝ)^2, continuous_subtype_val.pow 2⟩,
      HasCompactSupport.of_compactSpace _⟩
  rw [weightedLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have he := ofReal_integral_eq_lintegral_ofReal
    (f := fun x : spectrum ℝ R => (x : ℝ)^2)
    (show Integrable (fun x : spectrum ℝ R => (x : ℝ)^2) (spectralMeasure R hs z)
      from f.integrable)
    (Filter.Eventually.of_forall (fun x => sq_nonneg (x : ℝ)))
  rw [← he, square_integral]

instance : IsFiniteMeasure (weightedLaw R hs z) :=
  ⟨by rw [weighted_mass]; exact ENNReal.ofReal_lt_top⟩

theorem weighted_probability (hz : ‖R z‖ = 1) : IsProbabilityMeasure (weightedLaw R hs z) :=
  ⟨by simp [weighted_mass, hz]⟩

theorem nonzero_ae : ∀ᵐ (x : spectrum ℝ R) ∂weightedLaw R hs z, (x : ℝ) ≠ 0 := by
  rw [weightedLaw, ae_withDensity_iff (by fun_prop)]
  apply Filter.Eventually.of_forall
  intro x hx hx0
  simp [hx0] at hx

def massSquare (x : spectrum ℝ R) : ℝ := ((x : ℝ)⁻¹ - 1)^2
theorem massSquare_measurable : Measurable (massSquare R) := by unfold massSquare; fun_prop

def massLaw : Measure ℝ := (weightedLaw R hs z).map (massSquare R)

instance : IsFiniteMeasure (massLaw R hs z) := by unfold massLaw; infer_instance

theorem mass_probability (hz : ‖R z‖ = 1) : IsProbabilityMeasure (massLaw R hs z) := by
  letI := weighted_probability R hs z hz
  exact Measure.isProbabilityMeasure_map (massSquare_measurable R).aemeasurable

theorem weighted_moments (n : ℕ) :
    ∫ x, (x : ℝ)^n ∂weightedLaw R hs z = (inner ℂ (R z) ((R^n) (R z))).re := by
  rw [weighted_integral]
  have he : (fun x : spectrum ℝ R => (x : ℝ)^2 * (x : ℝ)^n) =
      (fun x : spectrum ℝ R => (x : ℝ)^(n+2)) := by ext x; ring
  rw [he, moments]
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hs
  have hi := hsym z ((R^n) (R z))
  change inner ℂ (R z) ((R^n) (R z)) = inner ℂ z (R ((R^n) (R z))) at hi
  rw [hi]
  congr 2
  rw [pow_add, pow_two]
  simp only [ContinuousLinearMap.mul_apply]
  have hc : (R^n) (R (R z)) = R ((R^n) (R z)) := by
    change (R^n * R) (R z) = (R * R^n) (R z)
    rw [← pow_succ, ← pow_succ']
  exact hc

variable [Nontrivial X]

theorem spectral_bounds (hR : 0 ≤ R) (q : ℝ) (hq : ‖R‖ ≤ q) (x : spectrum ℝ R) :
    0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ q :=
  ⟨spectrum_nonneg_of_nonneg hR x.property,
    (le_abs_self (x : ℝ)).trans ((spectrum.norm_le_norm_of_mem x.property).trans hq)⟩

theorem inverse_lower (δ r : ℝ) (hδ : 0 ≤ δ) (hr : 0 < r)
    (hb : r ≤ (1 + δ)⁻¹) : δ ≤ r⁻¹-1 := by
  have hmul : r*(1+δ) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 1+δ)).mp (by simpa using hb)
  have hinv : 1+δ ≤ r⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hr]
    nlinarith
  linarith

theorem mass_lower_ae (hR : 0 ≤ R) (δ : ℝ) (hδ : 0 ≤ δ)
    (hb : ‖R‖ ≤ (1 + δ)⁻¹) : ∀ᵐ s ∂massLaw R hs z, δ^2 ≤ s := by
  rw [massLaw, ae_map_iff (massSquare_measurable R).aemeasurable
    (by measurability)]
  filter_upwards [nonzero_ae R hs z] with x hx
  obtain ⟨h0,hq⟩ := spectral_bounds R hR _ hb x
  have hl := inverse_lower δ x hδ (lt_of_le_of_ne h0 (Ne.symm hx)) hq
  dsimp [massSquare]
  nlinarith

/-- The mass law preserves every resolvent moment of the normalized range seed. -/
theorem mass_moments (hR : 0 ≤ R) (δ : ℝ) (hδ : 0 ≤ δ)
    (hb : ‖R‖ ≤ (1 + δ)⁻¹) (n : ℕ) :
    ∫ s, ((1 + Real.sqrt s)⁻¹)^n ∂massLaw R hs z =
      (inner ℂ (R z) ((R^n) (R z))).re := by
  rw [massLaw, integral_map (massSquare_measurable R).aemeasurable
    (by apply Measurable.aestronglyMeasurable; fun_prop :
      AEStronglyMeasurable (fun s : ℝ => ((1 + Real.sqrt s)⁻¹)^n)
      ((weightedLaw R hs z).map (massSquare R)))]
  rw [← weighted_moments R hs z n]
  apply integral_congr_ae
  filter_upwards [nonzero_ae R hs z] with x hx
  obtain ⟨h0, hq⟩ := spectral_bounds R hR _ hb x
  have hl := inverse_lower δ x hδ (lt_of_le_of_ne h0 (Ne.symm hx)) hq
  have hp : 0 ≤ (x : ℝ)⁻¹ - 1 := hδ.trans hl
  simp only [massSquare, Real.sqrt_sq hp, add_sub_cancel, inv_inv]

end
end UnifiedTheory.Audit.KFCausalResolventMassMeasure
