/- The exact entropy budget for all-plaquette localization. A useful union
rate is conditional on this explicit budget. In particular, sufficiently fast
volume growth defeats this bound at every nonvacuous hard-defect threshold. -/
import UnifiedTheory.Clay.YangMills.WilsonPlaquetteContraction

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPlaquetteEntropy
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonPhysicalVariance WilsonHighFieldDecay
open WilsonPlaquetteCover WilsonPlaquetteContraction
open WilsonPlaquetteColumnTail (rate)

/-- The Gaussian Haar mass is at most one for nonnegative coupling. -/
theorem gaussian_mass_le_one (β : ℝ) (hβ : 0 ≤ β) : SU2GaussianMass.mass β ≤ 1 := by
  calc
    _ ≤ ∫ _q : Q, (1 : ℝ) ∂SU2HaarTilt.haar := by
      apply integral_mono
        ((SU2GaussianMass.weight_continuous β).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)) (integrable_const _)
      intro q
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith)
        (sq_nonneg _))
    _ = 1 := by simp

theorem cap_ge_one (β : ℝ) (hβ : 3 / 4 ≤ β) : 1 ≤ SU2GaussianMass.cap β := by
  have hm := gaussian_mass_le_one β (by linarith)
  have hc := SU2GaussianMass.cap_nonneg β (by linarith)
  have hh := mul_le_mul_of_nonneg_right hm hc
  have hl := SU2GaussianMass.mass_cap_lower β hβ
  linarith

variable (n : ℕ)

def totalRate (β R : ℝ) : ℝ := 3 * (2 * n : ℝ) ^ 3 * rate β R

def price (β : ℝ) : ℝ := 3 * (2 * n : ℝ) ^ 3 * (SU2GaussianMass.cap β) ^ 2

theorem totalRate_factor (β R : ℝ) : totalRate n β R = price n β * Real.exp (-β * R) := by
  unfold totalRate price rate
  ring

variable [NeZero n]

theorem price_pos (β : ℝ) (hβ : 3 / 4 ≤ β) : 0 < price n β := by
  have hc : 0 < SU2GaussianMass.cap β := lt_of_lt_of_le zero_lt_one (cap_ge_one β hβ)
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
  unfold price
  positivity

/-- The entropy condition is an explicit hypothesis, not an inferred physical trajectory. -/
theorem entropy_price (β : ℝ) (hβ : 3 / 4 ≤ β) (R t : ℝ)
    (hv : Real.log (price n β) + t ≤ β * R) : totalRate n β R ≤ Real.exp (-t) := by
  rw [totalRate_factor, ← Real.exp_log (price_pos n β hβ), ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- Actual contraction of bad-region sources, after paying the finite volume price. -/
theorem entropy_contraction (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (hR : 0 < R) (t : ℝ)
    (hv : Real.log (price n β) + t ≤ β * R) (f : C(Slice (2 * n), ℝ))
    (hs : ∀ u, u ∉ allBad n R → f u = 0) :
    mass (2 * n) β (by linarith) (step (2 * n) β (by linarith) f) ≤
      Real.exp (-t) * mass (2 * n) β (by linarith) f :=
  (all_plaquettes_decay n β hβ R hR f hs).trans
    (mul_le_mul_of_nonneg_right (entropy_price n β hβ R t hv) (mass_nonneg _ _ _ f))

theorem entropy_coercivity (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (hR : 0 < R) (t : ℝ)
    (hv : Real.log (price n β) + t ≤ β * R) (f : C(Slice (2 * n), ℝ))
    (hs : ∀ u, u ∉ allBad n R → f u = 0) :
    (1 - Real.exp (-t)) * mass (2 * n) β (by linarith) f ≤ loss (2 * n) β (by linarith) f := by
  rw [loss_mass]
  have h := entropy_contraction n β hβ R hR t hv f hs
  linarith

/-- If 2 beta <= 3 log(2n), the all-plaquette rate is at least three for
R <= 2. This diagnoses this estimate, not the actual probability or gap. -/
theorem fast_volume_obstruction (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (hR : R ≤ 2)
    (hv : 2 * β ≤ 3 * Real.log (2 * n : ℝ)) : 3 ≤ totalRate n β R := by
  have hn : 0 < (2 * n : ℝ) := by
    have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
    positivity
  have he : 1 ≤ (2 * n : ℝ) ^ 3 * Real.exp (-β * R) := by
    rw [← Real.exp_log (pow_pos hn 3), ← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith [mul_le_mul_of_nonneg_left hR (show 0 ≤ β by linarith)]
  have hc := cap_ge_one β hβ
  have hc2 : 1 ≤ (SU2GaussianMass.cap β) ^ 2 := by nlinarith
  have hp := mul_le_mul_of_nonneg_left hc2
    (show 0 ≤ (2 * n : ℝ) ^ 3 * Real.exp (-β * R) by positivity)
  unfold totalRate rate
  nlinarith

omit [NeZero n] in
/-- Above this hard threshold the all-bad event is empty, independently of dynamics. -/
theorem allBad_empty_of_large_threshold (R : ℝ) (hR : 2 < R) : allBad n R = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨q,hq⟩ := hu
  have hb := (WilsonSlabBounds.characterDefect_bounds
    (WilsonTimeSlab.spatialHolonomy u q.1 q.2.val.1 q.2.val.2)).2
  change 2 * R ≤ 2 - (WilsonSingleLinkStaples.character
    (WilsonTimeSlab.spatialHolonomy u q.1 q.2.val.1 q.2.val.2)).re at hq
  linarith

end
end UnifiedTheory.Clay.YangMills.WilsonPlaquetteEntropy
