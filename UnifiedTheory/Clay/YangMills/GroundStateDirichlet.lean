/- Exact ground-state transform for a continuous symmetric kernel on a compact
space. The positive normalized eigenpair is an explicit input; this file does
not construct it for Wilson's kernel, identify a finite periodic law with its
vacuum, or prove a uniform ultraviolet energy estimate. -/
import UnifiedTheory.Clay.YangMills.LocalGibbsComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.GroundStateDirichlet
noncomputable section
open MeasureTheory

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

def transition (K : X × X → ℝ) (ψ : X → ℝ) (ℓ : ℝ) (x y : X) : ℝ :=
  K (x, y) * ψ y / (ℓ * ψ x)

def edgeDensity (K : X × X → ℝ) (ψ : X → ℝ) (ℓ : ℝ) (z : X × X) : ℝ :=
  K z * ψ z.1 * ψ z.2 / ℓ

def stationaryLaw (ψ : X → ℝ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal ((ψ x) ^ 2))

def edgeLaw (K : X × X → ℝ) (ψ : X → ℝ) (ℓ : ℝ) : Measure (X × X) :=
  (μ.prod μ).withDensity (fun z => ENNReal.ofReal (edgeDensity K ψ ℓ z))

theorem edgeDensity_continuous (K : X × X → ℝ) (hK : Continuous K)
    (ψ : X → ℝ) (hψ : Continuous ψ) (ℓ : ℝ) : Continuous (edgeDensity K ψ ℓ) :=
  ((hK.mul (hψ.comp continuous_fst)).mul (hψ.comp continuous_snd)).div_const ℓ

theorem edgeDensity_nonneg (K : X × X → ℝ) (hK : ∀ z, 0 ≤ K z)
    (ψ : X → ℝ) (hψ : ∀ x, 0 ≤ ψ x) (ℓ : ℝ) (hℓ : 0 < ℓ) (z : X × X) :
    0 ≤ edgeDensity K ψ ℓ z :=
  div_nonneg (mul_nonneg (mul_nonneg (hK z) (hψ z.1)) (hψ z.2)) hℓ.le

theorem edgeDensity_symmetric (K : X × X → ℝ) (hK : ∀ x y, K (x, y) = K (y, x))
    (ψ : X → ℝ) (ℓ : ℝ) (x y : X) :
    edgeDensity K ψ ℓ (x, y) = edgeDensity K ψ ℓ (y, x) := by
  unfold edgeDensity
  rw [hK x y]
  ring

theorem detailed_balance (K : X × X → ℝ) (ψ : X → ℝ)
    (ℓ : ℝ) (hℓ : 0 < ℓ) (x y : X) :
    (ψ x) ^ 2 * transition K ψ ℓ x y = edgeDensity K ψ ℓ (x, y) := by
  unfold transition edgeDensity
  field_simp

theorem transition_normalized (K : X × X → ℝ) (ψ : X → ℝ)
    (hψ : ∀ x, 0 < ψ x) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (heig : ∀ x, (∫ y, K (x, y) * ψ y ∂μ) = ℓ * ψ x) (x : X) :
    (∫ y, transition K ψ ℓ x y ∂μ) = 1 := by
  unfold transition
  rw [integral_div, heig x]
  exact div_self (mul_ne_zero (ne_of_gt hℓ) (ne_of_gt (hψ x)))

theorem edge_marginal (K : X × X → ℝ) (ψ : X → ℝ) (ℓ : ℝ) (hℓ : ℓ ≠ 0)
    (heig : ∀ x, (∫ y, K (x, y) * ψ y ∂μ) = ℓ * ψ x) (x : X) :
    (∫ y, edgeDensity K ψ ℓ (x, y) ∂μ) = (ψ x) ^ 2 := by
  have he : (fun y => edgeDensity K ψ ℓ (x, y)) =
      (fun y => (ψ x / ℓ) * (K (x, y) * ψ y)) := by
    funext y
    unfold edgeDensity
    ring
  rw [he, integral_const_mul, heig x]
  field_simp

theorem stationaryLaw_probability (ψ : X → ℝ) (hψ : Continuous ψ)
    (hnorm : (∫ x, (ψ x) ^ 2 ∂μ) = 1) : IsProbabilityMeasure (stationaryLaw μ ψ) := by
  constructor
  unfold stationaryLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      ((hψ.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (Filter.Eventually.of_forall (fun x => sq_nonneg (ψ x))), hnorm]
  simp

theorem edge_normalized (K : X × X → ℝ) (hK : Continuous K)
    (ψ : X → ℝ) (hψ : Continuous ψ) (ℓ : ℝ) (hℓ : ℓ ≠ 0)
    (heig : ∀ x, (∫ y, K (x, y) * ψ y ∂μ) = ℓ * ψ x)
    (hnorm : (∫ x, (ψ x) ^ 2 ∂μ) = 1) :
    (∫ z, edgeDensity K ψ ℓ z ∂μ.prod μ) = 1 := by
  rw [integral_prod _ ((edgeDensity_continuous K hK ψ hψ ℓ).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))]
  simp_rw [edge_marginal μ K ψ ℓ hℓ heig]
  exact hnorm

theorem edgeLaw_probability (K : X × X → ℝ) (hK : Continuous K) (hK0 : ∀ z, 0 ≤ K z)
    (ψ : X → ℝ) (hψ : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (heig : ∀ x, (∫ y, K (x, y) * ψ y ∂μ) = ℓ * ψ x)
    (hnorm : (∫ x, (ψ x) ^ 2 ∂μ) = 1) : IsProbabilityMeasure (edgeLaw μ K ψ ℓ) := by
  constructor
  unfold edgeLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      ((edgeDensity_continuous K hK ψ hψ ℓ).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
      (Filter.Eventually.of_forall (edgeDensity_nonneg K hK0 ψ hψ0 ℓ hℓ)),
    edge_normalized μ K hK ψ hψ ℓ hℓ.ne' heig hnorm]
  simp

theorem stationary_integral (ψ : X → ℝ) (hψ : Continuous ψ) (F : X → ℝ) :
    (∫ x, F x ∂stationaryLaw μ ψ) = ∫ x, (ψ x) ^ 2 * F x ∂μ := by
  unfold stationaryLaw
  rw [integral_withDensity_eq_integral_toReal_smul (hψ.pow 2).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]

theorem edge_integral (K : X × X → ℝ) (hK : Continuous K) (hK0 : ∀ z, 0 ≤ K z)
    (ψ : X → ℝ) (hψ : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (F : X × X → ℝ) :
    (∫ z, F z ∂edgeLaw μ K ψ ℓ) = ∫ z, edgeDensity K ψ ℓ z * F z ∂μ.prod μ := by
  unfold edgeLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    (edgeDensity_continuous K hK ψ hψ ℓ).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (edgeDensity_nonneg K hK0 ψ hψ0 ℓ hℓ _), smul_eq_mul]

def normSquared (ψ F : X → ℝ) : ℝ := ∫ x, (ψ x) ^ 2 * (F x) ^ 2 ∂μ

def pairing (K : X × X → ℝ) (ψ : X → ℝ) (ℓ : ℝ) (F : X → ℝ) : ℝ :=
  ∫ z, edgeDensity K ψ ℓ z * F z.1 * F z.2 ∂μ.prod μ

def dirichlet (K : X × X → ℝ) (ψ : X → ℝ) (ℓ : ℝ) (F : X → ℝ) : ℝ :=
  normSquared μ ψ F - pairing μ K ψ ℓ F

private theorem square_first (K : X × X → ℝ) (hK : Continuous K)
    (ψ : X → ℝ) (hψ : Continuous ψ) (ℓ : ℝ) (hℓ : ℓ ≠ 0)
    (heig : ∀ x, (∫ y, K (x, y) * ψ y ∂μ) = ℓ * ψ x)
    (F : X → ℝ) (hF : Continuous F) :
    (∫ z, edgeDensity K ψ ℓ z * (F z.1) ^ 2 ∂μ.prod μ) = normSquared μ ψ F := by
  have hi : Integrable (fun z => edgeDensity K ψ ℓ z * (F z.1) ^ 2) (μ.prod μ) :=
    ((edgeDensity_continuous K hK ψ hψ ℓ).mul
    ((hF.comp continuous_fst).pow 2)).integrable_of_hasCompactSupport
      (μ := μ.prod μ) (HasCompactSupport.of_compactSpace _)
  rw [integral_prod _ hi]
  simp_rw [integral_mul_const, edge_marginal μ K ψ ℓ hℓ heig]
  rfl

/-- The actual defect of the normalized ground-state kernel equals half the
stationary one-step squared increment. It is an identity, not an O(a) bound. -/
theorem dirichlet_identity (K : X × X → ℝ) (hK : Continuous K)
    (hsym : ∀ x y, K (x, y) = K (y, x))
    (ψ : X → ℝ) (hψ : Continuous ψ) (ℓ : ℝ) (hℓ : ℓ ≠ 0)
    (heig : ∀ x, (∫ y, K (x, y) * ψ y ∂μ) = ℓ * ψ x)
    (F : X → ℝ) (hF : Continuous F) :
    dirichlet μ K ψ ℓ F =
      (1 / 2 : ℝ) * ∫ z, edgeDensity K ψ ℓ z * (F z.1 - F z.2) ^ 2 ∂μ.prod μ := by
  have hc := edgeDensity_continuous K hK ψ hψ ℓ
  have hi1 : Integrable (fun z => edgeDensity K ψ ℓ z * (F z.1) ^ 2) (μ.prod μ) :=
    (hc.mul ((hF.comp continuous_fst).pow 2)).integrable_of_hasCompactSupport
    (μ := μ.prod μ) (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun z => edgeDensity K ψ ℓ z * (F z.2) ^ 2) (μ.prod μ) :=
    (hc.mul ((hF.comp continuous_snd).pow 2)).integrable_of_hasCompactSupport
    (μ := μ.prod μ) (HasCompactSupport.of_compactSpace _)
  have hic : Integrable (fun z => edgeDensity K ψ ℓ z * F z.1 * F z.2) (μ.prod μ) :=
    ((hc.mul (hF.comp continuous_fst)).mul (hF.comp continuous_snd)).integrable_of_hasCompactSupport
    (μ := μ.prod μ) (HasCompactSupport.of_compactSpace _)
  have hs2 : (∫ z, edgeDensity K ψ ℓ z * (F z.2) ^ 2 ∂μ.prod μ) = normSquared μ ψ F := by
    rw [integral_prod_symm _ hi2]
    simp_rw [edgeDensity_symmetric K hsym ψ ℓ]
    simp_rw [integral_mul_const, edge_marginal μ K ψ ℓ hℓ heig]
    rfl
  have he : (fun z => edgeDensity K ψ ℓ z * (F z.1 - F z.2) ^ 2) =
      (fun z => edgeDensity K ψ ℓ z * (F z.1) ^ 2 + edgeDensity K ψ ℓ z * (F z.2) ^ 2 -
        2 * (edgeDensity K ψ ℓ z * F z.1 * F z.2)) := by funext z; ring
  have hisum : Integrable (fun z => edgeDensity K ψ ℓ z * (F z.1) ^ 2 +
      edgeDensity K ψ ℓ z * (F z.2) ^ 2) (μ.prod μ) := hi1.add hi2
  rw [he, integral_sub hisum (hic.const_mul 2), integral_add hi1 hi2,
    integral_const_mul, square_first μ K hK ψ hψ ℓ hℓ heig F hF, hs2]
  unfold dirichlet pairing
  ring

theorem dirichlet_nonneg (K : X × X → ℝ) (hK : Continuous K) (hK0 : ∀ z, 0 ≤ K z)
    (hsym : ∀ x y, K (x, y) = K (y, x))
    (ψ : X → ℝ) (hψ : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (heig : ∀ x, (∫ y, K (x, y) * ψ y ∂μ) = ℓ * ψ x)
    (F : X → ℝ) (hF : Continuous F) : 0 ≤ dirichlet μ K ψ ℓ F := by
  rw [dirichlet_identity μ K hK hsym ψ hψ ℓ hℓ.ne' heig F hF]
  exact mul_nonneg (by norm_num) (integral_nonneg (fun z =>
    mul_nonneg (edgeDensity_nonneg K hK0 ψ hψ0 ℓ hℓ z) (sq_nonneg _)))

/-- The square-increment formula expressed as an expectation under the actual
constructed stationary two-time law. Normalization is proved above when ψ has
unit squared norm. The continuum O(a) upper bound is not a conclusion. -/
theorem dirichlet_expectation (K : X × X → ℝ) (hK : Continuous K) (hK0 : ∀ z, 0 ≤ K z)
    (hsym : ∀ x y, K (x, y) = K (y, x))
    (ψ : X → ℝ) (hψ : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (heig : ∀ x, (∫ y, K (x, y) * ψ y ∂μ) = ℓ * ψ x)
    (F : X → ℝ) (hF : Continuous F) :
    dirichlet μ K ψ ℓ F = (1 / 2 : ℝ) * ∫ z, (F z.1 - F z.2) ^ 2 ∂edgeLaw μ K ψ ℓ := by
  rw [edge_integral μ K hK hK0 ψ hψ hψ0 ℓ hℓ]
  exact dirichlet_identity μ K hK hsym ψ hψ ℓ hℓ.ne' heig F hF

end
end UnifiedTheory.Clay.YangMills.GroundStateDirichlet
