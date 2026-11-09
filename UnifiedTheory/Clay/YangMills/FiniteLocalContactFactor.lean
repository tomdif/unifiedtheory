/- One coherent local contact matrix for a finite family of Schwartz sources.
Its quadratic form is exactly the existing local source factor. No counterterm
coefficient or continuum bound is chosen by this finite-source dictionary. -/
import UnifiedTheory.Clay.YangMills.WilsonQuadraticJets
import UnifiedTheory.Clay.YangMills.FiniteSourceWickJets

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.FiniteLocalContactFactor
noncomputable section
open MeasureTheory ContinuumControl PeriodicLattice4 SchwartzConfigurationTensor
open DiagonalContactTerms LocalCountertermReflection

/-- The off-diagonal polarization of the actual local contact distribution. -/
theorem contact_tensor_mixed (f g : CorrelationTest 1) :
    contact (tensor 1 1 f g) = ∫ x, f x * g x := by
  rw [contact_apply]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => tensor_concat 1 1 f g x x)

theorem contact_tensor_symmetric (f g : CorrelationTest 1) :
    contact (tensor 1 1 f g) = contact (tensor 1 1 g f) := by
  rw [contact_tensor_mixed, contact_tensor_mixed]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => mul_comm (f x) (g x))

/-- The cross-reflection contact is exactly zero at a strict physical support gap. -/
theorem contact_tensor_reflected_zero (τ a : ℝ) (plane : Plane)
    (f g : CorrelationTest 1) (hf : SupportedAfter τ f) (hg : SupportedAfter τ g)
    (hgap : CellReflectionCovariance.cellOffset a plane < 2 * τ) :
    contact (tensor 1 1 (theta a plane f) g) = 0 := by
  rw [contact_tensor_mixed]
  exact integral_eq_zero_of_ae (Filter.Eventually.of_forall
    (fun x => mixed_product_zero τ a plane f g hf hg hgap x))

variable {I : Type*} [Fintype I]

/-- One common matrix determines all ray and cross counterterms. -/
def contactMatrix (κ : ℝ) (f : I → CorrelationTest 1) (i j : I) : ℝ :=
  2 * κ * (contact (tensor 1 1 (f i) (f j))).re

omit [Fintype I] in
theorem contactMatrix_symmetric (κ : ℝ) (f : I → CorrelationTest 1) (i j : I) :
    contactMatrix κ f i j = contactMatrix κ f j i := by
  unfold contactMatrix
  rw [contact_tensor_symmetric]

def finiteSource (f : I → CorrelationTest 1) (t : I → ℝ) : CorrelationTest 1 :=
  ∑ i, (t i : ℂ) • f i

@[simp] theorem finiteSource_apply (f : I → CorrelationTest 1) (t : I → ℝ)
    (x : Configuration 1) : finiteSource f t x = ∑ i, (t i : ℂ) * f i x := by
  simp [finiteSource, SchwartzMap.sum_apply]

/-- Exact local quadratic expansion for an arbitrary finite source family. -/
theorem localSquare_finiteSource (f : I → CorrelationTest 1) (t : I → ℝ) :
    localSquare (finiteSource f t) =
      ∑ i, ∑ j, (t i : ℂ) * (t j : ℂ) * contact (tensor 1 1 (f i) (f j)) := by
  have hi (i j : I) : Integrable (fun x => f i x * f j x) :=
    (f j).integrable.bdd_mul (f i).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall (SchwartzMap.norm_le_seminorm ℝ (f i)))
  have he (x : Configuration 1) : (finiteSource f t x)^2 =
      ∑ i, ∑ j, ((t i : ℂ) * (t j : ℂ)) * (f i x * f j x) := by
    rw [finiteSource_apply, pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold localSquare
  simp_rw [he]
  rw [integral_finset_sum _ (fun i _ =>
    integrable_finset_sum _ (fun j _ => (hi i j).const_mul _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum _ (fun j _ => (hi i j).const_mul _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, contact_tensor_mixed]

/-- The finite matrix and the original local source functional agree exactly. -/
theorem quadratic_eq_localSquare (κ : ℝ) (f : I → CorrelationTest 1) (t : I → ℝ) :
    FiniteSourceWickJets.quadratic (contactMatrix κ f) t =
      κ * (localSquare (finiteSource f t)).re := by
  rw [localSquare_finiteSource]
  unfold FiniteSourceWickJets.quadratic contactMatrix
  simp only [Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem finiteSource_real (f : I → CorrelationTest 1) (hf : ∀ i x, (f i x).im = 0)
    (t : I → ℝ) (x : Configuration 1) : (finiteSource f t x).im = 0 := by
  simp [finiteSource_apply, Complex.mul_im, hf]

/-- The finite quadratic factor is literally the existing source renormalization factor. -/
theorem sourceFactor_finiteSource (κ : ℝ) (f : I → CorrelationTest 1)
    (hf : ∀ i x, (f i x).im = 0) (t : I → ℝ) :
    sourceFactor κ (finiteSource f t) =
      (Real.exp (-FiniteSourceWickJets.quadratic (contactMatrix κ f) t) : ℂ) := by
  rw [quadratic_eq_localSquare]
  simpa only [Complex.ofReal_one, one_smul, one_pow, mul_one] using
    WilsonQuadraticJets.sourceFactor_real_ray κ 1 (finiteSource f t)
      (finiteSource_real f hf t)

end
end UnifiedTheory.Clay.YangMills.FiniteLocalContactFactor
