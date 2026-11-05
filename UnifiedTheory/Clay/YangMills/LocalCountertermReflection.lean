/- Local quadratic source counterterms preserve reflection Gram positivity on
strictly separated Schwartz sources, with either sign of the coefficient.
This is an exact generating-functional identity. It does not choose physical
counterterm coefficients or supply bounds for differentiated hierarchies. -/
import UnifiedTheory.Clay.YangMills.DiagonalContactTerms
import UnifiedTheory.Clay.YangMills.PositiveKernelForm
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.LocalCountertermReflection
noncomputable section
open MeasureTheory ContinuumControl PeriodicLattice4
open AffineCellReflection CellReflectionCovariance SchwartzConfigurationConjugation
open DiagonalContactTerms CountableCorrelationCompactness

/-- The local quadratic source term, with no complex conjugation: this is
holomorphic in the source and restricts to the usual square for real sources. -/
def localSquare (f : CorrelationTest 1) : ℂ := ∫ x, (f x)^2

theorem square_integrable (f : CorrelationTest 1) :
    Integrable (fun x => (f x)^2) := by
  simpa only [pow_two] using f.integrable.bdd_mul f.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (SchwartzMap.norm_le_seminorm ℝ f))

theorem localSquare_zero : localSquare 0 = 0 := by simp [localSquare]

/-- Antilinear reflection on the actual one-point Schwartz test space. -/
def theta (a : ℝ) (plane : Plane) (f : CorrelationTest 1) : CorrelationTest 1 :=
  conjugation 1 (reflectionPullback 1 a plane f)

theorem theta_apply (a : ℝ) (plane : Plane) (f : CorrelationTest 1)
    (x : Configuration 1) : theta a plane f x = star (f (reflectPoints 1 a plane x)) := by
  simp only [theta, conjugation_apply, reflectionPullback_apply]

theorem localSquare_theta (a : ℝ) (plane : Plane) (f : CorrelationTest 1) :
    localSquare (theta a plane f) = star (localSquare f) := by
  have hi := (reflection_preserves_volume 1 a plane).integral_comp
    (reflectionEquiv 1 a plane).measurableEmbedding (fun x => (f x)^2)
  unfold localSquare
  simp only [theta_apply, Complex.star_def, ← map_pow]
  rw [integral_conj]
  exact congrArg (starRingEnd ℂ) hi

/-- Reflection and positive-time support force the mixed local product to vanish. -/
theorem mixed_product_zero (tau a : ℝ) (plane : Plane) (f g : CorrelationTest 1)
    (hf : SupportedAfter tau f) (hg : SupportedAfter tau g)
    (hgap : cellOffset a plane < 2 * tau) (x : Configuration 1) :
    theta a plane f x * g x = 0 := by
  by_cases hgx : g x = 0
  · simp [hgx]
  by_cases hfx : f (reflectPoints 1 a plane x) = 0
  · simp [theta_apply, hfx]
  have ht := hf (reflectPoints 1 a plane x) hfx
  have hs := hg x hgx
  change tau ≤ cellOffset a plane - x (0,0) at ht
  change tau ≤ x (0,0) at hs
  linarith

def sourcePair (a : ℝ) (plane : Plane) (f g : CorrelationTest 1) : CorrelationTest 1 :=
  theta a plane f + g

/-- The local square has no cross-half contribution, including at nonzero
lattice reflection offset when the actual support gap is positive. -/
theorem localSquare_pair (tau a : ℝ) (plane : Plane) (f g : CorrelationTest 1)
    (hf : SupportedAfter tau f) (hg : SupportedAfter tau g)
    (hgap : cellOffset a plane < 2 * tau) :
    localSquare (sourcePair a plane f g) = star (localSquare f) + localSquare g := by
  have he : (fun x => (sourcePair a plane f g x)^2) =
      fun x => (theta a plane f x)^2 + (g x)^2 := by
    funext x
    change (theta a plane f x + g x)^2 = _
    have hz := mixed_product_zero tau a plane f g hf hg hgap x
    calc
      _ = (theta a plane f x)^2 + (g x)^2 + 2*(theta a plane f x*g x) := by ring
      _ = _ := by rw [hz]; ring
  unfold localSquare at ⊢
  rw [he, integral_add (square_integrable _) (square_integrable _)]
  exact congrArg (fun z => z + ∫ x, (g x)^2) (localSquare_theta a plane f)

/-- Either sign is allowed; the physical coefficient has not been selected. -/
def sourceFactor (c : ℝ) (f : CorrelationTest 1) : ℂ :=
  Complex.exp (-(c : ℂ) * localSquare f)

def renormalize (Z : CorrelationTest 1 → ℂ) (c : ℝ) (f : CorrelationTest 1) : ℂ :=
  sourceFactor c f * Z f

theorem sourceFactor_ne_zero (c : ℝ) (f : CorrelationTest 1) : sourceFactor c f ≠ 0 :=
  Complex.exp_ne_zero _

theorem sourceFactor_star (c : ℝ) (f : CorrelationTest 1) :
    star (sourceFactor c f) = Complex.exp (-(c : ℂ) * star (localSquare f)) := by
  simp only [sourceFactor, Complex.star_def, ← Complex.exp_conj, map_mul, map_neg,
    Complex.conj_ofReal]

theorem sourceFactor_pair (c tau a : ℝ) (plane : Plane) (f g : CorrelationTest 1)
    (hf : SupportedAfter tau f) (hg : SupportedAfter tau g)
    (hgap : cellOffset a plane < 2 * tau) :
    sourceFactor c (sourcePair a plane f g) = star (sourceFactor c f) * sourceFactor c g := by
  rw [sourceFactor, localSquare_pair tau a plane f g hf hg hgap, mul_add,
    Complex.exp_add, sourceFactor_star]
  rfl

theorem renormalize_pair (Z : CorrelationTest 1 → ℂ) (c tau a : ℝ) (plane : Plane)
    (f g : CorrelationTest 1) (hf : SupportedAfter tau f) (hg : SupportedAfter tau g)
    (hgap : cellOffset a plane < 2 * tau) :
    renormalize Z c (sourcePair a plane f g) =
      star (sourceFactor c f) * sourceFactor c g * Z (sourcePair a plane f g) := by
  rw [renormalize, sourceFactor_pair c tau a plane f g hf hg hgap]

/-- Strictly positive-time sources, with a uniform lower support edge. -/
def Source (tau : ℝ) := {f : CorrelationTest 1 // SupportedAfter tau f}

def pair (tau a : ℝ) (plane : Plane) (f g : Source tau) : CorrelationTest 1 :=
  sourcePair a plane f.val g.val

/-- Exact diagonal congruence of every finite reflection Gram form. -/
theorem gramValue_renormalize (Z : CorrelationTest 1 → ℂ) (c tau a : ℝ) (plane : Plane)
    (hgap : cellOffset a plane < 2 * tau) (N : ℕ) (f : Fin N → Source tau) (z : Fin N → ℂ) :
    gramValue (pair tau a plane) (renormalize Z c) N f z =
      gramValue (pair tau a plane) Z N f (fun i => z i * sourceFactor c (f i).val) := by
  unfold gramValue pair
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [renormalize_pair Z c tau a plane _ _ (f i).property (f j).property hgap, star_mul]
  ring

/-- Arbitrary real local quadratic counterterms preserve all finite source
reflection Gram forms, not just a diagonal two-point pairing. -/
theorem reflection_positive (Z : CorrelationTest 1 → ℂ) (c tau a : ℝ) (plane : Plane)
    (hgap : cellOffset a plane < 2 * tau) (hZ : GramPositive (pair tau a plane) Z) :
    GramPositive (pair tau a plane) (renormalize Z c) := by
  intro N f z
  rw [gramValue_renormalize Z c tau a plane hgap]
  exact hZ N f _

theorem renormalize_zero (Z : CorrelationTest 1 → ℂ) (c : ℝ) :
    renormalize Z c 0 = Z 0 := by simp [renormalize, sourceFactor, localSquare_zero]

theorem renormalize_add (Z : CorrelationTest 1 → ℂ) (c d : ℝ) :
    renormalize (renormalize Z c) d = renormalize Z (c+d) := by
  funext f
  simp only [renormalize, sourceFactor, ← mul_assoc, ← Complex.exp_add, Complex.ofReal_add]
  congr 2
  ring

theorem renormalize_cancel (Z : CorrelationTest 1 → ℂ) (c : ℝ) :
    renormalize (renormalize Z c) (-c) = Z := by
  rw [renormalize_add, add_neg_cancel]
  funext f
  simp [renormalize, sourceFactor]

/-- The operation cannot manufacture reflection positivity from its failure. -/
theorem reflection_positive_iff (Z : CorrelationTest 1 → ℂ) (c tau a : ℝ) (plane : Plane)
    (hgap : cellOffset a plane < 2 * tau) :
    GramPositive (pair tau a plane) (renormalize Z c) ↔ GramPositive (pair tau a plane) Z := by
  constructor
  · intro h
    have ht := reflection_positive (renormalize Z c) (-c) tau a plane hgap h
    rwa [renormalize_cancel] at ht
  · exact reflection_positive Z c tau a plane hgap

end
end UnifiedTheory.Clay.YangMills.LocalCountertermReflection
