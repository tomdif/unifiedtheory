/- Genuine four-dimensional Poincare kinematics. The full affine Minkowski
isometry group and its proper orthochronous subgroup are geometric objects;
this module does not construct a quantum-field representation of either. -/
import UnifiedTheory.Clay.YangMills.LocalFields
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.PoincareKinematics
noncomputable section
open LocalFields

/-- All affine transformations preserving Minkowski squared intervals. This
includes parity and time reversal; physical unitary covariance will use the
proper orthochronous subgroup below. -/
def minkowskiIsometries : Subgroup (Spacetime ≃ᵃ[ℝ] Spacetime) where
  carrier := {e | ∀ x y, minkowskiSquare (e x - e y) = minkowskiSquare (x - y)}
  one_mem' := by intro x y; rfl
  mul_mem' := by
    intro e f he hf x y
    exact (he (f x) (f y)).trans (hf x y)
  inv_mem' := by
    intro e he x y
    simpa using (he (e.symm x) (e.symm y)).symm

abbrev Poincare := minkowskiIsometries

def transform (g : Poincare) : Spacetime ≃ᵃ[ℝ] Spacetime := g.val

@[simp] theorem transform_one (x : Spacetime) : transform 1 x = x := rfl

@[simp] theorem transform_mul (g h : Poincare) (x : Spacetime) :
    transform (g * h) x = transform g (transform h x) := rfl

@[simp] theorem transform_inv_apply (g : Poincare) (x : Spacetime) :
    transform g (transform g⁻¹ x) = x := (transform g).apply_symm_apply x

@[simp] theorem transform_apply_inv (g : Poincare) (x : Spacetime) :
    transform g⁻¹ (transform g x) = x := (transform g).symm_apply_apply x

theorem preserves_interval (g : Poincare) (x y : Spacetime) :
    minkowskiSquare (transform g x - transform g y) = minkowskiSquare (x - y) :=
  g.property x y

/-- Affine maps separate into their linear part and the image of the origin. -/
theorem affine_decomposition (e : Spacetime ≃ᵃ[ℝ] Spacetime) (x : Spacetime) :
    e x = e.linear x + e 0 := by
  simpa using e.map_vadd (0 : Spacetime) x

theorem affine_difference (e : Spacetime ≃ᵃ[ℝ] Spacetime) (x y : Spacetime) :
    e x - e y = e.linear (x - y) := by
  rw [affine_decomposition e x, affine_decomposition e y, map_sub]
  abel

theorem preserves_linear_square (g : Poincare) (x : Spacetime) :
    minkowskiSquare ((transform g).linear x) = minkowskiSquare x := by
  simpa only [affine_difference, sub_zero] using preserves_interval g x 0

/-- Translations are actual elements of the spacetime group. -/
def translation (a : Spacetime) : Poincare :=
  ⟨AffineEquiv.constVAdd ℝ Spacetime a, by
    intro x y
    change minkowskiSquare ((a + x) - (a + y)) = minkowskiSquare (x - y)
    congr 1
    abel⟩

@[simp] theorem translation_apply (a x : Spacetime) :
    transform (translation a) x = a + x := rfl

@[simp] theorem translation_zero : translation 0 = 1 := by
  apply Subtype.ext
  ext x
  simp [translation]

theorem translation_add (a b : Spacetime) :
    translation (a + b) = translation a * translation b := by
  apply Subtype.ext
  apply AffineEquiv.ext
  intro x
  change (a + b) + x = a + (b + x)
  exact add_assoc a b x

@[simp] theorem translation_inv (a : Spacetime) :
    (translation a)⁻¹ = translation (-a) := by
  apply Subtype.ext
  exact AffineEquiv.constVAdd_symm ℝ Spacetime a

theorem translation_injective : Function.Injective translation := by
  intro a b h
  have hx := congrArg (fun g : Poincare => transform g 0) h
  simpa using hx

theorem translation_ne_one {a : Spacetime} (ha : a ≠ 0) : translation a ≠ 1 := by
  intro h
  apply ha
  exact translation_injective (h.trans translation_zero.symm)

/-- The open future timelike cone in the (+---) convention. -/
def FutureTimelike (x : Spacetime) : Prop :=
  0 < minkowskiSquare x ∧ 0 < x 0

/-- Orientation of the linear part, as a multiplicative determinant. -/
def orientation : Poincare →* ℝˣ :=
  (LinearEquiv.det : (Spacetime ≃ₗ[ℝ] Spacetime) →* ℝˣ).comp
    (AffineEquiv.linearHom.comp minkowskiIsometries.subtype)

/-- The determinant-one, future-cone-preserving subgroup. The two-sided cone
condition makes the restriction precise without assuming inverse preservation. -/
def properOrthochronous : Subgroup Poincare where
  carrier := {g | orientation g = 1 ∧
    ∀ x, FutureTimelike ((transform g).linear x) ↔ FutureTimelike x}
  one_mem' := by
    constructor
    · exact map_one orientation
    · intro x; rfl
  mul_mem' := by
    intro g h hg hh
    constructor
    · rw [map_mul, hg.1, hh.1, one_mul]
    · intro x
      exact (hg.2 ((transform h).linear x)).trans (hh.2 x)
  inv_mem' := by
    intro g hg
    constructor
    · rw [map_inv, hg.1, inv_one]
    · intro x
      have hx := (hg.2 ((transform g).linear.symm x)).symm
      simpa only [LinearEquiv.apply_symm_apply] using hx

abbrev ProperPoincare := properOrthochronous

theorem translation_mem_proper (a : Spacetime) : translation a ∈ properOrthochronous := by
  constructor
  · change LinearEquiv.det (LinearEquiv.refl ℝ Spacetime) = 1
    exact LinearEquiv.det_refl
  · intro x; rfl

def properTranslation (a : Spacetime) : ProperPoincare :=
  ⟨translation a, translation_mem_proper a⟩

/-- Every affine spacetime equivalence is a homeomorphism in finite dimension. -/
def spacetimeHomeomorph (g : Poincare) : Spacetime ≃ₜ Spacetime :=
  (transform g).toHomeomorphOfFiniteDimensional

@[simp] theorem spacetimeHomeomorph_apply (g : Poincare) (x : Spacetime) :
    spacetimeHomeomorph g x = transform g x := rfl

theorem continuous_transform (g : Poincare) : Continuous (transform g) :=
  (transform g).continuous_of_finiteDimensional

/-- Polynomial growth and smoothness of genuine affine spacetime maps. -/
theorem affine_temperateGrowth (e : Spacetime ≃ᵃ[ℝ] Spacetime) :
    Function.HasTemperateGrowth e := by
  have h := e.linear.toContinuousLinearEquiv.hasTemperateGrowth.add
    (Function.HasTemperateGrowth.const (e 0))
  change Function.HasTemperateGrowth (fun x => e.linear x + e 0) at h
  convert h using 1
  funext x
  exact affine_decomposition e x

/-- The inverse linear operator norm controls distances even for a translated
affine map. This is the coercivity needed for Schwartz pullback. -/
theorem affine_antilipschitz (e : Spacetime ≃ᵃ[ℝ] Spacetime) :
    AntilipschitzWith
      ‖(e.linear.toContinuousLinearEquiv.symm : Spacetime →L[ℝ] Spacetime)‖₊ e := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  have h := e.linear.toContinuousLinearEquiv.antilipschitz.le_mul_dist x y
  simpa only [dist_eq_norm, ← map_sub, LinearEquiv.coe_toContinuousLinearEquiv',
    ← affine_difference] using h

end
end UnifiedTheory.Clay.YangMills.PoincareKinematics
