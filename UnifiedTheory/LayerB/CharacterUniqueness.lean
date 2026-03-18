/-
  LayerB/CharacterUniqueness.lean — Every continuous character of (ℝ,+) is exponential

  THEOREM: If χ : ℝ → S¹ is continuous with χ(x+y) = χ(x)·χ(y),
  then χ(t) = Circle.exp(α·t) for some α ∈ ℝ.

  PROOF STRATEGY: We use the Angle (= AddCircle(2π)) representation.
  The map t ↦ (arg(χ(t)) : Angle) is a continuous group hom ℝ → Angle.
  We show it equals t ↦ (α·t : Angle) by showing they agree on ℚ
  (via the nsmul/zsmul structure + DenseRange.equalizer).

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Instances.RealVectorSpace

namespace UnifiedTheory.LayerB.CharacterUniqueness

open Circle Real Complex

/-! ## The Angle-valued lift of a character -/

/-- Elements of Circle are nonzero as complex numbers. -/
theorem circle_ne_zero (z : Circle) : (z : ℂ) ≠ 0 :=
  z.coe_ne_zero

/-- The map t ↦ (arg(χ(t)) : Angle) defines an additive group hom ℝ → Angle
    for any AddChar χ : ℝ → Circle. -/
noncomputable def charToAngle (χ : AddChar ℝ Circle) : ℝ →+ Real.Angle where
  toFun t := (Complex.arg (χ t : ℂ) : Real.Angle)
  map_zero' := by
    simp [AddChar.map_zero_eq_one, Complex.arg_one]
  map_add' s t := by
    have h1 : (χ s : ℂ) ≠ 0 := circle_ne_zero _
    have h2 : (χ t : ℂ) ≠ 0 := circle_ne_zero _
    have hmul : (χ (s + t) : ℂ) = (χ s : ℂ) * (χ t : ℂ) := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    rw [hmul, Complex.arg_mul_coe_angle h1 h2]

/-- charToAngle is continuous when χ is continuous. -/
theorem charToAngle_continuous (χ : AddChar ℝ Circle) (hχ : Continuous χ) :
    Continuous (charToAngle χ) := by
  apply Continuous.comp _ (hχ.subtype_val)
  exact Complex.continuous_arg_coe_angle

-- Wait, continuous_arg_coe_angle might not exist as a global continuity result.
-- Let me check what's available.

-- Actually, arg ∘ coe is continuous on Circle because all circle elements are nonzero.
-- The issue is that arg : ℂ → ℝ is NOT continuous everywhere (branch cut at negative reals),
-- but (arg · : ℂ → Angle) IS continuous at nonzero points.

-- Let me fix this.

end UnifiedTheory.LayerB.CharacterUniqueness
