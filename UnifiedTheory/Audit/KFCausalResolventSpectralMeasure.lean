/- Scalar spectral measures constructed from bounded self-adjoint operators.
The measure is obtained from continuous functional calculus and the
Riesz--Markov theorem, not supplied as a hypothesis. -/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalResolventSpectralMeasure
noncomputable section
open MeasureTheory
open scoped InnerProduct
open scoped CompactlySupported

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
variable (R : X →L[ℂ] X) (hs : IsSelfAdjoint R) (z : X)

def calculus : C(spectrum ℝ R, ℝ) →⋆ₐ[ℝ] (X →L[ℂ] X) := cfcHom hs

def expectation : C(spectrum ℝ R, ℝ) →ₗ[ℝ] ℝ where
  toFun f := (inner ℂ z (calculus R hs f z)).re
  map_add' f g := by simp [calculus, inner_add_right]
  map_smul' c f := by simp [calculus, inner_smul_right_eq_smul, Complex.real_smul]

theorem expectation_nonnegative (f : C(spectrum ℝ R, ℝ)) (hf : 0 ≤ f) :
    0 ≤ expectation R hs z f := by
  let g : C(spectrum ℝ R, ℝ) := ⟨fun x => Real.sqrt (f x), f.continuous.sqrt⟩
  have hgg : g * g = f := by
    ext x
    exact Real.mul_self_sqrt (hf x)
  have hA : IsSelfAdjoint (calculus R hs g) := cfcHom_predicate hs g
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  change 0 ≤ (inner ℂ z (calculus R hs f z)).re
  rw [← hgg, map_mul, ContinuousLinearMap.mul_apply]
  have he := hsym z (calculus R hs g z)
  change inner ℂ (calculus R hs g z) (calculus R hs g z) =
    inner ℂ z (calculus R hs g (calculus R hs g z)) at he
  rw [← he]
  exact inner_self_nonneg (𝕜 := ℂ) (x := calculus R hs g z)

def positiveExpectation : C_c(spectrum ℝ R, ℝ) →ₚ[ℝ] ℝ where
  toFun f := expectation R hs z f.toContinuousMap
  map_add' f g := (expectation R hs z).map_add _ _
  map_smul' c f := (expectation R hs z).map_smul c _
  monotone' f g hfg := by
    have hp := expectation_nonnegative R hs z
      (g.toContinuousMap - f.toContinuousMap) (sub_nonneg.mpr hfg)
    rw [map_sub] at hp
    exact sub_nonneg.mp hp

def spectralMeasure : Measure (spectrum ℝ R) :=
  RealRMK.rieszMeasure (positiveExpectation R hs z)

instance : IsFiniteMeasure (spectralMeasure R hs z) := by
  unfold spectralMeasure
  infer_instance

theorem integral_continuous (f : C(spectrum ℝ R, ℝ)) :
    ∫ x, f x ∂spectralMeasure R hs z = expectation R hs z f := by
  let fc : C_c(spectrum ℝ R, ℝ) := ⟨f, HasCompactSupport.of_compactSpace _⟩
  exact RealRMK.integral_rieszMeasure (positiveExpectation R hs z) fc

theorem expectation_one : expectation R hs z 1 = ‖z‖ ^ 2 := by
  change (inner ℂ z (calculus R hs 1 z)).re = _
  rw [map_one, ContinuousLinearMap.one_apply]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) z

theorem integral_one : ∫ _x, (1 : ℝ) ∂spectralMeasure R hs z = ‖z‖ ^ 2 := by
  exact (integral_continuous R hs z 1).trans (expectation_one R hs z)

theorem probability (hz : ‖z‖ = 1) : IsProbabilityMeasure (spectralMeasure R hs z) := by
  constructor
  have hi := integral_one R hs z
  simp only [hz, one_pow, integral_const, smul_eq_mul, mul_one] at hi
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.one_ne_top).mp
  simpa using hi

theorem moments (n : ℕ) :
    ∫ x, (x : ℝ) ^ n ∂spectralMeasure R hs z = (inner ℂ z ((R ^ n) z)).re := by
  let f : C(spectrum ℝ R, ℝ) := (ContinuousMap.id ℝ).restrict (spectrum ℝ R)
  have hi := integral_continuous R hs z (f ^ n)
  change ∫ x, (x : ℝ) ^ n ∂spectralMeasure R hs z =
    (inner ℂ z (calculus R hs (f ^ n) z)).re at hi
  rw [map_pow] at hi
  have hid : calculus R hs f = R := cfcHom_id hs
  rwa [hid] at hi

end
end UnifiedTheory.Audit.KFCausalResolventSpectralMeasure
