/-
  Audit/KFCausalCSpecHighDensityLimit.lean   (Volume sector — Step 6, distortion → 0)

  Step 6 of the Hauptvermutung ladder: the proper-time distortion between two embeddings
  tends to zero as the sprinkling density increases (the diamonds shrink, so the
  curvature error β and count error ε both vanish).

  The F3-bypass (`KFCausalCSpecTwoEmbeddingProperTime`) traps the proper-time ratio in

      L(β,ε) ≤ τ₁/τ₂ ≤ U(β,ε),   L = 1/U,   U = ((1+β)(1+ε)/((1-β)(1-ε)))^(1/d) ≥ 1,

  a band symmetric about 1 under inversion.  This file proves:
    * `distortion_le_of_band` : trapped in `[1/U, U]` (U ≥ 1) forces `|τ₁/τ₂ - 1| ≤ U - 1`;
    * `highDensity_upperFactor_tendsto_one` : `U(β,ε) → 1` as `(β,ε) → (0,0)`;
    * `highDensity_distortion_tendsto_zero` : hence the distortion bound `U - 1 → 0`.

  Composed: as density → ∞ the errors → 0, the band collapses to `{1}`, and the two
  embeddings agree on proper time in the limit -- the quantitative statement of the
  Hauptvermutung's high-density isometry, modulo the still-open global gluing (Step 5).

  Zero sorry. Zero custom axioms.
-/
import Mathlib

set_option autoImplicit false

open Filter Topology

namespace UnifiedTheory.Audit.KFCausalCSpecHighDensityLimit

/-- **Distortion bound from the symmetric band.**  A ratio trapped in `[1/U, U]` with
`U ≥ 1` is within `U - 1` of `1`.  (`U = 1` gives exact agreement.) -/
theorem distortion_le_of_band (x U : ℝ) (hU : 1 ≤ U) (hlo : U⁻¹ ≤ x) (hhi : x ≤ U) :
    |x - 1| ≤ U - 1 := by
  have hUpos : 0 < U := by linarith
  have hUne : U ≠ 0 := hUpos.ne'
  rw [abs_le]
  refine ⟨?_, by linarith⟩
  have hkey : U⁻¹ - (2 - U) = (U - 1) ^ 2 / U := by field_simp; ring
  have hnn : 0 ≤ U⁻¹ - (2 - U) := by rw [hkey]; exact div_nonneg (sq_nonneg _) hUpos.le
  linarith

/-- **High-density collapse of the upper band factor.**  As the curvature and count errors
`(β, ε) → (0, 0)`, the upper band factor `U(β,ε) → 1`. -/
theorem highDensity_upperFactor_tendsto_one (d : ℕ) :
    Tendsto (fun p : ℝ × ℝ =>
        ((1 + p.1) * (1 + p.2) / ((1 - p.1) * (1 - p.2))) ^ ((d : ℝ)⁻¹))
      (𝓝 (0, 0)) (𝓝 1) := by
  have hcont : ContinuousAt
      (fun p : ℝ × ℝ => (1 + p.1) * (1 + p.2) / ((1 - p.1) * (1 - p.2))) (0, 0) := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · norm_num
  have hbase : Tendsto (fun p : ℝ × ℝ => (1 + p.1) * (1 + p.2) / ((1 - p.1) * (1 - p.2)))
      (𝓝 (0, 0)) (𝓝 1) := by
    convert hcont.tendsto using 2
    norm_num
  have hrpow : ContinuousAt (fun x : ℝ => x ^ ((d : ℝ)⁻¹)) 1 :=
    Real.continuousAt_rpow_const 1 _ (Or.inl one_ne_zero)
  have hcomp := (hrpow.tendsto).comp hbase
  simpa [Function.comp, Real.one_rpow] using hcomp

/-- **Distortion bound vanishes.**  The guaranteed proper-time distortion bound `U - 1`
tends to `0` as `(β, ε) → (0, 0)` -- the high-density limit of the Hauptvermutung band. -/
theorem highDensity_distortion_tendsto_zero (d : ℕ) :
    Tendsto (fun p : ℝ × ℝ =>
        ((1 + p.1) * (1 + p.2) / ((1 - p.1) * (1 - p.2))) ^ ((d : ℝ)⁻¹) - 1)
      (𝓝 (0, 0)) (𝓝 0) := by
  have := (highDensity_upperFactor_tendsto_one d).sub_const 1
  simpa using this

#print axioms distortion_le_of_band
#print axioms highDensity_upperFactor_tendsto_one
#print axioms highDensity_distortion_tendsto_zero

end UnifiedTheory.Audit.KFCausalCSpecHighDensityLimit
