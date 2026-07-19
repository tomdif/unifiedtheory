/-
  LayerB/LohmillerSlotinePredictionEGeneralizedSech.lean — Phase E3'.

  GENERALIZED 2-PARAMETER SECH FAMILY  r(x) = A · sech(B·x)  in the
  static matter-coupled curved Schrödinger equilibrium.  Extends E3
  (`r = sech(x/σ)`, i.e., A = 1, B = 1/σ) to a 2-parameter family.

  Headline (proved here):  For the generalized sech profile
      r_{A,B}(x) := A · sech(B·x),  (with A ≠ 0)
  the (derived) Ricci scalar of the emergent metric is

      R(x) = 2·(B/A)²    — CONSTANT in x, parametrized by the ratio.

  Special cases:
    • A = 1, B = 1/σ:  recovers E3 with R = 2/σ².
    • A = 1, B = 1:    R = 2 (normalized sech).
    • General (A, B): R depends only on the dimensional ratio B/A.

  Algebraic content (the derivation uses cosh² − sinh² = 1):
      r_x = −A·B·tanh(Bx)·sech(Bx) = −B·tanh(Bx)·r,
      r_xx = B²·r·(1 − 2·sech²(Bx)) = B²·r·(1 − 2·(r/A)²),
      r_x² − r·r_xx = B²·tanh²(Bx)·r² − B²·r²·(1 − 2·(r/A)²)
                   = B²·r²·(tanh² − 1 + 2·r²/A²)
                   = B²·r²·(−sech² + 2·sech²·A²/A²)    [tanh² − 1 = −sech²]
                   = B²·r⁴/A²
  Plugging into the family law  R = 2·(r_x² − r·r_xx)/r⁴  gives
      R = 2·B²/A².

  Internal-model framing (carrying E1/E2/E3/E4/E-family caveat
  forward):  the "Ricci scalar" here is the Ricci scalar of the
  emergent 1+1-dim conformal metric `g = r²·diag(−1,1)` constructed
  in `LohmillerSlotineBackreaction`.

  Zero sorry.  Standard axioms only.
-/
import UnifiedTheory.LayerB.LohmillerSlotinePredictionE1
import UnifiedTheory.LayerB.LohmillerSlotinePredictionE3
import UnifiedTheory.LayerB.LohmillerSlotinePredictionEFamily
import Mathlib.Analysis.Complex.Trigonometric

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.LohmillerSlotinePredictionEGeneralizedSech

open Real
open UnifiedTheory.LayerB.LohmillerSlotinePredictionE1
open UnifiedTheory.LayerB.LohmillerSlotinePredictionE3
open UnifiedTheory.LayerB.LohmillerSlotinePredictionEFamily

/-! ════════════════════════════════════════════════════════════════════════
    PART 1 — GENERALIZED SECH SCALARS.

    Same scalar-level convention as E3:  the chain-rule formulas are
    defined as independent functions, so algebraic identities hold
    regardless of any chain-rule verification.
    ════════════════════════════════════════════════════════════════════════ -/

/-- Generalized sech profile `r_{A,B}(x) := A · sech(B·x)`. -/
noncomputable def gSechProfile (A B x : ℝ) : ℝ :=
  A * (1 / Real.cosh (B * x))

/-- Spatial derivative (chain rule):
        `r_x = −A·B·sinh(Bx)/cosh²(Bx) = −B·tanh(Bx)·r`. -/
noncomputable def gSechProfile_x (A B x : ℝ) : ℝ :=
  -A * B * (Real.sinh (B * x) / (Real.cosh (B * x)) ^ 2)

/-- Second spatial derivative (chain rule):
        `r_xx = A·B²·(1 − 2·sech²(Bx))·sech(Bx)`. -/
noncomputable def gSechProfile_xx (A B x : ℝ) : ℝ :=
  A * B ^ 2 * (1 - 2 / (Real.cosh (B * x)) ^ 2) *
    (1 / Real.cosh (B * x))

/-- The generalized sech profile is positive iff `A > 0`
    (since `Real.cosh > 0`). -/
theorem gSechProfile_pos_of_A_pos (A B x : ℝ) (hA : 0 < A) :
    0 < gSechProfile A B x := by
  unfold gSechProfile
  have hc := Real.cosh_pos (B * x)
  positivity

/-- The generalized sech profile is nonzero iff `A ≠ 0`. -/
theorem gSechProfile_ne_zero (A B x : ℝ) (hA : A ≠ 0) :
    gSechProfile A B x ≠ 0 := by
  unfold gSechProfile
  have hc : Real.cosh (B * x) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  have h_inv : 1 / Real.cosh (B * x) ≠ 0 := one_div_ne_zero hc
  exact mul_ne_zero hA h_inv

/-- `cosh(Bx) ≠ 0` everywhere. -/
theorem cosh_Bx_ne_zero (B x : ℝ) : Real.cosh (B * x) ≠ 0 :=
  ne_of_gt (Real.cosh_pos _)

/-! ════════════════════════════════════════════════════════════════════════
    PART 2 — FAMILY LAW NUMERATOR  r_x² − r·r_xx = B²·r⁴/A².
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Key algebraic identity**:
        `r_x² − r·r_xx = (B²/A²) · r⁴`,
    plugging into the family law gives `R = 2·B²/A²`.
    Proved via cosh² − sinh² = 1. -/
theorem gSech_numerator_eq
    (A B x : ℝ) (hA : A ≠ 0) :
    (gSechProfile_x A B x) ^ 2
        - gSechProfile A B x * gSechProfile_xx A B x
      = (B ^ 2 / A ^ 2) * (gSechProfile A B x) ^ 4 := by
  unfold gSechProfile gSechProfile_x gSechProfile_xx
  have hc := cosh_Bx_ne_zero B x
  have hc2 : (Real.cosh (B * x)) ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hc4 : (Real.cosh (B * x)) ^ 4 ≠ 0 := pow_ne_zero 4 hc
  have hA2 : A ^ 2 ≠ 0 := pow_ne_zero 2 hA
  have hA4 : A ^ 4 ≠ 0 := pow_ne_zero 4 hA
  have h_id : (Real.cosh (B * x)) ^ 2 - (Real.sinh (B * x)) ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq (B * x)
  have h_sinh_sq :
      (Real.sinh (B * x)) ^ 2 = (Real.cosh (B * x)) ^ 2 - 1 := by linarith
  -- Distribute the square on the spatial-derivative term explicitly
  -- so we can substitute the sinh² identity.
  have h_left :
      (-A * B * (Real.sinh (B * x) / (Real.cosh (B * x)) ^ 2)) ^ 2
        = A ^ 2 * B ^ 2 * (Real.sinh (B * x)) ^ 2
            / (Real.cosh (B * x)) ^ 4 := by
    field_simp
  rw [h_left, h_sinh_sq]
  -- Now the goal only contains cosh terms.
  field_simp
  ring

/-! ════════════════════════════════════════════════════════════════════════
    PART 3 — RICCI SCALAR = 2·(B/A)², CONSTANT IN x.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **PHASE E3' HEADLINE — `R = 2·(B/A)²` FOR GENERALIZED SECH**.

    For the generalized sech profile `r_{A,B}(x) := A·sech(B·x)`
    (with `A ≠ 0`), the derived Ricci scalar from the family law is
    the constant  `R = 2·B²/A² = 2·(B/A)²`.

    This recovers E3's `R = 2/σ²` (with A = 1, B = 1/σ) and extends
    it:  R depends only on the dimensionless ratio `B/A`, not on the
    individual values. -/
theorem derivedRicci_gSech
    (A B x : ℝ) (hA : A ≠ 0) :
    derivedRicci (gSechProfile A B x)
                 (gSechProfile_x A B x)
                 (gSechProfile_xx A B x)
      = 2 * B ^ 2 / A ^ 2 := by
  unfold derivedRicci
  rw [gSech_numerator_eq A B x hA]
  have hr := gSechProfile_ne_zero A B x hA
  have hr4 : (gSechProfile A B x) ^ 4 ≠ 0 := pow_ne_zero 4 hr
  have hA2 : A ^ 2 ≠ 0 := pow_ne_zero 2 hA
  field_simp

/-- **Constancy of R**:  for any two points `x₁, x₂`, the generalized
    sech Ricci is the same value `2·(B/A)²` — formal homogeneity. -/
theorem derivedRicci_gSech_constant
    (A B x1 x2 : ℝ) (hA : A ≠ 0) :
    derivedRicci (gSechProfile A B x1)
                 (gSechProfile_x A B x1)
                 (gSechProfile_xx A B x1)
      = derivedRicci (gSechProfile A B x2)
                     (gSechProfile_x A B x2)
                     (gSechProfile_xx A B x2) := by
  rw [derivedRicci_gSech A B x1 hA, derivedRicci_gSech A B x2 hA]

/-- **Sign of R determined by `B/A`**:
      • `B = 0`  ⇒  `R = 0`  (degenerate: r is constant A).
      • `B ≠ 0` ⇒  `R > 0`  (positive curvature — de Sitter-like).
    No negative-R generalized sech profile exists with this ansatz. -/
theorem derivedRicci_gSech_nonneg
    (A B x : ℝ) (hA : A ≠ 0) :
    0 ≤ derivedRicci (gSechProfile A B x)
                     (gSechProfile_x A B x)
                     (gSechProfile_xx A B x) := by
  rw [derivedRicci_gSech A B x hA]
  have hA2_pos : 0 < A ^ 2 := by
    apply sq_pos_of_ne_zero
    exact hA
  have h_num_nn : 0 ≤ 2 * B ^ 2 := by positivity
  exact div_nonneg h_num_nn (le_of_lt hA2_pos)

/-! ════════════════════════════════════════════════════════════════════════
    PART 4 — CONSISTENCY WITH E3.

    Verify that the generalized result reduces correctly when
    A = 1, B = 1/σ, i.e., `gSechProfile 1 (1/σ) = sechProfile σ`.
    ════════════════════════════════════════════════════════════════════════ -/

/-- For `A = 1` and `B = 1/σ`, the generalized sech `gSechProfile`
    reduces to the σ-parameterized sech `sechProfile` (modulo the
    rewriting `(1/σ)·x = x/σ`). -/
theorem gSechProfile_specializes_to_sechProfile
    (σ x : ℝ) (hσ : σ ≠ 0) :
    gSechProfile 1 (1 / σ) x = sechProfile σ x := by
  unfold gSechProfile sechProfile
  rw [one_mul]
  congr 2
  rw [mul_comm, mul_one_div]

/-- **Consistency theorem** — R for the generalized sech with
    `A=1, B=1/σ` equals R for the original sech soliton (both `2/σ²`). -/
theorem derivedRicci_gSech_specializes
    (σ x : ℝ) (hσ : σ ≠ 0) :
    derivedRicci (gSechProfile 1 (1 / σ) x)
                 (gSechProfile_x 1 (1 / σ) x)
                 (gSechProfile_xx 1 (1 / σ) x)
      = 2 / σ ^ 2 := by
  rw [derivedRicci_gSech 1 (1 / σ) x one_ne_zero]
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  field_simp

/-! ════════════════════════════════════════════════════════════════════════
    PART 5 — STATUS / FRONTIER.

    Closed in this file:
      ✓ `gSechProfile`, `gSechProfile_x`, `gSechProfile_xx`.
      ✓ Positivity (for `A > 0`) + nonzero (for `A ≠ 0`).
      ✓ **`gSech_numerator_eq`** — key algebraic identity
        `r_x² − r·r_xx = B²·r⁴/A²` via cosh² − sinh² = 1.
      ✓ **`derivedRicci_gSech`** — headline `R = 2·B²/A²`.
      ✓ Constancy (`derivedRicci_gSech_constant`) and nonnegativity
        (`derivedRicci_gSech_nonneg`) corollaries.
      ✓ Consistency with E3 (specialization to A=1, B=1/σ).

    Family interpretation:
      The full 2-parameter family of generalized sechs all have
      constant Ricci, parametrized by the dimensionless ratio B/A:
        R = 2·(B/A)².
      So the LSBridge homogeneous-curvature family in 1D is naturally
      indexed by a single scalar — the curvature radius.

    Open continuations:
    • Identification with the orbit of E3 under conformal/scaling
      transformations:  is `r → A·r(B·x)` a symmetry of the LSBridge
      static matter-coupled curved equilibrium?
    • Lean-formal proof that the 2-parameter sech family is the FULL
      family of constant-positive-R solutions in 1D (Liouville
      uniqueness theorem at C > 0).
    ════════════════════════════════════════════════════════════════════════ -/

end UnifiedTheory.LayerB.LohmillerSlotinePredictionEGeneralizedSech
