/-
  LayerB/LohmillerSlotinePredictionEFullNoGo.lean — Phase E5b.

  FULL ODE-LEVEL NEGATIVE-R IMPOSSIBILITY THEOREM.

  Extends the IsLocalMax bridge (Part 5–6 of the negativity no-go file)
  to a fully global statement:

    **There is no `C²` function `r : ℝ → ℝ` with `r ∈ [m, M]` globally
    (with `0 < m` and `M < ∞`) satisfying the constant-R relation
    `(r_x)² − r·r_xx = C·r⁴` for some `C < 0`.**

  Proof strategy (Taylor approach, staying in `r` directly):
    (1) From the constraint:  `r·r_xx = r_x² − C·r⁴ ≥ −C·r⁴ ≥ −C·m⁴ > 0`.
        Using `r ≤ M`:  `r_xx ≥ −C·m⁴ / M =: d > 0`  uniformly.
    (2) By Mathlib's `Convex.mul_sub_le_image_sub_of_le_deriv`
        (applied to `deriv r` with constant lower bound `d`):
        `deriv r y ≥ deriv r 0 + d · y`  for  `y ≥ 0`.
    (3) Define `F(y) := r(y) − r(0) − (deriv r 0) · y − (d/2) · y²`.
        Then `deriv F y = deriv r y − deriv r 0 − d · y ≥ 0`  for  `y ≥ 0`,
        so `F` is non-decreasing on `[0, ∞)`, and `F(y) ≥ F(0) = 0`.
        Hence  `r(y) ≥ r(0) + (deriv r 0) · y + (d/2) · y²`.
    (4) As `y → ∞`, the quadratic RHS exceeds any constant `M`.
        Contradiction with `r ≤ M`.

  Combined with the existing IsLocalMax-bridged no-go (compact intervals
  / max-attaining profiles), this fully closes the constant-negative-R
  obstruction for globally smooth bounded positive profiles on ℝ.

  Zero sorry.  Standard axioms only.
-/
import UnifiedTheory.LayerB.LohmillerSlotinePredictionENegativityNoGo
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.Order.DenselyOrdered

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.LohmillerSlotinePredictionEFullNoGo

open Real Filter Topology Set
open UnifiedTheory.LayerB.LohmillerSlotinePredictionEFamily
open UnifiedTheory.LayerB.LohmillerSlotinePredictionENegativityNoGo

/-! ════════════════════════════════════════════════════════════════════════
    PART 1 — AUXILIARY:  QUADRATIC LOWER BOUND FROM UNIFORM CONVEXITY.

    For a C² function with uniformly positive second derivative
    `deriv (deriv f) ≥ d > 0`, the function grows at least quadratically
    on [0, ∞):
        `f(y) ≥ f(0) + (deriv f 0) · y + (d/2) · y²`  for  `y ≥ 0`.

    The proof uses two applications of
    `Convex.mul_sub_le_image_sub_of_le_deriv`:
      (i) to `deriv f` with constant lower bound `d` on [0, ∞), giving
          `deriv f y ≥ deriv f 0 + d · y`  for  `y ≥ 0`;
     (ii) to `F(y) := f(y) − f(0) − (deriv f 0)·y − (d/2)·y²` with
          deriv ≥ 0 on `(0, ∞)`, giving `F(y) ≥ F(0) = 0` for `y ≥ 0`.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Uniform-convexity quadratic lower bound** on `[0, ∞)`. -/
theorem quadratic_lower_bound_of_unif_convex
    {f : ℝ → ℝ} {d : ℝ} (hd : 0 < d)
    (h_diff : ContDiff ℝ 2 f)
    (h_ff : ∀ x, d ≤ deriv (deriv f) x)
    {y : ℝ} (hy : 0 ≤ y) :
    f 0 + deriv f 0 * y + (d / 2) * y ^ 2 ≤ f y := by
  -- Differentiability facts.
  have h_diff_f : Differentiable ℝ f :=
    h_diff.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have h_diff_d : Differentiable ℝ (deriv f) := by
    have h_d := ContDiff.differentiable_iteratedDeriv 1 h_diff
                  (by norm_num : (1 : WithTop ℕ∞) < 2)
    rwa [iteratedDeriv_one] at h_d
  -- Step (i):  (deriv f) y ≥ (deriv f 0) + d · y  for y ≥ 0.
  have h_step_i : deriv f 0 + d * y ≤ deriv f y := by
    have h := mul_sub_le_image_sub_of_le_deriv h_diff_d h_ff hy
    linarith
  -- Define the auxiliary F.
  let F : ℝ → ℝ := fun z => f z - f 0 - deriv f 0 * z - (d / 2) * z ^ 2
  -- Compute deriv F at each z.
  have h_HasDeriv_F : ∀ z, HasDerivAt F (deriv f z - deriv f 0 - d * z) z := by
    intro z
    have hf : HasDerivAt (fun z => f z) (deriv f z) z :=
      h_diff_f.differentiableAt.hasDerivAt
    have h_const : HasDerivAt (fun _ : ℝ => f 0) 0 z := hasDerivAt_const z (f 0)
    have h_lin : HasDerivAt (fun z => deriv f 0 * z) (deriv f 0) z := by
      have := (hasDerivAt_id z).const_mul (deriv f 0)
      simpa using this
    have h_z_sq : HasDerivAt (fun z => z ^ 2) (2 * z) z := by
      have := hasDerivAt_pow 2 z
      simpa using this
    have h_quad : HasDerivAt (fun z => (d / 2) * z ^ 2) (d * z) z := by
      have := h_z_sq.const_mul (d / 2)
      convert this using 1
      ring
    -- F z = f z - f 0 - deriv f 0 * z - (d/2) * z^2.
    have := ((hf.sub h_const).sub h_lin).sub h_quad
    convert this using 1
    ring
  have h_diff_F : Differentiable ℝ F := fun z => (h_HasDeriv_F z).differentiableAt
  have h_deriv_F : ∀ z, deriv F z = deriv f z - deriv f 0 - d * z := fun z =>
    (h_HasDeriv_F z).deriv
  -- Step (ii):  on [0, ∞), deriv F ≥ 0,  so F is non-decreasing.
  -- Need to use Convex.mul_sub_le_image_sub_of_le_deriv with D = Ici 0 and C = 0.
  have h_F_mono : (0 : ℝ) * (y - 0) ≤ F y - F 0 := by
    apply Convex.mul_sub_le_image_sub_of_le_deriv (convex_Ici 0)
        h_diff_F.continuous.continuousOn h_diff_F.differentiableOn
    · intro z hz
      rw [interior_Ici] at hz
      have hz_le : 0 ≤ z := le_of_lt hz
      have h_step_i_z : deriv f 0 + d * z ≤ deriv f z := by
        have h := mul_sub_le_image_sub_of_le_deriv h_diff_d h_ff hz_le
        linarith
      rw [h_deriv_F z]
      linarith
    · exact Set.left_mem_Ici
    · exact hy
    · exact hy
  -- F 0 = 0:
  have h_F_zero : F 0 = 0 := by
    show f 0 - f 0 - deriv f 0 * 0 - (d / 2) * 0 ^ 2 = 0
    ring
  -- Rearrange:  F y ≥ 0  ⇒  f y ≥ f 0 + (deriv f 0)·y + (d/2)·y².
  have h_F_y : 0 ≤ F y := by linarith [h_F_zero]
  -- F y = f y - f 0 - deriv f 0 * y - (d/2) * y^2.
  show f 0 + deriv f 0 * y + (d / 2) * y ^ 2 ≤ f y
  have : F y = f y - f 0 - deriv f 0 * y - (d / 2) * y ^ 2 := rfl
  linarith

/-! ════════════════════════════════════════════════════════════════════════
    PART 2 — LSBridge FULL NEGATIVE-R NO-GO.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Full negative-R no-go**:  there is NO `C²` function `r : ℝ → ℝ`
    with `r(x) ∈ [m, M]` globally (with `0 < m ≤ M`) satisfying the
    constant-R relation `(deriv r x)² − r x · (deriv (deriv r) x) = C · (r x)⁴`
    for some `C < 0` and all `x`.

    This is the **structural completion of the LSBridge constant-R
    classification**:
      • R ≡ 0  achievable (E4 exponential).
      • R ≡ 2C > 0  achievable (E-Gen-Sech with B/A = √C).
      • R ≡ 2C < 0  NOT achievable for ANY globally bounded smooth
        positive profile. -/
theorem no_global_smooth_bounded_negative_R
    (r : ℝ → ℝ) (m M C : ℝ)
    (hm : 0 < m) (hmM : m ≤ M)
    (hC : C < 0)
    (h_diff : ContDiff ℝ 2 r)
    (h_lower : ∀ x, m ≤ r x)
    (h_upper : ∀ x, r x ≤ M)
    (h_const_R :
      ∀ x, (deriv r x) ^ 2 - r x * deriv (deriv r) x = C * (r x) ^ 4) :
    False := by
  -- Step 1:  derive r_xx ≥ d > 0 uniformly.
  have hM_pos : 0 < M := lt_of_lt_of_le hm hmM
  set d := -C * m ^ 4 / M with hd_def
  have hd_pos : 0 < d := by
    have h_num_pos : 0 < -C * m ^ 4 := by
      have h_neg_C_pos : 0 < -C := by linarith
      have h_m4_pos : 0 < m ^ 4 := by positivity
      exact mul_pos h_neg_C_pos h_m4_pos
    exact div_pos h_num_pos hM_pos
  have h_rxx_uniform : ∀ x, d ≤ deriv (deriv r) x := by
    intro x
    have h_constraint := h_const_R x
    -- r·r_xx = r_x² - C·r⁴ ≥ -C·r⁴ ≥ -C·m⁴.
    have h_rprime_sq_nn : 0 ≤ (deriv r x) ^ 2 := sq_nonneg _
    have h_r_pos : 0 < r x := lt_of_lt_of_le hm (h_lower x)
    have h_r_ne : r x ≠ 0 := ne_of_gt h_r_pos
    have h_r4_lb : m ^ 4 ≤ (r x) ^ 4 := by
      have h1 : 0 ≤ m := le_of_lt hm
      have h2 : m ≤ r x := h_lower x
      have h_pow_mono : m ^ 4 ≤ (r x) ^ 4 := pow_le_pow_left₀ h1 h2 4
      exact h_pow_mono
    -- r·r_xx = r_x² - C·r⁴ ≥ -C·r⁴ ≥ -C·m⁴.
    have h_rrxx_lb : -C * m ^ 4 ≤ r x * deriv (deriv r) x := by
      have h_neg_C_pos : 0 < -C := by linarith
      have h_C_r4_le_C_m4 : C * (r x) ^ 4 ≤ C * m ^ 4 := by
        have : -C * m ^ 4 ≤ -C * (r x) ^ 4 :=
          mul_le_mul_of_nonneg_left h_r4_lb (le_of_lt h_neg_C_pos)
        linarith
      -- r_x² ≥ 0, so r_x² - C·r⁴ ≥ -C·r⁴ ≥ -C·m⁴.
      linarith [h_constraint]
    -- r·r_xx ≥ -C·m⁴ and r ≤ M ⟹ r_xx ≥ -C·m⁴/M = d.
    -- This requires r·r_xx ≥ -C·m⁴ AND r ≤ M ⟹ r_xx ≥ -C·m⁴/M.
    -- Standard:  if a·b ≥ k > 0 and 0 < a ≤ M, then b ≥ k/M.
    have h_rxM : r x * deriv (deriv r) x ≤ M * deriv (deriv r) x ∨
                 deriv (deriv r) x ≤ 0 := by
      by_cases h_pos : 0 ≤ deriv (deriv r) x
      · left
        exact mul_le_mul_of_nonneg_right (h_upper x) h_pos
      · right; linarith
    rcases h_rxM with h_le | h_neg
    · -- r·r_xx ≤ M·r_xx, combined with r·r_xx ≥ -C·m⁴, gives M·r_xx ≥ -C·m⁴.
      have h_M_rxx : -C * m ^ 4 ≤ M * deriv (deriv r) x := by linarith
      have h_d_le : d ≤ deriv (deriv r) x := by
        rw [hd_def]
        exact (div_le_iff₀ hM_pos).mpr (by linarith)
      exact h_d_le
    · -- r_xx ≤ 0 ⟹ r·r_xx ≤ 0 (since r > 0) ⟹ -C·m⁴ ≤ 0, contradicting C < 0 ∧ m > 0.
      exfalso
      have h_r_rxx_le : r x * deriv (deriv r) x ≤ 0 := by
        have h_r_pos' : 0 ≤ r x := le_of_lt h_r_pos
        exact mul_nonpos_of_nonneg_of_nonpos h_r_pos' h_neg
      have h_neg_C_m4_pos : 0 < -C * m ^ 4 := by
        have h_neg_C : 0 < -C := by linarith
        have h_m4 : 0 < m ^ 4 := by positivity
        exact mul_pos h_neg_C h_m4
      linarith
  -- Step 2:  By the quadratic lower bound, r y ≥ r 0 + r'(0)·y + (d/2)·y² for y ≥ 0.
  -- For y large enough, the RHS exceeds M, contradicting r y ≤ M.
  -- Specifically, pick y such that (d/2)·y² > M + |r'(0)·y| + ... — but easier to use:
  -- (d/2)·y² → ∞, so eventually exceeds M - r 0 + |r'(0)| · y, etc.
  -- Pick y = max(1, 2·(M + |deriv r 0|)/d + 1) ?  Just exhibit a specific y.
  -- Simpler:  pick y₀ such that  d/2 · y₀² - |deriv r 0| · y₀ - r 0 - M > 0.
  -- The simplest construction: take y₀ very large.
  -- Use the auxiliary lemma to get the bound, then derive contradiction.
  -- For y ≥ 0, r y ≥ r 0 + deriv r 0 · y + (d/2)·y², and r y ≤ M.
  -- Hence r 0 + deriv r 0 · y + (d/2)·y² ≤ M for all y ≥ 0.
  -- Picking y = 1 + |deriv r 0| / d + 2 · M / d  (sufficient large), we'll get contradiction.
  -- Or use Tendsto: as y → ∞, the lower bound diverges, contradicting r ≤ M.
  -- Direct construction:
  --   Let y₀ = 2 * (|deriv r 0| + |r 0| + M + 1) / d  + 1.
  --   Then (d/2)·y₀² ≥ (d/2) · y₀ · y₀ ≥ y₀ · (|deriv r 0| + |r 0| + M + 1).
  --   And deriv r 0 · y₀ ≥ -|deriv r 0| · y₀.
  --   So r 0 + deriv r 0 · y₀ + (d/2)·y₀² ≥ r 0 - |deriv r 0|·y₀ + y₀ · (|deriv r 0| + |r 0| + M + 1)
  --     = r 0 + y₀ · (|r 0| + M + 1) ≥ r 0 + 1·(|r 0| + M + 1)
  --     = r 0 + |r 0| + M + 1 ≥ M + 1 > M.  Contradiction.
  -- But this requires y₀ ≥ 1 — which holds since y₀ ≥ 1.
  -- Let me use a specific y₀:
  set y₀ := 2 * (|deriv r 0| + |r 0| + M + 1) / d + 1 with hy₀_def
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  have h_d_pos_inv : 0 < 2 * (|deriv r 0| + |r 0| + M + 1) / d := by
    apply div_pos
    · have h1 : 0 ≤ |deriv r 0| := abs_nonneg _
      have h2 : 0 ≤ |r 0| := abs_nonneg _
      linarith
    · exact hd_pos
  have hy₀_pos : 0 ≤ y₀ := by rw [hy₀_def]; linarith
  have hy₀_ge_one : 1 ≤ y₀ := by rw [hy₀_def]; linarith
  -- Apply the quadratic lower bound at y = y₀.
  have h_lb := quadratic_lower_bound_of_unif_convex hd_pos h_diff h_rxx_uniform hy₀_pos
  -- h_lb : r 0 + deriv r 0 * y₀ + (d / 2) * y₀ ^ 2 ≤ r y₀.
  have h_r_y_upper : r y₀ ≤ M := h_upper y₀
  -- Derive a contradiction from the lower bound on r y₀ exceeding M.
  -- Show:  M < r 0 + deriv r 0 * y₀ + (d / 2) * y₀ ^ 2.
  -- Use:  deriv r 0 * y₀ ≥ -|deriv r 0| * y₀  and  (d/2)·y₀ · y₀ ≥ y₀ · (|deriv r 0| + |r 0| + M + 1).
  -- Plus r 0 ≥ -|r 0|.
  have h_lhs_lower : M + 1 ≤ r 0 + deriv r 0 * y₀ + (d / 2) * y₀ ^ 2 := by
    have h_abs_r0 : -|r 0| ≤ r 0 := neg_abs_le _
    have h_abs_dr0 : -|deriv r 0| ≤ deriv r 0 := neg_abs_le _
    -- (d/2)·y₀² = (d·y₀/2)·y₀.  And (d·y₀/2) ≥ |deriv r 0| + |r 0| + M + 1 from y₀'s definition.
    have h_half_d_y0 : |deriv r 0| + |r 0| + M + 1 ≤ d * y₀ / 2 := by
      rw [hy₀_def]
      have : d * (2 * (|deriv r 0| + |r 0| + M + 1) / d + 1)
              = 2 * (|deriv r 0| + |r 0| + M + 1) + d := by
        field_simp
      rw [show d * (2 * (|deriv r 0| + |r 0| + M + 1) / d + 1) / 2
              = (2 * (|deriv r 0| + |r 0| + M + 1) + d) / 2 by rw [this]]
      have h_d_half_pos : 0 < d / 2 := by linarith
      linarith
    have h_quad_bound : (|deriv r 0| + |r 0| + M + 1) * y₀ ≤ (d / 2) * y₀ ^ 2 := by
      have : (d / 2) * y₀ ^ 2 = (d * y₀ / 2) * y₀ := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right h_half_d_y0 hy₀_pos
    -- Now combine:
    -- r 0 + deriv r 0 · y₀ + (d/2)·y₀²
    --   ≥ -|r 0| + (-|deriv r 0|·y₀) + (|deriv r 0| + |r 0| + M + 1)·y₀
    --   = -|r 0| + y₀·(M + 1 + |r 0|)
    --   ≥ M + 1  (using y₀ ≥ 1).
    have h1 : -|deriv r 0| * y₀ ≤ deriv r 0 * y₀ :=
      mul_le_mul_of_nonneg_right h_abs_dr0 hy₀_pos
    nlinarith [h_abs_r0, h_quad_bound, h1, hy₀_ge_one,
               abs_nonneg (deriv r 0), abs_nonneg (r 0)]
  linarith

/-! ════════════════════════════════════════════════════════════════════════
    PART 3 — CLASSIFICATION COMPLETION SUMMARY.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **LSBridge constant-R classification — FULL VERSION**.

    The constant-R classification is now COMPLETE for globally smooth
    bounded positive profiles on ℝ:
      • R ≡ 0:    achieved by exponential family (E4).
      • R ≡ 2C, C > 0:  achieved by generalized sech family with B/A = √C.
      • R ≡ 2C, C < 0:  **NOT achievable** for any C² function
        `r : ℝ → ℝ` with `m ≤ r ≤ M` globally (and `0 < m`).

    This theorem packages the no-go in the form:  "if `r` is C²-bounded
    positive globally, then the conserved scalar `R/2 = (r_x² − r·r_xx)/r⁴`
    cannot be a strictly negative constant." -/
theorem LSBridge_no_global_smooth_bounded_negative_R
    (r : ℝ → ℝ) (m M : ℝ)
    (hm : 0 < m) (hmM : m ≤ M)
    (h_diff : ContDiff ℝ 2 r)
    (h_lower : ∀ x, m ≤ r x)
    (h_upper : ∀ x, r x ≤ M) :
    ¬ ∃ C : ℝ, C < 0 ∧
      ∀ x, (deriv r x) ^ 2 - r x * deriv (deriv r) x = C * (r x) ^ 4 := by
  rintro ⟨C, hC, h_const_R⟩
  exact no_global_smooth_bounded_negative_R r m M C hm hmM hC h_diff
    h_lower h_upper h_const_R

/-! ════════════════════════════════════════════════════════════════════════
    PART 4 — STATUS / FRONTIER.

    Closed in this file:
      ✓ `quadratic_lower_bound_of_unif_convex` — auxiliary analysis:
        uniformly-convex C² function has quadratic lower bound on `[0,∞)`.
      ✓ `no_global_smooth_bounded_negative_R` — the full no-go.
      ✓ `LSBridge_no_global_smooth_bounded_negative_R` — packaged
        classification-completion theorem.

    Classification status (final):

      ┌──────────────┬──────────────────────────────────┬────────────────┐
      │ R value      │ Family                            │ Achievable?    │
      ├──────────────┼──────────────────────────────────┼────────────────┤
      │ R ≡ 0        │ E4 exponential `exp(αx+β)`        │ YES (witness)  │
      │ R ≡ 2C > 0   │ E-Gen-Sech `A·sech(Bx)`           │ YES (witness)  │
      │ R ≡ 2C < 0   │ —                                 │ NO globally    │
      └──────────────┴──────────────────────────────────┴────────────────┘

      The "NO globally" verdict is now formally established:  no C²
      function `r : ℝ → ℝ` bounded above and below away from zero
      can have constant negative R.

    This closes the structural classification side of the LSBridge
    program.  Combined with the σ(t) dynamics file's closure of the
    dynamic side, the LSBridge framework now has its complete
    classification + dynamical-prediction theorem package.

    Open continuations (post-classification):
    • Quantitative size estimates:  given `r ∈ [m, M]` and `r_xx ≥ d`,
      how big does `(M − r₀)` need to be for the contradiction to
      bite?  (Gives explicit `r_pertinent` ranges.)
    • Extension to non-globally-bounded but `r → const` at infinity.
    ════════════════════════════════════════════════════════════════════════ -/

end UnifiedTheory.LayerB.LohmillerSlotinePredictionEFullNoGo
