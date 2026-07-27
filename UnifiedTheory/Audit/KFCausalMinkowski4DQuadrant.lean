/-
  Audit/KFCausalMinkowski4DQuadrant.lean — the quadrant passage (step 1):
  uniform linear bounds on the two boundary lines

  From the kernel bounds:
  * `D1_bound_uniform`: |D1(ε,v)| ≤ a·(2v² + 2ε² + 3εv)·ε — the u-axis line of
    the rectangle identity dies linearly in ε, uniformly on 0 < v ≤ B;
  * `K_bound_uniform`: |𝒦(u,δ) + 1/6| ≤ a·(uδ² + u³ + (3/2)u²δ)·δ — the v-axis
    line converges to the −1/6 axis constant linearly in δ, uniformly on
    0 < u ≤ A.

  These are the rates that carry `corner4_rectangle_chain` to `(0,∞)²` by plain
  norm × strip-measure estimates — no dominated convergence.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowski4DKernelBounds
import UnifiedTheory.Audit.KFCausalMinkowski4DRectangleChain
import UnifiedTheory.Audit.KFCausalMinkowski4DDictionary

open Real
open UnifiedTheory.Audit.KFCausalMinkowski4DKernel
open UnifiedTheory.Audit.KFCausalMinkowski4DKernelBounds

namespace UnifiedTheory.Audit.KFCausalMinkowski4DQuadrant

/-- The `u`-axis line dies linearly: for `a ≥ 0`, `ε > 0`, `v ≠ 0`,
`|D1(ε,v)| ≤ a(2v² + 2ε² + 3ε|v|)·ε`. -/
theorem D1_bound_uniform (a ε v : ℝ) (ha : 0 ≤ a) (hε : 0 < ε) (hv : v ≠ 0) :
    |ε⁻¹ * G4 (a*ε^2*v^2) + ε * (v^2)⁻¹ * H4 (a*ε^2*v^2)
      - a*ε^2*v * K4d (a*ε^2*v^2)|
    ≤ a * (2*v^2 + 2*ε^2 + 3*ε*|v|) * ε := by
  have hz : 0 ≤ a*ε^2*v^2 := by positivity
  have h1 : |ε⁻¹ * G4 (a*ε^2*v^2)| ≤ 2*a*ε*v^2 := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hε)]
    calc ε⁻¹ * |G4 (a*ε^2*v^2)| ≤ ε⁻¹ * (2*(a*ε^2*v^2)) := by
          apply mul_le_mul_of_nonneg_left (G4_abs_le _ hz)
            (le_of_lt (inv_pos.mpr hε))
      _ = 2*a*ε*v^2 := by field_simp
  have h2 : |ε * (v^2)⁻¹ * H4 (a*ε^2*v^2)| ≤ 2*a*ε^3 := by
    have hv2 : (0:ℝ) < v^2 := by positivity
    rw [abs_mul, abs_mul, abs_of_pos hε, abs_of_pos (inv_pos.mpr hv2)]
    calc ε * (v^2)⁻¹ * |H4 (a*ε^2*v^2)| ≤ ε * (v^2)⁻¹ * (2*(a*ε^2*v^2)) := by
          apply mul_le_mul_of_nonneg_left (H4_abs_le _ hz) (by positivity)
      _ = 2*a*ε^3 := by field_simp
  have h3 : |a*ε^2*v * K4d (a*ε^2*v^2)| ≤ 3*a*ε^2*|v| := by
    rw [abs_mul]
    calc |a*ε^2*v| * |K4d (a*ε^2*v^2)| ≤ |a*ε^2*v| * 3 :=
          mul_le_mul_of_nonneg_left (K4d_abs_le _ hz) (abs_nonneg _)
      _ = 3*a*ε^2*|v| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg (sq_nonneg ε)]
          ring
  have hsum : a * (2*v^2 + 2*ε^2 + 3*ε*|v|) * ε
      = 2*a*ε*v^2 + 2*a*ε^3 + 3*a*ε^2*|v| := by ring
  rw [abs_le]
  constructor
  · linarith [h1, h2, h3, neg_abs_le (ε⁻¹ * G4 (a*ε^2*v^2)),
      neg_abs_le (ε * (v^2)⁻¹ * H4 (a*ε^2*v^2)),
      le_abs_self (a*ε^2*v * K4d (a*ε^2*v^2))]
  · linarith [h1, h2, h3, le_abs_self (ε⁻¹ * G4 (a*ε^2*v^2)),
      le_abs_self (ε * (v^2)⁻¹ * H4 (a*ε^2*v^2)),
      neg_abs_le (a*ε^2*v * K4d (a*ε^2*v^2))]

/-- The `v`-axis line converges linearly to the axis constant: for `a ≥ 0`,
`δ > 0`, `u ≠ 0`, `|𝒦(u,δ) + 1/6| ≤ a(|u|δ² + |u|³ + (3/2)u²δ)·δ`. -/
theorem K_bound_uniform (a u δ : ℝ) (ha : 0 ≤ a) (hδ : 0 < δ) (hu : u ≠ 0) :
    |(δ/u) * J4 (a*u^2*δ^2) + u * δ⁻¹ * J4 (a*u^2*δ^2)
      - (1/2) * K4 (a*u^2*δ^2) + 1/6|
    ≤ a * (|u| * δ^2 + |u|^3 + (3/2)*u^2*δ) * δ := by
  have hz : 0 ≤ a*u^2*δ^2 := by positivity
  have hK40 : K4 0 = 1/3 := by
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4
    norm_num
  have h1 : |(δ/u) * J4 (a*u^2*δ^2)| ≤ a * |u| * δ^3 := by
    rw [abs_mul, abs_div, abs_of_pos hδ]
    calc δ/|u| * |J4 (a*u^2*δ^2)| ≤ δ/|u| * (a*u^2*δ^2) := by
          apply mul_le_mul_of_nonneg_left (J4_abs_le _ hz) (by positivity)
      _ = a * |u| * δ^3 := by
          rw [div_mul_eq_mul_div, div_eq_iff (abs_ne_zero.mpr hu),
            show u^2 = |u|^2 from (sq_abs u).symm]
          ring
  have h2 : |u * δ⁻¹ * J4 (a*u^2*δ^2)| ≤ a * |u|^3 * δ := by
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hδ)]
    calc |u| * δ⁻¹ * |J4 (a*u^2*δ^2)| ≤ |u| * δ⁻¹ * (a*u^2*δ^2) := by
          apply mul_le_mul_of_nonneg_left (J4_abs_le _ hz) (by positivity)
      _ = a * |u|^3 * δ := by
          rw [show u^2 = |u|^2 from (sq_abs u).symm]
          field_simp
  have h3 : |(1/2) * K4 (a*u^2*δ^2) - 1/6| ≤ (3/2)*a*u^2*δ^2 := by
    have := K4_sub_K40_abs_le (a*u^2*δ^2) hz
    rw [hK40] at this
    calc |(1/2) * K4 (a*u^2*δ^2) - 1/6|
        = (1/2) * |K4 (a*u^2*δ^2) - 1/3| := by
          rw [← abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2), ← abs_mul]
          congr 1
          ring
      _ ≤ (1/2) * (3*(a*u^2*δ^2)) := by
          apply mul_le_mul_of_nonneg_left this (by norm_num)
      _ = (3/2)*a*u^2*δ^2 := by ring
  have hsum : a * (|u| * δ^2 + |u|^3 + (3/2)*u^2*δ) * δ
      = a * |u| * δ^3 + a * |u|^3 * δ + (3/2)*a*u^2*δ^2 := by ring
  rw [abs_le]
  constructor
  · linarith [h1, h2, h3, neg_abs_le ((δ/u) * J4 (a*u^2*δ^2)),
      neg_abs_le (u * δ⁻¹ * J4 (a*u^2*δ^2)),
      le_abs_self ((1/2) * K4 (a*u^2*δ^2) - 1/6)]
  · linarith [h1, h2, h3, le_abs_self ((δ/u) * J4 (a*u^2*δ^2)),
      le_abs_self (u * δ⁻¹ * J4 (a*u^2*δ^2)),
      neg_abs_le ((1/2) * K4 (a*u^2*δ^2) - 1/6)]

/-- **The u-axis strip estimate**: the boundary line of the rectangle identity
is `O(ε)` uniformly — `|∫_δ^B D1(ε,v)F(ε,v)dv| ≤ a(2B²+2ε²+3εB)ε·C_F·B`. -/
theorem strip_u_axis (a ε δ B CF : ℝ) (ha : 0 ≤ a) (hε : 0 < ε)
    (hδ : 0 < δ) (hδB : δ ≤ B) (F : ℝ → ℝ) (hCF : ∀ v, |F v| ≤ CF) :
    |∫ v in δ..B, (ε⁻¹ * G4 (a*ε^2*v^2) + ε * (v^2)⁻¹ * H4 (a*ε^2*v^2)
        - a*ε^2*v * K4d (a*ε^2*v^2)) * F v|
    ≤ a * (2*B^2 + 2*ε^2 + 3*ε*B) * ε * CF * B := by
  have hCF0 : 0 ≤ CF := le_trans (abs_nonneg _) (hCF 0)
  have hB : 0 < B := lt_of_lt_of_le hδ hδB
  have hbound : ∀ v ∈ Set.uIoc δ B,
      ‖(ε⁻¹ * G4 (a*ε^2*v^2) + ε * (v^2)⁻¹ * H4 (a*ε^2*v^2)
        - a*ε^2*v * K4d (a*ε^2*v^2)) * F v‖
      ≤ a * (2*B^2 + 2*ε^2 + 3*ε*B) * ε * CF := by
    intro v hv
    rw [Set.uIoc_of_le hδB] at hv
    have hv0 : 0 < v := lt_trans hδ hv.1
    have hvB : v ≤ B := hv.2
    rw [Real.norm_eq_abs, abs_mul]
    calc |ε⁻¹ * G4 (a*ε^2*v^2) + ε * (v^2)⁻¹ * H4 (a*ε^2*v^2)
          - a*ε^2*v * K4d (a*ε^2*v^2)| * |F v|
        ≤ (a * (2*v^2 + 2*ε^2 + 3*ε*|v|) * ε) * CF := by
          apply mul_le_mul (D1_bound_uniform a ε v ha hε (ne_of_gt hv0))
            (hCF v) (abs_nonneg _) (by positivity)
      _ ≤ a * (2*B^2 + 2*ε^2 + 3*ε*B) * ε * CF := by
          apply mul_le_mul_of_nonneg_right ?_ hCF0
          apply mul_le_mul_of_nonneg_right ?_ (le_of_lt hε)
          apply mul_le_mul_of_nonneg_left ?_ ha
          rw [abs_of_pos hv0]
          nlinarith [hv0, hvB, hε]
  calc |∫ v in δ..B, (ε⁻¹ * G4 (a*ε^2*v^2) + ε * (v^2)⁻¹ * H4 (a*ε^2*v^2)
        - a*ε^2*v * K4d (a*ε^2*v^2)) * F v|
      ≤ a * (2*B^2 + 2*ε^2 + 3*ε*B) * ε * CF * |B - δ| := by
        rw [← Real.norm_eq_abs]
        exact intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ ≤ a * (2*B^2 + 2*ε^2 + 3*ε*B) * ε * CF * B := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [abs_of_nonneg (by linarith)]
        linarith

/-- **The v-axis strip estimate — the counterterm emerges**: the boundary line
converges to `−(1/6)∫F_u(u,0)du` at rate `O(δ)`:

    |∫_ε^A 𝒦(u,δ)F_u(u,δ)du + (1/6)∫_ε^A F_u(u,0)du|
      ≤ (a(Aδ²+A³+(3/2)A²δ)δ·C + (1/6)Mδ)·A. -/
theorem strip_v_axis (a δ ε A CFu Mv : ℝ) (ha : 0 ≤ a) (hδ : 0 < δ)
    (hε : 0 < ε) (hεA : ε ≤ A) (Fu Fuv : ℝ → ℝ → ℝ)
    (hFuc : Continuous (Function.uncurry Fu))
    (hd : ∀ u v, HasDerivAt (fun v' => Fu u v') (Fuv u v) v)
    (hCFu : ∀ u v, |Fu u v| ≤ CFu) (hMv : ∀ u v, |Fuv u v| ≤ Mv) :
    |(∫ u in ε..A, ((δ/u) * J4 (a*u^2*δ^2) + u * δ⁻¹ * J4 (a*u^2*δ^2)
        - (1/2) * K4 (a*u^2*δ^2)) * Fu u δ)
      + (1/6) * ∫ u in ε..A, Fu u 0|
    ≤ (a * (A*δ^2 + A^3 + (3/2)*A^2*δ) * δ * CFu + (1/6)*Mv*δ) * A := by
  have hCFu0 : 0 ≤ CFu := le_trans (abs_nonneg _) (hCFu 0 0)
  have hMv0 : 0 ≤ Mv := le_trans (abs_nonneg _) (hMv 0 0)
  have hA : 0 < A := lt_of_lt_of_le hε hεA
  have hmvt : ∀ u, |Fu u δ - Fu u 0| ≤ Mv * δ := by
    intro u
    have h := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun v => Fu u v) (f' := fun v => Fuv u v) (C := Mv) (s := Set.univ)
      (fun v _ => (hd u v).hasDerivWithinAt)
      (fun v _ => by simpa [Real.norm_eq_abs] using hMv u v)
      (Set.mem_univ 0) (Set.mem_univ δ)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_pos hδ] at h
    exact h
  have hcomb : ((1:ℝ)/6) * ∫ u in ε..A, Fu u 0
      = ∫ u in ε..A, (1/6) * Fu u 0 := (intervalIntegral.integral_const_mul _ _).symm
  rw [hcomb, ← intervalIntegral.integral_add]
  · have hbound : ∀ u ∈ Set.uIoc ε A,
        ‖((δ/u) * J4 (a*u^2*δ^2) + u * δ⁻¹ * J4 (a*u^2*δ^2)
          - (1/2) * K4 (a*u^2*δ^2)) * Fu u δ + (1/6) * Fu u 0‖
        ≤ a * (A*δ^2 + A^3 + (3/2)*A^2*δ) * δ * CFu + (1/6)*Mv*δ := by
      intro u hu
      rw [Set.uIoc_of_le hεA] at hu
      have hu0 : 0 < u := lt_trans hε hu.1
      have huA : u ≤ A := hu.2
      have hsplit : ((δ/u) * J4 (a*u^2*δ^2) + u * δ⁻¹ * J4 (a*u^2*δ^2)
            - (1/2) * K4 (a*u^2*δ^2)) * Fu u δ + (1/6) * Fu u 0
          = (((δ/u) * J4 (a*u^2*δ^2) + u * δ⁻¹ * J4 (a*u^2*δ^2)
            - (1/2) * K4 (a*u^2*δ^2)) + 1/6) * Fu u δ
            - (1/6) * (Fu u δ - Fu u 0) := by ring
      rw [Real.norm_eq_abs, hsplit]
      have h1 : |(((δ/u) * J4 (a*u^2*δ^2) + u * δ⁻¹ * J4 (a*u^2*δ^2)
          - (1/2) * K4 (a*u^2*δ^2)) + 1/6) * Fu u δ|
          ≤ a * (A*δ^2 + A^3 + (3/2)*A^2*δ) * δ * CFu := by
        rw [abs_mul]
        calc |((δ/u) * J4 (a*u^2*δ^2) + u * δ⁻¹ * J4 (a*u^2*δ^2)
              - (1/2) * K4 (a*u^2*δ^2)) + 1/6| * |Fu u δ|
            ≤ (a * (|u| * δ^2 + |u|^3 + (3/2)*u^2*δ) * δ) * CFu := by
              apply mul_le_mul ?_ (hCFu u δ) (abs_nonneg _) (by positivity)
              exact K_bound_uniform a u δ ha hδ (ne_of_gt hu0)
          _ ≤ a * (A*δ^2 + A^3 + (3/2)*A^2*δ) * δ * CFu := by
              apply mul_le_mul_of_nonneg_right ?_ hCFu0
              apply mul_le_mul_of_nonneg_right ?_ (le_of_lt hδ)
              apply mul_le_mul_of_nonneg_left ?_ ha
              rw [abs_of_pos hu0]
              have hu2 : u^2 ≤ A^2 := by nlinarith
              have hu3 : u^3 ≤ A^3 := by
                nlinarith [mul_le_mul_of_nonneg_right hu2 (le_of_lt hu0),
                  mul_le_mul_of_nonneg_left huA (sq_nonneg A)]
              nlinarith [hu3, mul_le_mul_of_nonneg_right huA (sq_nonneg δ),
                mul_le_mul_of_nonneg_right hu2 (le_of_lt hδ)]
      have h2 : |(1/6 : ℝ) * (Fu u δ - Fu u 0)| ≤ (1/6)*Mv*δ := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/6)]
        calc (1/6) * |Fu u δ - Fu u 0| ≤ (1/6) * (Mv * δ) := by
              apply mul_le_mul_of_nonneg_left (hmvt u) (by norm_num)
          _ = (1/6)*Mv*δ := by ring
      rw [abs_le]
      constructor
      · linarith [h1, h2,
          neg_abs_le ((((δ/u) * J4 (a*u^2*δ^2) + u * δ⁻¹ * J4 (a*u^2*δ^2)
            - (1/2) * K4 (a*u^2*δ^2)) + 1/6) * Fu u δ),
          le_abs_self ((1/6 : ℝ) * (Fu u δ - Fu u 0))]
      · linarith [h1, h2,
          le_abs_self ((((δ/u) * J4 (a*u^2*δ^2) + u * δ⁻¹ * J4 (a*u^2*δ^2)
            - (1/2) * K4 (a*u^2*δ^2)) + 1/6) * Fu u δ),
          neg_abs_le ((1/6 : ℝ) * (Fu u δ - Fu u 0))]
    calc |∫ u in ε..A, (((δ/u) * J4 (a*u^2*δ^2) + u * δ⁻¹ * J4 (a*u^2*δ^2)
          - (1/2) * K4 (a*u^2*δ^2)) * Fu u δ + (1/6) * Fu u 0)|
        ≤ (a * (A*δ^2 + A^3 + (3/2)*A^2*δ) * δ * CFu + (1/6)*Mv*δ) * |A - ε| := by
          rw [← Real.norm_eq_abs]
          exact intervalIntegral.norm_integral_le_of_norm_le_const hbound
      _ ≤ (a * (A*δ^2 + A^3 + (3/2)*A^2*δ) * δ * CFu + (1/6)*Mv*δ) * A := by
          apply mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [abs_of_nonneg (by linarith)]
          linarith
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hεA]
    have hJC : Continuous J4 := by
      unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4
      fun_prop
    have hKC : Continuous K4 := by
      unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4
      fun_prop
    apply ContinuousOn.mul
    · apply ContinuousOn.sub
      · apply ContinuousOn.add
        · exact (continuousOn_const.div continuousOn_id
            (fun u hu => ne_of_gt (lt_of_lt_of_le hε hu.1))).mul
            (hJC.comp (by fun_prop : Continuous (fun u : ℝ => a*u^2*δ^2))).continuousOn
        · exact (continuousOn_id.mul continuousOn_const).mul
            (hJC.comp (by fun_prop : Continuous (fun u : ℝ => a*u^2*δ^2))).continuousOn
      · exact continuousOn_const.mul
          (hKC.comp (by fun_prop : Continuous (fun u : ℝ => a*u^2*δ^2))).continuousOn
    · exact (hFuc.comp (continuous_id.prodMk continuous_const)).continuousOn
  · exact (Continuous.intervalIntegrable (by
      exact continuous_const.mul (hFuc.comp (continuous_id.prodMk continuous_const))) _ _)

/-- **The gate kernel is bounded on boxes**: for `u, v > 0`,
`|𝒦(u,v)| ≤ a·uv³ + a·u³v + 7/2` — with `K4_abs_bound`, the only ingredient of
the cone/gate strip passages. -/
theorem K_box_bound (a u v : ℝ) (ha : 0 ≤ a) (hu : 0 < u) (hv : 0 < v)
    (hK7 : |K4 (a*u^2*v^2)| ≤ 7) :
    |(v/u) * J4 (a*u^2*v^2) + u * v⁻¹ * J4 (a*u^2*v^2)
      - (1/2) * K4 (a*u^2*v^2)|
    ≤ a*u*v^3 + a*u^3*v + 7/2 := by
  have hz : 0 ≤ a*u^2*v^2 := by positivity
  have h1 : |(v/u) * J4 (a*u^2*v^2)| ≤ a*u*v^3 := by
    rw [abs_mul, abs_div, abs_of_pos hv, abs_of_pos hu]
    calc v/u * |J4 (a*u^2*v^2)| ≤ v/u * (a*u^2*v^2) := by
          apply mul_le_mul_of_nonneg_left (J4_abs_le _ hz) (by positivity)
      _ = a*u*v^3 := by field_simp
  have h2 : |u * v⁻¹ * J4 (a*u^2*v^2)| ≤ a*u^3*v := by
    rw [abs_mul, abs_mul, abs_of_pos hu, abs_of_pos (inv_pos.mpr hv)]
    calc u * v⁻¹ * |J4 (a*u^2*v^2)| ≤ u * v⁻¹ * (a*u^2*v^2) := by
          apply mul_le_mul_of_nonneg_left (J4_abs_le _ hz) (by positivity)
      _ = a*u^3*v := by field_simp
  have h3 : |(1/2 : ℝ) * K4 (a*u^2*v^2)| ≤ 7/2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
    linarith [hK7]
  rw [abs_le]
  constructor
  · linarith [h1, h2, h3, neg_abs_le ((v/u) * J4 (a*u^2*v^2)),
      neg_abs_le (u * v⁻¹ * J4 (a*u^2*v^2)),
      le_abs_self ((1/2 : ℝ) * K4 (a*u^2*v^2))]
  · linarith [h1, h2, h3, le_abs_self ((v/u) * J4 (a*u^2*v^2)),
      le_abs_self (u * v⁻¹ * J4 (a*u^2*v^2)),
      neg_abs_le ((1/2 : ℝ) * K4 (a*u^2*v^2))]

/-- **The tail reduction**: for a bounded measurable integrand supported in
`[0,A]`, the `(0,∞)`-integral differs from the `[ε,A]`-interval integral by at
most `C·ε` — the workhorse of the rectangle → quadrant passage. -/
theorem integral_Ioi_sub_interval (f : ℝ → ℝ) (C A ε : ℝ)
    (hC : 0 ≤ C) (hε : 0 < ε) (hεA : ε ≤ A)
    (hm : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))))
    (hbound : ∀ x, 0 < x → |f x| ≤ C) (hsupp : ∀ x, A ≤ x → f x = 0) :
    |(∫ x in Set.Ioi (0:ℝ), f x) - ∫ x in ε..A, f x| ≤ C * ε := by
  have hA : 0 < A := lt_of_lt_of_le hε hεA
  have hint : MeasureTheory.IntegrableOn f (Set.Ioi (0:ℝ)) := by
    have hdom : MeasureTheory.Integrable
        ((Set.Ioc (0:ℝ) A).indicator (fun _ => C))
        (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) := by
      apply MeasureTheory.Integrable.integrableOn
      rw [MeasureTheory.integrable_indicator_iff measurableSet_Ioc]
      exact MeasureTheory.integrableOn_const
        (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    apply MeasureTheory.Integrable.mono' hdom hm
    apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
    intro x hx
    rw [Set.mem_Ioi] at hx
    by_cases hxA : x ≤ A
    · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hx, hxA⟩), Real.norm_eq_abs]
      exact hbound x hx
    · have hnot : x ∉ Set.Ioc (0:ℝ) A := fun hmem => hxA (Set.mem_Ioc.mp hmem).2
      rw [Set.indicator_of_notMem hnot, hsupp x (le_of_lt (not_le.mp hxA))]
      simp
  have h1 : MeasureTheory.IntegrableOn f (Set.Ioc (0:ℝ) A) :=
    hint.mono_set (fun x hx => hx.1)
  have h2 : MeasureTheory.IntegrableOn f (Set.Ioi A) :=
    hint.mono_set (fun x hx => Set.mem_Ioi.mpr (lt_trans hA hx))
  have h3 : MeasureTheory.IntegrableOn f (Set.Ioc (0:ℝ) ε) :=
    hint.mono_set (fun x hx => hx.1)
  have h4 : MeasureTheory.IntegrableOn f (Set.Ioc ε A) :=
    hint.mono_set (fun x hx => Set.mem_Ioi.mpr (lt_trans hε hx.1))
  have hsplit1 : (∫ x in Set.Ioi (0:ℝ), f x) = ∫ x in Set.Ioc (0:ℝ) A, f x := by
    rw [show Set.Ioi (0:ℝ) = Set.Ioc 0 A ∪ Set.Ioi A from
      (Set.Ioc_union_Ioi_eq_Ioi (le_of_lt hA)).symm,
      MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
        measurableSet_Ioi h1 h2]
    have hz : (∫ x in Set.Ioi A, f x) = 0 := by
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        (fun x hx => hsupp x (le_of_lt hx)), MeasureTheory.integral_zero]
    rw [hz, add_zero]
  have hsplit2 : (∫ x in Set.Ioc (0:ℝ) A, f x)
      = (∫ x in Set.Ioc (0:ℝ) ε, f x) + ∫ x in Set.Ioc ε A, f x := by
    rw [← Set.Ioc_union_Ioc_eq_Ioc (le_of_lt hε) hεA,
      MeasureTheory.setIntegral_union (by
        rw [Set.disjoint_left]
        intro x hx1 hx2
        exact absurd hx2.1 (not_lt.mpr hx1.2))
        measurableSet_Ioc h3 h4]
  have hival : (∫ x in ε..A, f x) = ∫ x in Set.Ioc ε A, f x :=
    intervalIntegral.integral_of_le hεA
  rw [hsplit1, hsplit2, hival,
    show (∫ x in Set.Ioc (0:ℝ) ε, f x) + (∫ x in Set.Ioc ε A, f x)
      - (∫ x in Set.Ioc ε A, f x) = ∫ x in Set.Ioc (0:ℝ) ε, f x from by ring,
    ← Real.norm_eq_abs]
  apply le_trans (MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
    (fun x hx => by rw [Real.norm_eq_abs]; exact hbound x hx.1))
  apply le_of_eq
  show C * (MeasureTheory.volume (Set.Ioc (0:ℝ) ε)).toReal = C * ε
  rw [Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (le_of_lt hε)]

/-- **The double tail**: for a bounded measurable integrand supported in the
box `[0,A]×[0,B]`, the iterated quadrant integral differs from the iterated
`[t,A]×[t,B]`-rectangle integral by at most `C·A·t + C·t·B`. -/
theorem double_tail (g : ℝ → ℝ → ℝ) (Cg A B t : ℝ) (hCg : 0 ≤ Cg)
    (hm : Measurable (Function.uncurry g))
    (hbound : ∀ x y, 0 < x → 0 < y → |g x y| ≤ Cg)
    (hsuppU : ∀ x y, A ≤ x → g x y = 0) (hsuppV : ∀ x y, B ≤ y → g x y = 0)
    (ht : 0 < t) (htA : t ≤ A) (htB : t ≤ B) :
    |(∫ y in Set.Ioi (0:ℝ), ∫ x in Set.Ioi (0:ℝ), g x y)
      - ∫ y in t..B, ∫ x in t..A, g x y|
    ≤ Cg*A*t + Cg*t*B := by
  have hA : 0 < A := lt_of_lt_of_le ht htA
  have hB : 0 < B := lt_of_lt_of_le ht htB
  have hmy : ∀ y : ℝ, MeasureTheory.AEStronglyMeasurable (fun x => g x y)
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) :=
    fun y => (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  -- the inner-tail estimate, per y > 0
  have hinner_tail : ∀ y : ℝ, 0 < y → ∀ s : ℝ, 0 < s → s ≤ A →
      |(∫ x in Set.Ioi (0:ℝ), g x y) - ∫ x in s..A, g x y| ≤ Cg * s :=
    fun y hy s hs hsA => integral_Ioi_sub_interval (fun x => g x y) Cg A s hCg hs hsA
      (hmy y) (fun x hx => hbound x y hx hy) (fun x hx => hsuppU x y hx)
  -- the inner integral is bounded by Cg·A and supported in y ≤ B
  have hinner_bound : ∀ y : ℝ, 0 < y → |∫ x in Set.Ioi (0:ℝ), g x y| ≤ Cg * A := by
    intro y hy
    have h := hinner_tail y hy A hA le_rfl
    rw [intervalIntegral.integral_same, sub_zero] at h
    exact h
  have hinner_supp : ∀ y : ℝ, B ≤ y → (∫ x in Set.Ioi (0:ℝ), g x y) = 0 := by
    intro y hy
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun x _ => hsuppV x y hy), MeasureTheory.integral_zero]
  -- marginal measurability
  have hmarg : MeasureTheory.AEStronglyMeasurable
      (fun y => ∫ x in Set.Ioi (0:ℝ), g x y)
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) := by
    have hswap : Measurable (Function.uncurry (fun y x => g x y)) :=
      hm.comp measurable_swap
    exact (hswap.stronglyMeasurable.integral_prod_right').measurable.aestronglyMeasurable
  -- interval integrability of both inner functions on [t,B]
  have hIIfull : IntervalIntegrable (fun y => ∫ x in Set.Ioi (0:ℝ), g x y)
      MeasureTheory.volume t B := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le htB]
    apply MeasureTheory.Integrable.mono'
      (MeasureTheory.integrableOn_const
        (C := Cg * A) (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
      (hmarg.mono_measure (MeasureTheory.Measure.restrict_mono
        (fun y hy => Set.mem_Ioi.mpr (lt_trans ht hy.1)) le_rfl))
    apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
    intro y hy
    rw [Real.norm_eq_abs]
    exact hinner_bound y (lt_trans ht hy.1)
  have hIIrect : IntervalIntegrable (fun y => ∫ x in t..A, g x y)
      MeasureTheory.volume t B := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le htB]
    have hmarg2 : MeasureTheory.AEStronglyMeasurable (fun y => ∫ x in t..A, g x y)
        (MeasureTheory.volume.restrict (Set.Ioc t B)) := by
      have he : (fun y => ∫ x in t..A, g x y)
          = fun y => ∫ x in Set.Ioc t A, g x y :=
        funext fun y => intervalIntegral.integral_of_le htA
      rw [he]
      have hswap : Measurable (Function.uncurry (fun y x => g x y)) :=
        hm.comp measurable_swap
      exact (hswap.stronglyMeasurable.integral_prod_right').measurable.aestronglyMeasurable
    apply MeasureTheory.Integrable.mono'
      (MeasureTheory.integrableOn_const
        (C := Cg * A) (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
      hmarg2
    apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
    intro y hy
    rw [Real.norm_eq_abs, ← Real.norm_eq_abs]
    apply le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := Cg) (fun x hx => by
        rw [Real.norm_eq_abs]
        rw [Set.uIoc_of_le htA] at hx
        exact hbound x y (lt_trans ht hx.1) (lt_trans ht hy.1)))
    rw [abs_of_nonneg (by linarith)]
    nlinarith [ht]
  -- assemble: quadrant − rectangle = outer tail + inner tails
  have hout : |(∫ y in Set.Ioi (0:ℝ), ∫ x in Set.Ioi (0:ℝ), g x y)
      - ∫ y in t..B, ∫ x in Set.Ioi (0:ℝ), g x y| ≤ (Cg * A) * t :=
    integral_Ioi_sub_interval _ (Cg * A) B t (by positivity) ht htB hmarg
      (fun y hy => hinner_bound y hy) hinner_supp
  have hin : |(∫ y in t..B, ∫ x in Set.Ioi (0:ℝ), g x y)
      - ∫ y in t..B, ∫ x in t..A, g x y| ≤ (Cg * t) * B := by
    rw [← intervalIntegral.integral_sub hIIfull hIIrect, ← Real.norm_eq_abs]
    apply le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := Cg * t) (fun y hy => by
        rw [Real.norm_eq_abs]
        rw [Set.uIoc_of_le htB] at hy
        exact hinner_tail y (lt_trans ht hy.1) t ht htA))
    rw [abs_of_nonneg (by linarith)]
    nlinarith [ht, hCg, mul_nonneg (mul_nonneg hCg (le_of_lt ht)) (le_of_lt ht)]
  calc |(∫ y in Set.Ioi (0:ℝ), ∫ x in Set.Ioi (0:ℝ), g x y)
      - ∫ y in t..B, ∫ x in t..A, g x y|
      ≤ |(∫ y in Set.Ioi (0:ℝ), ∫ x in Set.Ioi (0:ℝ), g x y)
        - ∫ y in t..B, ∫ x in Set.Ioi (0:ℝ), g x y|
        + |(∫ y in t..B, ∫ x in Set.Ioi (0:ℝ), g x y)
        - ∫ y in t..B, ∫ x in t..A, g x y| := by
        have h := abs_sub_abs_le_abs_sub (0:ℝ) (0:ℝ)
        rw [abs_le]
        constructor
        · linarith [neg_abs_le ((∫ y in Set.Ioi (0:ℝ), ∫ x in Set.Ioi (0:ℝ), g x y)
            - ∫ y in t..B, ∫ x in Set.Ioi (0:ℝ), g x y),
            neg_abs_le ((∫ y in t..B, ∫ x in Set.Ioi (0:ℝ), g x y)
            - ∫ y in t..B, ∫ x in t..A, g x y)]
        · linarith [le_abs_self ((∫ y in Set.Ioi (0:ℝ), ∫ x in Set.Ioi (0:ℝ), g x y)
            - ∫ y in t..B, ∫ x in Set.Ioi (0:ℝ), g x y),
            le_abs_self ((∫ y in t..B, ∫ x in Set.Ioi (0:ℝ), g x y)
            - ∫ y in t..B, ∫ x in t..A, g x y)]
    _ ≤ (Cg * A) * t + (Cg * t) * B := by linarith [hout, hin]
    _ = Cg*A*t + Cg*t*B := by ring

#print axioms double_tail

#print axioms K_box_bound

#print axioms strip_u_axis
#print axioms strip_v_axis

#print axioms D1_bound_uniform
#print axioms K_bound_uniform

end UnifiedTheory.Audit.KFCausalMinkowski4DQuadrant
