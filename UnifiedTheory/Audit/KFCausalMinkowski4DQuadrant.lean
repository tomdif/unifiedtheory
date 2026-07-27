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

open Real Filter Topology
open UnifiedTheory.Audit.KFCausalMinkowski4DKernel
open UnifiedTheory.Audit.KFCausalMinkowski4DKernelBounds
open UnifiedTheory.Audit.KFCausalMinkowski4DMoments
open UnifiedTheory.Audit.KFCausalMinkowski4DRectangleChain
open UnifiedTheory.Audit.KFCausalMinkowski4DDictionary

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

-- The two closing `linarith` calls carry six absolute-value bounds plus the
-- rectangle-chain equation over very large integral expressions.
set_option maxHeartbeats 1600000 in
/-- **THE QUADRANT IDENTITY** (fixed `a > 0`): for a profile `F` with continuous
uncurried derivatives, uniform bounds, and support strictly inside the box
`[0,A]×[0,B]`,

    ∬_{(0,∞)²} a(v−u)²·f4D(au²v²)·F  =  (1/6)·F(0,0)  +  ∬_{(0,∞)²} 𝒦·F_uv.

The BDG counterterm coefficient `1/6` is *derived*: it is the `δ → 0` limit of
the v-axis IBP boundary.  Proof: the exact rectangle chain at `ε = δ = t`, the
five error pieces each `O(t)` (double tails, strips, edge-FTC tail), and
`ge_of_tendsto` along `𝓝[>]0`. -/
theorem corner4_quadrant (a A B CF CFu Mv Ccone : ℝ)
    (ha : 0 < a) (hA : 0 < A) (hB : 0 < B)
    (F Fu Fuv : ℝ → ℝ → ℝ)
    (hFC : Continuous (Function.uncurry F))
    (hFuc : Continuous (Function.uncurry Fu))
    (hFuvc : Continuous (Function.uncurry Fuv))
    (hFd : ∀ v u, HasDerivAt (fun u' => F u' v) (Fu u v) u)
    (hFud : ∀ u v, HasDerivAt (fun v' => Fu u v') (Fuv u v) v)
    (hCF : ∀ u v, |F u v| ≤ CF) (hCFu : ∀ u v, |Fu u v| ≤ CFu)
    (hMv : ∀ u v, |Fuv u v| ≤ Mv)
    (hCcone : ∀ u v, |a*(v-u)^2 * f4D (a*u^2*v^2) * F u v| ≤ Ccone)
    (hsUF : ∀ u v, A ≤ u → F u v = 0) (hsVF : ∀ u v, B ≤ v → F u v = 0)
    (hsUFu : ∀ u v, A ≤ u → Fu u v = 0) (hsVFu : ∀ u v, B ≤ v → Fu u v = 0)
    (hsUFuv : ∀ u v, A ≤ u → Fuv u v = 0) (hsVFuv : ∀ u v, B ≤ v → Fuv u v = 0) :
    (∫ v in Set.Ioi (0:ℝ), ∫ u in Set.Ioi (0:ℝ),
        a*(v-u)^2 * f4D (a*u^2*v^2) * F u v)
      = (1/6) * F 0 0
        + ∫ u in Set.Ioi (0:ℝ), ∫ v in Set.Ioi (0:ℝ),
            ((v/u) * J4 (a*u^2*v^2) + u * v⁻¹ * J4 (a*u^2*v^2)
              - (1/2) * K4 (a*u^2*v^2)) * Fuv u v := by
  have hCF0 : 0 ≤ CF := le_trans (abs_nonneg _) (hCF 0 0)
  have hCFu0 : 0 ≤ CFu := le_trans (abs_nonneg _) (hCFu 0 0)
  have hMv0 : 0 ≤ Mv := le_trans (abs_nonneg _) (hMv 0 0)
  have hCcone0 : 0 ≤ Ccone := le_trans (abs_nonneg _) (hCcone 0 0)
  have hCKF0 : (0:ℝ) ≤ (a*A*B^3 + a*A^3*B + 7/2) * Mv := by positivity
  -- measurability of the two double-tail integrands
  have hconeMeas : Measurable (Function.uncurry (fun u v =>
      a*(v-u)^2 * f4D (a*u^2*v^2) * F u v)) := by
    have hc : Continuous (fun p : ℝ × ℝ => a*(p.2-p.1)^2 * f4D (a*p.1^2*p.2^2)) := by
      unfold UnifiedTheory.Audit.KFCausalMinkowski4DMoments.f4D
      fun_prop
    exact (hc.mul hFC).measurable
  have hJm : Measurable J4 := by
    have : Continuous J4 := by
      unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4
      fun_prop
    exact this.measurable
  have hKm : Measurable K4 := by
    have : Continuous K4 := by
      unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4
      fun_prop
    exact this.measurable
  have hgateMeas : Measurable (Function.uncurry (fun x y =>
      ((x/y) * J4 (a*y^2*x^2) + y * x⁻¹ * J4 (a*y^2*x^2)
        - (1/2) * K4 (a*y^2*x^2)) * Fuv y x)) := by
    have hq : Measurable (fun p : ℝ × ℝ => a*p.2^2*p.1^2) := by fun_prop
    exact ((((measurable_fst.div measurable_snd).mul (hJm.comp hq)).add
      ((measurable_snd.mul measurable_fst.inv).mul (hJm.comp hq))).sub
      (measurable_const.mul (hKm.comp hq))).mul
      (hFuvc.measurable.comp (measurable_snd.prodMk measurable_fst))
  -- pointwise gate bound
  have hKFb : ∀ x y : ℝ, 0 < x → 0 < y →
      |((x/y) * J4 (a*y^2*x^2) + y * x⁻¹ * J4 (a*y^2*x^2)
        - (1/2) * K4 (a*y^2*x^2)) * Fuv y x|
      ≤ (a*A*B^3 + a*A^3*B + 7/2) * Mv := by
    intro x y hx hy
    rcases le_or_gt A y with hyA | hyA
    · rw [hsUFuv y x hyA, mul_zero, abs_zero]
      exact hCKF0
    rcases le_or_gt B x with hxB | hxB
    · rw [hsVFuv y x hxB, mul_zero, abs_zero]
      exact hCKF0
    have hbox := K_box_bound a y x ha.le hy hx
      (UnifiedTheory.Audit.KFCausalMinkowski4DCorner.K4_abs_bound _ (by positivity))
    rw [abs_mul]
    have hx2 : x^2 ≤ B^2 := by nlinarith
    have hx3 : x^3 ≤ B^3 := by
      nlinarith [mul_le_mul_of_nonneg_right hx2 (le_of_lt hx),
        mul_le_mul_of_nonneg_left (le_of_lt hxB) (sq_nonneg B)]
    have hy2 : y^2 ≤ A^2 := by nlinarith
    have hy3 : y^3 ≤ A^3 := by
      nlinarith [mul_le_mul_of_nonneg_right hy2 (le_of_lt hy),
        mul_le_mul_of_nonneg_left (le_of_lt hyA) (sq_nonneg A)]
    have hmono : a*y*x^3 + a*y^3*x + 7/2 ≤ a*A*B^3 + a*A^3*B + 7/2 := by
      have p1 : y*x^3 ≤ A*B^3 := by
        nlinarith [mul_le_mul_of_nonneg_right (le_of_lt hyA) (pow_pos hx 3).le,
          mul_le_mul_of_nonneg_left hx3 (le_of_lt hA)]
      have p2 : y^3*x ≤ A^3*B := by
        nlinarith [mul_le_mul_of_nonneg_right hy3 (le_of_lt hx),
          mul_le_mul_of_nonneg_left (le_of_lt hxB) (by positivity : (0:ℝ) ≤ A^3)]
      nlinarith [mul_le_mul_of_nonneg_left p1 (le_of_lt ha),
        mul_le_mul_of_nonneg_left p2 (le_of_lt ha)]
    calc |(x/y) * J4 (a*y^2*x^2) + y * x⁻¹ * J4 (a*y^2*x^2)
          - (1/2) * K4 (a*y^2*x^2)| * |Fuv y x|
        ≤ (a*y*x^3 + a*y^3*x + 7/2) * Mv :=
          mul_le_mul hbox (hMv y x) (abs_nonneg _) (by positivity)
      _ ≤ (a*A*B^3 + a*A^3*B + 7/2) * Mv :=
          mul_le_mul_of_nonneg_right hmono hMv0
  -- the per-t error bound
  have hkey : ∀ t ∈ Set.Ioo (0:ℝ) (min A B),
      |(∫ v in Set.Ioi (0:ℝ), ∫ u in Set.Ioi (0:ℝ),
          a*(v-u)^2 * f4D (a*u^2*v^2) * F u v)
        - ((1/6) * F 0 0
          + ∫ u in Set.Ioi (0:ℝ), ∫ v in Set.Ioi (0:ℝ),
              ((v/u) * J4 (a*u^2*v^2) + u * v⁻¹ * J4 (a*u^2*v^2)
                - (1/2) * K4 (a*u^2*v^2)) * Fuv u v)|
      ≤ (Ccone*A + Ccone*B + 7*a*B^3*CF + (7/2)*a*A^4*CFu + (1/6)*A*Mv
          + (1/6)*CFu + (a*A*B^3 + a*A^3*B + 7/2)*Mv*B
          + (a*A*B^3 + a*A^3*B + 7/2)*Mv*A) * t := by
    intro t ht
    obtain ⟨ht0, htm⟩ := ht
    have htA : t ≤ A := le_of_lt (lt_of_lt_of_le htm (min_le_left A B))
    have htB : t ≤ B := le_of_lt (lt_of_lt_of_le htm (min_le_right A B))
    -- the exact rectangle chain at ε = δ = t
    have hchain := corner4_rectangle_chain a t A t B ht0 htA ht0 htB F Fu Fuv
      hFC hFd hFud hFuc hFuvc (fun v => hsUF A v le_rfl) (fun u => hsVFu u B le_rfl)
    -- (1) the cone double tail
    have hd1 := double_tail (fun u v => a*(v-u)^2 * f4D (a*u^2*v^2) * F u v)
      Ccone A B t hCcone0 hconeMeas (fun x y _ _ => hCcone x y)
      (fun x y hx => by dsimp only; rw [hsUF x y hx, mul_zero])
      (fun x y hy => by dsimp only; rw [hsVF x y hy, mul_zero]) ht0 htA htB
    -- (2) the u-axis strip
    have hs1 := strip_u_axis a t t B CF ha.le ht0 ht0 htB (fun v => F t v)
      (fun v => hCF t v)
    have h2fin : |∫ v in t..B, (t⁻¹ * G4 (a*t^2*v^2) + t * (v^2)⁻¹ * H4 (a*t^2*v^2)
        - a*t^2*v * K4d (a*t^2*v^2)) * F t v| ≤ 7*a*B^3*CF*t := by
      apply le_trans hs1
      have hpoly : 2*B^2+2*t^2+3*t*B ≤ 7*B^2 := by nlinarith
      calc a*(2*B^2+2*t^2+3*t*B)*t*CF*B
          = (a*(2*B^2+2*t^2+3*t*B))*(t*CF*B) := by ring
        _ ≤ (a*(7*B^2))*(t*CF*B) := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpoly (le_of_lt ha)) (by positivity)
        _ = 7*a*B^3*CF*t := by ring
    -- (3) the v-axis strip
    have hs2 := strip_v_axis a t t A CFu Mv ha.le ht0 ht0 htA Fu Fuv hFuc hFud
      hCFu hMv
    have h3fin : |(∫ u in t..A, ((t/u) * J4 (a*u^2*t^2) + u * t⁻¹ * J4 (a*u^2*t^2)
        - (1/2) * K4 (a*u^2*t^2)) * Fu u t) + (1/6) * ∫ u in t..A, Fu u 0|
        ≤ ((7/2)*a*A^4*CFu + (1/6)*A*Mv)*t := by
      apply le_trans hs2
      have hpoly2 : A*t^2 + A^3 + (3/2)*A^2*t ≤ (7/2)*A^3 := by
        have p1 : t*t ≤ A*t := mul_le_mul_of_nonneg_right htA (le_of_lt ht0)
        have p2 : A*t ≤ A*A := mul_le_mul_of_nonneg_left htA (le_of_lt hA)
        nlinarith [p1, p2, mul_le_mul_of_nonneg_left p1 (le_of_lt hA),
          mul_le_mul_of_nonneg_left p2 (le_of_lt hA)]
      calc (a*(A*t^2 + A^3 + (3/2)*A^2*t)*t*CFu + (1/6)*Mv*t)*A
          = (a*(A*t^2 + A^3 + (3/2)*A^2*t))*(t*CFu*A) + (1/6)*Mv*A*t := by ring
        _ ≤ (a*((7/2)*A^3))*(t*CFu*A) + (1/6)*Mv*A*t := by
            have hmul : (a*(A*t^2 + A^3 + (3/2)*A^2*t))*(t*CFu*A)
                ≤ (a*((7/2)*A^3))*(t*CFu*A) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hpoly2 (le_of_lt ha)) (by positivity)
            linarith [hmul]
        _ = ((7/2)*a*A^4*CFu + (1/6)*A*Mv)*t := by ring
    -- (4) the edge-FTC tail
    have hedge : (∫ u in Set.Ioi (0:ℝ), Fu u 0) = -F 0 0 :=
      edge_ftc (fun u => F u 0) (fun u => Fu u 0) A hA (fun u => hFd 0 u)
        (hFuc.comp (continuous_id.prodMk continuous_const))
        (fun u hu => hsUF u 0 hu)
    have htail4 := integral_Ioi_sub_interval (fun u => Fu u 0) CFu A t hCFu0
      ht0 htA
      ((hFuc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
      (fun u _ => hCFu u 0) (fun u hu => hsUFu u 0 hu)
    have h4 : |-((1:ℝ)/6) * (∫ u in t..A, Fu u 0) - (1/6)*F 0 0|
        ≤ (1/6)*CFu*t := by
      have heq : -((1:ℝ)/6) * (∫ u in t..A, Fu u 0) - (1/6)*F 0 0
          = -((1/6) * ((∫ u in t..A, Fu u 0)
            - (∫ u in Set.Ioi (0:ℝ), Fu u 0))) := by
        rw [hedge]
        ring
      rw [heq, abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/6)]
      rw [abs_sub_comm] at htail4
      calc (1/6) * |(∫ u in t..A, Fu u 0) - ∫ u in Set.Ioi (0:ℝ), Fu u 0|
          ≤ (1/6) * (CFu * t) := mul_le_mul_of_nonneg_left htail4 (by norm_num)
        _ = (1/6)*CFu*t := by ring
    -- (5) the gate double tail
    have hd5 := double_tail (fun x y => ((x/y) * J4 (a*y^2*x^2)
        + y * x⁻¹ * J4 (a*y^2*x^2) - (1/2) * K4 (a*y^2*x^2)) * Fuv y x)
      ((a*A*B^3 + a*A^3*B + 7/2) * Mv) B A t hCKF0 hgateMeas hKFb
      (fun x y hx => by dsimp only; rw [hsVFuv y x hx, mul_zero])
      (fun x y hy => by dsimp only; rw [hsUFuv y x hy, mul_zero]) ht0 htB htA
    -- assemble
    rw [abs_le]
    constructor
    · linarith [hd1, h2fin, h3fin, h4, hd5, hchain,
        neg_abs_le ((∫ v in Set.Ioi (0:ℝ), ∫ u in Set.Ioi (0:ℝ),
          a*(v-u)^2 * f4D (a*u^2*v^2) * F u v)
          - ∫ v in t..B, ∫ u in t..A, a*(v-u)^2 * f4D (a*u^2*v^2) * F u v),
        le_abs_self (∫ v in t..B, (t⁻¹ * G4 (a*t^2*v^2)
          + t * (v^2)⁻¹ * H4 (a*t^2*v^2) - a*t^2*v * K4d (a*t^2*v^2)) * F t v),
        neg_abs_le ((∫ u in t..A, ((t/u) * J4 (a*u^2*t^2)
          + u * t⁻¹ * J4 (a*u^2*t^2) - (1/2) * K4 (a*u^2*t^2)) * Fu u t)
          + (1/6) * ∫ u in t..A, Fu u 0),
        neg_abs_le (-((1:ℝ)/6) * (∫ u in t..A, Fu u 0) - (1/6)*F 0 0),
        le_abs_self ((∫ y in Set.Ioi (0:ℝ), ∫ x in Set.Ioi (0:ℝ),
          ((x/y) * J4 (a*y^2*x^2) + y * x⁻¹ * J4 (a*y^2*x^2)
            - (1/2) * K4 (a*y^2*x^2)) * Fuv y x)
          - ∫ y in t..A, ∫ x in t..B, ((x/y) * J4 (a*y^2*x^2)
            + y * x⁻¹ * J4 (a*y^2*x^2) - (1/2) * K4 (a*y^2*x^2)) * Fuv y x)]
    · linarith [hd1, h2fin, h3fin, h4, hd5, hchain,
        le_abs_self ((∫ v in Set.Ioi (0:ℝ), ∫ u in Set.Ioi (0:ℝ),
          a*(v-u)^2 * f4D (a*u^2*v^2) * F u v)
          - ∫ v in t..B, ∫ u in t..A, a*(v-u)^2 * f4D (a*u^2*v^2) * F u v),
        neg_abs_le (∫ v in t..B, (t⁻¹ * G4 (a*t^2*v^2)
          + t * (v^2)⁻¹ * H4 (a*t^2*v^2) - a*t^2*v * K4d (a*t^2*v^2)) * F t v),
        le_abs_self ((∫ u in t..A, ((t/u) * J4 (a*u^2*t^2)
          + u * t⁻¹ * J4 (a*u^2*t^2) - (1/2) * K4 (a*u^2*t^2)) * Fu u t)
          + (1/6) * ∫ u in t..A, Fu u 0),
        le_abs_self (-((1:ℝ)/6) * (∫ u in t..A, Fu u 0) - (1/6)*F 0 0),
        neg_abs_le ((∫ y in Set.Ioi (0:ℝ), ∫ x in Set.Ioi (0:ℝ),
          ((x/y) * J4 (a*y^2*x^2) + y * x⁻¹ * J4 (a*y^2*x^2)
            - (1/2) * K4 (a*y^2*x^2)) * Fuv y x)
          - ∫ y in t..A, ∫ x in t..B, ((x/y) * J4 (a*y^2*x^2)
            + y * x⁻¹ * J4 (a*y^2*x^2) - (1/2) * K4 (a*y^2*x^2)) * Fuv y x)]
  -- squeeze along 𝓝[>]0
  have htend : Tendsto (fun t : ℝ =>
      (Ccone*A + Ccone*B + 7*a*B^3*CF + (7/2)*a*A^4*CFu + (1/6)*A*Mv
        + (1/6)*CFu + (a*A*B^3 + a*A^3*B + 7/2)*Mv*B
        + (a*A*B^3 + a*A^3*B + 7/2)*Mv*A) * t) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => t) (𝓝[>] (0:ℝ)) (𝓝 0) :=
      tendsto_id.mono_right nhdsWithin_le_nhds
    have h2 := h1.const_mul
      (Ccone*A + Ccone*B + 7*a*B^3*CF + (7/2)*a*A^4*CFu + (1/6)*A*Mv
        + (1/6)*CFu + (a*A*B^3 + a*A^3*B + 7/2)*Mv*B
        + (a*A*B^3 + a*A^3*B + 7/2)*Mv*A)
    rw [mul_zero] at h2
    exact h2
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ),
      |(∫ v in Set.Ioi (0:ℝ), ∫ u in Set.Ioi (0:ℝ),
          a*(v-u)^2 * f4D (a*u^2*v^2) * F u v)
        - ((1/6) * F 0 0
          + ∫ u in Set.Ioi (0:ℝ), ∫ v in Set.Ioi (0:ℝ),
              ((v/u) * J4 (a*u^2*v^2) + u * v⁻¹ * J4 (a*u^2*v^2)
                - (1/2) * K4 (a*u^2*v^2)) * Fuv u v)|
      ≤ (Ccone*A + Ccone*B + 7*a*B^3*CF + (7/2)*a*A^4*CFu + (1/6)*A*Mv
          + (1/6)*CFu + (a*A*B^3 + a*A^3*B + 7/2)*Mv*B
          + (a*A*B^3 + a*A^3*B + 7/2)*Mv*A) * t := by
    filter_upwards [Filter.inter_mem
      (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_min hA hB)))
      self_mem_nhdsWithin] with t ht
    exact hkey t ⟨Set.mem_Ioi.mp ht.2, Set.mem_Iio.mp ht.1⟩
  have hle := ge_of_tendsto htend hev
  have h0 := abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  linarith [h0]

#print axioms corner4_quadrant

#print axioms double_tail

#print axioms K_box_bound

#print axioms strip_u_axis
#print axioms strip_v_axis

#print axioms D1_bound_uniform
#print axioms K_bound_uniform

end UnifiedTheory.Audit.KFCausalMinkowski4DQuadrant
