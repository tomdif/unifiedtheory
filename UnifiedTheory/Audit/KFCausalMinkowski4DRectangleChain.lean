/-
  Audit/KFCausalMinkowski4DRectangleChain.lean — chaining the rungs + axis limits

  * `corner4_rectangle_chain`: the two IBP rungs chained through the rectangle
    Fubini — the exact finite-`a` identity on `[ε,A]×[δ,B]`:

      ∬ a(v−u)²f4D·F  =  −∫ D1(ε,v)F(ε,v)dv + ∫ 𝒦(u,δ)F_u(u,δ)du + ∬ 𝒦·F_uv.

  * `D1_axis_limit`: the `u`-axis boundary dies:  D1(ε,v) → 0  as ε → 0⁺
    (slope argument at `G4(0) = 0`).
  * `K_axis_limit`: the `v`-axis boundary produces the axis constant:
    𝒦(u,δ) → −K4(0)/2 = −1/6  as δ → 0⁺ — the constant whose counterterm
    cancellation `(3/(2π))·(1/6)·(4π) = 1` is already machine-checked.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowski4DRectangleIBP

open MeasureTheory Real Set Filter Topology
open UnifiedTheory.Audit.KFCausalMinkowski4DKernel
open UnifiedTheory.Audit.KFCausalMinkowski4DMoments
open UnifiedTheory.Audit.KFCausalMinkowski4DRectangleIBP

namespace UnifiedTheory.Audit.KFCausalMinkowski4DRectangleChain

/-- **The chained rectangle identity.**  Both IBP rungs composed through the
rectangle Fubini: exact at finite `a`, on `[ε,A]×[δ,B]`, for `F` supported
inside (`F(A,·) = 0`, `F_u(·,B) = 0`). -/
theorem corner4_rectangle_chain (a ε A δ B : ℝ)
    (hε : 0 < ε) (hεA : ε ≤ A) (hδ : 0 < δ) (hδB : δ ≤ B)
    (F Fu Fuv : ℝ → ℝ → ℝ)
    (hFC : Continuous (Function.uncurry F))
    (hFd : ∀ v u, HasDerivAt (fun u' => F u' v) (Fu u v) u)
    (hFud : ∀ u v, HasDerivAt (fun v' => Fu u v') (Fuv u v) v)
    (hFuc : Continuous (Function.uncurry Fu))
    (hFuvc : Continuous (Function.uncurry Fuv))
    (hFA : ∀ v, F A v = 0) (hFuB : ∀ u, Fu u B = 0) :
    ∫ v in δ..B, ∫ u in ε..A, a*(v-u)^2 * f4D (a*u^2*v^2) * F u v
      = -(∫ v in δ..B, (ε⁻¹ * G4 (a*ε^2*v^2) + ε * (v^2)⁻¹ * H4 (a*ε^2*v^2)
            - a*ε^2*v * K4d (a*ε^2*v^2)) * F ε v)
        + (∫ u in ε..A, ((δ/u) * J4 (a*u^2*δ^2) + u * δ⁻¹ * J4 (a*u^2*δ^2)
            - (1/2) * K4 (a*u^2*δ^2)) * Fu u δ)
        + ∫ u in ε..A, ∫ v in δ..B, ((v/u) * J4 (a*u^2*v^2)
            + u * v⁻¹ * J4 (a*u^2*v^2) - (1/2) * K4 (a*u^2*v^2)) * Fuv u v := by
  have hGC : Continuous G4 := by
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.G4
      UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4
      UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4d
    fun_prop
  have hHC : Continuous H4 := by
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.H4
      UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4
      UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4d
    fun_prop
  have hKdC : Continuous K4d := by
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4d
    fun_prop
  have hJC : Continuous J4 := by
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4
    fun_prop
  have hKC : Continuous K4 := by
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4
    fun_prop
  -- two-variable continuity of the two Fubini integrands on the closed rectangle
  have hD1F : ContinuousOn (fun p : ℝ × ℝ =>
      (p.2⁻¹ * G4 (a*p.2^2*p.1^2) + p.2 * (p.1^2)⁻¹ * H4 (a*p.2^2*p.1^2)
        - a*p.2^2*p.1 * K4d (a*p.2^2*p.1^2)) * Fu p.2 p.1)
      (Icc δ B ×ˢ Icc ε A) := by
    have hz : Continuous (fun p : ℝ × ℝ => a*p.2^2*p.1^2) := by fun_prop
    apply ContinuousOn.mul
    · apply ContinuousOn.sub
      · apply ContinuousOn.add
        · exact (continuous_snd.continuousOn.inv₀
            (fun p hp => ne_of_gt (lt_of_lt_of_le hε hp.2.1))).mul
            (hGC.comp hz).continuousOn
        · exact (continuous_snd.continuousOn.mul
            ((continuous_fst.pow 2).continuousOn.inv₀
              (fun p hp => pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hδ hp.1.1))))).mul
            (hHC.comp hz).continuousOn
      · exact (by fun_prop : Continuous (fun p : ℝ × ℝ => a*p.2^2*p.1)).continuousOn.mul
          (hKdC.comp hz).continuousOn
    · exact (hFuc.comp (continuous_snd.prodMk continuous_fst)).continuousOn
  have hKFuv : ContinuousOn (fun p : ℝ × ℝ =>
      ((p.2/p.1) * J4 (a*p.1^2*p.2^2) + p.1 * p.2⁻¹ * J4 (a*p.1^2*p.2^2)
        - (1/2) * K4 (a*p.1^2*p.2^2)) * Fuv p.1 p.2)
      (Icc ε A ×ˢ Icc δ B) := by
    have hz : Continuous (fun p : ℝ × ℝ => a*p.1^2*p.2^2) := by fun_prop
    apply ContinuousOn.mul
    · apply ContinuousOn.sub
      · apply ContinuousOn.add
        · exact (continuous_snd.continuousOn.div continuous_fst.continuousOn
            (fun p hp => ne_of_gt (lt_of_lt_of_le hε hp.1.1))).mul
            (hJC.comp hz).continuousOn
        · exact (continuous_fst.continuousOn.mul
            (continuous_snd.continuousOn.inv₀
              (fun p hp => ne_of_gt (lt_of_lt_of_le hδ hp.2.1)))).mul
            (hJC.comp hz).continuousOn
      · exact continuousOn_const.mul (hKC.comp hz).continuousOn
    · exact hFuvc.continuousOn
  -- product integrability
  have hprod1 : Integrable (Function.uncurry (fun v u =>
      (u⁻¹ * G4 (a*u^2*v^2) + u * (v^2)⁻¹ * H4 (a*u^2*v^2)
        - a*u^2*v * K4d (a*u^2*v^2)) * Fu u v))
      ((volume.restrict (Ioc δ B)).prod (volume.restrict (Ioc ε A))) := by
    rw [Measure.prod_restrict]
    exact (hD1F.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hprod2 : Integrable (Function.uncurry (fun u v =>
      ((v/u) * J4 (a*u^2*v^2) + u * v⁻¹ * J4 (a*u^2*v^2)
        - (1/2) * K4 (a*u^2*v^2)) * Fuv u v))
      ((volume.restrict (Ioc ε A)).prod (volume.restrict (Ioc δ B))) := by
    rw [Measure.prod_restrict]
    exact (hKFuv.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  -- E1: inner rung + split over v
  have hbc1 : IntervalIntegrable (fun v => (ε⁻¹ * G4 (a*ε^2*v^2)
      + ε * (v^2)⁻¹ * H4 (a*ε^2*v^2) - a*ε^2*v * K4d (a*ε^2*v^2)) * F ε v)
      volume δ B := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hδB]
    apply ContinuousOn.mul
    · apply ContinuousOn.sub
      · apply ContinuousOn.add
        · exact continuousOn_const.mul
            (hGC.comp (by fun_prop : Continuous (fun v : ℝ => a*ε^2*v^2))).continuousOn
        · exact (continuousOn_const.mul ((continuousOn_id.pow 2).inv₀
            (fun v hv => pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hδ hv.1))))).mul
            (hHC.comp (by fun_prop : Continuous (fun v : ℝ => a*ε^2*v^2))).continuousOn
      · exact (continuousOn_const.mul continuousOn_id).mul
          (hKdC.comp (by fun_prop : Continuous (fun v : ℝ => a*ε^2*v^2))).continuousOn
    · exact (hFC.comp (continuous_const.prodMk continuous_id)).continuousOn
  have hIm1 : IntervalIntegrable (fun v => ∫ u in ε..A,
      (u⁻¹ * G4 (a*u^2*v^2) + u * (v^2)⁻¹ * H4 (a*u^2*v^2)
        - a*u^2*v * K4d (a*u^2*v^2)) * Fu u v) volume δ B := by
    rw [intervalIntegrable_iff, uIoc_of_le hδB]
    have hm := hprod1.integral_prod_left
    have he : (fun v => ∫ u in ε..A,
        (u⁻¹ * G4 (a*u^2*v^2) + u * (v^2)⁻¹ * H4 (a*u^2*v^2)
          - a*u^2*v * K4d (a*u^2*v^2)) * Fu u v)
        = fun v => ∫ u in Ioc ε A,
        (u⁻¹ * G4 (a*u^2*v^2) + u * (v^2)⁻¹ * H4 (a*u^2*v^2)
          - a*u^2*v * K4d (a*u^2*v^2)) * Fu u v :=
      funext fun v => intervalIntegral.integral_of_le hεA
    rw [he]
    exact hm
  have E1 : (∫ v in δ..B, ∫ u in ε..A, a*(v-u)^2 * f4D (a*u^2*v^2) * F u v)
      = -(∫ v in δ..B, (ε⁻¹ * G4 (a*ε^2*v^2) + ε * (v^2)⁻¹ * H4 (a*ε^2*v^2)
            - a*ε^2*v * K4d (a*ε^2*v^2)) * F ε v)
        - ∫ v in δ..B, ∫ u in ε..A,
            (u⁻¹ * G4 (a*u^2*v^2) + u * (v^2)⁻¹ * H4 (a*u^2*v^2)
              - a*u^2*v * K4d (a*u^2*v^2)) * Fu u v := by
    rw [intervalIntegral.integral_congr (g := fun v =>
        -((ε⁻¹ * G4 (a*ε^2*v^2) + ε * (v^2)⁻¹ * H4 (a*ε^2*v^2)
            - a*ε^2*v * K4d (a*ε^2*v^2)) * F ε v)
        - ∫ u in ε..A, (u⁻¹ * G4 (a*u^2*v^2) + u * (v^2)⁻¹ * H4 (a*u^2*v^2)
            - a*u^2*v * K4d (a*u^2*v^2)) * Fu u v) ?_]
    · have hneg1 : IntervalIntegrable (fun v => -((ε⁻¹ * G4 (a*ε^2*v^2)
          + ε * (v^2)⁻¹ * H4 (a*ε^2*v^2) - a*ε^2*v * K4d (a*ε^2*v^2)) * F ε v))
          volume δ B := hbc1.neg
      rw [intervalIntegral.integral_sub hneg1 hIm1,
        intervalIntegral.integral_neg]
    · intro v hv
      rw [uIcc_of_le hδB] at hv
      exact corner4_ibp_u a v ε A hε hεA (ne_of_gt (lt_of_lt_of_le hδ hv.1))
        (fun u => F u v) (fun u => Fu u v) (hFd v)
        (hFuc.comp (continuous_id.prodMk continuous_const)) (hFA v)
  -- E2: the Fubini swap
  have E2 : (∫ v in δ..B, ∫ u in ε..A,
      (u⁻¹ * G4 (a*u^2*v^2) + u * (v^2)⁻¹ * H4 (a*u^2*v^2)
        - a*u^2*v * K4d (a*u^2*v^2)) * Fu u v)
      = ∫ u in ε..A, ∫ v in δ..B,
      (u⁻¹ * G4 (a*u^2*v^2) + u * (v^2)⁻¹ * H4 (a*u^2*v^2)
        - a*u^2*v * K4d (a*u^2*v^2)) * Fu u v := by
    have he : (fun v => ∫ u in ε..A,
        (u⁻¹ * G4 (a*u^2*v^2) + u * (v^2)⁻¹ * H4 (a*u^2*v^2)
          - a*u^2*v * K4d (a*u^2*v^2)) * Fu u v)
        = fun v => ∫ u in Ioc ε A,
        (u⁻¹ * G4 (a*u^2*v^2) + u * (v^2)⁻¹ * H4 (a*u^2*v^2)
          - a*u^2*v * K4d (a*u^2*v^2)) * Fu u v :=
      funext fun v => intervalIntegral.integral_of_le hεA
    rw [show (∫ v in δ..B, ∫ u in ε..A,
        (u⁻¹ * G4 (a*u^2*v^2) + u * (v^2)⁻¹ * H4 (a*u^2*v^2)
          - a*u^2*v * K4d (a*u^2*v^2)) * Fu u v)
        = ∫ v in δ..B, ∫ u in Ioc ε A,
        (u⁻¹ * G4 (a*u^2*v^2) + u * (v^2)⁻¹ * H4 (a*u^2*v^2)
          - a*u^2*v * K4d (a*u^2*v^2)) * Fu u v from by rw [he]]
    have hint : Integrable (Function.uncurry (fun v u =>
        (u⁻¹ * G4 (a*u^2*v^2) + u * (v^2)⁻¹ * H4 (a*u^2*v^2)
          - a*u^2*v * K4d (a*u^2*v^2)) * Fu u v))
        ((volume.restrict (uIoc δ B)).prod (volume.restrict (Ioc ε A))) := by
      rw [uIoc_of_le hδB]
      exact hprod1
    rw [intervalIntegral_integral_swap hint]
    rw [intervalIntegral.integral_of_le hεA]
  -- E3: outer rung + split over u
  have hbc2 : IntervalIntegrable (fun u => ((δ/u) * J4 (a*u^2*δ^2)
      + u * δ⁻¹ * J4 (a*u^2*δ^2) - (1/2) * K4 (a*u^2*δ^2)) * Fu u δ)
      volume ε A := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hεA]
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
  have hIm2 : IntervalIntegrable (fun u => ∫ v in δ..B,
      ((v/u) * J4 (a*u^2*v^2) + u * v⁻¹ * J4 (a*u^2*v^2)
        - (1/2) * K4 (a*u^2*v^2)) * Fuv u v) volume ε A := by
    rw [intervalIntegrable_iff, uIoc_of_le hεA]
    have hm := hprod2.integral_prod_left
    have he : (fun u => ∫ v in δ..B,
        ((v/u) * J4 (a*u^2*v^2) + u * v⁻¹ * J4 (a*u^2*v^2)
          - (1/2) * K4 (a*u^2*v^2)) * Fuv u v)
        = fun u => ∫ v in Ioc δ B,
        ((v/u) * J4 (a*u^2*v^2) + u * v⁻¹ * J4 (a*u^2*v^2)
          - (1/2) * K4 (a*u^2*v^2)) * Fuv u v :=
      funext fun u => intervalIntegral.integral_of_le hδB
    rw [he]
    exact hm
  have E3 : (∫ u in ε..A, ∫ v in δ..B,
      (u⁻¹ * G4 (a*u^2*v^2) + u * (v^2)⁻¹ * H4 (a*u^2*v^2)
        - a*u^2*v * K4d (a*u^2*v^2)) * Fu u v)
      = -(∫ u in ε..A, ((δ/u) * J4 (a*u^2*δ^2) + u * δ⁻¹ * J4 (a*u^2*δ^2)
            - (1/2) * K4 (a*u^2*δ^2)) * Fu u δ)
        - ∫ u in ε..A, ∫ v in δ..B, ((v/u) * J4 (a*u^2*v^2)
            + u * v⁻¹ * J4 (a*u^2*v^2) - (1/2) * K4 (a*u^2*v^2)) * Fuv u v := by
    rw [intervalIntegral.integral_congr (g := fun u =>
        -(((δ/u) * J4 (a*u^2*δ^2) + u * δ⁻¹ * J4 (a*u^2*δ^2)
            - (1/2) * K4 (a*u^2*δ^2)) * Fu u δ)
        - ∫ v in δ..B, ((v/u) * J4 (a*u^2*v^2) + u * v⁻¹ * J4 (a*u^2*v^2)
            - (1/2) * K4 (a*u^2*v^2)) * Fuv u v) ?_]
    · have hneg2 : IntervalIntegrable (fun u => -(((δ/u) * J4 (a*u^2*δ^2)
          + u * δ⁻¹ * J4 (a*u^2*δ^2) - (1/2) * K4 (a*u^2*δ^2)) * Fu u δ))
          volume ε A := hbc2.neg
      rw [intervalIntegral.integral_sub hneg2 hIm2,
        intervalIntegral.integral_neg]
    · intro u hu
      rw [uIcc_of_le hεA] at hu
      exact corner4_ibp_v a u δ B hδ hδB (ne_of_gt (lt_of_lt_of_le hε hu.1))
        (fun v => Fu u v) (fun v => Fuv u v) (hFud u)
        (hFuvc.comp (continuous_const.prodMk continuous_id)) (hFuB u)
  rw [E1, E2, E3]
  ring

/-- **The `u`-axis boundary dies**: `D1(ε,v) → 0` as `ε → 0⁺` (slope argument
at `G4(0) = 0`). -/
theorem D1_axis_limit (a v : ℝ) (ha : 0 < a) (hv : v ≠ 0) :
    Tendsto (fun ε => ε⁻¹ * G4 (a*ε^2*v^2) + ε * (v^2)⁻¹ * H4 (a*ε^2*v^2)
      - a*ε^2*v * K4d (a*ε^2*v^2)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hG0 : G4 0 = 0 := by
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.G4
      UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4
      UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4d
    norm_num
  have hz : Tendsto (fun ε : ℝ => a*ε^2*v^2) (𝓝[>] 0) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h0 := (by fun_prop : Continuous (fun ε : ℝ => a*ε^2*v^2)).tendsto 0
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        mul_zero, zero_mul] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [mem_Ioi] at hε
      have hvp : 0 < v^2 := by positivity
      have : (0:ℝ) < a*ε^2*v^2 := by positivity
      exact ne_of_gt this
  have hslope := hasDerivAt_iff_tendsto_slope.mp (G4_hasDerivAt 0)
  have hcomp := hslope.comp hz
  have hlin : Tendsto (fun ε : ℝ => a*ε*v^2) (𝓝[>] 0) (𝓝 0) := by
    have h0 := (by fun_prop : Continuous (fun ε : ℝ => a*ε*v^2)).tendsto 0
    simp only [mul_zero, zero_mul] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hT1 : Tendsto (fun ε => ε⁻¹ * G4 (a*ε^2*v^2)) (𝓝[>] 0) (𝓝 0) := by
    have hmul := hcomp.mul hlin
    rw [mul_zero] at hmul
    apply hmul.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [mem_Ioi] at hε
    show slope G4 0 (a*ε^2*v^2) * (a*ε*v^2) = ε⁻¹ * G4 (a*ε^2*v^2)
    rw [slope_def_field, hG0, sub_zero, sub_zero]
    field_simp
  have hT2 : Tendsto (fun ε : ℝ => ε * (v^2)⁻¹ * H4 (a*ε^2*v^2)
      - a*ε^2*v * K4d (a*ε^2*v^2)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => ε * (v^2)⁻¹ * H4 (a*ε^2*v^2)
        - a*ε^2*v * K4d (a*ε^2*v^2)) := by
      unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.H4
        UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4
        UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4d
        UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4d
      fun_prop
    have h0 := hc.tendsto 0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_mul, mul_zero, sub_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have := hT1.add hT2
  simpa using this.congr (fun ε => by ring)

/-- **The `v`-axis boundary carries the axis constant**:
`𝒦(u,δ) → −K4(0)/2 = −1/6` as `δ → 0⁺` — the `−1/6` of the counterterm
cancellation `(3/(2π))·(1/6)·(4π) = 1`. -/
theorem K_axis_limit (a u : ℝ) (ha : 0 < a) (hu : u ≠ 0) :
    Tendsto (fun δ => (δ/u) * J4 (a*u^2*δ^2) + u * δ⁻¹ * J4 (a*u^2*δ^2)
      - (1/2) * K4 (a*u^2*δ^2)) (𝓝[>] (0:ℝ)) (𝓝 (-(1/6))) := by
  have hJ0 : J4 0 = 0 := by
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4
    norm_num
  have hK0 : K4 0 = 1/3 := by
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4
    norm_num
  have hz : Tendsto (fun δ : ℝ => a*u^2*δ^2) (𝓝[>] 0) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h0 := (by fun_prop : Continuous (fun δ : ℝ => a*u^2*δ^2)).tendsto 0
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        mul_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      rw [mem_Ioi] at hδ
      have hup : 0 < u^2 := by positivity
      have : (0:ℝ) < a*u^2*δ^2 := by positivity
      exact ne_of_gt this
  have hslope := hasDerivAt_iff_tendsto_slope.mp (J4_hasDerivAt 0)
  have hcomp := hslope.comp hz
  have hlin : Tendsto (fun δ : ℝ => a*u^3*δ) (𝓝[>] 0) (𝓝 0) := by
    have h0 := (by fun_prop : Continuous (fun δ : ℝ => a*u^3*δ)).tendsto 0
    simp only [mul_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hT2 : Tendsto (fun δ => u * δ⁻¹ * J4 (a*u^2*δ^2)) (𝓝[>] 0) (𝓝 0) := by
    have hmul := hcomp.mul hlin
    rw [mul_zero] at hmul
    apply hmul.congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [mem_Ioi] at hδ
    show slope J4 0 (a*u^2*δ^2) * (a*u^3*δ) = u * δ⁻¹ * J4 (a*u^2*δ^2)
    rw [slope_def_field, hJ0, sub_zero, sub_zero]
    field_simp
  have hT13 : Tendsto (fun δ : ℝ => (δ/u) * J4 (a*u^2*δ^2)
      - (1/2) * K4 (a*u^2*δ^2)) (𝓝[>] 0) (𝓝 (-(1/6))) := by
    have hc : Continuous (fun δ : ℝ => (δ/u) * J4 (a*u^2*δ^2)
        - (1/2) * K4 (a*u^2*δ^2)) := by
      unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4
        UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4
      fun_prop
    have h0 := hc.tendsto 0
    have hval : (0:ℝ)/u * J4 (a*u^2*0^2) - (1/2) * K4 (a*u^2*0^2) = -(1/6) := by
      norm_num [hJ0, hK0]
    rw [hval] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have := hT2.add hT13
  rw [zero_add] at this
  apply this.congr (fun δ => by ring)

#print axioms corner4_rectangle_chain
#print axioms D1_axis_limit
#print axioms K_axis_limit

end UnifiedTheory.Audit.KFCausalMinkowski4DRectangleChain
