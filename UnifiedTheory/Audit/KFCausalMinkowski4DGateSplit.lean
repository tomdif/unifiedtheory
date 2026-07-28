/-
  Audit/KFCausalMinkowski4DGateSplit.lean — the gate split

  At fixed `a > 0`, the quadrant gate object `√a·∬𝒦·g` splits into exactly the
  three iterated integrals consumed by `bdg_4d_corner_gate`: linearity of the
  inner and outer integrals (per-piece integrability from the kernel bounds),
  the Fubini swap of the `(v/u)`-piece, and the `u·v⁻¹ = u/v` normalization.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowski4DNullReduction

open MeasureTheory Real Set
open UnifiedTheory.Audit.KFCausalMinkowski4DKernel
open UnifiedTheory.Audit.KFCausalMinkowski4DKernelBounds
open UnifiedTheory.Audit.KFCausalMinkowski4DQuadrant
open UnifiedTheory.Audit.KFCausalMinkowski4DNullReduction

namespace UnifiedTheory.Audit.KFCausalMinkowski4DGateSplit

/-- **The gate split**: at fixed `a > 0`, the quadrant gate object splits into
the three iterated integrals consumed by `bdg_4d_corner_gate`. -/
theorem quadrant_gate_split (a A B Mg : ℝ) (ha : 0 < a) (hA : 0 < A) (hB : 0 < B)
    (g : ℝ → ℝ → ℝ) (hgm : Measurable (Function.uncurry g))
    (hgb : ∀ u v, |g u v| ≤ Mg)
    (hsU : ∀ u v, A ≤ u → g u v = 0) (hsV : ∀ u v, B ≤ v → g u v = 0) :
    Real.sqrt a * (∫ u in Set.Ioi (0:ℝ), ∫ v in Set.Ioi (0:ℝ),
        ((v/u) * J4 (a*u^2*v^2) + u * v⁻¹ * J4 (a*u^2*v^2)
          - (1/2) * K4 (a*u^2*v^2)) * g u v)
      = (∫ u in Set.Ioi (0:ℝ), Real.sqrt a * ∫ v in Set.Ioi (0:ℝ),
          (u/v) * J4 (a*u^2*v^2) * g u v)
        + (∫ v in Set.Ioi (0:ℝ), Real.sqrt a * ∫ u in Set.Ioi (0:ℝ),
            (v/u) * J4 (a*u^2*v^2) * g u v)
        - (1/2) * (Real.sqrt a * ∫ u in Set.Ioi (0:ℝ), ∫ v in Set.Ioi (0:ℝ),
            K4 (a*u^2*v^2) * g u v) := by
  have hMg0 : 0 ≤ Mg := le_trans (abs_nonneg _) (hgb 0 0)
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
  have hzq : Measurable (fun p : ℝ × ℝ => a*p.1^2*p.2^2) := by fun_prop
  -- piece measurabilities (uncurried, (u,v) orientation)
  have hm1 : Measurable (Function.uncurry (fun u v =>
      (v/u) * J4 (a*u^2*v^2) * g u v)) :=
    ((measurable_snd.div measurable_fst).mul (hJm.comp hzq)).mul hgm
  have hm2 : Measurable (Function.uncurry (fun u v =>
      u * v⁻¹ * J4 (a*u^2*v^2) * g u v)) :=
    (((measurable_fst.mul measurable_snd.inv)).mul (hJm.comp hzq)).mul hgm
  have hm3 : Measurable (Function.uncurry (fun u v =>
      (1/2) * K4 (a*u^2*v^2) * g u v)) :=
    ((measurable_const.mul (hKm.comp hzq))).mul hgm
  -- pointwise bounds on positives (kernel bounds kill the singular factors)
  have hb1 : ∀ u v, 0 < u → 0 < v → |(v/u) * J4 (a*u^2*v^2) * g u v|
      ≤ a*A*B^3*Mg := by
    intro u v hu hv
    rcases le_or_gt A u with huA | huA
    · rw [hsU u v huA, mul_zero, abs_zero]
      positivity
    rcases le_or_gt B v with hvB | hvB
    · rw [hsV u v hvB, mul_zero, abs_zero]
      positivity
    have hz : 0 ≤ a*u^2*v^2 := by positivity
    rw [abs_mul, abs_mul, abs_div, abs_of_pos hv, abs_of_pos hu]
    have hJ : |J4 (a*u^2*v^2)| ≤ a*u^2*v^2 := J4_abs_le _ hz
    have hstep : v/u * |J4 (a*u^2*v^2)| ≤ a*u*v^3 := by
      calc v/u * |J4 (a*u^2*v^2)| ≤ v/u * (a*u^2*v^2) :=
            mul_le_mul_of_nonneg_left hJ (by positivity)
        _ = a*u*v^3 := by field_simp
    calc v/u * |J4 (a*u^2*v^2)| * |g u v| ≤ (a*u*v^3) * Mg :=
          mul_le_mul hstep (hgb u v) (abs_nonneg _) (by positivity)
      _ ≤ a*A*B^3*Mg := by
          have hv3 : v^3 ≤ B^3 := by
            have hv2 : v^2 ≤ B^2 := by nlinarith
            nlinarith [mul_le_mul_of_nonneg_right hv2 (le_of_lt hv),
              mul_le_mul_of_nonneg_left (le_of_lt hvB) (sq_nonneg B)]
          have : u*v^3 ≤ A*B^3 := by
            nlinarith [mul_le_mul_of_nonneg_right (le_of_lt huA) (by positivity : (0:ℝ) ≤ v^3),
              mul_le_mul_of_nonneg_left hv3 (le_of_lt hA)]
          nlinarith [mul_le_mul_of_nonneg_left this (le_of_lt ha)]
  have hb2 : ∀ u v, 0 < u → 0 < v → |u * v⁻¹ * J4 (a*u^2*v^2) * g u v|
      ≤ a*A^3*B*Mg := by
    intro u v hu hv
    rcases le_or_gt A u with huA | huA
    · rw [hsU u v huA, mul_zero, abs_zero]
      positivity
    rcases le_or_gt B v with hvB | hvB
    · rw [hsV u v hvB, mul_zero, abs_zero]
      positivity
    have hz : 0 ≤ a*u^2*v^2 := by positivity
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hu, abs_of_pos (inv_pos.mpr hv)]
    have hJ : |J4 (a*u^2*v^2)| ≤ a*u^2*v^2 := J4_abs_le _ hz
    have hstep : u * v⁻¹ * |J4 (a*u^2*v^2)| ≤ a*u^3*v := by
      calc u * v⁻¹ * |J4 (a*u^2*v^2)| ≤ u * v⁻¹ * (a*u^2*v^2) :=
            mul_le_mul_of_nonneg_left hJ (by positivity)
        _ = a*u^3*v := by field_simp
    calc u * v⁻¹ * |J4 (a*u^2*v^2)| * |g u v| ≤ (a*u^3*v) * Mg :=
          mul_le_mul hstep (hgb u v) (abs_nonneg _) (by positivity)
      _ ≤ a*A^3*B*Mg := by
          have hu3 : u^3 ≤ A^3 := by
            have hu2 : u^2 ≤ A^2 := by nlinarith
            nlinarith [mul_le_mul_of_nonneg_right hu2 (le_of_lt hu),
              mul_le_mul_of_nonneg_left (le_of_lt huA) (sq_nonneg A)]
          have : u^3*v ≤ A^3*B := by
            nlinarith [mul_le_mul_of_nonneg_right hu3 (le_of_lt hv),
              mul_le_mul_of_nonneg_left (le_of_lt hvB) (by positivity : (0:ℝ) ≤ A^3)]
          nlinarith [mul_le_mul_of_nonneg_left this (le_of_lt ha)]
  have hb3 : ∀ u v, 0 < u → 0 < v → |(1/2) * K4 (a*u^2*v^2) * g u v|
      ≤ (7/2)*Mg := by
    intro u v hu hv
    have hz : 0 ≤ a*u^2*v^2 := by positivity
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
    have hK := UnifiedTheory.Audit.KFCausalMinkowski4DCorner.K4_abs_bound _ hz
    calc 1/2 * |K4 (a*u^2*v^2)| * |g u v| ≤ 1/2 * 7 * Mg := by
          apply mul_le_mul ?_ (hgb u v) (abs_nonneg _) (by norm_num)
          exact mul_le_mul_of_nonneg_left hK (by norm_num)
      _ = (7/2)*Mg := by ring
  -- supports of the pieces
  have hs1U : ∀ u v, 0 < v → A ≤ u → (v/u) * J4 (a*u^2*v^2) * g u v = 0 :=
    fun u v _ hu => by rw [hsU u v hu, mul_zero]
  have hs1V : ∀ u v, 0 < u → B ≤ v → (v/u) * J4 (a*u^2*v^2) * g u v = 0 :=
    fun u v _ hv => by rw [hsV u v hv, mul_zero]
  -- slice integrability (fixed u > 0, in v)
  have hsl : ∀ (h : ℝ → ℝ → ℝ), Measurable (Function.uncurry h) →
      (∀ u v, 0 < u → 0 < v → |h u v| ≤ a*A*B^3*Mg + a*A^3*B*Mg + (7/2)*Mg) →
      (∀ u v, 0 < u → B ≤ v → h u v = 0) →
      ∀ u : ℝ, 0 < u → IntegrableOn (fun v => h u v) (Set.Ioi (0:ℝ)) := by
    intro h hm hb hs u hu
    exact integrableOn_Ioi_of_bounded_support (fun v => h u v)
      (a*A*B^3*Mg + a*A^3*B*Mg + (7/2)*Mg) B hB
      ((hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (fun v hv => hb u v hu hv) (fun v hv => hs u v hu hv)
  set C0 : ℝ := a*A*B^3*Mg + a*A^3*B*Mg + (7/2)*Mg with hC0def
  have hC00 : 0 ≤ C0 := by rw [hC0def]; positivity
  -- slice integrabilities
  have hsl1 := hsl _ hm1 (fun u v hu hv => le_trans (hb1 u v hu hv)
    (by rw [hC0def]; nlinarith [hb2 u v hu hv, hb3 u v hu hv,
      abs_nonneg (u * v⁻¹ * J4 (a*u^2*v^2) * g u v),
      abs_nonneg ((1/2) * K4 (a*u^2*v^2) * g u v)]))
    hs1V
  have hsl2 := hsl _ hm2 (fun u v hu hv => le_trans (hb2 u v hu hv)
    (by rw [hC0def]; nlinarith [hb1 u v hu hv, hb3 u v hu hv,
      abs_nonneg ((v/u) * J4 (a*u^2*v^2) * g u v),
      abs_nonneg ((1/2) * K4 (a*u^2*v^2) * g u v)]))
    (fun u v _ hv => by rw [hsV u v hv, mul_zero])
  have hsl3 := hsl _ hm3 (fun u v hu hv => le_trans (hb3 u v hu hv)
    (by rw [hC0def]; nlinarith [hb1 u v hu hv, hb2 u v hu hv,
      abs_nonneg ((v/u) * J4 (a*u^2*v^2) * g u v),
      abs_nonneg (u * v⁻¹ * J4 (a*u^2*v^2) * g u v)]))
    (fun u v _ hv => by rw [hsV u v hv, mul_zero])
  -- inner split per u
  have hinner : ∀ u : ℝ, 0 < u →
      (∫ v in Set.Ioi (0:ℝ), ((v/u) * J4 (a*u^2*v^2) + u * v⁻¹ * J4 (a*u^2*v^2)
        - (1/2) * K4 (a*u^2*v^2)) * g u v)
      = (∫ v in Set.Ioi (0:ℝ), (v/u) * J4 (a*u^2*v^2) * g u v)
        + (∫ v in Set.Ioi (0:ℝ), u * v⁻¹ * J4 (a*u^2*v^2) * g u v)
        - ∫ v in Set.Ioi (0:ℝ), (1/2) * K4 (a*u^2*v^2) * g u v := by
    intro u hu
    have h12 : MeasureTheory.Integrable (fun v =>
        (v/u) * J4 (a*u^2*v^2) * g u v + u * v⁻¹ * J4 (a*u^2*v^2) * g u v)
        (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) := (hsl1 u hu).add (hsl2 u hu)
    rw [← MeasureTheory.integral_add (hsl1 u hu) (hsl2 u hu),
      ← MeasureTheory.integral_sub h12 (hsl3 u hu)]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro v _
    ring
  -- marginal integrability, generically
  have hmarg : ∀ (h : ℝ → ℝ → ℝ), Measurable (Function.uncurry h) →
      (∀ u v, 0 < u → 0 < v → |h u v| ≤ C0) →
      (∀ u v, 0 < v → A ≤ u → h u v = 0) →
      (∀ u v, 0 < u → B ≤ v → h u v = 0) →
      MeasureTheory.IntegrableOn (fun u => ∫ v in Set.Ioi (0:ℝ), h u v)
        (Set.Ioi (0:ℝ)) := by
    intro h hm hb hsu hsv
    apply integrableOn_Ioi_of_bounded_support _ (C0*B) A hA
    · exact ((hm.stronglyMeasurable.integral_prod_right').measurable
        ).aestronglyMeasurable
    · intro u hu
      have htail := integral_Ioi_sub_interval (fun v => h u v) C0 B B hC00 hB
        le_rfl ((hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
        (fun v hv => hb u v hu hv) (fun v hv => hsv u v hu hv)
      rw [intervalIntegral.integral_same, sub_zero] at htail
      exact htail
    · intro u hu
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        (fun v hv => hsu u v (Set.mem_Ioi.mp hv) hu), MeasureTheory.integral_zero]
  have hM1 := hmarg _ hm1 (fun u v hu hv => le_trans (hb1 u v hu hv)
      (by rw [hC0def]; nlinarith [abs_nonneg (u * v⁻¹ * J4 (a*u^2*v^2) * g u v),
        abs_nonneg ((1/2) * K4 (a*u^2*v^2) * g u v), hb2 u v hu hv, hb3 u v hu hv]))
    hs1U hs1V
  have hM2 := hmarg _ hm2 (fun u v hu hv => le_trans (hb2 u v hu hv)
      (by rw [hC0def]; nlinarith [abs_nonneg ((v/u) * J4 (a*u^2*v^2) * g u v),
        abs_nonneg ((1/2) * K4 (a*u^2*v^2) * g u v), hb1 u v hu hv, hb3 u v hu hv]))
    (fun u v _ hu => by rw [hsU u v hu, mul_zero])
    (fun u v _ hv => by rw [hsV u v hv, mul_zero])
  have hM3 := hmarg _ hm3 (fun u v hu hv => le_trans (hb3 u v hu hv)
      (by rw [hC0def]; nlinarith [abs_nonneg ((v/u) * J4 (a*u^2*v^2) * g u v),
        abs_nonneg (u * v⁻¹ * J4 (a*u^2*v^2) * g u v), hb1 u v hu hv, hb2 u v hu hv]))
    (fun u v _ hu => by rw [hsU u v hu, mul_zero])
    (fun u v _ hv => by rw [hsV u v hv, mul_zero])
  -- outer split
  have houter : (∫ u in Set.Ioi (0:ℝ), ∫ v in Set.Ioi (0:ℝ),
      ((v/u) * J4 (a*u^2*v^2) + u * v⁻¹ * J4 (a*u^2*v^2)
        - (1/2) * K4 (a*u^2*v^2)) * g u v)
      = (∫ u in Set.Ioi (0:ℝ), ∫ v in Set.Ioi (0:ℝ), (v/u) * J4 (a*u^2*v^2) * g u v)
        + (∫ u in Set.Ioi (0:ℝ), ∫ v in Set.Ioi (0:ℝ),
            u * v⁻¹ * J4 (a*u^2*v^2) * g u v)
        - ∫ u in Set.Ioi (0:ℝ), ∫ v in Set.Ioi (0:ℝ),
            (1/2) * K4 (a*u^2*v^2) * g u v := by
    have h12 : MeasureTheory.Integrable (fun u =>
        (∫ v in Set.Ioi (0:ℝ), (v/u) * J4 (a*u^2*v^2) * g u v)
          + ∫ v in Set.Ioi (0:ℝ), u * v⁻¹ * J4 (a*u^2*v^2) * g u v)
        (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) := hM1.add hM2
    rw [← MeasureTheory.integral_add hM1 hM2,
      ← MeasureTheory.integral_sub h12 hM3]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    exact hinner u (Set.mem_Ioi.mp hu)
  -- the T2 Fubini swap
  have hswap : (∫ u in Set.Ioi (0:ℝ), ∫ v in Set.Ioi (0:ℝ),
      (v/u) * J4 (a*u^2*v^2) * g u v)
      = ∫ v in Set.Ioi (0:ℝ), ∫ u in Set.Ioi (0:ℝ),
        (v/u) * J4 (a*u^2*v^2) * g u v :=
    MeasureTheory.integral_integral_swap (prod_box_integrable
      (fun u v => (v/u) * J4 (a*u^2*v^2) * g u v) (a*A*B^3*Mg) A B
      (by positivity) hA hB hm1 hb1 hs1U hs1V)
  -- the u/v-form congruence
  have hform : (∫ u in Set.Ioi (0:ℝ), ∫ v in Set.Ioi (0:ℝ),
      u * v⁻¹ * J4 (a*u^2*v^2) * g u v)
      = ∫ u in Set.Ioi (0:ℝ), ∫ v in Set.Ioi (0:ℝ),
        (u/v) * J4 (a*u^2*v^2) * g u v := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u _
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro v _
    dsimp only
    rw [div_eq_mul_inv]
  -- the half-pull
  have hhalf : (∫ u in Set.Ioi (0:ℝ), ∫ v in Set.Ioi (0:ℝ),
      (1/2) * K4 (a*u^2*v^2) * g u v)
      = (1/2) * ∫ u in Set.Ioi (0:ℝ), ∫ v in Set.Ioi (0:ℝ),
        K4 (a*u^2*v^2) * g u v := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp only
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro v _
    ring
  -- assemble
  rw [houter, hhalf]
  rw [show (∫ u in Set.Ioi (0:ℝ), Real.sqrt a * ∫ v in Set.Ioi (0:ℝ),
      (u/v) * J4 (a*u^2*v^2) * g u v)
      = Real.sqrt a * ∫ u in Set.Ioi (0:ℝ), ∫ v in Set.Ioi (0:ℝ),
        (u/v) * J4 (a*u^2*v^2) * g u v from MeasureTheory.integral_const_mul _ _]
  rw [show (∫ v in Set.Ioi (0:ℝ), Real.sqrt a * ∫ u in Set.Ioi (0:ℝ),
      (v/u) * J4 (a*u^2*v^2) * g u v)
      = Real.sqrt a * ∫ v in Set.Ioi (0:ℝ), ∫ u in Set.Ioi (0:ℝ),
        (v/u) * J4 (a*u^2*v^2) * g u v from MeasureTheory.integral_const_mul _ _]
  rw [← hswap, ← hform]
  ring

#print axioms quadrant_gate_split


end UnifiedTheory.Audit.KFCausalMinkowski4DGateSplit
