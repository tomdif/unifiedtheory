/-
  Audit/KFCausalMinkowski4DLogRate.lean — THE LOG-DIVERGENCE RATE
  (fluctuation campaign, central analysis)

  For a kernel with mass (the variance's `f4Dsq`, mass `(315/2)√π`), the boost
  profile integral is the divergence, and its rate is exactly logarithmic with
  an explicit error bound:

    | ∫₀^∞ g(s, (√a·s)⁻¹)/s ds  −  g(0,0)·ln(A·√a·B) |  ≤  Mu·A + Mv·B.

  The supports make the window `[(√a·B)⁻¹, A]` sharp on both ends; inside it
  the profile differs from `g(0,0)` by `Mu·s + Mv·(√a·s)⁻¹`, whose `/s`
  integrals are bounded uniformly in `a`.  Multiplied by the fluctuation mass,
  this is the `½·ln ρ` coefficient of the causal-set variance. -/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowski4DQuadrant

open MeasureTheory Real Set
open UnifiedTheory.Audit.KFCausalMinkowski4DQuadrant

namespace UnifiedTheory.Audit.KFCausalMinkowski4DLogRate

/-- **The log-divergence rate of the massive boost profile.** -/
theorem log_rate (g pdug pdvg : ℝ → ℝ → ℝ) (Mu Mv A B : ℝ)
    (hA : 0 < A) (hB : 0 < B)
    (hgc : Continuous (Function.uncurry g))
    (hdu : ∀ v u, HasDerivAt (fun u' => g u' v) (pdug u v) u)
    (hdv : ∀ u v, HasDerivAt (fun v' => g u v') (pdvg u v) v)
    (hMu : ∀ u v, |pdug u v| ≤ Mu) (hMv : ∀ u v, |pdvg u v| ≤ Mv)
    (hsuppU : ∀ u v, A ≤ u → g u v = 0) (hsuppV : ∀ u v, B ≤ v → g u v = 0)
    (a : ℝ) (ha : 0 < a) (hwin : (Real.sqrt a * B)⁻¹ < A) :
    |(∫ s in Ioi (0:ℝ), g s ((Real.sqrt a * s)⁻¹) / s)
      - g 0 0 * Real.log (A * (Real.sqrt a * B))| ≤ Mu * A + Mv * B := by
  have hMu0 : 0 ≤ Mu := le_trans (abs_nonneg _) (hMu 0 0)
  have hMv0 : 0 ≤ Mv := le_trans (abs_nonneg _) (hMv 0 0)
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  set lo := (Real.sqrt a * B)⁻¹ with hlodef
  have hlo : 0 < lo := by positivity
  have hloA : lo ≤ A := le_of_lt hwin
  -- the two-variable MVT bound
  have hmvt : ∀ s y : ℝ, 0 ≤ s → 0 ≤ y → |g s y - g 0 0| ≤ Mu * s + Mv * y := by
    intro s y hs hy
    have h1 : |g s y - g 0 y| ≤ Mu * s := by
      have h := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := fun u => g u y) (f' := fun u => pdug u y) (C := Mu) (s := Set.univ)
        (fun u _ => (hdu y u).hasDerivWithinAt)
        (fun u _ => by simpa [Real.norm_eq_abs] using hMu u y)
        (Set.mem_univ 0) (Set.mem_univ s)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg hs] at h
      exact h
    have h2 : |g 0 y - g 0 0| ≤ Mv * y := by
      have h := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := fun v => g 0 v) (f' := fun v => pdvg 0 v) (C := Mv) (s := Set.univ)
        (fun v _ => (hdv 0 v).hasDerivWithinAt)
        (fun v _ => by simpa [Real.norm_eq_abs] using hMv 0 v)
        (Set.mem_univ 0) (Set.mem_univ y)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg hy] at h
      exact h
    rw [abs_le]
    constructor <;> linarith [h1, h2, le_abs_self (g s y - g 0 y),
      neg_abs_le (g s y - g 0 y), le_abs_self (g 0 y - g 0 0),
      neg_abs_le (g 0 y - g 0 0)]
  -- window sharpness
  have hoff : ∀ s : ℝ, 0 < s → s ∉ Ioc lo A →
      g s ((Real.sqrt a * s)⁻¹) = 0 := by
    intro s hs hnot
    rw [Set.mem_Ioc, not_and_or] at hnot
    rcases hnot with h1 | h2
    · apply hsuppV
      have hle : s ≤ lo := not_lt.mp h1
      have h3 : Real.sqrt a * s ≤ 1 / B := by
        calc Real.sqrt a * s ≤ Real.sqrt a * lo :=
              mul_le_mul_of_nonneg_left hle (le_of_lt hsa)
          _ = 1 / B := by rw [hlodef]; field_simp
      calc B = 1 / (1/B) := by field_simp
        _ ≤ 1 / (Real.sqrt a * s) := one_div_le_one_div_of_le (by positivity) h3
        _ = (Real.sqrt a * s)⁻¹ := one_div _
    · exact hsuppU _ _ (le_of_lt (lt_of_not_ge h2))
  -- reduce to the window
  have hwinint : (∫ s in Ioi (0:ℝ), g s ((Real.sqrt a * s)⁻¹) / s)
      = ∫ s in Ioc lo A, g s ((Real.sqrt a * s)⁻¹) / s := by
    rw [show (∫ s in Ioi (0:ℝ), g s ((Real.sqrt a * s)⁻¹) / s)
        = ∫ s in Ioi (0:ℝ),
          (Ioc lo A).indicator (fun s => g s ((Real.sqrt a * s)⁻¹) / s) s from by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      rw [mem_Ioi] at hs
      dsimp only
      by_cases hmem : s ∈ Ioc lo A
      · rw [Set.indicator_of_mem hmem]
      · rw [Set.indicator_of_notMem hmem, hoff s hs hmem, zero_div]]
    rw [integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc,
      Set.inter_eq_self_of_subset_left
        (fun x hx => Set.mem_Ioi.mpr (lt_trans hlo hx.1))]
  -- the reference logarithm
  have h0notin : (0:ℝ) ∉ uIcc lo A := by
    rw [uIcc_of_le hloA]
    intro hmem
    exact absurd hmem.1 (not_le.mpr hlo)
  have hlogint : (∫ s in Ioc lo A, s⁻¹) = Real.log (A * (Real.sqrt a * B)) := by
    rw [← intervalIntegral.integral_of_le hloA, integral_inv h0notin,
      show A / lo = A * (Real.sqrt a * B) from by rw [hlodef]; field_simp]
  -- the inverse-square primitive on the window
  have hsqint : (∫ s in Ioc lo A, (s^2)⁻¹) = lo⁻¹ - A⁻¹ := by
    rw [← intervalIntegral.integral_of_le hloA]
    have hder : ∀ x ∈ uIcc lo A, HasDerivAt (fun t => -t⁻¹) ((x^2)⁻¹) x := by
      intro x hx
      rw [uIcc_of_le hloA] at hx
      have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hlo hx.1)
      have h := (hasDerivAt_inv hx0).neg
      simpa using h
    have hcont : ContinuousOn (fun s : ℝ => (s^2)⁻¹) (uIcc lo A) := by
      rw [uIcc_of_le hloA]
      exact ((continuousOn_id.pow 2).inv₀
        (fun x hx => pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hlo hx.1))))
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
      (hcont.intervalIntegrable)]
    ring
  -- integrability of the window integrands
  have hcontg : ContinuousOn (fun s => g s ((Real.sqrt a * s)⁻¹) / s)
      (Icc lo A) := by
    apply ContinuousOn.div
    · exact hgc.comp_continuousOn (continuousOn_id.prodMk
        ((continuousOn_const.mul continuousOn_id).inv₀
          (fun x hx => ne_of_gt (mul_pos hsa (lt_of_lt_of_le hlo hx.1)))))
    · exact continuousOn_id
    · exact fun x hx => ne_of_gt (lt_of_lt_of_le hlo hx.1)
  have hint1 : IntegrableOn (fun s => g s ((Real.sqrt a * s)⁻¹) / s)
      (Ioc lo A) :=
    (hcontg.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hcontinv : ContinuousOn (fun s : ℝ => g 0 0 * s⁻¹) (Icc lo A) :=
    continuousOn_const.mul (continuousOn_id.inv₀
      (fun x hx => ne_of_gt (lt_of_lt_of_le hlo hx.1)))
  have hint2 : IntegrableOn (fun s : ℝ => g 0 0 * s⁻¹) (Ioc lo A) :=
    (hcontinv.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hcontdom : ContinuousOn
      (fun s : ℝ => Mu + Mv * (Real.sqrt a)⁻¹ * (s^2)⁻¹) (Icc lo A) :=
    continuousOn_const.add (continuousOn_const.mul
      ((continuousOn_id.pow 2).inv₀
        (fun x hx => pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hlo hx.1)))))
  have hdomint : IntegrableOn
      (fun s : ℝ => Mu + Mv * (Real.sqrt a)⁻¹ * (s^2)⁻¹) (Ioc lo A) :=
    (hcontdom.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  -- assemble
  rw [hwinint, ← hlogint]
  have hEq : (∫ s in Ioc lo A, g s ((Real.sqrt a * s)⁻¹) / s)
      - g 0 0 * ∫ s in Ioc lo A, s⁻¹
      = ∫ s in Ioc lo A,
          (g s ((Real.sqrt a * s)⁻¹) / s - g 0 0 * s⁻¹) := by
    rw [← integral_const_mul, ← integral_sub hint1 hint2]
  rw [hEq, ← Real.norm_eq_abs]
  apply le_trans (norm_integral_le_of_norm_le hdomint ?_)
  · -- evaluate the dominator integral and close
    have hconst : (∫ s in Ioc lo A, (Mu : ℝ))
        = Mu * (A - lo) := by
      rw [setIntegral_const]
      show (MeasureTheory.volume (Ioc lo A)).toReal • Mu = Mu * (A - lo)
      rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
      ring
    have hsqpart : IntegrableOn
        (fun s : ℝ => Mv * (Real.sqrt a)⁻¹ * (s^2)⁻¹) (Ioc lo A) :=
      ((continuousOn_const.mul ((continuousOn_id.pow 2).inv₀
        (fun x hx => pow_ne_zero 2 (ne_of_gt
          (lt_of_lt_of_le hlo hx.1))))).integrableOn_compact
        isCompact_Icc).mono_set Ioc_subset_Icc_self
    have hsplit : (∫ s in Ioc lo A,
        (Mu + Mv * (Real.sqrt a)⁻¹ * (s^2)⁻¹))
        = Mu * (A - lo) + Mv * (Real.sqrt a)⁻¹ * (lo⁻¹ - A⁻¹) := by
      have hMuconst : IntegrableOn (fun _ : ℝ => Mu) (Ioc lo A) :=
        ((continuousOn_const : ContinuousOn (fun _ : ℝ => Mu) (Icc lo A)
          ).integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
      rw [integral_add hMuconst hsqpart, hconst, integral_const_mul, hsqint]
    rw [hsplit]
    have hloinv : lo⁻¹ = Real.sqrt a * B := by rw [hlodef, inv_inv]
    have hbound2 : Mv * (Real.sqrt a)⁻¹ * (lo⁻¹ - A⁻¹) ≤ Mv * B := by
      rw [hloinv]
      have h1 : Real.sqrt a * B - A⁻¹ ≤ Real.sqrt a * B := by
        have : (0:ℝ) < A⁻¹ := by positivity
        linarith
      calc Mv * (Real.sqrt a)⁻¹ * (Real.sqrt a * B - A⁻¹)
          ≤ Mv * (Real.sqrt a)⁻¹ * (Real.sqrt a * B) := by
            apply mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = Mv * B := by field_simp
    have hbound1 : Mu * (A - lo) ≤ Mu * A := by
      apply mul_le_mul_of_nonneg_left ?_ hMu0
      linarith
    linarith [hbound1, hbound2]
  · apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro s hs
    have hs0 : 0 < s := lt_trans hlo hs.1
    have hy0 : 0 ≤ (Real.sqrt a * s)⁻¹ := by positivity
    rw [Real.norm_eq_abs,
      show g s ((Real.sqrt a * s)⁻¹) / s - g 0 0 * s⁻¹
        = (g s ((Real.sqrt a * s)⁻¹) - g 0 0) / s from by
      field_simp]
    rw [abs_div, abs_of_pos hs0, div_le_iff₀ hs0]
    calc |g s ((Real.sqrt a * s)⁻¹) - g 0 0|
        ≤ Mu * s + Mv * (Real.sqrt a * s)⁻¹ :=
          hmvt s _ (le_of_lt hs0) hy0
      _ = (Mu + Mv * (Real.sqrt a)⁻¹ * (s^2)⁻¹) * s := by
          field_simp

end UnifiedTheory.Audit.KFCausalMinkowski4DLogRate
