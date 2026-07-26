/-
  Audit/KFCausalMinkowskiFrullani.lean   (Volume sector → Frullani + the K4 zero mass)

  Rung 4c of the 4D ladder: FRULLANI'S INTEGRAL — the named missing library lemma of
  the K4-corner — formalized for the class the corner needs (`C¹`, bounded
  derivative, vanishing past `R`), plus the K4 boost-volume zero mass.

  FRULLANI (`frullani`):  for such `f` and `b ≥ 1`,

      ∫₀^∞ (f(b·u) − f(u))/u du  =  −f(0)·ln b.

  Proof (ε-truncation, all steps elementary):
   • on `(ε,∞)` the substitution `s = b·u` gives the EXACT identity
     `∫_ε^∞ (f(bu)−f(u))/u du = −∫_{Ioc ε bε} f(s)/s ds`;
   • as `ε → 0⁺` the left side tends to the full integral (the integrand is bounded
     by `M(b−1)` — mean value — so the `(0,ε]` piece is `O(ε)`), and the right side
     tends to `−f(0)ln b` (`∫_{Ioc ε bε} s⁻¹ = ln b` exactly; the `f − f(0)` error is
     again `O(ε)` by the mean-value bound);
   • uniqueness of limits along `𝓝[>]0` closes it.

  THE K4 ZERO MASS (`K4_mass_zero`):  `∫₀^∞ K4(w²) dw = 0` — the substituted form of
  `M[K4](½) = 0`, the fact that kills the divergent boost volume in the K4-corner.

  K4-CORNER STATUS after this file: of its ingredients — boost measure exactly
  `K4(w²)dw·dτ` (Jacobian `1/√a`, computed), boost-volume cancellation
  (`K4_mass_zero`, HERE), the Frullani evaluation of the log-difference (`frullani`,
  HERE), the corner constant `C_K = √π/3` — all analytic content is now
  machine-checked or exactly derived; the remaining formal step is the iterated-1D
  assembly (substitution–Fubini–subtraction–DCT with the `|K4(w²)|(C + |ln w|)`
  dominator), the same shape as the closed J4-edge slice chain.

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowski4DEdgeAssembly

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory Real Set Filter Topology
open UnifiedTheory.Audit.KFCausalMinkowski4DKernel
open UnifiedTheory.Audit.KFCausalMinkowski4DGate
open UnifiedTheory.Audit.KFCausalMinkowski4DEdge

namespace UnifiedTheory.Audit.KFCausalMinkowskiFrullani

/-! ## Frullani's integral (C¹, bounded derivative, vanishing past `R`) -/

/-- **Frullani's integral.**  For `f ∈ C¹` with `|f'| ≤ M`, vanishing past `R`, and
`b ≥ 1`:  `∫₀^∞ (f(bu) − f(u))/u du = −f(0)·ln b`. -/
theorem frullani (f f' : ℝ → ℝ) (M R : ℝ) (hR : 0 < R)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hM : ∀ x, |f' x| ≤ M)
    (hsupp : ∀ x, R ≤ x → f x = 0)
    (b : ℝ) (hb : 1 ≤ b) :
    ∫ u in Ioi (0:ℝ), (f (b*u) - f u) / u = -(f 0) * Real.log b := by
  have hb0 : (0:ℝ) < b := lt_of_lt_of_le one_pos hb
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  -- mean-value bound
  have hlip : ∀ x y : ℝ, |f x - f y| ≤ M * |x - y| := by
    intro x y
    have h := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := f) (f' := f') (fun z _ => (hd z).hasDerivWithinAt)
      (fun z _ => by simpa [Real.norm_eq_abs] using hM z) (mem_univ y) (mem_univ x)
    simpa [Real.norm_eq_abs] using h
  -- |f| ≤ M·R on [0,∞)
  have hfb : ∀ s : ℝ, 0 ≤ s → |f s| ≤ M * R := by
    intro s hs
    by_cases h : R ≤ s
    · rw [hsupp s h]; simpa using mul_nonneg hM0 hR.le
    · push_neg at h
      have := hlip s R
      rw [hsupp R le_rfl, sub_zero] at this
      calc |f s| ≤ M * |s - R| := this
        _ ≤ M * R := by
            apply mul_le_mul_of_nonneg_left ?_ hM0
            rw [abs_sub_comm, abs_of_nonneg (by linarith)]
            linarith
  -- the full integrand is integrable on (0,∞): bounded by M(b−1)... ≤ M·b, support ≤ R
  have hintfull : IntegrableOn (fun u => (f (b*u) - f u) / u) (Ioi (0:ℝ)) := by
    have hmeas : AEStronglyMeasurable (fun u => (f (b*u) - f u) / u)
        (volume.restrict (Ioi (0:ℝ))) := by
      exact (((hfc.comp (continuous_const.mul continuous_id)).sub hfc).measurable.div
        measurable_id).aestronglyMeasurable
    have hDint : Integrable (fun u => (Ioc (0:ℝ) R).indicator (fun _ => M * b) u) := by
      rw [integrable_indicator_iff measurableSet_Ioc]
      exact integrableOn_const (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    apply Integrable.mono' hDint.integrableOn hmeas
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro u hu
    rw [mem_Ioi] at hu
    by_cases huR : u ≤ R
    · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hu, huR⟩), Real.norm_eq_abs, abs_div,
        div_le_iff₀ (abs_pos.mpr hu.ne')]
      calc |f (b*u) - f u| ≤ M * |b*u - u| := hlip (b*u) u
        _ = M * ((b-1)*u) := by
            rw [show b*u - u = (b-1)*u from by ring,
              abs_of_nonneg (mul_nonneg (by linarith) hu.le)]
        _ ≤ M * b * |u| := by
            rw [abs_of_pos hu]
            nlinarith
    · push_neg at huR
      have h1 : f (b*u) = 0 := hsupp _ (le_trans huR.le (le_mul_of_one_le_left hu.le hb))
      have h2 : f u = 0 := hsupp _ huR.le
      rw [h1, h2, sub_zero, zero_div, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => mul_nonneg hM0 hb0.le) u
  -- the ε-identity: on (ε,∞), the integral equals −∫_{Ioc ε bε} f/s
  have hident : ∀ ε : ℝ, 0 < ε →
      (∫ u in Ioi ε, (f (b*u) - f u) / u) = -∫ s in Ioc ε (b*ε), f s / s := by
    intro ε hε
    have hεb : ε ≤ b * ε := le_mul_of_one_le_left hε.le hb
    -- integrability of f s / s on Ioi δ for δ > 0
    have hfs_int : ∀ δ : ℝ, 0 < δ → IntegrableOn (fun s => f s / s) (Ioi δ) := by
      intro δ hδ
      have hmeas : AEStronglyMeasurable (fun s => f s / s) (volume.restrict (Ioi δ)) :=
        (hfc.measurable.div measurable_id).aestronglyMeasurable
      have hDint : Integrable (fun s => (Ioc δ R).indicator (fun _ => M * R / δ) s) := by
        rw [integrable_indicator_iff measurableSet_Ioc]
        exact integrableOn_const (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      apply Integrable.mono' hDint.integrableOn hmeas
      apply ae_restrict_of_forall_mem measurableSet_Ioi
      intro s hs
      rw [mem_Ioi] at hs
      have hs0 : 0 < s := lt_trans hδ hs
      by_cases hsR : s ≤ R
      · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hs, hsR⟩), Real.norm_eq_abs, abs_div,
          abs_of_pos hs0]
        rw [div_eq_mul_one_div, div_eq_mul_one_div (M*R) δ]
        exact mul_le_mul (hfb s hs0.le) (one_div_le_one_div_of_le hδ hs.le)
          (by positivity) (mul_nonneg hM0 hR.le)
      · push_neg at hsR
        rw [hsupp s hsR.le, zero_div, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => by positivity) s
    -- substitution: ∫_{Ioi ε} f(bu)/u = ∫_{Ioi bε} f/s
    have hsub : (∫ u in Ioi ε, f (b*u) / u) = ∫ s in Ioi (b*ε), f s / s := by
      have hcomp := integral_comp_mul_left_Ioi (fun s => f s / s) ε hb0
      rw [smul_eq_mul] at hcomp
      have hcancel : (∫ x in Ioi ε, (fun s => f s / s) (b * x))
          = ∫ x in Ioi ε, b⁻¹ * (f (b*x) / x) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        rw [mem_Ioi] at hx
        have hx0 : 0 < x := lt_trans hε hx
        show f (b*x) / (b*x) = b⁻¹ * (f (b*x) / x)
        field_simp
      rw [hcancel, integral_const_mul] at hcomp
      -- hcomp : b⁻¹ * ∫ f(bx)/x = b⁻¹ * ∫_{Ioi bε} f/s
      have := mul_left_cancel₀ (inv_ne_zero hb0.ne') hcomp
      exact this
    -- split the (ε,∞) integral of f/s
    have hsplit : (∫ s in Ioi ε, f s / s)
        = (∫ s in Ioc ε (b*ε), f s / s) + ∫ s in Ioi (b*ε), f s / s := by
      rw [← Ioc_union_Ioi_eq_Ioi hεb,
        setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
          ((hfs_int ε hε).mono_set Ioc_subset_Ioi_self)
          ((hfs_int ε hε).mono_set (Ioi_subset_Ioi hεb))]
    -- assemble
    have hpt : (∫ u in Ioi ε, (f (b*u) - f u) / u)
        = (∫ u in Ioi ε, f (b*u) / u) - ∫ u in Ioi ε, f u / u := by
      rw [← integral_sub]
      · apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        dsimp only
        rw [sub_div]
      · -- integrability of f(bu)/u on Ioi ε
        have hmeas : AEStronglyMeasurable (fun u => f (b*u) / u)
            (volume.restrict (Ioi ε)) :=
          ((hfc.comp (continuous_const.mul continuous_id)).measurable.div
            measurable_id).aestronglyMeasurable
        have hDint : Integrable (fun u => (Ioc ε R).indicator (fun _ => M * R / ε) u) := by
          rw [integrable_indicator_iff measurableSet_Ioc]
          exact integrableOn_const (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
        apply Integrable.mono' hDint.integrableOn hmeas
        apply ae_restrict_of_forall_mem measurableSet_Ioi
        intro u hu
        rw [mem_Ioi] at hu
        have hu0 : 0 < u := lt_trans hε hu
        by_cases huR : u ≤ R
        · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hu, huR⟩), Real.norm_eq_abs, abs_div,
            abs_of_pos hu0]
          rw [div_eq_mul_one_div, div_eq_mul_one_div (M*R) ε]
          exact mul_le_mul (hfb (b*u) (by positivity)) (one_div_le_one_div_of_le hε hu.le)
            (by positivity) (mul_nonneg hM0 hR.le)
        · push_neg at huR
          rw [hsupp (b*u) (le_trans huR.le (le_mul_of_one_le_left hu0.le hb)), zero_div,
            norm_zero]
          exact Set.indicator_nonneg (fun _ _ => by positivity) u
      · exact hfs_int ε hε
    rw [hpt, hsub, hsplit]
    ring
  -- limit of the left side: → full integral
  have hIoc_small : ∀ ε : ℝ, 0 < ε →
      |∫ u in Ioc (0:ℝ) ε, (f (b*u) - f u) / u| ≤ M * b * ε := by
    intro ε hε
    have h := norm_setIntegral_le_of_norm_le_const (C := M * b)
      (s := Ioc (0:ℝ) ε) (f := fun u => (f (b*u) - f u) / u)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) ?_
    · rw [Real.norm_eq_abs] at h
      calc |∫ u in Ioc (0:ℝ) ε, (f (b*u) - f u) / u|
          ≤ M * b * (volume (Ioc (0:ℝ) ε)).toReal := h
        _ = M * b * ε := by
            rw [Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hε.le]
    · intro u hu
      obtain ⟨hu0, huε⟩ := hu
      rw [Real.norm_eq_abs, abs_div, div_le_iff₀ (abs_pos.mpr hu0.ne')]
      calc |f (b*u) - f u| ≤ M * |b*u - u| := hlip (b*u) u
        _ = M * ((b-1)*u) := by
            rw [show b*u - u = (b-1)*u from by ring,
              abs_of_nonneg (mul_nonneg (by linarith) hu0.le)]
        _ ≤ M * b * |u| := by
            rw [abs_of_pos hu0]
            nlinarith
  have hA : Tendsto (fun ε => ∫ u in Ioi ε, (f (b*u) - f u) / u) (𝓝[>] (0:ℝ))
      (𝓝 (∫ u in Ioi (0:ℝ), (f (b*u) - f u) / u)) := by
    have hsplit0 : ∀ ε : ℝ, 0 < ε →
        (∫ u in Ioi ε, (f (b*u) - f u) / u)
          = (∫ u in Ioi (0:ℝ), (f (b*u) - f u) / u)
            - ∫ u in Ioc (0:ℝ) ε, (f (b*u) - f u) / u := by
      intro ε hε
      rw [show (∫ u in Ioi (0:ℝ), (f (b*u) - f u) / u)
          = (∫ u in Ioc (0:ℝ) ε, (f (b*u) - f u) / u)
            + ∫ u in Ioi ε, (f (b*u) - f u) / u from by
        rw [← Ioc_union_Ioi_eq_Ioi hε.le,
          setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
            (hintfull.mono_set Ioc_subset_Ioi_self)
            (hintfull.mono_set (Ioi_subset_Ioi hε.le))]]
      ring
    have hr : Tendsto (fun ε => ∫ u in Ioc (0:ℝ) ε, (f (b*u) - f u) / u)
        (𝓝[>] (0:ℝ)) (𝓝 0) := by
      apply squeeze_zero_norm'
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        replace hε : 0 < ε := hε
        simpa [Real.norm_eq_abs] using hIoc_small ε hε
      · have h : Tendsto (fun ε : ℝ => M*b*ε) (𝓝 (0:ℝ)) (𝓝 (M*b*0)) :=
          (continuous_const.mul continuous_id).tendsto (0:ℝ)
        rw [mul_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
    have hconst : Tendsto (fun _ : ℝ => ∫ u in Ioi (0:ℝ), (f (b*u) - f u) / u)
        (𝓝[>] (0:ℝ)) (𝓝 (∫ u in Ioi (0:ℝ), (f (b*u) - f u) / u)) := tendsto_const_nhds
    have h := hconst.sub hr
    rw [sub_zero] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    replace hε : 0 < ε := hε
    exact (hsplit0 ε hε).symm
  -- limit of the right side: → −f(0)·log b
  have hlog : ∀ ε : ℝ, 0 < ε → (∫ s in Ioc ε (b*ε), (f 0) * s⁻¹) = f 0 * Real.log b := by
    intro ε hε
    have hεb : ε ≤ b * ε := le_mul_of_one_le_left hε.le hb
    rw [integral_const_mul]
    congr 1
    rw [← intervalIntegral.integral_of_le hεb, integral_inv (by
      rw [Set.uIcc_of_le hεb]
      intro hmem
      exact absurd hmem.1 (not_le.mpr hε)),
      mul_div_assoc, div_self hε.ne', mul_one]
  have herr_small : ∀ ε : ℝ, 0 < ε →
      |∫ s in Ioc ε (b*ε), (f s - f 0) / s| ≤ M * (b*ε - ε) := by
    intro ε hε
    have h := norm_setIntegral_le_of_norm_le_const (C := M)
      (s := Ioc ε (b*ε)) (f := fun s => (f s - f 0) / s)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) ?_
    · rw [Real.norm_eq_abs] at h
      calc |∫ s in Ioc ε (b*ε), (f s - f 0) / s|
          ≤ M * (volume (Ioc ε (b*ε))).toReal := h
        _ ≤ M * (b*ε - ε) := by
            rw [Real.volume_Ioc, ENNReal.toReal_ofReal
              (by nlinarith [le_mul_of_one_le_left hε.le hb] : (0:ℝ) ≤ b*ε - ε)]
    · intro s hs
      obtain ⟨hs1, _⟩ := hs
      have hs0 : 0 < s := lt_trans hε hs1
      rw [Real.norm_eq_abs, abs_div, div_le_iff₀ (abs_pos.mpr hs0.ne')]
      calc |f s - f 0| ≤ M * |s - 0| := hlip s 0
        _ = M * |s| := by rw [sub_zero]
  have hBsplit : ∀ ε : ℝ, 0 < ε →
      (∫ s in Ioc ε (b*ε), f s / s)
        = f 0 * Real.log b + ∫ s in Ioc ε (b*ε), (f s - f 0) / s := by
    intro ε hε
    rw [← hlog ε hε, ← integral_add]
    · apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      obtain ⟨hs1, _⟩ := hs
      have hs0 : 0 < s := lt_trans hε hs1
      dsimp only
      field_simp
      try ring
    · -- integrability of f0 * s⁻¹ on Ioc ε bε
      have hmeas : AEStronglyMeasurable (fun s : ℝ => (f 0) * s⁻¹)
          (volume.restrict (Ioc ε (b*ε))) :=
        (measurable_const.mul measurable_inv).aestronglyMeasurable
      have hDint : Integrable
          (fun s => (Ioc ε (b*ε)).indicator (fun _ => |f 0| / ε) s) := by
        rw [integrable_indicator_iff measurableSet_Ioc]
        exact integrableOn_const (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      apply Integrable.mono' hDint.integrableOn hmeas ?_
      apply ae_restrict_of_forall_mem measurableSet_Ioc
      intro s hs
      obtain ⟨hs1, hs2⟩ := hs
      have hs0 : 0 < s := lt_trans hε hs1
      rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hs1, hs2⟩), Real.norm_eq_abs, abs_mul,
        abs_inv, abs_of_pos hs0]
      rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le hε hs1.le
    · -- integrability of (f s − f0)/s on Ioc ε bε
      have hmeas : AEStronglyMeasurable (fun s : ℝ => (f s - f 0) / s)
          (volume.restrict (Ioc ε (b*ε))) :=
        ((hfc.sub continuous_const).measurable.div measurable_id).aestronglyMeasurable
      have hDint : Integrable
          (fun s => (Ioc ε (b*ε)).indicator (fun _ => M) s) := by
        rw [integrable_indicator_iff measurableSet_Ioc]
        exact integrableOn_const (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      apply Integrable.mono' hDint.integrableOn hmeas ?_
      apply ae_restrict_of_forall_mem measurableSet_Ioc
      intro s hs
      obtain ⟨hs1, hs2⟩ := hs
      have hs0 : 0 < s := lt_trans hε hs1
      rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hs1, hs2⟩), Real.norm_eq_abs, abs_div,
        div_le_iff₀ (abs_pos.mpr hs0.ne')]
      calc |f s - f 0| ≤ M * |s - 0| := hlip s 0
        _ = M * |s| := by rw [sub_zero]
  have herr : Tendsto (fun ε => ∫ s in Ioc ε (b*ε), (f s - f 0) / s)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    apply squeeze_zero_norm'
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      replace hε : 0 < ε := hε
      simpa [Real.norm_eq_abs] using herr_small ε hε
    · have h2 : Tendsto (fun ε : ℝ => M * ((b-1)*ε)) (𝓝 (0:ℝ)) (𝓝 0) := by
        have h0 : Tendsto (fun ε : ℝ => M * ((b-1)*ε)) (𝓝 (0:ℝ)) (𝓝 (M * ((b-1)*0))) :=
          (continuous_const.mul (continuous_const.mul continuous_id)).tendsto (0:ℝ)
        simpa using h0
      have h3 : (fun ε : ℝ => M * (b*ε - ε)) = fun ε : ℝ => M * ((b-1)*ε) := by
        funext ε; ring
      rw [h3]
      exact h2.mono_left nhdsWithin_le_nhds
  have hB : Tendsto (fun ε => -∫ s in Ioc ε (b*ε), f s / s) (𝓝[>] (0:ℝ))
      (𝓝 (-(f 0) * Real.log b)) := by
    have hconst : Tendsto (fun _ : ℝ => f 0 * Real.log b) (𝓝[>] (0:ℝ))
        (𝓝 (f 0 * Real.log b)) := tendsto_const_nhds
    have h := (hconst.add herr).neg
    rw [add_zero] at h
    have h2 : Tendsto (fun ε => -(f 0 * Real.log b + ∫ s in Ioc ε (b*ε), (f s - f 0) / s))
        (𝓝[>] (0:ℝ)) (𝓝 (-(f 0) * Real.log b)) := by
      convert h using 2
      ring
    apply h2.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    replace hε : 0 < ε := hε
    rw [hBsplit ε hε]
  -- uniqueness of limits
  have hAB : Tendsto (fun ε => -∫ s in Ioc ε (b*ε), f s / s) (𝓝[>] (0:ℝ))
      (𝓝 (∫ u in Ioi (0:ℝ), (f (b*u) - f u) / u)) := by
    apply hA.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    replace hε : 0 < ε := hε
    exact hident ε hε
  exact tendsto_nhds_unique hAB hB

/-! ## The K4 boost-volume zero mass -/

/-- **`∫₀^∞ K4(w²) dw = 0`** — the substituted `M[K4](½) = 0`: the fact that cancels
the divergent boost volume in the K4-corner. -/
theorem K4_mass_zero : ∫ w in Ioi (0:ℝ), K4 (w^2) = 0 := by
  have hsub := integral_comp_rpow_Ioi (fun ξ => ξ ^ ((1:ℝ)/2 - 1) * K4 ξ) (p := 2) (by norm_num)
  rw [K4_moment_half] at hsub
  have key : (∫ x in Ioi (0:ℝ), (|(2:ℝ)| * x ^ ((2:ℝ) - 1)) •
      ((fun ξ => ξ ^ ((1:ℝ)/2 - 1) * K4 ξ) (x ^ (2:ℝ))))
      = ∫ x in Ioi (0:ℝ), 2 * K4 (x^2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    rw [mem_Ioi] at hx
    dsimp only
    rw [smul_eq_mul]
    rw [show x ^ ((2:ℝ) - 1) = x from by
        rw [show (2:ℝ) - 1 = 1 from by norm_num, Real.rpow_one],
      show (x ^ (2:ℝ)) ^ ((1:ℝ)/2 - 1) = x⁻¹ from by
        rw [← Real.rpow_mul hx.le,
          show (2:ℝ) * ((1:ℝ)/2 - 1) = -1 from by norm_num, Real.rpow_neg_one],
      show x ^ (2:ℝ) = x ^ (2:ℕ) from by rw [← Real.rpow_natCast x 2]; norm_num,
      show |(2:ℝ)| = 2 from abs_of_pos (by norm_num)]
    have hne : x ≠ 0 := hx.ne'
    field_simp
    try ring
  rw [key, integral_const_mul] at hsub
  linarith [hsub]

#print axioms frullani
#print axioms K4_mass_zero

end UnifiedTheory.Audit.KFCausalMinkowskiFrullani
