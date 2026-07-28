/-
  Audit/KFCausalMinkowski4DPolar.lean — R1: the polar factorization, rung a

  The ℝ³ spherical reduction is two applications of the plane polar change of
  variables.  This file packages Mathlib's `integral_comp_polarCoord_symm` into
  the iterated form used by the reduction:

    ∫∫_{ℝ²} f  =  ∫_{r>0} ∫_{θ∈(−π,π)} r·f(r cos θ, r sin θ).
-/
import Mathlib

open MeasureTheory Real Set

namespace UnifiedTheory.Audit.KFCausalMinkowski4DPolar

/-- **The plane polar factorization, iterated form**: for integrable `f` with
integrable polar pullback,

    ∫ x, ∫ y, f(x,y) = ∫_{r>0} ∫_{θ∈(−π,π)} r·f(r cos θ, r sin θ). -/
theorem polar_iterated (f : ℝ × ℝ → ℝ) (hf : Integrable f)
    (hpol : IntegrableOn (fun p : ℝ × ℝ =>
      p.1 * f (p.1 * Real.cos p.2, p.1 * Real.sin p.2))
      (Ioi (0:ℝ) ×ˢ Ioo (-π) π) (volume.prod volume)) :
    (∫ x : ℝ, ∫ y : ℝ, f (x, y))
      = ∫ r in Ioi (0:ℝ), ∫ θ in Ioo (-π) π,
          r * f (r * Real.cos θ, r * Real.sin θ) := by
  have hbase := integral_comp_polarCoord_symm f
  have htarget : polarCoord.target = Ioi (0:ℝ) ×ˢ Ioo (-π) π := rfl
  have hsymm : ∀ p : ℝ × ℝ, polarCoord.symm p
      = (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := fun p => rfl
  have hL : (∫ p in polarCoord.target, p.1 • f (polarCoord.symm p))
      = ∫ r in Ioi (0:ℝ), ∫ θ in Ioo (-π) π,
          r * f (r * Real.cos θ, r * Real.sin θ) := by
    have hEq : (fun p : ℝ × ℝ => p.1 • f (polarCoord.symm p))
        = fun p : ℝ × ℝ =>
          p.1 * f (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := by
      funext p
      rw [smul_eq_mul, hsymm]
    rw [htarget, hEq]
    exact setIntegral_prod _ hpol
  have hR : (∫ p : ℝ × ℝ, f p) = ∫ x : ℝ, ∫ y : ℝ, f (x, y) := by
    exact integral_prod f hf
  rw [← hR, ← hbase, hL]

/-- **R1 rung b — the angle shift**: for a `2π`-periodic integrand, the polar
angle window `(−π,π)` equals the parametrization window `0..2π`. -/
theorem angle_shift (k : ℝ → ℝ) (hk : Function.Periodic k (2*π)) :
    (∫ θ in Ioo (-π) π, k θ) = ∫ ψ in (0:ℝ)..(2*π), k ψ := by
  have h1 : (∫ θ in Ioo (-π) π, k θ) = ∫ θ in (-π)..π, k θ := by
    rw [intervalIntegral.integral_of_le (by linarith [pi_pos] : -π ≤ π),
      integral_Ioc_eq_integral_Ioo]
  have h2 := hk.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2*π = π from by ring, zero_add] at h2
  rw [h1, h2]

/-- **R1 rung c — the half-plane polar factorization**: restricting the second
coordinate to `(0,∞)` restricts the polar angle to `(0,π)`. -/
theorem polar_halfplane (F : ℝ × ℝ → ℝ)
    (hf : Integrable (fun p : ℝ × ℝ =>
      (Ioi (0:ℝ)).indicator (fun s => F (p.1, s)) p.2))
    (hpol : IntegrableOn (fun p : ℝ × ℝ =>
      p.1 * (Ioi (0:ℝ)).indicator (fun s => F (p.1 * Real.cos p.2, s))
        (p.1 * Real.sin p.2))
      (Ioi (0:ℝ) ×ˢ Ioo (-π) π) (volume.prod volume)) :
    (∫ z : ℝ, ∫ s in Ioi (0:ℝ), F (z, s))
      = ∫ r in Ioi (0:ℝ), ∫ θ in Ioo (0:ℝ) π,
          r * F (r * Real.cos θ, r * Real.sin θ) := by
  have hbase := polar_iterated (fun p : ℝ × ℝ =>
    (Ioi (0:ℝ)).indicator (fun s => F (p.1, s)) p.2) hf hpol
  have hL : (∫ x : ℝ, ∫ y : ℝ,
      (Ioi (0:ℝ)).indicator (fun s => F (x, s)) y)
      = ∫ z : ℝ, ∫ s in Ioi (0:ℝ), F (z, s) := by
    refine congrArg _ (funext fun x => ?_)
    exact integral_indicator measurableSet_Ioi
  have hR : ∀ r : ℝ, 0 < r →
      (∫ θ in Ioo (-π) π,
        r * (Ioi (0:ℝ)).indicator (fun s => F (r * Real.cos θ, s))
          (r * Real.sin θ))
      = ∫ θ in Ioo (0:ℝ) π, r * F (r * Real.cos θ, r * Real.sin θ) := by
    intro r hr
    have hcongr : ∀ θ ∈ Ioo (-π) π,
        r * (Ioi (0:ℝ)).indicator (fun s => F (r * Real.cos θ, s))
          (r * Real.sin θ)
        = (Ioo (0:ℝ) π).indicator
            (fun θ' => r * F (r * Real.cos θ', r * Real.sin θ')) θ := by
      intro θ hθw
      by_cases hθ : θ ∈ Ioo (0:ℝ) π
      · rw [Set.indicator_of_mem hθ, Set.indicator_of_mem (Set.mem_Ioi.mpr
          (mul_pos hr (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)))]
      · have hθ0 : θ ≤ 0 := by
          by_contra hpos
          exact hθ ⟨lt_of_not_ge hpos, hθw.2⟩
        have hsin : Real.sin θ ≤ 0 :=
          Real.sin_nonpos_of_nonpos_of_neg_pi_le hθ0 (le_of_lt hθw.1)
        rw [Set.indicator_of_notMem hθ, Set.indicator_of_notMem
          (fun hmem => absurd (Set.mem_Ioi.mp hmem)
            (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos (le_of_lt hr) hsin))),
          mul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioo hcongr,
      integral_indicator measurableSet_Ioo,
      Measure.restrict_restrict measurableSet_Ioo,
      Set.inter_eq_self_of_subset_left (fun x hx => by
        have h := Set.mem_Ioo.mp hx
        exact Set.mem_Ioo.mpr ⟨by linarith [h.1, Real.pi_pos], h.2⟩)]
  rw [← hL, hbase]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  exact hR r (Set.mem_Ioi.mp hr)

#print axioms angle_shift
#print axioms polar_halfplane

/-- **R1 rung d — the spherical factorization**: two polar factorizations
compose into the spherical one; the surface element `r² sin θ` emerges as
`r · (r sin θ)` — the two polar radii. -/
theorem spherical_factorization (h : ℝ → ℝ → ℝ → ℝ)
    (h1 : ∀ z : ℝ, Integrable (fun p : ℝ × ℝ => h p.1 p.2 z))
    (h2 : ∀ z : ℝ, IntegrableOn (fun p : ℝ × ℝ =>
      p.1 * h (p.1 * Real.cos p.2) (p.1 * Real.sin p.2) z)
      (Ioi (0:ℝ) ×ˢ Ioo (-π) π) (volume.prod volume))
    (h3 : Integrable (fun p : ℝ × ℝ => (Ioi (0:ℝ)).indicator
      (fun s => s * ∫ ψ in (0:ℝ)..(2*π),
        h (s * Real.cos ψ) (s * Real.sin ψ) p.1) p.2))
    (h4 : IntegrableOn (fun p : ℝ × ℝ =>
      p.1 * (Ioi (0:ℝ)).indicator
        (fun s => s * ∫ ψ in (0:ℝ)..(2*π),
          h (s * Real.cos ψ) (s * Real.sin ψ) (p.1 * Real.cos p.2))
        (p.1 * Real.sin p.2))
      (Ioi (0:ℝ) ×ˢ Ioo (-π) π) (volume.prod volume)) :
    (∫ z : ℝ, ∫ x : ℝ, ∫ y : ℝ, h x y z)
      = ∫ r in Ioi (0:ℝ), r^2 * ∫ θ in (0:ℝ)..π,
          (∫ ψ in (0:ℝ)..(2*π), h (r * Real.sin θ * Real.cos ψ)
            (r * Real.sin θ * Real.sin ψ) (r * Real.cos θ)) * Real.sin θ := by
  -- E1+E2: per z, the (x,y)-plane in polar with the angle shifted to 0..2π
  have hE12 : ∀ z : ℝ, (∫ x : ℝ, ∫ y : ℝ, h x y z)
      = ∫ s in Ioi (0:ℝ), s * ∫ ψ in (0:ℝ)..(2*π),
          h (s * Real.cos ψ) (s * Real.sin ψ) z := by
    intro z
    rw [polar_iterated (fun p : ℝ × ℝ => h p.1 p.2 z) (h1 z) (h2 z)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s _
    have hper : Function.Periodic
        (fun ψ => s * h (s * Real.cos ψ) (s * Real.sin ψ) z) (2*π) := by
      intro ψ
      simp [Real.cos_add_two_pi, Real.sin_add_two_pi]
    dsimp only
    calc (∫ θ in Ioo (-π) π, s * h (s * Real.cos θ) (s * Real.sin θ) z)
        = ∫ ψ in (0:ℝ)..(2*π), s * h (s * Real.cos ψ) (s * Real.sin ψ) z :=
          angle_shift _ hper
      _ = s * ∫ ψ in (0:ℝ)..(2*π), h (s * Real.cos ψ) (s * Real.sin ψ) z :=
          intervalIntegral.integral_const_mul _ _
  -- E3: the (z,s) half-plane in polar
  have hE3 := polar_halfplane (fun p : ℝ × ℝ =>
    p.2 * ∫ ψ in (0:ℝ)..(2*π),
      h (p.2 * Real.cos ψ) (p.2 * Real.sin ψ) p.1) h3 h4
  calc (∫ z : ℝ, ∫ x : ℝ, ∫ y : ℝ, h x y z)
      = ∫ z : ℝ, ∫ s in Ioi (0:ℝ), s * ∫ ψ in (0:ℝ)..(2*π),
          h (s * Real.cos ψ) (s * Real.sin ψ) z :=
        congrArg _ (funext hE12)
    _ = ∫ r in Ioi (0:ℝ), ∫ θ in Ioo (0:ℝ) π,
          r * ((r * Real.sin θ) * ∫ ψ in (0:ℝ)..(2*π),
            h ((r * Real.sin θ) * Real.cos ψ) ((r * Real.sin θ) * Real.sin ψ)
              (r * Real.cos θ)) := hE3
    _ = ∫ r in Ioi (0:ℝ), r^2 * ∫ θ in (0:ℝ)..π,
          (∫ ψ in (0:ℝ)..(2*π), h (r * Real.sin θ * Real.cos ψ)
            (r * Real.sin θ * Real.sin ψ) (r * Real.cos θ)) * Real.sin θ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r _
        dsimp only
        rw [show (∫ θ in (0:ℝ)..π, (∫ ψ in (0:ℝ)..(2*π),
            h (r * Real.sin θ * Real.cos ψ) (r * Real.sin θ * Real.sin ψ)
              (r * Real.cos θ)) * Real.sin θ)
            = ∫ θ in Ioo (0:ℝ) π, (∫ ψ in (0:ℝ)..(2*π),
              h (r * Real.sin θ * Real.cos ψ) (r * Real.sin θ * Real.sin ψ)
                (r * Real.cos θ)) * Real.sin θ from by
          rw [intervalIntegral.integral_of_le (le_of_lt Real.pi_pos),
            integral_Ioc_eq_integral_Ioo]]
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioo
        intro θ _
        dsimp only
        ring

#print axioms spherical_factorization

/-- **The polished spherical factorization**: for a continuous field supported
in the ball of radius `S`, all four integrability hypotheses discharge. -/
theorem spherical_factorization_cc (h : ℝ → ℝ → ℝ → ℝ) (S : ℝ) (hS : 0 < S)
    (hc : Continuous (fun p : ℝ × ℝ × ℝ => h p.1 p.2.1 p.2.2))
    (hsupp : ∀ x y z, S^2 ≤ x^2 + y^2 + z^2 → h x y z = 0) :
    (∫ z : ℝ, ∫ x : ℝ, ∫ y : ℝ, h x y z)
      = ∫ r in Ioi (0:ℝ), r^2 * ∫ θ in (0:ℝ)..π,
          (∫ ψ in (0:ℝ)..(2*π), h (r * Real.sin θ * Real.cos ψ)
            (r * Real.sin θ * Real.sin ψ) (r * Real.cos θ)) * Real.sin θ := by
  -- global bound from compact support
  have hcs : HasCompactSupport (fun p : ℝ × ℝ × ℝ => h p.1 p.2.1 p.2.2) := by
    apply HasCompactSupport.intro
      (K := Icc (-S) S ×ˢ (Icc (-S) S ×ˢ Icc (-S) S))
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
    intro p hp
    rw [Set.mem_prod, not_and_or] at hp
    rcases hp with h1 | h23
    · rw [Set.mem_Icc, not_and_or] at h1
      apply hsupp
      rcases h1 with ha | hb
      · nlinarith [lt_of_not_ge ha, sq_nonneg p.2.1, sq_nonneg p.2.2]
      · nlinarith [lt_of_not_ge hb, sq_nonneg p.2.1, sq_nonneg p.2.2]
    · rw [Set.mem_prod, not_and_or] at h23
      rcases h23 with h2 | h3
      · rw [Set.mem_Icc, not_and_or] at h2
        apply hsupp
        rcases h2 with ha | hb
        · nlinarith [lt_of_not_ge ha, sq_nonneg p.1, sq_nonneg p.2.2]
        · nlinarith [lt_of_not_ge hb, sq_nonneg p.1, sq_nonneg p.2.2]
      · rw [Set.mem_Icc, not_and_or] at h3
        apply hsupp
        rcases h3 with ha | hb
        · nlinarith [lt_of_not_ge ha, sq_nonneg p.1, sq_nonneg p.2.1]
        · nlinarith [lt_of_not_ge hb, sq_nonneg p.1, sq_nonneg p.2.1]
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hc
  have hCb : ∀ x y z, |h x y z| ≤ C := fun x y z => by
    simpa [Real.norm_eq_abs] using hC (x, y, z)
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hCb 0 0 0)
  -- the ψ-integral: uniform bound, radial support, measurability
  have hIbnd : ∀ s z : ℝ, |∫ ψ in (0:ℝ)..(2*π),
      h (s * Real.cos ψ) (s * Real.sin ψ) z| ≤ C * (2*π) := by
    intro s z
    rw [← Real.norm_eq_abs]
    apply le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := C) (fun ψ _ => by rw [Real.norm_eq_abs]; exact hCb _ _ _))
    rw [sub_zero, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2*π)]
  have hIzero : ∀ s z : ℝ, S^2 ≤ s^2 + z^2 →
      (∫ ψ in (0:ℝ)..(2*π), h (s * Real.cos ψ) (s * Real.sin ψ) z) = 0 := by
    intro s z hsz
    rw [intervalIntegral.integral_congr (g := fun _ => 0) (fun ψ _ => by
      apply hsupp
      have hcs2 := Real.sin_sq_add_cos_sq ψ
      nlinarith [hcs2])]
    simp
  have hImeas : Measurable (fun p : ℝ × ℝ => ∫ ψ in (0:ℝ)..(2*π),
      h (p.2 * Real.cos ψ) (p.2 * Real.sin ψ) p.1) := by
    have hKm : Measurable (Function.uncurry (fun (p : ℝ × ℝ) (ψ : ℝ) =>
        h (p.2 * Real.cos ψ) (p.2 * Real.sin ψ) p.1)) := by
      exact hc.measurable.comp (by fun_prop : Measurable
        (fun q : (ℝ × ℝ) × ℝ =>
          ((q.1.2 * Real.cos q.2, q.1.2 * Real.sin q.2, q.1.1) : ℝ × ℝ × ℝ)))
    have he : (fun p : ℝ × ℝ => ∫ ψ in (0:ℝ)..(2*π),
        h (p.2 * Real.cos ψ) (p.2 * Real.sin ψ) p.1)
        = fun p : ℝ × ℝ => ∫ ψ in Ioc (0:ℝ) (2*π),
          h (p.2 * Real.cos ψ) (p.2 * Real.sin ψ) p.1 :=
      funext fun p => intervalIntegral.integral_of_le (by positivity)
    rw [he]
    exact (hKm.stronglyMeasurable.integral_prod_right').measurable
  apply spherical_factorization h
  -- h1: the (x,y)-slice is continuous with compact support
  · intro z
    have hslc : Continuous (fun p : ℝ × ℝ => h p.1 p.2 z) :=
      hc.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))
    apply hslc.integrable_of_hasCompactSupport
    apply HasCompactSupport.intro (K := Icc (-S) S ×ˢ Icc (-S) S)
      (isCompact_Icc.prod isCompact_Icc)
    intro p hp
    rw [Set.mem_prod, not_and_or] at hp
    apply hsupp
    rcases hp with h1 | h2
    · rw [Set.mem_Icc, not_and_or] at h1
      rcases h1 with ha | hb
      · nlinarith [lt_of_not_ge ha, sq_nonneg p.2, sq_nonneg z]
      · nlinarith [lt_of_not_ge hb, sq_nonneg p.2, sq_nonneg z]
    · rw [Set.mem_Icc, not_and_or] at h2
      rcases h2 with ha | hb
      · nlinarith [lt_of_not_ge ha, sq_nonneg p.1, sq_nonneg z]
      · nlinarith [lt_of_not_ge hb, sq_nonneg p.1, sq_nonneg z]
  -- h2: the polar pullback per z, on the finite-measure box
  · intro z
    have hdom : MeasureTheory.IntegrableOn
        ((Ioc (0:ℝ) S ×ˢ Ioo (-π) π).indicator (fun _ => S * C))
        (Ioi (0:ℝ) ×ˢ Ioo (-π) π) (volume.prod volume) := by
      apply MeasureTheory.Integrable.integrableOn
      rw [MeasureTheory.integrable_indicator_iff
        (measurableSet_Ioc.prod measurableSet_Ioo)]
      have hbox : (volume.prod volume) (Ioc (0:ℝ) S ×ˢ Ioo (-π) π) ≠ ⊤ := by
        rw [Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioo]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
      exact MeasureTheory.integrableOn_const (hs := hbox)
    apply MeasureTheory.Integrable.mono' hdom
    · exact ((continuous_fst.mul (hc.comp ((continuous_fst.mul
        (Real.continuous_cos.comp continuous_snd)).prodMk
        ((continuous_fst.mul (Real.continuous_sin.comp continuous_snd)).prodMk
          continuous_const)))).aestronglyMeasurable)
    · apply MeasureTheory.ae_restrict_of_forall_mem
        (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      have hp1 : (0:ℝ) < p.1 := hp.1
      by_cases hpS : p.1 ≤ S
      · rw [Set.indicator_of_mem (Set.mem_prod.mpr
          ⟨Set.mem_Ioc.mpr ⟨hp1, hpS⟩, hp.2⟩), Real.norm_eq_abs, abs_mul,
          abs_of_pos hp1]
        calc p.1 * |h (p.1 * Real.cos p.2) (p.1 * Real.sin p.2) z|
            ≤ p.1 * C := mul_le_mul_of_nonneg_left (hCb _ _ _) (le_of_lt hp1)
          _ ≤ S * C := mul_le_mul_of_nonneg_right hpS hC0
      · have hz : h (p.1 * Real.cos p.2) (p.1 * Real.sin p.2) z = 0 := by
          apply hsupp
          have hexp : (p.1 * Real.cos p.2)^2 + (p.1 * Real.sin p.2)^2
              = p.1^2 := by
            linear_combination p.1^2 * (Real.sin_sq_add_cos_sq p.2)
          have hprod := mul_pos (sub_pos.mpr (lt_of_not_ge hpS))
            (show (0:ℝ) < p.1 + S by linarith [hS])
          nlinarith [hexp, hprod, sq_nonneg z]
        rw [Set.indicator_of_notMem (fun hmem =>
          hpS (Set.mem_Ioc.mp (Set.mem_prod.mp hmem).1).2), hz, mul_zero,
          norm_zero]
  -- h3: the half-plane family is bounded with box support
  · have hdom : MeasureTheory.Integrable
        ((Icc (-S) S ×ˢ Icc (0:ℝ) S).indicator (fun _ => S * (C * (2*π))))
        (volume : Measure (ℝ × ℝ)) := by
      rw [MeasureTheory.integrable_indicator_iff
        (measurableSet_Icc.prod measurableSet_Icc)]
      exact MeasureTheory.integrableOn_const (hs := by
        rw [show (volume : Measure (ℝ × ℝ)) (Icc (-S) S ×ˢ Icc (0:ℝ) S)
            = volume (Icc (-S) S) * volume (Icc (0:ℝ) S) from
          Measure.prod_prod _ _]
        rw [Real.volume_Icc, Real.volume_Icc]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    apply MeasureTheory.Integrable.mono' hdom
    · have heq : (fun p : ℝ × ℝ => (Ioi (0:ℝ)).indicator
          (fun s => s * ∫ ψ in (0:ℝ)..(2*π),
            h (s * Real.cos ψ) (s * Real.sin ψ) p.1) p.2)
          = fun p : ℝ × ℝ => ({q : ℝ × ℝ | 0 < q.2}).indicator
            (fun q => q.2 * ∫ ψ in (0:ℝ)..(2*π),
              h (q.2 * Real.cos ψ) (q.2 * Real.sin ψ) q.1) p := by
        funext p
        by_cases hp2 : 0 < p.2
        · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hp2),
            Set.indicator_of_mem (show p ∈ {q : ℝ × ℝ | 0 < q.2} from hp2)]
        · rw [Set.indicator_of_notMem (fun hmem => hp2 (Set.mem_Ioi.mp hmem)),
            Set.indicator_of_notMem
              (show p ∉ {q : ℝ × ℝ | 0 < q.2} from fun hmem => hp2 hmem)]
      rw [heq]
      exact ((measurable_snd.mul hImeas).indicator
        (measurableSet_lt measurable_const measurable_snd)).aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro p
      by_cases hp2 : 0 < p.2
      · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hp2)]
        by_cases hbox : |p.1| ≤ S ∧ p.2 ≤ S
        · rw [Set.indicator_of_mem (Set.mem_prod.mpr
            ⟨Set.mem_Icc.mpr (abs_le.mp hbox.1),
             Set.mem_Icc.mpr ⟨le_of_lt hp2, hbox.2⟩⟩), Real.norm_eq_abs,
            abs_mul, abs_of_pos hp2]
          calc p.2 * |∫ ψ in (0:ℝ)..(2*π),
              h (p.2 * Real.cos ψ) (p.2 * Real.sin ψ) p.1|
              ≤ p.2 * (C * (2*π)) :=
                mul_le_mul_of_nonneg_left (hIbnd _ _) (le_of_lt hp2)
            _ ≤ S * (C * (2*π)) := mul_le_mul_of_nonneg_right hbox.2
                (mul_nonneg hC0 (by positivity))
        · have hz : (∫ ψ in (0:ℝ)..(2*π),
              h (p.2 * Real.cos ψ) (p.2 * Real.sin ψ) p.1) = 0 := by
            apply hIzero
            rw [not_and_or] at hbox
            rcases hbox with ha | hb
            · have habs := lt_of_not_ge ha
              have hprod := mul_pos (sub_pos.mpr habs)
                (show (0:ℝ) < |p.1| + S by positivity)
              nlinarith [hprod, sq_abs p.1, sq_nonneg p.2]
            · have hprod := mul_pos (sub_pos.mpr (lt_of_not_ge hb))
                (show (0:ℝ) < p.2 + S by linarith [hS, hp2])
              nlinarith [hprod, sq_nonneg p.1]
          rw [hz, mul_zero, norm_zero]
          exact Set.indicator_nonneg (fun _ _ =>
            mul_nonneg (le_of_lt hS) (mul_nonneg hC0 (by positivity))) _
      · rw [Set.indicator_of_notMem (fun hmem => hp2 (Set.mem_Ioi.mp hmem)),
          norm_zero]
        exact Set.indicator_nonneg (fun _ _ =>
          mul_nonneg (le_of_lt hS) (mul_nonneg hC0 (by positivity))) _
  -- h4: the half-plane polar pullback, on the finite-measure box
  · have hdom : MeasureTheory.IntegrableOn
        ((Ioc (0:ℝ) S ×ˢ Ioo (-π) π).indicator (fun _ => S * (S * (C * (2*π)))))
        (Ioi (0:ℝ) ×ˢ Ioo (-π) π) (volume.prod volume) := by
      apply MeasureTheory.Integrable.integrableOn
      rw [MeasureTheory.integrable_indicator_iff
        (measurableSet_Ioc.prod measurableSet_Ioo)]
      have hbox : (volume.prod volume) (Ioc (0:ℝ) S ×ˢ Ioo (-π) π) ≠ ⊤ := by
        rw [Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioo]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
      exact MeasureTheory.integrableOn_const (hs := hbox)
    apply MeasureTheory.Integrable.mono' hdom
    · have heq : (fun p : ℝ × ℝ => p.1 * (Ioi (0:ℝ)).indicator
          (fun s => s * ∫ ψ in (0:ℝ)..(2*π),
            h (s * Real.cos ψ) (s * Real.sin ψ) (p.1 * Real.cos p.2))
          (p.1 * Real.sin p.2))
          = fun p : ℝ × ℝ => p.1 * ({q : ℝ × ℝ | 0 < q.1 * Real.sin q.2}).indicator
            (fun q => (q.1 * Real.sin q.2) * ∫ ψ in (0:ℝ)..(2*π),
              h ((q.1 * Real.sin q.2) * Real.cos ψ)
                ((q.1 * Real.sin q.2) * Real.sin ψ) (q.1 * Real.cos q.2)) p := by
        funext p
        by_cases hps : 0 < p.1 * Real.sin p.2
        · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hps),
            Set.indicator_of_mem (show p ∈ {q : ℝ × ℝ | 0 < q.1 * Real.sin q.2}
              from hps)]
        · rw [Set.indicator_of_notMem (fun hmem => hps (Set.mem_Ioi.mp hmem)),
            Set.indicator_of_notMem
              (show p ∉ {q : ℝ × ℝ | 0 < q.1 * Real.sin q.2}
                from fun hmem => hps hmem)]
      rw [heq]
      have hin : Measurable (fun q : ℝ × ℝ =>
          (q.1 * Real.sin q.2) * ∫ ψ in (0:ℝ)..(2*π),
            h ((q.1 * Real.sin q.2) * Real.cos ψ)
              ((q.1 * Real.sin q.2) * Real.sin ψ) (q.1 * Real.cos q.2)) := by
        have hmap : Measurable (fun q : ℝ × ℝ =>
            ((q.1 * Real.cos q.2, q.1 * Real.sin q.2) : ℝ × ℝ)) := by
          fun_prop
        exact (measurable_fst.mul (Real.measurable_sin.comp measurable_snd)).mul
          (hImeas.comp hmap)
      exact (measurable_fst.mul (hin.indicator
        (measurableSet_lt measurable_const
          (measurable_fst.mul
            (Real.measurable_sin.comp measurable_snd))))).aestronglyMeasurable
    · apply MeasureTheory.ae_restrict_of_forall_mem
        (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      have hp1 : (0:ℝ) < p.1 := hp.1
      by_cases hpS : p.1 ≤ S
      · rw [Set.indicator_of_mem (Set.mem_prod.mpr
          ⟨Set.mem_Ioc.mpr ⟨hp1, hpS⟩, hp.2⟩), Real.norm_eq_abs, abs_mul,
          abs_of_pos hp1]
        have hinner : |(Ioi (0:ℝ)).indicator
            (fun s => s * ∫ ψ in (0:ℝ)..(2*π),
              h (s * Real.cos ψ) (s * Real.sin ψ) (p.1 * Real.cos p.2))
            (p.1 * Real.sin p.2)| ≤ S * (C * (2*π)) := by
          by_cases hps : 0 < p.1 * Real.sin p.2
          · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hps), abs_mul,
              abs_of_pos hps]
            have hsle : p.1 * Real.sin p.2 ≤ S :=
              le_trans (mul_le_of_le_one_right (le_of_lt hp1)
                (Real.sin_le_one _)) hpS
            calc (p.1 * Real.sin p.2) * |∫ ψ in (0:ℝ)..(2*π),
                h ((p.1 * Real.sin p.2) * Real.cos ψ)
                  ((p.1 * Real.sin p.2) * Real.sin ψ) (p.1 * Real.cos p.2)|
                ≤ (p.1 * Real.sin p.2) * (C * (2*π)) :=
                  mul_le_mul_of_nonneg_left (hIbnd _ _) (le_of_lt hps)
              _ ≤ S * (C * (2*π)) := mul_le_mul_of_nonneg_right hsle
                  (mul_nonneg hC0 (by positivity))
          · rw [Set.indicator_of_notMem (fun hmem =>
              hps (Set.mem_Ioi.mp hmem)), abs_zero]
            exact mul_nonneg (le_of_lt hS) (mul_nonneg hC0 (by positivity))
        refine le_trans (mul_le_mul_of_nonneg_left hinner (le_of_lt hp1)) ?_
        exact mul_le_mul_of_nonneg_right hpS
          (mul_nonneg (le_of_lt hS) (mul_nonneg hC0 (by positivity)))
      · have hz : (Ioi (0:ℝ)).indicator
            (fun s => s * ∫ ψ in (0:ℝ)..(2*π),
              h (s * Real.cos ψ) (s * Real.sin ψ) (p.1 * Real.cos p.2))
            (p.1 * Real.sin p.2) = 0 := by
          by_cases hps : 0 < p.1 * Real.sin p.2
          · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hps)]
            rw [hIzero _ _ (by
              have hexp : (p.1 * Real.sin p.2)^2 + (p.1 * Real.cos p.2)^2
                  = p.1^2 := by
                linear_combination p.1^2 * (Real.sin_sq_add_cos_sq p.2)
              have hprod := mul_pos (sub_pos.mpr (lt_of_not_ge hpS))
                (show (0:ℝ) < p.1 + S by linarith [hS])
              nlinarith [hexp, hprod]), mul_zero]
          · exact Set.indicator_of_notMem (fun hmem =>
              hps (Set.mem_Ioi.mp hmem)) _
        rw [Set.indicator_of_notMem (fun hmem =>
          hpS (Set.mem_Ioc.mp (Set.mem_prod.mp hmem).1).2), hz, mul_zero,
          norm_zero]

#print axioms spherical_factorization_cc

#print axioms polar_iterated

end UnifiedTheory.Audit.KFCausalMinkowski4DPolar
