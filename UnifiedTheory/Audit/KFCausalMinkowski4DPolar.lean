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

#print axioms polar_iterated

end UnifiedTheory.Audit.KFCausalMinkowski4DPolar
