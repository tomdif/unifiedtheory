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

#print axioms polar_iterated

end UnifiedTheory.Audit.KFCausalMinkowski4DPolar
