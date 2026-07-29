/-
  Audit/KFCausalMinkowski4DCriticalLine.lean — ONE ZERO, TWO JOBS
  (the critical-line dichotomy of discrete Lorentzian noise)

  The boost group of 4D Minkowski space acts on the causal-interval geometry
  through the multiplicative group (ℝ₊, du/u), whose Plancherel/critical line
  is Re(s) = ½.  The Benincasa–Dowker–Glaser layer weights (1, −9, 16, −8)
  place a Mellin ZERO of the mean pair kernel `f4D` exactly on the critical
  point s = ½, and this single zero does two jobs:

  (i)  MEAN:   it cancels the boost divergence, so ⟨B_ρφ⟩ converges to □φ
       (`f4D_moment_half`, feeding the committed operator theorem);
  (ii) NOISE:  it kills the infrared divergence of the fluctuation covariance
       at separated points (`f4D_w_mass_zero`: the null-boundary w-mass
       vanishes), so the noise field is short-range correlated and every
       extended observable self-averages.

  Meanwhile NO weight system can place such a zero for the noise INTENSITY:
  the variance kernel's coefficients are squares, its critical mass is a sum
  of positive Γ-terms, and it is strictly positive for the BDG weights
  (`f4Dsq_mass_half_pos`) and for EVERY admissible finite layer family
  (`no_self_averaging_GCB`).  Amplitude zeros are possible and load-bearing;
  intensity zeros are impossible: per-point noise is irreducible, extended
  self-averaging is automatic — both consequences of the same critical-line
  structure.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowski4DVarianceRate
import UnifiedTheory.Audit.KFCausalMinkowski4DMesoscale

open MeasureTheory Real Set
open UnifiedTheory.Audit.KFCausalMinkowski4DMoments
open UnifiedTheory.Audit.KFCausalMinkowski4DSecondOrder
open UnifiedTheory.Audit.KFCausalMinkowski4DVarianceRate
open UnifiedTheory.Audit.KFCausalMinkowski4DMesoscale

namespace UnifiedTheory.Audit.KFCausalMinkowski4DCriticalLine

/-- **THE CRITICAL-LINE DICHOTOMY** ("one zero, two jobs").
The 4D BDG mean kernel has its Mellin zero on the critical point s = ½ in
both guises — the Mellin mass and the null-boundary w-mass — while the
variance (intensity) kernel's critical mass is strictly positive.  The same
spectral condition that makes the mean converge makes the noise self-average;
no condition can close the per-point noise channel. -/
theorem critical_line_dichotomy :
    ((∫ ξ in Ioi (0:ℝ), ξ ^ ((1:ℝ)/2 - 1) * f4D ξ) = 0
      ∧ (∫ w in Ioi (0:ℝ), f4D (w^2)) = 0)
    ∧ 0 < ∫ ξ in Ioi (0:ℝ), ξ ^ ((1/2:ℝ) - 1) * f4Dsq ξ :=
  ⟨⟨f4D_moment_half, f4D_w_mass_zero⟩, f4Dsq_mass_half_pos⟩

/-- The impossibility side, for the whole admissible class: any finite layer
family with nonvanishing zeroth weight (forced by the mean's normalization)
has strictly positive intensity mass at the critical point — restated from
`no_self_averaging_GCB`.  Amplitude zeros exist; intensity zeros cannot. -/
theorem intensity_zero_impossible (N : ℕ) (w : ℕ → ℝ)
    (hw : ∃ n, n < N ∧ w n ≠ 0) :
    0 < ∫ ξ in Ioi (0:ℝ), ξ ^ ((1/2:ℝ) - 1) *
      (Real.exp (-ξ) * ∑ n ∈ Finset.range N,
        (w n)^2 * ξ^n / (Nat.factorial n : ℝ)) :=
  no_self_averaging_GCB N w hw

#print axioms critical_line_dichotomy
#print axioms intensity_zero_impossible

end UnifiedTheory.Audit.KFCausalMinkowski4DCriticalLine
