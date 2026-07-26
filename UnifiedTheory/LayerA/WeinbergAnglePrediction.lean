/-
  LayerA/WeinbergAnglePrediction.lean — sin²θ_W(M_Z) as an OUTPUT of unification with
  the framework's full predicted matter content.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  THE PREDICTION.

  Imposing gauge unification (α₁ = α₂ = α₃ at M_GUT) turns the low-energy inputs
  `A = 1/α_EM(M_Z)` and `T = 1/α_3(M_Z)` into an OUTPUT for `s = sin²θ_W(M_Z)`.  At
  one loop the unification condition is the b-ratio identity
  `α₁⁻¹ − α₂⁻¹ = ρ (α₂⁻¹ − α₃⁻¹)` with `ρ = (b₁−b₂)/(b₂−b₃)`, and the GUT
  normalization gives `α₁⁻¹ = (3/5)(1−s)A`, `α₂⁻¹ = sA`, `α₃⁻¹ = T`.  Solving:

      s = ( 3A/5 + ρT ) / ( A (ρ + 8/5) ).                       (`weinberg_from_unification`)

  NUMERICS (`scripts/weinberg_angle_prediction.py`), with `A = 127.95`, `T = 8.47`:

      SM only                         ρ = 1.896  →  s = 0.2075   (the classic 10%-low miss)
      SM + octet + triplet (no VL)    ρ = ...    →  s = 0.2098   (barely moves: Y=0 can't help)
      SM + octet + triplet + 1 VL     ρ = 1.368  →  s = 0.2326   (measured 0.23122 — 0.6%)

  With proper thresholds (triplet at the 2.7 TeV thermal-DM mass, octet+VL floating,
  `M_GUT` fixed at the derived reduced Planck mass) the prediction is `s = 0.239`
  (3.3%), with `1/α_GUT = 31.9` against the framework's algebraic `32π/3 = 33.5`.

  WHAT THIS SHOWS.  The framework's full predicted content moves `sin²θ_W(M_Z)` from
  the SM's 10%-low `0.207` to within a few percent of the measured `0.231` — and the
  step that closes the gap is exactly the vector-like leptons, whose necessity
  `TraceHyperchargeExile` derives (the Y=0 adjoint sector alone leaves it at 0.210).
  The residual few percent is within one-loop + threshold uncertainty.

  WHAT IS PROVED (zero sorry, zero custom axioms):
   • `weinberg_from_unification` — the closed-form solve `s = (3A/5 + ρT)/(A(ρ+8/5))`
     from the unification b-ratio constraint and the GUT normalization.

  SCOPE (honest).  One loop; the closed form is the single-scale limit (all new
  matter light).  The threshold-resolved value (0.239) uses the derived
  `M_GUT = reduced Planck` and floats the octet/VL scale.  The `b`-coefficients are
  group theory (`AdjointDimension` fixes the adjoint ones); the low-energy `A, T` are
  measured inputs.  Two-loop shifts (~1%) are comparable to the residual and are not
  included.
-/
import Mathlib

set_option autoImplicit false

namespace UnifiedTheory.LayerA.WeinbergAnglePrediction

/-- **sin²θ_W(M_Z) from unification.**  Given the one-loop unification b-ratio
constraint `(3/5)(1−s)A − sA = ρ(sA − T)` (i.e. `α₁⁻¹ − α₂⁻¹ = ρ(α₂⁻¹ − α₃⁻¹)` with
GUT normalization `α₁⁻¹ = (3/5)(1−s)A`, `α₂⁻¹ = sA`, `α₃⁻¹ = T`), the weak angle is
determined by the b-ratio `ρ` and the low-energy inputs `A = 1/α_EM`, `T = 1/α_3`:

    s = (3A/5 + ρT) / (A(ρ + 8/5)). -/
theorem weinberg_from_unification (s A T rho : ℝ)
    (hden : A * (rho + 8 / 5) ≠ 0)
    (hunif : (3 / 5) * (1 - s) * A - s * A = rho * (s * A - T)) :
    s = (3 * A / 5 + rho * T) / (A * (rho + 8 / 5)) := by
  rw [eq_div_iff hden]
  linear_combination -hunif

#print axioms weinberg_from_unification

end UnifiedTheory.LayerA.WeinbergAnglePrediction
