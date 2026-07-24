/-
  Audit/KFCausalCSpecContinuationProfile.lean   (arc file 1/6)

  CENTERED CONTINUATION PROFILES AND THE LOCAL CENSUS IDENTITY

  For a chart `i` with three local directions `a : Fin 3`, the depth-r
  continuation profile `raw a : H` records how the direction propagates into the
  common causal carrier `H` (a real inner-product space; concretely the weighted
  L2 space over overlap points and depths).  The census-torsor descent works with
  the CENTERED profile `raw a - (1/3) Σ raw`, which subtracts the direction mean.

  The single provable content of this file is the local form of the census /
  bulk-cancellation identity:  the centered profiles sum to zero over the three
  directions.  Equivalently, every centered profile lands in the zero-sum space
  `V = {x : Σ x = 0}` — the standard S3-representation that the twisted gap
  (file 6) uses.  This is exactly the `CensusIdentities` bulk-cancellation, now
  attached to the direction frame.

  SCOPE: this is the ORDER/CONFORMAL sector.  It carries none of the scale/volume
  data; the metric anchor (interval cardinality) is a separate certificate.

  Zero sorry. Zero custom axioms.
-/
import Mathlib

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecContinuationProfile

open scoped BigOperators RealInnerProductSpace

/-- The three local directions of a regular chart. -/
abbrev Direction := Fin 3

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Centering: subtract the direction mean from each raw continuation profile. -/
noncomputable def centered (raw : Direction → H) : Direction → H :=
  fun a => raw a - (3⁻¹ : ℝ) • (∑ a', raw a')

/-- **Local census identity (bulk cancellation on the frame).** The centered
continuation profiles sum to zero over the three directions: every frame's
centered profiles live in the zero-sum space `V`. -/
theorem centered_sum_zero (raw : Direction → H) :
    ∑ a, centered raw a = 0 := by
  simp only [centered, Fin.sum_univ_three]
  module

/-- Centering is idempotent on its own image up to the mean it already removed:
the mean of a centered family is zero, so re-centering changes nothing. -/
theorem centered_mean_zero (raw : Direction → H) :
    (3⁻¹ : ℝ) • (∑ a', centered raw a') = 0 := by
  rw [centered_sum_zero, smul_zero]

#print axioms centered_sum_zero

end UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
