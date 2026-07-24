/-
  Audit/KFCausalCSpecCountConcentration.lean   (Volume sector — count-concentration skeleton)

  The DISTRIBUTION-FREE probabilistic skeleton feeding the loop-holonomy band.  It
  supplies the probability of the "good event" that the deterministic band
  (`KFCausalCSpecLoopHolonomyBand`) assumes, WITHOUT yet committing to Poisson.

  Everything here takes the count's mean and variance as HYPOTHESES.  Instantiating
  them for a Poisson count (mean = variance = lambda) is the deliberately separate
  next unit; Mathlib has no Poisson moments, so that instantiation is a one-lemma
  hole (`Var(Poisson lambda) = lambda`) plugged later.

    * `chebyshev_relative_error` : for a count `X` with `mean = lambda`,
      `variance <= lambda`, Chebyshev gives
          Pr(|X/lambda - 1| >= eps)  <=  1/(lambda * eps^2).
      (step 1 -- the concentration mechanism, via Mathlib's Chebyshev.)

    * `edge_failure_bound` : an edge compares TWO counts, so its bad event is a union
      of two single-count tails; a union bound (NO independence) gives
          <=  1/(lambda_u eps^2) + 1/(lambda_v eps^2).
      (the two-count correction, in probability form.)

    * `loop_failure_union_bound` : summing the per-edge bad events over a finite loop
      by a finite union bound (NO independence) bounds the loop's total failure
      probability by the sum of the per-edge bounds.
      (step 4 -- valid for correlated overlapping diamonds precisely because it never
      assumes independence.)

  Chaining these with `loop_holonomy_band` gives: OFF a failure event of the summed
  probability, `U^(-m/d) <= H_gamma <= U^(m/d)`.

  Zero sorry. Zero custom axioms.
-/
import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace UnifiedTheory.Audit.KFCausalCSpecCountConcentration

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Chebyshev relative-error bound (step 1).**  A single normalized count with
`mean = lambda` and `variance <= lambda` concentrates:
`Pr(|X/lambda - 1| >= eps) <= 1/(lambda * eps^2)`.  Distribution-free. -/
theorem chebyshev_relative_error [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    {lam ε : ℝ} (hlam : 0 < lam) (hε : 0 < ε)
    (hmean : μ[X] = lam) (hvar : variance X μ ≤ lam) :
    μ {ω | ε ≤ |X ω / lam - 1|} ≤ ENNReal.ofReal (1 / (lam * ε ^ 2)) := by
  have hset : {ω | ε ≤ |X ω / lam - 1|} = {ω | lam * ε ≤ |X ω - μ[X]|} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [hmean, show X ω / lam - 1 = (X ω - lam) / lam by rw [sub_div, div_self hlam.ne'],
      abs_div, abs_of_pos hlam, le_div_iff₀ hlam, mul_comm ε lam]
  rw [hset]
  refine le_trans (meas_ge_le_variance_div_sq hX (mul_pos hlam hε)) ?_
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_iff₀ (pow_pos (mul_pos hlam hε) 2)]
  have h1 : 1 / (lam * ε ^ 2) * (lam * ε) ^ 2 = lam := by
    field_simp
  rw [h1]
  exact hvar

/-- **Two-count edge bound.**  An edge scale compares two counts, so it fails when
EITHER count's relative error exceeds `eps`.  A union bound (no independence) adds the
two single-count tails. -/
theorem edge_failure_bound [IsFiniteMeasure μ] {Xu Xv : Ω → ℝ}
    (hXu : MemLp Xu 2 μ) (hXv : MemLp Xv 2 μ) {lam_u lam_v ε : ℝ}
    (hlu : 0 < lam_u) (hlv : 0 < lam_v) (hε : 0 < ε)
    (hmu : μ[Xu] = lam_u) (hmv : μ[Xv] = lam_v)
    (hvu : variance Xu μ ≤ lam_u) (hvv : variance Xv μ ≤ lam_v) :
    μ ({ω | ε ≤ |Xu ω / lam_u - 1|} ∪ {ω | ε ≤ |Xv ω / lam_v - 1|})
      ≤ ENNReal.ofReal (1 / (lam_u * ε ^ 2)) + ENNReal.ofReal (1 / (lam_v * ε ^ 2)) :=
  le_trans (measure_union_le _ _)
    (add_le_add (chebyshev_relative_error hXu hlu hε hmu hvu)
      (chebyshev_relative_error hXv hlv hε hmv hvv))

/-- **Loop failure union bound (step 4).**  The loop's total bad event is the union
of the per-edge bad events; a finite union bound (no independence) bounds its measure
by the sum of the per-edge bounds. -/
theorem loop_failure_union_bound {ι : Type*} (s : Finset ι) (B : ι → Set Ω)
    (p : ι → ENNReal) (hp : ∀ i ∈ s, μ (B i) ≤ p i) :
    μ (⋃ i ∈ s, B i) ≤ ∑ i ∈ s, p i :=
  le_trans (measure_biUnion_finset_le s B) (Finset.sum_le_sum hp)

#print axioms chebyshev_relative_error
#print axioms edge_failure_bound
#print axioms loop_failure_union_bound

end UnifiedTheory.Audit.KFCausalCSpecCountConcentration
