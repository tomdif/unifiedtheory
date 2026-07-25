/-
  Audit/KFCausalCSpecLayerMomentConditions.lean   (Volume sector → goal B, layer conditions)

  The moment conditions on the BDG layer coefficients, built on the Poisson factorial
  moments (`KFCausalCSpecPoissonFactorialMoment`).

  The causal-set d'Alembertian / BDG action mean is a LAYER-WEIGHTED sum `Σ_k c_k (·)`
  over order-interval layer indices, expressed in the falling-factorial basis where the
  Poisson moments are exact (`E[(N)_k] = r^k`).  Two facts control it:

    * `poisson_layerResponse_hasSum` : the mean layer response is the POLYNOMIAL
        Σ_k c_k r^k  in the intensity `r` (linearity over the factorial moments);
    * `layerResponse_secondOrder` : the conditions `c_0 = c_1 = 0` (annihilate constant
        and linear fields) force that polynomial to be `r^2 · Q(r)`, i.e. SECOND ORDER.

  After the volume integral `r ~ ρ V`, a second-order response is exactly what yields the
  Laplacian `□` plus the curvature term: the BDG coefficients are chosen so their
  factorial-basis constant and linear parts vanish, killing the volume-divergent orders.
  This is the discrete algebraic core of the continuum-limit construction (the full limit
  additionally needs interval-volume geometry + asymptotic Poisson integrals).

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalCSpecPoissonFactorialMoment

set_option autoImplicit false

open Real NNReal ProbabilityTheory
open UnifiedTheory.Audit.KFCausalCSpecPoissonFactorialMoment

namespace UnifiedTheory.Audit.KFCausalCSpecLayerMomentConditions

/-- **Mean layer response is a polynomial in the intensity.**  For layer coefficients `c`
(supported on `range K`), the Poisson-mean of the layer-weighted operator, in the
falling-factorial basis, sums to the polynomial `Σ_k c_k r^k`.  Linearity over the exact
factorial moments `E[(N)_k] = r^k`. -/
theorem poisson_layerResponse_hasSum (r : ℝ≥0) (K : ℕ) (c : ℕ → ℝ) :
    HasSum (fun n => poissonPMFReal r n *
        ∑ k ∈ Finset.range K, c k * (Nat.descFactorial n k : ℝ))
      (∑ k ∈ Finset.range K, c k * (r : ℝ) ^ k) := by
  have h : HasSum (fun n => ∑ k ∈ Finset.range K,
      c k * (poissonPMFReal r n * (Nat.descFactorial n k : ℝ)))
      (∑ k ∈ Finset.range K, c k * (r : ℝ) ^ k) := by
    apply hasSum_sum
    intro k _
    exact (poissonPMFReal_descFactorial_hasSum r k).mul_left (c k)
  have heq : ∀ n, poissonPMFReal r n * ∑ k ∈ Finset.range K, c k * (Nat.descFactorial n k : ℝ)
      = ∑ k ∈ Finset.range K, c k * (poissonPMFReal r n * (Nat.descFactorial n k : ℝ)) := by
    intro n
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp only [heq]
  exact h

/-- **Second-order condition.**  If the layer coefficients annihilate the constant and
linear parts (`c 0 = 0`, `c 1 = 0`), the mean response polynomial `Σ_k c_k r^k` is
`r^2 · Q(r)` -- second order in the intensity, so the volume-divergent (0th and 1st order)
contributions cancel and only the Laplacian + curvature order survives. -/
theorem layerResponse_secondOrder (K : ℕ) (c : ℕ → ℝ) (h0 : c 0 = 0) (h1 : c 1 = 0) (r : ℝ) :
    ∑ k ∈ Finset.range K, c k * r ^ k
      = r ^ 2 * ∑ k ∈ Finset.range K, c k * (if 2 ≤ k then r ^ (k - 2) else 0) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · simp [h0]
    · simp [h1]
  · rw [if_pos hk]
    have hpow : r ^ k = r ^ 2 * r ^ (k - 2) := by rw [← pow_add]; congr 1; omega
    rw [hpow]; ring

/-- **The surviving second-order coefficient is `c 2`.**  Evaluating the factored
polynomial's cofactor `Q` at `r = 0` isolates the `k = 2` layer weight -- the curvature
normalization of the operator. -/
theorem layerResponse_leadingCoeff (K : ℕ) (c : ℕ → ℝ) (hK : 2 < K) :
    ∑ k ∈ Finset.range K, c k * (if 2 ≤ k then (0 : ℝ) ^ (k - 2) else 0) = c 2 := by
  rw [Finset.sum_eq_single 2]
  · simp
  · intro k _ hk2
    rcases Nat.lt_or_ge k 2 with hk | hk
    · rw [if_neg (by omega)]; ring
    · rw [if_pos hk]
      have : k - 2 ≠ 0 := by omega
      rw [zero_pow this]; ring
  · intro h
    exact absurd (Finset.mem_range.mpr hK) h

#print axioms poisson_layerResponse_hasSum
#print axioms layerResponse_secondOrder
#print axioms layerResponse_leadingCoeff

end UnifiedTheory.Audit.KFCausalCSpecLayerMomentConditions
