/-
Algebra supporting the chiral continuum comparison experiment.

These results fix the chirality dictionary, isolate the fifth-order resolvent
response, and distinguish it from amplitude-polynomial subtractions of degree
at most four. They do not prove cutoff convergence, the complete measure-current
comparison, or a dynamical continuum Standard Model.
-/
import UnifiedTheory.Audit.KFCausalOverlapChirality
import Mathlib.Algebra.Polynomial.Degree.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalChiralContinuumComparison
noncomputable section
open Matrix
open UnifiedTheory.Audit.KFCausalOverlapChirality

section ChiralityDictionary
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "Operator" => Matrix ι ι ℂ

/-- The repository's positive sign-projector is the negative deformed chirality. -/
theorem negative_domain_is_positive_sign (g e : Operator) (hg : g * g = 1) :
    minus (chirality g (overlap g e)) = plus e := by
  rw [overlap_chirality g e hg]
  simp [minus, plus]

/-- Hsu's positive continuum chiral domain matches the complementary sign-projector. -/
theorem positive_domain_is_negative_sign (g e : Operator) (hg : g * g = 1) :
    plus (chirality g (overlap g e)) = minus e := by
  rw [overlap_chirality g e hg]
  simp [minus, plus, sub_eq_add_neg]

theorem complementary_intertwining (g e : Operator)
    (hg : g * g = 1) (he : e * e = 1) :
    overlap g e * plus (chirality g (overlap g e)) = minus g * overlap g e := by
  simp only [plus, minus, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
    Matrix.mul_one, chirality_intertwining g e hg he,
    Matrix.neg_mul, sub_eq_add_neg]
  congr 1
  noncomm_ring
end ChiralityDictionary

section SubtractedResponse
variable {R : Type*} [Ring R]

/-- Exact resolvent remainder after subtracting the first four response terms.
No commutativity assumption on the ambient ring is needed. -/
theorem fifth_resolvent_remainder (K Q : R) (hQ : Q * (1 + K) = 1) :
    Q * K - (K - K ^ 2 + K ^ 3 - K ^ 4) = Q * K ^ 5 := by
  calc
    _ = Q * K ^ 5 + (Q * (1 + K) - 1) * (K - K ^ 2 + K ^ 3 - K ^ 4) := by
      noncomm_ring
    _ = Q * K ^ 5 := by rw [hQ]; simp
end SubtractedResponse

section TraceResponse
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "Operator" => Matrix ι ι ℂ

theorem fifth_trace_remainder (K Q : Operator) (hQ : Q * (1 + K) = 1) :
    trace (Q * K) - (trace K - trace (K ^ 2) + trace (K ^ 3) - trace (K ^ 4)) =
      trace (Q * K ^ 5) := by
  simpa only [Matrix.trace_sub, Matrix.trace_add] using
    congrArg Matrix.trace (fifth_resolvent_remainder K Q hQ)
end TraceResponse

/-- A degree-four amplitude subtraction cannot alter the fifth coefficient. -/
theorem fifth_counterterm_coefficient_zero (p : Polynomial ℂ) (hp : p.natDegree ≤ 4) :
    p.coeff 5 = 0 := by
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp (by decide))

/-- Supplied integer hypercharges and multiplicities of one SM generation. -/
theorem supplied_generation_linear_cancellation :
    (6 : ℤ) * 1 + 3 * (-4) + 3 * 2 + 2 * (-3) + 6 = 0 := by norm_num

theorem supplied_generation_cubic_cancellation :
    (6 : ℤ) * 1 ^ 3 + 3 * (-4) ^ 3 + 3 * 2 ^ 3 + 2 * (-3) ^ 3 + 6 ^ 3 = 0 := by
  norm_num

/-- Anomaly cancellation does not force the fifth charge moment to vanish. -/
theorem supplied_generation_fifth_moment :
    (6 : ℤ) * 1 ^ 5 + 3 * (-4) ^ 5 + 3 * 2 ^ 5 + 2 * (-3) ^ 5 + 6 ^ 5 = 4320 := by
  norm_num

end
end UnifiedTheory.Audit.KFCausalChiralContinuumComparison
