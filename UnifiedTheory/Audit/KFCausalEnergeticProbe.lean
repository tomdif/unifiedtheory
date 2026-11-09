/-
  Algebraic and scalar support for energetic neutral-probe constraints.
  The Duhamel integration, operator-norm estimates, and graph support
  theorem are analytic suppliers in ENERGETIC_PROBE_SECTOR.md.
-/
import UnifiedTheory.Audit.KFCausalPatchGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalEnergeticProbe
noncomputable section

def comm {A : Type*} [Ring A] (x y : A) : A := x * y - y * x

/-- The complementary blocks add back to the original operator. -/
theorem block_decomposition {A : Type*} [Ring A] (P K : A) :
    P * K * P + (1 - P) * K * (1 - P) +
      (P * K * (1 - P) + (1 - P) * K * P) = K := by
  noncomm_ring

/-- Idempotence makes the double commutator the off-diagonal part. -/
theorem off_diagonal_double_comm {A : Type*} [Ring A]
    (P K : A) (hP : P * P = P) :
    comm P (comm P K) = P * K * (1 - P) + (1 - P) * K * P := by
  have hleft : P * (P * K) = P * K := by rw [← mul_assoc, hP]
  have hright : K * P * P = K * P := by rw [mul_assoc, hP]
  simp only [comm, mul_sub, sub_mul, mul_one, one_mul, hleft, hright]
  noncomm_ring

/-- This identity avoids a bound proportional to the extensive norm of K. -/
theorem second_commutator_identity {A : Type*} [Ring A] (P K : A) :
    comm K (comm P (comm P K)) = -comm P (comm K (comm K P)) := by
  simp only [comm]
  noncomm_ring

/-- The penalty commutator inverts the off-diagonal part. -/
theorem penalty_commutator_inverse {A : Type*} [Ring A]
    (R V : A) (hR : R * R = R) (hzero : R * V * R = 0)
    (hoff : R * V + V * R = V) : comm R (comm R V) = V := by
  have hleft : R * (R * V) = R * V := by rw [← mul_assoc, hR]
  have hright : V * R * R = V * R := by rw [mul_assoc, hR]
  simp only [comm, mul_sub, sub_mul, hleft, hright]
  rw [← mul_assoc R V R, hzero]
  simpa using hoff

/-- Algebra used when differentiating the comparison intertwiner. -/
theorem perturbed_intertwiner {A : Type*} [Ring A] (H V S : A) :
    (H + V) * S - S * H = comm H S + V * S := by
  simp only [comm]
  noncomm_ring

/-- Jacobi combines the two mixed geometry/probe commutators. -/
theorem mixed_commutator_identity {A : Type*} [Ring A] (G T P : A) :
    comm G (comm T P) + comm T (comm G P) =
      comm (comm G T) P + (comm T (comm G P) + comm T (comm G P)) := by
  simp only [comm]
  noncomm_ring

/-- The static degree-six constants in the analytic estimate. -/
theorem static_error_numerator (k t : ℝ) :
    2 * (6 * k) + t * (72 * k ^ 2 + (6 * k) ^ 2) =
      12 * k + 108 * k ^ 2 * t := by ring

/-- A supplied uniform numerator controls every size and allowed time. -/
theorem uniform_penalty_accuracy (error numerator gap tolerance : ℝ)
    (hg : 0 < gap) (he : error ≤ numerator / gap)
    (hscale : numerator ≤ tolerance * gap) : error ≤ tolerance := by
  exact he.trans ((div_le_iff₀ hg).mpr hscale)

/-- Leakage probability is bounded by the square of the amplitude error. -/
theorem leakage_probability_bound (leakage error : ℝ)
    (hl : 0 ≤ leakage) (he : leakage ≤ error) : leakage ^ 2 ≤ error ^ 2 := by
  nlinarith

/-- The finite-penalty ninth-order path survives the supplied tail bound. -/
theorem finite_penalty_shortcut (amplitude leading remainder : ℝ)
    (hl : 0 < leading) (hr : remainder ≤ leading / 5)
    (ha : leading - remainder ≤ amplitude) :
    0 < leading / 2 ∧ leading / 2 ≤ amplitude := by
  constructor <;> linarith

#print axioms block_decomposition
#print axioms off_diagonal_double_comm
#print axioms second_commutator_identity
#print axioms penalty_commutator_inverse
#print axioms perturbed_intertwiner
#print axioms mixed_commutator_identity
#print axioms static_error_numerator
#print axioms uniform_penalty_accuracy
#print axioms leakage_probability_bound
#print axioms finite_penalty_shortcut

end
end UnifiedTheory.Audit.KFCausalEnergeticProbe
