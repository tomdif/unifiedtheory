/-
Concrete, unconditional q-series input for UnifiedTheory.

The functions here are the actual infinite integer power series defined by
Watson's sums. R1 and its companion relations are proved by the imported
RamanujanLean port, rather than supplied as hypotheses on arbitrary ring elements.

No identification with causal histories, Hamiltonian degeneracies, black-hole
microstates, or the Standard Model is asserted. The existing MTC0/MTC1 consumers
retain their own hypotheses; those distinct theorems are not consequences of R1.
-/
import UnifiedTheory.QSeries.Watson.F0Rel

set_option autoImplicit false

namespace UnifiedTheory.LayerA.WatsonSeriesBridge

open PowerSeries UnifiedTheory.QSeries.Watson

/-- The full R1 identity, with all three series concretely defined. -/
theorem chi0_R1 : chiA = 2 * F0w - P0w := chi0_R1_watson

/-- Exact equality at every coefficient, not just a checked finite prefix. -/
theorem chi0_R1_coeff (n : ℕ) :
    coeff n chiA = 2 * coeff n F0w - coeff n P0w := by
  have h := congrArg (coeff n) chi0_R1
  simpa [two_mul, map_add] using h

/-- R1 and Watson's two companion identities eliminate `F₀` and `φ₀` at `q²`.
The factor two keeps the identity over the integers without division. -/
theorem chi0_even_argument_elimination :
    2 * expand 2 two_ne_zero chiA =
      4 + 4 * X * psi2w * expand 4 (by norm_num) Hw - 3 * f0w + th4w * Gw := by
  have hR := congrArg (expand 2 two_ne_zero) chi0_R1
  simp only [map_sub, map_mul, map_ofNat] at hR
  linear_combination 2 * hR + watson_2_0 + 2 * watson_3_0

/-- Infinite distinct-parts/unrestricted-parts product identity. -/
theorem distinct_times_unrestricted_denominator :
    IP (-1) 1 1 * IP 1 1 1 = IP 1 2 2 := by
  have h := IP_sq 1 (a := 1) (b := 1) le_rfl le_rfl
  norm_num at h
  simpa [mul_comm] using h

/-- Euler's equality of distinct-parts and odd-parts generating products. -/
theorem distinct_eq_odd_partition_product :
    IP (-1) 1 1 = Ring.inverse (IP 1 1 2) := by
  symm
  apply inv_eq_of_mul_eq_one
  simpa [mul_comm] using euler_E4

end UnifiedTheory.LayerA.WatsonSeriesBridge
