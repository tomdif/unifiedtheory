/-
  Audit/KFCausalCSpecTwistedGap.lean   (arc file 6/6)

  THE TWISTED SPECTRAL MODE DROPS OUT:  V^{S3} = 0

  The direction fields live in the zero-sum space `V = {x : Σ x = 0}`, the
  standard (irreducible, 2-dimensional) representation of S3.  Because the
  holonomy image is all of S3 (file 5), a flat global section is an S3-invariant
  vector of `V`, i.e. an element of `V^{S3}`.  We prove `V^{S3} = 0`.

  Consequently the twisted sheet Laplacian `L_ρ`, whose kernel is exactly the
  invariants, has TRIVIAL kernel: it is positive definite, so it has a nonzero
  lowest eigenmode.  Since `V` itself is nontrivial (`zerosum_nontrivial`), this
  lowest mode is a genuine nonzero twisted section — canonical up to its lowest
  eigenspace, exactly as claimed (simplicity would need a separate gap theorem).

  This is the cleanest brick of the arc: pure representation theory, no empirical
  margin, no restriction-stability.

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalCSpecMonodromy

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecTwistedGap

open scoped BigOperators
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecMonodromy

/-- **V^{S3} = 0.**  A zero-sum direction field invariant under every permutation
of the three directions is zero.  (Follows from the two-transposition obstruction
of file 5, since all of S3 in particular contains `(0 1)` and `(1 2)`.) -/
theorem invariant_zerosum_eq_zero (x : Direction → ℝ)
    (hinv : ∀ σ : Equiv.Perm Direction, x ∘ σ = x)
    (hsum : IsZeroSum x) : x = 0 :=
  no_global_section x (hinv (Equiv.swap 0 1)) (hinv (Equiv.swap 1 2)) hsum

/-- The zero-sum space is nontrivial: `(1, -1, 0)` is a nonzero flat direction
field, so the twisted mode the Laplacian selects is a genuine nonzero section. -/
theorem zerosum_nontrivial :
    ∃ x : Direction → ℝ, IsZeroSum x ∧ x ≠ 0 := by
  refine ⟨![1, -1, 0], ?_, ?_⟩
  · simp [IsZeroSum, Fin.sum_univ_three]
  · intro h
    have := congrFun h 0
    simp at this

/-- **Twisted-kernel triviality (abstract spectral corollary).**  Model the
twisted Laplacian by a quadratic energy `E ≥ 0` whose zero set is exactly the
invariant zero-sum fields.  Then the only zero-energy field is `0`: `L_ρ` is
positive definite on the zero-sum space.  Any nonzero field has strictly positive
energy — the twisted gap. -/
theorem twisted_energy_pos
    (E : (Direction → ℝ) → ℝ)
    (hE_kernel : ∀ x, E x = 0 ↔ (∀ σ : Equiv.Perm Direction, x ∘ σ = x) ∧ IsZeroSum x)
    (hE_nonneg : ∀ x, 0 ≤ E x)
    (x : Direction → ℝ) (hx_zs : IsZeroSum x) (hx_ne : x ≠ 0) :
    0 < E x := by
  rcases lt_or_eq_of_le (hE_nonneg x) with h | h
  · exact h
  · exfalso
    have hk := (hE_kernel x).mp h.symm
    exact hx_ne (invariant_zerosum_eq_zero x hk.1 hx_zs)

#print axioms invariant_zerosum_eq_zero
#print axioms zerosum_nontrivial
#print axioms twisted_energy_pos

end UnifiedTheory.Audit.KFCausalCSpecTwistedGap
