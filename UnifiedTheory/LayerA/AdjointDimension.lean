/-
  LayerA/AdjointDimension.lean — The adjoint multiplet dimensions are FORCED.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT.  `ConnectionDefectAdjoint.lean` proves the connection-sector fermion
  transforms in the ADJOINT (its charge = a loop holonomy conjugated by the gauge
  parameter).  But its `adjointSMspectrum` *posits* the count `8 + 3 + 1 = 12`.
  This file DERIVES that count: the adjoint representation space is `sl(n)` (the
  traceless matrices — the exact space `GaugeFromTraceless` shows carries the
  gauge bosons), and

        dim sl(n) = n² − 1.

  So the color adjoint is `dim sl(3) = 8` (the octet), the weak adjoint is
  `dim sl(2) = 3` (the triplet), and the abelian factor contributes `1`.  The
  multiplet dimensions `8, 3, 1` are not chosen — they are rank–nullity applied
  to the surjective trace, the same structural fact that makes the bosons live in
  `sl(n)`.  A fermion sharing the connection's adjoint transformation shares its
  dimension.

  WHAT IS PROVED (zero sorry, zero custom axioms):
   • `finrank_slMatrix` :  `dim ℝ sl(n) = n² − 1`  (rank–nullity on `trace`).
   • `finrank_octet` / `finrank_triplet` :  `dim sl(3) = 8`, `dim sl(2) = 3`.
   • `adjoint_fermion_count` :  `dim sl(3) + dim sl(2) + 1 = 12` — one adjoint
     fermion per gauge generator, the octet + triplet + singlet, derived.

  SCOPE (honest).  This forces the *dimensions* of the adjoint content from the
  group theory of the connection sector.  It does NOT, on its own, force the
  connection-sector fermions to exist (the framework's minimality still selects
  vertex/fundamental matter — the fork documented in `ConnectionDefectAdjoint`),
  nor does it run the couplings (the unification consequence is numerical and
  conditional).  It closes the group-theory half of the multiplet count: IF the
  connection sector carries fermionic matter, its multiplicities are exactly the
  octet + triplet + singlet.
-/
import Mathlib

set_option autoImplicit false

namespace UnifiedTheory.LayerA.AdjointDimension

open Matrix Module

/-- `sl(n)` = the traceless real `n×n` matrices = kernel of the trace linear map.
This is the adjoint representation space: the gauge bosons live here
(`GaugeFromTraceless`), and so does a connection-sector fermion. -/
noncomputable def slMatrix (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  LinearMap.ker (traceLinearMap (Fin n) ℝ ℝ)

/-- **The adjoint dimension: `dim sl(n) = n² − 1`.**  Rank–nullity for the trace
linear map, which is surjective onto `ℝ` (`trace_surjective`), on the `n²`-
dimensional matrix space (`finrank_matrix`). -/
theorem finrank_slMatrix (n : ℕ) (hn : 0 < n) :
    finrank ℝ (slMatrix n) = n ^ 2 - 1 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hsurj : Function.Surjective (traceLinearMap (Fin n) ℝ ℝ) :=
    trace_surjective
  have hrange : finrank ℝ
      (LinearMap.range (traceLinearMap (Fin n) ℝ ℝ)) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, finrank_self]
  have hV : finrank ℝ (Matrix (Fin n) (Fin n) ℝ) = n ^ 2 := by
    rw [finrank_matrix]; simp [sq]
  have hrn := (traceLinearMap (Fin n) ℝ ℝ).finrank_range_add_finrank_ker
  rw [hrange, hV] at hrn
  simp only [slMatrix]
  omega

/-- **The color octet: `dim sl(3) = 8`.**  The adjoint of `SU(3)`. -/
theorem finrank_octet : finrank ℝ (slMatrix 3) = 8 := by
  rw [finrank_slMatrix 3 (by norm_num)]
  norm_num

/-- **The weak triplet: `dim sl(2) = 3`.**  The adjoint of `SU(2)`. -/
theorem finrank_triplet : finrank ℝ (slMatrix 2) = 3 := by
  rw [finrank_slMatrix 2 (by norm_num)]
  norm_num

/-- **The adjoint fermion count is derived: `8 + 3 + 1 = 12`.**  Octet + triplet +
abelian singlet = one adjoint fermion per gauge generator, with the octet and
triplet dimensions forced by `dim sl(n) = n² − 1`, not posited. -/
theorem adjoint_fermion_count :
    finrank ℝ (slMatrix 3) + finrank ℝ (slMatrix 2) + 1 = 12 := by
  rw [finrank_octet, finrank_triplet]


#print axioms finrank_slMatrix
#print axioms finrank_octet
#print axioms finrank_triplet
#print axioms adjoint_fermion_count

end UnifiedTheory.LayerA.AdjointDimension
