/-
  LayerA/TraceHyperchargeExile.lean — WHY hypercharge cannot come from the
  connection: it is the trace direction, and the edge/adjoint sector is traceless.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  THE STRUCTURAL IDEA (what the unification computation informs).

  `AdjointUnificationObstruction` showed the adjoint (edge) content cannot unify
  because it is hypercharge-neutral (`Δb₁ = 0`), and the explicit running
  (`scripts/unification_vl.py`) shows the minimal fix is exactly ONE vector-like
  lepton doublet (hypercharged, FUNDAMENTAL) added to the octet + triplet, giving
  `M_GUT ≈ 10¹⁷ GeV`, `1/α_GUT ≈ 34`.

  The reason is the trace decomposition of the matrix algebra:

        gl(n) = sl(n) ⊕ ℝ·I           (adjoint / traceless)  ⊕  (trace / abelian).

  The connection/edge matter is `sl(n)`-valued (traceless — the adjoint, `dim n²−1`).
  The ONE remaining direction, the trace `ℝ·I`, is the abelian factor — and the
  adjoint action is TRIVIAL on it (`W (c·I) W⁻¹ = c·I`), so as edge matter it is a
  chargeless SINGLET.  The edge sector therefore realizes the abelian direction
  only as `Y = 0`; it cannot carry hypercharge.  Hypercharge-carrying matter must
  be VERTEX/fundamental.  Hypercharge is "geometrically exiled" from the
  connection.

  This is the root of both facts: the two-sector matter dichotomy (edge = adjoint,
  `Y=0`, the gaugino-like dark content; vertex = fundamental, hypercharged), and
  the failure of adjoint-only unification.

  WHAT IS PROVED (zero sorry, zero custom axioms):
   • `abelian_direction_dim_one` — the trace complement of `sl(n)` in `gl(n)` is
     exactly 1-dimensional: a single abelian factor.
   • `adjoint_fixes_scalar` — the adjoint action fixes the trace direction:
     `W (c·I) W⁻¹ = c·I`.  As edge matter the abelian direction is a neutral
     singlet, so the connection sector cannot source hypercharge.
-/
import UnifiedTheory.LayerA.AdjointDimension

namespace UnifiedTheory.LayerA.TraceHyperchargeExile

open Matrix Module UnifiedTheory.LayerA.AdjointDimension

/-- **The abelian direction is one-dimensional.**  `dim gl(n) − dim sl(n) = 1`:
the trace complement of the traceless (adjoint) matrices is a single direction —
the one abelian factor `U(1)`. -/
theorem abelian_direction_dim_one (n : ℕ) (hn : 0 < n) :
    finrank ℝ (Matrix (Fin n) (Fin n) ℝ) - finrank ℝ (slMatrix n) = 1 := by
  have hV : finrank ℝ (Matrix (Fin n) (Fin n) ℝ) = n ^ 2 := by
    rw [finrank_matrix]; simp [sq]
  rw [hV, finrank_slMatrix n hn]
  have : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
  omega

/-- **The adjoint action fixes the trace direction.**  `W (c·I) W⁻¹ = c·I` for every
holonomy `W`.  The abelian (trace) direction is adjoint-trivial, so realized as
edge/connection matter it is a chargeless singlet — the connection sector cannot
carry hypercharge. -/
theorem adjoint_fixes_scalar {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (hW : IsUnit W.det)
    (c : ℝ) :
    W * (c • (1 : Matrix (Fin n) (Fin n) ℝ)) * W⁻¹ = c • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  rw [mul_smul_comm, mul_one, smul_mul_assoc, mul_nonsing_inv W hW]

#print axioms abelian_direction_dim_one
#print axioms adjoint_fixes_scalar

end UnifiedTheory.LayerA.TraceHyperchargeExile
