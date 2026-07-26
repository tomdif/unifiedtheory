/-
  LayerA/AdjointUnificationObstruction.lean — WHY the adjoint content alone does
  NOT unify the couplings: it is hypercharge-neutral.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST CORRECTION.  Attempting to make UNIFICATION unconditional forces a direct
  computation, and it comes out NEGATIVE — sharpening (and partly refuting) the
  earlier "octet + triplet move the B-ratio onto the target" note.

  The one-loop B-test: three lines `1/α_i` unify iff `(b₂−b₃)/(b₁−b₂) = A₂₃/A₁₂`,
  with `A_ij = 1/α_i − 1/α_j` at `M_Z` (measured) giving the target `0.7177`.  The
  SM gives `0.5275`.  Adding the connection sector's adjoint content — octet
  `(8,1,0)`, triplet `(1,3,0)`, singlet `(1,1,0)` — moves it only to `0.5435`
  (Dirac), a `+0.016` shift against the `+0.19` needed (see
  `scripts/unification_btest.py`).

  THE STRUCTURAL REASON, proved here:  the adjoint content is HYPERCHARGE-NEUTRAL
  (adjoint representations are neutral under the abelian factor — every state has
  `Y = 0`).  So its contribution to the hypercharge β-coefficient `b₁ ∝ Σ Y²` is
  exactly ZERO.  The octet and triplet touch only `b₂, b₃`; the `U(1)` line is
  untouched.  But unification (with the measured couplings) requires moving the
  `U(1)` line — it needs HYPERCHARGED matter (vector-like leptons).  The
  connection/adjoint sector cannot supply it.

  WHAT IS PROVED (zero sorry, zero custom axioms):
   • `adjoint_b1_contribution_zero` — the adjoint content's hypercharge β-
     contribution `(2/5) Σ Y²` is `0`.

  CONSEQUENCE (honest verdict).  Unification is NOT made unconditional by the
  adjoint reps, and the obstruction is not merely the R3 continuum wall: even
  granting a literal continuum β-function, the adjoint content is the WRONG
  content for gauge unification, because it cannot move `b₁`.  The adjoint reps
  are real, massless, and run (the earlier files, unconditional) — but they do
  not unify the Standard Model couplings by themselves.  Unification needs
  hypercharged matter the connection sector does not produce.
-/
import UnifiedTheory.LayerA.ConnectionDefectAdjoint

namespace UnifiedTheory.LayerA.AdjointUnificationObstruction

open UnifiedTheory.LayerA.ConnectionDefectAdjoint
open UnifiedTheory.LayerA.AnomalyConstraints

/-- The hypercharge (`U(1)_Y`) one-loop β-contribution of a fermion spectrum,
`Δb₁ = (2/5) Σ Y²` (GUT-normalized: `(2/3)·(3/5)·Σ Y²`). -/
noncomputable def b1Contribution {N : ℕ} (S : ChargeSpectrum N) : ℝ :=
  (2 / 5) * ∑ i, (S.charge i) ^ 2

/-- **The adjoint content contributes ZERO to the hypercharge β-function.**  Adjoint
representations are neutral under the abelian factor: every state has `Y = 0`, so
`Σ Y² = 0`.  The octet + triplet cannot move the `U(1)` line, which is exactly what
gauge unification (with the measured couplings) requires — so the adjoint content
alone does not unify. -/
theorem adjoint_b1_contribution_zero : b1Contribution adjointSMspectrum = 0 := by
  simp [b1Contribution, adjointSMspectrum]

#print axioms adjoint_b1_contribution_zero

end UnifiedTheory.LayerA.AdjointUnificationObstruction
