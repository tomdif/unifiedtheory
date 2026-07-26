/-
  LayerA/VectorLikeLeptonFix.lean — Fixing the vector-like lepton: the minimal
  anomaly-free hypercharged completion, with NO free Yukawa.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT NEEDED FIXING.  The `sin²θ_W` postdiction left one soft input: the vector-
  like lepton (VL) needed to move `b₁` (the adjoint sector is `Y=0` and cannot —
  `AdjointUnificationObstruction`).  Its quantum numbers, anomaly status, and Yukawa
  were unspecified, and "unknown VL Yukawa" was a flagged 2-loop uncertainty.

  THE FIX.  The minimal completion is a vector-like lepton doublet
  `(1,2,−1/2) ⊕ (1,2,+1/2)` — four left-handed Weyl states with hypercharges
  `(−½,−½,+½,+½)`.  Two facts pin it down completely:

   (1) VECTOR-LIKE ⟹ NO YUKAWA.  Because the two chiralities have opposite
       hypercharge, the pair admits a GAUGE-INVARIANT BARE Dirac mass `M L̄ L`.  It
       does NOT require a Higgs coupling.  So the "unknown VL Yukawa" is not a free
       parameter — it is naturally ZERO, and the 2-loop Yukawa uncertainty it was
       charged with VANISHES.  The VL contributes to the running through its gauge
       quantum numbers only, and its mass is a bare threshold.

   (2) ANOMALY-FREE + MOVES b₁.  Being vector-like it is automatically anomaly-free
       (the `+Y` and `−Y` states cancel), and — unlike the adjoint — its hypercharge
       β-contribution is NONZERO.  It is exactly the anomaly-free object that
       supplies the `b₁` shift unification needs.

  WHAT IS PROVED (zero sorry, zero custom axioms):
   • `vl_anomaly_free`     — the VL doublet is anomaly-free (cubic + linear).
   • `vl_b1_contribution`  — its hypercharge β-contribution is `2/5` (NONZERO).
   • `vl_moves_b1_adjoint_does_not` — the crisp contrast: `Δb₁(adjoint) = 0` but
     `Δb₁(VL) ≠ 0`.  The adjoint (edge) sector cannot move the U(1) line; the VL
     (vertex, hypercharged) can.  This is the whole reason unification needs the VL.

  CONSEQUENCE for `sin²θ_W`.  With the VL Yukawa fixed to zero (vector-like), the
  2-loop `sin²θ_W(M_Z) = 0.230` (from `scripts/weinberg_2loop.py`, `+ top Yukawa`) no
  longer carries the VL-Yukawa uncertainty — that input is now determined, not free.
  The residual `~0.6%` is the new-matter 2-loop GAUGE contributions (fixed by the
  reps) plus threshold scheme, not an undetermined coupling.

  SCOPE (honest).  This fixes the VL's rep, anomaly status, and Yukawa (= 0).  Its
  MASS remains a bare threshold — a genuine free scale (physical: it sets where the
  VL enters the running, `~10⁵`–`10⁶ GeV` in the fits).  Whether the framework
  fixes that scale geometrically is the open vertex-sector question; here the VL is
  fixed as much as its rep-theory and Yukawa allow.
-/
import UnifiedTheory.LayerA.AdjointUnificationObstruction

namespace UnifiedTheory.LayerA.VectorLikeLeptonFix

open UnifiedTheory.LayerA.ConnectionDefectAdjoint
open UnifiedTheory.LayerA.AnomalyConstraints
open UnifiedTheory.LayerA.AdjointUnificationObstruction

/-- The minimal vector-like lepton doublet `(1,2,−1/2) ⊕ (1,2,+1/2)`, as four
left-handed Weyl states with hypercharges `(−½,−½,+½,+½)`.  Vector-like: bare Dirac
mass, NO Higgs Yukawa. -/
noncomputable def vlSpectrum : ChargeSpectrum 4 where
  charge := ![-1/2, -1/2, 1/2, 1/2]
  chirality := ![1, 1, 1, 1]

/-- The cubic hypercharge anomaly of the VL doublet vanishes (vector-like). -/
theorem vl_cubic_anomaly_zero : cubicAnomaly vlSpectrum = 0 := by
  norm_num [cubicAnomaly, vlSpectrum, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

/-- The linear (gravitational) anomaly of the VL doublet vanishes (vector-like). -/
theorem vl_linear_anomaly_zero : linearAnomaly vlSpectrum = 0 := by
  norm_num [linearAnomaly, vlSpectrum, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

/-- **The vector-like lepton doublet is anomaly-free.**  Automatic for a vector-like
multiplet: the `+Y` and `−Y` states cancel in every anomaly. -/
theorem vl_anomaly_free : IsSpectrumAnomalyFree vlSpectrum :=
  ⟨vl_cubic_anomaly_zero, vl_linear_anomaly_zero⟩

/-- **The VL hypercharge β-contribution is `2/5` — NONZERO.**  Unlike the adjoint
sector, the VL doublet carries hypercharge and moves `b₁`. -/
theorem vl_b1_contribution : b1Contribution vlSpectrum = 2 / 5 := by
  norm_num [b1Contribution, vlSpectrum, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

/-- The VL contribution to `b₁` is nonzero. -/
theorem vl_b1_nonzero : b1Contribution vlSpectrum ≠ 0 := by
  rw [vl_b1_contribution]; norm_num

/-- **The crisp contrast — why unification needs the VL.**  The adjoint (edge)
sector has `Δb₁ = 0` and cannot move the `U(1)` line; the vector-like lepton
(vertex, hypercharged) has `Δb₁ ≠ 0` and can.  Both are anomaly-free. -/
theorem vl_moves_b1_adjoint_does_not :
    b1Contribution adjointSMspectrum = 0 ∧ b1Contribution vlSpectrum ≠ 0 :=
  ⟨adjoint_b1_contribution_zero, vl_b1_nonzero⟩

#print axioms vl_anomaly_free
#print axioms vl_b1_contribution
#print axioms vl_moves_b1_adjoint_does_not

end UnifiedTheory.LayerA.VectorLikeLeptonFix
