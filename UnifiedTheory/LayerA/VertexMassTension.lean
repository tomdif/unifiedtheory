/-
  LayerA/VertexMassTension.lean — Fixing the VL mass from the vertex sector
  DEMOTES the unification: the framework's own single-scale principle sends the
  vector-like lepton to M_P, where it decouples and cannot help.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  THE HONEST OUTCOME (negative — a self-consistent tension).

  `NeutrinoScale.lean` states the framework's principle for UNPROTECTED masses
  explicitly: with a single fundamental scale `M_P`, "any heavy mass `M` must
  satisfy `M ≤ M_P`", and an unprotected mass is driven to the maximum — the
  right-handed neutrino sits at `M_R = M_P`.

  A vector-like lepton mass is exactly such an unprotected mass.  Indeed the fix
  that made the VL clean — VECTOR-LIKE ⟹ anomaly-free and NO Yukawa
  (`VectorLikeLeptonFix`) — is precisely what removes any chiral symmetry
  protecting its mass.  So the SAME principle the framework uses for `M_R` gives

        M_VL = M_P  ( ≈ the reduced-Planck unification scale, and above it ).

  But the vector-like lepton only helps unification by RUNNING between `M_Z` and
  `M_GUT`: its contribution to a coupling is proportional to the lever arm
  `ln(M_GUT / M_VL)`.  With `M_VL ≥ M_GUT` (as the single-scale principle forces)
  that lever arm is `≤ 0` — the VL is never active below `M_GUT` and contributes
  NOTHING to the low-energy running.  Then `sin²θ_W(M_Z)` reverts to its
  no-VL value `≈ 0.210` (the SM-like 9% miss), and unification fails.

  THE TRILEMMA (why this is structural, not a detail).  The VL cannot be
  simultaneously (a) anomaly-free, (b) Yukawa-free, and (c) light:
   • (a)+(b) — a vector-like multiplet — makes its mass unprotected ⟹ `M_P` (heavy,
     useless), by the framework's own naturalness.
   • (c) light needs chiral protection ⟹ a Yukawa (not (b)) AND anomaly partners
     (not the minimal (a)).
  The clean VL of `VectorLikeLeptonFix` is the (a)+(b) branch — hence heavy.

  CONSEQUENCE.  Fixing the VL mass from the vertex sector does NOT land it at the
  `~10⁶ GeV` the unification fit wanted; it lands it at `M_P`, where it decouples.
  So the `sin²θ_W ≈ 0.230` success is CONDITIONAL on a VL mass tuned ~13 orders of
  magnitude below the single scale — an assumption the framework does not justify
  and that contradicts its own treatment of the neutrino seesaw (`M_R = M_P`).  This
  demotes the weak-angle result: it is not naturally realized.

  WHAT IS PROVED (zero sorry, zero custom axioms):
   • `vl_at_gut_no_running`      — at `M_VL = M_GUT` the lever arm `ln(M_GUT/M_VL)` is 0.
   • `vl_natural_mass_decouples` — for `M_VL ≥ M_GUT` (the single-scale value) the
     lever arm is `≤ 0`: the VL contributes no positive sub-GUT running.

  SCOPE (honest).  The negative conclusion rests on the framework's OWN single-scale
  naturalness (the `NeutrinoScale` principle) applied consistently.  The only escape
  is a mechanism that protects the VL mass far below `M_P` — a chiral symmetry or a
  suppressed vertex eigenvalue — which the framework does not currently supply.  So
  the VL mass is the one input in the arc that the vertex sector does NOT fix
  favorably; it fixes it UNfavorably (at `M_P`).
-/
import Mathlib

set_option autoImplicit false

namespace UnifiedTheory.LayerA.VertexMassTension

open Real

/-- The one-loop running lever arm of a threshold at `M_VL` below `M_GUT`:
`ln(M_GUT / M_VL)`.  A particle's contribution to the sub-`M_GUT` running is
proportional to this. -/
noncomputable def leverArm (MGUT MVL : ℝ) : ℝ := Real.log (MGUT / MVL)

/-- **A VL exactly at the GUT scale has zero lever arm** — it does not run below
`M_GUT` and contributes nothing to the low-energy couplings. -/
theorem vl_at_gut_no_running (M : ℝ) (hM : 0 < M) : leverArm M M = 0 := by
  unfold leverArm
  rw [div_self hM.ne', Real.log_one]

/-- **The single-scale principle decouples the VL.**  If the vector-like mass sits at
or above the GUT scale — as `M_VL = M_P ≥ M_GUT` forces (`NeutrinoScale` naturalness
applied to an unprotected mass) — its lever arm `ln(M_GUT/M_VL) ≤ 0`: the VL is never
active below `M_GUT` and supplies no positive `b₁` running.  Unification loses the VL,
and `sin²θ_W` reverts to its no-VL value. -/
theorem vl_natural_mass_decouples (MGUT MVL : ℝ) (hMGUT : 0 < MGUT) (hMVL : 0 < MVL)
    (h : MGUT ≤ MVL) :
    leverArm MGUT MVL ≤ 0 := by
  unfold leverArm
  apply Real.log_nonpos
  · positivity
  · rw [div_le_one hMVL]; exact h

#print axioms vl_at_gut_no_running
#print axioms vl_natural_mass_decouples

end UnifiedTheory.LayerA.VertexMassTension
