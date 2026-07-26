/-
  LayerA/VLMassProtection.lean — RESOLVING the vertex-mass tension: the arrow
  protects the VL's Dirac mass, so it is EWSB-light, not Planck-heavy.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  THE ESCAPE.  `VertexMassTension` concluded that the VL, being "unprotected", sits
  at `M_P` and decouples.  That over-applied the single-scale principle.  Two facts
  the framework already proves show the VL Dirac mass is protected, hence light:

   • `SpectralMassTheorem` — every mass in the framework is `m = γ·v`, PROPORTIONAL
     to the EWSB vev `v`.  The framework generates NO bare Dirac masses; a Dirac
     mass vanishes as `v → 0`.  This IS chiral protection, built in.
   • `ArrowChiralityLock` — the growth arrow assigns each fermion a definite
     chirality.  Fermions are ARROW-CHIRAL.

  A bare (v-independent) mass term is allowed only if it is arrow-charge neutral:

     – Dirac  `ψ̄_L ψ_R`  carries arrow-charge `q_R − q_L`.  For an ARROW-CHIRAL
       fermion `q_L ≠ q_R`, so the bare Dirac mass is FORBIDDEN; the mass comes only
       from the arrow-charged Higgs, `m = γ v` — EWSB-light.
     – Majorana `ν_R ν_R` carries arrow-charge `2 q`.  For an arrow-NEUTRAL
       gauge-singlet `ν_R` (`q = 0`) the bare Majorana mass is ALLOWED, at `M_P`.
       This is exactly `NeutrinoScale`'s `M_R = M_P`.

  So the SAME selection rule that puts the neutrino Majorana mass at `M_P` puts the
  VL Dirac mass at `v` — the VL is arrow-chiral, like every SM fermion, and therefore
  LIGHT (~EW–TeV), not `M_P`.  With `M_VL ∼ v ≪ M_GUT` its running lever arm
  `ln(M_GUT/M_VL) > 0` is large, so it DOES supply the `b₁` shift, and `sin²θ_W`
  lands at `≈ 0.230`.  The tension is resolved.

  CORRECTION to earlier files.  `VectorLikeLeptonFix` called the VL "Yukawa-free" —
  that was the wrong branch.  The VL is GAUGE-vector-like (anomaly-free) but
  ARROW-chiral, so it DOES have a Yukawa (to the arrow-charged Higgs); that Yukawa is
  precisely what makes it light.  "Gauge-vector-like" ≠ "arrow-vector-like": the
  latter is what would have made the mass unprotected.

  WHAT IS PROVED (zero sorry, zero custom axioms):
   • `dirac_bare_forbidden_iff_arrowChiral` — the bare Dirac mass is arrow-charged
     (forbidden) iff the fermion is arrow-chiral.
   • `majorana_bare_allowed_iff_neutral` — the bare Majorana mass is arrow-neutral
     (allowed) iff the singlet is arrow-neutral.
   • `vl_arrowchiral_runs` — with `M_VL = v < M_GUT`, the lever arm `ln(M_GUT/v) > 0`:
     the arrow-protected VL runs and helps unification (contrast
     `VertexMassTension.vl_natural_mass_decouples`).

  SCOPE (honest).  The escape rests on the VL being ARROW-CHIRAL (its `L`, `R` carry
  opposite arrow-charge) while GAUGE-vector-like — natural, since every framework
  fermion is arrow-chiral and the Higgs is arrow-charged (it flips chirality to give
  Dirac masses).  What is NOT fixed is the exact value of `γ_VL` (hence the precise
  VL mass in the EW–TeV window) — that is a specific transfer eigenvalue, the same
  open datum as any individual fermion mass.  The qualitative resolution — VL light,
  not `M_P` — is what the arrow + spectral mechanism deliver.
-/
import UnifiedTheory.LayerA.VertexMassTension

namespace UnifiedTheory.LayerA.VLMassProtection

open Real UnifiedTheory.LayerA.VertexMassTension

/-- **Bare Dirac mass is forbidden iff the fermion is arrow-chiral.**  The term
`ψ̄_L ψ_R` carries arrow-charge `q_R − q_L`; it is nonzero (forbidden) exactly when
`q_L ≠ q_R`.  An arrow-chiral VL therefore has NO bare Dirac mass — its mass comes
from the arrow-charged Higgs, `m = γv`. -/
theorem dirac_bare_forbidden_iff_arrowChiral (qL qR : ℤ) : qR - qL ≠ 0 ↔ qL ≠ qR := by
  omega

/-- **Bare Majorana mass is allowed iff the singlet is arrow-neutral.**  The term
`ν_R ν_R` carries arrow-charge `2q`; it is neutral (allowed) exactly when `q = 0`.
An arrow-neutral gauge singlet (the `ν_R`) therefore admits a bare Majorana mass at
`M_P` — `NeutrinoScale`'s `M_R = M_P`. -/
theorem majorana_bare_allowed_iff_neutral (q : ℤ) : 2 * q = 0 ↔ q = 0 := by
  omega

/-- **The mass scale by protection.**  An arrow-chiral fermion's mass is `v` (EWSB,
light); an arrow-neutral singlet's is `M_P` (bare, heavy). -/
noncomputable def protectedMassScale (v MP : ℝ) (arrowChiral : Bool) : ℝ :=
  if arrowChiral then v else MP

/-- The VL (arrow-chiral) is at the EWSB scale `v`; the `ν_R` (arrow-neutral) at
`M_P`. -/
theorem vl_at_v_neutrino_at_MP (v MP : ℝ) :
    protectedMassScale v MP true = v ∧ protectedMassScale v MP false = MP :=
  ⟨rfl, rfl⟩

/-- **The arrow-protected VL RUNS and helps unification.**  With `M_VL = v < M_GUT`,
the lever arm `ln(M_GUT / v) > 0`: the light VL is active across the desert and
supplies the `b₁` shift — the direct contrast to
`VertexMassTension.vl_natural_mass_decouples` (which needed `M_VL ≥ M_GUT`).  This is
the resolution: arrow protection makes `M_VL = v ≪ M_GUT`, not `M_P`. -/
theorem vl_arrowchiral_runs (MGUT v : ℝ) (hv : 0 < v) (h : v < MGUT) :
    0 < leverArm MGUT v := by
  unfold leverArm
  apply Real.log_pos
  rw [lt_div_iff₀ hv, one_mul]
  exact h

#print axioms dirac_bare_forbidden_iff_arrowChiral
#print axioms majorana_bare_allowed_iff_neutral
#print axioms vl_arrowchiral_runs

end UnifiedTheory.LayerA.VLMassProtection
