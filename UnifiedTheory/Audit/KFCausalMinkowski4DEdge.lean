/-
  Audit/KFCausalMinkowski4DEdge.lean   (Volume sector → 4D edge structure)

  Rung 3a of the 4D ladder: the exact-derivative form of `K4` and the two
  EDGE-MASS ZEROS that make the 4D light-cone edges finite.

  After the double IBP with the 4D kernel (`kernel4_mixed`), the mean operator's
  edge behavior along the null axes is controlled by two Mellin masses:

   • the `K4` edge mass `∫₀^∞ K4(a u²v²) dv ∝ M[K4](½)` — VANISHES (`K4_moment_half`):
     `M[K4](s) = ⅓[Γ(s) + 4Γ(s+1) − 4Γ(s+2)] = (−4/3)Γ(s)(s−½)(s+½)`, root at `s = ½`.
   • the `(u/v)·J4` leading edge term `∝ M[J4](0) = ∫ z⁻¹J4 dz` — VANISHES
     (`J4_moment_neg_one`): `⅓∫e^{−z}(1−z) = ⅓(Γ(1) − Γ(2)) = 0`.

  Both zeros are again the RESONANCE at work: `M[K4](s) ∝ (s−½)(s+½)` — the same
  `s = ±½` structure that solved the kernel ODEs.

  THE EXACT-DERIVATIVE FORM OF `K4` (`L4_ode` / `K4_exact_deriv`): with

      L4(z) = ⅓e^{−z}(1 + 2z),        2z·L4' + L4 = K4,

  one has `∂_v[v·L4(a u²v²)] = K4(a u²v²)` — `K4` is an exact `v`-derivative with a
  REGULAR (nonsingular) primitive, the 4D analogue of the 2D
  `f2D = −½∂_W(We^{−aUW})'`-structure, enabling the second-stage IBP of the
  edge/corner analysis.

  ASSEMBLY STATUS (documented, not yet formalized): with the kernel identity and
  these edge facts, the 4D mean operator obeys
     ⟨Bφ⟩ = (4/√6)√ρ [ −φ(0) + (3/2π)∬ ∂_u∂_v𝒦4·φ̄ ],
  the double IBP's corner/edge terms give `+φ(0)` (the `−1/6` axis constant times
  `(3/2π)·4π = 6` — counterterm cancels EXACTLY), leaving `(4/√6)√ρ·(3/2π)∬𝒦4·∂_u∂_vφ̄`;
  the remaining limit concentrates on the axes via the vanishing edge masses and
  boundary-FTC, exactly the corner-gate mechanism.  Formalizing that two-scale
  concentration is the remaining rung (plus the S²/profile reduction).

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowski4DKernel

set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Real Set
open UnifiedTheory.Audit.KFCausalMinkowski4DMoments
open UnifiedTheory.Audit.KFCausalMinkowski4DKernel

namespace UnifiedTheory.Audit.KFCausalMinkowski4DEdge

/-! ## The regular primitive `L4` -/

/-- The regular primitive `L4(z) = ⅓e^{−z}(1 + 2z)`. -/
noncomputable def L4 (z : ℝ) : ℝ := (1/3) * Real.exp (-z) * (1 + 2*z)

/-- `L4' = ⅓e^{−z}(1 − 2z)`. -/
noncomputable def L4d (z : ℝ) : ℝ := (1/3) * Real.exp (-z) * (1 - 2*z)

private lemma exp_neg_hasDerivAt (z : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-z)) z := by
  simpa using (Real.hasDerivAt_exp (-z)).comp z (hasDerivAt_neg z)

theorem L4_hasDerivAt (z : ℝ) : HasDerivAt L4 (L4d z) z := by
  show HasDerivAt (fun x => (1/3) * Real.exp (-x) * (1 + 2*x)) (L4d z) z
  have h2x : HasDerivAt (fun x : ℝ => 2*x) 2 z := by
    simpa using (hasDerivAt_id z).const_mul (2:ℝ)
  have hp : HasDerivAt (fun x : ℝ => 1 + 2*x) 2 z := h2x.const_add 1
  have h := ((exp_neg_hasDerivAt z).const_mul (1/3)).mul hp
  convert h using 1
  unfold L4d
  ring

/-- **`K4` is `(2θ+1)L4`.**  `2z·L4' + L4 = K4`: in Mellin space `(1−2s)L̂4 = K̂4`,
solvable because `K̂4(s) = (−4/3)Γ(s)(s−½)(s+½)` carries the `(s−½)` factor. -/
theorem L4_ode (z : ℝ) : 2*z*L4d z + L4 z = K4 z := by
  unfold L4d L4 K4
  ring

/-- **`K4` is an exact `v`-derivative with regular primitive.**
`∂_v [v·L4(a u²v²)] = K4(a u²v²)` — the second-stage IBP kernel for the edge
analysis (no singular weight; `v·L4` vanishes at `v = 0`). -/
theorem K4_exact_deriv (a u v : ℝ) :
    HasDerivAt (fun v' => v' * L4 (a*u^2*v'^2)) (K4 (a*u^2*v^2)) v := by
  have hL : HasDerivAt (fun v' : ℝ => L4 (a*u^2*v'^2))
      (L4d (a*u^2*v^2) * (2*a*u^2*v)) v := by
    have hz : HasDerivAt (fun v' : ℝ => a*u^2*v'^2) (2*a*u^2*v) v := by
      have h := (hasDerivAt_pow 2 v).const_mul (a*u^2)
      norm_num at h
      convert h using 1
      ring
    simpa [Function.comp] using (L4_hasDerivAt (a*u^2*v^2)).comp v hz
  have hid : HasDerivAt (fun v' : ℝ => v') 1 v := hasDerivAt_id v
  have h := hid.mul hL
  convert h using 1
  rw [← L4_ode (a*u^2*v^2)]
  ring

/-! ## The two edge-mass zeros -/

/-- **The `K4` edge mass vanishes**: `∫₀^∞ ξ^{−1/2} K4(ξ) dξ = 0` (`M[K4](½) = 0`).
This kills the leading edge contribution of the `−½K4` kernel piece along the null
axes — the 4D edge integrals are finite because of it. -/
theorem K4_moment_half : ∫ ξ in Ioi (0:ℝ), ξ ^ ((1:ℝ)/2 - 1) * K4 ξ = 0 := by
  have h := generic_mellin (1/2) (by norm_num) (1/3) (4/3) (-8/3) 0
  rw [setIntegral_congr_fun measurableSet_Ioi
    (g := fun ξ => ξ ^ ((1:ℝ)/2 - 1) *
      (Real.exp (-ξ) * ((1:ℝ)/3 + (4:ℝ)/3 * ξ + ((-8:ℝ)/3 / 2) * ξ ^ 2 + ((0:ℝ) / 6) * ξ ^ 3)))
    (fun ξ _ => by dsimp only; unfold K4; ring)]
  rw [h, Real.Gamma_one_half_eq, G_half_1, G_half_2]
  ring

/-- **The `J4` inverse-moment vanishes**: `∫₀^∞ ξ⁻¹ J4(ξ) dξ = ⅓(Γ(1) − Γ(2)) = 0`
(`M[J4](0) = 0`).  This kills the leading edge term of the `(u/v)·J4` kernel piece —
the singular-looking weight contributes nothing at the axis. -/
theorem J4_moment_neg_one : ∫ ξ in Ioi (0:ℝ), ξ⁻¹ * J4 ξ = 0 := by
  have ie0 : IntegrableOn (fun ξ : ℝ => Real.exp (-ξ)) (Ioi 0) := by
    simpa using UnifiedTheory.Audit.KFCausalMinkowskiAngular2D.integrable_exp_pow 0
  have ie1 : IntegrableOn (fun ξ : ℝ => Real.exp (-ξ) * ξ) (Ioi 0) := by
    simpa using UnifiedTheory.Audit.KFCausalMinkowskiAngular2D.integrable_exp_pow 1
  rw [setIntegral_congr_fun measurableSet_Ioi
    (g := fun ξ => (1/3) * Real.exp (-ξ) - (1/3) * (Real.exp (-ξ) * ξ))
    ?_]
  · rw [integral_sub (ie0.const_mul (1/3)) (ie1.const_mul (1/3)), integral_const_mul,
      integral_const_mul, integral_exp_neg_Ioi]
    have h1 : ∫ ξ in Ioi (0:ℝ), Real.exp (-ξ) * ξ = 1 := by
      simpa using UnifiedTheory.Audit.KFCausalCSpecLaplaceScaling.gamma_monomial_integral 1
    rw [h1]
    norm_num
  · intro ξ hξ
    rw [mem_Ioi] at hξ
    dsimp only
    unfold J4
    field_simp
    try ring

#print axioms L4_hasDerivAt
#print axioms L4_ode
#print axioms K4_exact_deriv
#print axioms K4_moment_half
#print axioms J4_moment_neg_one

end UnifiedTheory.Audit.KFCausalMinkowski4DEdge
