/-
  Audit/KFCausalMinkowski4DKernel.lean   (Volume sector → the 4D null-kernel identity)

  Rung 2 of the 4D ladder: the EXACT 4D kernel identity — the 4D analogue of the 2D
  corner-gate identity `∂_U∂_W H(aUW) = a·f2D(aUW)` that closed the 2D operator theorem.

  THE SETUP.  In 4D the past cone in radial-null coordinates (`u = −(t+r)`,
  `v = −(t−r)`, `v ≥ u ≥ 0`, symmetrized to the quadrant) has measure `∝ (v−u)² du dv`
  (the `r²` of the S² shells), the interval volume is `V = (π/24)(uv)²` (`τ² = uv`),
  so the smearing argument is `z = a·u²v²` with `a = ρπ/24`.  The obstruction relative
  to 2D is the `(v−u)²` Jacobian and the QUADRATIC `z = a(uv)²`.

  THE IDENTITY (this file, machine-checked): with

      K4(z) = ⅓e^{−z}(1 + 4z − 4z²),      J4(z) = ⅓e^{−z}(z − z²),

  the mixed partial of the combined kernel is exactly the 4D cone integrand:

      ∂_u∂_v [ (v/u)·J4(z) + (u/v)·J4(z) − ½·K4(z) ]  =  a·(v−u)²·f4D(z),  z = a u²v².

  (`kernel4_deriv_v` + `kernel4_mixed`.)  It decomposes via two ODEs:

      K4' + z·K4''            = f4D(z)         (`K4_ode`, the −2uv piece)
      4z²·J4'' + 4z·J4' − J4  = z·f4D(z)       (`J4_ode`, the u² and v² pieces).

  WHY THE KERNELS EXIST — THE RESONANCE.  In Mellin space the second ODE reads
  `(4s² − 1)Ĵ(s) = f̂4D(s+1)`, and `f̂4D(s) = Γ(s)·(−4/3)(s−½)(s−1)(s−3/2)`
  (`f4D_mellin`), so the would-be poles at `s = ±½` are CANCELED by the `s = 1/2`,
  `s = 3/2` moment zeros: the SAME cancellation conditions that force the layer
  coefficients (`layer_uniqueness`) are exactly the solvability conditions for the
  4D kernels in closed exponential-polynomial form.  The layer weights `(1,−9,16,−8)`
  are what make the 4D light cone integrable by parts.

  EDGE STRUCTURE (for the next rung): on the axes the combined kernel tends to the
  CONSTANT `−½K4(0) = −1/6` (`J4(0) = 0` kills the singular-looking `(v/u)` pieces),
  so the double IBP will produce corner/edge terms `∝ φ(0)` — the counterterm
  cancellation — and the interior term `∬ 𝒦4 ∂_u∂_vφ̄`, exactly as in 2D.

  HONEST SCOPE.  This rung certifies the exact-derivative structure (the analytic
  heart).  Remaining for the complete 4D operator theorem: the corner-limit lemmas
  for `z = a u²v²` concentration, the edge-constant handling, the S²-average/profile
  reduction (`φ̄`), and the final assembly — the 4D analogues of the corner gate and
  the 2D assembly, in that order.

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowski4DMoments

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Real
open UnifiedTheory.Audit.KFCausalMinkowski4DMoments

namespace UnifiedTheory.Audit.KFCausalMinkowski4DKernel

/-! ## The two 4D kernels and their derivatives -/

/-- The 4D `uv`-kernel `K4(z) = ⅓e^{−z}(1 + 4z − 4z²)`. -/
noncomputable def K4 (z : ℝ) : ℝ := (1/3) * Real.exp (-z) * (1 + 4*z - 4*z^2)

/-- `K4' = ⅓e^{−z}(3 − 12z + 4z²)`. -/
noncomputable def K4d (z : ℝ) : ℝ := (1/3) * Real.exp (-z) * (3 - 12*z + 4*z^2)

/-- `K4'' = ⅓e^{−z}(−15 + 20z − 4z²)`. -/
noncomputable def K4dd (z : ℝ) : ℝ := (1/3) * Real.exp (-z) * (-15 + 20*z - 4*z^2)

/-- The 4D `u²/v²`-kernel `J4(z) = ⅓e^{−z}(z − z²)`.  `J4(0) = 0` regularizes the
`(v/u)` weights on the axes. -/
noncomputable def J4 (z : ℝ) : ℝ := (1/3) * Real.exp (-z) * (z - z^2)

/-- `J4' = ⅓e^{−z}(1 − 3z + z²)`. -/
noncomputable def J4d (z : ℝ) : ℝ := (1/3) * Real.exp (-z) * (1 - 3*z + z^2)

/-- `J4'' = ⅓e^{−z}(−4 + 5z − z²)`. -/
noncomputable def J4dd (z : ℝ) : ℝ := (1/3) * Real.exp (-z) * (-4 + 5*z - z^2)

/-- The `∂_v`-combination `G4 = J4 + 2z·J4'` (from the `(v/u)` piece). -/
noncomputable def G4 (z : ℝ) : ℝ := J4 z + 2*z*J4d z

/-- The `∂_v`-combination `H4 = 2z·J4' − J4` (from the `(u/v)` piece). -/
noncomputable def H4 (z : ℝ) : ℝ := 2*z*J4d z - J4 z

private lemma exp_neg_hasDerivAt (z : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-z)) z := by
  simpa using (Real.hasDerivAt_exp (-z)).comp z (hasDerivAt_neg z)

private lemma hasDerivAt_sq (x : ℝ) : HasDerivAt (fun y : ℝ => y^2) (2*x) x := by
  have h := hasDerivAt_pow 2 x
  norm_num at h
  exact h

theorem K4_hasDerivAt (z : ℝ) : HasDerivAt K4 (K4d z) z := by
  show HasDerivAt (fun x => (1/3) * Real.exp (-x) * (1 + 4*x - 4*x^2)) (K4d z) z
  have h4x : HasDerivAt (fun x : ℝ => 4*x) 4 z := by
    simpa using (hasDerivAt_id z).const_mul (4:ℝ)
  have h4sq : HasDerivAt (fun x : ℝ => 4*x^2) (4*(2*z)) z := (hasDerivAt_sq z).const_mul 4
  have hp : HasDerivAt (fun x : ℝ => 1 + 4*x - 4*x^2) (4 - 4*(2*z)) z :=
    (h4x.const_add 1).sub h4sq
  have h := ((exp_neg_hasDerivAt z).const_mul (1/3)).mul hp
  convert h using 1
  unfold K4d
  ring

theorem K4d_hasDerivAt (z : ℝ) : HasDerivAt K4d (K4dd z) z := by
  show HasDerivAt (fun x => (1/3) * Real.exp (-x) * (3 - 12*x + 4*x^2)) (K4dd z) z
  have h12x : HasDerivAt (fun x : ℝ => 12*x) 12 z := by
    simpa using (hasDerivAt_id z).const_mul (12:ℝ)
  have h4sq : HasDerivAt (fun x : ℝ => 4*x^2) (4*(2*z)) z := (hasDerivAt_sq z).const_mul 4
  have hp : HasDerivAt (fun x : ℝ => 3 - 12*x + 4*x^2) (-12 + 4*(2*z)) z :=
    (h12x.const_sub 3).add h4sq
  have h := ((exp_neg_hasDerivAt z).const_mul (1/3)).mul hp
  convert h using 1
  unfold K4dd
  ring

theorem J4_hasDerivAt (z : ℝ) : HasDerivAt J4 (J4d z) z := by
  show HasDerivAt (fun x => (1/3) * Real.exp (-x) * (x - x^2)) (J4d z) z
  have hid : HasDerivAt (fun x : ℝ => x) 1 z := hasDerivAt_id z
  have hp : HasDerivAt (fun x : ℝ => x - x^2) (1 - 2*z) z := hid.sub (hasDerivAt_sq z)
  have h := ((exp_neg_hasDerivAt z).const_mul (1/3)).mul hp
  convert h using 1
  unfold J4d
  ring

theorem J4d_hasDerivAt (z : ℝ) : HasDerivAt J4d (J4dd z) z := by
  show HasDerivAt (fun x => (1/3) * Real.exp (-x) * (1 - 3*x + x^2)) (J4dd z) z
  have h3x : HasDerivAt (fun x : ℝ => 3*x) 3 z := by
    simpa using (hasDerivAt_id z).const_mul (3:ℝ)
  have hp : HasDerivAt (fun x : ℝ => 1 - 3*x + x^2) (-3 + 2*z) z :=
    (h3x.const_sub 1).add (hasDerivAt_sq z)
  have h := ((exp_neg_hasDerivAt z).const_mul (1/3)).mul hp
  convert h using 1
  unfold J4dd
  ring

theorem G4_hasDerivAt (z : ℝ) : HasDerivAt G4 (3*J4d z + 2*z*J4dd z) z := by
  show HasDerivAt (fun x => J4 x + 2*x*J4d x) (3*J4d z + 2*z*J4dd z) z
  have h2x : HasDerivAt (fun x : ℝ => 2*x) 2 z := by
    simpa using (hasDerivAt_id z).const_mul (2:ℝ)
  have h2 := h2x.mul (J4d_hasDerivAt z)
  have h := (J4_hasDerivAt z).add h2
  convert h using 1
  ring

theorem H4_hasDerivAt (z : ℝ) : HasDerivAt H4 (J4d z + 2*z*J4dd z) z := by
  show HasDerivAt (fun x => 2*x*J4d x - J4 x) (J4d z + 2*z*J4dd z) z
  have h2x : HasDerivAt (fun x : ℝ => 2*x) 2 z := by
    simpa using (hasDerivAt_id z).const_mul (2:ℝ)
  have h2 := h2x.mul (J4d_hasDerivAt z)
  have h := h2.sub (J4_hasDerivAt z)
  convert h using 1
  ring

/-! ## The two kernel ODEs (and the resonance) -/

/-- **ODE 1 (the `uv`-kernel).**  `K4' + z·K4'' = f4D(z)`. -/
theorem K4_ode (z : ℝ) : K4d z + z * K4dd z = f4D z := by
  unfold K4d K4dd f4D
  ring

/-- **ODE 2 (the `u²/v²`-kernel).**  `4z²J4'' + 4zJ4' − J4 = z·f4D(z)`.  Its Mellin
form `(4s²−1)Ĵ = f̂4D(s+1)` is solvable in exponential-polynomial form precisely
because `f̂4D` vanishes at `s = 1/2` and `s = 3/2` — the moment zeros of
`layer_uniqueness` are the solvability conditions. -/
theorem J4_ode (z : ℝ) : 4*z^2*J4dd z + 4*z*J4d z - J4 z = z * f4D z := by
  unfold J4dd J4d J4 f4D
  ring

/-! ## The chain derivatives in the null coordinates -/

private lemma z_deriv_v (a u v : ℝ) :
    HasDerivAt (fun v' : ℝ => a*u^2*v'^2) (2*a*u^2*v) v := by
  have h := (hasDerivAt_sq v).const_mul (a*u^2)
  convert h using 1
  ring

private lemma z_deriv_u (a u v : ℝ) :
    HasDerivAt (fun u' : ℝ => a*u'^2*v^2) (2*a*u*v^2) u := by
  have h := (hasDerivAt_sq u).const_mul (a*v^2)
  convert h using 1
  · funext x; ring
  · ring

/-- **The first partial `∂_v` of the combined 4D kernel.**  For `u, v ≠ 0`,

    ∂_v [ (v/u)J4(z) + (u/v)J4(z) − ½K4(z) ]
      = u⁻¹·G4(z) + u·(v²)⁻¹·H4(z) − a u²v·K4'(z),      z = a u²v². -/
theorem kernel4_deriv_v (a u v : ℝ) (hu : u ≠ 0) (hv : v ≠ 0) :
    HasDerivAt (fun v' => (v'/u) * J4 (a*u^2*v'^2) + u * v'⁻¹ * J4 (a*u^2*v'^2)
        - (1/2) * K4 (a*u^2*v'^2))
      (u⁻¹ * G4 (a*u^2*v^2) + u * (v^2)⁻¹ * H4 (a*u^2*v^2)
        - a*u^2*v * K4d (a*u^2*v^2)) v := by
  have hJcomp : HasDerivAt (fun v' : ℝ => J4 (a*u^2*v'^2))
      (J4d (a*u^2*v^2) * (2*a*u^2*v)) v := by
    simpa [Function.comp] using (J4_hasDerivAt (a*u^2*v^2)).comp v (z_deriv_v a u v)
  have hKcomp : HasDerivAt (fun v' : ℝ => K4 (a*u^2*v'^2))
      (K4d (a*u^2*v^2) * (2*a*u^2*v)) v := by
    simpa [Function.comp] using (K4_hasDerivAt (a*u^2*v^2)).comp v (z_deriv_v a u v)
  have pA : HasDerivAt (fun v' => (v'/u) * J4 (a*u^2*v'^2))
      (u⁻¹ * G4 (a*u^2*v^2)) v := by
    have hdiv : HasDerivAt (fun v' : ℝ => v'/u) (1/u) v := by
      simpa using (hasDerivAt_id v).div_const u
    have h := hdiv.mul hJcomp
    convert h using 1
    unfold G4
    field_simp
    try ring
  have pB : HasDerivAt (fun v' => u * v'⁻¹ * J4 (a*u^2*v'^2))
      (u * (v^2)⁻¹ * H4 (a*u^2*v^2)) v := by
    have hinv : HasDerivAt (fun v' : ℝ => u * v'⁻¹) (u * (-(v^2)⁻¹)) v :=
      (hasDerivAt_inv hv).const_mul u
    have h := hinv.mul hJcomp
    convert h using 1
    unfold H4
    field_simp
    ring
  have pC : HasDerivAt (fun v' => (1/2) * K4 (a*u^2*v'^2))
      (a*u^2*v * K4d (a*u^2*v^2)) v := by
    have h := hKcomp.const_mul (1/2 : ℝ)
    convert h using 1
    ring
  exact (pA.add pB).sub pC

/-- **The mixed partial `∂_u∂_v` — THE 4D KERNEL IDENTITY.**  For `u, v ≠ 0`,

    ∂_u [ u⁻¹·G4(z) + u·(v²)⁻¹·H4(z) − a u²v·K4'(z) ]  =  a·(v−u)²·f4D(z),

with `z = a u²v²`: the mixed second derivative of the combined kernel is exactly the
4D cone integrand `(v−u)²f4D` (times `a`) — the 4D analogue of the 2D
`∂_U∂_W H(aUW) = a·f2D(aUW)`. -/
theorem kernel4_mixed (a u v : ℝ) (hu : u ≠ 0) (hv : v ≠ 0) :
    HasDerivAt (fun u' => u'⁻¹ * G4 (a*u'^2*v^2) + u' * (v^2)⁻¹ * H4 (a*u'^2*v^2)
        - a*u'^2*v * K4d (a*u'^2*v^2))
      (a*(v-u)^2 * f4D (a*u^2*v^2)) u := by
  have hGcomp : HasDerivAt (fun u' : ℝ => G4 (a*u'^2*v^2))
      ((3*J4d (a*u^2*v^2) + 2*(a*u^2*v^2)*J4dd (a*u^2*v^2)) * (2*a*u*v^2)) u := by
    simpa [Function.comp] using (G4_hasDerivAt (a*u^2*v^2)).comp u (z_deriv_u a u v)
  have hHcomp : HasDerivAt (fun u' : ℝ => H4 (a*u'^2*v^2))
      ((J4d (a*u^2*v^2) + 2*(a*u^2*v^2)*J4dd (a*u^2*v^2)) * (2*a*u*v^2)) u := by
    simpa [Function.comp] using (H4_hasDerivAt (a*u^2*v^2)).comp u (z_deriv_u a u v)
  have hKdcomp : HasDerivAt (fun u' : ℝ => K4d (a*u'^2*v^2))
      (K4dd (a*u^2*v^2) * (2*a*u*v^2)) u := by
    simpa [Function.comp] using (K4d_hasDerivAt (a*u^2*v^2)).comp u (z_deriv_u a u v)
  have qA : HasDerivAt (fun u' => u'⁻¹ * G4 (a*u'^2*v^2))
      (a*v^2 * f4D (a*u^2*v^2)) u := by
    have h := (hasDerivAt_inv hu).mul hGcomp
    convert h using 1
    unfold G4 J4 J4d J4dd f4D
    field_simp
    ring
  have qB : HasDerivAt (fun u' => u' * (v^2)⁻¹ * H4 (a*u'^2*v^2))
      (a*u^2 * f4D (a*u^2*v^2)) u := by
    have hlin : HasDerivAt (fun u' : ℝ => u' * (v^2)⁻¹) ((v^2)⁻¹) u := by
      simpa using (hasDerivAt_id u).mul_const ((v^2)⁻¹ : ℝ)
    have h := hlin.mul hHcomp
    convert h using 1
    unfold H4 J4 J4d J4dd f4D
    field_simp
    ring
  have qC : HasDerivAt (fun u' => a*u'^2*v * K4d (a*u'^2*v^2))
      (2*a*u*v * f4D (a*u^2*v^2)) u := by
    have hpow : HasDerivAt (fun u' : ℝ => a*u'^2*v) (a*(2*u)*v) u := by
      have h := (hasDerivAt_sq u).const_mul a
      have h2 := h.mul_const v
      convert h2 using 1
    have h := hpow.mul hKdcomp
    convert h using 1
    unfold K4d K4dd f4D
    ring
  have h := (qA.add qB).sub qC
  convert h using 1
  ring

/-! ## Edge structure (input to the next rung) -/

/-- `K4(0) = 1/3`: the combined kernel tends to the constant `−½K4(0) = −1/6` on the
axes (the `J4` pieces vanish there since `J4(0) = 0`) — the source of the corner/edge
terms that will cancel the BDG counterterm. -/
theorem K4_zero : K4 0 = 1/3 := by unfold K4; norm_num

theorem J4_zero : J4 0 = 0 := by unfold J4; norm_num

#print axioms K4_hasDerivAt
#print axioms K4d_hasDerivAt
#print axioms J4_hasDerivAt
#print axioms J4d_hasDerivAt
#print axioms G4_hasDerivAt
#print axioms H4_hasDerivAt
#print axioms K4_ode
#print axioms J4_ode
#print axioms kernel4_deriv_v
#print axioms kernel4_mixed

end UnifiedTheory.Audit.KFCausalMinkowski4DKernel
