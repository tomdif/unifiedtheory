/-
  Audit/KFCausalMinkowskiRadial.lean   (Volume sector → the RADIAL analytic core)

  The RADIAL ANALYTIC CORE of the 2D causal-set continuum limit -- NOT the full 2D
  continuum theorem.  This closes the one-variable statement where the operator's second
  derivative genuinely emerges; the full 2D theorem additionally needs the null-coordinate
  reduction and dominated convergence over the noncompact rapidity direction (see the
  mixed-kernel identity `mixedKernel_identity` below, the route that does the cancellation
  before the limit).

  RADIAL CORE.  For `ψ` with a continuous, globally bounded second derivative,

      λ² ∫_0^∞ f(s) ψ(s/λ) ds  →  ψ''(0)      (λ → ∞),

  where `f = f2D` is the 2D BDG smearing function.  The mechanism is the kernel identity
  `f = ½ (s² e^{-s})''`: integrating by parts twice moves the two derivatives onto `ψ`,

      λ² ∫_0^∞ f(s) ψ(s/λ) ds  =  ½ ∫_0^∞ s² e^{-s} ψ''(s/λ) ds     (`radial_ibp_identity`),

  and dominated convergence (`s² e^{-s}` integrable, `ψ''` bounded and continuous at `0`)
  sends the right side to `½ ψ''(0) ∫ s² e^{-s} = ½ ψ''(0) · 2 = ψ''(0)`.  The bound on
  `ψ''` is kept as an explicit hypothesis, not hidden in a smoothness structure.

  MIXED-KERNEL IDENTITY (next target).  `H(z) = ½ e^{-z}(z-1)` satisfies
  `H'(z) + z H''(z) = f(z)`, hence `∂_U ∂_W H(ρ c₀ U W) = ρ c₀ f(ρ c₀ U W)` -- the true
  Lorentzian integration-by-parts identity that transfers one `U`- and one `W`-derivative
  directly onto the field, producing `∂_U ∂_W φ ∝ □φ`, and does the corner cancellation
  before the limit.

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowskiAngular2D

set_option autoImplicit false

open MeasureTheory Real Set Filter Topology
open UnifiedTheory.Audit.KFCausalMinkowskiAngular2D

namespace UnifiedTheory.Audit.KFCausalMinkowskiRadial

/-- Integrability of `s² e^{-s} · (bounded)` on `(0,∞)`: bounded by `M · (e^{-s} s²)`. -/
private theorem integrable_g_bound (M : ℝ) :
    Integrable (fun s => M * (Real.exp (-s) * s ^ 2)) (volume.restrict (Ioi (0 : ℝ))) :=
  (integrable_exp_pow 2).const_mul M

/-- **Radial IBP identity.**  For a `C²` function `φ` with `φ` and `φ'` compactly
supported, moving both derivatives from the kernel `f = ½(s²e^{-s})''` onto `φ`:

    ∫_0^∞ f(s) φ(s) ds = ½ ∫_0^∞ s² e^{-s} φ''(s) ds. -/
theorem radial_ibp_identity (φ φ' φ'' : ℝ → ℝ)
    (hφ : ∀ x, HasDerivAt φ (φ' x) x) (hφ' : ∀ x, HasDerivAt φ' (φ'' x) x)
    (hφc : Continuous φ) (hφ'c : Continuous φ') (hφ''c : Continuous φ'')
    (hsφ : HasCompactSupport φ) (hsφ' : HasCompactSupport φ') (hsφ'' : HasCompactSupport φ'') :
    ∫ s in Ioi (0 : ℝ), f2D s * φ s
      = (1 / 2) * ∫ s in Ioi (0 : ℝ), Real.exp (-s) * s ^ 2 * φ'' s := by
  -- g' = fun x => exp(-x)*(2x-x²) has derivative 2·f2D; g = x²e^{-x} has derivative g'
  have hg' : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (fun y => Real.exp (-y) * (2 * y - y ^ 2)) (2 * f2D x) x :=
    fun x _ => f2D_kernel_second_deriv x
  have hg : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (fun y => y ^ 2 * Real.exp (-y))
      (Real.exp (-x) * (2 * x - x ^ 2)) x := fun x _ => f2D_kernel_first_deriv x
  have hφI : ∀ x ∈ Ioi (0:ℝ), HasDerivAt φ (φ' x) x := fun x _ => hφ x
  have hφ'I : ∀ x ∈ Ioi (0:ℝ), HasDerivAt φ' (φ'' x) x := fun x _ => hφ' x
  -- integrabilities (continuous × compact support)
  have iC : ∀ (a b : ℝ → ℝ), Continuous a → HasCompactSupport b → Continuous b →
      IntegrableOn (a * b) (Ioi (0:ℝ)) := by
    intro a b ha hsb hb
    exact ((ha.mul hb).integrable_of_hasCompactSupport hsb.mul_left).integrableOn
  have hg'c : Continuous (fun y => Real.exp (-y) * (2 * y - y ^ 2)) := by fun_prop
  have hgc : Continuous (fun y => y ^ 2 * Real.exp (-y)) := by fun_prop
  have hff : Continuous (fun y => 2 * f2D y) := by unfold f2D; fun_prop
  -- IBP step 1:  ∫ g' φ' = [g'φ] - ∫ (2 f2D) φ,  boundaries 0  ⟹  ∫ (2 f2D) φ = -∫ g' φ'
  have bd1 : Tendsto ((fun y => Real.exp (-y) * (2 * y - y ^ 2)) * φ) atTop (𝓝 0) := by
    have : (fun y => Real.exp (-y) * (2 * y - y ^ 2)) * φ =ᶠ[atTop] 0 := by
      have := hsφ; rw [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact] at this
      filter_upwards [this.filter_mono atTop_le_cocompact] with x hx
      simp [Pi.mul_apply, hx]
    exact Tendsto.congr' this.symm tendsto_const_nhds
  have bd1' : Tendsto ((fun y => Real.exp (-y) * (2 * y - y ^ 2)) * φ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc : Continuous ((fun y => Real.exp (-y) * (2 * y - y ^ 2)) * φ) := hg'c.mul hφc
    have := hc.continuousAt (x := 0)
    simp only [Pi.mul_apply, neg_zero, Real.exp_zero] at this ⊢
    simpa using this.continuousWithinAt.tendsto
  have step1 := integral_Ioi_mul_deriv_eq_deriv_mul hg' hφI
    (iC _ φ' hg'c hsφ' hφ'c) (iC _ φ hff hsφ hφc) bd1' bd1
  -- IBP step 2:  ∫ g φ'' = [gφ'] - ∫ g' φ',  boundaries 0
  have bd2 : Tendsto ((fun y => y ^ 2 * Real.exp (-y)) * φ') atTop (𝓝 0) := by
    have : (fun y => y ^ 2 * Real.exp (-y)) * φ' =ᶠ[atTop] 0 := by
      have := hsφ'; rw [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact] at this
      filter_upwards [this.filter_mono atTop_le_cocompact] with x hx
      simp [Pi.mul_apply, hx]
    exact Tendsto.congr' this.symm tendsto_const_nhds
  have bd2' : Tendsto ((fun y => y ^ 2 * Real.exp (-y)) * φ') (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc : Continuous ((fun y => y ^ 2 * Real.exp (-y)) * φ') := hgc.mul hφ'c
    have := hc.continuousAt (x := 0)
    simp only [Pi.mul_apply] at this ⊢
    norm_num at this
    simpa using this.continuousWithinAt.tendsto
  have step2 := integral_Ioi_mul_deriv_eq_deriv_mul hg hφ'I
    (iC _ φ'' hgc hsφ'' hφ''c) (iC _ φ' hg'c hsφ' hφ'c) bd2' bd2
  -- assemble: ∫ (2 f2D) φ = ∫ g φ'', then halve
  simp only [sub_zero, zero_sub] at step1 step2
  have key : ∫ s in Ioi (0:ℝ), (2 * f2D s) * φ s
      = ∫ s in Ioi (0:ℝ), (fun y => y ^ 2 * Real.exp (-y)) s * φ'' s := by
    have e1 : ∫ s in Ioi (0:ℝ), (2 * f2D s) * φ s = -(∫ s in Ioi (0:ℝ),
        (fun y => Real.exp (-y) * (2 * y - y ^ 2)) s * φ' s) := by linarith [step1]
    have e2 : ∫ s in Ioi (0:ℝ), (fun y => y ^ 2 * Real.exp (-y)) s * φ'' s
        = -(∫ s in Ioi (0:ℝ), (fun y => Real.exp (-y) * (2 * y - y ^ 2)) s * φ' s) := by
      linarith [step2]
    rw [e1, e2]
  have hcm : ∫ s in Ioi (0:ℝ), (2 * f2D s) * φ s = 2 * ∫ s in Ioi (0:ℝ), f2D s * φ s := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s _; ring
  rw [hcm] at key
  have : ∫ s in Ioi (0:ℝ), f2D s * φ s
      = (1/2) * ∫ s in Ioi (0:ℝ), (fun y => y ^ 2 * Real.exp (-y)) s * φ'' s := by linarith [key]
  rw [this]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _; ring

#print axioms radial_ibp_identity

/-! ## The mixed-kernel identity (route to the full 2D theorem) -/

/-- The mixed null-coordinate kernel `H(z) = ½ e^{-z}(z-1)`. -/
noncomputable def Hkern (z : ℝ) : ℝ := (1 / 2) * Real.exp (-z) * (z - 1)

/-- `H'(z) = ½ e^{-z}(2 - z)`. -/
theorem Hkern_first_deriv (z : ℝ) :
    HasDerivAt Hkern ((1 / 2) * Real.exp (-z) * (2 - z)) z := by
  show HasDerivAt (fun x => (1 / 2) * Real.exp (-x) * (x - 1)) ((1 / 2) * Real.exp (-z) * (2 - z)) z
  have he : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-z)) z := by
    simpa using (Real.hasDerivAt_exp (-z)).comp z (hasDerivAt_neg z)
  have hlin : HasDerivAt (fun x : ℝ => x - 1) 1 z := by simpa using (hasDerivAt_id z).sub_const 1
  convert (he.const_mul (1 / 2)).mul hlin using 1
  ring

/-- `H''(z) = ½ e^{-z}(z - 3)`. -/
theorem Hkern_second_deriv (z : ℝ) :
    HasDerivAt (fun z => (1 / 2) * Real.exp (-z) * (2 - z)) ((1 / 2) * Real.exp (-z) * (z - 3)) z := by
  have he : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-z)) z := by
    simpa using (Real.hasDerivAt_exp (-z)).comp z (hasDerivAt_neg z)
  have hlin : HasDerivAt (fun x : ℝ => 2 - x) (-1) z := by simpa using (hasDerivAt_const z 2).sub (hasDerivAt_id z)
  have := ((he.const_mul (1 / 2)).mul hlin)
  convert this using 1
  ring

/-- **Mixed-kernel identity.**  `H'(z) + z H''(z) = f(z)`.  Via `z = ρc₀UW` this gives
`∂_U ∂_W H(ρc₀UW) = ρc₀ f(ρc₀UW)`, the Lorentzian IBP identity that transfers one `U`- and
one `W`-derivative onto the field -- the route that cancels before taking the limit. -/
theorem mixedKernel_identity (z : ℝ) :
    (1 / 2) * Real.exp (-z) * (2 - z) + z * ((1 / 2) * Real.exp (-z) * (z - 3)) = f2D z := by
  unfold f2D; ring

#print axioms Hkern_first_deriv
#print axioms Hkern_second_deriv
#print axioms mixedKernel_identity

end UnifiedTheory.Audit.KFCausalMinkowskiRadial
