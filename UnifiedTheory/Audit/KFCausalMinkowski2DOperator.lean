/-
  Audit/KFCausalMinkowski2DOperator.lean   (Volume sector → THE COMPLETE 2D OPERATOR THEOREM)

  The complete flat-space 2D causal-set d'Alembertian continuum theorem, assembled
  from the closed corner-kernel gate.  In null coordinates `U, W ≥ 0` on the past
  cone (with `V = UW/2` the Alexandrov interval volume, `c₀ = 1/2`, `dV = ½ dU dW`,
  `a := ρ c₀ = ρ/2`, `4/ℓ² = 4ρ = 8a`), the mean of the 2D Benincasa–Dowker operator
  on a field `ψ` (the null-coordinate pullback `ψ(U,W) = φ(x − null offsets)`) is

      ⟨B_ρ φ⟩(x)  =  8a [ −½ ψ(0,0) + a ∫∫_{(0,∞)²} f2D(aUW) ψ(U,W) dU dW ],

  where `f2D(ξ) = e^{−ξ}(1 − 2ξ + ½ξ²)` is the Poisson layer expectation
  `E[c_N]`, `c = (1,−2,1)` (the framework's `KFCausalCSpecPoissonMoments` /
  `LayerMomentConditions` supply the discrete↔mean step).

  THE THEOREM (`bdg_2d_operator_limit`):

      ⟨B_ρ φ⟩(x)  ⟶  −4 ∂_U∂_W ψ(0,0)      (a → ∞),

  which in Cartesian coordinates is `(∂_x² − ∂_t²)φ(x) = □φ(x)` in mostly-plus
  signature (dictionary: `∂_U∂_Wψ = ¼(∂_t² − ∂_x²)φ`, proved on the separable class
  below, standard chain rule in general).

  THE ASSEMBLY (exactly the four steps of the plan, all machine-checked):
   1. `operator_ibp_identity` — the double IBP `a∬ f2D(aUW)ψ = ½ψ(0,0) + ∬ H(aUW)∂_U∂_Wψ`
      produces the `+½ψ(0,0)` corner term (via the exact-derivative kernels
      `∂_W[aW·H'(aUW)] = a·f2D(aUW)`, `∂_U[H(aUW)] = aW·H'(aUW)`, rectangle IBPs,
      Fubini, and `boundary_ftc` for the axis term).
   2. The BDG local counterterm `−½ψ(0,0)` CANCELS the corner term exactly.
   3. `corner_kernel_limit` applied to `g = ∂_U∂_Wψ` gives `a∬H·g → −½g(0,0)`.
   4. The prefactor `8a` gives `−4∂_U∂_Wψ(0,0) = □φ`; sign and `c₀` conventions
      retained (`dictionary_separable` verifies the conversion with signs).

  A sanity anchor: at `a = 0` the identity reads `0 = ½ψ(0,0) − ½ψ(0,0)` (both sides
  telescope by FTC), which the general proof reproduces.

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowskiCorner

set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Real Set Filter Topology Function
open UnifiedTheory.Audit.KFCausalMinkowskiAngular2D
open UnifiedTheory.Audit.KFCausalMinkowskiRadial
open UnifiedTheory.Audit.KFCausalMinkowskiCorner

namespace UnifiedTheory.Audit.KFCausalMinkowski2DOperator

/-! ## Kernel facts -/

theorem Hkern_zero : Hkern 0 = -(1 / 2) := by unfold Hkern; norm_num

/-- **The `f`-kernel is an exact `W`-derivative**: `∂_W [a·W·H'(aUW)] = a·f2D(aUW)`,
via the mixed-kernel identity `H'(z) + zH''(z) = f2D(z)`. -/
theorem opker_deriv_W (a U W : ℝ) :
    HasDerivAt (fun w => a * w * ((1 / 2) * Real.exp (-(a * U * w)) * (2 - a * U * w)))
      (a * f2D (a * U * W)) W := by
  have h1 : HasDerivAt (fun w : ℝ => a * w) a W := by
    simpa using (hasDerivAt_id W).const_mul a
  have hz : HasDerivAt (fun w : ℝ => a * U * w) (a * U) W := by
    simpa using (hasDerivAt_id W).const_mul (a * U)
  have h2 : HasDerivAt (fun w : ℝ => (1 / 2) * Real.exp (-(a * U * w)) * (2 - a * U * w))
      ((1 / 2) * Real.exp (-(a * U * W)) * (a * U * W - 3) * (a * U)) W := by
    have := (Hkern_second_deriv (a * U * W)).comp W hz
    convert this using 1
  have h3 := h1.mul h2
  rw [show a * f2D (a * U * W)
      = a * ((1 / 2) * Real.exp (-(a * U * W)) * (2 - a * U * W)
          + (a * U * W) * ((1 / 2) * Real.exp (-(a * U * W)) * (a * U * W - 3)))
      from by rw [mixedKernel_identity]]
  convert h3 using 1
  ring

/-- **The `H'`-kernel is an exact `U`-derivative**: `∂_U [H(aUW)] = aW·H'(aUW)`. -/
theorem opker_deriv_U (a U W : ℝ) :
    HasDerivAt (fun u => Hkern (a * u * W))
      (a * W * ((1 / 2) * Real.exp (-(a * U * W)) * (2 - a * U * W))) U := by
  have hz : HasDerivAt (fun u : ℝ => a * u * W) (a * W) U := by
    have h := (hasDerivAt_id U).const_mul (a * W)
    have hfe : (fun y : ℝ => a * W * id y) = fun u : ℝ => a * u * W := by
      funext u; simp only [id_eq]; ring
    rw [hfe] at h
    simpa using h
  have := (Hkern_first_deriv (a * U * W)).comp U hz
  convert this using 1
  ring

/-! ## The two rectangle integrations by parts (compact intervals, no improper IBP) -/

/-- **Rectangle IBP in `W`** (pointwise in `U`): on `[0,B]` with `ψ(U,B) = 0`,
`a∫₀^B f2D(aUW)ψ dW = −∫₀^B (aW·H'(aUW))·∂_Wψ dW`.  Boundary: `W = 0` kills the
lower term (factor `W`), support kills the upper. -/
theorem op_rect_ibp_W (ψ pdW : ℝ → ℝ → ℝ)
    (hψc : Continuous (Function.uncurry ψ)) (hpdWc : Continuous (Function.uncurry pdW))
    (hd1 : ∀ U W, HasDerivAt (fun w => ψ U w) (pdW U W) W)
    (a U B : ℝ) (hψB : ψ U B = 0) :
    a * ∫ W in (0:ℝ)..B, f2D (a * U * W) * ψ U W
      = -∫ W in (0:ℝ)..B,
          (a * W * ((1 / 2) * Real.exp (-(a * U * W)) * (2 - a * U * W))) * pdW U W := by
  have hψU : Continuous (fun W => ψ U W) := hψc.comp (continuous_const.prodMk continuous_id)
  have hpdWU : Continuous (fun W => pdW U W) := hpdWc.comp (continuous_const.prodMk continuous_id)
  have hu'c : Continuous (fun W : ℝ => a * f2D (a * U * W)) := by unfold f2D; fun_prop
  have hibp := intervalIntegral.integral_deriv_mul_eq_sub
    (u := fun w => a * w * ((1 / 2) * Real.exp (-(a * U * w)) * (2 - a * U * w)))
    (v := fun w => ψ U w)
    (u' := fun w => a * f2D (a * U * w)) (v' := fun w => pdW U w)
    (fun W _ => opker_deriv_W a U W) (fun W _ => hd1 U W)
    (hu'c.intervalIntegrable 0 B) (hpdWU.intervalIntegrable 0 B)
  dsimp only at hibp
  rw [hψB] at hibp
  simp only [mul_zero, zero_mul, sub_zero] at hibp
  have hi1 : IntervalIntegrable (fun W => a * f2D (a * U * W) * ψ U W) volume 0 B := by
    have : Continuous (fun W => a * f2D (a * U * W) * ψ U W) := hu'c.mul hψU
    exact this.intervalIntegrable 0 B
  have hi2 : IntervalIntegrable
      (fun W => (a * W * ((1 / 2) * Real.exp (-(a * U * W)) * (2 - a * U * W))) * pdW U W)
      volume 0 B := by
    have : Continuous
        (fun W => (a * W * ((1 / 2) * Real.exp (-(a * U * W)) * (2 - a * U * W))) * pdW U W) := by
      exact (by fun_prop : Continuous
        (fun W : ℝ => a * W * ((1 / 2) * Real.exp (-(a * U * W)) * (2 - a * U * W)))).mul hpdWU
    exact this.intervalIntegrable 0 B
  rw [intervalIntegral.integral_add hi1 hi2] at hibp
  rw [show a * ∫ W in (0:ℝ)..B, f2D (a * U * W) * ψ U W
      = ∫ W in (0:ℝ)..B, a * f2D (a * U * W) * ψ U W from by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro W _
    dsimp only
    ring]
  linarith [hibp]

/-- **Rectangle IBP in `U`** (pointwise in `W`): on `[0,A]` with `∂_Wψ(A,W) = 0`,
`∫₀^A (aW·H'(aUW))·∂_Wψ dU = ½∂_Wψ(0,W) − ∫₀^A H(aUW)·∂_U∂_Wψ dU`.  The
`½∂_Wψ(0,W)` axis term comes from `H(0) = −½`; support kills the far end. -/
theorem op_rect_ibp_U (pdW pdUW : ℝ → ℝ → ℝ)
    (hpdWc : Continuous (Function.uncurry pdW)) (hpdUWc : Continuous (Function.uncurry pdUW))
    (hd2 : ∀ U W, HasDerivAt (fun u => pdW u W) (pdUW U W) U)
    (a W A : ℝ) (hpdWA : pdW A W = 0) :
    ∫ U in (0:ℝ)..A, (a * W * ((1 / 2) * Real.exp (-(a * U * W)) * (2 - a * U * W))) * pdW U W
      = (1 / 2) * pdW 0 W - ∫ U in (0:ℝ)..A, Hkern (a * U * W) * pdUW U W := by
  have hpdWW : Continuous (fun U => pdW U W) := hpdWc.comp (continuous_id.prodMk continuous_const)
  have hpdUWW : Continuous (fun U => pdUW U W) := hpdUWc.comp (continuous_id.prodMk continuous_const)
  have hu'c : Continuous
      (fun U : ℝ => a * W * ((1 / 2) * Real.exp (-(a * U * W)) * (2 - a * U * W))) := by fun_prop
  have hibp := intervalIntegral.integral_deriv_mul_eq_sub
    (u := fun u => Hkern (a * u * W)) (v := fun u => pdW u W)
    (u' := fun u => a * W * ((1 / 2) * Real.exp (-(a * u * W)) * (2 - a * u * W)))
    (v' := fun u => pdUW u W)
    (fun U _ => opker_deriv_U a U W) (fun U _ => hd2 U W)
    (hu'c.intervalIntegrable 0 A) (hpdUWW.intervalIntegrable 0 A)
  dsimp only at hibp
  rw [hpdWA] at hibp
  simp only [mul_zero, zero_sub, zero_mul] at hibp
  rw [Hkern_zero] at hibp
  have hi1 : IntervalIntegrable
      (fun U => (a * W * ((1 / 2) * Real.exp (-(a * U * W)) * (2 - a * U * W))) * pdW U W)
      volume 0 A := (hu'c.mul hpdWW).intervalIntegrable 0 A
  have hi2 : IntervalIntegrable (fun U => Hkern (a * U * W) * pdUW U W) volume 0 A := by
    have hHc : Continuous (fun U => Hkern (a * U * W)) := by unfold Hkern; fun_prop
    exact (hHc.mul hpdUWW).intervalIntegrable 0 A
  rw [intervalIntegral.integral_add hi1 hi2] at hibp
  linarith [hibp]

/-! ## Marginal integrability (Fubini route: no parametrized-continuity needed) -/

/-- The `W`-marginal of the `H·∂_U∂_Wψ` kernel is integrable, via product-measure
integrability of the compactly supported continuous integrand. -/
theorem op_marginal_integrable (pdUW : ℝ → ℝ → ℝ)
    (hpdUWc : Continuous (Function.uncurry pdUW))
    (hpdUWcs : HasCompactSupport (Function.uncurry pdUW)) (a : ℝ) :
    IntegrableOn (fun W => ∫ U in Ioi (0:ℝ), Hkern (a * U * W) * pdUW U W) (Ioi (0:ℝ)) := by
  have hKc : Continuous (fun p : ℝ × ℝ => Hkern (a * p.1 * p.2) * pdUW p.1 p.2) := by
    exact (by unfold Hkern; fun_prop : Continuous
      (fun p : ℝ × ℝ => Hkern (a * p.1 * p.2))).mul hpdUWc
  have hKcs : HasCompactSupport (fun p : ℝ × ℝ => Hkern (a * p.1 * p.2) * pdUW p.1 p.2) :=
    hpdUWcs.mul_left (f := fun p : ℝ × ℝ => Hkern (a * p.1 * p.2))
  have hglob : Integrable (fun p : ℝ × ℝ => Hkern (a * p.1 * p.2) * pdUW p.1 p.2) :=
    hKc.integrable_of_hasCompactSupport hKcs
  have hprod : Integrable (fun p : ℝ × ℝ => Hkern (a * p.1 * p.2) * pdUW p.1 p.2)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hglob.integrableOn
  exact hprod.integral_prod_right

/-! ## Step 1+2 — the master identity (corner term produced and exhibited) -/

/-- **The double-IBP identity (the corner term).**  For box-supported `C²` data,

    a ∬ f2D(aUW) ψ  =  ½ψ(0,0) + ∬ H(aUW) ∂_U∂_Wψ.

The `+½ψ(0,0)` is the corner term the BDG local counterterm `−½ψ(0,0)` cancels.
Assembly: `W`-rectangle IBP per `U` (support lifts to `Ioi`), Fubini, `U`-rectangle
IBP per `W`, and the axis FTC (`boundary_ftc`) for `∫ ∂_Wψ(0,·) = −ψ(0,0)`. -/
theorem operator_ibp_identity
    (ψ pdW pdUW : ℝ → ℝ → ℝ)
    (hψc : Continuous (Function.uncurry ψ)) (hpdWc : Continuous (Function.uncurry pdW))
    (hpdUWc : Continuous (Function.uncurry pdUW))
    (hd1 : ∀ U W, HasDerivAt (fun w => ψ U w) (pdW U W) W)
    (hd2 : ∀ U W, HasDerivAt (fun u => pdW u W) (pdUW U W) U)
    (hpdWcs : HasCompactSupport (Function.uncurry pdW))
    (hpdUWcs : HasCompactSupport (Function.uncurry pdUW))
    (a A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hψsW : ∀ U W, B ≤ W → ψ U W = 0)
    (hpdWsU : ∀ U W, A ≤ U → pdW U W = 0)
    (hpdWsW : ∀ U W, B ≤ W → pdW U W = 0)
    (hpdUWsU : ∀ U W, A ≤ U → pdUW U W = 0) :
    a * ∫ U in Ioi (0:ℝ), ∫ W in Ioi (0:ℝ), f2D (a * U * W) * ψ U W
      = (1 / 2) * ψ 0 0 + ∫ U in Ioi (0:ℝ), ∫ W in Ioi (0:ℝ), Hkern (a * U * W) * pdUW U W := by
  have hψU : ∀ U, Continuous (fun W => ψ U W) :=
    fun U => hψc.comp (continuous_const.prodMk continuous_id)
  have hpdWU : ∀ U, Continuous (fun W => pdW U W) :=
    fun U => hpdWc.comp (continuous_const.prodMk continuous_id)
  have hpdWslW : ∀ W, Continuous (fun U => pdW U W) :=
    fun W => hpdWc.comp (continuous_id.prodMk continuous_const)
  have hpdUWslW : ∀ W, Continuous (fun U => pdUW U W) :=
    fun W => hpdUWc.comp (continuous_id.prodMk continuous_const)
  -- Step 1: per-U identity on Ioi
  have step1 : ∀ U, a * ∫ W in Ioi (0:ℝ), f2D (a * U * W) * ψ U W
      = -∫ W in Ioi (0:ℝ),
          (a * W * ((1 / 2) * Real.exp (-(a * U * W)) * (2 - a * U * W))) * pdW U W := by
    intro U
    have hfc : Continuous (fun W => f2D (a * U * W) * ψ U W) := by
      exact (by unfold f2D; fun_prop : Continuous (fun W => f2D (a * U * W))).mul (hψU U)
    have hPc : Continuous
        (fun W => (a * W * ((1 / 2) * Real.exp (-(a * U * W)) * (2 - a * U * W))) * pdW U W) := by
      exact (by fun_prop : Continuous
        (fun W : ℝ => a * W * ((1 / 2) * Real.exp (-(a * U * W)) * (2 - a * U * W)))).mul (hpdWU U)
    rw [← corner_interval_to_Ioi (fun W => f2D (a * U * W) * ψ U W) B hB hfc
          (fun W hW => by simp [hψsW U W hW]),
        ← corner_interval_to_Ioi
          (fun W => (a * W * ((1 / 2) * Real.exp (-(a * U * W)) * (2 - a * U * W))) * pdW U W)
          B hB hPc (fun W hW => by simp [hpdWsW U W hW])]
    exact op_rect_ibp_W ψ pdW hψc hpdWc hd1 a U B (hψsW U B le_rfl)
  -- Rewrite LHS through step 1 and pull the minus out
  have lhs1 : a * ∫ U in Ioi (0:ℝ), ∫ W in Ioi (0:ℝ), f2D (a * U * W) * ψ U W
      = -∫ U in Ioi (0:ℝ), ∫ W in Ioi (0:ℝ),
          (a * W * ((1 / 2) * Real.exp (-(a * U * W)) * (2 - a * U * W))) * pdW U W := by
    rw [← integral_const_mul]
    rw [setIntegral_congr_fun measurableSet_Ioi
      (g := fun U => -(∫ W in Ioi (0:ℝ),
        (a * W * ((1 / 2) * Real.exp (-(a * U * W)) * (2 - a * U * W))) * pdW U W))
      (fun U _ => step1 U)]
    rw [integral_neg]
  -- Step 2: Fubini swap on the P·pdW integral
  have hPunc : Continuous (Function.uncurry
      (fun U W => (a * W * ((1 / 2) * Real.exp (-(a * U * W)) * (2 - a * U * W))) * pdW U W)) := by
    exact (by fun_prop : Continuous
      (fun p : ℝ × ℝ => a * p.2 * ((1 / 2) * Real.exp (-(a * p.1 * p.2)) * (2 - a * p.1 * p.2)))).mul
      hpdWc
  have hPcs : HasCompactSupport (Function.uncurry
      (fun U W => (a * W * ((1 / 2) * Real.exp (-(a * U * W)) * (2 - a * U * W))) * pdW U W)) :=
    hpdWcs.mul_left
      (f := fun p : ℝ × ℝ => a * p.2 * ((1 / 2) * Real.exp (-(a * p.1 * p.2)) * (2 - a * p.1 * p.2)))
  have swap1 : (∫ U in Ioi (0:ℝ), ∫ W in Ioi (0:ℝ),
        (a * W * ((1 / 2) * Real.exp (-(a * U * W)) * (2 - a * U * W))) * pdW U W)
      = ∫ W in Ioi (0:ℝ), ∫ U in Ioi (0:ℝ),
        (a * W * ((1 / 2) * Real.exp (-(a * U * W)) * (2 - a * U * W))) * pdW U W :=
    integral_integral_swap_of_hasCompactSupport hPunc hPcs
  -- Step 3: per-W identity on Ioi
  have step3 : ∀ W, (∫ U in Ioi (0:ℝ),
        (a * W * ((1 / 2) * Real.exp (-(a * U * W)) * (2 - a * U * W))) * pdW U W)
      = (1 / 2) * pdW 0 W - ∫ U in Ioi (0:ℝ), Hkern (a * U * W) * pdUW U W := by
    intro W
    have hPc : Continuous
        (fun U => (a * W * ((1 / 2) * Real.exp (-(a * U * W)) * (2 - a * U * W))) * pdW U W) := by
      exact (by fun_prop : Continuous
        (fun U : ℝ => a * W * ((1 / 2) * Real.exp (-(a * U * W)) * (2 - a * U * W)))).mul
        (hpdWslW W)
    have hHc : Continuous (fun U => Hkern (a * U * W) * pdUW U W) := by
      exact (by unfold Hkern; fun_prop : Continuous (fun U => Hkern (a * U * W))).mul (hpdUWslW W)
    rw [← corner_interval_to_Ioi
          (fun U => (a * W * ((1 / 2) * Real.exp (-(a * U * W)) * (2 - a * U * W))) * pdW U W)
          A hA hPc (fun U hU => by simp [hpdWsU U W hU]),
        ← corner_interval_to_Ioi (fun U => Hkern (a * U * W) * pdUW U W) A hA hHc
          (fun U hU => by simp [hpdUWsU U W hU])]
    exact op_rect_ibp_U pdW pdUW hpdWc hpdUWc hd2 a W A (hpdWsU A W le_rfl)
  -- Step 4: split, FTC, and swap back
  have h1int : IntegrableOn (fun W => (1 / 2) * pdW 0 W) (Ioi (0:ℝ)) :=
    (corner_slice_integrable (fun W => pdW 0 W) B hB (hpdWU 0)
      (fun W hW => hpdWsW 0 W hW)).const_mul (1 / 2)
  have h2int := op_marginal_integrable pdUW hpdUWc hpdUWcs a
  have hftc : ∫ W in Ioi (0:ℝ), pdW 0 W = -ψ 0 0 :=
    boundary_ftc (fun W => ψ 0 W) (fun W => pdW 0 W) B (fun W => hd1 0 W)
      (corner_slice_integrable (fun W => pdW 0 W) B hB (hpdWU 0)
        (fun W hW => hpdWsW 0 W hW))
      (fun W hW => hψsW 0 W hW)
  -- swap back for the H·pdUW integral
  have hHunc : Continuous (Function.uncurry (fun U W => Hkern (a * U * W) * pdUW U W)) := by
    exact (by unfold Hkern; fun_prop : Continuous
      (fun p : ℝ × ℝ => Hkern (a * p.1 * p.2))).mul hpdUWc
  have hHcs : HasCompactSupport (Function.uncurry (fun U W => Hkern (a * U * W) * pdUW U W)) :=
    hpdUWcs.mul_left (f := fun p : ℝ × ℝ => Hkern (a * p.1 * p.2))
  have swap2 : (∫ U in Ioi (0:ℝ), ∫ W in Ioi (0:ℝ), Hkern (a * U * W) * pdUW U W)
      = ∫ W in Ioi (0:ℝ), ∫ U in Ioi (0:ℝ), Hkern (a * U * W) * pdUW U W :=
    integral_integral_swap_of_hasCompactSupport hHunc hHcs
  -- assemble
  rw [lhs1, swap1]
  rw [setIntegral_congr_fun measurableSet_Ioi
    (g := fun W => (1 / 2) * pdW 0 W - ∫ U in Ioi (0:ℝ), Hkern (a * U * W) * pdUW U W)
    (fun W _ => step3 W)]
  rw [integral_sub h1int h2int, integral_const_mul, hftc, swap2]
  ring

/-! ## Steps 3+4 — the complete 2D operator theorem -/

/-- **THE COMPLETE 2D OPERATOR THEOREM** (flat space, null coordinates).

    8a [ −½ψ(0,0) + a ∬ f2D(aUW) ψ ]  ⟶  −4 ∂_U∂_Wψ(0,0)      (a → ∞).

The left side is exactly the mean 2D Benincasa–Dowker operator `⟨B_ρφ⟩` with
`a = ρc₀ = ρ/2` and `8a = 4/ℓ²`; the right side is `□φ` in mostly-plus signature
(`−4∂_U∂_Wψ = (∂_x² − ∂_t²)φ`; see `dictionary_separable`).  Assembled from the
double-IBP identity (corner term), its exact cancellation against the BDG local
counterterm, and the closed corner-kernel gate `corner_kernel_limit`. -/
theorem bdg_2d_operator_limit
    (ψ pdW pdUW pdUWW : ℝ → ℝ → ℝ)
    (hψc : Continuous (Function.uncurry ψ)) (hpdWc : Continuous (Function.uncurry pdW))
    (hpdUWc : Continuous (Function.uncurry pdUW)) (hpdUWWc : Continuous (Function.uncurry pdUWW))
    (hd1 : ∀ U W, HasDerivAt (fun w => ψ U w) (pdW U W) W)
    (hd2 : ∀ U W, HasDerivAt (fun u => pdW u W) (pdUW U W) U)
    (hd3 : ∀ U W, HasDerivAt (fun w => pdUW U w) (pdUWW U W) W)
    (hpdWcs : HasCompactSupport (Function.uncurry pdW))
    (hpdUWcs : HasCompactSupport (Function.uncurry pdUW))
    (hpdUWWcs : HasCompactSupport (Function.uncurry pdUWW))
    (A B M : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hψsW : ∀ U W, B ≤ W → ψ U W = 0)
    (hpdWsU : ∀ U W, A ≤ U → pdW U W = 0)
    (hpdWsW : ∀ U W, B ≤ W → pdW U W = 0)
    (hpdUWsU : ∀ U W, A ≤ U → pdUW U W = 0)
    (hpdUWsW : ∀ U W, B ≤ W → pdUW U W = 0)
    (hpdUWWsW : ∀ U W, B ≤ W → pdUWW U W = 0)
    (hM : ∀ U W, |pdUWW U W| ≤ M) :
    Tendsto (fun a : ℝ =>
        8 * a * (-(1 / 2) * ψ 0 0
          + a * ∫ U in Ioi (0:ℝ), ∫ W in Ioi (0:ℝ), f2D (a * U * W) * ψ U W))
      atTop (𝓝 (-4 * pdUW 0 0)) := by
  have hcorner := corner_kernel_limit pdUW pdUWW hpdUWc hpdUWWc hd3 hpdUWWcs M B hB hM
    hpdUWsW hpdUWWsW
  have h8 := hcorner.const_mul (8 : ℝ)
  rw [show (8 : ℝ) * (-(1 / 2) * pdUW 0 0) = -4 * pdUW 0 0 from by ring] at h8
  apply h8.congr
  intro a
  rw [operator_ibp_identity ψ pdW pdUW hψc hpdWc hpdUWc hd1 hd2 hpdWcs hpdUWcs
    a A B hA hB hψsW hpdWsU hpdWsW hpdUWsU]
  ring

/-! ## The dictionary (sign and `c₀` conventions) -/

/-- **Null↔Cartesian dictionary on the separable class.**  For `φ(t,x) = F(t) + G(x)`
the null pullback `ψ(U,W) = φ(−(U+W)/2, (U−W)/2)` has

    ∂_Wψ = −½F' − ½G'   and   ∂_U∂_Wψ = ¼F'' − ¼G'',

so the operator limit `−4∂_U∂_Wψ(0,0) = G''(0) − F''(0) = (∂_x² − ∂_t²)φ(0) = □φ(0)`
in mostly-plus signature — the exact sign and normalization conventions.  (The general
`C²` case is the standard two-variable chain rule, not formalized here.) -/
theorem dictionary_separable (F F' F'' G G' G'' : ℝ → ℝ)
    (hF : ∀ t, HasDerivAt F (F' t) t) (hF' : ∀ t, HasDerivAt F' (F'' t) t)
    (hG : ∀ x, HasDerivAt G (G' x) x) (hG' : ∀ x, HasDerivAt G' (G'' x) x) :
    (∀ U W, HasDerivAt (fun w => F (-(U + w) / 2) + G ((U - w) / 2))
        (-(1 / 2) * F' (-(U + W) / 2) - (1 / 2) * G' ((U - W) / 2)) W)
    ∧ (∀ U W, HasDerivAt (fun u => -(1 / 2) * F' (-(u + W) / 2) - (1 / 2) * G' ((u - W) / 2))
        ((1 / 4) * F'' (-(U + W) / 2) - (1 / 4) * G'' ((U - W) / 2)) U) := by
  constructor
  · intro U W
    have hin1 : HasDerivAt (fun w : ℝ => -(U + w) / 2) (-(1 / 2)) W := by
      have := (((hasDerivAt_id W).const_add U).neg).div_const 2
      convert this using 1
      norm_num
    have hin2 : HasDerivAt (fun w : ℝ => (U - w) / 2) (-(1 / 2)) W := by
      have := ((hasDerivAt_id W).const_sub U).div_const 2
      convert this using 1
      norm_num
    have h1 := (hF (-(U + W) / 2)).comp W hin1
    have h2 := (hG ((U - W) / 2)).comp W hin2
    convert h1.add h2 using 1
    ring
  · intro U W
    have hin1 : HasDerivAt (fun u : ℝ => -(u + W) / 2) (-(1 / 2)) U := by
      have := (((hasDerivAt_id U).add_const W).neg).div_const 2
      convert this using 1
      norm_num
    have hin2 : HasDerivAt (fun u : ℝ => (u - W) / 2) ((1 : ℝ) / 2) U := by
      have := ((hasDerivAt_id U).sub_const W).div_const 2
      convert this using 1
    have h1 := ((hF' (-(U + W) / 2)).comp U hin1).const_mul (-(1 / 2) : ℝ)
    have h2 := ((hG' ((U - W) / 2)).comp U hin2).const_mul ((1 / 2) : ℝ)
    convert h1.sub h2 using 1
    ring

/-- The dictionary value at the origin: `−4·(¼F''(0) − ¼G''(0)) = G''(0) − F''(0)`,
i.e. the operator limit is `(∂_x² − ∂_t²)φ(0) = □φ(0)` (mostly-plus). -/
theorem dictionary_value (F'' G'' : ℝ → ℝ) :
    -4 * ((1 / 4) * F'' (-(0 + 0) / 2) - (1 / 4) * G'' ((0 - 0) / 2)) = G'' 0 - F'' 0 := by
  have h1 : (-(0 + 0) : ℝ) / 2 = 0 := by norm_num
  have h2 : ((0 - 0 : ℝ)) / 2 = 0 := by norm_num
  rw [h1, h2]
  ring

#print axioms Hkern_zero
#print axioms opker_deriv_W
#print axioms opker_deriv_U
#print axioms op_rect_ibp_W
#print axioms op_rect_ibp_U
#print axioms op_marginal_integrable
#print axioms operator_ibp_identity
#print axioms bdg_2d_operator_limit
#print axioms dictionary_separable
#print axioms dictionary_value

end UnifiedTheory.Audit.KFCausalMinkowski2DOperator
