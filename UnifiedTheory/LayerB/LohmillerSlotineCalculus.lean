/-
  LayerB/LohmillerSlotineCalculus.lean — Mathlib calculus hookup for
  LohmillerSlotineBridge.

  CLOSES the `LSBridgeComponent.calculusHookup` pending component
  pre-registered in LohmillerSlotineBridge.

  Connects the ABSTRACT `WaveData` scalars (r, s, r_t, r_x, r_xx,
  s_t, s_x, s_xx, …) of LohmillerSlotineBridge to ACTUAL Mathlib
  partial derivatives of smooth functions r, s : ℝ × ℝ → ℝ.

  Strategy:
    1. `SmoothWaveField` bundles smooth r, s, V plus m, ħ positivity.
    2. `partialT`, `partialX`, `partialXX` are Mathlib `deriv` applied
       to the partial-functions x ↦ f(x, t) / t ↦ f(x, t).
    3. `WaveData.atPoint` extracts a pointwise `WaveData` snapshot.
    4. `psi` is the complex L-S wavefunction ψ = r·(cos s + i sin s).
    5. Headline lemmas express ∂_t (ψ.re), ∂_t (ψ.im), ∂_x (ψ.re),
       ∂_x (ψ.im), ∂_x² (ψ.re), ∂_x² (ψ.im) via Mathlib `HasDerivAt`
       calculus and the standard product/chain rules — these are the
       calculus identities that the abstract WaveData scalars were
       always supposed to represent.
    6. Bridge theorem: pointwise Schrödinger PDE residual (real and
       imaginary parts) coincide with LohmillerSlotineBridge's
       schrodResidualReal · cos s − schrodResidualImag · sin s  and
       schrodResidualReal · sin s + schrodResidualImag · cos s,
       so PDE residual = 0 ↔ HamiltonJacobiWithBohm ∧ ContinuityEquation
       at the point.

  Zero sorry.  Zero custom axioms (beyond `propext`, `Classical.choice`,
  `Quot.sound` standard).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.Order.OrderClosedExtr
import UnifiedTheory.LayerB.LohmillerSlotineBridge

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.LohmillerSlotineCalculus

open UnifiedTheory.LayerB.LohmillerSlotineBridge
open scoped Topology

/-! ════════════════════════════════════════════════════════════════════════
    PART 1 — SMOOTH WAVE FIELD AND POINTWISE PARTIAL DERIVATIVES
    ════════════════════════════════════════════════════════════════════════ -/

/-- A smooth wave field on 1+1-dimensional spacetime:
      r(x, t) : real-valued amplitude factor (interpreted as √ρ)
      s(x, t) : real-valued phase factor   (interpreted as φ/ħ)
      V(x, t) : real-valued potential
      m, hbar : positive constants. -/
structure SmoothWaveField where
  r : ℝ → ℝ → ℝ
  s : ℝ → ℝ → ℝ
  V : ℝ → ℝ → ℝ
  m : ℝ
  hbar : ℝ
  m_pos : 0 < m
  hbar_pos : 0 < hbar

namespace SmoothWaveField

/-- Time partial derivative of an (x, t)-function at point (x, t):
      (∂_t f)(x, t) := d/dτ f(x, τ) |_{τ = t}. -/
noncomputable def partialT (f : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  deriv (fun τ => f x τ) t

/-- Spatial partial derivative:
      (∂_x f)(x, t) := d/dξ f(ξ, t) |_{ξ = x}. -/
noncomputable def partialX (f : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  deriv (fun ξ => f ξ t) x

/-- Second spatial partial derivative:
      (∂_x² f)(x, t) := d/dξ (∂_x f)(ξ, t) |_{ξ = x}. -/
noncomputable def partialXX (f : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  deriv (fun ξ => partialX f ξ t) x

end SmoothWaveField

/-- The L-S complex wavefunction  ψ(x, t) = r(x, t) · (cos s + i sin s). -/
noncomputable def psi (sw : SmoothWaveField) (x t : ℝ) : ℂ :=
  ⟨sw.r x t * Real.cos (sw.s x t), sw.r x t * Real.sin (sw.s x t)⟩

/-- Real part of ψ at a point. -/
noncomputable def psiRe (sw : SmoothWaveField) (x t : ℝ) : ℝ :=
  sw.r x t * Real.cos (sw.s x t)

/-- Imaginary part of ψ at a point. -/
noncomputable def psiIm (sw : SmoothWaveField) (x t : ℝ) : ℝ :=
  sw.r x t * Real.sin (sw.s x t)

theorem psi_re_eq (sw : SmoothWaveField) (x t : ℝ) :
    (psi sw x t).re = psiRe sw x t := rfl

theorem psi_im_eq (sw : SmoothWaveField) (x t : ℝ) :
    (psi sw x t).im = psiIm sw x t := rfl

/-- Pointwise `WaveData` snapshot at (x, t). -/
noncomputable def WaveData.atPoint (sw : SmoothWaveField) (x t : ℝ) :
    LohmillerSlotineBridge.WaveData where
  r := sw.r x t
  s := sw.s x t
  r_t := SmoothWaveField.partialT sw.r x t
  s_t := SmoothWaveField.partialT sw.s x t
  r_x := SmoothWaveField.partialX sw.r x t
  s_x := SmoothWaveField.partialX sw.s x t
  r_xx := SmoothWaveField.partialXX sw.r x t
  s_xx := SmoothWaveField.partialXX sw.s x t
  V := sw.V x t
  m := sw.m
  hbar := sw.hbar
  m_pos := sw.m_pos
  hbar_pos := sw.hbar_pos

/-! ════════════════════════════════════════════════════════════════════════
    PART 2 — TIME DERIVATIVES OF ψ.re AND ψ.im VIA CHAIN/PRODUCT RULE

    The standard product+chain rule expansion of ψ = r·(cos s + i sin s):

      ∂_t ψ.re = ∂_t r · cos s − r · sin s · ∂_t s
      ∂_t ψ.im = ∂_t r · sin s + r · cos s · ∂_t s

    Proved via Mathlib's `HasDerivAt.mul`, `HasDerivAt.cos`,
    `HasDerivAt.sin`.  Hypotheses:  r and s differentiable in t at the
    point.
    ════════════════════════════════════════════════════════════════════════ -/

variable (sw : SmoothWaveField) (x t : ℝ)

/-- The "x-fixed" t-curves of r and s. -/
local notation "rT" => fun τ => sw.r x τ
local notation "sT" => fun τ => sw.s x τ

/-- Time-derivative of ψ.re via product + chain rule.
    Hypotheses: r, s differentiable in t at the point. -/
theorem deriv_psiRe_t
    (hr : DifferentiableAt ℝ (fun τ => sw.r x τ) t)
    (hs : DifferentiableAt ℝ (fun τ => sw.s x τ) t) :
    deriv (fun τ => psiRe sw x τ) t =
      SmoothWaveField.partialT sw.r x t * Real.cos (sw.s x t)
        - sw.r x t * Real.sin (sw.s x t)
            * SmoothWaveField.partialT sw.s x t := by
  -- Decompose: ψ.re = (r at x as function of τ) * (cos ∘ (s at x as function of τ))
  have hr' : HasDerivAt (fun τ => sw.r x τ)
      (SmoothWaveField.partialT sw.r x t) t := hr.hasDerivAt
  have hs' : HasDerivAt (fun τ => sw.s x τ)
      (SmoothWaveField.partialT sw.s x t) t := hs.hasDerivAt
  have hcos : HasDerivAt (fun τ => Real.cos (sw.s x τ))
      (-Real.sin (sw.s x t) * SmoothWaveField.partialT sw.s x t) t :=
    hs'.cos
  have hmul : HasDerivAt (fun τ => sw.r x τ * Real.cos (sw.s x τ))
      (SmoothWaveField.partialT sw.r x t * Real.cos (sw.s x t)
        + sw.r x t * (-Real.sin (sw.s x t)
            * SmoothWaveField.partialT sw.s x t)) t :=
    hr'.mul hcos
  -- Conclude via .deriv
  have := hmul.deriv
  -- Rearrange algebraically:  a + b·(-c·d) = a − b·c·d
  rw [show
    SmoothWaveField.partialT sw.r x t * Real.cos (sw.s x t)
      + sw.r x t * (-Real.sin (sw.s x t)
          * SmoothWaveField.partialT sw.s x t)
    = SmoothWaveField.partialT sw.r x t * Real.cos (sw.s x t)
        - sw.r x t * Real.sin (sw.s x t)
            * SmoothWaveField.partialT sw.s x t from by ring] at this
  -- The deriv of ψ.re unfolds to the deriv of r · cos(s)
  change deriv (fun τ => sw.r x τ * Real.cos (sw.s x τ)) t = _
  exact this

/-- Time-derivative of ψ.im via product + chain rule. -/
theorem deriv_psiIm_t
    (hr : DifferentiableAt ℝ (fun τ => sw.r x τ) t)
    (hs : DifferentiableAt ℝ (fun τ => sw.s x τ) t) :
    deriv (fun τ => psiIm sw x τ) t =
      SmoothWaveField.partialT sw.r x t * Real.sin (sw.s x t)
        + sw.r x t * Real.cos (sw.s x t)
            * SmoothWaveField.partialT sw.s x t := by
  have hr' : HasDerivAt (fun τ => sw.r x τ)
      (SmoothWaveField.partialT sw.r x t) t := hr.hasDerivAt
  have hs' : HasDerivAt (fun τ => sw.s x τ)
      (SmoothWaveField.partialT sw.s x t) t := hs.hasDerivAt
  have hsin : HasDerivAt (fun τ => Real.sin (sw.s x τ))
      (Real.cos (sw.s x t) * SmoothWaveField.partialT sw.s x t) t :=
    hs'.sin
  have hmul : HasDerivAt (fun τ => sw.r x τ * Real.sin (sw.s x τ))
      (SmoothWaveField.partialT sw.r x t * Real.sin (sw.s x t)
        + sw.r x t * (Real.cos (sw.s x t)
            * SmoothWaveField.partialT sw.s x t)) t :=
    hr'.mul hsin
  have := hmul.deriv
  rw [show
    SmoothWaveField.partialT sw.r x t * Real.sin (sw.s x t)
      + sw.r x t * (Real.cos (sw.s x t)
          * SmoothWaveField.partialT sw.s x t)
    = SmoothWaveField.partialT sw.r x t * Real.sin (sw.s x t)
        + sw.r x t * Real.cos (sw.s x t)
            * SmoothWaveField.partialT sw.s x t from by ring] at this
  change deriv (fun τ => sw.r x τ * Real.sin (sw.s x τ)) t = _
  exact this

/-! ════════════════════════════════════════════════════════════════════════
    PART 3 — FIRST SPATIAL DERIVATIVES OF ψ.re AND ψ.im

    Analogous to Part 2 but for ∂_x instead of ∂_t.  Same chain/product
    rule structure, with x in place of t.  Hypotheses:  r and s
    differentiable in x at the point (with t fixed).
    ════════════════════════════════════════════════════════════════════════ -/

/-- Spatial-derivative of ψ.re via product + chain rule. -/
theorem deriv_psiRe_x
    (hr : DifferentiableAt ℝ (fun ξ => sw.r ξ t) x)
    (hs : DifferentiableAt ℝ (fun ξ => sw.s ξ t) x) :
    deriv (fun ξ => psiRe sw ξ t) x =
      SmoothWaveField.partialX sw.r x t * Real.cos (sw.s x t)
        - sw.r x t * Real.sin (sw.s x t)
            * SmoothWaveField.partialX sw.s x t := by
  have hr' : HasDerivAt (fun ξ => sw.r ξ t)
      (SmoothWaveField.partialX sw.r x t) x := hr.hasDerivAt
  have hs' : HasDerivAt (fun ξ => sw.s ξ t)
      (SmoothWaveField.partialX sw.s x t) x := hs.hasDerivAt
  have hcos : HasDerivAt (fun ξ => Real.cos (sw.s ξ t))
      (-Real.sin (sw.s x t) * SmoothWaveField.partialX sw.s x t) x :=
    hs'.cos
  have hmul : HasDerivAt (fun ξ => sw.r ξ t * Real.cos (sw.s ξ t))
      (SmoothWaveField.partialX sw.r x t * Real.cos (sw.s x t)
        + sw.r x t * (-Real.sin (sw.s x t)
            * SmoothWaveField.partialX sw.s x t)) x :=
    hr'.mul hcos
  have := hmul.deriv
  rw [show
    SmoothWaveField.partialX sw.r x t * Real.cos (sw.s x t)
      + sw.r x t * (-Real.sin (sw.s x t)
          * SmoothWaveField.partialX sw.s x t)
    = SmoothWaveField.partialX sw.r x t * Real.cos (sw.s x t)
        - sw.r x t * Real.sin (sw.s x t)
            * SmoothWaveField.partialX sw.s x t from by ring] at this
  change deriv (fun ξ => sw.r ξ t * Real.cos (sw.s ξ t)) x = _
  exact this

/-- Spatial-derivative of ψ.im via product + chain rule. -/
theorem deriv_psiIm_x
    (hr : DifferentiableAt ℝ (fun ξ => sw.r ξ t) x)
    (hs : DifferentiableAt ℝ (fun ξ => sw.s ξ t) x) :
    deriv (fun ξ => psiIm sw ξ t) x =
      SmoothWaveField.partialX sw.r x t * Real.sin (sw.s x t)
        + sw.r x t * Real.cos (sw.s x t)
            * SmoothWaveField.partialX sw.s x t := by
  have hr' : HasDerivAt (fun ξ => sw.r ξ t)
      (SmoothWaveField.partialX sw.r x t) x := hr.hasDerivAt
  have hs' : HasDerivAt (fun ξ => sw.s ξ t)
      (SmoothWaveField.partialX sw.s x t) x := hs.hasDerivAt
  have hsin : HasDerivAt (fun ξ => Real.sin (sw.s ξ t))
      (Real.cos (sw.s x t) * SmoothWaveField.partialX sw.s x t) x :=
    hs'.sin
  have hmul : HasDerivAt (fun ξ => sw.r ξ t * Real.sin (sw.s ξ t))
      (SmoothWaveField.partialX sw.r x t * Real.sin (sw.s x t)
        + sw.r x t * (Real.cos (sw.s x t)
            * SmoothWaveField.partialX sw.s x t)) x :=
    hr'.mul hsin
  have := hmul.deriv
  rw [show
    SmoothWaveField.partialX sw.r x t * Real.sin (sw.s x t)
      + sw.r x t * (Real.cos (sw.s x t)
          * SmoothWaveField.partialX sw.s x t)
    = SmoothWaveField.partialX sw.r x t * Real.sin (sw.s x t)
        + sw.r x t * Real.cos (sw.s x t)
            * SmoothWaveField.partialX sw.s x t from by ring] at this
  change deriv (fun ξ => sw.r ξ t * Real.sin (sw.s ξ t)) x = _
  exact this

/-! ════════════════════════════════════════════════════════════════════════
    PART 4 — POINTWISE SCHRÖDINGER PDE  ↔  ALGEBRAIC HJ + CONTINUITY

    Substituting the chain-rule expansions into the Schrödinger PDE
    residual at (x, t):

        Re(iħ ∂_t ψ + (ħ²/2m) ∂_x² ψ − V ψ)
          = schrodResidualReal · cos s − schrodResidualImag · sin s
        Im(iħ ∂_t ψ + (ħ²/2m) ∂_x² ψ − V ψ)
          = schrodResidualReal · sin s + schrodResidualImag · cos s

    The 2×2 rotation matrix is invertible (det = 1), so the PDE
    residual vanishes iff the algebraic schrodResiduals do — and by
    `schrodinger_satisfied_iff` (LohmillerSlotineBridge) iff
    `HamiltonJacobiWithBohm` ∧ `ContinuityEquation` hold pointwise.
    ════════════════════════════════════════════════════════════════════════ -/

/-- Bundles the four standard chain-rule expansions of ∂_t ψ and
    ∂_x² ψ at a point.  These are CONCLUSIONS of standard Mathlib
    calculus on smooth (r, s).  The `_t` expansions are discharged
    by `deriv_psiRe_t` and `deriv_psiIm_t` (Part 2).  The `_xx`
    expansions are the same chain-rule pattern iterated one more time. -/
structure ChainRuleExpansions (sw : SmoothWaveField) (x t : ℝ) : Prop where
  /-- ∂_t Re(ψ) = r_t · cos s − r · sin s · s_t. -/
  partialT_psiRe :
    deriv (fun τ => psiRe sw x τ) t =
      SmoothWaveField.partialT sw.r x t * Real.cos (sw.s x t)
        - sw.r x t * Real.sin (sw.s x t)
            * SmoothWaveField.partialT sw.s x t
  /-- ∂_t Im(ψ) = r_t · sin s + r · cos s · s_t. -/
  partialT_psiIm :
    deriv (fun τ => psiIm sw x τ) t =
      SmoothWaveField.partialT sw.r x t * Real.sin (sw.s x t)
        + sw.r x t * Real.cos (sw.s x t)
            * SmoothWaveField.partialT sw.s x t
  /-- ∂_x² Re(ψ) = (r_xx − r·s_x²)·cos s − (2·r_x·s_x + r·s_xx)·sin s. -/
  partialXX_psiRe :
    SmoothWaveField.partialXX (fun ξ τ => psiRe sw ξ τ) x t =
      (SmoothWaveField.partialXX sw.r x t
        - sw.r x t * SmoothWaveField.partialX sw.s x t ^ 2)
          * Real.cos (sw.s x t)
        - (2 * SmoothWaveField.partialX sw.r x t
            * SmoothWaveField.partialX sw.s x t
          + sw.r x t * SmoothWaveField.partialXX sw.s x t)
            * Real.sin (sw.s x t)
  /-- ∂_x² Im(ψ) = (r_xx − r·s_x²)·sin s + (2·r_x·s_x + r·s_xx)·cos s. -/
  partialXX_psiIm :
    SmoothWaveField.partialXX (fun ξ τ => psiIm sw ξ τ) x t =
      (SmoothWaveField.partialXX sw.r x t
        - sw.r x t * SmoothWaveField.partialX sw.s x t ^ 2)
          * Real.sin (sw.s x t)
        + (2 * SmoothWaveField.partialX sw.r x t
            * SmoothWaveField.partialX sw.s x t
          + sw.r x t * SmoothWaveField.partialXX sw.s x t)
            * Real.cos (sw.s x t)

/-- The real part of the Schrödinger PDE residual at (x, t),
    using the chain-rule expansions of partial derivatives. -/
noncomputable def PDE_residualRe (sw : SmoothWaveField) (x t : ℝ) : ℝ :=
  -sw.hbar * deriv (fun τ => psiIm sw x τ) t
    + (sw.hbar ^ 2 / (2 * sw.m))
        * SmoothWaveField.partialXX (fun ξ τ => psiRe sw ξ τ) x t
    - sw.V x t * psiRe sw x t

/-- The imag part of the Schrödinger PDE residual at (x, t). -/
noncomputable def PDE_residualIm (sw : SmoothWaveField) (x t : ℝ) : ℝ :=
  sw.hbar * deriv (fun τ => psiRe sw x τ) t
    + (sw.hbar ^ 2 / (2 * sw.m))
        * SmoothWaveField.partialXX (fun ξ τ => psiIm sw ξ τ) x t
    - sw.V x t * psiIm sw x t

/-- **Algebraic decomposition of the PDE residual.**

    Given the chain-rule expansions (bundled in `ChainRuleExpansions`),
    the real and imaginary parts of the Schrödinger PDE residual at
    (x, t) decompose via the polar rotation matrix:

      PDE_residualRe = schrodResidualReal · cos s − schrodResidualImag · sin s
      PDE_residualIm = schrodResidualReal · sin s + schrodResidualImag · cos s

    where the schrodResiduals are evaluated on `WaveData.atPoint sw x t`. -/
theorem PDE_residual_decomp (sw : SmoothWaveField) (x t : ℝ)
    (h : ChainRuleExpansions sw x t) :
    PDE_residualRe sw x t =
      schrodResidualReal (WaveData.atPoint sw x t) * Real.cos (sw.s x t)
        - schrodResidualImag (WaveData.atPoint sw x t) * Real.sin (sw.s x t)
    ∧ PDE_residualIm sw x t =
      schrodResidualReal (WaveData.atPoint sw x t) * Real.sin (sw.s x t)
        + schrodResidualImag (WaveData.atPoint sw x t) * Real.cos (sw.s x t) := by
  simp only [PDE_residualRe, PDE_residualIm]
  rw [h.partialT_psiRe, h.partialT_psiIm, h.partialXX_psiRe, h.partialXX_psiIm]
  simp only [psiRe, psiIm, schrodResidualReal, schrodResidualImag,
    WaveData.atPoint]
  refine ⟨?_, ?_⟩ <;> ring

/-- Algebraic lemma: a 2×2 rotation matrix is invertible, so
    (a cos s − b sin s = 0 ∧ a sin s + b cos s = 0) ↔ (a = 0 ∧ b = 0). -/
theorem rotation_matrix_invertible (a b s : ℝ) :
    (a * Real.cos s - b * Real.sin s = 0
      ∧ a * Real.sin s + b * Real.cos s = 0)
    ↔ (a = 0 ∧ b = 0) := by
  have hcs : Real.cos s ^ 2 + Real.sin s ^ 2 = 1 := by
    linear_combination Real.sin_sq_add_cos_sq s
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · -- Combine: cos s · h1 + sin s · h2  gives  a · (cos² + sin²) = 0  hence a = 0
      have key : a * (Real.cos s ^ 2 + Real.sin s ^ 2) = 0 := by
        linear_combination Real.cos s * h1 + Real.sin s * h2
      rw [hcs, mul_one] at key
      exact key
    · -- Combine: -sin s · h1 + cos s · h2  gives  b · (cos² + sin²) = 0  hence b = 0
      have key : b * (Real.cos s ^ 2 + Real.sin s ^ 2) = 0 := by
        linear_combination -Real.sin s * h1 + Real.cos s * h2
      rw [hcs, mul_one] at key
      exact key
  · rintro ⟨ha, hb⟩
    rw [ha, hb]; refine ⟨by ring, by ring⟩

/-- **HEADLINE THEOREM (calculusHookup closure)**.

    Under the chain-rule expansions (`ChainRuleExpansions`), the
    pointwise Schrödinger PDE residual vanishes IFF the algebraic
    Hamilton-Jacobi-with-Bohm and continuity equations hold at the
    point.

    This is the bridge from the abstract WaveData algebra of
    LohmillerSlotineBridge to actual partial derivatives of smooth
    (r, s) fields.  Combined with `deriv_psiRe_t`, `deriv_psiIm_t`,
    `deriv_psiRe_x`, `deriv_psiIm_x` (Parts 2 + 3) and the analogous
    `_xx` lemmas (same chain-rule pattern iterated), this realizes
    the `calculusHookup` component as a Mathlib-calculus theorem. -/
theorem schrodinger_PDE_iff_HJ_continuity (sw : SmoothWaveField) (x t : ℝ)
    (h : ChainRuleExpansions sw x t) :
    (PDE_residualRe sw x t = 0 ∧ PDE_residualIm sw x t = 0)
    ↔ (HamiltonJacobiWithBohm (WaveData.atPoint sw x t)
        ∧ ContinuityEquation (WaveData.atPoint sw x t)) := by
  obtain ⟨hRe, hIm⟩ := PDE_residual_decomp sw x t h
  rw [hRe, hIm, rotation_matrix_invertible,
      ← residualReal_iff_HJ, ← residualImag_iff_continuity]

/-! ════════════════════════════════════════════════════════════════════════
    PART 5 — DISCHARGING ChainRuleExpansions FROM SMOOTHNESS

    The `_xx` clauses of `ChainRuleExpansions` are the spatial-second-
    derivative chain-rule identities for ψ.re = r·cos(s) and ψ.im =
    r·sin(s).  These can be discharged from standard differentiability
    hypotheses on r and s (and their first spatial partials).
    ════════════════════════════════════════════════════════════════════════ -/

/-- Function-extensionality lemma: under r, s differentiable everywhere
    in ξ, the function ξ ↦ ∂_x (r·cos s)(ξ, t) is the chain-rule
    expression as a function of ξ. -/
theorem partialX_psiRe_funext (sw : SmoothWaveField) (t : ℝ)
    (hr : Differentiable ℝ (fun ξ => sw.r ξ t))
    (hs : Differentiable ℝ (fun ξ => sw.s ξ t)) :
    (fun ξ => SmoothWaveField.partialX
        (fun ξ' τ => sw.r ξ' τ * Real.cos (sw.s ξ' τ)) ξ t)
    = (fun ξ => SmoothWaveField.partialX sw.r ξ t * Real.cos (sw.s ξ t)
                - sw.r ξ t * Real.sin (sw.s ξ t)
                    * SmoothWaveField.partialX sw.s ξ t) := by
  funext ξ
  exact deriv_psiRe_x sw ξ t (hr ξ) (hs ξ)

/-- Similar for ψ.im = r · sin(s). -/
theorem partialX_psiIm_funext (sw : SmoothWaveField) (t : ℝ)
    (hr : Differentiable ℝ (fun ξ => sw.r ξ t))
    (hs : Differentiable ℝ (fun ξ => sw.s ξ t)) :
    (fun ξ => SmoothWaveField.partialX
        (fun ξ' τ => sw.r ξ' τ * Real.sin (sw.s ξ' τ)) ξ t)
    = (fun ξ => SmoothWaveField.partialX sw.r ξ t * Real.sin (sw.s ξ t)
                + sw.r ξ t * Real.cos (sw.s ξ t)
                    * SmoothWaveField.partialX sw.s ξ t) := by
  funext ξ
  exact deriv_psiIm_x sw ξ t (hr ξ) (hs ξ)

/-- ∂_x²(r·cos s) via iterated chain/product rule. -/
theorem partialXX_psiRe_eq (sw : SmoothWaveField) (x t : ℝ)
    (hr : Differentiable ℝ (fun ξ => sw.r ξ t))
    (hs : Differentiable ℝ (fun ξ => sw.s ξ t))
    (hr_x : Differentiable ℝ (fun ξ => SmoothWaveField.partialX sw.r ξ t))
    (hs_x : Differentiable ℝ (fun ξ => SmoothWaveField.partialX sw.s ξ t)) :
    SmoothWaveField.partialXX
        (fun ξ τ => sw.r ξ τ * Real.cos (sw.s ξ τ)) x t =
      (SmoothWaveField.partialXX sw.r x t
        - sw.r x t * SmoothWaveField.partialX sw.s x t ^ 2)
          * Real.cos (sw.s x t)
      - (2 * SmoothWaveField.partialX sw.r x t
            * SmoothWaveField.partialX sw.s x t
          + sw.r x t * SmoothWaveField.partialXX sw.s x t)
          * Real.sin (sw.s x t) := by
  -- partialXX f x t = deriv (ξ ↦ partialX f ξ t) x
  unfold SmoothWaveField.partialXX
  -- Rewrite the inner partialX as the chain-rule expression
  rw [partialX_psiRe_funext sw t hr hs]
  -- Now compute deriv of the chain-rule expression via HasDerivAt machinery
  have hr_at : HasDerivAt (fun ξ => sw.r ξ t)
      (SmoothWaveField.partialX sw.r x t) x := (hr x).hasDerivAt
  have hs_at : HasDerivAt (fun ξ => sw.s ξ t)
      (SmoothWaveField.partialX sw.s x t) x := (hs x).hasDerivAt
  have hr_x_at : HasDerivAt (fun ξ => SmoothWaveField.partialX sw.r ξ t)
      (deriv (fun ξ => SmoothWaveField.partialX sw.r ξ t) x) x :=
    (hr_x x).hasDerivAt
  have hs_x_at : HasDerivAt (fun ξ => SmoothWaveField.partialX sw.s ξ t)
      (deriv (fun ξ => SmoothWaveField.partialX sw.s ξ t) x) x :=
    (hs_x x).hasDerivAt
  have h_cos := hs_at.cos
  have h_sin := hs_at.sin
  have h_term1 := hr_x_at.mul h_cos      -- (r_x · cos s)'
  have h_rsin := hr_at.mul h_sin         -- (r · sin s)'
  have h_term2 := h_rsin.mul hs_x_at     -- (r · sin s · s_x)'
  have h_diff := h_term1.sub h_term2
  have hd := h_diff.deriv
  simp only [Pi.mul_apply] at hd
  linear_combination hd

/-- ∂_x²(r·sin s) via iterated chain/product rule. -/
theorem partialXX_psiIm_eq (sw : SmoothWaveField) (x t : ℝ)
    (hr : Differentiable ℝ (fun ξ => sw.r ξ t))
    (hs : Differentiable ℝ (fun ξ => sw.s ξ t))
    (hr_x : Differentiable ℝ (fun ξ => SmoothWaveField.partialX sw.r ξ t))
    (hs_x : Differentiable ℝ (fun ξ => SmoothWaveField.partialX sw.s ξ t)) :
    SmoothWaveField.partialXX
        (fun ξ τ => sw.r ξ τ * Real.sin (sw.s ξ τ)) x t =
      (SmoothWaveField.partialXX sw.r x t
        - sw.r x t * SmoothWaveField.partialX sw.s x t ^ 2)
          * Real.sin (sw.s x t)
      + (2 * SmoothWaveField.partialX sw.r x t
            * SmoothWaveField.partialX sw.s x t
          + sw.r x t * SmoothWaveField.partialXX sw.s x t)
          * Real.cos (sw.s x t) := by
  unfold SmoothWaveField.partialXX
  rw [partialX_psiIm_funext sw t hr hs]
  have hr_at : HasDerivAt (fun ξ => sw.r ξ t)
      (SmoothWaveField.partialX sw.r x t) x := (hr x).hasDerivAt
  have hs_at : HasDerivAt (fun ξ => sw.s ξ t)
      (SmoothWaveField.partialX sw.s x t) x := (hs x).hasDerivAt
  have hr_x_at : HasDerivAt (fun ξ => SmoothWaveField.partialX sw.r ξ t)
      (deriv (fun ξ => SmoothWaveField.partialX sw.r ξ t) x) x :=
    (hr_x x).hasDerivAt
  have hs_x_at : HasDerivAt (fun ξ => SmoothWaveField.partialX sw.s ξ t)
      (deriv (fun ξ => SmoothWaveField.partialX sw.s ξ t) x) x :=
    (hs_x x).hasDerivAt
  have h_cos := hs_at.cos
  have h_sin := hs_at.sin
  have h_term1 := hr_x_at.mul h_sin      -- (r_x · sin s)'
  have h_rcos := hr_at.mul h_cos         -- (r · cos s)'
  have h_term2 := h_rcos.mul hs_x_at     -- (r · cos s · s_x)'
  have h_sum := h_term1.add h_term2
  have hd := h_sum.deriv
  simp only [Pi.mul_apply] at hd
  linear_combination hd

/-! ════════════════════════════════════════════════════════════════════════
    PART 6 — `SmoothEnough` BUNDLE AND FULLY SELF-CONTAINED HEADLINE
    ════════════════════════════════════════════════════════════════════════ -/

/-- Bundle of standard differentiability hypotheses sufficient to
    discharge `ChainRuleExpansions` at (x, t). -/
structure SmoothEnough (sw : SmoothWaveField) (x t : ℝ) : Prop where
  /-- r is differentiable in t at (x, t). -/
  hr_t : DifferentiableAt ℝ (fun τ => sw.r x τ) t
  /-- s is differentiable in t at (x, t). -/
  hs_t : DifferentiableAt ℝ (fun τ => sw.s x τ) t
  /-- r is differentiable in x everywhere (at this t). -/
  hr_x : Differentiable ℝ (fun ξ => sw.r ξ t)
  /-- s is differentiable in x everywhere (at this t). -/
  hs_x : Differentiable ℝ (fun ξ => sw.s ξ t)
  /-- ∂_x r is differentiable in x everywhere (at this t). -/
  hr_xx : Differentiable ℝ (fun ξ => SmoothWaveField.partialX sw.r ξ t)
  /-- ∂_x s is differentiable in x everywhere (at this t). -/
  hs_xx : Differentiable ℝ (fun ξ => SmoothWaveField.partialX sw.s ξ t)

/-- **Discharge `ChainRuleExpansions` from `SmoothEnough`**. -/
theorem ChainRuleExpansions.ofSmoothEnough (sw : SmoothWaveField) (x t : ℝ)
    (h : SmoothEnough sw x t) : ChainRuleExpansions sw x t where
  partialT_psiRe := deriv_psiRe_t sw x t h.hr_t h.hs_t
  partialT_psiIm := deriv_psiIm_t sw x t h.hr_t h.hs_t
  partialXX_psiRe := partialXX_psiRe_eq sw x t h.hr_x h.hs_x h.hr_xx h.hs_xx
  partialXX_psiIm := partialXX_psiIm_eq sw x t h.hr_x h.hs_x h.hr_xx h.hs_xx

/-- **HEADLINE (fully self-contained, from smoothness).**

    For a smooth wave field sufficiently differentiable at (x, t):
        pointwise Schrödinger PDE residual = 0
      ⟺
        HamiltonJacobiWithBohm + ContinuityEquation hold pointwise.

    This is the calculus-hookup endpoint:  ALL chain-rule expansions
    are discharged by Mathlib calculus on standard smoothness
    hypotheses;  the algebraic core (HJ-with-Bohm + Continuity) is
    proved in `LohmillerSlotineBridge`.  No remaining mechanical
    Mathlib calculus follow-up. -/
theorem schrodinger_PDE_iff_HJ_continuity_smooth
    (sw : SmoothWaveField) (x t : ℝ) (h : SmoothEnough sw x t) :
    (PDE_residualRe sw x t = 0 ∧ PDE_residualIm sw x t = 0)
    ↔ (HamiltonJacobiWithBohm (WaveData.atPoint sw x t)
        ∧ ContinuityEquation (WaveData.atPoint sw x t)) :=
  schrodinger_PDE_iff_HJ_continuity sw x t
    (ChainRuleExpansions.ofSmoothEnough sw x t h)

/-! ════════════════════════════════════════════════════════════════════════
    PART 6.5 — LOCAL SIBLING:  `SmoothEnoughAt` AND NODE-FRIENDLY BRIDGE

    The global `SmoothEnough` bundle requires *global* spatial
    differentiability (`Differentiable ℝ (fun ξ => sw.r ξ t)` for ALL
    ξ ∈ ℝ).  This is much stronger than what the PDE bridge at a single
    point `(x, t)` actually needs.

    Physical wave functions have nodes — points where ψ = 0 — at which
    polar coordinates degenerate.  A globally-smooth polar wave field
    that matches ψ near such a node does NOT exist.  But local polar
    coordinates DO exist on each connected component of the nonzero
    locus (proved in `LohmillerSlotineNodes.polar_on_nonzero_locus`).

    Here we add a **localized sibling stack** to the global theory:
      • `SmoothEnoughAt sw x t`  — local nbhd-based differentiability,
      • localized funext lemmas via `Filter.EventuallyEq`,
      • localized `partialXX_*_at` recovering the same pointwise identity,
      • `ChainRuleExpansions.ofSmoothEnoughAt`,
      • `schrodinger_PDE_iff_HJ_continuity_at` — node-friendly bridge.

    The original global stack is untouched.  The new local stack is a
    proper weakening, so the old API stays usable as a corollary.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Localized SmoothEnough**:  the bundle of differentiability
    hypotheses needed for the PDE bridge at a single point `(x, t)`,
    using `DifferentiableAt` and neighborhood filters (`∀ᶠ ξ in 𝓝 x`)
    instead of global `Differentiable ℝ`.

    Strictly weaker than `SmoothEnough`.  In particular, a `ContDiff ℝ 2`
    field on an OPEN nbhd of `(x, t)` discharges this — no constraint on
    the field's behavior far from `(x, t)` is required. -/
structure SmoothEnoughAt (sw : SmoothWaveField) (x t : ℝ) : Prop where
  /-- r is differentiable in t at the point. -/
  hr_t : DifferentiableAt ℝ (fun τ => sw.r x τ) t
  /-- s is differentiable in t at the point. -/
  hs_t : DifferentiableAt ℝ (fun τ => sw.s x τ) t
  /-- r is differentiable in ξ on a neighborhood of x (at this t). -/
  hr_x_nbhd : ∀ᶠ ξ in 𝓝 x, DifferentiableAt ℝ (fun ξ' => sw.r ξ' t) ξ
  /-- s is differentiable in ξ on a neighborhood of x (at this t). -/
  hs_x_nbhd : ∀ᶠ ξ in 𝓝 x, DifferentiableAt ℝ (fun ξ' => sw.s ξ' t) ξ
  /-- ∂_x r is differentiable in ξ on a neighborhood of x (at this t). -/
  hr_xx_nbhd : ∀ᶠ ξ in 𝓝 x,
    DifferentiableAt ℝ (fun ξ' => SmoothWaveField.partialX sw.r ξ' t) ξ
  /-- ∂_x s is differentiable in ξ on a neighborhood of x (at this t). -/
  hs_xx_nbhd : ∀ᶠ ξ in 𝓝 x,
    DifferentiableAt ℝ (fun ξ' => SmoothWaveField.partialX sw.s ξ' t) ξ

/-- The global `SmoothEnough` implies the localized `SmoothEnoughAt`. -/
theorem SmoothEnoughAt.of_smoothEnough
    {sw : SmoothWaveField} {x t : ℝ} (h : SmoothEnough sw x t) :
    SmoothEnoughAt sw x t where
  hr_t := h.hr_t
  hs_t := h.hs_t
  hr_x_nbhd := Filter.Eventually.of_forall (fun ξ => h.hr_x ξ)
  hs_x_nbhd := Filter.Eventually.of_forall (fun ξ => h.hs_x ξ)
  hr_xx_nbhd := Filter.Eventually.of_forall (fun ξ => h.hr_xx ξ)
  hs_xx_nbhd := Filter.Eventually.of_forall (fun ξ => h.hs_xx ξ)

/-- Localized sibling of `partialX_psiRe_funext`:  equality of
    `∂_x(r · cos s)` with the chain-rule expression holds on a
    *neighborhood* of `x` (rather than globally). -/
theorem partialX_psiRe_eventuallyEq (sw : SmoothWaveField) (x t : ℝ)
    (hr : ∀ᶠ ξ in 𝓝 x, DifferentiableAt ℝ (fun ξ' => sw.r ξ' t) ξ)
    (hs : ∀ᶠ ξ in 𝓝 x, DifferentiableAt ℝ (fun ξ' => sw.s ξ' t) ξ) :
    (fun ξ => SmoothWaveField.partialX
        (fun ξ' τ => sw.r ξ' τ * Real.cos (sw.s ξ' τ)) ξ t)
    =ᶠ[𝓝 x] (fun ξ => SmoothWaveField.partialX sw.r ξ t * Real.cos (sw.s ξ t)
                - sw.r ξ t * Real.sin (sw.s ξ t)
                    * SmoothWaveField.partialX sw.s ξ t) := by
  filter_upwards [hr, hs] with ξ hrξ hsξ
  exact deriv_psiRe_x sw ξ t hrξ hsξ

/-- Localized sibling of `partialX_psiIm_funext`. -/
theorem partialX_psiIm_eventuallyEq (sw : SmoothWaveField) (x t : ℝ)
    (hr : ∀ᶠ ξ in 𝓝 x, DifferentiableAt ℝ (fun ξ' => sw.r ξ' t) ξ)
    (hs : ∀ᶠ ξ in 𝓝 x, DifferentiableAt ℝ (fun ξ' => sw.s ξ' t) ξ) :
    (fun ξ => SmoothWaveField.partialX
        (fun ξ' τ => sw.r ξ' τ * Real.sin (sw.s ξ' τ)) ξ t)
    =ᶠ[𝓝 x] (fun ξ => SmoothWaveField.partialX sw.r ξ t * Real.sin (sw.s ξ t)
                + sw.r ξ t * Real.cos (sw.s ξ t)
                    * SmoothWaveField.partialX sw.s ξ t) := by
  filter_upwards [hr, hs] with ξ hrξ hsξ
  exact deriv_psiIm_x sw ξ t hrξ hsξ

/-- Localized sibling of `partialXX_psiRe_eq`.  The same pointwise
    identity holds under purely neighborhood-based hypotheses. -/
theorem partialXX_psiRe_at (sw : SmoothWaveField) (x t : ℝ)
    (hr : ∀ᶠ ξ in 𝓝 x, DifferentiableAt ℝ (fun ξ' => sw.r ξ' t) ξ)
    (hs : ∀ᶠ ξ in 𝓝 x, DifferentiableAt ℝ (fun ξ' => sw.s ξ' t) ξ)
    (hr_x : ∀ᶠ ξ in 𝓝 x,
      DifferentiableAt ℝ (fun ξ' => SmoothWaveField.partialX sw.r ξ' t) ξ)
    (hs_x : ∀ᶠ ξ in 𝓝 x,
      DifferentiableAt ℝ (fun ξ' => SmoothWaveField.partialX sw.s ξ' t) ξ) :
    SmoothWaveField.partialXX
        (fun ξ τ => sw.r ξ τ * Real.cos (sw.s ξ τ)) x t =
      (SmoothWaveField.partialXX sw.r x t
        - sw.r x t * SmoothWaveField.partialX sw.s x t ^ 2)
          * Real.cos (sw.s x t)
      - (2 * SmoothWaveField.partialX sw.r x t
            * SmoothWaveField.partialX sw.s x t
          + sw.r x t * SmoothWaveField.partialXX sw.s x t)
          * Real.sin (sw.s x t) := by
  unfold SmoothWaveField.partialXX
  rw [Filter.EventuallyEq.deriv_eq (partialX_psiRe_eventuallyEq sw x t hr hs)]
  -- Now the goal matches the global `partialXX_psiRe_eq` proof tail.
  have hr_at : HasDerivAt (fun ξ => sw.r ξ t)
      (SmoothWaveField.partialX sw.r x t) x := hr.self_of_nhds.hasDerivAt
  have hs_at : HasDerivAt (fun ξ => sw.s ξ t)
      (SmoothWaveField.partialX sw.s x t) x := hs.self_of_nhds.hasDerivAt
  have hr_x_at : HasDerivAt (fun ξ => SmoothWaveField.partialX sw.r ξ t)
      (deriv (fun ξ => SmoothWaveField.partialX sw.r ξ t) x) x :=
    hr_x.self_of_nhds.hasDerivAt
  have hs_x_at : HasDerivAt (fun ξ => SmoothWaveField.partialX sw.s ξ t)
      (deriv (fun ξ => SmoothWaveField.partialX sw.s ξ t) x) x :=
    hs_x.self_of_nhds.hasDerivAt
  have h_cos := hs_at.cos
  have h_sin := hs_at.sin
  have h_term1 := hr_x_at.mul h_cos
  have h_rsin := hr_at.mul h_sin
  have h_term2 := h_rsin.mul hs_x_at
  have h_diff := h_term1.sub h_term2
  have hd := h_diff.deriv
  simp only [Pi.mul_apply] at hd
  linear_combination hd

/-- Localized sibling of `partialXX_psiIm_eq`. -/
theorem partialXX_psiIm_at (sw : SmoothWaveField) (x t : ℝ)
    (hr : ∀ᶠ ξ in 𝓝 x, DifferentiableAt ℝ (fun ξ' => sw.r ξ' t) ξ)
    (hs : ∀ᶠ ξ in 𝓝 x, DifferentiableAt ℝ (fun ξ' => sw.s ξ' t) ξ)
    (hr_x : ∀ᶠ ξ in 𝓝 x,
      DifferentiableAt ℝ (fun ξ' => SmoothWaveField.partialX sw.r ξ' t) ξ)
    (hs_x : ∀ᶠ ξ in 𝓝 x,
      DifferentiableAt ℝ (fun ξ' => SmoothWaveField.partialX sw.s ξ' t) ξ) :
    SmoothWaveField.partialXX
        (fun ξ τ => sw.r ξ τ * Real.sin (sw.s ξ τ)) x t =
      (SmoothWaveField.partialXX sw.r x t
        - sw.r x t * SmoothWaveField.partialX sw.s x t ^ 2)
          * Real.sin (sw.s x t)
      + (2 * SmoothWaveField.partialX sw.r x t
            * SmoothWaveField.partialX sw.s x t
          + sw.r x t * SmoothWaveField.partialXX sw.s x t)
          * Real.cos (sw.s x t) := by
  unfold SmoothWaveField.partialXX
  rw [Filter.EventuallyEq.deriv_eq (partialX_psiIm_eventuallyEq sw x t hr hs)]
  have hr_at : HasDerivAt (fun ξ => sw.r ξ t)
      (SmoothWaveField.partialX sw.r x t) x := hr.self_of_nhds.hasDerivAt
  have hs_at : HasDerivAt (fun ξ => sw.s ξ t)
      (SmoothWaveField.partialX sw.s x t) x := hs.self_of_nhds.hasDerivAt
  have hr_x_at : HasDerivAt (fun ξ => SmoothWaveField.partialX sw.r ξ t)
      (deriv (fun ξ => SmoothWaveField.partialX sw.r ξ t) x) x :=
    hr_x.self_of_nhds.hasDerivAt
  have hs_x_at : HasDerivAt (fun ξ => SmoothWaveField.partialX sw.s ξ t)
      (deriv (fun ξ => SmoothWaveField.partialX sw.s ξ t) x) x :=
    hs_x.self_of_nhds.hasDerivAt
  have h_cos := hs_at.cos
  have h_sin := hs_at.sin
  have h_term1 := hr_x_at.mul h_sin
  have h_rcos := hr_at.mul h_cos
  have h_term2 := h_rcos.mul hs_x_at
  have h_sum := h_term1.add h_term2
  have hd := h_sum.deriv
  simp only [Pi.mul_apply] at hd
  linear_combination hd

/-- **Discharge `ChainRuleExpansions` from `SmoothEnoughAt`**.

    The localized sibling of `ChainRuleExpansions.ofSmoothEnough`.
    Produces the same pointwise chain-rule bundle from strictly weaker
    hypotheses. -/
theorem ChainRuleExpansions.ofSmoothEnoughAt
    (sw : SmoothWaveField) (x t : ℝ) (h : SmoothEnoughAt sw x t) :
    ChainRuleExpansions sw x t := by
  obtain ⟨hr_t, hs_t, hr_x_nbhd, hs_x_nbhd, hr_xx_nbhd, hs_xx_nbhd⟩ := h
  exact
    { partialT_psiRe := deriv_psiRe_t sw x t hr_t hs_t
      partialT_psiIm := deriv_psiIm_t sw x t hr_t hs_t
      partialXX_psiRe :=
        partialXX_psiRe_at sw x t hr_x_nbhd hs_x_nbhd hr_xx_nbhd hs_xx_nbhd
      partialXX_psiIm :=
        partialXX_psiIm_at sw x t hr_x_nbhd hs_x_nbhd hr_xx_nbhd hs_xx_nbhd }

/-- **NODE-FRIENDLY HEADLINE**.

    Localized form of `schrodinger_PDE_iff_HJ_continuity_smooth`.
    Consumes only nbhd-local differentiability — never assumes global
    polar regularity — so it composes directly with `polar_on_nonzero_locus`
    on the nonzero locus of an arbitrary smooth complex wave field.

    This is the right hookup target for the node-friendly LS bridge. -/
theorem schrodinger_PDE_iff_HJ_continuity_at
    (sw : SmoothWaveField) (x t : ℝ) (h : SmoothEnoughAt sw x t) :
    (PDE_residualRe sw x t = 0 ∧ PDE_residualIm sw x t = 0)
    ↔ (HamiltonJacobiWithBohm (WaveData.atPoint sw x t)
        ∧ ContinuityEquation (WaveData.atPoint sw x t)) :=
  schrodinger_PDE_iff_HJ_continuity sw x t
    (ChainRuleExpansions.ofSmoothEnoughAt sw x t h)

/-! ════════════════════════════════════════════════════════════════════════
    PART 7 — STATUS

    The calculus hookup is FULLY CLOSED:

      (a) Smooth wave field infrastructure (Part 1).
      (b) Mathlib chain-rule expansions for ∂_t Re/Im(ψ)
          and ∂_x Re/Im(ψ) (Parts 2-3).
      (c) Mathlib chain-rule expansions for ∂_x² Re/Im(ψ) (Part 5).
      (d) `SmoothEnough` bundle of standard smoothness hypotheses
          and `ChainRuleExpansions.ofSmoothEnough` discharging all
          chain-rule clauses (Part 6).
      (e) `schrodinger_PDE_iff_HJ_continuity_smooth`: pointwise PDE
          Schrödinger ⟺ HJ-with-Bohm + Continuity, taking only
          standard smoothness hypotheses as input.

    Zero sorry.  Zero custom axioms (beyond `propext`, `Classical.choice`,
    `Quot.sound` standard).

    The only remaining frontier in the LSBridge family is
    `LSBridgeComponent.continuumLimitOfKP` — the discrete poset-growth
    K/P amplitude → smooth (r, s) field bridge, separately scoped in
    LohmillerSlotineContinuumLimit.lean (per the three-sub-bridge plan).
    ════════════════════════════════════════════════════════════════════════ -/

end UnifiedTheory.LayerB.LohmillerSlotineCalculus
