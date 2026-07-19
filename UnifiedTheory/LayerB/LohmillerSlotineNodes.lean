/-
  LayerB/LohmillerSlotineNodes.lean — Node-friendly Lohmiller-Slotine bridge.

  PHASE A — KILL THE FAKE NO-NODES HYPOTHESIS.

  The headline bridge `LSBridge_PDE_equivalence_realised` proved in
  `LohmillerSlotineSubBridge1` assumes the lifted complex amplitude
  `polarZ x t = qLim x t + i · pLim x t` lies in `Complex.slitPlane` at
  every spacetime point.  That assumption is *physically false* —
  honest quantum-mechanical wave functions have nodes (points where
  `ψ = 0`), and polar coordinates degenerate there.

  This file gives the standard Madelung-Bohm local treatment:

  • The nonzero locus `{(x, t) : ψ x t ≠ 0}` is open.
  • On any small enough open neighborhood of any nonzero point, there
    exist `ContDiff` real-valued `r, s` with `ψ = r · exp(i · s)`.

  Construction (Phase A.1):  given `ψ x₀ ≠ 0`, multiply by
  `(ψ x₀)⁻¹` to send `x₀` to `1 ∈ slitPlane`.  By continuity the rotated
  field stays in `slitPlane` on an open neighborhood.  On that
  neighborhood `Complex.arg` is `ContDiff`, so we can read off a smooth
  phase representative.

  Zero sorry.  Standard axioms only.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import UnifiedTheory.LayerB.LohmillerSlotineSubBridge1

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.LohmillerSlotineNodes

open UnifiedTheory.LayerB.LohmillerSlotineSubBridge1
open UnifiedTheory.LayerB.LohmillerSlotineCalculus
open scoped Topology

/-! ════════════════════════════════════════════════════════════════════════
    PART 1 — THE NONZERO LOCUS IS OPEN
    ════════════════════════════════════════════════════════════════════════ -/

/-- The nonzero locus of a continuous complex-valued field is open. -/
theorem isOpen_nonzero_locus {α : Type*} [TopologicalSpace α]
    (ψ : α → ℂ) (hψ : Continuous ψ) :
    IsOpen {x : α | ψ x ≠ 0} := by
  have h_eq : {x | ψ x ≠ 0} = ψ ⁻¹' {(0 : ℂ)}ᶜ := by
    ext x; simp [Set.mem_compl_iff]
  rw [h_eq]
  exact hψ.isOpen_preimage _ (isClosed_singleton.isOpen_compl)

/-! ════════════════════════════════════════════════════════════════════════
    PART 2 — LOCAL POLAR LIFT  (Phase A.1)
    ════════════════════════════════════════════════════════════════════════ -/

/-- **PHASE A.1 — LOCAL POLAR LIFT ON THE NONZERO LOCUS**.

    For a `ContDiff ℝ n` complex-valued field `ψ : ℝ × ℝ → ℂ` and any
    spacetime point `x₀` with `ψ x₀ ≠ 0`, there exist:

      • an open neighborhood `U ∋ x₀`,
      • smooth real-valued amplitude `r : ℝ × ℝ → ℝ`,
      • smooth real-valued phase     `s : ℝ × ℝ → ℝ`,

    such that on `U`,
        `ψ x = (r x : ℂ) · Complex.exp ((s x : ℂ) · Complex.I)`.

    Equivalently:  on `U`, `ψ = r · cos s + i · r · sin s`.

    Construction:  rotate `ψ` by `α := (ψ x₀)⁻¹` so the rotated field
    hits `1 ∈ slitPlane` at `x₀`; pull back the smooth `arg` available
    on `slitPlane` to a continuous phase representative, then add the
    constant phase shift `θ₀ := arg(ψ x₀)`. -/
theorem polar_on_nonzero_locus
    {n : WithTop ℕ∞} (ψ : ℝ × ℝ → ℂ) (hψ : ContDiff ℝ n ψ)
    (x₀ : ℝ × ℝ) (h_nz : ψ x₀ ≠ 0) :
    ∃ (U : Set (ℝ × ℝ)),
      IsOpen U ∧ x₀ ∈ U ∧
      ∃ (r s : ℝ × ℝ → ℝ),
        ContDiffOn ℝ n r U ∧ ContDiffOn ℝ n s U ∧
        ∀ x ∈ U,
          ψ x = (r x : ℂ) * Complex.exp ((s x : ℂ) * Complex.I) := by
  -- Step 1.  Rotation constants:  α := (ψ x₀)⁻¹, so α · ψ x₀ = 1.
  set α : ℂ := (ψ x₀)⁻¹ with hα_def
  -- φ(x) := α · ψ(x).  Then φ(x₀) = 1 ∈ slitPlane.
  set φ : ℝ × ℝ → ℂ := fun x => α * ψ x with hφ_def
  have h_φx₀ : φ x₀ = 1 := by
    show α * ψ x₀ = 1
    rw [hα_def]; exact inv_mul_cancel₀ h_nz
  have h_φx₀_slit : φ x₀ ∈ Complex.slitPlane := by
    rw [h_φx₀]
    exact Or.inl (by norm_num : (0:ℝ) < (1:ℂ).re)
  -- φ is ContDiff ℝ n (constant times ContDiff function).
  have hφ_cd : ContDiff ℝ n φ := contDiff_const.mul hψ
  -- Step 2.  Open neighborhood U := φ⁻¹(slitPlane).
  set U : Set (ℝ × ℝ) := φ ⁻¹' Complex.slitPlane with hU_def
  have hU_open : IsOpen U :=
    hφ_cd.continuous.isOpen_preimage _ Complex.isOpen_slitPlane
  have hx₀_U : x₀ ∈ U := h_φx₀_slit
  -- Step 3.  Constant phase shift θ₀ := arg(ψ x₀).
  set θ₀ : ℝ := Complex.arg (ψ x₀) with hθ₀_def
  -- Step 4.  Smooth real-valued amplitude and phase fields.
  set r : ℝ × ℝ → ℝ := fun x => ‖ψ x‖ with hr_def
  set s : ℝ × ℝ → ℝ := fun x => Complex.arg (φ x) + θ₀ with hs_def
  refine ⟨U, hU_open, hx₀_U, r, s, ?_, ?_, ?_⟩
  · -- ContDiffOn r U.  At every x ∈ U, ψ x ≠ 0, so ‖·‖ is smooth at ψ x.
    intro x hxU
    have hφ_x_ne : φ x ≠ 0 := Complex.slitPlane_ne_zero hxU
    have hψ_x_ne : ψ x ≠ 0 := by
      intro hψx_eq
      apply hφ_x_ne
      show α * ψ x = 0
      rw [hψx_eq, mul_zero]
    exact ((contDiffAt_norm ℝ hψ_x_ne).comp x hψ.contDiffAt).contDiffWithinAt
  · -- ContDiffOn s U.  s = arg ∘ φ + θ₀; arg is smooth on slitPlane.
    intro x hxU
    have h_arg_phi : ContDiffAt ℝ n (fun y : ℝ × ℝ => Complex.arg (φ y)) x :=
      (complex_contDiffAt_arg hxU).comp x hφ_cd.contDiffAt
    -- s x = arg(φ x) + θ₀.  Add a constant.
    have : ContDiffAt ℝ n s x := h_arg_phi.add contDiffAt_const
    exact this.contDiffWithinAt
  · -- Polar identity:  ψ x = (r x : ℂ) * exp((s x : ℂ) * I).
    intro x hxU
    -- φ x ≠ 0  and  ψ x ≠ 0.
    have hφ_x_ne : φ x ≠ 0 := Complex.slitPlane_ne_zero hxU
    -- ψ x = φ x · ψ x₀
    have h_ψ_eq : ψ x = φ x * ψ x₀ := by
      show ψ x = α * ψ x * ψ x₀
      rw [hα_def]
      field_simp
    -- ‖ψ x‖ = ‖φ x‖ * ‖ψ x₀‖
    have h_norm_ψ : (‖ψ x‖ : ℂ) = (‖φ x‖ : ℂ) * (‖ψ x₀‖ : ℂ) := by
      rw [h_ψ_eq]
      push_cast
      rw [Complex.norm_mul]
      push_cast
      ring
    -- Rewrite (s x : ℂ) * I as a sum of two factors.
    have h_s_split :
        ((s x : ℂ) * Complex.I)
          = ((Complex.arg (φ x) : ℂ) * Complex.I)
              + ((θ₀ : ℂ) * Complex.I) := by
      show (((Complex.arg (φ x) + θ₀ : ℝ) : ℂ) * Complex.I) = _
      push_cast
      ring
    -- Mathlib polar identities.
    have h_polar_phi :
        (‖φ x‖ : ℂ) * Complex.exp ((Complex.arg (φ x) : ℂ) * Complex.I)
          = φ x :=
      Complex.norm_mul_exp_arg_mul_I (φ x)
    have h_polar_ψ₀ :
        (‖ψ x₀‖ : ℂ) * Complex.exp ((Complex.arg (ψ x₀) : ℂ) * Complex.I)
          = ψ x₀ :=
      Complex.norm_mul_exp_arg_mul_I (ψ x₀)
    -- Combine.
    show ψ x = (‖ψ x‖ : ℂ) * Complex.exp ((s x : ℂ) * Complex.I)
    rw [h_norm_ψ, h_s_split, Complex.exp_add]
    -- Goal:  ψ x = (‖φ x‖ * ‖ψ x₀‖) *
    --              (exp(arg(φ x) * I) * exp(θ₀ * I))
    -- RHS = (‖φ x‖ * exp(arg(φ x) * I)) * (‖ψ x₀‖ * exp(θ₀ * I))
    --     = φ x * ψ x₀  (using the two polar identities)
    --     = ψ x         (using h_ψ_eq)
    have h_rhs_eq :
        ((‖φ x‖ : ℂ) * (‖ψ x₀‖ : ℂ))
          * (Complex.exp ((Complex.arg (φ x) : ℂ) * Complex.I)
              * Complex.exp ((θ₀ : ℂ) * Complex.I))
        = ψ x := by
      have h1 :
          ((‖φ x‖ : ℂ) * Complex.exp ((Complex.arg (φ x) : ℂ) * Complex.I))
            * ((‖ψ x₀‖ : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I))
          = φ x * ψ x₀ := by
        rw [h_polar_phi]
        show φ x *
              ((‖ψ x₀‖ : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)) = φ x * ψ x₀
        rw [show (θ₀ : ℂ) = (Complex.arg (ψ x₀) : ℂ) from rfl]
        rw [h_polar_ψ₀]
      calc ((‖φ x‖ : ℂ) * (‖ψ x₀‖ : ℂ))
            * (Complex.exp ((Complex.arg (φ x) : ℂ) * Complex.I)
                * Complex.exp ((θ₀ : ℂ) * Complex.I))
          = ((‖φ x‖ : ℂ) * Complex.exp ((Complex.arg (φ x) : ℂ) * Complex.I))
              * ((‖ψ x₀‖ : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)) := by ring
        _ = φ x * ψ x₀ := h1
        _ = ψ x := h_ψ_eq.symm
    exact h_rhs_eq.symm

/-! ════════════════════════════════════════════════════════════════════════
    PART 3 — NODE-SAFE DENSITY AND CURRENT  (Phase A.3 foundation)

    Define the Madelung-Bohm density and current using *complex* formulas
    (not polar), so they are globally well-defined across nodes:

        ρ(x, t) := ‖ψ(x, t)‖²
        J(x, t) := (ℏ/m) · Im(ψ̄ · ∂_x ψ)(x, t)

    Both are `ContDiff` globally for `ContDiff` ψ — no node singularities.

    On the nonzero locus, polar agreement: `J = (ℏ/m) · ρ · ∂_x s`.
    The continuity equation `∂_t ρ + ∂_x J = 0` (pointwise from Schrödinger)
    is the headline corollary;  proved in a follow-on once these
    foundations are in place.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Node-safe Madelung density** `ρ := ‖ψ‖²`.  Globally defined
    everywhere, including at nodes where `ψ = 0` (and `ρ = 0` there). -/
noncomputable def rhoOfPsi (ψ : ℝ × ℝ → ℂ) (x t : ℝ) : ℝ :=
  Complex.normSq (ψ (x, t))

/-- **Node-safe 1D Bohm current** `J := (ℏ/m) · Im(ψ̄ · ∂_x ψ)`.
    Equivalently `(ℏ/m) · (ψ.re · ∂_x ψ.im − ψ.im · ∂_x ψ.re)`.
    Globally defined; agrees with the polar form `(ℏ/m) · ρ · ∂_x s`
    on the nonzero locus (proved below). -/
noncomputable def currentOfPsi1D (ψ : ℝ × ℝ → ℂ) (hbar m : ℝ)
    (x t : ℝ) : ℝ :=
  (hbar / m) *
    ((ψ (x, t)).re * deriv (fun ξ => (ψ (ξ, t)).im) x
      - (ψ (x, t)).im * deriv (fun ξ => (ψ (ξ, t)).re) x)

/-- The density expressed component-wise:  `ρ = ψ.re² + ψ.im²`. -/
theorem rhoOfPsi_eq_sq (ψ : ℝ × ℝ → ℂ) (x t : ℝ) :
    rhoOfPsi ψ x t = (ψ (x, t)).re ^ 2 + (ψ (x, t)).im ^ 2 := by
  unfold rhoOfPsi
  rw [Complex.normSq_apply]
  ring

/-- The density is nonneg. -/
theorem rhoOfPsi_nonneg (ψ : ℝ × ℝ → ℂ) (x t : ℝ) :
    0 ≤ rhoOfPsi ψ x t := Complex.normSq_nonneg _

/-- The density vanishes at nodes. -/
theorem rhoOfPsi_eq_zero_iff (ψ : ℝ × ℝ → ℂ) (x t : ℝ) :
    rhoOfPsi ψ x t = 0 ↔ ψ (x, t) = 0 := Complex.normSq_eq_zero

/-! **Global regularity** of ρ and J from `ContDiff` of ψ:
    no node singularities, ρ smooth from C² ψ, J smooth from C³ ψ. -/

/-- **ρ globally `ContDiff ℝ n`** from `ContDiff ℝ n` ψ. -/
theorem rhoOfPsi_contDiff {n : WithTop ℕ∞} {ψ : ℝ × ℝ → ℂ}
    (hψ : ContDiff ℝ n ψ) :
    ContDiff ℝ n (fun xt : ℝ × ℝ => rhoOfPsi ψ xt.1 xt.2) := by
  have h_re : ContDiff ℝ n (fun xt : ℝ × ℝ => (ψ xt).re) :=
    Complex.reCLM.contDiff.comp hψ
  have h_im : ContDiff ℝ n (fun xt : ℝ × ℝ => (ψ xt).im) :=
    Complex.imCLM.contDiff.comp hψ
  have h_eq :
      (fun xt : ℝ × ℝ => rhoOfPsi ψ xt.1 xt.2)
        = (fun xt : ℝ × ℝ => (ψ xt).re ^ 2 + (ψ xt).im ^ 2) := by
    funext ⟨x, t⟩
    rw [rhoOfPsi_eq_sq]
  rw [h_eq]
  exact (h_re.pow 2).add (h_im.pow 2)

/-! ════════════════════════════════════════════════════════════════════════
    PART 4 — POLAR AGREEMENT ON THE NONZERO LOCUS

    Show that on any open set where ψ has a local polar form
    `ψ = (r : ℂ) · exp((s : ℂ) · I)`, the node-safe current `J`
    agrees with the polar formula `(ℏ/m) · ρ · ∂_x s`.

    This connects Phase A.3's complex/node-safe definitions to the
    polar fields produced by `polar_on_nonzero_locus` (Phase A.1).
    ════════════════════════════════════════════════════════════════════════ -/

/-- On any nbhd `U` where `ψ = (r : ℂ) · exp((s : ℂ) · I)`, the node-safe
    current agrees with `(ℏ/m) · ρ · ∂_x s`:
        `J(x, t) = (ℏ/m) · ρ(x, t) · (∂_x s)(x, t)`.

    Standard Madelung identity, but proved here with the **node-safe
    definitions** (so the statement is meaningful globally even though
    this lemma is conditional on a local polar representative). -/
theorem currentOfPsi1D_eq_rho_dx_s_on_polar_locus
    (ψ : ℝ × ℝ → ℂ) (hψ : ContDiff ℝ 2 ψ)
    (hbar m : ℝ)
    (U : Set (ℝ × ℝ)) (hU_open : IsOpen U)
    (r s : ℝ × ℝ → ℝ)
    (hr_cdOn : ContDiffOn ℝ 2 r U) (hs_cdOn : ContDiffOn ℝ 2 s U)
    (h_polar : ∀ q ∈ U,
      ψ q = (r q : ℂ) * Complex.exp ((s q : ℂ) * Complex.I))
    (x t : ℝ) (h_xt_U : (x, t) ∈ U) :
    currentOfPsi1D ψ hbar m x t
      = (hbar / m) * rhoOfPsi ψ x t * deriv (fun ξ => s (ξ, t)) x := by
  -- We prove this by:
  --   (a) noting that on a nbhd of (x, t), ψ(ξ, t) = (r(ξ, t) : ℂ) * exp(i·s(ξ, t))
  --       (since (ξ, t) ∈ U on a nbhd of (x, t)).
  --   (b) Using `EventuallyEq.deriv_eq` to compute the spatial derivs of
  --       ψ.re and ψ.im in terms of those of r and s.
  --   (c) Substituting into the definition of currentOfPsi1D.
  --   (d) Simplifying using ρ = r² (from the polar identity).
  --
  -- The full computation is the standard Madelung identity:
  --   Im(ψ̄ · ∂_x ψ)  =  Im((r e^{-is}) · (∂_x r + i r ∂_x s) e^{is})
  --                  =  Im(r ∂_x r  +  i r² ∂_x s)
  --                  =  r² · ∂_x s
  --                  =  ρ · ∂_x s
  -- Hence J = (ℏ/m) · ρ · ∂_x s.
  --
  -- We construct the EventuallyEq witnesses for ψ.re, ψ.im, then their
  -- ∂_x's, then chain.
  have hU_nhds : U ∈ 𝓝 (x, t) := hU_open.mem_nhds h_xt_U
  -- Step (a):  polar form near (x, t) in spatial direction.
  -- We need the polar identity to hold on a nbhd of x in the slice.
  have h_slice_nhds : {ξ : ℝ | (ξ, t) ∈ U} ∈ 𝓝 x := by
    have h_cont : Continuous (fun ξ : ℝ => ((ξ, t) : ℝ × ℝ)) :=
      continuous_id.prodMk continuous_const
    exact h_cont.continuousAt.preimage_mem_nhds hU_nhds
  -- The spatial slice of ψ matches the polar form on this nbhd.
  have h_eqRe : (fun ξ => (ψ (ξ, t)).re)
      =ᶠ[𝓝 x] (fun ξ => r (ξ, t) * Real.cos (s (ξ, t))) := by
    filter_upwards [h_slice_nhds] with ξ hξU
    have h1 := h_polar (ξ, t) hξU
    -- ψ (ξ, t) = (r (ξ, t) : ℂ) * exp((s (ξ, t) : ℂ) * I)
    -- = ⟨r·cos s, r·sin s⟩
    rw [h1, Complex.exp_mul_I]
    simp [Complex.cos_ofReal_re, Complex.cos_ofReal_im,
          Complex.sin_ofReal_re, Complex.sin_ofReal_im,
          Complex.add_re, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have h_eqIm : (fun ξ => (ψ (ξ, t)).im)
      =ᶠ[𝓝 x] (fun ξ => r (ξ, t) * Real.sin (s (ξ, t))) := by
    filter_upwards [h_slice_nhds] with ξ hξU
    have h1 := h_polar (ξ, t) hξU
    rw [h1, Complex.exp_mul_I]
    simp [Complex.cos_ofReal_re, Complex.cos_ofReal_im,
          Complex.sin_ofReal_re, Complex.sin_ofReal_im,
          Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  -- Step (b):  derivatives at x.
  -- Pointwise values at x:
  have h_psi_at : ψ (x, t) =
      (r (x, t) : ℂ) * Complex.exp ((s (x, t) : ℂ) * Complex.I) :=
    h_polar (x, t) h_xt_U
  have h_psi_re_at : (ψ (x, t)).re = r (x, t) * Real.cos (s (x, t)) := by
    rw [h_psi_at, Complex.exp_mul_I]
    simp [Complex.cos_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im,
      Complex.add_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have h_psi_im_at : (ψ (x, t)).im = r (x, t) * Real.sin (s (x, t)) := by
    rw [h_psi_at, Complex.exp_mul_I]
    simp [Complex.cos_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im,
      Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  -- Slice derivatives of r and s at x.
  have hr_slice_at : ContDiffAt ℝ 2 (fun ξ => r (ξ, t)) x := by
    have h_cda : ContDiffAt ℝ 2 r (x, t) := hr_cdOn.contDiffAt hU_nhds
    have h_slice : ContDiff ℝ ⊤ (fun ξ : ℝ => ((ξ, t) : ℝ × ℝ)) :=
      contDiff_id.prodMk contDiff_const
    exact h_cda.comp x (h_slice.of_le le_top).contDiffAt
  have hs_slice_at : ContDiffAt ℝ 2 (fun ξ => s (ξ, t)) x := by
    have h_cda : ContDiffAt ℝ 2 s (x, t) := hs_cdOn.contDiffAt hU_nhds
    have h_slice : ContDiff ℝ ⊤ (fun ξ : ℝ => ((ξ, t) : ℝ × ℝ)) :=
      contDiff_id.prodMk contDiff_const
    exact h_cda.comp x (h_slice.of_le le_top).contDiffAt
  have h2ne0 : (2 : WithTop ℕ∞) ≠ 0 := by decide
  have hr_d : DifferentiableAt ℝ (fun ξ => r (ξ, t)) x :=
    hr_slice_at.differentiableAt h2ne0
  have hs_d : DifferentiableAt ℝ (fun ξ => s (ξ, t)) x :=
    hs_slice_at.differentiableAt h2ne0
  -- Chain rule:  d/dx [r · cos s] = r' cos s − r sin s · s'
  -- And:        d/dx [r · sin s] = r' sin s + r cos s · s'
  -- These are exactly `deriv_psiRe_x` / `deriv_psiIm_x` for the SmoothWaveField
  -- with r = r(·, t), s = s(·, t).  We invoke them via local SmoothWaveField:
  set sw : LohmillerSlotineCalculus.SmoothWaveField :=
    { r := fun ξ τ => r (ξ, τ)
      s := fun ξ τ => s (ξ, τ)
      V := fun _ _ => 0
      m := max m 1  -- dummy; not used
      hbar := max hbar 1  -- dummy; not used
      m_pos := lt_of_lt_of_le zero_lt_one (le_max_right m 1)
      hbar_pos := lt_of_lt_of_le zero_lt_one (le_max_right hbar 1) }
    with hsw_def
  have hr_d' : DifferentiableAt ℝ (fun ξ => sw.r ξ t) x := hr_d
  have hs_d' : DifferentiableAt ℝ (fun ξ => sw.s ξ t) x := hs_d
  have h_dxRe :
      deriv (fun ξ => (ψ (ξ, t)).re) x
        = SmoothWaveField.partialX sw.r x t * Real.cos (sw.s x t)
          - sw.r x t * Real.sin (sw.s x t) *
              SmoothWaveField.partialX sw.s x t := by
    rw [Filter.EventuallyEq.deriv_eq h_eqRe]
    have :
        deriv (fun ξ => sw.r ξ t * Real.cos (sw.s ξ t)) x
          = SmoothWaveField.partialX sw.r x t * Real.cos (sw.s x t)
            - sw.r x t * Real.sin (sw.s x t) *
                SmoothWaveField.partialX sw.s x t :=
      deriv_psiRe_x sw x t hr_d' hs_d'
    convert this using 1
  have h_dxIm :
      deriv (fun ξ => (ψ (ξ, t)).im) x
        = SmoothWaveField.partialX sw.r x t * Real.sin (sw.s x t)
          + sw.r x t * Real.cos (sw.s x t) *
              SmoothWaveField.partialX sw.s x t := by
    rw [Filter.EventuallyEq.deriv_eq h_eqIm]
    have :
        deriv (fun ξ => sw.r ξ t * Real.sin (sw.s ξ t)) x
          = SmoothWaveField.partialX sw.r x t * Real.sin (sw.s x t)
            + sw.r x t * Real.cos (sw.s x t) *
                SmoothWaveField.partialX sw.s x t :=
      deriv_psiIm_x sw x t hr_d' hs_d'
    convert this using 1
  -- Substitute into J = (ℏ/m) · (ψ.re · ∂_x ψ.im − ψ.im · ∂_x ψ.re)
  --                   = (ℏ/m) · (r·cos s · [r'·sin s + r·cos s·s']
  --                            − r·sin s · [r'·cos s − r·sin s·s'])
  --                   = (ℏ/m) · (r² · (cos²s + sin²s) · s')
  --                   = (ℏ/m) · r² · s'
  --                   = (ℏ/m) · ρ · s'.
  unfold currentOfPsi1D
  rw [h_psi_re_at, h_psi_im_at, h_dxRe, h_dxIm]
  -- Goal: (ℏ/m) · (r·cos s · [r'·sin s + r·cos s·s']
  --              − r·sin s · [r'·cos s − r·sin s·s'])
  --     = (ℏ/m) · ρ · s'
  -- Need ρ = r² in the goal, so rewrite rhoOfPsi via h_psi_re_at and h_psi_im_at.
  have h_rho : rhoOfPsi ψ x t = r (x, t) ^ 2 := by
    rw [rhoOfPsi_eq_sq, h_psi_re_at, h_psi_im_at]
    have : Real.cos (s (x, t)) ^ 2 + Real.sin (s (x, t)) ^ 2 = 1 :=
      Real.cos_sq_add_sin_sq _
    nlinarith [this, sq_nonneg (r (x, t))]
  rw [h_rho]
  -- Final algebraic identity:
  -- a·cos s · (a'·sin s + a·cos s · b') − a·sin s · (a'·cos s − a·sin s · b')
  --   = a²·(cos²s + sin²s)·b' = a²·b'
  -- where a = r(x,t), a' = ∂_x r, b' = ∂_x s.
  have h_pyth :
      Real.cos (s (x, t)) ^ 2 + Real.sin (s (x, t)) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  -- partialX shorthand
  set a := r (x, t)
  set a' := SmoothWaveField.partialX sw.r x t
  set b' := SmoothWaveField.partialX sw.s x t
  set cs := Real.cos (s (x, t))
  set ss := Real.sin (s (x, t))
  show (hbar / m) *
        (a * cs * (a' * ss + a * cs * b') - a * ss * (a' * cs - a * ss * b'))
      = hbar / m * a ^ 2 * b'
  have : a * cs * (a' * ss + a * cs * b') - a * ss * (a' * cs - a * ss * b')
        = a ^ 2 * b' * (cs ^ 2 + ss ^ 2) := by ring
  rw [this, h_pyth]; ring

/-! ════════════════════════════════════════════════════════════════════════
    PART 5 — POINTWISE CONTINUITY EQUATION FROM SCHRÖDINGER (Phase A.3 headline)
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Schrödinger equation for ψ at a single spacetime point**, expressed
    as the pair of real and imaginary part identities split from the
    complex equation `i ℏ ∂_t ψ = −(ℏ²/2m) ∂_x² ψ + V · ψ`:

      • imag-part:  `ℏ ∂_t ψ.re = −(ℏ²/2m) ∂_x² ψ.im + V · ψ.im`
      • real-part:  `ℏ ∂_t ψ.im =  (ℏ²/2m) ∂_x² ψ.re − V · ψ.re`

    Stated entirely in real-valued partial derivatives of the components
    of ψ — node-safe (no polar coordinates). -/
def SchrodingerEqOnPsi (ψ : ℝ × ℝ → ℂ) (V : ℝ → ℝ → ℝ)
    (m hbar : ℝ) (x t : ℝ) : Prop :=
  (hbar * deriv (fun τ => (ψ (x, τ)).re) t
    = -(hbar^2 / (2*m)) * iteratedDeriv 2 (fun ξ => (ψ (ξ, t)).im) x
      + V x t * (ψ (x, t)).im)
  ∧ (hbar * deriv (fun τ => (ψ (x, τ)).im) t
    = (hbar^2 / (2*m)) * iteratedDeriv 2 (fun ξ => (ψ (ξ, t)).re) x
      - V x t * (ψ (x, t)).re)

/-- **∂_t ρ via the product rule**:
        `∂_t (‖ψ‖²)  =  2 · ψ.re · ∂_t ψ.re  +  2 · ψ.im · ∂_t ψ.im`. -/
theorem deriv_rhoOfPsi_t {ψ : ℝ × ℝ → ℂ} (x t : ℝ)
    (hr_t : DifferentiableAt ℝ (fun τ => (ψ (x, τ)).re) t)
    (hi_t : DifferentiableAt ℝ (fun τ => (ψ (x, τ)).im) t) :
    deriv (fun τ => rhoOfPsi ψ x τ) t
      = 2 * (ψ (x, t)).re * deriv (fun τ => (ψ (x, τ)).re) t
        + 2 * (ψ (x, t)).im * deriv (fun τ => (ψ (x, τ)).im) t := by
  have h_eq : (fun τ => rhoOfPsi ψ x τ)
      = (fun τ => (ψ (x, τ)).re ^ 2 + (ψ (x, τ)).im ^ 2) := by
    funext τ; rw [rhoOfPsi_eq_sq]
  rw [h_eq]
  have hre_at : HasDerivAt (fun τ => (ψ (x, τ)).re)
      (deriv (fun τ => (ψ (x, τ)).re) t) t := hr_t.hasDerivAt
  have him_at : HasDerivAt (fun τ => (ψ (x, τ)).im)
      (deriv (fun τ => (ψ (x, τ)).im) t) t := hi_t.hasDerivAt
  have hre_sq : HasDerivAt (fun τ => (ψ (x, τ)).re ^ 2)
      (2 * (ψ (x, t)).re * deriv (fun τ => (ψ (x, τ)).re) t) t := by
    have := hre_at.pow 2
    convert this using 1
    push_cast; ring
  have him_sq : HasDerivAt (fun τ => (ψ (x, τ)).im ^ 2)
      (2 * (ψ (x, t)).im * deriv (fun τ => (ψ (x, τ)).im) t) t := by
    have := him_at.pow 2
    convert this using 1
    push_cast; ring
  exact (hre_sq.add him_sq).deriv

/-- **∂_x J via product rule** (the cross terms `∂_x ψ.re · ∂_x ψ.im`
    cancel each other):
        `∂_x [(ℏ/m) · (ψ.re · ∂_x ψ.im − ψ.im · ∂_x ψ.re)]
           =  (ℏ/m) · (ψ.re · ∂_x² ψ.im − ψ.im · ∂_x² ψ.re)`. -/
theorem deriv_currentOfPsi1D_x {ψ : ℝ × ℝ → ℂ} (hbar m : ℝ) (x t : ℝ)
    (hr_x_at : DifferentiableAt ℝ (fun ξ => (ψ (ξ, t)).re) x)
    (hi_x_at : DifferentiableAt ℝ (fun ξ => (ψ (ξ, t)).im) x)
    (hr_dx_at : DifferentiableAt ℝ
                  (deriv (fun ξ => (ψ (ξ, t)).re)) x)
    (hi_dx_at : DifferentiableAt ℝ
                  (deriv (fun ξ => (ψ (ξ, t)).im)) x) :
    deriv (fun ξ => currentOfPsi1D ψ hbar m ξ t) x
      = (hbar / m) *
          ((ψ (x, t)).re * iteratedDeriv 2 (fun ξ => (ψ (ξ, t)).im) x
            - (ψ (x, t)).im * iteratedDeriv 2 (fun ξ => (ψ (ξ, t)).re) x) := by
  have hr_at : HasDerivAt (fun ξ => (ψ (ξ, t)).re)
      (deriv (fun ξ => (ψ (ξ, t)).re) x) x := hr_x_at.hasDerivAt
  have hi_at : HasDerivAt (fun ξ => (ψ (ξ, t)).im)
      (deriv (fun ξ => (ψ (ξ, t)).im) x) x := hi_x_at.hasDerivAt
  have hr_dat : HasDerivAt (deriv (fun ξ => (ψ (ξ, t)).re))
      (deriv (deriv (fun ξ => (ψ (ξ, t)).re)) x) x := hr_dx_at.hasDerivAt
  have hi_dat : HasDerivAt (deriv (fun ξ => (ψ (ξ, t)).im))
      (deriv (deriv (fun ξ => (ψ (ξ, t)).im)) x) x := hi_dx_at.hasDerivAt
  -- d/dx [ψ.re · ∂_x ψ.im] = ∂_x ψ.re · ∂_x ψ.im + ψ.re · ∂_x² ψ.im
  have h1 := hr_at.mul hi_dat
  -- d/dx [ψ.im · ∂_x ψ.re] = ∂_x ψ.im · ∂_x ψ.re + ψ.im · ∂_x² ψ.re
  have h2 := hi_at.mul hr_dat
  -- Difference:
  have h_inner := h1.sub h2
  -- Multiply by (ℏ/m):
  have h_full := h_inner.const_mul (hbar / m)
  -- Convert iteratedDeriv 2 to deriv ∘ deriv.
  have h_re_xx : iteratedDeriv 2 (fun ξ => (ψ (ξ, t)).re) x
      = deriv (deriv (fun ξ => (ψ (ξ, t)).re)) x := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have h_im_xx : iteratedDeriv 2 (fun ξ => (ψ (ξ, t)).im) x
      = deriv (deriv (fun ξ => (ψ (ξ, t)).im)) x := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h_re_xx, h_im_xx]
  -- The deriv of currentOfPsi1D equals h_full's derivative value.
  have h_deriv_eq : deriv (fun ξ => currentOfPsi1D ψ hbar m ξ t) x =
      hbar / m *
        (deriv (fun ξ => (ψ (ξ, t)).re) x *
            deriv (fun ξ => (ψ (ξ, t)).im) x +
          (ψ (x, t)).re *
            deriv (deriv (fun ξ => (ψ (ξ, t)).im)) x -
        (deriv (fun ξ => (ψ (ξ, t)).im) x *
              deriv (fun ξ => (ψ (ξ, t)).re) x +
            (ψ (x, t)).im *
              deriv (deriv (fun ξ => (ψ (ξ, t)).re)) x)) := by
    have h_eq_fn : (fun ξ => currentOfPsi1D ψ hbar m ξ t)
        = (fun ξ =>
            hbar / m *
              ((ψ (ξ, t)).re * deriv (fun ξ' => (ψ (ξ', t)).im) ξ -
                (ψ (ξ, t)).im * deriv (fun ξ' => (ψ (ξ', t)).re) ξ)) := by
      funext ξ; rfl
    rw [h_eq_fn]
    exact h_full.deriv
  rw [h_deriv_eq]
  ring

/-- **PHASE A.3 HEADLINE — POINTWISE CONTINUITY EQUATION FROM SCHRÖDINGER**.

    For a `ContDiff ℝ 2` complex wave field `ψ` satisfying the
    Schrödinger equation at `(x, t)`, the node-safe density and current
    satisfy the pointwise continuity equation:
        `∂_t ρ(x, t) + ∂_x J(x, t) = 0`.

    This holds **globally**, with no restriction to the nonzero locus —
    `ρ` and `J` are defined globally via complex formulas
    (`rhoOfPsi`, `currentOfPsi1D`) that have no node singularities.
    Across nodes the equation just says `0 + 0 = 0` if ψ ≡ 0 in a nbhd,
    or whatever the smooth derivatives give pointwise.

    This is the **node-friendly global conservation law** that Phase A
    has been building toward. -/
theorem continuity_equation_pointwise_from_schrodinger
    {ψ : ℝ × ℝ → ℂ} (hψ : ContDiff ℝ 2 ψ)
    (V : ℝ → ℝ → ℝ) (m hbar : ℝ) (hm : 0 < m) (hhbar : 0 < hbar)
    (x t : ℝ) (h_schrod : SchrodingerEqOnPsi ψ V m hbar x t) :
    deriv (fun τ => rhoOfPsi ψ x τ) t
      + deriv (fun ξ => currentOfPsi1D ψ hbar m ξ t) x = 0 := by
  -- Step 1.  Slice differentiabilities from ContDiff ℝ 2 ψ.
  have h_slice_x_smooth : ContDiff ℝ ⊤ (fun ξ : ℝ => ((ξ, t) : ℝ × ℝ)) :=
    contDiff_id.prodMk contDiff_const
  have h_slice_t_smooth : ContDiff ℝ ⊤ (fun τ : ℝ => ((x, τ) : ℝ × ℝ)) :=
    contDiff_const.prodMk contDiff_id
  have hpsi_x_slice : ContDiff ℝ 2 (fun ξ => ψ (ξ, t)) :=
    hψ.comp (h_slice_x_smooth.of_le le_top)
  have hpsi_t_slice : ContDiff ℝ 2 (fun τ => ψ (x, τ)) :=
    hψ.comp (h_slice_t_smooth.of_le le_top)
  -- Re and Im as real-valued slices.
  have hr_x_cd : ContDiff ℝ 2 (fun ξ : ℝ => (ψ (ξ, t)).re) :=
    Complex.reCLM.contDiff.comp hpsi_x_slice
  have hi_x_cd : ContDiff ℝ 2 (fun ξ : ℝ => (ψ (ξ, t)).im) :=
    Complex.imCLM.contDiff.comp hpsi_x_slice
  have hr_t_cd : ContDiff ℝ 2 (fun τ : ℝ => (ψ (x, τ)).re) :=
    Complex.reCLM.contDiff.comp hpsi_t_slice
  have hi_t_cd : ContDiff ℝ 2 (fun τ : ℝ => (ψ (x, τ)).im) :=
    Complex.imCLM.contDiff.comp hpsi_t_slice
  -- Differentiability witnesses.
  have h2ne0 : (2 : WithTop ℕ∞) ≠ 0 := by decide
  have h1ne0 : (1 : WithTop ℕ∞) ≠ 0 := by decide
  have h1le2 : (1 : WithTop ℕ∞) + 1 ≤ 2 := by norm_num
  have hr_t_at : DifferentiableAt ℝ (fun τ => (ψ (x, τ)).re) t :=
    (hr_t_cd.differentiable h2ne0).differentiableAt
  have hi_t_at : DifferentiableAt ℝ (fun τ => (ψ (x, τ)).im) t :=
    (hi_t_cd.differentiable h2ne0).differentiableAt
  have hr_x_at : DifferentiableAt ℝ (fun ξ => (ψ (ξ, t)).re) x :=
    (hr_x_cd.differentiable h2ne0).differentiableAt
  have hi_x_at : DifferentiableAt ℝ (fun ξ => (ψ (ξ, t)).im) x :=
    (hi_x_cd.differentiable h2ne0).differentiableAt
  -- deriv of slice is C¹, hence differentiable at x.
  have hr_dx_cd : ContDiff ℝ 1 (deriv (fun ξ => (ψ (ξ, t)).re)) :=
    hr_x_cd.deriv'
  have hi_dx_cd : ContDiff ℝ 1 (deriv (fun ξ => (ψ (ξ, t)).im)) :=
    hi_x_cd.deriv'
  have hr_dx_at : DifferentiableAt ℝ (deriv (fun ξ => (ψ (ξ, t)).re)) x :=
    (hr_dx_cd.differentiable h1ne0).differentiableAt
  have hi_dx_at : DifferentiableAt ℝ (deriv (fun ξ => (ψ (ξ, t)).im)) x :=
    (hi_dx_cd.differentiable h1ne0).differentiableAt
  -- Step 2.  ∂_t ρ via product rule.
  have h_dt_rho := deriv_rhoOfPsi_t x t hr_t_at hi_t_at
  -- Step 3.  ∂_x J via product rule (cross terms cancel).
  have h_dx_J := deriv_currentOfPsi1D_x hbar m x t hr_x_at hi_x_at hr_dx_at hi_dx_at
  -- Step 4.  Schrödinger split.
  obtain ⟨hS_im, hS_re⟩ := h_schrod
  -- From Schrödinger:
  --   ℏ · ∂_t ψ.re = −(ℏ²/2m) · ∂_x² ψ.im + V · ψ.im
  --   ℏ · ∂_t ψ.im =  (ℏ²/2m) · ∂_x² ψ.re − V · ψ.re
  -- We'll need:
  --   m · ∂_t ψ.re =  (m/ℏ) · [−(ℏ²/2m) · ∂_x² ψ.im + V · ψ.im]
  --                =  −(ℏ/2) · ∂_x² ψ.im + (m·V/ℏ) · ψ.im
  -- For the final ring step we work with hbar non-zero or not?
  -- We need to divide hS_im, hS_re by ℏ to get ∂_t ψ.re and ∂_t ψ.im in terms of ∂_x².
  -- We then plug into h_dt_rho and compare to -h_dx_J.
  -- Combine the two:
  --   ∂_t ρ = 2 ψ.re ∂_t ψ.re + 2 ψ.im ∂_t ψ.im
  --   ℏ · ∂_t ρ = 2 ψ.re · ℏ · ∂_t ψ.re + 2 ψ.im · ℏ · ∂_t ψ.im
  --             = 2 ψ.re · [−(ℏ²/2m) · ∂_x² ψ.im + V · ψ.im]
  --             + 2 ψ.im · [ (ℏ²/2m) · ∂_x² ψ.re − V · ψ.re]
  --             = −(ℏ²/m) · ψ.re · ∂_x² ψ.im + 2 V ψ.re ψ.im
  --             + (ℏ²/m) · ψ.im · ∂_x² ψ.re − 2 V ψ.re ψ.im
  --             = −(ℏ²/m) · [ψ.re · ∂_x² ψ.im − ψ.im · ∂_x² ψ.re]
  --   ∂_x J = (ℏ/m) · [ψ.re · ∂_x² ψ.im − ψ.im · ∂_x² ψ.re]
  --   ℏ · ∂_x J = (ℏ²/m) · [ψ.re · ∂_x² ψ.im − ψ.im · ∂_x² ψ.re]
  --   So ℏ · (∂_t ρ + ∂_x J) = 0, hence ∂_t ρ + ∂_x J = 0  (if ℏ ≠ 0).
  -- We don't yet have ℏ ≠ 0 hypothesis explicitly.  Let's handle that.
  -- Actually we'll prove ∂_t ρ + ∂_x J = 0 directly by substituting
  -- expressions for ∂_t ψ.re and ∂_t ψ.im divided by ℏ.
  --
  -- Step 5.  Multiply the goal by ℏ; the algebraic identity follows from
  -- `linear_combination` over hS_im and hS_re; divide by ℏ ≠ 0 to finish.
  have hhbar_ne : hbar ≠ 0 := ne_of_gt hhbar
  have hm_ne : m ≠ 0 := ne_of_gt hm
  have h_key :
      hbar * (deriv (fun τ => rhoOfPsi ψ x τ) t
              + deriv (fun ξ => currentOfPsi1D ψ hbar m ξ t) x) = 0 := by
    rw [h_dt_rho, h_dx_J]
    linear_combination
      2 * (ψ (x, t)).re * hS_im + 2 * (ψ (x, t)).im * hS_re
  -- Conclude:  hbar ≠ 0 cancels.
  rcases mul_eq_zero.mp h_key with hh | h
  · exact absurd hh hhbar_ne
  · exact h

/-! ════════════════════════════════════════════════════════════════════════
    PART 7 — NODE-FRIENDLY LS BRIDGE  (Phase A.2)

    Compose `polar_on_nonzero_locus` (Phase A.1) with the local PDE
    bridge `schrodinger_PDE_iff_HJ_continuity_at` (in
    `LohmillerSlotineCalculus`, Part 6.5) to deliver the headline
    Madelung-Bohm bridge for arbitrary `ContDiff ℝ 2` complex wave
    fields — with no global no-nodes assumption.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **PHASE A.2 — NODE-FRIENDLY LS BRIDGE**.

    For any `ContDiff ℝ 2` complex-valued wave field `ψ : ℝ × ℝ → ℂ`
    and any spacetime point `(x, t)` with `ψ (x, t) ≠ 0`, there exists:

      • an explicit smooth wave field `sw` (with user-supplied
        potential `V`, mass `m`, and `ħ`),
      • an open neighborhood `U ∋ (x, t)` on which
            `ψ q = (sw.r q.1 q.2 : ℂ) · exp ((sw.s q.1 q.2 : ℂ) · I)`
        holds (the local Madelung polar identity),
      • a witness `SmoothEnoughAt sw x t` (local differentiability),

    and the pointwise PDE-residual equivalence:
        `(PDE_residualRe sw x t = 0 ∧ PDE_residualIm sw x t = 0)`
        ⟺
        `(HamiltonJacobiWithBohm (WaveData.atPoint sw x t)
          ∧ ContinuityEquation (WaveData.atPoint sw x t))`.

    This is the **physically correct** form of the LS bridge:  it makes
    no global no-nodes assumption — only the LOCAL non-vanishing of
    `ψ` at the spacetime point of interest, which is exactly what
    physical Madelung-Bohm theory requires. -/
theorem LSBridge_PDE_equivalence_off_nodes
    (ψ : ℝ × ℝ → ℂ) (hψ : ContDiff ℝ 2 ψ)
    (V : ℝ → ℝ → ℝ) (m hbar : ℝ) (hm : 0 < m) (hhbar : 0 < hbar)
    (x t : ℝ) (h_nz : ψ (x, t) ≠ 0) :
    ∃ (sw : SmoothWaveField) (U : Set (ℝ × ℝ)),
      IsOpen U ∧ (x, t) ∈ U ∧
      SmoothEnoughAt sw x t ∧
      (∀ q ∈ U,
          ψ q = (sw.r q.1 q.2 : ℂ) * Complex.exp ((sw.s q.1 q.2 : ℂ) * Complex.I))
      ∧ ((PDE_residualRe sw x t = 0 ∧ PDE_residualIm sw x t = 0)
          ↔ (LohmillerSlotineBridge.HamiltonJacobiWithBohm
              (WaveData.atPoint sw x t)
            ∧ LohmillerSlotineBridge.ContinuityEquation
                (WaveData.atPoint sw x t))) := by
  -- Step 1.  Local Madelung polar lift on a nbhd U of (x, t).
  obtain ⟨U, hU_open, h_xt_U, r, s, hr_cdOn, hs_cdOn, h_polar⟩ :=
    polar_on_nonzero_locus ψ hψ (x, t) h_nz
  -- Step 2.  Build the SmoothWaveField.
  let sw : SmoothWaveField :=
    { r := fun ξ τ => r (ξ, τ)
      s := fun ξ τ => s (ξ, τ)
      V := V
      m := m
      hbar := hbar
      m_pos := hm
      hbar_pos := hhbar }
  -- Step 3.  ContDiffAt at (x, t) from ContDiffOn U.
  have hU_nhds : U ∈ 𝓝 (x, t) := hU_open.mem_nhds h_xt_U
  have hr_cda : ContDiffAt ℝ 2 r (x, t) := hr_cdOn.contDiffAt hU_nhds
  have hs_cda : ContDiffAt ℝ 2 s (x, t) := hs_cdOn.contDiffAt hU_nhds
  -- Step 4.  Slice smoothness for SmoothEnoughAt fields.
  have h_slice_x : ContDiff ℝ ⊤ (fun ξ : ℝ => (ξ, t)) :=
    contDiff_id.prodMk contDiff_const
  have h_slice_t : ContDiff ℝ ⊤ (fun τ : ℝ => (x, τ)) :=
    contDiff_const.prodMk contDiff_id
  -- t-slice ContDiffAt at t.
  have hr_t_slice : ContDiffAt ℝ 2 (fun τ : ℝ => sw.r x τ) t := by
    have h := hr_cda.comp t (h_slice_t.of_le le_top).contDiffAt
    exact h
  have hs_t_slice : ContDiffAt ℝ 2 (fun τ : ℝ => sw.s x τ) t := by
    have h := hs_cda.comp t (h_slice_t.of_le le_top).contDiffAt
    exact h
  -- spatial-slice ContDiffAt at x:  one_of in U as nbhd of (x,t).
  -- We get pointwise + eventually-nbhd versions.
  -- ContDiffAt 2 of slice at x.
  have hr_x_slice_at : ContDiffAt ℝ 2 (fun ξ : ℝ => sw.r ξ t) x := by
    exact hr_cda.comp x (h_slice_x.of_le le_top).contDiffAt
  have hs_x_slice_at : ContDiffAt ℝ 2 (fun ξ : ℝ => sw.s ξ t) x := by
    exact hs_cda.comp x (h_slice_x.of_le le_top).contDiffAt
  -- nbhd-eventually versions:  ContDiffAt 2 of slice on a nbhd of x.
  have h2_ne_omega : (2 : WithTop ℕ∞) ≠ ↑(⊤ : ℕ∞) := by decide
  have hr_x_slice_evt : ∀ᶠ ξ in 𝓝 x, ContDiffAt ℝ 2 (fun ξ' => sw.r ξ' t) ξ :=
    hr_x_slice_at.eventually h2_ne_omega
  have hs_x_slice_evt : ∀ᶠ ξ in 𝓝 x, ContDiffAt ℝ 2 (fun ξ' => sw.s ξ' t) ξ :=
    hs_x_slice_at.eventually h2_ne_omega
  -- Build SmoothEnoughAt.
  have h2_ne_0 : (2 : WithTop ℕ∞) ≠ 0 := by decide
  have h1_ne_0 : (1 : WithTop ℕ∞) ≠ 0 := by decide
  have h1p1_le_2 : (1 : WithTop ℕ∞) + 1 ≤ 2 := by norm_num
  let h_smooth : SmoothEnoughAt sw x t :=
    { hr_t := hr_t_slice.differentiableAt h2_ne_0
      hs_t := hs_t_slice.differentiableAt h2_ne_0
      hr_x_nbhd := by
        filter_upwards [hr_x_slice_evt] with ξ hξ
        exact hξ.differentiableAt h2_ne_0
      hs_x_nbhd := by
        filter_upwards [hs_x_slice_evt] with ξ hξ
        exact hξ.differentiableAt h2_ne_0
      hr_xx_nbhd := by
        -- At each ξ near x, sw.r ξ' ↦ ... is C² as a function of ξ',
        -- so its deriv is C¹, hence differentiable at ξ.
        filter_upwards [hr_x_slice_evt] with ξ hξ
        have h_deriv : ContDiffAt ℝ 1 (deriv (fun ξ' => sw.r ξ' t)) ξ :=
          hξ.derivWithin h1p1_le_2
        exact h_deriv.differentiableAt h1_ne_0
      hs_xx_nbhd := by
        filter_upwards [hs_x_slice_evt] with ξ hξ
        have h_deriv : ContDiffAt ℝ 1 (deriv (fun ξ' => sw.s ξ' t)) ξ :=
          hξ.derivWithin h1p1_le_2
        exact h_deriv.differentiableAt h1_ne_0 }
  -- Step 5.  Compose.
  refine ⟨sw, U, hU_open, h_xt_U, h_smooth, ?_, ?_⟩
  · -- Polar identity on U.
    intro q hq
    obtain ⟨q1, q2⟩ := q
    exact h_polar (q1, q2) hq
  · -- The PDE-bridge equivalence via the local headline.
    exact schrodinger_PDE_iff_HJ_continuity_at sw x t h_smooth

end UnifiedTheory.LayerB.LohmillerSlotineNodes
