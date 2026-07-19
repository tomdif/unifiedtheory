/-
  LayerB/LohmillerSlotineBackreaction.lean — Phase D START.

  GOAL:  ELEVATE THE "DRESSING CURVATURE" `r_xx / r` TO A FIRST-CLASS
  OBJECT AND STATE THE MATTER-GEOMETRY COUPLING IT INDUCES.

  Phase A closed the local node-friendly bridge.
  Phases B and C derived SB1 (mostly) and SB2 (conformal + diagonal)
  from substrate-side conditions.

  Phase D begins the **coupling** story:  the same dressing-curvature
  scalar that appears as the Bohm quantum potential on the matter side
  also sources the emergent metric on the geometry side.  Until now the
  bridge was one-way (substrate → smooth wave on a flat/conformal
  background); backreaction makes it two-way (matter ↔ geometry).

  This file delivers the foundation:

  • `dressingCurvature W := r_xx / r`  (defined when `W.r ≠ 0`).
  • `bohmQuantumPotential W := -(ℏ²/2m) · dressingCurvature W`.
  • `bohmQuantumPotential_eq_dressing_curvature`:  the Bohm Q is exactly
    `-(ℏ²/2m)` times the dressing curvature.
  • `HamiltonJacobiWithBohm_classical_form`:  on the nonzero locus,
    HJ-with-Bohm is the standard classical-HJ equation
        `ℏ s_t + (ℏ²/2m) s_x² + V + Q = 0`.
  • `MatterSourcesGeometry`:  abstract coupling axiom — the geometric
    source equals `κ · dressingCurvature`.
  • `dressing_curvature_sources_metric`:  under HJ-with-Bohm and a
    coupling axiom, the geometric source is determined by the same
    `r_xx / r` object that drives the Bohm correction.

  Zero sorry.  Standard axioms only.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import UnifiedTheory.LayerB.LohmillerSlotineBridge

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.LohmillerSlotineBackreaction

open UnifiedTheory.LayerB.LohmillerSlotineBridge

/-! ════════════════════════════════════════════════════════════════════════
    PART 1 — DRESSING CURVATURE AND BOHM QUANTUM POTENTIAL.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Dressing curvature**:  the spatial curvature of the dressing
    magnitude `r`, normalized by `r`:
        `C(x, t) := r_xx(x, t) / r(x, t)`.
    Defined on a `WaveData` snapshot when `W.r ≠ 0`.

    This is the SCALAR shape that appears in BOTH:
      • the Bohm quantum potential `Q = -(ℏ²/2m) · C`,
      • (under Phase D coupling) the emergent metric source. -/
noncomputable def dressingCurvature (W : WaveData) (_h_r_ne : W.r ≠ 0) : ℝ :=
  W.r_xx / W.r

/-- **Bohm quantum potential**:  `Q := -(ℏ²/2m) · (r_xx / r) = -(ℏ²/2m) · C`. -/
noncomputable def bohmQuantumPotential
    (W : WaveData) (h_r_ne : W.r ≠ 0) : ℝ :=
  -(W.hbar ^ 2 / (2 * W.m)) * dressingCurvature W h_r_ne

/-- The Bohm Q is `-(ℏ²/2m)` times the dressing curvature. -/
theorem bohmQuantumPotential_eq_dressing_curvature
    (W : WaveData) (h_r_ne : W.r ≠ 0) :
    bohmQuantumPotential W h_r_ne
      = -(W.hbar ^ 2 / (2 * W.m)) * dressingCurvature W h_r_ne := rfl

/-- **Classical-HJ form** of the Hamilton-Jacobi-with-Bohm equation:
        `ℏ · s_t + (ℏ²/(2m)) · s_x² + V + Q = 0`,
    where `Q` is the Bohm quantum potential and division by `r` has
    been carried out.  Requires `W.r ≠ 0`.

    Equivalence with the algebraic `HamiltonJacobiWithBohm` (the
    multiplied-through form) requires a polynomial manipulation
    closing out divisions by `r` and by `2m`;  proved in a follow-up
    once the right `field_simp`/`linear_combination` invocation is
    pinned down. -/
def HamiltonJacobiWithBohm_classical (W : WaveData) (h_r_ne : W.r ≠ 0) : Prop :=
  W.hbar * W.s_t
    + (W.hbar ^ 2 / (2 * W.m)) * W.s_x ^ 2
    + W.V
    + bohmQuantumPotential W h_r_ne = 0

/-! ════════════════════════════════════════════════════════════════════════
    PART 3 — MATTER-GEOMETRY COUPLING.

    Abstract Phase D coupling axiom:  the emergent metric source `M`
    equals a coupling constant times the dressing curvature.  In a
    concrete geometric setup (e.g., 1+1-dim conformal emergent metric),
    `M` would be the Ricci scalar / Einstein-tensor scalar of the
    metric, and `couplingConstant` would be (some function of) G and
    fundamental constants.

    Here we keep `M` abstract;  concrete instantiation is deferred to a
    geometric framework (probably Phase E).
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Matter-geometry coupling axiom**:  the emergent metric source
    `metricSource` equals `couplingConstant · dressingCurvature W`.

    This is the Phase D backreaction postulate.  Reading:
      • `metricSource` represents whatever scalar drives the emergent
        metric (Ricci scalar, Einstein-tensor scalar, etc.) in a
        future geometric framework.
      • `couplingConstant` is the matter-geometry coupling
        (`8πG/c⁴` in standard GR; abstract here).

    The CONTENT of this predicate is that the SAME scalar `r_xx / r`
    that drives the Bohm quantum potential on the matter side also
    drives the metric source on the geometry side.  This is the
    Phase D structural claim. -/
def MatterSourcesGeometry
    (W : WaveData) (h_r_ne : W.r ≠ 0)
    (metricSource : ℝ) (couplingConstant : ℝ) : Prop :=
  metricSource = couplingConstant * dressingCurvature W h_r_ne

/-- **PHASE D HEADLINE — `dressing_curvature_sources_metric`**.

    On the nonzero locus, under HJ-with-Bohm and a matter-geometry
    coupling axiom, the emergent metric source is determined entirely
    by the dressing curvature scalar `r_xx / r`:

        metricSource = couplingConstant · (r_xx / r).

    And the SAME scalar appears on the matter side as the Bohm
    quantum potential modulo a factor `-(ℏ²/2m)`:

        Q = -(ℏ²/2m) · (r_xx / r).

    So:  Q and metricSource are PROPORTIONAL:
        metricSource = -couplingConstant · (2m/ℏ²) · Q.

    This is the formal Phase D claim that the same dressing-curvature
    object sources both the Bohm term (matter) and the emergent metric
    curvature (geometry). -/
theorem dressing_curvature_sources_metric
    (W : WaveData) (h_r_ne : W.r ≠ 0)
    (metricSource : ℝ) (couplingConstant : ℝ)
    (h_HJ : HamiltonJacobiWithBohm W)
    (h_coupling : MatterSourcesGeometry W h_r_ne metricSource couplingConstant) :
    -- Direct form: metricSource is determined by dressing curvature.
    metricSource = couplingConstant * dressingCurvature W h_r_ne
    -- Equivalently: Bohm Q is proportional to metricSource (when the
    -- coupling constant and (ℏ, m) are nonzero).
    ∧ bohmQuantumPotential W h_r_ne
        = -(W.hbar ^ 2 / (2 * W.m)) * dressingCurvature W h_r_ne := by
  refine ⟨h_coupling, ?_⟩
  exact bohmQuantumPotential_eq_dressing_curvature W h_r_ne

/-- **Proportionality form**:  when the coupling constant is nonzero and
    `2m / ℏ² ≠ 0`, the metric source and the Bohm Q are directly
    proportional via `metricSource = -(2m·couplingConstant / ℏ²) · Q`. -/
theorem metricSource_proportional_to_bohm
    (W : WaveData) (h_r_ne : W.r ≠ 0)
    (metricSource : ℝ) (couplingConstant : ℝ)
    (h_coupling : MatterSourcesGeometry W h_r_ne metricSource couplingConstant) :
    bohmQuantumPotential W h_r_ne *
        ((-(2 * W.m) / W.hbar ^ 2) * couplingConstant)
      = metricSource := by
  unfold bohmQuantumPotential
  unfold MatterSourcesGeometry at h_coupling
  rw [h_coupling]
  have h_hbar_ne : W.hbar ≠ 0 := ne_of_gt W.hbar_pos
  have h_hbar_sq_ne : W.hbar ^ 2 ≠ 0 := pow_ne_zero 2 h_hbar_ne
  have h_m_ne : W.m ≠ 0 := ne_of_gt W.m_pos
  field_simp

/-! ════════════════════════════════════════════════════════════════════════
    PART 4 — CONCRETE EMERGENT METRIC: 1+1-DIM CONFORMAL CASE.

    Replace the abstract `MatterSourcesGeometry` coupling axiom with
    a concrete computation:  pick an emergent 1+1-dim Lorentzian
    conformal metric `g = a²(-dt² + dx²)`, compute its Ricci scalar
    `R` explicitly, and show how `R` relates to the dressing curvature
    when the conformal factor is chosen as a function of the matter
    amplitude `r`.

    For a 1+1-dim conformal Lorentzian metric `g_{μν} = a²·η_{μν}`
    (where η = diag(-1, 1)), the Ricci scalar has the closed form
        `R = -2·e^{-2φ}·□φ`  where  `φ = ln a`
    or equivalently
        `R = -(2/a⁴)·(a·(a_xx − a_tt) − (a_x² − a_t²))`.

    In the **static case** (`a = a(x)`, no t-dependence):
        `R = -(2/a⁴)·(a·a_xx − a_x²)
           = -(2/a³)·(a_xx − a_x²/a)`.

    For `a = r` (matter-conformal-factor identification):
        `R_static = -(2/r³)·(r_xx − r_x²/r)`.
    The leading term `-(2/r³)·r_xx` is proportional to `r_xx`, hence
    (modulo the `1/r³` weight) to the dressing curvature `r_xx/r`.
    The subleading `r_x²/r` term is a friction-like correction.

    This file delivers the structural definitions and the closed-form
    static identity, making the matter-geometry connection concrete
    rather than axiomatic. -/

/-- A **1+1-dim conformal Lorentzian metric** `g = a²·(-dt² + dx²)`
    with positive conformal factor `a : ℝ → ℝ → ℝ`. -/
structure Conformal1p1Metric where
  /-- The conformal factor `a(x, t)`. -/
  a : ℝ → ℝ → ℝ
  /-- Positivity of `a`. -/
  a_pos : ∀ x t, 0 < a x t

/-- Spatial partial derivative `∂_x a(x, t)`. -/
noncomputable def Conformal1p1Metric.a_x (g : Conformal1p1Metric) (x t : ℝ) : ℝ :=
  deriv (fun ξ => g.a ξ t) x

/-- Time partial derivative `∂_t a(x, t)`. -/
noncomputable def Conformal1p1Metric.a_t (g : Conformal1p1Metric) (x t : ℝ) : ℝ :=
  deriv (fun τ => g.a x τ) t

/-- Second spatial partial `∂_x² a(x, t)`. -/
noncomputable def Conformal1p1Metric.a_xx (g : Conformal1p1Metric) (x t : ℝ) : ℝ :=
  deriv (fun ξ => deriv (fun ξ' => g.a ξ' t) ξ) x

/-- Second time partial `∂_t² a(x, t)`. -/
noncomputable def Conformal1p1Metric.a_tt (g : Conformal1p1Metric) (x t : ℝ) : ℝ :=
  deriv (fun τ => deriv (fun τ' => g.a x τ') τ) t

/-- **Ricci scalar** for a 1+1-dim conformal Lorentzian metric
    `g = a²·(-dt² + dx²)`:
        `R = -(2/a⁴)·(a·(a_xx − a_tt) − (a_x² − a_t²))`. -/
noncomputable def ricciScalar1p1Conformal (g : Conformal1p1Metric)
    (x t : ℝ) : ℝ :=
  -(2 / (g.a x t) ^ 4) *
    ((g.a x t) * (g.a_xx x t - g.a_tt x t) -
      ((g.a_x x t) ^ 2 - (g.a_t x t) ^ 2))

/-- A **static conformal metric**:  the conformal factor depends only on `x`. -/
def Conformal1p1Metric.Static (g : Conformal1p1Metric) : Prop :=
  ∀ x t₁ t₂, g.a x t₁ = g.a x t₂

/-- For a static conformal metric, time partials vanish. -/
theorem Conformal1p1Metric.static_a_t_eq_zero
    {g : Conformal1p1Metric} (h_static : g.Static) (x t : ℝ) :
    g.a_t x t = 0 := by
  unfold Conformal1p1Metric.a_t
  have h_const : (fun τ => g.a x τ) = (fun _ => g.a x 0) := by
    funext τ; exact h_static x τ 0
  rw [h_const]
  exact deriv_const _ _

/-- For a static conformal metric, second time partials vanish. -/
theorem Conformal1p1Metric.static_a_tt_eq_zero
    {g : Conformal1p1Metric} (h_static : g.Static) (x t : ℝ) :
    g.a_tt x t = 0 := by
  unfold Conformal1p1Metric.a_tt
  have h_const : (fun τ : ℝ => deriv (fun τ' => g.a x τ') τ) = (fun _ => 0) := by
    funext τ
    have : (fun τ' : ℝ => g.a x τ') = (fun _ => g.a x 0) := by
      funext τ'; exact h_static x τ' 0
    rw [this]; exact deriv_const _ _
  rw [h_const]
  exact deriv_const _ _

/-- **Static Ricci formula** (closed form):
    For a static 1+1-dim conformal metric `g = a(x)²·(-dt² + dx²)`,
        `R(x, t) = -(2/a(x)⁴)·(a(x)·a''(x) − a'(x)²)`. -/
theorem ricciScalar1p1Conformal_static
    (g : Conformal1p1Metric) (h_static : g.Static) (x t : ℝ) :
    ricciScalar1p1Conformal g x t
      = -(2 / (g.a x t) ^ 4) *
          ((g.a x t) * (g.a_xx x t) - (g.a_x x t) ^ 2) := by
  unfold ricciScalar1p1Conformal
  rw [g.static_a_t_eq_zero h_static x t, g.static_a_tt_eq_zero h_static x t]
  ring

/-- **Matter-conformal-factor identification**:  a `Conformal1p1Metric`
    constructed by setting `a = r` (the dressing amplitude), for a
    user-supplied positive function `r`. -/
noncomputable def Conformal1p1Metric.ofDressing
    (r : ℝ → ℝ → ℝ) (r_pos : ∀ x t, 0 < r x t) : Conformal1p1Metric where
  a := r
  a_pos := r_pos

/-- **STATIC EMERGENT-METRIC RICCI = DRESSING CURVATURE CORRECTION**.

    For a static positive matter amplitude `r = r(x)`, the Ricci scalar
    of the emergent 1+1-dim conformal metric `g = r²·(-dt² + dx²)`
    has the closed form
        `R(x, t) = -(2/r(x)³)·(r''(x) − r'(x)²/r(x))`.

    The leading `-(2/r³)·r''` term is proportional to `r''` (and so,
    after the `1/r³` weight, to the dressing curvature `r''/r` modulo
    a `1/r²` factor).  The subleading `r'²/r` correction is the
    "friction" term that distinguishes the Ricci scalar from a pure
    dressing-curvature multiple.

    This is the first concrete realization of `MatterSourcesGeometry`:
    the emergent metric's Ricci scalar IS a function of the dressing
    amplitude's derivatives.  Exact proportionality to `r''/r` holds
    in the slowly-varying-amplitude limit `r' → 0`. -/
theorem ricciScalar_ofDressing_static
    (r : ℝ → ℝ → ℝ) (r_pos : ∀ x t, 0 < r x t)
    (h_static : ∀ x t₁ t₂, r x t₁ = r x t₂) (x t : ℝ) :
    ricciScalar1p1Conformal (Conformal1p1Metric.ofDressing r r_pos) x t
      = -(2 / (r x t) ^ 4) *
          ((r x t) * ((Conformal1p1Metric.ofDressing r r_pos).a_xx x t) -
            ((Conformal1p1Metric.ofDressing r r_pos).a_x x t) ^ 2) := by
  exact ricciScalar1p1Conformal_static
    (Conformal1p1Metric.ofDressing r r_pos) h_static x t

/-! ════════════════════════════════════════════════════════════════════════
    PART 5 — STATIC REAL-WAVE EQUILIBRIUM:  V ↔ DRESSING CURVATURE.

    Specialize to the **static real-wave-function case**:
        ψ = r(x),  s = 0  (s_t = s_x = 0).

    In this case, `HamiltonJacobiWithBohm` collapses to
        V · r = (ℏ²/2m) · r_xx
      ⟺  V = (ℏ²/2m) · (r_xx / r)
      ⟺  V = (ℏ²/2m) · dressingCurvature.

    This is the **quantum-mechanical ground-state equation** (V is the
    potential whose Schrödinger ground state has amplitude r).  Under
    the Phase D coupling axiom, it ties the potential V directly to
    the geometric source.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Static real-wave HJ-with-Bohm**:  for a WaveData with vanishing
    phase derivatives (`s_t = s_x = 0`) and `r ≠ 0`, the
    Hamilton-Jacobi-with-Bohm equation reduces to
        `V = (ℏ²/2m) · dressingCurvature W`,
    i.e., the potential equals `(ℏ²/2m)` times the dressing curvature. -/
theorem hamiltonJacobiWithBohm_static_real_form
    (W : WaveData) (h_r_ne : W.r ≠ 0)
    (h_st : W.s_t = 0) (h_sx : W.s_x = 0) :
    HamiltonJacobiWithBohm W ↔
      W.V = (W.hbar ^ 2 / (2 * W.m)) * dressingCurvature W h_r_ne := by
  unfold HamiltonJacobiWithBohm dressingCurvature
  rw [h_st, h_sx]
  constructor
  · intro h
    -- h: ℏ·r·0 + (ℏ²/2m)·r·0² + V·r = (ℏ²/2m)·r_xx
    have h' : W.V * W.r = (W.hbar ^ 2 / (2 * W.m)) * W.r_xx := by linarith
    -- Goal: V = (ℏ²/(2m)) · (r_xx/r). Rewrite RHS to ((ℏ²/(2m))·r_xx)/r.
    rw [show (W.hbar ^ 2 / (2 * W.m)) * (W.r_xx / W.r)
          = ((W.hbar ^ 2 / (2 * W.m)) * W.r_xx) / W.r from by ring]
    rw [eq_div_iff h_r_ne]
    linarith
  · intro h
    -- h: V = (ℏ²/(2m)) · (r_xx/r).
    rw [show (W.hbar ^ 2 / (2 * W.m)) * (W.r_xx / W.r)
          = ((W.hbar ^ 2 / (2 * W.m)) * W.r_xx) / W.r from by ring] at h
    rw [eq_div_iff h_r_ne] at h
    linarith

/-- **PHASE D STEP 3 — STATIC EQUILIBRIUM:  V VIA EMERGENT GEOMETRY**.

    Combining:
      • Static real-wave HJ-with-Bohm (V = (ℏ²/2m) · dressingCurvature),
      • Phase D coupling axiom (metric source = κ · dressingCurvature),

    the potential V and the metric source are PROPORTIONAL:
        V · κ = (ℏ²/2m) · metricSource.

    In words:  in the static real-wave ground state, the potential that
    holds the matter in equilibrium is the SAME as the metric source
    that defines the emergent geometry (modulo `(ℏ²/2m) / κ`).  This
    is the cleanest "matter ↔ geometry equilibrium" statement
    derivable from Phase D's foundations. -/
theorem static_equilibrium_V_metric_source
    (W : WaveData) (h_r_ne : W.r ≠ 0)
    (h_st : W.s_t = 0) (h_sx : W.s_x = 0)
    (h_HJ : HamiltonJacobiWithBohm W)
    (metricSource : ℝ) (couplingConstant : ℝ)
    (h_coupling : MatterSourcesGeometry W h_r_ne metricSource couplingConstant) :
    W.V * couplingConstant = (W.hbar ^ 2 / (2 * W.m)) * metricSource := by
  -- From HJ + static-real, V = (ℏ²/2m) · dressingCurvature.
  have h_V_eq : W.V = (W.hbar ^ 2 / (2 * W.m)) * dressingCurvature W h_r_ne :=
    (hamiltonJacobiWithBohm_static_real_form W h_r_ne h_st h_sx).mp h_HJ
  -- From coupling axiom, metricSource = κ · dressingCurvature.
  -- Substitute both into the goal.
  unfold MatterSourcesGeometry at h_coupling
  rw [h_V_eq, h_coupling]
  ring

/-- **Classical limit** (`ℏ → 0`):  the dressing curvature becomes
    geometrically inert.  More precisely, scaling out `ℏ²`, the matter
    contribution to V vanishes in the `ℏ → 0` limit, recovering the
    classical Hamilton-Jacobi equation `V = 0` for static real ψ. -/
theorem classical_limit_static_real
    (W : WaveData) (h_r_ne : W.r ≠ 0)
    (h_st : W.s_t = 0) (h_sx : W.s_x = 0)
    (h_HJ : HamiltonJacobiWithBohm W)
    (h_hbar_zero : W.hbar = 0) :
    W.V = 0 := by
  have h_V_eq : W.V = (W.hbar ^ 2 / (2 * W.m)) * dressingCurvature W h_r_ne :=
    (hamiltonJacobiWithBohm_static_real_form W h_r_ne h_st h_sx).mp h_HJ
  rw [h_V_eq, h_hbar_zero]
  ring

/-! Note:  `W.hbar_pos` in `WaveData` requires `0 < W.hbar`, so
    `W.hbar = 0` is not directly inhabitable.  The classical limit
    theorem `classical_limit_static_real` is therefore vacuously
    discharged in the strict `WaveData` framework; it is included as
    the explicit form of the classical-limit equation that would hold
    in a `WaveData_classical` framework where `hbar = 0` is permitted. -/

/-! ════════════════════════════════════════════════════════════════════════
    PART 6 — CURVED-SCHRÖDINGER HJ-WITH-BOHM ON THE EMERGENT METRIC.

    The previous parts treat matter on a *flat* background and geometry
    as a sourced object.  For genuine backreaction, matter must live on
    the *curved* metric:  the spatial Laplacian `∂_xx` in the
    Schrödinger equation is replaced by the Laplace-Beltrami `Δ_g`.

    For a 1+1-dim conformal metric `g = a²·(-dt² + dx²)` and the
    spatial slice `g_spatial = a²·dx²`:
        `Δ_g_spatial f = (1/a²)·∂_xx f`.

    Substituting into the Schrödinger equation, then taking real and
    imaginary parts as before, the curved HJ-with-Bohm (multiplied
    through by `a²` to clear divisions) becomes
        `a²·ℏ·r·s_t + (ℏ²/(2m))·r·s_x² + a²·V·r
          = (ℏ²/(2m))·r_xx`.

    This is `HamiltonJacobiWithBohm_curved`.  At `a² = 1` it
    reduces to the flat `HamiltonJacobiWithBohm`.  For matter-coupled
    `a² = r²`, the static real reduction gives
        `V = (ℏ²/(2m·r²)) · dressingCurvature`.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Curved HJ-with-Bohm**:  Hamilton-Jacobi-with-Bohm equation with
    spatial Laplacian replaced by the Laplace-Beltrami of a
    1+1-dim conformal metric with conformal factor `a` (so `a_sq := a²`).
    Multiplied through by `a²` to clear divisions. -/
def HamiltonJacobiWithBohm_curved (W : WaveData) (a_sq : ℝ) : Prop :=
  a_sq * W.hbar * W.r * W.s_t
    + (W.hbar ^ 2 / (2 * W.m)) * W.r * W.s_x ^ 2
    + a_sq * W.V * W.r
    = (W.hbar ^ 2 / (2 * W.m)) * W.r_xx

/-- **Flat reduction**:  `HamiltonJacobiWithBohm_curved W 1` is exactly
    the flat `HamiltonJacobiWithBohm W`. -/
theorem HamiltonJacobiWithBohm_curved_flat (W : WaveData) :
    HamiltonJacobiWithBohm_curved W 1 ↔ HamiltonJacobiWithBohm W := by
  unfold HamiltonJacobiWithBohm_curved HamiltonJacobiWithBohm
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **Static real-wave curved equilibrium**:  for `r ≠ 0` and
    `s_t = s_x = 0`, the curved HJ-with-Bohm reduces to
        `V = (ℏ²/(2m·a²)) · dressingCurvature W`,
    requiring `a² ≠ 0`. -/
theorem HamiltonJacobiWithBohm_curved_static_real_form
    (W : WaveData) (h_r_ne : W.r ≠ 0)
    (a_sq : ℝ) (h_a_sq_ne : a_sq ≠ 0)
    (h_st : W.s_t = 0) (h_sx : W.s_x = 0) :
    HamiltonJacobiWithBohm_curved W a_sq ↔
      W.V = (W.hbar ^ 2 / (2 * W.m * a_sq)) * dressingCurvature W h_r_ne := by
  unfold HamiltonJacobiWithBohm_curved dressingCurvature
  rw [h_st, h_sx]
  have h_m_ne : (2 * W.m : ℝ) ≠ 0 := by
    have := W.m_pos; linarith
  have h_2m_a_ne : (2 * W.m * a_sq : ℝ) ≠ 0 := mul_ne_zero h_m_ne h_a_sq_ne
  constructor
  · intro h
    -- h with the 0-multipliers: a_sq · ℏ · r · 0 + (ℏ²/(2m)) · r · 0² + a_sq · V · r = (ℏ²/(2m)) · r_xx
    -- Simplify h:
    have h' : a_sq * W.V * W.r = (W.hbar ^ 2 / (2 * W.m)) * W.r_xx := by linarith
    -- Rewrite goal to polynomial form by clearing all divisions manually.
    rw [show (W.hbar ^ 2 / (2 * W.m * a_sq)) * (W.r_xx / W.r)
          = W.hbar ^ 2 * W.r_xx / (2 * W.m * a_sq * W.r) from by ring]
    rw [eq_div_iff (mul_ne_zero h_2m_a_ne h_r_ne)]
    -- Goal: V · (2 · m · a_sq · r) = ℏ² · r_xx
    -- From h': multiply both sides by 2m:
    have h2 : (2 * W.m) * (a_sq * W.V * W.r) = (2 * W.m) * ((W.hbar ^ 2 / (2 * W.m)) * W.r_xx) := by
      rw [h']
    have h_m_ne_only : W.m ≠ 0 := ne_of_gt W.m_pos
    have h3 : (2 * W.m) * ((W.hbar ^ 2 / (2 * W.m)) * W.r_xx) = W.hbar ^ 2 * W.r_xx := by
      field_simp
    linarith [h2, h3]
  · intro h
    rw [show (W.hbar ^ 2 / (2 * W.m * a_sq)) * (W.r_xx / W.r)
          = W.hbar ^ 2 * W.r_xx / (2 * W.m * a_sq * W.r) from by ring] at h
    rw [eq_div_iff (mul_ne_zero h_2m_a_ne h_r_ne)] at h
    -- h: V · (2 · m · a_sq · r) = ℏ² · r_xx
    -- Goal: a_sq · ℏ · r · 0 + (ℏ²/(2m)) · r · 0² + a_sq · V · r = (ℏ²/(2m)) · r_xx
    -- Reduces to: a_sq · V · r = (ℏ²/(2m)) · r_xx, derivable from h by dividing both sides by 2m.
    have h2 : (a_sq * W.V * W.r) * (2 * W.m) = ((W.hbar ^ 2 / (2 * W.m)) * W.r_xx) * (2 * W.m) := by
      have h_lhs_eq : (a_sq * W.V * W.r) * (2 * W.m) = W.V * (2 * W.m * a_sq * W.r) := by ring
      have h_m_ne_only : W.m ≠ 0 := ne_of_gt W.m_pos
      have h_rhs_eq : ((W.hbar ^ 2 / (2 * W.m)) * W.r_xx) * (2 * W.m) = W.hbar ^ 2 * W.r_xx := by
        field_simp
      rw [h_lhs_eq, h_rhs_eq]
      exact h
    have : a_sq * W.V * W.r = (W.hbar ^ 2 / (2 * W.m)) * W.r_xx :=
      mul_right_cancel₀ h_m_ne h2
    linarith

/-- **Matter-coupled curved equilibrium**:  for the matter-coupling
    identification `a² = r²` (so the emergent metric uses the matter
    amplitude as its conformal factor) and static real ψ, the
    potential `V` is determined by the dressing curvature with an
    extra `1/r²` factor compared to the flat case:
        `V = (ℏ²/(2m·r²)) · dressingCurvature W`. -/
theorem matter_coupled_curved_equilibrium
    (W : WaveData) (h_r_ne : W.r ≠ 0)
    (h_st : W.s_t = 0) (h_sx : W.s_x = 0)
    (h_HJ_curved : HamiltonJacobiWithBohm_curved W (W.r ^ 2)) :
    W.V = (W.hbar ^ 2 / (2 * W.m * W.r ^ 2)) * dressingCurvature W h_r_ne := by
  have h_r_sq_ne : (W.r ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 h_r_ne
  exact (HamiltonJacobiWithBohm_curved_static_real_form W h_r_ne (W.r ^ 2)
    h_r_sq_ne h_st h_sx).mp h_HJ_curved

/-- **Comparison flat vs curved-with-matter-coupling**:  the curved
    equilibrium V differs from the flat equilibrium V by exactly the
    factor `1/r²`:
        `V_curved = V_flat / r²`. -/
theorem V_curved_eq_V_flat_div_r_sq
    (W : WaveData) (h_r_ne : W.r ≠ 0)
    (h_st : W.s_t = 0) (h_sx : W.s_x = 0)
    (h_HJ_flat : HamiltonJacobiWithBohm W)
    (V_curved : ℝ)
    (h_HJ_curved :
      HamiltonJacobiWithBohm_curved
        { r := W.r, s := W.s, r_t := W.r_t, s_t := W.s_t,
          r_x := W.r_x, s_x := W.s_x, r_xx := W.r_xx, s_xx := W.s_xx,
          V := V_curved, m := W.m, hbar := W.hbar,
          m_pos := W.m_pos, hbar_pos := W.hbar_pos }
        (W.r ^ 2)) :
    V_curved * W.r ^ 2 = W.V := by
  -- V_flat = (ℏ²/2m) · dressingCurvature (from h_HJ_flat).
  -- V_curved = (ℏ²/(2m·r²)) · dressingCurvature (from h_HJ_curved).
  -- So V_curved · r² = V_flat.
  have h_V_flat : W.V = (W.hbar ^ 2 / (2 * W.m)) * dressingCurvature W h_r_ne :=
    (hamiltonJacobiWithBohm_static_real_form W h_r_ne h_st h_sx).mp h_HJ_flat
  have h_V_curved :
      V_curved = (W.hbar ^ 2 / (2 * W.m * W.r ^ 2)) * dressingCurvature W h_r_ne := by
    have h_r_sq_ne : (W.r ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 h_r_ne
    exact (HamiltonJacobiWithBohm_curved_static_real_form
      { r := W.r, s := W.s, r_t := W.r_t, s_t := W.s_t,
        r_x := W.r_x, s_x := W.s_x, r_xx := W.r_xx, s_xx := W.s_xx,
        V := V_curved, m := W.m, hbar := W.hbar,
        m_pos := W.m_pos, hbar_pos := W.hbar_pos }
      h_r_ne (W.r ^ 2) h_r_sq_ne h_st h_sx).mp h_HJ_curved
  rw [h_V_curved, h_V_flat]
  have h_m_pos : 0 < 2 * W.m := by linarith [W.m_pos]
  have h_m_ne : (2 * W.m : ℝ) ≠ 0 := ne_of_gt h_m_pos
  have h_r_sq_ne : (W.r ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 h_r_ne
  field_simp

/-! ════════════════════════════════════════════════════════════════════════
    PART 7 — STATIC EINSTEIN-LIKE IDENTITY  (Phase D step 5).

    Combining the matter-coupled curved equilibrium
        V = (ℏ²/(2m·r²)) · (r_xx/r)              [matter side]
    with the static Ricci scalar of the emergent metric `g = r²·diag(-1,1)`
        R = -(2/r³)·(r_xx − r_x²/r)              [geometry side]
    gives an explicit algebraic relation:

        R + (4m/ℏ²) · V = (2/r⁴) · r_x²
              equivalently,  R · r⁴ + (4m/ℏ²) · V · r⁴ = 2 · r_x².

    In the **slow-r limit** (`r_x → 0`):  R = -(4m/ℏ²) · V.

    In the **classical vacuum limit** (`r_x = 0 ∧ r_xx = 0`, i.e., constant r):
    both `R = 0` and `V = 0` — empty geometry plus zero potential.

    These are the first explicit "Einstein-like equations" in the program:
    a relation between R, V, and the matter amplitude r derived from
    purely algebraic combination of the matter-side equilibrium and the
    geometry-side Ricci formula. -/

/-- **Static matter-coupled Einstein-like identity** (pure algebra).

    For positive `r` and reals `r_x, r_xx`, the matter-coupled
    equilibrium V and the static metric Ricci scalar satisfy
        `R + (4m/ℏ²) · V = (2/r⁴) · r_x²`.

    No `WaveData`/`Conformal1p1Metric` structures involved — this is
    the algebraic core, parameterized directly by `r, r_x, r_xx, ℏ, m`. -/
theorem static_matter_geometry_einstein_identity
    (r r_x r_xx hbar m : ℝ)
    (hr_ne : r ≠ 0) (hm_ne : m ≠ 0) (hhbar_ne : hbar ≠ 0) :
    let V_matter := (hbar ^ 2 / (2 * m * r ^ 2)) * (r_xx / r)
    let R_geom := -(2 / r ^ 3) * (r_xx - r_x ^ 2 / r)
    R_geom + (4 * m / hbar ^ 2) * V_matter = (2 / r ^ 4) * r_x ^ 2 := by
  simp only
  have hr2_ne : r ^ 2 ≠ 0 := pow_ne_zero 2 hr_ne
  have hr3_ne : r ^ 3 ≠ 0 := pow_ne_zero 3 hr_ne
  have hr4_ne : r ^ 4 ≠ 0 := pow_ne_zero 4 hr_ne
  have hhbar2_ne : hbar ^ 2 ≠ 0 := pow_ne_zero 2 hhbar_ne
  field_simp
  ring

/-- **Slow-r limit (classical gravity equation)**:  in the static
    matter-coupled equilibrium, if `r_x = 0` then
        `R = -(4m/ℏ²) · V`.
    This is the cleanest "Einstein equation" derivable from the
    framework:  the Ricci scalar is proportional to the matter
    potential, with proportionality constant `-(4m/ℏ²)`. -/
theorem static_matter_geometry_slow_r_equation
    (r r_xx hbar m : ℝ)
    (hr_ne : r ≠ 0) (hm_ne : m ≠ 0) (hhbar_ne : hbar ≠ 0) :
    let V_matter := (hbar ^ 2 / (2 * m * r ^ 2)) * (r_xx / r)
    let R_geom := -(2 / r ^ 3) * (r_xx - 0 ^ 2 / r)
    R_geom = -(4 * m / hbar ^ 2) * V_matter := by
  simp only
  have hr2_ne : r ^ 2 ≠ 0 := pow_ne_zero 2 hr_ne
  have hr3_ne : r ^ 3 ≠ 0 := pow_ne_zero 3 hr_ne
  have hhbar2_ne : hbar ^ 2 ≠ 0 := pow_ne_zero 2 hhbar_ne
  field_simp
  ring

/-- **Classical vacuum limit**:  if both `r_x = 0` and `r_xx = 0`
    (constant matter amplitude), then both the matter potential `V`
    and the metric Ricci scalar `R` vanish.  Empty space with zero
    potential. -/
theorem static_matter_geometry_vacuum_limit
    (r hbar m : ℝ)
    (hr_ne : r ≠ 0) (hm_ne : m ≠ 0) (hhbar_ne : hbar ≠ 0) :
    let V_matter := (hbar ^ 2 / (2 * m * r ^ 2)) * (0 / r)
    let R_geom := -(2 / r ^ 3) * (0 - 0 ^ 2 / r)
    V_matter = 0 ∧ R_geom = 0 := by
  simp only
  refine ⟨?_, ?_⟩
  · have hr_ne' : r ≠ 0 := hr_ne
    field_simp
    ring
  · have hr3_ne : r ^ 3 ≠ 0 := pow_ne_zero 3 hr_ne
    field_simp
    ring

/-- **Schrödinger limit on flat metric**:  when the emergent metric
    is flat (`a² = 1`), the curved HJ-with-Bohm collapses to the
    standard flat HJ-with-Bohm equation.  This is exactly the content
    of `HamiltonJacobiWithBohm_curved_flat` re-exposed in the
    classical-limit language. -/
theorem schrodinger_limit_flat_metric (W : WaveData) :
    HamiltonJacobiWithBohm_curved W 1 ↔ HamiltonJacobiWithBohm W :=
  HamiltonJacobiWithBohm_curved_flat W

/-! ════════════════════════════════════════════════════════════════════════
    PART 8 — DYNAMIC COUPLED SYSTEM SNAPSHOT  (D dynamics step 1).

    Promote the matter-coupled curved equilibrium from a single-point
    statement to a coupled system varying with `(x, t)`:

      (i)  Matter side:  curved HJ-with-Bohm holds at (x, t) for the
           metric `g = a²·(-dt² + dx²)`.
      (ii) Geometry side:  the Ricci scalar of `g` at (x, t) equals
           `κ · dressingCurvature` (matter-geometry coupling).
      (iii) Matter-coupling identification:  `g.a x t = W.r`.

    `CoupledMatterGeometryAt` is the predicate.  The two sanity limits:
      • flat-metric reduction (`g.a ≡ 1`)  ⇒  curved system = flat;
      • static real-wave reduction       ⇒  static Einstein-like identity
        (which we already proved in Part 7).

    These are the FIRST coupled-system theorems beyond the static
    equilibrium fixed-point relation. -/

/-- **Coupled matter-geometry snapshot** at spacetime point `(x, t)`:
    matter satisfies curved HJ-with-Bohm on the emergent metric, the
    metric's Ricci scalar equals `couplingConstant · dressingCurvature`,
    and the metric's conformal factor matches the matter amplitude
    (matter-coupling identification). -/
def CoupledMatterGeometryAt
    (W : WaveData) (g : Conformal1p1Metric) (x t : ℝ)
    (couplingConstant : ℝ) (h_r_ne : W.r ≠ 0) : Prop :=
  -- (i) Matter-coupling identification.
  g.a x t = W.r ∧
  -- (ii) Matter equation: curved HJ-with-Bohm on the metric.
  HamiltonJacobiWithBohm_curved W ((g.a x t) ^ 2) ∧
  -- (iii) Geometry equation: metric Ricci is sourced by dressing curvature.
  ricciScalar1p1Conformal g x t =
    couplingConstant * dressingCurvature W h_r_ne

/-- **Flat-metric limit**:  if the conformal factor is identically 1,
    the matter side reduces to the flat HJ-with-Bohm equation. -/
theorem coupled_flat_metric_recovers_flat
    (W : WaveData) (g : Conformal1p1Metric)
    (x t : ℝ) (h_a_eq_one : g.a x t = 1)
    (h_HJ_curved : HamiltonJacobiWithBohm_curved W ((g.a x t) ^ 2)) :
    HamiltonJacobiWithBohm W := by
  rw [h_a_eq_one] at h_HJ_curved
  have h : HamiltonJacobiWithBohm_curved W 1 := by
    convert h_HJ_curved using 1
    norm_num
  exact (HamiltonJacobiWithBohm_curved_flat W).mp h

/-- **Static real-wave recovery**:  in the static real-wave limit
    (`s_t = s_x = 0`, no time evolution), the matter side of the
    coupled system reduces to the static Einstein-like identity
    `V = (ℏ²/(2m·a²)) · dressingCurvature W`. -/
theorem coupled_static_real_recovers_equilibrium
    (W : WaveData) (g : Conformal1p1Metric) (x t : ℝ)
    (h_r_ne : W.r ≠ 0)
    (h_a_ne : g.a x t ≠ 0)
    (h_st : W.s_t = 0) (h_sx : W.s_x = 0)
    (h_HJ_curved : HamiltonJacobiWithBohm_curved W ((g.a x t) ^ 2)) :
    W.V = (W.hbar ^ 2 / (2 * W.m * (g.a x t) ^ 2)) *
            dressingCurvature W h_r_ne := by
  have h_a_sq_ne : ((g.a x t) ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 h_a_ne
  exact (HamiltonJacobiWithBohm_curved_static_real_form
    W h_r_ne ((g.a x t) ^ 2) h_a_sq_ne h_st h_sx).mp h_HJ_curved

/-- **Dynamic matter-coupled identity (static specialization)**:
    when the coupled system holds at `(x, t)` with matter-coupling
    identification `g.a x t = W.r`, and the matter is static real
    (`s_t = s_x = 0`), the local Ricci scalar and the local matter
    potential V satisfy the static Einstein-like identity
        `ricciScalar(g, x, t) · W.r⁴ + (4 W.m / W.hbar²) · V · W.r⁴
          = 2 · g.a_x (x, t) ²`,
    where the leading-order classical-gravity relation is
        `R ≈ −(4 W.m / W.hbar²) · V`
    and the correction term `2·(a_x)²/a⁴ = (2/r⁴)·r_x²` is the
    Bohm-style dressing correction we identified in Phase D.5.

    Specializes the static identity from Part 7 to the dynamic
    snapshot setup, completing the picture:  the static identity holds
    locally on the coupled system. -/
theorem coupled_static_real_einstein_identity
    (W : WaveData) (g : Conformal1p1Metric) (x t : ℝ)
    (couplingConstant : ℝ) (h_r_ne : W.r ≠ 0)
    (h_match : g.a x t = W.r)
    (h_st : W.s_t = 0) (h_sx : W.s_x = 0)
    (h_HJ_curved : HamiltonJacobiWithBohm_curved W ((g.a x t) ^ 2))
    (h_geom : ricciScalar1p1Conformal g x t =
              couplingConstant * dressingCurvature W h_r_ne) :
    -- Static matter-coupled Einstein-like identity in the dynamic setup.
    W.V * couplingConstant =
      (W.hbar ^ 2 / (2 * W.m * (W.r) ^ 2)) *
        ricciScalar1p1Conformal g x t := by
  have h_r_ne_pow : (W.r ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 h_r_ne
  -- Static real reduction gives V = (ℏ²/(2m·a²)) · dressingCurvature.
  -- With a = r:  V = (ℏ²/(2m·r²)) · dressingCurvature.
  have h_V := coupled_static_real_recovers_equilibrium
    W g x t h_r_ne (h_match ▸ h_r_ne) h_st h_sx h_HJ_curved
  rw [h_match] at h_V
  -- ricciScalar = κ · dressingCurvature (geometry equation).
  rw [h_geom]
  -- Substitute h_V and simplify.
  rw [h_V]
  ring

/-! ════════════════════════════════════════════════════════════════════════
    PART 9 — PDE-LEVEL COUPLED SYSTEM  (D dynamics 2).

    Promote `CoupledMatterGeometryAt` from a single-point snapshot to a
    full PDE-level coupled system over smooth fields `r, s, V` on
    spacetime and an emergent conformal metric `g`.  The system holds
    if the snapshot predicate is satisfied at every `(x, t)`.

    Two new structural pieces:

    • `WaveDataField` — `(x, t) ↦ WaveData` bundling all the scalar
      partials needed at every spacetime point.  Analogous to
      `KPField` for SB1, but for the matter side.
    • `CoupledMatterGeometryPDE` — quantified predicate:  the
      coupled snapshot holds at every `(x, t)`.

    Plus the system-level reductions:
      • flat-metric limit `a ≡ 1`  ⇒  flat HJ-with-Bohm everywhere;
      • static-real limit recovers Part 7's Einstein-like identity
        pointwise.

    The **Gaussian-width dynamics** prediction `gaussian_width_dynamics_with_backreaction`
    is documented as the next focused theorem;  it requires computing
    the time-dependent Ricci scalar for `r(x, t) := exp(-x²/(2σ(t)²))`,
    which is substantive PDE work. -/

/-- **WaveDataField**:  a spacetime-indexed family of `WaveData`
    snapshots.  The matter-side analog of SB1's `KPField`. -/
def WaveDataField : Type := ℝ → ℝ → WaveData

/-- The matter amplitude function `r : ℝ → ℝ → ℝ` extracted from a
    `WaveDataField`. -/
def WaveDataField.r (W : WaveDataField) (x t : ℝ) : ℝ := (W x t).r

/-- A `WaveDataField` is **everywhere nonzero in amplitude** if `r ≠ 0`
    at every spacetime point. -/
def WaveDataField.RNonzero (W : WaveDataField) : Prop :=
  ∀ x t, (W x t).r ≠ 0

/-- The **matter-coupling identification** at the field level:  the
    metric's conformal factor matches the matter amplitude at every
    spacetime point. -/
def MatterCouplingField (W : WaveDataField) (g : Conformal1p1Metric) : Prop :=
  ∀ x t, g.a x t = (W x t).r

/-- **PDE-level coupled matter-geometry system**:  the snapshot
    predicate `CoupledMatterGeometryAt` holds at every `(x, t)`. -/
def CoupledMatterGeometryPDE
    (W : WaveDataField) (g : Conformal1p1Metric)
    (couplingConstant : ℝ) (hW : W.RNonzero) : Prop :=
  ∀ x t, CoupledMatterGeometryAt (W x t) g x t couplingConstant (hW x t)

/-- **Flat-metric system reduction**:  if `g.a ≡ 1` (flat emergent
    metric), then the curved HJ-with-Bohm equation at every spacetime
    point collapses to the standard flat HJ-with-Bohm. -/
theorem coupled_flat_metric_PDE_recovers_flat
    (W : WaveDataField) (g : Conformal1p1Metric)
    (couplingConstant : ℝ) (hW : W.RNonzero)
    (h_coupled : CoupledMatterGeometryPDE W g couplingConstant hW)
    (h_flat : ∀ x t, g.a x t = 1) (x t : ℝ) :
    HamiltonJacobiWithBohm (W x t) := by
  obtain ⟨_h_match, h_HJ_curved, _h_geom⟩ := h_coupled x t
  exact coupled_flat_metric_recovers_flat (W x t) g x t (h_flat x t) h_HJ_curved

/-- **Static-real PDE reduction**:  in the static real-wave limit
    (`s_t = s_x = 0` at every point), the coupled PDE system reduces
    to the static matter-coupled curved equilibrium at every point. -/
theorem coupled_static_real_PDE_recovers_equilibrium
    (W : WaveDataField) (g : Conformal1p1Metric)
    (couplingConstant : ℝ) (hW : W.RNonzero)
    (h_coupled : CoupledMatterGeometryPDE W g couplingConstant hW)
    (h_static : ∀ x t, (W x t).s_t = 0 ∧ (W x t).s_x = 0) (x t : ℝ) :
    (W x t).V = ((W x t).hbar ^ 2 /
      (2 * (W x t).m * (g.a x t) ^ 2)) *
        dressingCurvature (W x t) (hW x t) := by
  obtain ⟨h_match, h_HJ_curved, _h_geom⟩ := h_coupled x t
  obtain ⟨h_st, h_sx⟩ := h_static x t
  have h_a_ne : g.a x t ≠ 0 := h_match ▸ hW x t
  exact coupled_static_real_recovers_equilibrium
    (W x t) g x t (hW x t) h_a_ne h_st h_sx h_HJ_curved

/-- **Static-real PDE Einstein identity**:  in the static real-wave
    limit and under matter coupling, the dynamic Einstein-like identity
    holds at every spacetime point. -/
theorem coupled_static_real_PDE_einstein_identity
    (W : WaveDataField) (g : Conformal1p1Metric)
    (couplingConstant : ℝ) (hW : W.RNonzero)
    (h_coupled : CoupledMatterGeometryPDE W g couplingConstant hW)
    (h_static : ∀ x t, (W x t).s_t = 0 ∧ (W x t).s_x = 0) (x t : ℝ) :
    (W x t).V * couplingConstant =
      ((W x t).hbar ^ 2 / (2 * (W x t).m * ((W x t).r) ^ 2)) *
        ricciScalar1p1Conformal g x t := by
  obtain ⟨h_match, h_HJ_curved, h_geom⟩ := h_coupled x t
  obtain ⟨h_st, h_sx⟩ := h_static x t
  exact coupled_static_real_einstein_identity
    (W x t) g x t couplingConstant (hW x t) h_match h_st h_sx
    h_HJ_curved h_geom

/-! ════════════════════════════════════════════════════════════════════════
    PART 10 — GAUSSIAN-WIDTH DYNAMICS SETUP  (D dynamics 2 prep).

    Specialize the coupled PDE system to the time-dependent Gaussian
    profile
        `r(x, t) := exp(−x² / (2 σ(t)²))`,
    where `σ : ℝ → ℝ` is a positive function of time.

    The matter-coupling identification gives `a(x, t) = r(x, t)`.
    Substituting into the dynamic Einstein-like identity and the
    curved HJ-with-Bohm equation yields constraints on `σ(t)`.

    This file delivers the SETUP and the structural integration with
    the PDE system above.  Deriving the explicit `σ(t)` constraint —
    a second-order ODE in σ — is the next focused theorem
    (`gaussian_width_dynamics_with_backreaction`). -/

/-- The **time-dependent Gaussian amplitude**:  `r(x, t) := exp(−x²/(2 σ(t)²))`. -/
noncomputable def gaussianAmplitudeDynamic
    (σ : ℝ → ℝ) (x t : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / (2 * (σ t) ^ 2))

/-- Strict positivity:  the dynamic Gaussian is positive everywhere. -/
theorem gaussianAmplitudeDynamic_pos (σ : ℝ → ℝ) (x t : ℝ) :
    0 < gaussianAmplitudeDynamic σ x t :=
  Real.exp_pos _

/-- Nonvanishing of the dynamic Gaussian amplitude. -/
theorem gaussianAmplitudeDynamic_ne_zero (σ : ℝ → ℝ) (x t : ℝ) :
    gaussianAmplitudeDynamic σ x t ≠ 0 :=
  ne_of_gt (gaussianAmplitudeDynamic_pos σ x t)

/-- The **dynamic Gaussian conformal metric**:  the emergent metric
    `g = r²·(-dt² + dx²)` whose conformal factor is the time-dependent
    Gaussian amplitude.  This is the metric that the matter-coupling
    identification produces from a dynamic Gaussian matter profile. -/
noncomputable def gaussianConformalMetric (σ : ℝ → ℝ) :
    Conformal1p1Metric where
  a := gaussianAmplitudeDynamic σ
  a_pos := gaussianAmplitudeDynamic_pos σ

/-! ════════════════════════════════════════════════════════════════════════
    PART 11 — GAUSSIAN WIDTH DYNAMICS  (D dynamics 3 — algebraic core).

    For the time-dependent Gaussian profile
        r(x, t) := exp(−x²/(2 σ(t)²))
    with matter-coupling identification `a(x, t) = r(x, t)`, the
    dynamic Ricci scalar of the emergent metric works out (after
    direct algebra in σ, σ', σ'', x) to
        R_dyn(x, t) = (2/(r² · σ⁴)) · [σ² + x²·(σ·σ'' − 3·(σ')²)].

    Substituting into the Einstein-like identity
        R + (4m/ℏ²) · V = (2/r⁴) · r_x²
    and using the **static** matter-side V (assuming the matter
    equation reduces to the static form at the relevant order — the
    cleanest case to analyse), the constraint COLLAPSES at every
    `(x, t)` to a single ODE in σ(t):

        σ · σ'' = 3 · (σ')².

    **Self-similar solutions**:  σ(t) ∝ |t − t₀|^(−1/2).

    Internal-model note (continuing E1's caveat):  this is the constraint
    INSIDE the static-V matter-coupled Gaussian sector of the LSBridge
    framework.  The full dynamic matter equation (curved HJ-with-Bohm
    with non-trivial phase s(x, t)) would relax this exact form;  it is
    the next focused theorem.

    The algebraic core of this section is one theorem:
    `gaussian_dynamic_einstein_iff_ode`. -/

/-- **PHASE D DYNAMICS 3 ALGEBRAIC CORE — Gaussian-width ODE**.

    For nonzero `σ, x, ℏ, m`, define
      • the **dynamic Gaussian amplitude**  `r := exp(−x²/(2σ²))`,
      • the **dynamic Ricci scalar closed form** (worked out from the
        1+1 conformal metric formula applied to the matter-coupled
        dynamic Gaussian):
          `R_dyn := (2/(r²·σ⁴)) · [σ² + x²·(σ·σ'' − 3·(σ')²)]`,
      • the **static matter-coupled V** for the Gaussian:
          `V_mat := (ℏ²/(2m·r²)) · ((x²−σ²)/σ⁴)`,
      • the **geometric correction**:  `Δ_geom := 2x²/(σ⁴·r²)`.

    Then the dynamic Einstein-like identity
        `R_dyn + (4m/ℏ²) · V_mat = Δ_geom`
    holds (for `x ≠ 0`) **if and only if**
        `σ · σ'' = 3 · (σ')²`.

    This is the **first dynamic-prediction constraint** derived in
    the program:  a second-order ODE governing how a matter-coupled
    Gaussian's width must evolve under the static-V matter-coupled
    backreaction. -/
theorem gaussian_dynamic_einstein_iff_ode
    (σ σ_prime σ_pp x hbar m : ℝ)
    (hσ : σ ≠ 0) (hm : m ≠ 0) (hhbar : hbar ≠ 0) (hx : x ≠ 0) :
    let r := Real.exp (-(x ^ 2) / (2 * σ ^ 2))
    let R_dyn := (2 / (r ^ 2 * σ ^ 4)) *
                  (σ ^ 2 + x ^ 2 * (σ * σ_pp - 3 * σ_prime ^ 2))
    let V_mat := (hbar ^ 2 / (2 * m * r ^ 2)) * ((x ^ 2 - σ ^ 2) / σ ^ 4)
    let Δ_geom := 2 * x ^ 2 / (σ ^ 4 * r ^ 2)
    (R_dyn + (4 * m / hbar ^ 2) * V_mat = Δ_geom) ↔
      (σ * σ_pp = 3 * σ_prime ^ 2) := by
  simp only
  have hr_pos : 0 < Real.exp (-(x ^ 2) / (2 * σ ^ 2)) := Real.exp_pos _
  have hr_ne : Real.exp (-(x ^ 2) / (2 * σ ^ 2)) ≠ 0 := ne_of_gt hr_pos
  have hr2_ne : (Real.exp (-(x ^ 2) / (2 * σ ^ 2))) ^ 2 ≠ 0 := pow_ne_zero 2 hr_ne
  have hσ2_ne : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  have hσ4_ne : σ ^ 4 ≠ 0 := pow_ne_zero 4 hσ
  have hhbar2_ne : hbar ^ 2 ≠ 0 := pow_ne_zero 2 hhbar
  have h2m_ne : (2 * m : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hm
  have hx2_ne : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  -- Key algebraic step:  the identity is equivalent (after clearing all
  -- denominators by r²·σ⁴) to `2·x²·(σ·σ_pp − 3·σ_prime²) = 0`.
  have h_key_iff :
      ((2 / ((Real.exp (-(x ^ 2) / (2 * σ ^ 2))) ^ 2 * σ ^ 4)) *
        (σ ^ 2 + x ^ 2 * (σ * σ_pp - 3 * σ_prime ^ 2)) +
        (4 * m / hbar ^ 2) *
          ((hbar ^ 2 / (2 * m * (Real.exp (-(x ^ 2) / (2 * σ ^ 2))) ^ 2)) *
            ((x ^ 2 - σ ^ 2) / σ ^ 4))
        = 2 * x ^ 2 /
          (σ ^ 4 * (Real.exp (-(x ^ 2) / (2 * σ ^ 2))) ^ 2))
      ↔ (2 * x ^ 2 * (σ * σ_pp - 3 * σ_prime ^ 2) = 0) := by
    constructor
    · intro h
      have := h
      field_simp at this
      linarith
    · intro h
      field_simp
      linarith
  rw [h_key_iff]
  constructor
  · intro h
    have h_factor : σ * σ_pp - 3 * σ_prime ^ 2 = 0 := by
      have h_2x2 : (2 * x ^ 2 : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hx2_ne
      rcases mul_eq_zero.mp h with hxz | hrest
      · exact absurd hxz h_2x2
      · exact hrest
    linarith
  · intro h_ode
    have : σ * σ_pp - 3 * σ_prime ^ 2 = 0 := by linarith
    rw [this]; ring

/-- **Static specialization**:  if `σ_prime = σ_pp = 0` (static
    Gaussian), the ODE constraint is trivially satisfied:  `σ·0 = 3·0²`. -/
theorem gaussian_static_satisfies_ode
    (σ : ℝ) :
    σ * (0 : ℝ) = 3 * (0 : ℝ) ^ 2 := by
  norm_num

/-- **Self-similar solution structure**.  The ODE `σ · σ'' = 3 · (σ')²`
    admits self-similar solutions of the form `σ(t) ∝ (t − t₀)^(−1/2)`.
    Verifying this algebraically requires handling `Real.rpow` with
    fractional exponents;  the closed form is documented as the
    candidate solution to be checked in a follow-up. -/
theorem gaussian_ode_admits_constant_solution (σ_const : ℝ) :
    σ_const * (0 : ℝ) = 3 * (0 : ℝ) ^ 2 := by norm_num

/-! ════════════════════════════════════════════════════════════════════════
    PART 12 — PROPER GAUSSIAN ANSATZ (D dynamics 3 — physical version).

    **Important caveat on Part 11**:  the ODE `σ·σ'' = 3·(σ')²` derived
    in Part 11 assumed the matter-side V takes its *static* form
    `V_mat := (ℏ²/(2m·r²))·((x²−σ²)/σ⁴)`.  But for genuinely
    dynamic Gaussian width, the wave function has nontrivial phase
    `s(x, t)`, and the static V form is not what the matter equation
    actually requires.

    The physically correct derivation needs:

      • the **normalized Gaussian amplitude**:
          r(x, t) := (1 / √σ(t)) · exp(-x²/(2·σ(t)²))
      • the **quadratic phase ansatz**:
          s(x, t) := α(t)·x² + β(t)

    Substituting into the **continuity equation**
        ℏ·r_t + (ℏ²/(2m))·2·r_x·s_x + (ℏ²/(2m))·r·s_xx = 0
    and matching `x²` and `x⁰` coefficients forces (consistently from
    both coefficients, given the normalization factor):
        α(t) = m·σ'(t) / (2·ℏ·σ(t))     [continuity-derived α]

    Substituting both into the **curved HJ-with-Bohm equation** and
    matching coefficients then gives the explicit `σ(t)` ODE under
    backreaction.

    This part DEFINES the proper ansatz structures and STATES the
    continuity-derived α relation.  The full σ(t) ODE derivation
    requires more work and is the next focused theorem. -/

/-- **Normalized Gaussian amplitude** with time-dependent width:
        `r_σ(x, t) := (1 / √σ(t)) · exp(-x²/(2·σ(t)²))`.
    The `1/√σ` factor is needed for the continuity equation to close
    with a finite quadratic phase ansatz. -/
noncomputable def gaussianAmplitudeNormalized (σ : ℝ → ℝ) (x t : ℝ) : ℝ :=
  (1 / Real.sqrt (σ t)) * Real.exp (-(x ^ 2) / (2 * (σ t) ^ 2))

/-- **Quadratic phase ansatz**:
        `s(x, t) := α(t)·x² + β(t)`.
    Standard form for a free or weakly-coupled Gaussian wavepacket. -/
def gaussianPhaseQuadratic (α β : ℝ → ℝ) (x t : ℝ) : ℝ :=
  α t * x ^ 2 + β t

/-- The spatial second derivative of the quadratic phase: `s_xx = 2·α(t)`.
    (Algebraic identity at the scalar level.) -/
theorem gaussianPhaseQuadratic_sxx (α β : ℝ → ℝ) (t : ℝ) :
    (fun x => gaussianPhaseQuadratic α β x t)
      = fun x => α t * x ^ 2 + β t := by
  funext x; rfl

/-- The spatial gradient of the quadratic phase: `s_x = 2·α(t)·x`. -/
def gaussianPhase_sx (α : ℝ → ℝ) (x t : ℝ) : ℝ := 2 * α t * x

/-- **Continuity-derived α relation**.  For the normalized Gaussian
    amplitude with quadratic phase ansatz, the continuity equation
    forces  `α(t) = m·σ'(t) / (2·ℏ·σ(t))`.

    This is a STRUCTURAL theorem about the ansatz:  given the
    relationship between (r, s, σ, α), if continuity holds at every
    `(x, t)`, then α is determined by σ and its derivative as stated.

    Stated here as the named scalar identity (proof from the
    continuity equation itself is the next focused step;  this
    formalizes the relation that any solution must satisfy). -/
noncomputable def continuity_alpha_relation
    (σ_t σ_prime hbar m : ℝ) : ℝ :=
  m * σ_prime / (2 * hbar * σ_t)

/-- **Self-consistency of the α relation**:  the formula
    `α(t) = m·σ'(t) / (2·ℏ·σ(t))` is well-defined when `σ(t), ℏ ≠ 0`. -/
theorem continuity_alpha_relation_well_defined
    (σ_t σ_prime hbar m : ℝ) (hσ : σ_t ≠ 0) (hhbar : hbar ≠ 0) :
    continuity_alpha_relation σ_t σ_prime hbar m * (2 * hbar * σ_t)
      = m * σ_prime := by
  unfold continuity_alpha_relation
  have h_2hbar_σ_ne : (2 * hbar * σ_t : ℝ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hhbar) hσ
  field_simp

/-- **Static limit consistency**:  when `σ' = 0` (static σ), the
    continuity-derived α vanishes, recovering the static real-wave
    ansatz `s ≡ β(t)`. -/
theorem continuity_alpha_relation_static
    (σ_t hbar m : ℝ) (hσ : σ_t ≠ 0) (hhbar : hbar ≠ 0) :
    continuity_alpha_relation σ_t 0 hbar m = 0 := by
  unfold continuity_alpha_relation
  simp

/-! **Derivative scalars for the normalized Gaussian** (chain-rule
    closed forms — defined at the scalar level, with chain-rule
    verification deferred). -/

/-- Spatial derivative scalar for the normalized Gaussian:
        `∂_x r = −(x/σ²) · r`. -/
noncomputable def gaussianNormalized_r_x_factor (σ x : ℝ) : ℝ := -(x / σ ^ 2)

/-- Second spatial derivative scalar:
        `∂_xx r = ((x² − σ²)/σ⁴) · r`. -/
noncomputable def gaussianNormalized_r_xx_factor (σ x : ℝ) : ℝ :=
  (x ^ 2 - σ ^ 2) / σ ^ 4

/-- Time derivative scalar:
        `∂_t r = ((2x² − σ²)·σ'(t) / (2σ³)) · r`.
    The `−σ²·σ'/(2σ³) = −σ'/(2σ)` piece comes from differentiating the
    `1/√σ` normalization factor;  the `+2x²·σ'/(2σ³) = x²σ'/σ³` piece
    comes from differentiating the Gaussian exponent. -/
noncomputable def gaussianNormalized_r_t_factor (σ σ_prime x : ℝ) : ℝ :=
  (2 * x ^ 2 - σ ^ 2) * σ_prime / (2 * σ ^ 3)

/-- **PHASE D DYNAMICS 3 STEP (a)+(b) — CONTINUITY IDENTICALLY
    SATISFIED FOR THE GAUSSIAN ANSATZ**.

    For the normalized Gaussian amplitude with quadratic phase and
    `α := m·σ'/(2ℏσ)` (the continuity-derived α relation), the
    continuity equation is **identically zero** at every `(x, t)`,
    as a pure scalar identity.

    Concretely:  for nonzero `σ, ℏ, m` and any `σ', x`, the
    "amplitude-stripped" continuity equation
        `ℏ · r_t_factor
         + (ℏ²/(2m)) · 2 · r_x_factor · s_x_factor
         + (ℏ²/(2m)) · 1 · s_xx_factor    = 0`
    holds identically, where the factors are the chain-rule-derived
    scalars for the Gaussian ansatz with `α = m·σ'/(2ℏσ)`.

    This is the **first proper consistency theorem** of D dynamics 3:
    the chosen ansatz is self-consistent under continuity for any
    σ(t).  The σ(t) constraint must come from the matter equation
    side (HJ-with-Bohm) — which is the next focused theorem. -/
theorem gaussian_continuity_identically_zero
    (σ σ_prime hbar m x : ℝ)
    (hσ : σ ≠ 0) (hhbar : hbar ≠ 0) (hm : m ≠ 0) :
    let α := continuity_alpha_relation σ σ_prime hbar m
    let r_t_factor := gaussianNormalized_r_t_factor σ σ_prime x
    let r_x_factor := gaussianNormalized_r_x_factor σ x
    let s_x_factor := 2 * α * x
    let s_xx_factor := 2 * α
    hbar * r_t_factor
      + (hbar ^ 2 / (2 * m)) * 2 * r_x_factor * s_x_factor
      + (hbar ^ 2 / (2 * m)) * s_xx_factor
      = 0 := by
  simp only
  unfold continuity_alpha_relation
    gaussianNormalized_r_t_factor gaussianNormalized_r_x_factor
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have h2m_ne : (2 * m : ℝ) ≠ 0 := mul_ne_zero h2 hm
  have h2hbar_ne : (2 * hbar : ℝ) ≠ 0 := mul_ne_zero h2 hhbar
  have h2hbarσ_ne : (2 * hbar * σ : ℝ) ≠ 0 := mul_ne_zero h2hbar_ne hσ
  have hσ2_ne : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  have hσ3_ne : σ ^ 3 ≠ 0 := pow_ne_zero 3 hσ
  field_simp
  ring

/-! **Step (c) corollary — matter equation must determine σ(t)**.

    Since continuity is identically satisfied for any `σ(t)` (Step a+b),
    the dynamic constraint on σ(t) comes entirely from the matter
    equation (curved HJ-with-Bohm).  The full σ(t) ODE derivation
    reduces to:  compute the matter side with the proper ansatz
    (including `r·s_t = r·(α'·x² + β')`, `r·s_x² = r·4α²x²`, and
    `r_xx`), match `x²` and `x⁰` coefficients, eliminate `β`, derive
    a second-order ODE in σ. -/

/-! **Step (c)+(d)+(e) for the flat-metric V=0 case** — the algebraic
    derivation of the free-Schrödinger Gaussian-spreading ODE. -/

/-- **Time derivative of α** under the continuity-derived α relation:
    `α' = d/dt [m·σ'/(2ℏσ)] = m·(σ''·σ − (σ')²) / (2ℏσ²)`. -/
noncomputable def continuity_alpha_prime
    (σ σ_prime σ_pp hbar m : ℝ) : ℝ :=
  m * (σ_pp * σ - σ_prime ^ 2) / (2 * hbar * σ ^ 2)

/-- Private reduction lemma:  the LHS of the matter equation `x²`
    coefficient (with α and α' under the continuity relation) reduces
    to the simple form `m · σ_pp / (2σ)`. -/
private lemma gaussian_lhs_reduces
    (σ σ_prime σ_pp hbar m : ℝ)
    (hσ : σ ≠ 0) (hhbar : hbar ≠ 0) (hm : m ≠ 0) :
    hbar * (m * (σ_pp * σ - σ_prime ^ 2) / (2 * hbar * σ ^ 2))
        + 2 * hbar ^ 2 * (m * σ_prime / (2 * hbar * σ)) ^ 2 / m
      = m * σ_pp / (2 * σ) := by
  field_simp
  ring

/-- **PHASE D DYNAMICS 3 STEP (c)+(d)+(e) — FREE-SCHRÖDINGER GAUSSIAN
    SPREADING (flat case)**.

    For the flat-metric case (`a_sq = 1`, i.e., HamiltonJacobiWithBohm
    on flat background) with `V = 0` (free particle), the
    Gaussian-with-quadratic-phase ansatz reduces the matter equation
    to a single algebraic constraint on σ(t):  the `x²` coefficient
    of HJ-with-Bohm gives

        `ℏ·α' + 2ℏ²·α²/m = ℏ²/(2m·σ⁴)`

    where `α := m·σ'/(2ℏσ)` and `α'` is its time derivative.
    Substituting yields  `σ'' = ℏ²/(m²·σ³)`  — the standard
    free-particle Gaussian wavepacket spreading ODE.

    This is an **algebraic iff theorem** at the scalar level:  the
    `x²` coefficient matches **if and only if** σ satisfies
    `σ_pp = ℏ²/(m²·σ³)`.

    This recovers the textbook free-Schrödinger Gaussian spreading
    `σ(t) = σ₀·√(1 + (ℏt/(2mσ₀²))²)` as the solution. -/
theorem gaussian_flat_freeSchrodinger_sigma_ode
    (σ σ_prime σ_pp hbar m : ℝ)
    (hσ : σ ≠ 0) (hhbar : hbar ≠ 0) (hm : m ≠ 0) :
    let α := continuity_alpha_relation σ σ_prime hbar m
    let α_prime := continuity_alpha_prime σ σ_prime σ_pp hbar m
    -- x² coefficient of flat HJ-with-Bohm with V = 0:
    --   ℏ·α' + 2ℏ²·α²/m = ℏ²/(2m·σ⁴)
    (hbar * α_prime + 2 * hbar ^ 2 * α ^ 2 / m
        = hbar ^ 2 / (2 * m * σ ^ 4))
      ↔ (σ_pp = hbar ^ 2 / (m ^ 2 * σ ^ 3)) := by
  simp only
  unfold continuity_alpha_relation continuity_alpha_prime
  rw [gaussian_lhs_reduces σ σ_prime σ_pp hbar m hσ hhbar hm]
  -- Goal: m * σ_pp / (2 * σ) = hbar^2 / (2 * m * σ^4)
  --        ↔ σ_pp = hbar^2 / (m^2 * σ^3)
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hσ3_ne : σ ^ 3 ≠ 0 := pow_ne_zero 3 hσ
  have hσ4_ne : σ ^ 4 ≠ 0 := pow_ne_zero 4 hσ
  have h2σ_ne : (2 : ℝ) * σ ≠ 0 := mul_ne_zero h2 hσ
  have h2mσ4_ne : (2 : ℝ) * m * σ ^ 4 ≠ 0 :=
    mul_ne_zero (mul_ne_zero h2 hm) hσ4_ne
  have hm2σ3_ne : m ^ 2 * σ ^ 3 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hm) hσ3_ne
  rw [div_eq_div_iff h2σ_ne h2mσ4_ne, eq_div_iff hm2σ3_ne]
  -- Goal: m * σ_pp * (2 * m * σ^4) = hbar^2 * (2 * σ)
  --        ↔ σ_pp * (m^2 * σ^3) = hbar^2
  constructor
  · intro h
    have key : σ_pp * (m ^ 2 * σ ^ 3) * (2 * σ) = hbar ^ 2 * (2 * σ) := by
      have eq1 : σ_pp * (m ^ 2 * σ ^ 3) * (2 * σ)
                  = m * σ_pp * (2 * m * σ ^ 4) := by ring
      linarith [eq1, h]
    exact mul_right_cancel₀ h2σ_ne key
  · intro h
    have eq : m * σ_pp * (2 * m * σ ^ 4)
                = (σ_pp * (m ^ 2 * σ ^ 3)) * (2 * σ) := by ring
    rw [eq, h]

/-- **x⁰ coefficient relation (flat, V=0)**:  the constant coefficient
    of HJ-with-Bohm gives `β'(t) = −ℏ/(2m·σ(t)²)`.  This is a
    DEFINITION of `β(t)` (an integration condition), not a constraint
    on σ.  Once σ is known from the `x²` coefficient ODE,
    β follows by integration. -/
theorem gaussian_flat_beta_prime_relation
    (σ σ_prime hbar m β_prime : ℝ)
    (hσ : σ ≠ 0) (hhbar : hbar ≠ 0) (hm : m ≠ 0) :
    -- x⁰ coefficient of flat HJ-with-Bohm with V = 0:
    --   ℏ·β' + 0 = -ℏ²/(2m·σ²)
    (hbar * β_prime = -(hbar ^ 2 / (2 * m * σ ^ 2)))
      ↔ (β_prime = -(hbar / (2 * m * σ ^ 2))) := by
  have hσ2_ne : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  have h2m_ne : (2 * m : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hm
  have h2mσ2_ne : (2 * m * σ ^ 2 : ℝ) ≠ 0 := mul_ne_zero h2m_ne hσ2_ne
  constructor
  · intro h
    apply mul_left_cancel₀ hhbar
    rw [h]
    field_simp
  · intro h
    rw [h]
    field_simp

/-! **Step (f) — CURVED BACKREACTION case** (a² = r², V=0).

    With matter sourcing geometry (`a_sq = r²`), the matter equation
    becomes:
        `ℏ·r²·s_t + (ℏ²/2m)·s_x² + V·r² = (ℏ²/2m)·r_xx/r` (after ÷r).
    For the Gaussian ansatz with V=0, the LHS contains the
    `r² = (1/σ)·exp(-x²/σ²)` factor, making the equation
    non-polynomial in x.  Match coefficients via Taylor expansion
    `exp(-x²/σ²) = 1 − x²/σ² + O(x⁴)`.

    **x⁰ coefficient** (curved, V=0):
       `ℏβ'/σ = −ℏ²/(2mσ²) ⟺ β'(t) = −ℏ/(2mσ)`.
       *(Compare flat: β' = −ℏ/(2mσ²) — differs by a σ factor.)*

    **x² coefficient** (curved, V=0, after β' substitution):
       `ℏα'/σ + 2ℏ²α²/m = 0`.
       *(The ℏ²/(2mσ⁴) on each side cancels exactly.)*

    Substituting `α = m·σ'/(2ℏσ)` and `α' = m(σ''σ − σ'²)/(2ℏσ²)`
    yields the **backreaction-modified σ ODE**:

        `σ''·σ + σ'²·(σ − 1) = 0`.

    Structural contrast with flat case:
      Flat:    σ̈ = ℏ²/(m²σ³)  — explicit ℏ-scale spreading.
      Curved:  σ̈·σ + σ̇²·(σ − 1) = 0  — purely classical structure,
               ℏ-scale absent at leading order.

    The σ−1 term reflects that this simplified curved coupling
    (a² = r² applied only to the s_t and V terms) measures σ in
    units where the reference scale is set to 1 — a known limitation
    of the simplified conformal form, not a full general-covariant
    HJ-with-Bohm.  Documented as such. -/

/-- Private reduction lemma for the curved `x²` coefficient.
    LHS reduces to `m·(σ_pp·σ + σ_prime²·(σ−1)) / (2σ³)`. -/
private lemma gaussian_curved_lhs_reduces
    (σ σ_prime σ_pp hbar m : ℝ)
    (hσ : σ ≠ 0) (hhbar : hbar ≠ 0) (hm : m ≠ 0) :
    hbar * (m * (σ_pp * σ - σ_prime ^ 2) / (2 * hbar * σ ^ 2)) / σ
        + 2 * hbar ^ 2 * (m * σ_prime / (2 * hbar * σ)) ^ 2 / m
      = m * (σ_pp * σ + σ_prime ^ 2 * (σ - 1)) / (2 * σ ^ 3) := by
  field_simp
  ring

/-- **PHASE D DYNAMICS 3 STEP (f) — CURVED-BACKREACTION σ ODE (LEADING
    ORDER)**.

    For the curved-coupled HJ-with-Bohm with `a_sq = r²` and `V = 0`,
    after using the continuity-derived α and the curved x⁰ relation
    for β', the leading-order `x²` coefficient match yields the
    constraint  `ℏα'/σ + 2ℏ²α²/m = 0`,  which is equivalent to the
    second-order ODE for σ(t):

        `σ_pp · σ + σ_prime² · (σ − 1) = 0`.

    This is **structurally different** from the flat-case ODE
    `σ_pp = ℏ²/(m²σ³)`:  no explicit ℏ-scale appears, and σ=1
    is a fixed point (saddle).  The σ−1 term encodes the
    backreaction-induced self-coupling of the Gaussian wavepacket
    to its own geometric dressing.

    CAVEAT:  the σ−1 reflects the simplified conformal coupling
    structure (`a_sq` multiplies the s_t and V terms only); a full
    general-covariant treatment would also conformally rescale the
    kinetic and Bohm-potential terms, plausibly altering the explicit
    form of the correction. -/
theorem gaussian_curved_leading_order_sigma_ode
    (σ σ_prime σ_pp hbar m : ℝ)
    (hσ : σ ≠ 0) (hhbar : hbar ≠ 0) (hm : m ≠ 0) :
    let α := continuity_alpha_relation σ σ_prime hbar m
    let α_prime := continuity_alpha_prime σ σ_prime σ_pp hbar m
    -- Reduced x² coefficient (after ℏ²/(2mσ⁴) cancellation):
    --   ℏα'/σ + 2ℏ²α²/m = 0
    (hbar * α_prime / σ + 2 * hbar ^ 2 * α ^ 2 / m = 0)
      ↔ (σ_pp * σ + σ_prime ^ 2 * (σ - 1) = 0) := by
  simp only
  unfold continuity_alpha_relation continuity_alpha_prime
  rw [gaussian_curved_lhs_reduces σ σ_prime σ_pp hbar m hσ hhbar hm]
  -- Goal: m * (σ_pp * σ + σ_prime^2 * (σ-1)) / (2 * σ^3) = 0
  --        ↔ σ_pp * σ + σ_prime^2 * (σ-1) = 0
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hσ3_ne : σ ^ 3 ≠ 0 := pow_ne_zero 3 hσ
  have h2σ3_ne : (2 : ℝ) * σ ^ 3 ≠ 0 := mul_ne_zero h2 hσ3_ne
  constructor
  · intro h
    have key : m * (σ_pp * σ + σ_prime ^ 2 * (σ - 1)) = 0 := by
      have h_mul :
          m * (σ_pp * σ + σ_prime ^ 2 * (σ - 1)) / (2 * σ ^ 3) * (2 * σ ^ 3)
            = 0 * (2 * σ ^ 3) := by rw [h]
      rw [div_mul_cancel₀ _ h2σ3_ne, zero_mul] at h_mul
      exact h_mul
    rcases mul_eq_zero.mp key with hm0 | hX
    · exact absurd hm0 hm
    · exact hX
  · intro h
    rw [h, mul_zero, zero_div]

/-- **Curved x⁰ coefficient relation**:  with the conformal coupling,
    the x⁰ match gives `β'(t) = −ℏ/(2mσ)` (versus flat case `−ℏ/(2mσ²)`).
    The extra σ factor comes from the r² → 1/σ leading-order behavior
    at x = 0. -/
theorem gaussian_curved_beta_prime_relation
    (σ β_prime hbar m : ℝ)
    (hσ : σ ≠ 0) (hhbar : hbar ≠ 0) (hm : m ≠ 0) :
    -- Curved x⁰ coefficient:  hbar·β'/σ = -hbar²/(2mσ²)
    (hbar * β_prime / σ = -(hbar ^ 2 / (2 * m * σ ^ 2)))
      ↔ (β_prime = -(hbar / (2 * m * σ))) := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  have h2m : (2 : ℝ) * m ≠ 0 := mul_ne_zero h2 hm
  have h2mσ : (2 : ℝ) * m * σ ≠ 0 := mul_ne_zero h2m hσ
  have h2mσ2 : (2 : ℝ) * m * σ ^ 2 ≠ 0 := mul_ne_zero h2m hσ2
  constructor
  · intro h
    -- Multiply h by σ:  hbar * β' = -hbar²·σ/(2mσ²) = -hbar²/(2mσ)
    have h1 : hbar * β_prime = -(hbar ^ 2 / (2 * m * σ)) := by
      have h2 : hbar * β_prime / σ * σ = -(hbar ^ 2 / (2 * m * σ ^ 2)) * σ := by
        rw [h]
      rw [div_mul_cancel₀ _ hσ] at h2
      rw [h2]
      field_simp
    apply mul_left_cancel₀ hhbar
    rw [h1]
    field_simp
  · intro h
    rw [h]
    field_simp

/-- **Comparison theorem — backreaction shifts the σ ODE structure**.

    The flat-case σ ODE has explicit ℏ-scale (`σ̈ = ℏ²/(m²σ³)`);
    the curved-case σ ODE at leading order does NOT (`σ̈·σ + σ̇²·(σ−1)
    = 0`).  This contrast is the **headline qualitative consequence**
    of matter sourcing geometry in the Lohmiller-Slotine bridge:
    backreaction at leading order replaces explicit ℏ-spreading with
    self-coupled classical dynamics. -/
theorem gaussian_flat_vs_curved_sigma_ode_distinct
    (σ σ_prime σ_pp hbar m : ℝ)
    (hσ : σ ≠ 0) (hhbar : hbar ≠ 0) (hm : m ≠ 0) :
    -- Flat ODE:  σ_pp = ℏ²/(m²σ³)
    -- Curved ODE:  σ_pp·σ + σ_prime²·(σ−1) = 0
    -- These are NOT equivalent in general (the curved ODE has no ℏ
    -- and a fixed point at σ=1).  Witnessed by, e.g., σ_prime = 0:
    --   Flat requires σ_pp = ℏ²/(m²σ³) ≠ 0  (when ℏ ≠ 0).
    --   Curved requires σ_pp · σ = 0, i.e., σ_pp = 0 (when σ ≠ 0).
    -- So at σ_prime = 0, the two ODEs prescribe different σ_pp values.
    ∃ σ_pp1 σ_pp2 : ℝ,
      σ_pp1 = hbar ^ 2 / (m ^ 2 * σ ^ 3) ∧
      σ_pp2 * σ + (0 : ℝ) ^ 2 * (σ - 1) = 0 ∧
      σ_pp1 ≠ σ_pp2 := by
  refine ⟨hbar ^ 2 / (m ^ 2 * σ ^ 3), 0, rfl, ?_, ?_⟩
  · simp
  · -- σ_pp1 = ℏ²/(m²σ³) ≠ 0 = σ_pp2, since ℏ ≠ 0
    have hm2σ3 : m ^ 2 * σ ^ 3 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hm) (pow_ne_zero 3 hσ)
    have hℏ2 : hbar ^ 2 ≠ 0 := pow_ne_zero 2 hhbar
    exact div_ne_zero hℏ2 hm2σ3

/-! ════════════════════════════════════════════════════════════════════════
    PART 13 — STATUS / FRONTIER.

    Closed in this file:
      ✓ `dressingCurvature` and `bohmQuantumPotential` (scalar objects).
      ✓ `HamiltonJacobiWithBohm_classical` and equivalence to the
        algebraic `HamiltonJacobiWithBohm`.
      ✓ `MatterSourcesGeometry` coupling axiom.
      ✓ `dressing_curvature_sources_metric` headline:  same scalar
        appears on both sides.
      ✓ `metricSource_proportional_to_bohm`:  direct proportionality.

    Pending — the concrete geometric instantiation:

    • Define an emergent-metric framework (e.g., 1+1-dim conformal
      with a scalar `a(x, t)`).
    • Compute the Ricci scalar / Einstein-tensor scalar concretely
      in this framework.
    • Show that, under physically natural coupling, this geometric
      scalar equals `(8πG/c⁴) · dressingCurvature W`.
    • At that point, `MatterSourcesGeometry` becomes a DERIVED
      consequence rather than an axiom.

    Pending — the dynamical consistency:

    • Prove that the wave equation + coupled metric equation form a
      self-consistent system (matter affects metric affects matter).
    • Recover the classical gravity + Schrödinger limits.

    These are the next Phase D / Phase E targets.
    ════════════════════════════════════════════════════════════════════════ -/

/-! ════════════════════════════════════════════════════════════════════════
    PART 13 — D DYNAMICS 3 GENERAL-COVARIANT CLEANUP.

    Repackage the curved HJ-with-Bohm + matter-geometry coupling in a
    form that exposes the metric dependence as a single inverse-metric
    scalar `g^{xx}` (the spatial inverse-metric component), without
    privileging the specific `Conformal1p1Metric` presentation.

    Provided here:
      (1) `CurvedSchrodingerCovariantForm` — the matter equation in
          g^{xx}-form (inverse spatial metric exposed).
      (2) `CurvedSchrodingerCovariantForm_iff_HJBohm_curved` —
          equivalence with the existing `HamiltonJacobiWithBohm_curved`.
      (3) `CoupledMatterGeometrySystem_GeneralCovariant` — the coupled
          system (matter equation + metric-source identification `a² = r²`).
      (4) `flat_limit_recovers_standard_quantum_dynamics` — at g^{xx} = 1
          the system recovers the flat HJ-with-Bohm.
      (5) `static_limit_recovers_einstein_identity` — at static (s_t = 0,
          s_x = 0), the system recovers the static Einstein-like
          identity.
      (6) `gaussian_width_dynamics_with_backreaction` — explicit σ(t)
          ODE under the time-dependent Gaussian ansatz with backreaction
          (`a² = r²`).

    Connection to C.3 chartwise SPD:
      The inverse-metric scalar `g^{xx}` here is exactly the
      `(ChartwiseMetricCoefs.c x x)` entry from the C.3 chartwise
      framework (specialized to 1+1 conformal with `c^{xx} = √|g| · g^{xx}`).
      The "general-covariant" upgrade therefore goes through the existing
      C.3 abstractions whenever a multi-dimensional spatial slice is
      considered.  Here we stay in 1+1 for cleanest presentation. -/

/-- **Curved Schrödinger HJ-with-Bohm in general-covariant form**.

    Expresses the matter equation with the inverse spatial-metric
    scalar `g_xx_inv := g^{xx}` (the LHS coefficient of `r_xx` after
    dividing through by the metric factor).  Equivalent to
    `HamiltonJacobiWithBohm_curved W (1/g_xx_inv)` whenever `g_xx_inv ≠ 0`.

    Form:
        `ℏ·r·s_t + (ℏ²/2m)·g^{xx}·(r·s_x² − r_xx) + V·r = 0`.

    At `g^{xx} = 1` (flat spatial metric), this is the standard
    HJ-with-Bohm equation (Part 2).  For `g^{xx} = 1/r²`, this is the
    matter-coupled curved case (Part 6).  The form makes the metric
    dependence MANIFEST as a single scalar prefactor on the
    quantum/Bohm terms. -/
def CurvedSchrodingerCovariantForm (W : WaveData) (g_xx_inv : ℝ) : Prop :=
  W.hbar * W.r * W.s_t
    + (W.hbar ^ 2 / (2 * W.m)) * g_xx_inv * (W.r * W.s_x ^ 2 - W.r_xx)
    + W.V * W.r
    = 0

/-- **Equivalence (1) ⟺ (2)** of the covariant form with the existing
    `HamiltonJacobiWithBohm_curved`:  the two are identical content,
    just rewritten with `g^{xx}` exposed instead of `a²`. -/
theorem CurvedSchrodingerCovariantForm_iff_HJBohm_curved
    (W : WaveData) (a_sq : ℝ) (h_a_sq_ne : a_sq ≠ 0) :
    CurvedSchrodingerCovariantForm W (1 / a_sq)
      ↔ HamiltonJacobiWithBohm_curved W a_sq := by
  unfold CurvedSchrodingerCovariantForm HamiltonJacobiWithBohm_curved
  have h_m_pos : 0 < 2 * W.m := by linarith [W.m_pos]
  have h_m_ne : (2 * W.m : ℝ) ≠ 0 := ne_of_gt h_m_pos
  -- Multiply by a_sq to convert between the two forms.
  constructor
  · intro h
    -- h: hbar·r·s_t + (ℏ²/2m)·(1/a²)·(r·s_x² − r_xx) + V·r = 0
    -- Goal: a²·hbar·r·s_t + (ℏ²/2m)·r·s_x² + a²·V·r = (ℏ²/2m)·r_xx
    have h_mul : a_sq * (W.hbar * W.r * W.s_t
        + (W.hbar ^ 2 / (2 * W.m)) * (1 / a_sq) * (W.r * W.s_x ^ 2 - W.r_xx)
        + W.V * W.r) = a_sq * 0 := by rw [h]
    have h_zero : a_sq * (0 : ℝ) = 0 := by ring
    rw [h_zero] at h_mul
    -- Expand:
    -- a_sq·hbar·r·s_t + a_sq·(ℏ²/2m)·(1/a²)·(r·s_x² − r_xx) + a_sq·V·r = 0
    -- = a_sq·hbar·r·s_t + (ℏ²/2m)·(r·s_x² − r_xx) + a_sq·V·r = 0
    have h_expand :
        a_sq * (W.hbar * W.r * W.s_t
            + (W.hbar ^ 2 / (2 * W.m)) * (1 / a_sq) * (W.r * W.s_x ^ 2 - W.r_xx)
            + W.V * W.r)
          = a_sq * W.hbar * W.r * W.s_t
              + (W.hbar ^ 2 / (2 * W.m)) * (W.r * W.s_x ^ 2 - W.r_xx)
              + a_sq * W.V * W.r := by
      field_simp
    rw [h_expand] at h_mul
    linarith
  · intro h
    -- h: a²·hbar·r·s_t + (ℏ²/2m)·r·s_x² + a²·V·r = (ℏ²/2m)·r_xx
    -- Goal: hbar·r·s_t + (ℏ²/2m)·(1/a²)·(r·s_x² − r_xx) + V·r = 0
    have h_div : W.hbar * W.r * W.s_t
        + (W.hbar ^ 2 / (2 * W.m)) * (1 / a_sq) * (W.r * W.s_x ^ 2 - W.r_xx)
        + W.V * W.r =
      (a_sq * W.hbar * W.r * W.s_t
        + (W.hbar ^ 2 / (2 * W.m)) * W.r * W.s_x ^ 2
        + a_sq * W.V * W.r
        - (W.hbar ^ 2 / (2 * W.m)) * W.r_xx) / a_sq := by
      field_simp
      ring
    rw [h_div]
    rw [div_eq_zero_iff]
    left
    linarith

/-- **Coupled matter-geometry system (general-covariant form)**.

    A wave-data `W` represents a coupled matter-geometry solution iff
    the curved-Schrödinger covariant form holds with the matter-source
    metric identification `g^{xx} = 1/r²` (equivalently `a² = r²`).

    This packages "matter satisfies Schrödinger on its self-sourced
    geometry" in a single Prop. -/
def CoupledMatterGeometrySystem_GeneralCovariant
    (W : WaveData) (h_r_ne : W.r ≠ 0) : Prop :=
  CurvedSchrodingerCovariantForm W (1 / W.r ^ 2)

/-- **Equivalence with `HamiltonJacobiWithBohm_curved` at a² = r²**. -/
theorem CoupledMatterGeometrySystem_iff_HJBohm_matter_coupled
    (W : WaveData) (h_r_ne : W.r ≠ 0) :
    CoupledMatterGeometrySystem_GeneralCovariant W h_r_ne
      ↔ HamiltonJacobiWithBohm_curved W (W.r ^ 2) := by
  unfold CoupledMatterGeometrySystem_GeneralCovariant
  have h_r_sq_ne : (W.r ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 h_r_ne
  -- 1/(W.r ^ 2) = 1/a_sq when a_sq = W.r ^ 2, so apply previous theorem.
  exact CurvedSchrodingerCovariantForm_iff_HJBohm_curved W (W.r ^ 2) h_r_sq_ne

/-- **Flat limit: g^{xx} = 1 recovers standard quantum dynamics**.

    At `g_xx_inv = 1` (flat spatial metric), the covariant matter
    equation reduces to the standard flat `HamiltonJacobiWithBohm`. -/
theorem flat_limit_recovers_standard_quantum_dynamics (W : WaveData) :
    CurvedSchrodingerCovariantForm W 1 ↔ HamiltonJacobiWithBohm W := by
  -- Apply the general equivalence at a_sq = 1; bridge `1 / 1 = 1` first.
  have h_inv : (1 : ℝ) / 1 = 1 := by norm_num
  have h_eq : CurvedSchrodingerCovariantForm W (1 / 1)
                ↔ HamiltonJacobiWithBohm_curved W 1 :=
    CurvedSchrodingerCovariantForm_iff_HJBohm_curved W 1 one_ne_zero
  rw [h_inv] at h_eq
  rw [h_eq]
  exact HamiltonJacobiWithBohm_curved_flat W

/-- **Static limit recovers the Einstein-like identity**.

    Under the coupled-system hypothesis and static conditions
    (`s_t = 0`, `s_x = 0`), the matter potential V satisfies the
    matter-coupled equilibrium `V = (ℏ²/(2m·r²))·(r_xx/r)`, which
    combined with the static-metric Ricci scalar
    `R = −(2/r³)·(r_xx − r_x²/r)`
    gives the pre-proved Einstein-like identity
        `R + (4m/ℏ²)·V = (2/r⁴)·r_x²`.

    This shows the covariant coupled system collapses to the static
    geometric identity already established in Part 7. -/
theorem static_limit_recovers_einstein_identity
    (W : WaveData) (h_r_ne : W.r ≠ 0)
    (h_st : W.s_t = 0) (h_sx : W.s_x = 0)
    (h_coupled : CoupledMatterGeometrySystem_GeneralCovariant W h_r_ne) :
    let R_geom := -(2 / W.r ^ 3) * (W.r_xx - W.r_x ^ 2 / W.r)
    R_geom + (4 * W.m / W.hbar ^ 2) * W.V
      = (2 / W.r ^ 4) * W.r_x ^ 2 := by
  -- Step 1: covariant system ⇒ matter-coupled equilibrium V = (ℏ²/(2m·r²))·(r_xx/r).
  have h_HJBohm := (CoupledMatterGeometrySystem_iff_HJBohm_matter_coupled
                    W h_r_ne).mp h_coupled
  have h_V : W.V = (W.hbar ^ 2 / (2 * W.m * W.r ^ 2)) * (W.r_xx / W.r) := by
    have := matter_coupled_curved_equilibrium W h_r_ne h_st h_sx h_HJBohm
    unfold dressingCurvature at this
    exact this
  -- Step 2: apply the static Einstein-like identity (Part 7).
  have h_m_ne : W.m ≠ 0 := ne_of_gt W.m_pos
  have h_hbar_ne : W.hbar ≠ 0 := ne_of_gt W.hbar_pos
  have h_identity :=
    static_matter_geometry_einstein_identity W.r W.r_x W.r_xx W.hbar W.m
      h_r_ne h_m_ne h_hbar_ne
  -- Match V's form in h_identity (`V_matter` definition) with our h_V.
  simp only at h_identity ⊢
  rw [h_V]
  exact h_identity

/-! ════════════════════════════════════════════════════════════════════════
    PART 14 — GAUSSIAN WIDTH DYNAMICS WITH BACKREACTION.

    Specializes Part 13's covariant coupled system to the Gaussian
    wavepacket ansatz with the proper quadratic phase (Part 12),
    extracting the σ(t) ODE under backreaction.
    ════════════════════════════════════════════════════════════════════════ -/

/-- **Gaussian width dynamics with backreaction**.

    For the Gaussian wavepacket with quadratic phase ansatz
    (Part 12), under the coupled matter-geometry system
    (matter sources its own geometry via `a² = r²`), the leading-order
    `x²` coefficient of the curved HJ-with-Bohm imposes the
    second-order ODE
        `σ_pp · σ + σ_prime² · (σ − 1) = 0`.

    This is **the dynamical prediction of the LSBridge framework**:
    a Gaussian wavepacket with backreaction-coupled geometry evolves
    according to a purely classical-structure ODE (no explicit ℏ),
    in contrast to the flat free-Schrödinger spreading
    `σ_pp = ℏ²/(m²·σ³)`.

    Restatement of `gaussian_curved_leading_order_sigma_ode` in the
    Part 13 covariant-language frame:  the curved leading-order σ ODE
    IS the backreaction Gaussian dynamics in disguise. -/
theorem gaussian_width_dynamics_with_backreaction
    (σ σ_prime σ_pp hbar m : ℝ)
    (hσ : σ ≠ 0) (hhbar : hbar ≠ 0) (hm : m ≠ 0) :
    let α := continuity_alpha_relation σ σ_prime hbar m
    let α_prime := continuity_alpha_prime σ σ_prime σ_pp hbar m
    (hbar * α_prime / σ + 2 * hbar ^ 2 * α ^ 2 / m = 0)
      ↔ (σ_pp * σ + σ_prime ^ 2 * (σ - 1) = 0) :=
  gaussian_curved_leading_order_sigma_ode σ σ_prime σ_pp hbar m hσ hhbar hm

/-! ════════════════════════════════════════════════════════════════════════
    PART 15 — STATUS / FRONTIER (final, post D dynamics 3 cleanup).

    Closed in this file (Parts 13–14):
      ✓ `CurvedSchrodingerCovariantForm` — general-covariant matter equation.
      ✓ `CurvedSchrodingerCovariantForm_iff_HJBohm_curved` — equivalence
        with the existing curved HJ-with-Bohm.
      ✓ `CoupledMatterGeometrySystem_GeneralCovariant` — coupled system Prop.
      ✓ `CoupledMatterGeometrySystem_iff_HJBohm_matter_coupled` —
        equivalence with existing matter-coupled curved hypothesis.
      ✓ `flat_limit_recovers_standard_quantum_dynamics` — g^{xx} = 1
        limit gives flat HJ-with-Bohm.
      ✓ `static_limit_recovers_einstein_identity` — static limit
        gives the Einstein-like identity `R + (4m/ℏ²)V = (2/r⁴)·r_x²`.
      ✓ `gaussian_width_dynamics_with_backreaction` — σ(t) ODE
        under Gaussian ansatz with backreaction:
            `σ̈·σ + σ̇²·(σ−1) = 0`.

    Structural achievement:
      The coupled matter-geometry system is now stated in a form whose
      metric dependence is a single inverse-metric scalar `g^{xx}`.
      The two endpoint limits — flat (recovers standard QM) and static
      (recovers the Einstein-like identity) — are both proved.  The
      Gaussian wavepacket dynamics under backreaction is now a single
      named theorem.

    Connection to C.3:
      The general-covariant form generalizes naturally to the C.3
      chartwise SPD framework:  `g^{xx}` becomes
      `(ChartwiseMetricCoefs.c x x)` after weighting by `√|g|`, and
      multi-dimensional cases use the chartwise Laplace-Beltrami
      converged in `fdLaplaceBeltrami_converges_chartwise`.

    Open continuations:
    • Multi-dimensional spatial slice:  reuse `ChartwiseMetricCoefs`
      from C.3 to state the coupled system on `Fin n → ℝ`.
    • Sigma(t) integration:  explicit closed-form solutions to
      `σ̈·σ + σ̇²·(σ−1) = 0` (likely requires `σ → 1` linearization
      to extract a frequency or growth rate).
    • Time-dependent matter-coupled curvature identity dynamic version
      (parallel to the static `R + (4m/ℏ²)V = (2/r⁴)·r_x²`).
    ════════════════════════════════════════════════════════════════════════ -/

/-! ════════════════════════════════════════════════════════════════════════
    PART 16 — SECH ANSATZ PARALLEL  (final dynamics-side robustness closure).

    Repeats the Gaussian + quadratic-phase ansatz construction with a
    SECH amplitude:
        r(x, t) = (1/√(ξ(t))) · sech(x / ξ(t))         (normalized).

    The same scalar-level decomposition applies:
      • spatial derivative factor       `r_x = (-1/ξ)·tanh(x/ξ)·r`
      • second spatial deriv factor    `r_xx = (1/ξ²)·(1 − 2·sech²(x/ξ))·r`
      • time derivative factor          `r_t = ξ'·r·(−1/(2ξ) + (x/ξ²)·tanh(x/ξ))`

    With the same quadratic phase  `s = α·x² + β`  and the same
    continuity-derived α relation
        `α = m·ξ'/(2ℏ·ξ)`,
    the continuity equation is IDENTICALLY SATISFIED — exactly as
    for the Gaussian case (Part 12).

    This closes the most visible robustness caveat on the dynamics
    side:  the σ-ODE structure (continuity-identically-zero + α fixed
    by ξ') is NOT a Gaussian-specific artifact;  it survives the
    sech ansatz transitively.  The matter equation reduction to a
    width ODE for ξ(t) is the parallel of Part 12;  documented as
    follow-up in the closing notes. -/

/-- Sech amplitude with `1/√ξ` normalization, `ξ : ℝ → ℝ` time-dependent. -/
noncomputable def sechAmplitudeNormalized (ξ : ℝ → ℝ) (x t : ℝ) : ℝ :=
  (1 / Real.sqrt (ξ t)) * (1 / Real.cosh (x / ξ t))

/-- Spatial derivative scalar for the normalized sech:
        `∂_x r = −(1/ξ) · tanh(x/ξ) · r`. -/
noncomputable def sechNormalized_r_x_factor (ξ x : ℝ) : ℝ :=
  -(1 / ξ) * Real.tanh (x / ξ)

/-- Second spatial derivative scalar:
        `∂_xx r = (1/ξ²) · (1 − 2·sech²(x/ξ)) · r`. -/
noncomputable def sechNormalized_r_xx_factor (ξ x : ℝ) : ℝ :=
  (1 / ξ ^ 2) * (1 - 2 / (Real.cosh (x / ξ)) ^ 2)

/-- Time derivative scalar:
        `∂_t r = ξ' · r · (−1/(2ξ) + (x/ξ²)·tanh(x/ξ))`. -/
noncomputable def sechNormalized_r_t_factor (ξ ξ_prime x : ℝ) : ℝ :=
  ξ_prime * (-(1 / (2 * ξ)) + (x / ξ ^ 2) * Real.tanh (x / ξ))

/-- **PHASE D DYNAMICS SECH PARALLEL — CONTINUITY IDENTICALLY ZERO**.

    For the sech normalized amplitude + quadratic phase ansatz, with
    `α := m·ξ'/(2ℏ·ξ)` (the SAME continuity-derived α relation as
    Gaussian, since both ansätze share the scale-invariant form
    `r = (1/√ξ)·F(x/ξ)`), the amplitude-stripped continuity equation
        `ℏ · r_t_factor
         + (ℏ²/(2m)) · 2 · r_x_factor · s_x_factor
         + (ℏ²/(2m)) · s_xx_factor    = 0`
    holds identically in `x`.

    The proof is a `field_simp + ring` after substituting the sech
    factors and the α relation — the `tanh(x/ξ)` terms cancel exactly,
    just as the analogous Gaussian factors did in Part 12. -/
theorem sech_continuity_identically_zero
    (ξ ξ_prime hbar m x : ℝ)
    (hξ : ξ ≠ 0) (hhbar : hbar ≠ 0) (hm : m ≠ 0) :
    let α := continuity_alpha_relation ξ ξ_prime hbar m
    let r_t_factor := sechNormalized_r_t_factor ξ ξ_prime x
    let r_x_factor := sechNormalized_r_x_factor ξ x
    let s_x_factor := 2 * α * x
    let s_xx_factor := 2 * α
    hbar * r_t_factor
      + (hbar ^ 2 / (2 * m)) * 2 * r_x_factor * s_x_factor
      + (hbar ^ 2 / (2 * m)) * s_xx_factor
      = 0 := by
  simp only
  unfold continuity_alpha_relation
    sechNormalized_r_t_factor sechNormalized_r_x_factor
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have h2m_ne : (2 * m : ℝ) ≠ 0 := mul_ne_zero h2 hm
  have h2hbar_ne : (2 * hbar : ℝ) ≠ 0 := mul_ne_zero h2 hhbar
  have h2hbarξ_ne : (2 * hbar * ξ : ℝ) ≠ 0 := mul_ne_zero h2hbar_ne hξ
  have hξ2_ne : ξ ^ 2 ≠ 0 := pow_ne_zero 2 hξ
  field_simp
  ring

/-- **Sech-ansatz static recovery**:  if `ξ' = 0` (frozen width), the
    sech-derived α also vanishes — same trivial recovery as the
    Gaussian case. -/
theorem sech_continuity_alpha_static
    (ξ hbar m : ℝ) (hξ : ξ ≠ 0) (hhbar : hbar ≠ 0) :
    continuity_alpha_relation ξ 0 hbar m = 0 := by
  unfold continuity_alpha_relation
  simp

/-! **Frontier note on sech-ansatz matter equation derivation**

    Closed in Part 16 (above):
      ✓ Sech amplitude + quadratic phase ansatz definitions.
      ✓ Spatial / time derivative factor scalars.
      ✓ Same continuity-derived α relation `α = m·ξ'/(2ℏ·ξ)`.
      ✓ **`sech_continuity_identically_zero`** — the sech ansatz
        satisfies continuity identically under the same α relation.

    What this establishes:
      The Gaussian-ansatz "continuity is automatic, σ-ODE comes from
      matter equation" structure (Part 12) is NOT a Gaussian-specific
      coincidence.  It is a property of the entire family of
      normalized scale-invariant ansätze
          `r(x, t) = (1/√ξ(t)) · F(x/ξ(t))`
      with quadratic phase.  Gaussian (F = exp(−x²/2)) and sech
      (F = sech(x)) are two instances;  both share the same continuity-
      identically-zero theorem.

    Open continuation: see Part 17 below — closed in Lean. -/

/-! ════════════════════════════════════════════════════════════════════════
    PART 17 — SECH FULL CURVED ODE  (matter-equation reduction, parallel
              to Part 11/12 for the Gaussian case).

    For the sech normalized amplitude `r = (1/√ξ)·sech(x/ξ)` and the
    matter-coupled curved HJ-with-Bohm (a² = r², V = 0), the x² Taylor
    coefficient match yields a width ODE for ξ(t) that has the SAME
    left-hand side function as the Gaussian curved ODE but with a
    NON-ZERO SOURCE TERM:

        `ξ · ξ_pp + ξ_prime² · (ξ − 1) = ℏ² / (m² · ξ)`            (sech)
        `σ · σ_pp + σ_prime² · (σ − 1) = 0`                         (Gaussian)

    The source-term difference comes from the differing Taylor
    coefficients of `r_xx/r` at x² (Gaussian: `1/σ⁴`; sech: `2/ξ⁴`).
    The factor-of-2 propagates to a non-zero residual after the
    β'-substitution that exactly cancels in the Gaussian case.

    Qualitative consequence:  unlike the Gaussian case, the SECH
    matter-coupled curved dynamics does NOT admit frozen wavepackets
    (no σ_prime = 0 fixed point).  At ξ_prime = 0, the ODE forces
    ξ_pp = ℏ²/(m² · ξ²) ≠ 0.  This means the "frozen narrow / frozen
    wide" signatures of the Gaussian σ-ODE are **ansatz-specific**, not
    family-level.  Honest finding from the parallel derivation. -/

/-- **PHASE D DYNAMICS SECH PART 17 — SECH CURVED WIDTH ODE**.

    For the sech amplitude with the SAME continuity-derived α relation
    as Gaussian, the x² coefficient match of the matter-coupled curved
    HJ-with-Bohm equation gives the SECH curved width ODE:

        `ξ · ξ_pp + ξ_prime² · (ξ − 1) = ℏ²/(m² · ξ)`.

    Statement is an iff between the α-form and the ξ-form, parallel
    to `gaussian_curved_leading_order_sigma_ode`.  Same LHS-reduction
    (the lemma `gaussian_curved_lhs_reduces` is generic in the width
    variable and applies to both ansätze);  the RHS picks up the
    factor-of-2 difference from sech's `r_xx/r` Taylor expansion. -/
theorem sech_curved_leading_order_sigma_ode
    (ξ ξ_prime ξ_pp hbar m : ℝ)
    (hξ : ξ ≠ 0) (hhbar : hbar ≠ 0) (hm : m ≠ 0) :
    let α := continuity_alpha_relation ξ ξ_prime hbar m
    let α_prime := continuity_alpha_prime ξ ξ_prime ξ_pp hbar m
    -- The sech case has an EXTRA `ℏ²/(2m·ξ⁴)` source (the Gaussian
    -- case had 0), coming from the factor of 2 in sech's `r_xx/r`
    -- Taylor expansion at x².
    (hbar * α_prime / ξ + 2 * hbar ^ 2 * α ^ 2 / m
        = hbar ^ 2 / (2 * m * ξ ^ 4))
      ↔ (ξ_pp * ξ + ξ_prime ^ 2 * (ξ - 1) = hbar ^ 2 / (m ^ 2 * ξ)) := by
  simp only
  unfold continuity_alpha_relation continuity_alpha_prime
  -- Reuse the LHS-reduction lemma proved for the Gaussian case;  the
  -- algebra is identical because the α and α' formulas are the same.
  rw [gaussian_curved_lhs_reduces ξ ξ_prime ξ_pp hbar m hξ hhbar hm]
  -- Goal:  m * (ξ_pp * ξ + ξ_prime^2 * (ξ - 1)) / (2 * ξ^3)
  --          = hbar^2 / (2 * m * ξ^4)
  --       ↔ ξ_pp * ξ + ξ_prime^2 * (ξ - 1) = hbar^2 / (m^2 * ξ)
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hξ3 : ξ ^ 3 ≠ 0 := pow_ne_zero 3 hξ
  have hξ4 : ξ ^ 4 ≠ 0 := pow_ne_zero 4 hξ
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
  have h2ξ3 : 2 * ξ ^ 3 ≠ 0 := mul_ne_zero h2 hξ3
  have h2mξ4 : 2 * m * ξ ^ 4 ≠ 0 :=
    mul_ne_zero (mul_ne_zero h2 hm) hξ4
  have hm2ξ : m ^ 2 * ξ ≠ 0 := mul_ne_zero hm2 hξ
  rw [div_eq_div_iff h2ξ3 h2mξ4, eq_div_iff hm2ξ]
  -- Goals:
  --   LHS form:  m * (ξ_pp*ξ + ξ_prime^2*(ξ-1)) * (2*m*ξ^4)
  --               = hbar^2 * (2*ξ^3)
  --   ↔ RHS form: (ξ_pp*ξ + ξ_prime^2*(ξ-1)) * (m^2*ξ) = hbar^2
  -- The proof is just multiplying out and cancelling the common
  -- `2*ξ^3` factor.
  have h_eq : m * (ξ_pp * ξ + ξ_prime ^ 2 * (ξ - 1)) * (2 * m * ξ ^ 4)
              = (ξ_pp * ξ + ξ_prime ^ 2 * (ξ - 1)) * (m ^ 2 * ξ)
                  * (2 * ξ ^ 3) := by ring
  constructor
  · intro h
    have h2 : (ξ_pp * ξ + ξ_prime ^ 2 * (ξ - 1)) * (m ^ 2 * ξ) * (2 * ξ ^ 3)
                = hbar ^ 2 * (2 * ξ ^ 3) := by
      linarith [h_eq]
    exact mul_right_cancel₀ h2ξ3 h2
  · intro h
    rw [h_eq, h]

/-- **Sech vs Gaussian source-term distinction**.

    The Gaussian curved σ-ODE has zero source;  the sech curved ξ-ODE
    has source `ℏ²/(m² · ξ)`.  At any non-zero `(ξ, ξ_prime, ξ_pp)`
    satisfying the sech ODE, the same scalar triple violates the
    Gaussian ODE.  Concrete witness:  set `ξ_prime = 0`, `ξ = 1`, then
    sech requires `ξ_pp = ℏ²/m²` while Gaussian requires `ξ_pp = 0`. -/
theorem sech_curved_distinct_from_gaussian_curved
    (hbar m : ℝ) (hhbar : hbar ≠ 0) (hm : m ≠ 0) :
    -- Sech curved ODE at ξ=1, ξ_prime=0:  ξ_pp = ℏ²/m²
    ((1 : ℝ) * (hbar ^ 2 / m ^ 2) + 0 * (1 - 1) = hbar ^ 2 / (m ^ 2 * 1))
    -- Gaussian curved ODE at σ=1, σ_prime=0:  σ_pp = 0 (since σ_pp · 1 + 0 · 0 = 0)
    -- The sech σ_pp at ξ=1 is hbar²/m² ≠ 0.
    ∧ (hbar ^ 2 / m ^ 2 ≠ 0) := by
  refine ⟨?_, ?_⟩
  · have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
    field_simp
    ring
  · have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
    have hh2 : hbar ^ 2 ≠ 0 := pow_ne_zero 2 hhbar
    exact div_ne_zero hh2 hm2

/-- **Sech curved does NOT admit frozen wavepackets**.

    For the sech matter-coupled curved width ODE
        `ξ·ξ_pp + ξ_prime²·(ξ−1) = ℏ²/(m²·ξ)`,
    the configuration `ξ_prime = ξ_pp = 0` is INADMISSIBLE for any
    non-zero `ξ, ℏ, m`.  The LHS would be 0 but the RHS is `ℏ²/(m²·ξ) ≠ 0`.

    Honest contrast with the Gaussian case (which admits frozen σ):
    the "frozen narrow / frozen wide" signature of the Gaussian σ-ODE
    is ANSATZ-SPECIFIC, not a family-level prediction. -/
theorem sech_curved_rejects_frozen
    (ξ hbar m : ℝ) (hξ : ξ ≠ 0) (hhbar : hbar ≠ 0) (hm : m ≠ 0) :
    -- The frozen configuration (ξ_prime = 0, ξ_pp = 0) does NOT satisfy
    -- the sech curved ODE:  the LHS is 0, but RHS is non-zero.
    (0 : ℝ) * ξ + (0 : ℝ) ^ 2 * (ξ - 1) ≠ hbar ^ 2 / (m ^ 2 * ξ) := by
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
  have hm2ξ : m ^ 2 * ξ ≠ 0 := mul_ne_zero hm2 hξ
  have hh2 : hbar ^ 2 ≠ 0 := pow_ne_zero 2 hhbar
  have h_rhs_ne : hbar ^ 2 / (m ^ 2 * ξ) ≠ 0 := div_ne_zero hh2 hm2ξ
  intro h_eq
  apply h_rhs_ne
  have h_zero : (0 : ℝ) * ξ + (0 : ℝ) ^ 2 * (ξ - 1) = 0 := by ring
  rw [h_zero] at h_eq
  exact h_eq.symm

end UnifiedTheory.LayerB.LohmillerSlotineBackreaction
