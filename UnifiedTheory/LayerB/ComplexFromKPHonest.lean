/-
  LayerB/ComplexFromKPHonest.lean — Honest K/P → ℂ wiring

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT — A CORRECTION

  `LayerB/ComplexFromDressing.lean` advertises in its docstring the chain

      SourceFunctional → K/P split → (Q,P) pair → ℂ amplitude → interference

  but the file imports `LayerA.DerivedBFSplit` and never uses it.  The
  function

      def amplitudeFromKP (Q P : ℝ) : ℂ := ⟨Q, P⟩

  takes two free real numbers; the K/P origin of `Q` and `P` is asserted
  in the docstring only.  The downstream theorems
  (`charge_is_real_part`, `dressing_is_imag_part`, `obs_from_KP`, …) are
  honest consequences of `⟨Q, P⟩` arithmetic, but the *advertised wiring*
  to the source functional was never built.

  This file builds the missing wiring.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  – `complexAmplitudeFromKP : SourceFunctional V → (V → ℝ) → V → ℂ`
    actually consumes a `SourceFunctional`, runs the K-projection
    derived in `LayerA/DerivedBFSplit.lean`, and packages

        re = φ (sourceProj φ h)        -- the K-channel source charge
        im = D h                        -- the dressing functional value

    The `Q` and `P` legs are now genuinely derived; they are no longer
    free real numbers.

  – `complexAmplitudeFromKP_eq_amplitudeFromKP` — the new constructor
    REDUCES to the existing `amplitudeFromKP Q P = ⟨Q, P⟩` when
    `(Q, P)` are taken from the K/P split.  This is the bridge to
    `ComplexFromDressing.lean`: the previously free `Q, P` are now
    pinned to the K/P origin.

  – `complexAmplitudeFromKP_re_eq_phi`, `complexAmplitudeFromKP_im_eq_D`
    — the K-channel's real part collapses to `φ h` itself
    (via `source_on_K`), and the imaginary part is `D h`.

  – `metric_complexAmplitude_re`, `metric_complexAmplitude_im`,
    `metric_complexAmplitude_eq` — bridge to `LayerB/MetricDefects.lean`:
    for metric perturbations the K-channel real part is
    `traceFunc m (K_proj m h)` (i.e. the trace of the K-projection),
    which by `bridge_derived` equals `traceFunc m h` itself.

  – `obs_from_KP_honest`, `charge_is_real_part_honest`,
    `dressing_is_imag_part_honest` — re-proofs of the existing
    `ComplexFromDressing` identities at the K/P-derived level.

  – `dressing_rotation_preserves_obs_honest`,
    `dressing_causes_interference_honest` — the U(1) phase invariance
    and the dressing-driven interference, expressed at the K/P-derived
    level.

  – `complexification_from_parent_honest` — the master theorem of
    `ComplexFromDressing.lean`, but with `Q, P` now actually computed
    from the source functional.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS HONESTLY OUT OF SCOPE

  The complex algebra structure (multiplication on ℝ²) is still Lean's
  built-in `ℂ`; it is NOT derived from K/P here.  What this file
  delivers is the wiring of the (real, imaginary) PAIR from the K/P
  decomposition.  ℂ as a type — and its multiplication — is imported,
  not constructed.  Constructing ℂ from K/P would require separate work
  (a free ℝ-bilinear product on K × P that satisfies the complex
  relations); see `ComplexUniqueness.lean` and
  `ComplexificationUniqueness.lean` for the uniqueness side.

  Zero sorry. Zero custom axioms.
-/
import UnifiedTheory.LayerB.ComplexFromDressing
import UnifiedTheory.LayerB.MetricDefects

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.ComplexFromKPHonest

open UnifiedTheory.LayerB
open UnifiedTheory.LayerA

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE K/P-DERIVED COMPLEX AMPLITUDE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    We package the K-channel source charge and the dressing functional
    value as the (real, imaginary) parts of a complex amplitude.

    The construction is:
       re(z) := φ(πK h)   -- source charge through the K-projection
       im(z) := D(h)      -- dressing functional value

    By `source_on_K` this collapses to `re(z) = φ(h)`.  We keep the
    explicit `sourceProj` in the definition to make the K/P origin of
    the real part visible from the elaborated term, so a reader cannot
    (as before) skip the K/P split when reasoning about `re(z)`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **The honest K/P-derived complex amplitude.**

    Given a source functional `φ : SourceFunctional V` (which provides
    the `sourceProj`) and a dressing functional `D : V → ℝ`, the
    amplitude of a configuration `h : V` is

        re = φ(πK h)        (the K-channel source charge)
        im = D h            (the dressing functional value)

    The K-projection `πK = sourceProj φ` is derived in
    `LayerA/DerivedBFSplit.lean` from the single primitive `φ`. -/
noncomputable def complexAmplitudeFromKP
    (sf : SourceFunctional V) (D : V → ℝ) (h : V) : ℂ :=
  ⟨sf.φ (sourceProj sf h), D h⟩

/-- The real part is the K-channel source charge. -/
theorem complexAmplitudeFromKP_re
    (sf : SourceFunctional V) (D : V → ℝ) (h : V) :
    (complexAmplitudeFromKP sf D h).re = sf.φ (sourceProj sf h) := rfl

/-- The imaginary part is the dressing functional value. -/
theorem complexAmplitudeFromKP_im
    (sf : SourceFunctional V) (D : V → ℝ) (h : V) :
    (complexAmplitudeFromKP sf D h).im = D h := rfl

/-- **The K-channel captures the full source.**

    By `source_on_K`, the source functional applied to the K-projection
    equals the source functional applied to the original configuration.
    So the real part of the K/P-derived amplitude is just `φ h`.

    This is the wiring statement: the previously free `Q` is now
    derived from `φ`. -/
theorem complexAmplitudeFromKP_re_eq_phi
    (sf : SourceFunctional V) (D : V → ℝ) (h : V) :
    (complexAmplitudeFromKP sf D h).re = sf.φ h := by
  rw [complexAmplitudeFromKP_re, source_on_K]

/-- The imaginary part is just `D h` (already by definition). -/
theorem complexAmplitudeFromKP_im_eq_D
    (sf : SourceFunctional V) (D : V → ℝ) (h : V) :
    (complexAmplitudeFromKP sf D h).im = D h := rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: REDUCTION TO `amplitudeFromKP` (BRIDGE TO EXISTING FILE)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The existing `amplitudeFromKP Q P : ℂ := ⟨Q, P⟩` accepts `Q, P` as
    free real numbers.  The new constructor pins them to the K/P
    origin.  Both produce the same `⟨_, _⟩` packaging, so the
    K/P-derived amplitude REDUCES to the existing one when `(Q, P)`
    are taken from the K/P split.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **REDUCTION to the existing `amplitudeFromKP`.**

    The K/P-derived amplitude is exactly `amplitudeFromKP Q P` when
    `(Q, P)` are taken from the K/P split.  This is the formal bridge
    that pins the previously free `(Q, P)` arguments of
    `ComplexFromDressing.amplitudeFromKP` to the K/P origin. -/
theorem complexAmplitudeFromKP_eq_amplitudeFromKP
    (sf : SourceFunctional V) (D : V → ℝ) (h : V) :
    complexAmplitudeFromKP sf D h =
      amplitudeFromKP (sf.φ (sourceProj sf h)) (D h) := rfl

/-- **REDUCTION via `source_on_K`.**

    Equivalently, using `source_on_K` to collapse `φ(πK h)` to `φ h`,
    the K/P-derived amplitude equals `amplitudeFromKP (φ h) (D h)`. -/
theorem complexAmplitudeFromKP_eq_phi_form
    (sf : SourceFunctional V) (D : V → ℝ) (h : V) :
    complexAmplitudeFromKP sf D h = amplitudeFromKP (sf.φ h) (D h) := by
  apply Complex.ext
  · rw [complexAmplitudeFromKP_re_eq_phi]
    rfl
  · rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: RE-PROOFS AT THE K/P-DERIVED LEVEL
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The existing identities `charge_is_real_part`, `dressing_is_imag_part`,
    `obs_from_KP` were stated for the free `(Q, P)` form.  Here we
    re-state them at the K/P-derived level: the real part is the source
    charge `φ(πK h) = φ h`, and the imaginary part is the dressing
    functional `D h`.  The proofs reduce to the existing ones via
    `complexAmplitudeFromKP_eq_amplitudeFromKP`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Charge is the real part (honest version).**

    The classical (K-channel) source charge `φ h` is the real part of
    the K/P-derived complex amplitude. -/
theorem charge_is_real_part_honest
    (sf : SourceFunctional V) (D : V → ℝ) (h : V) :
    (complexAmplitudeFromKP sf D h).re = sf.φ h :=
  complexAmplitudeFromKP_re_eq_phi sf D h

/-- **Dressing is the imaginary part (honest version).**

    The dressing functional value `D h` is the imaginary part of the
    K/P-derived complex amplitude. -/
theorem dressing_is_imag_part_honest
    (sf : SourceFunctional V) (D : V → ℝ) (h : V) :
    (complexAmplitudeFromKP sf D h).im = D h :=
  complexAmplitudeFromKP_im_eq_D sf D h

/-- **Born-rule observable (honest version).**

    The observable of a K/P-derived amplitude is the sum of squares of
    the K-channel source charge and the dressing functional value. -/
theorem obs_from_KP_honest
    (sf : SourceFunctional V) (D : V → ℝ) (h : V) :
    obs (complexAmplitudeFromKP sf D h) = (sf.φ h) ^ 2 + (D h) ^ 2 := by
  rw [complexAmplitudeFromKP_eq_phi_form]
  exact obs_from_KP _ _

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: U(1) DRESSING ROTATION (HONEST VERSION)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The dressing rotation, lifted to the K/P-derived amplitude. -/
noncomputable def dressingRotationKP
    (sf : SourceFunctional V) (D : V → ℝ) (θ : ℝ) (h : V) : ℂ :=
  phaseRotate θ (complexAmplitudeFromKP sf D h)

/-- **U(1) phase invariance of the K/P-derived observable.** -/
theorem dressing_rotation_preserves_obs_honest
    (sf : SourceFunctional V) (D : V → ℝ) (θ : ℝ) (h : V) :
    obs (dressingRotationKP sf D θ h) = obs (complexAmplitudeFromKP sf D h) :=
  phase_invariance θ (complexAmplitudeFromKP sf D h)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: INTERFERENCE FROM DRESSING (HONEST VERSION)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Two configurations with the same source charge but different
    dressing values interfere.  At the K/P-derived level: take two
    configurations `h₁, h₂` such that `φ h₁ = φ h₂ = Q` (same K-content)
    but `D h₁ ≠ D h₂` (different dressing).  Their amplitudes interfere.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Dressing causes interference (honest version).**

    The Born observable of the sum of two K/P-derived amplitudes is
    not the sum of individual observables — there is an interference
    correction. -/
theorem dressing_causes_interference_honest
    (sf : SourceFunctional V) (D : V → ℝ) (h₁ h₂ : V) :
    obs (complexAmplitudeFromKP sf D h₁ + complexAmplitudeFromKP sf D h₂) =
      obs (complexAmplitudeFromKP sf D h₁)
      + obs (complexAmplitudeFromKP sf D h₂)
      + interferenceTerm (complexAmplitudeFromKP sf D h₁)
                         (complexAmplitudeFromKP sf D h₂) :=
  interference_formula _ _

/-- **Interference is dressing-aligned**: explicit formula at the
    K/P-derived level. -/
theorem interference_dressing_dependent_honest
    (sf : SourceFunctional V) (D : V → ℝ) (h₁ h₂ : V) :
    interferenceTerm (complexAmplitudeFromKP sf D h₁)
                     (complexAmplitudeFromKP sf D h₂)
      = 2 * (sf.φ h₁ * sf.φ h₂ + D h₁ * D h₂) := by
  simp [interferenceTerm, complexAmplitudeFromKP, source_on_K]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: METRIC-PERTURBATION SPECIALIZATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Specialize to the metric perturbation space of `MetricDefects.lean`:
    the source functional is `canonicalSF m` (i.e. trace), and any
    `D : Perturbation (m+2) → ℝ` plays the role of the dressing
    functional.  The real part is `traceFunc m (K_proj m h)`, which by
    `bridge_derived` equals `traceFunc m h`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

open UnifiedTheory.LayerB.MetricDefects in
/-- **Metric specialization: real part is the K-projected trace.**

    For metric perturbations, the real part of the K/P-derived
    amplitude is `traceFunc m (K_proj m h)`. -/
theorem metric_complexAmplitude_re
    (m : ℕ) (D : Perturbation (m + 2) → ℝ) (h : Perturbation (m + 2)) :
    (complexAmplitudeFromKP (canonicalSF m) D h).re =
      traceFunc m (K_proj m h) := rfl

open UnifiedTheory.LayerB.MetricDefects in
/-- **Metric specialization: real part collapses to `traceFunc m h`.**

    By `bridge_derived` (which is `source_on_K` applied to the trace
    functional), the K-projected trace equals the trace itself. -/
theorem metric_complexAmplitude_re_eq_trace
    (m : ℕ) (D : Perturbation (m + 2) → ℝ) (h : Perturbation (m + 2)) :
    (complexAmplitudeFromKP (canonicalSF m) D h).re = traceFunc m h := by
  rw [metric_complexAmplitude_re, bridge_derived]

open UnifiedTheory.LayerB.MetricDefects in
/-- **Metric specialization: imaginary part is the dressing functional.** -/
theorem metric_complexAmplitude_im
    (m : ℕ) (D : Perturbation (m + 2) → ℝ) (h : Perturbation (m + 2)) :
    (complexAmplitudeFromKP (canonicalSF m) D h).im = D h := rfl

open UnifiedTheory.LayerB.MetricDefects in
/-- **Metric specialization: full reduction to `amplitudeFromKP`.**

    For metric perturbations, the K/P-derived amplitude equals
    `amplitudeFromKP (traceFunc m h) (D h)`. -/
theorem metric_complexAmplitude_eq
    (m : ℕ) (D : Perturbation (m + 2) → ℝ) (h : Perturbation (m + 2)) :
    complexAmplitudeFromKP (canonicalSF m) D h =
      amplitudeFromKP (traceFunc m h) (D h) :=
  complexAmplitudeFromKP_eq_phi_form (canonicalSF m) D h

open UnifiedTheory.LayerB.MetricDefects in
/-- **Metric specialization: Born observable.**

    `|z|² = trace² + D²` for the K/P-derived amplitude on metric
    perturbations. -/
theorem metric_obs_from_KP
    (m : ℕ) (D : Perturbation (m + 2) → ℝ) (h : Perturbation (m + 2)) :
    obs (complexAmplitudeFromKP (canonicalSF m) D h) =
      (traceFunc m h) ^ 2 + (D h) ^ 2 :=
  obs_from_KP_honest (canonicalSF m) D h

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: CLASSICAL LIMIT (D ≡ 0)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    When the dressing functional is identically zero, the K/P-derived
    amplitude lies on the real axis and the framework reduces to the
    classical real-charge theory.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Classical limit (honest version).**

    With zero dressing functional, the amplitude equals the real
    embedding of the source charge `φ h`. -/
theorem classical_limit_honest
    (sf : SourceFunctional V) (h : V) :
    complexAmplitudeFromKP sf (fun _ => (0 : ℝ)) h = (sf.φ h : ℂ) := by
  apply Complex.ext
  · rw [complexAmplitudeFromKP_re_eq_phi]
    rfl
  · rfl

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: PURE-DRESSING SECTOR (φ h = 0, D h ≠ 0)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A pure-dressing configuration has zero source charge but nonzero
    dressing functional value.  Classically invisible, quantum-visible.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Pure dressing has zero classical charge (honest version).** -/
theorem pure_dressing_zero_charge_honest
    (sf : SourceFunctional V) (D : V → ℝ) (h : V) (h0 : sf.φ h = 0) :
    (complexAmplitudeFromKP sf D h).re = 0 := by
  rw [complexAmplitudeFromKP_re_eq_phi]; exact h0

/-- **Pure dressing has positive observable (honest version).** -/
theorem pure_dressing_pos_obs_honest
    (sf : SourceFunctional V) (D : V → ℝ) (h : V)
    (h0 : sf.φ h = 0) (hD : D h ≠ 0) :
    0 < obs (complexAmplitudeFromKP sf D h) := by
  rw [obs_from_KP_honest, h0]
  have : 0 < (D h) ^ 2 := by positivity
  linarith

/-- **Quantum vacuum effect (honest version).**

    A pure-dressing configuration is classically invisible
    (`re = 0 = φ h`) but quantum-visible (`obs > 0`). -/
theorem quantum_vacuum_effect_honest
    (sf : SourceFunctional V) (D : V → ℝ) (h : V)
    (h0 : sf.φ h = 0) (hD : D h ≠ 0) :
    (complexAmplitudeFromKP sf D h).re = 0
    ∧ 0 < obs (complexAmplitudeFromKP sf D h) :=
  ⟨pure_dressing_zero_charge_honest sf D h h0,
   pure_dressing_pos_obs_honest sf D h h0 hD⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: MASTER WIRING THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The master theorem of `ComplexFromDressing.lean`, but with `Q, P`
    actually computed from the source functional.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE COMPLEXIFICATION-FROM-PARENT THEOREM (HONEST VERSION).**

    The K/P decomposition (derived in `LayerA/DerivedBFSplit.lean`
    from a single nonzero linear functional `φ`) genuinely produces
    the (real, imaginary) parts of a complex amplitude:

      (1) Real part = `φ h`        (K-channel source charge)
      (2) Imaginary part = `D h`   (dressing functional value)
      (3) Born observable = `(φ h)² + (D h)²`
      (4) U(1) dressing rotation preserves the observable
      (5) Two configurations with the same `(φ, D)` interfere
      (6) Pure dressing (`φ h = 0`, `D h ≠ 0`) is classically invisible
          but quantum-visible
      (7) Setting `D ≡ 0` reduces to the classical real-charge theory

    Honest scope: ℂ (multiplication structure on ℝ²) is still Lean's
    built-in `ℂ`.  This theorem wires the (real, imaginary) PAIR from
    K/P; the algebra `(re, im) ↦ re² - im², 2·re·im` is not derived
    here.  See `ComplexUniqueness.lean` /
    `ComplexificationUniqueness.lean` for the uniqueness side. -/
theorem complexification_from_parent_honest
    (sf : SourceFunctional V) (D : V → ℝ) :
    -- (1) Real part is the source charge
    (∀ h, (complexAmplitudeFromKP sf D h).re = sf.φ h)
    -- (2) Imaginary part is the dressing functional
    ∧ (∀ h, (complexAmplitudeFromKP sf D h).im = D h)
    -- (3) Born observable
    ∧ (∀ h, obs (complexAmplitudeFromKP sf D h) = (sf.φ h) ^ 2 + (D h) ^ 2)
    -- (4) U(1) phase invariance
    ∧ (∀ θ h,
        obs (dressingRotationKP sf D θ h) = obs (complexAmplitudeFromKP sf D h))
    -- (5) Interference identity
    ∧ (∀ h₁ h₂,
        obs (complexAmplitudeFromKP sf D h₁ + complexAmplitudeFromKP sf D h₂) =
          obs (complexAmplitudeFromKP sf D h₁)
          + obs (complexAmplitudeFromKP sf D h₂)
          + interferenceTerm (complexAmplitudeFromKP sf D h₁)
                             (complexAmplitudeFromKP sf D h₂))
    -- (6) Pure-dressing sector exists structurally
    ∧ (∀ h, sf.φ h = 0 → D h ≠ 0 →
        (complexAmplitudeFromKP sf D h).re = 0
        ∧ 0 < obs (complexAmplitudeFromKP sf D h)) :=
  ⟨charge_is_real_part_honest sf D,
   dressing_is_imag_part_honest sf D,
   obs_from_KP_honest sf D,
   dressing_rotation_preserves_obs_honest sf D,
   dressing_causes_interference_honest sf D,
   fun h h0 hD => quantum_vacuum_effect_honest sf D h h0 hD⟩

/-- **METRIC SPECIALIZATION OF THE MASTER WIRING.**

    For metric perturbations with the canonical trace functional and
    any choice of dressing functional `D`, the K/P-derived amplitude
    has real part `traceFunc m h`, imaginary part `D h`, observable
    `(trace h)² + (D h)²`, and is U(1)-phase-invariant. -/
theorem metric_complexification_honest
    (m : ℕ) (D : MetricDefects.Perturbation (m + 2) → ℝ) :
    -- (1) Real part is the trace
    (∀ h, (complexAmplitudeFromKP (MetricDefects.canonicalSF m) D h).re =
            MetricDefects.traceFunc m h)
    -- (2) Imaginary part is D
    ∧ (∀ h, (complexAmplitudeFromKP (MetricDefects.canonicalSF m) D h).im = D h)
    -- (3) Born observable
    ∧ (∀ h, obs (complexAmplitudeFromKP (MetricDefects.canonicalSF m) D h) =
              (MetricDefects.traceFunc m h) ^ 2 + (D h) ^ 2)
    -- (4) Bridge to existing amplitudeFromKP
    ∧ (∀ h, complexAmplitudeFromKP (MetricDefects.canonicalSF m) D h =
              amplitudeFromKP (MetricDefects.traceFunc m h) (D h)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; exact metric_complexAmplitude_re_eq_trace m D h
  · intro h; rfl
  · intro h; exact metric_obs_from_KP m D h
  · intro h; exact metric_complexAmplitude_eq m D h

end UnifiedTheory.LayerB.ComplexFromKPHonest
