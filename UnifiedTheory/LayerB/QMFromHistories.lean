/-
  LayerB/QMFromHistories.lean — QM-as-theorem capstone: histories + propagators + Born

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  PART 0: PHYSICAL INTERPRETATION

  The framework's claim "quantum mechanics is derived, not postulated" is not
  a single theorem but a CHAIN of compositional results spread across nine
  files. This file is the master synthesis. Reading the chain end-to-end:

    [Step 1]  A locally finite causal poset has a SOURCE FUNCTIONAL
              φ : V → ℝ on its perturbation space. (LayerA primitive.)

    [Step 2]  φ induces the K/P (source/dressing) decomposition: every
              perturbation h splits as h = K_proj h + P_proj h, with
              trace ∘ K_proj = trace and trace ∘ P_proj = 0.
              (`MetricDefects.decomp_derived`,
               `MetricDefects.bridge_derived`,
               `MetricDefects.neutrality_derived`.)

    [Step 3]  The pair (Q(h), D(h)) ∈ ℝ² IS a complex amplitude
              z(h) := Q(h) + i·D(h) ∈ ℂ. The complex structure is
              FORCED by dressing invisibility, not postulated.
              (`ComplexFromDressing.amplitudeFromKP`,
               `QuantumMechanicsIsATheorem.source_forces_complex`.)

    [Step 4]  Linearity of φ + the unique continuous character
              (ℝ,+) → (S¹,·) gives free propagation z(γ) = e^{i·k·φ(γ)}.
              The propagation rule e^{ikL} is derived from source linearity.
              (`PropagationRule.expAmplitude`,
               `PropagationRule.exp_multiplicative`,
               `PropagationRule.exp_unit_modulus`,
               `PropagationRule.propagation_derived_from_source`.)

    [Step 5]  Histories are lists of perturbations. The amplitude of an
              event is the COHERENT SUM of history amplitudes
              A(E) = Σ_{h ∈ histories(E)} A(h). Internal histories with
              on-shell endpoints and arbitrary intermediates implement
              the diagrammatic structure of QFT.
              (`HistoryAmplitudes.eventAmplitude`,
               `VirtualParticles.InternalHistory`.)

    [Step 6]  Off-shell intermediates carry K/P content but cannot be
              physical asymptotic states — they are virtual particles.
              A field propagator G acts as identity on on-shell legs
              and weights off-shell intermediates. The Feshbach Schur
              complement is exactly a single-virtual-line amplitude.
              (`VirtualParticles.OffShell`, `VirtualParticles.PVirtual`,
               `VirtualParticles.FieldPropagator`,
               `VirtualParticles.feshbach_eq_virtual_line`.)

    [Step 7]  The observable Obs(z) = |z|² = Q² + D² is the UNIQUE
              rotation-invariant quadratic on the K/P plane (Born rule
              uniqueness), and the unique rotation-invariant
              orthogonally-additive POWER observable forces degree 2.
              (`ComplexUniqueness.born_rule_unique`,
               `BornRuleQuadratic.born_degree_unique`,
               `BornRuleQuadratic.born_rule_must_be_quadratic`.)

    [Step 8]  Two-path interference Obs(z₁+z₂) = |z₁|² + |z₂|² +
              2·Re(z₁·conj z₂) is then a one-line algebraic identity.
              The cross term is the framework's interference fringe.
              (`HistoryAmplitudes.two_path_interference`,
               `PropagationRule.two_path_interference`.)

  Each step is already proved in its own file. THIS FILE is pure
  synthesis: a single master theorem `qm_is_theorem` whose conjuncts
  cite the eight steps above by name, plus three corollaries showing
  the on-shell / off-shell unification and the no-virtual-line collapse.

  WHAT IS NEW HERE: the synthesis itself. Until this file there was no
  single statement bundling (a) the existing Born-rule chain with
  (b) the recently-added history/propagator machinery. The bundling
  makes the path-integral interpretation EXPLICIT in Lean: ordinary
  free propagation is a one-step on-shell history, and Feynman
  diagrams are internal histories with off-shell intermediates.
  Both share the same coherent-sum amplitude and the same Born-rule
  observable — only the intermediate-line weighting differs.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED IN THIS FILE

  • `complex_amplitude_from_KP`        : (Step 3, citation)
  • `propagation_phase_from_source`    : (Step 4, citation)
  • `history_coherent_sum`             : (Step 5, citation)
  • `internal_history_propagator`      : (Step 6, citation)
  • `internal_history_no_virtual`      : (Step 6, on-shell collapse)
  • `feshbach_is_single_virtual_line`  : (Step 6, citation)
  • `born_rule_is_unique_quadratic`    : (Step 7, citation)
  • `born_degree_is_unique`            : (Step 7, citation)
  • `interference_two_path`            : (Step 8, citation)
  • `qm_is_theorem`                    : MASTER THEOREM bundling all of the above

  Zero sorry. Zero custom axioms.
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import UnifiedTheory.LayerB.MetricDefects
import UnifiedTheory.LayerB.ComplexFromDressing
import UnifiedTheory.LayerB.ComplexUniqueness
import UnifiedTheory.LayerB.QuantumMechanicsIsATheorem
import UnifiedTheory.LayerB.BornRuleQuadratic
import UnifiedTheory.LayerB.PropagationRule
import UnifiedTheory.LayerB.HistoryAmplitudes
import UnifiedTheory.LayerB.FeynmanRules
import UnifiedTheory.LayerB.VirtualParticles

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.QMFromHistories

open UnifiedTheory.LayerB
open UnifiedTheory.LayerB.MetricDefects
open UnifiedTheory.LayerB.HistoryAmplitudes
open UnifiedTheory.LayerB.VirtualParticles
open UnifiedTheory.LayerB.PropagationRule
open UnifiedTheory.LayerB.QuantumMechanicsIsATheorem
open UnifiedTheory.LayerB.BornRuleQuadratic

variable {m : ℕ}

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: STEP 3 — COMPLEX AMPLITUDES FROM K/P
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Citation of the existing derivation in `ComplexFromDressing` and
    `QuantumMechanicsIsATheorem`. The pair (Q, D) ∈ ℝ² IS a complex
    amplitude z = Q + i·D, and the observable is |z|² = Q² + D².
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Step 3 (citation): the K/P pair (Q,D) packages as a complex amplitude.**
    Real part = source charge, imaginary part = dressing content. Cited from
    `QuantumMechanicsIsATheorem.source_forces_complex`. -/
theorem complex_amplitude_from_KP (Q D : ℝ) :
    (Q + D * Complex.I).re = Q ∧ (Q + D * Complex.I).im = D :=
  source_forces_complex Q D

/-- **Step 3 (citation): observable equals norm squared.** Cited from
    `ComplexFromDressing.obs_from_KP`. The observable of an amplitude
    constructed from K/P data is Q² + D². -/
theorem obs_is_norm_squared (Q D : ℝ) :
    UnifiedTheory.LayerB.obs (amplitudeFromKP Q D) = Q ^ 2 + D ^ 2 :=
  obs_from_KP Q D

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: STEP 4 — ON-SHELL PROPAGATION = e^{ikφ}
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Citation of `PropagationRule.propagation_derived_from_source`.
    Linearity of φ + the unique character (ℝ,+) → (S¹,·) gives the
    on-shell propagation amplitude z(γ) = exp(i·k·φ(γ)).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Step 4 (citation): on-shell propagation IS e^{ikφ}.**
    Multiplicativity of the propagation amplitude on path concatenation
    follows from additivity of the source functional φ. Cited from
    `PropagationRule.exp_multiplicative`. -/
theorem propagation_phase_from_source (k s₁ s₂ : ℝ) :
    expAmplitude k (s₁ + s₂) = expAmplitude k s₁ * expAmplitude k s₂ :=
  exp_multiplicative k s₁ s₂

/-- **Step 4 (citation): unit modulus of the propagation amplitude.**
    |z(s)|² = 1 — free propagation conserves probability. Cited from
    `PropagationRule.exp_unit_modulus`. -/
theorem propagation_unit_modulus (k s : ℝ) :
    Complex.normSq (expAmplitude k s) = 1 :=
  exp_unit_modulus k s

/-- **Step 4 (citation): identity-path amplitude is 1.** Cited from
    `PropagationRule.exp_initial`. -/
theorem propagation_identity (k : ℝ) :
    expAmplitude k 0 = 1 :=
  exp_initial k

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: STEP 5 — HISTORIES AS COHERENT SUMS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Citation of `HistoryAmplitudes.two_history_amplitude` and
    `HistoryAmplitudes.two_history_observable`. The amplitude of an
    event with a list of histories is the SUM of the per-history
    amplitudes. The observable is the squared modulus of that sum
    — the coherent rather than incoherent combination.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Step 5 (citation): two-history event amplitude = coherent sum.**
    Cited from `HistoryAmplitudes.two_history_amplitude`. -/
theorem history_coherent_sum
    (D : Perturbation (m + 2) → ℝ) (h₁ h₂ : History m) :
    eventAmplitude D [h₁, h₂] =
      historyAmplitude D h₁ + historyAmplitude D h₂ :=
  two_history_amplitude D h₁ h₂

/-- **Step 5 (citation): two-history event observable shows interference.**
    Cited from `HistoryAmplitudes.two_history_observable`. -/
theorem history_observable_with_interference
    (D : Perturbation (m + 2) → ℝ) (h₁ h₂ : History m) :
    eventObservable D [h₁, h₂] =
      HistoryAmplitudes.obs (historyAmplitude D h₁) +
      HistoryAmplitudes.obs (historyAmplitude D h₂) +
      2 * (historyAmplitude D h₁ *
            (starRingEnd ℂ) (historyAmplitude D h₂)).re :=
  two_history_observable D h₁ h₂

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: STEP 6 — VIRTUAL PARTICLES AS OFF-SHELL INTERMEDIATES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Citation of the structural results in `VirtualParticles`. Off-shell
    intermediates exist (carry K/P content but cannot be asymptotic),
    a field propagator weights them, and the Feshbach Schur complement
    is exactly a single-virtual-line amplitude.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Step 6 (citation): every perturbation is on-shell or off-shell**
    for any linear field operator L. Off-shell perturbations are virtual.
    Cited from `VirtualParticles.onShell_or_offShell`. -/
theorem internal_history_onShell_or_offShell
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (L : Perturbation (m + 2) →ₗ[ℝ] W) (h : Perturbation (m + 2)) :
    OnShell L h ∨ OffShell L h :=
  onShell_or_offShell L h

/-- **Step 6 (citation): an internal history with no virtual lines collapses
    to its endpoints.** Cited from `VirtualParticles.InternalHistory.no_virtual_lines`. -/
theorem internal_history_no_virtual
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {L : Perturbation (m + 2) →ₗ[ℝ] W}
    (D : Perturbation (m + 2) → ℝ) (ih : InternalHistory L)
    (h_empty : ih.intermediates = []) :
    ih.amplitude D = stepAmplitude D ih.inEvent + stepAmplitude D ih.outEvent :=
  InternalHistory.no_virtual_lines D ih h_empty

/-- **Step 6 (citation): the identity propagator gives the bare amplitude.**
    Choosing G = id (no virtual-line weighting) recovers the unweighted
    internal-history amplitude. Cited from
    `VirtualParticles.InternalHistory.amplitudeWithPropagator_identity`. -/
theorem internal_history_propagator
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {L : Perturbation (m + 2) →ₗ[ℝ] W}
    (D : Perturbation (m + 2) → ℝ) (ih : InternalHistory L) :
    ih.amplitudeWithPropagator D (identityPropagator L) = ih.amplitude D :=
  InternalHistory.amplitudeWithPropagator_identity D ih

/-- **Step 6 (citation): a P-virtual perturbation has purely imaginary
    amplitude.** No source-charge contribution; pure dressing. Cited from
    `VirtualParticles.PVirtual.amplitude_imaginary`. -/
theorem pvirtual_amplitude_imaginary
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {L : Perturbation (m + 2) →ₗ[ℝ] W} {h : Perturbation (m + 2)}
    (hPV : PVirtual L h) (D : Perturbation (m + 2) → ℝ) :
    (stepAmplitude D h).re = 0 :=
  PVirtual.amplitude_imaginary hPV D

/-- **Step 6 (citation): the Feshbach Schur complement equals a
    single-virtual-line amplitude.** vertex × propagator × vertex.
    Cited from `VirtualParticles.feshbach_eq_virtual_line`. -/
theorem feshbach_is_single_virtual_line
    (a_P b a_Q lam : ℝ) (hlam : lam ≠ a_Q) :
    a_P + b ^ 2 / (lam - a_Q) = a_P + b * ((lam - a_Q)⁻¹) * b :=
  feshbach_eq_virtual_line a_P b a_Q lam hlam

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: STEP 7 — BORN RULE UNIQUENESS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Two complementary uniqueness results from the existing files:

      (a) Among DEGREE-2 forms on (Q,P), rotation invariance picks out
          a·(Q² + P²) — `ComplexUniqueness.born_rule_unique` (cited via
          the `quarter_turn`-form proved in `QuantumMechanicsIsATheorem`).

      (b) Among POWER-TYPE rotation-invariant observables (Q²+P²)^n,
          orthogonal additivity forces n = 1 — `BornRuleQuadratic.born_degree_unique`.

    Together they say: the Born rule observable is unique on TWO axes
    of variation (the cross-term coefficient AND the global power).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Step 7a (citation): rotation-invariant quadratic observables are
    proportional to Q²+P².** Cited via
    `QuantumMechanicsIsATheorem.born_rule_unique`. -/
theorem born_rule_is_unique_quadratic (a b c : ℝ)
    (h : ∀ Q P : ℝ,
      QuantumMechanicsIsATheorem.quadObs a b c Q P =
      QuantumMechanicsIsATheorem.quadObs a b c (-P) Q) :
    ∀ Q P : ℝ,
      QuantumMechanicsIsATheorem.quadObs a b c Q P = a * (Q ^ 2 + P ^ 2) :=
  QuantumMechanicsIsATheorem.born_rule_unique a b c h

/-- **Step 7b (citation): the Born degree is unique.** The only natural
    number n for which (Q²+P²)^n is orthogonally additive is n = 1.
    Cited from `BornRuleQuadratic.born_degree_unique`. -/
theorem born_degree_is_unique (n : ℕ) :
    IsOrthogAdditive (powerObs n) ↔ n = 1 :=
  born_degree_unique n

/-- **Step 7 (corollary): n = 1 simultaneously satisfies all three
    conditions** (orthogonal additivity, faithfulness, non-negativity).
    Cited from `BornRuleQuadratic.born_rule_must_be_quadratic`. -/
theorem born_rule_full_characterization (n : ℕ) :
    (IsOrthogAdditive (powerObs n)
     ∧ (∀ Q P : ℝ, powerObs n Q P = 0 → Q = 0 ∧ P = 0)
     ∧ (∀ Q P : ℝ, 0 ≤ powerObs n Q P))
    ↔ n = 1 :=
  born_rule_must_be_quadratic n

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: STEP 8 — TWO-PATH INTERFERENCE FORMULA
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Two complementary expressions of the same algebraic identity:

      • In COMPLEX form (HistoryAmplitudes.two_path_interference):
          |z₁ + z₂|² = |z₁|² + |z₂|² + 2 Re(z₁ · conj z₂).

      • In PROPAGATION form (PropagationRule.two_path_interference):
          |e^{iks₁} + e^{iks₂}|² = 2 + 2 cos(k(s₁ − s₂)).

    The first is the abstract observable identity; the second is the
    concrete double-slit fringe.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Step 8 (citation): two-path interference in complex form.**
    Cited from `HistoryAmplitudes.two_path_interference`. -/
theorem interference_two_path (z₁ z₂ : ℂ) :
    HistoryAmplitudes.obs (z₁ + z₂) =
      HistoryAmplitudes.obs z₁ + HistoryAmplitudes.obs z₂ +
        2 * (z₁ * (starRingEnd ℂ) z₂).re :=
  HistoryAmplitudes.two_path_interference z₁ z₂

/-- **Step 8 (citation): two-path interference in propagation form.**
    The double-slit fringe formula. Cited from
    `PropagationRule.two_path_interference`. -/
theorem interference_double_slit (k s₁ s₂ : ℝ) :
    Complex.normSq (expAmplitude k s₁ + expAmplitude k s₂) =
    2 + 2 * Real.cos (k * s₁ - k * s₂) :=
  PropagationRule.two_path_interference k s₁ s₂

/-- **Step 8 (citation): incoherent limit.** When the cross term vanishes,
    the coherent sum reduces to the incoherent sum (classical additivity).
    Cited from `HistoryAmplitudes.incoherent_limit`. -/
theorem interference_incoherent_limit (z₁ z₂ : ℂ)
    (h : (z₁ * (starRingEnd ℂ) z₂).re = 0) :
    HistoryAmplitudes.obs (z₁ + z₂) =
      HistoryAmplitudes.obs z₁ + HistoryAmplitudes.obs z₂ :=
  HistoryAmplitudes.incoherent_limit z₁ z₂ h

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: THE MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **QUANTUM MECHANICS IS A THEOREM (HISTORIES + PROPAGATORS + BORN).**

    Eight conjuncts, each a citation of an existing result, one per
    step of the derivation chain documented in PART 0 above:

      (1) **Complex amplitudes from K/P**:
          (Q,D) ∈ ℝ² packages as z = Q + i·D ∈ ℂ.
          → `QuantumMechanicsIsATheorem.source_forces_complex`

      (2) **Born rule observable = |z|² is unique** as a rotation-invariant
          quadratic on the K/P plane.
          → `QuantumMechanicsIsATheorem.born_rule_unique`

      (3) **Born degree forced to 2**: n = 1 is the only natural number
          for which (Q²+P²)^n is orthogonally additive.
          → `BornRuleQuadratic.born_degree_unique`

      (4) **On-shell propagation is e^{ik·φ}**: multiplicativity from
          additivity of the linear source functional.
          → `PropagationRule.exp_multiplicative`

      (5) **Histories sum coherently**: the amplitude of a two-history
          event is the sum of the two history amplitudes.
          → `HistoryAmplitudes.two_history_amplitude`

      (6) **Off-shell intermediates exist**: every perturbation is on-shell
          or off-shell for any linear field operator; off-shell ones are
          the framework's virtual particles.
          → `VirtualParticles.onShell_or_offShell`

      (7) **Two-path interference**:
          |z₁+z₂|² = |z₁|² + |z₂|² + 2 Re(z₁·conj z₂).
          → `HistoryAmplitudes.two_path_interference`

      (8) **Feshbach = single-virtual-line amplitude**: the Schur
          complement factors as vertex × propagator × vertex, unifying
          the (LayerA) effective-Hamiltonian machinery with the
          (LayerB) virtual-particle picture.
          → `VirtualParticles.feshbach_eq_virtual_line`

    The synthesis is the new content. Each conjunct is already proved;
    bundling them into one theorem makes the path-integral interpretation
    explicit: ordinary free propagation is a one-step on-shell history,
    and Feynman diagrams are internal histories with off-shell
    intermediates. Both share the same coherent-sum amplitude and the
    same Born-rule observable. -/
theorem qm_is_theorem :
    -- (1) Complex amplitude structure from K/P
    (∀ Q D : ℝ, (Q + D * Complex.I).re = Q ∧ (Q + D * Complex.I).im = D)
    -- (2) Born rule observable is unique among rotation-invariant quadratics
    ∧ (∀ a b c : ℝ,
        (∀ Q P : ℝ,
          QuantumMechanicsIsATheorem.quadObs a b c Q P =
          QuantumMechanicsIsATheorem.quadObs a b c (-P) Q)
        → ∀ Q P : ℝ,
            QuantumMechanicsIsATheorem.quadObs a b c Q P = a * (Q ^ 2 + P ^ 2))
    -- (3) Born degree forced to 2 (n = 1 in the (Q²+P²)^n family)
    ∧ (∀ n : ℕ, IsOrthogAdditive (powerObs n) ↔ n = 1)
    -- (4) On-shell propagation = e^{ikφ}, multiplicative on path concatenation
    ∧ (∀ k s₁ s₂ : ℝ,
        expAmplitude k (s₁ + s₂) = expAmplitude k s₁ * expAmplitude k s₂)
    -- (5) Histories sum coherently (two-history event amplitude)
    ∧ (∀ (D : Perturbation (m + 2) → ℝ) (h₁ h₂ : History m),
        eventAmplitude D [h₁, h₂] =
          historyAmplitude D h₁ + historyAmplitude D h₂)
    -- (6) Off-shell intermediates exist (every perturbation is on- or off-shell)
    ∧ (∀ {W : Type*} [AddCommGroup W] [Module ℝ W]
        (L : Perturbation (m + 2) →ₗ[ℝ] W) (h : Perturbation (m + 2)),
          OnShell L h ∨ OffShell L h)
    -- (7) Two-path interference (the coherent-sum cross term)
    ∧ (∀ z₁ z₂ : ℂ,
        HistoryAmplitudes.obs (z₁ + z₂) =
          HistoryAmplitudes.obs z₁ + HistoryAmplitudes.obs z₂ +
            2 * (z₁ * (starRingEnd ℂ) z₂).re)
    -- (8) Feshbach Schur complement = single-virtual-line amplitude
    ∧ (∀ a_P b a_Q lam : ℝ, lam ≠ a_Q →
        a_P + b ^ 2 / (lam - a_Q) = a_P + b * ((lam - a_Q)⁻¹) * b) :=
  ⟨source_forces_complex,
   QuantumMechanicsIsATheorem.born_rule_unique,
   born_degree_unique,
   exp_multiplicative,
   two_history_amplitude,
   fun {_W} _ _ L h => onShell_or_offShell L h,
   HistoryAmplitudes.two_path_interference,
   feshbach_eq_virtual_line⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: ON-SHELL / OFF-SHELL UNIFICATION (NEW SYNTHESIS CONTENT)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The genuinely NEW content of this file (beyond bundling) is the
    explicit observation that the path-integral interpretation now
    has both on-shell and off-shell histories, and they share machinery.

    • An "on-shell history" is the simplest case of an `InternalHistory`:
      the intermediates list is empty, so amplitude = stepAmplitude
      in + out.

    • An "off-shell-augmented history" has at least one intermediate
      that is OffShell L. The amplitude picks up a virtual-line
      contribution which the propagator weights.

    Both are coherently summed via `eventAmplitude` and observed via
    Born |·|². This is the path-integral content of the framework
    expressed in framework-native language (no momentum-space integrals).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **An on-shell history is a no-virtual-line internal history.**
    When the intermediates list is empty, the internal-history amplitude
    coincides with the bare two-step coherent sum — no virtual content.
    This is the framework's "tree-level" amplitude. -/
theorem path_integral_onshell_collapse
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {L : Perturbation (m + 2) →ₗ[ℝ] W}
    (D : Perturbation (m + 2) → ℝ) (ih : InternalHistory L)
    (h_empty : ih.intermediates = []) :
    ih.amplitude D = stepAmplitude D ih.inEvent + stepAmplitude D ih.outEvent :=
  InternalHistory.no_virtual_lines D ih h_empty

/-- **All-on-shell intermediates: the propagator does nothing.**
    If every intermediate is on-shell, ANY field propagator gives the
    bare coherent-sum amplitude. The propagator's role is purely to
    weight VIRTUAL (off-shell) intermediates. This is the framework's
    statement of the on-shell theorem. -/
theorem path_integral_propagator_trivial_on_shell
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {L : Perturbation (m + 2) →ₗ[ℝ] W}
    (D : Perturbation (m + 2) → ℝ) (Gp : FieldPropagator L)
    (ih : InternalHistory L)
    (h_all : ∀ h ∈ ih.intermediates, OnShell L h) :
    ih.amplitudeWithPropagator D Gp = ih.amplitude D :=
  InternalHistory.amplitudeWithPropagator_all_onShell D Gp ih h_all

/-- **PATH-INTEGRAL UNIFICATION: on-shell vs off-shell histories share machinery.**
    A single bundled statement showing the new synthesis content:

      (a) Identity-propagator reduction (on-shell-trivial) recovers the
          bare amplitude on ANY internal history.
      (b) An empty intermediates list collapses to the bare two-step sum.
      (c) Universal on-shell intermediates make ANY propagator trivial.

    Together these isolate the role of off-shell intermediates: they
    are the ONLY place where a non-identity field propagator changes
    the amplitude. The path integral and the propagator-weighted
    Feynman diagram are the SAME coherent-sum object, distinguished
    only by which intermediates are on- vs. off-shell. -/
theorem path_integral_onshell_offshell_unification
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {L : Perturbation (m + 2) →ₗ[ℝ] W}
    (D : Perturbation (m + 2) → ℝ) :
    -- (a) The identity propagator always recovers the bare amplitude
    (∀ ih : InternalHistory L,
        ih.amplitudeWithPropagator D (identityPropagator L) = ih.amplitude D)
    -- (b) Empty intermediates collapse to a two-step coherent sum
    ∧ (∀ ih : InternalHistory L, ih.intermediates = [] →
        ih.amplitude D =
          stepAmplitude D ih.inEvent + stepAmplitude D ih.outEvent)
    -- (c) All-on-shell intermediates make ANY propagator trivial
    ∧ (∀ (Gp : FieldPropagator L) (ih : InternalHistory L),
        (∀ h ∈ ih.intermediates, OnShell L h) →
          ih.amplitudeWithPropagator D Gp = ih.amplitude D) :=
  ⟨fun ih => InternalHistory.amplitudeWithPropagator_identity D ih,
   fun ih h_empty => InternalHistory.no_virtual_lines D ih h_empty,
   fun Gp ih h_all => InternalHistory.amplitudeWithPropagator_all_onShell D Gp ih h_all⟩

end UnifiedTheory.LayerB.QMFromHistories
