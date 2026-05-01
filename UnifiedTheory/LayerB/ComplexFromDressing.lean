/-
  LayerB/ComplexFromDressing.lean — Properties of the canonical
  complexification on the K/P pair.

  Given the K/P real pair (Q, P) — derived from a source functional in
  `LayerA.DerivedBFSplit` — the canonical SO(2)-invariant complexification
  (Q, P) ↦ Q + iP yields a complex amplitude with the standard observable
  structure: |z|² = Q² + P², U(1) phase invariance, dressing-induced
  interference, classical limit at P = 0.

  This complexification is the *unique* 2D commutative real division algebra
  (`LayerB/ComplexificationUniqueness.lean`, ~180 lines, fully proved) and
  the *unique* rotation-invariant quadratic observable up to scale
  (`LayerB/ComplexUniqueness.lean`, ~145 lines, fully proved). Each
  uniqueness theorem takes as hypothesis the structure that does the work
  (an algebra structure, or an SO(2) action) and shows ℂ is forced given
  that structure.

  The order-theoretic origin of either the SO(2) symmetry or the
  division-algebra structure on the K/P plane is treated as open. See
  `PHASE4_DIAGNOSTIC.md` for the surviving open derivation question
  (the SO(2) action on (Q, P) is currently stipulated via the
  `phaseRotate θ` definition in `LayerB.QuantumDefects`, not derived
  from causal-poset / K_F data).

  The derivation chain (with hypotheses made explicit):
    SourceFunctional → K/P split [LayerA.DerivedBFSplit, derived]
    → real pair (Q, P) ∈ ℝ²       [derived]
    → SO(2) action on (Q, P)      [stipulated; open question]
    → ℂ amplitude                  [forced from SO(2) by ComplexUniqueness]
    → interference                 [forced from ℂ amplitude, derived below]
-/
import UnifiedTheory.LayerB.QuantumDefects
import UnifiedTheory.LayerA.DerivedBFSplit

namespace UnifiedTheory.LayerB

open UnifiedTheory.LayerA

/-! ### The complexification from K/P -/

/-- A defect amplitude constructed from source (K) and dressing (P) content.
    z = Q + iP where Q = source strength, P = dressing strength. -/
def amplitudeFromKP (Q P : ℝ) : ℂ := ⟨Q, P⟩

/-- The observable of a K/P defect is Q² + P² = |z|². -/
theorem obs_from_KP (Q P : ℝ) :
    obs (amplitudeFromKP Q P) = Q ^ 2 + P ^ 2 := by
  simp [obs, amplitudeFromKP]

/-- Classical charge is the real part of the amplitude. -/
theorem charge_is_real_part (Q P : ℝ) :
    (amplitudeFromKP Q P).re = Q := rfl

/-- Dressing content is the imaginary part of the amplitude. -/
theorem dressing_is_imag_part (Q P : ℝ) :
    (amplitudeFromKP Q P).im = P := rfl

/-! ### Dressing rotation = U(1) phase -/

/-- Rotating the dressing content by angle θ while preserving charge:
    (Q, P) → (Q cos θ - P sin θ, Q sin θ + P cos θ).
    This IS phase rotation e^{iθ}z in the complex representation. -/
noncomputable def dressingRotation (θ : ℝ) (Q P : ℝ) : ℂ :=
  phaseRotate θ (amplitudeFromKP Q P)

/-- **Dressing rotation preserves the observable.**
    Rotating internal dressing content doesn't change |z|².
    This is the U(1) gauge invariance derived from dressing invisibility. -/
theorem dressing_rotation_preserves_obs (θ Q P : ℝ) :
    obs (dressingRotation θ Q P) = obs (amplitudeFromKP Q P) :=
  phase_invariance θ (amplitudeFromKP Q P)

/-! ### Interference from dressing -/

/-- **Two defects with same charge but different dressing interfere.**
    If d₁ = (Q, P₁) and d₂ = (Q, P₂), their composite amplitude
    is (2Q, P₁ + P₂), and the observable is NOT 2(Q² + P₁²):
    it depends on the relative dressing content. -/
theorem dressing_causes_interference (Q P₁ P₂ : ℝ) :
    obs (amplitudeFromKP Q P₁ + amplitudeFromKP Q P₂) =
    obs (amplitudeFromKP Q P₁) + obs (amplitudeFromKP Q P₂) +
    interferenceTerm (amplitudeFromKP Q P₁) (amplitudeFromKP Q P₂) :=
  interference_formula _ _

/-- **The interference term depends on dressing alignment.**
    For (Q, P₁) and (Q, P₂), the interference is 2(Q² + P₁P₂).
    When P₁ = P₂ (aligned dressing): constructive.
    When P₁ = -P₂ (anti-aligned): can be destructive. -/
theorem interference_is_dressing_dependent (Q P₁ P₂ : ℝ) :
    interferenceTerm (amplitudeFromKP Q P₁) (amplitudeFromKP Q P₂) =
    2 * (Q * Q + P₁ * P₂) := by
  simp [interferenceTerm, amplitudeFromKP]

/-- **Destructive dressing interference**: two defects with same charge Q
    but opposite dressing (P, -P) have reduced total observable compared
    to aligned dressing (P, P). -/
theorem destructive_dressing_sign (Q P : ℝ) (hP : P ≠ 0) :
    interferenceTerm (amplitudeFromKP Q P) (amplitudeFromKP Q (-P)) <
    interferenceTerm (amplitudeFromKP Q P) (amplitudeFromKP Q P) := by
  rw [interference_is_dressing_dependent, interference_is_dressing_dependent]
  have hP2 : 0 < P * P := mul_self_pos.mpr hP
  linarith

/-! ### Pure dressing defects = pure phase -/

/-- A **pure dressing defect** has Q = 0 and P ≠ 0.
    It carries no classical charge but has nonzero observable.
    It is a pure phase excitation. -/
theorem pure_dressing_zero_charge (P : ℝ) :
    (amplitudeFromKP 0 P).re = 0 := rfl

theorem pure_dressing_nonzero_obs (P : ℝ) (hP : P ≠ 0) :
    0 < obs (amplitudeFromKP 0 P) := by
  simp [obs, amplitudeFromKP]
  positivity

/-- **Pure dressing defects are classically invisible but quantum-visible.**
    A pure dressing defect has zero classical charge but nonzero
    quantum observable. This is the hallmark of quantum vacuum effects. -/
theorem quantum_vacuum_effect (P : ℝ) (hP : P ≠ 0) :
    (amplitudeFromKP 0 P).re = 0 ∧ 0 < obs (amplitudeFromKP 0 P) :=
  ⟨rfl, pure_dressing_nonzero_obs P hP⟩

/-! ### Classical limit -/

/-- **Classical defects have zero dressing (P = 0).**
    They sit on the real axis of ℂ and don't interfere with
    each other (the interference term is purely from Q, no phase). -/
theorem classical_defects_real (Q : ℝ) :
    amplitudeFromKP Q 0 = (Q : ℂ) := by
  simp [amplitudeFromKP, Complex.ext_iff, Complex.ofReal_re, Complex.ofReal_im]

/-- **Classical limit**: when all defects have P = 0, the interference
    term between them is 2Q₁Q₂, and the observable algebra reduces
    to the classical one. -/
theorem classical_interference_term (Q₁ Q₂ : ℝ) :
    interferenceTerm (amplitudeFromKP Q₁ 0) (amplitudeFromKP Q₂ 0) =
    2 * Q₁ * Q₂ := by
  simp [interferenceTerm, amplitudeFromKP]
  ring

/-! ### The derivation theorem -/

/-- **Properties of the canonical K/P complexification.**

    Given the canonical SO(2)-invariant complexification (Q, P) ↦ Q + iP —
    which is uniquely determined among 2D commutative real division
    algebras with multiplicative norm by `ComplexificationUniqueness`,
    and uniquely determined among rotation-invariant quadratic observables
    up to scale by `ComplexUniqueness` — the K/P amplitude has the
    standard complex-amplitude properties:

    (1) The observable is |z|² = Q² + P² (Born rule)
    (2) Dressing rotation is U(1) phase invariance (preserves observable)
    (3) Defects with same Q but different P interfere
    (4) Pure dressing (Q=0) is classically invisible but quantum-visible
    (5) Setting P=0 recovers the classical real-charge theory

    The order-theoretic origin of either the SO(2) symmetry or the
    division-algebra structure on the K/P plane is treated as open.
    See `PHASE4_DIAGNOSTIC.md`. -/
theorem complexification_from_parent :
    -- (1) Observable = Q² + P²
    (∀ Q P, obs (amplitudeFromKP Q P) = Q ^ 2 + P ^ 2)
    -- (2) U(1) phase invariance
    ∧ (∀ θ Q P, obs (dressingRotation θ Q P) = obs (amplitudeFromKP Q P))
    -- (3) Dressing causes interference
    ∧ (∀ Q P₁ P₂, obs (amplitudeFromKP Q P₁ + amplitudeFromKP Q P₂) =
        obs (amplitudeFromKP Q P₁) + obs (amplitudeFromKP Q P₂) +
        interferenceTerm (amplitudeFromKP Q P₁) (amplitudeFromKP Q P₂))
    -- (4) Pure dressing is quantum-visible
    ∧ (∀ P, P ≠ 0 → (amplitudeFromKP 0 P).re = 0 ∧ 0 < obs (amplitudeFromKP 0 P))
    -- (5) Classical limit
    ∧ (∀ Q, amplitudeFromKP Q 0 = (Q : ℂ)) :=
  ⟨obs_from_KP,
   dressing_rotation_preserves_obs,
   fun Q P₁ P₂ => dressing_causes_interference Q P₁ P₂,
   quantum_vacuum_effect,
   classical_defects_real⟩

end UnifiedTheory.LayerB
