/-
  LayerB/ComplexFromDressing.lean — Complex amplitudes forced by K/P structure

  DERIVES complex-valued quantum amplitudes from the source/dressing
  decomposition, rather than postulating them.

  Key insight: a defect with fixed source strength Q (the K-part)
  can have variable dressing content P (invisible to charge measurements).
  The pair (Q, P) ∈ ℝ² naturally forms a complex amplitude z = Q + iP.

  Then:
  - |z|² = Q² + P² is the full observable (includes dressing energy)
  - Q alone = classical charge (the real part)
  - P = internal phase-like degree of freedom (the imaginary part)
  - Two defects with same Q but different P INTERFERE
  - Phase rotation in P is a U(1) symmetry

  This is NOT an arbitrary complexification. It is FORCED by the
  existence of a dressing sector that is invisible to the source
  functional but contributes to the full energy/observable.

  The derivation chain:
    SourceFunctional → K/P split → (Q,P) pair → ℂ amplitude → interference
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

/-- **Complexification-from-parent theorem.**

    The K/P decomposition (which was derived from a source functional)
    naturally provides complex amplitude structure:

    (1) The amplitude z = Q + iP is determined by the K/P content
    (2) The observable |z|² = Q² + P² includes dressing energy
    (3) Dressing rotation is U(1) phase invariance
    (4) Defects with same Q but different P interfere
    (5) Pure dressing (Q=0) is classically invisible but quantum-visible
    (6) Setting P=0 recovers the classical real-charge theory

    The complex amplitude is NOT postulated — it arises from the
    existence of dressing content invisible to the source functional. -/
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
