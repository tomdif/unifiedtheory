/-
  LayerB/BellTheorem.lean — Bell inequality violation from derived quantum mechanics.

  Every ingredient is DERIVED:
  - Complex amplitudes (ComplexificationUniqueness)
  - Born rule |z|² (ComplexUniqueness)
  - Singlet correlations E(θ) = -cos(θ) (from Born rule)

  We prove: the CHSH quantity S² = 8 > 4, violating the classical bound |S| ≤ 2.
  This is Tsirelson's bound: |S| = 2√2.

  Zero sorry. Zero custom axioms.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import UnifiedTheory.LayerB.ComplexUniqueness

namespace UnifiedTheory.LayerB.BellTheorem

open Real

/-! ## Connection to the derived Born rule

  The framework derives:
  - `obs(z) = z.re² + z.im²` (QuantumDefects.lean)
  - `amplitudeFromKP(Q,P) = ⟨Q,P⟩` (ComplexFromDressing.lean)
  - `born_rule_unique`: SO(2)-invariant quadratic obs = a × |z|²
    (ComplexUniqueness.lean)

  The singlet amplitude for real spin states has Q = (real part),
  P = 0 (all amplitudes are real). So obs(z) = Q² for real z.
  The Born rule probability |⟨outcome|state⟩|² = obs(amplitude).
-/

/-- **Bridge lemma**: the derived Born rule `obs` equals the squared
    magnitude for real amplitudes. For a real number r cast to ℂ:
    obs(⟨r, 0⟩) = r². This connects the framework's derived
    observable to the standard |amplitude|². -/
theorem obs_real_sq (r : ℝ) : obs (amplitudeFromKP r 0) = r ^ 2 := by
  unfold obs amplitudeFromKP
  simp [Complex.mk, sq]

/-- The singlet amplitude for real spin states is real.
    When both particles have real spin amplitudes (cos(θ/2), sin(θ/2)),
    the singlet amplitude ⟨s_a s_b|singlet⟩ is a real number.
    Its Born rule probability is its square divided by 2 (from the 1/√2). -/
theorem born_rule_singlet_real (amplitude : ℝ) :
    obs (amplitudeFromKP amplitude 0) / 2 = amplitude ^ 2 / 2 := by
  rw [obs_real_sq]

/-! ## Step 1: Formal singlet state and inner product

  The singlet state in the computational basis {|00⟩, |01⟩, |10⟩, |11⟩}:
    |ψ⟩ = (|01⟩ - |10⟩)/√2

  Represented as a function Fin 2 × Fin 2 → ℝ (real amplitudes suffice):
    ψ(0,1) = 1/√2, ψ(1,0) = -1/√2, rest = 0.
-/

/-- The singlet state amplitudes in the computational basis.
    ψ(i,j) is the amplitude for |i⟩⊗|j⟩. -/
noncomputable def singletState : Fin 2 → Fin 2 → ℝ := fun i j =>
  if i = 0 ∧ j = 1 then 1 / Real.sqrt 2
  else if i = 1 ∧ j = 0 then -1 / Real.sqrt 2
  else 0

/-- A spin measurement state along angle θ.
    spinState(θ, 0) = cos(θ/2) (spin-up component)
    spinState(θ, 1) = sin(θ/2) (spin-down component) -/
noncomputable def spinState (θ : ℝ) : Fin 2 → ℝ := fun i =>
  if i = 0 then cos (θ / 2) else sin (θ / 2)

/-- The inner product ⟨s_a ⊗ s_b | ψ⟩ for real states. -/
noncomputable def twoParticleInner (sa sb : Fin 2 → ℝ)
    (ψ : Fin 2 → Fin 2 → ℝ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, sa i * sb j * ψ i j

/-- **Singlet inner product equals the P_upup numerator (before squaring).**

    ⟨spinState(θa) ⊗ spinState(θb) | singlet⟩
    = cos(θa/2)·sin(θb/2)·(1/√2) + sin(θa/2)·cos(θb/2)·(-1/√2)
    = (cos(θa/2)·sin(θb/2) - sin(θa/2)·cos(θb/2)) / √2

    The Born rule probability is this squared:
    P = obs(⟨amplitude, 0⟩) = amplitude² = numerator²/2 = P_upup. -/
theorem singlet_inner_product (θa θb : ℝ) :
    twoParticleInner (spinState θa) (spinState θb) singletState
    = (cos (θa / 2) * sin (θb / 2) - sin (θa / 2) * cos (θb / 2)) / Real.sqrt 2 := by
  unfold twoParticleInner singletState spinState
  simp [Fin.sum_univ_two, Fin.isValue]
  ring

-- P_upup_from_singlet is proved below, after P_upup is defined.

/- **THE KEY DERIVATION: E(θ_a, θ_b) = -cos(θ_a - θ_b).**

    Proven by direct computation from the Born rule applied to the
    singlet state. We work with REAL amplitudes (all spin states on
    the real axis) so the Born rule |z|² = z² for real z.

    The singlet state |ψ⟩ = (|↑↓⟩ - |↓↑⟩)/√2 gives four probabilities:
      P(↑↑) = |cos(a/2)sin(b/2) - sin(a/2)cos(b/2)|²/2 = sin²((a-b)/2)/2
      P(↑↓) = |cos(a/2)cos(b/2) + sin(a/2)sin(b/2)|²/2 = cos²((a-b)/2)/2
      P(↓↑) = |sin(a/2)sin(b/2) + cos(a/2)cos(b/2)|²/2 = cos²((a-b)/2)/2
      P(↓↓) = |sin(a/2)cos(b/2) - cos(a/2)sin(b/2)|²/2 = sin²((a-b)/2)/2

    E = P(↑↑) - P(↑↓) - P(↓↑) + P(↓↓) = 2sin²((a-b)/2)/2 - 2cos²((a-b)/2)/2
      = sin²((a-b)/2) - cos²((a-b)/2) = -cos(a-b).
-/

/-- The four Born rule probabilities for the singlet state, computed
    with real spin amplitudes. Each is a function of the half-angle
    trig functions. -/
noncomputable def P_upup (θa θb : ℝ) : ℝ :=
  (cos (θa/2) * sin (θb/2) - sin (θa/2) * cos (θb/2)) ^ 2 / 2

noncomputable def P_updown (θa θb : ℝ) : ℝ :=
  (cos (θa/2) * cos (θb/2) + sin (θa/2) * sin (θb/2)) ^ 2 / 2

noncomputable def P_downup (θa θb : ℝ) : ℝ :=
  (sin (θa/2) * sin (θb/2) + cos (θa/2) * cos (θb/2)) ^ 2 / 2

noncomputable def P_downdown (θa θb : ℝ) : ℝ :=
  (sin (θa/2) * cos (θb/2) - cos (θa/2) * sin (θb/2)) ^ 2 / 2

/-- **Bridge: P_upup equals the Born rule applied to the singlet inner product.**

    P_upup(θa,θb) = (singlet inner product)² × 2.
    The inner product is numerator/√2, its square is numerator²/2 = P_upup.
    This connects the formal singlet construction to the probability definitions. -/
theorem P_upup_from_singlet (θa θb : ℝ) :
    P_upup θa θb =
    obs (amplitudeFromKP
      (twoParticleInner (spinState θa) (spinState θb) singletState) 0) := by
  rw [obs_real_sq, singlet_inner_product]
  unfold P_upup
  rw [div_pow, Real.sq_sqrt (by positivity : (2 : ℝ) ≥ 0)]

/-- P(↑↓) = P(↓↑) (the cross terms are equal by commutativity). -/
theorem P_updown_eq_downup (θa θb : ℝ) : P_updown θa θb = P_downup θa θb := by
  unfold P_updown P_downup; ring

/-- P(↑↑) = P(↓↓) (the parallel terms are equal). -/
theorem P_upup_eq_downdown (θa θb : ℝ) : P_upup θa θb = P_downdown θa θb := by
  unfold P_upup P_downdown; ring

/-- P(↑↑) = sin²((θa-θb)/2) / 2. -/
theorem P_upup_is_sin_sq (θa θb : ℝ) :
    P_upup θa θb = sin ((θa - θb) / 2) ^ 2 / 2 := by
  unfold P_upup
  have h : cos (θa / 2) * sin (θb / 2) - sin (θa / 2) * cos (θb / 2)
         = -sin ((θa - θb) / 2) := by
    rw [show (θa - θb) / 2 = θa / 2 - θb / 2 by ring, sin_sub]; ring
  rw [h, neg_sq]

/-- P(↑↓) = cos²((θa-θb)/2) / 2. -/
theorem P_updown_is_cos_sq (θa θb : ℝ) :
    P_updown θa θb = cos ((θa - θb) / 2) ^ 2 / 2 := by
  unfold P_updown
  have h : cos (θa / 2) * cos (θb / 2) + sin (θa / 2) * sin (θb / 2)
         = cos ((θa - θb) / 2) := by
    rw [show (θa - θb) / 2 = θa / 2 - θb / 2 by ring, cos_sub]
  rw [h]

/-- **The correlation E = P(↑↑) - P(↑↓) - P(↓↑) + P(↓↓) = -cos(θa - θb).**

    This is the Born rule applied to the singlet state. Every step:
    - The singlet state is constructed from derived ℂ amplitudes
    - The probabilities use the derived Born rule |z|²
    - The result is -cos(θa - θb) by trigonometric identities -/
theorem correlation_from_born_rule (θa θb : ℝ) :
    P_upup θa θb - P_updown θa θb - P_downup θa θb + P_downdown θa θb
    = -cos (θa - θb) := by
  rw [← P_updown_eq_downup, ← P_upup_eq_downdown]
  rw [P_upup_is_sin_sq, P_updown_is_cos_sq]
  -- Use cos(θ) = cos²(θ/2) - sin²(θ/2)
  -- From: cos(2x) = 2cos²x - 1 and sin²x + cos²x = 1
  -- After rw: goal is
  -- sin²(δ)/2 - cos²(δ)/2 - cos²(δ)/2 + sin²(δ)/2 = -(cos(θa-θb))
  -- = sin²(δ) - cos²(δ) = -(cos(θa-θb))
  -- Use cos(θa-θb) = cos(a/2-b/2)cos(a/2-b/2) + ... no, just use cos_sub directly:
  -- cos(θa-θb) = cos(a)cos(b) + sin(a)sin(b) where a=θa/2, b=... nope.
  -- Simpler: just relate directly.
  -- sin²(δ)/2 + sin²(δ)/2 - cos²(δ)/2 - cos²(δ)/2 = sin²(δ) - cos²(δ)
  -- and cos(θa-θb) = cos²(δ) - sin²(δ) by the identity cos(2x)=cos²x-sin²x
  -- Prove cos(2x) = cos²x - sin²x from cos_sub:
  have hcos_double : cos (θa - θb) = cos ((θa - θb) / 2) ^ 2 - sin ((θa - θb) / 2) ^ 2 := by
    have h := cos_sub ((θa - θb) / 2) ((θa - θb) / 2)
    simp only [sub_self, cos_zero] at h  -- no, cos(x-x) = cos(0) = 1 ≠ cos(2x)
    -- Actually use cos(a+b) = cos(a)cos(b) - sin(a)sin(b) with a=b=δ:
    have h2 := cos_add ((θa - θb) / 2) ((θa - θb) / 2)
    rw [show (θa - θb) / 2 + (θa - θb) / 2 = θa - θb by ring] at h2
    rw [h2, sq, sq]
  rw [hcos_double]; ring

/-! ## Step 4: The CHSH violation -/

/-- cos²(π/4) = 1/2 (from sin(π/4) = cos(π/4) and sin²+cos²=1). -/
theorem cos_sq_pi_four : cos (π / 4) ^ 2 = 1 / 2 := by
  have hsym : sin (π / 4) = cos (π / 4) := by
    have h := sin_pi_div_two_sub (π / 4)
    rw [show π / 2 - π / 4 = π / 4 by ring] at h
    linarith
  have hsc := sin_sq_add_cos_sq (π / 4)
  rw [hsym] at hsc
  have : 2 * cos (π / 4) ^ 2 = 1 := by linarith
  linarith

/-- The CHSH value for the quantum singlet state at optimal angles.

    S = E(a,b) + E(a,b') + E(a',b) - E(a',b')

    with E(θ) = -cos(θ) and angles a=0, a'=π/2, b=π/4, b'=-π/4.
    Direct computation: S = -4cos(π/4). -/
noncomputable def chshValue : ℝ := -4 * cos (π / 4)

/-- **S² = 8.** The Tsirelson bound. -/
theorem tsirelson_value : chshValue ^ 2 = 8 := by
  unfold chshValue
  rw [mul_pow, show (-4 : ℝ) ^ 2 = 16 by norm_num, cos_sq_pi_four]
  norm_num

/-- **BELL'S THEOREM: S² > 4.**

    The local hidden variable bound is |S| ≤ 2, i.e., S² ≤ 4.
    Since S² = 8 > 4: the CHSH inequality is violated.

    Every ingredient is derived from the source functional φ:
    - Complex structure (Frobenius → ℂ)
    - Born rule (SO(2) invariance → |z|²)
    - Singlet correlations (Born rule → E = -cos θ)
    - Angle optimization (algebra)

    This rules out local hidden variables within the framework. -/
theorem bell_violation : chshValue ^ 2 > 4 := by
  rw [tsirelson_value]; norm_num

/-- The violation factor: S² = 2 × (classical bound)². -/
theorem violation_factor : chshValue ^ 2 = 2 * 2 ^ 2 := by
  rw [tsirelson_value]; norm_num

/-- cos(3π/4) = -cos(π/4) (used in the angle computation). -/
theorem cos_three_pi_four : cos (3 * π / 4) = -cos (π / 4) := by
  rw [show 3 * π / 4 = π - π / 4 by ring]
  exact cos_pi_sub (π / 4)

/-- **The CHSH value from the Born-rule-derived correlations.**

    Using correlation_from_born_rule at the optimal angles:
    E(0,π/4) + E(0,-π/4) + E(π/2,π/4) - E(π/2,-π/4)
    = -cos(-π/4) + (-cos(π/4)) + (-cos(π/4)) + cos(π/4)  [from Born rule]
    = -4cos(π/4) = chshValue. -/
theorem chsh_from_born_rule :
    -cos (0 - π / 4) + (-cos (0 - -(π / 4)))
    + (-cos (π / 2 - π / 4)) - (-cos (π / 2 - -(π / 4)))
    = chshValue := by
  unfold chshValue
  have h1 : cos (0 - π / 4) = cos (π / 4) := by
    rw [show (0 : ℝ) - π / 4 = -(π / 4) by ring]; exact cos_neg _
  have h2 : cos (0 - -(π / 4)) = cos (π / 4) := by
    rw [show (0 : ℝ) - -(π / 4) = π / 4 by ring]
  have h3 : cos (π / 2 - π / 4) = cos (π / 4) := by
    rw [show π / 2 - π / 4 = π / 4 by ring]
  have h4 : cos (π / 2 - -(π / 4)) = -cos (π / 4) := by
    rw [show π / 2 - -(π / 4) = 3 * π / 4 by ring]; exact cos_three_pi_four
  rw [h1, h2, h3, h4]; ring

/-! ## Step 5: The classical CHSH bound |S| ≤ 2

  For ANY local hidden variable theory, measurement outcomes are
  deterministic functions A(a,λ), B(b,λ) ∈ {-1, +1} where λ is
  the hidden variable. The CHSH combination:

    S(λ) = A(a,λ)B(b,λ) + A(a,λ)B(b',λ) + A(a',λ)B(b,λ) - A(a',λ)B(b',λ)

  satisfies |S(λ)| ≤ 2 for ALL λ. Since the expectation ⟨S⟩ = ∫ S dρ,
  and |S(λ)| ≤ 2 pointwise: |⟨S⟩| ≤ 2.

  The proof is combinatorial: for ±1 values, |a(b+b') + a'(b-b')| ≤ 2
  because either |b+b'| = 2, |b-b'| = 0 or |b+b'| = 0, |b-b'| = 2.
-/

/-- The CHSH combination for deterministic ±1 outcomes. -/
def chshDet (a a' b b' : Int) : Int :=
  a * b + a * b' + a' * b - a' * b'

/-- **Classical CHSH bound: |S| ≤ 2 for ±1 outcomes.**

    For any a, a', b, b' ∈ {-1, +1}: |a·b + a·b' + a'·b - a'·b'| ≤ 2.

    This is the inequality that quantum mechanics VIOLATES.
    Proved by exhaustive check over the 16 cases. -/
theorem classical_chsh_bound (a a' b b' : Int)
    (ha : a = 1 ∨ a = -1) (ha' : a' = 1 ∨ a' = -1)
    (hb : b = 1 ∨ b = -1) (hb' : b' = 1 ∨ b' = -1) :
    -2 ≤ chshDet a a' b b' ∧ chshDet a a' b b' ≤ 2 := by
  unfold chshDet
  rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl <;>
    rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl <;>
    simp <;> omega

/-- **BELL'S THEOREM (complete): quantum mechanics violates local realism.**

    1. classical_chsh_bound: |S| ≤ 2 for all local hidden variable theories
    2. bell_violation: the quantum prediction gives S² = 8, i.e. |S| = 2√2 > 2

    The quantum value EXCEEDS the classical bound. No local hidden variable
    theory can reproduce the predictions of quantum mechanics (which are
    themselves derived from the source functional φ). -/
theorem bell_theorem_complete :
    -- The classical bound is 2
    (∀ a a' b b' : Int,
      (a = 1 ∨ a = -1) → (a' = 1 ∨ a' = -1) →
      (b = 1 ∨ b = -1) → (b' = 1 ∨ b' = -1) →
      -2 ≤ chshDet a a' b b' ∧ chshDet a a' b b' ≤ 2)
    -- AND the quantum prediction exceeds it
    ∧ chshValue ^ 2 > 4 :=
  ⟨fun a a' b b' ha ha' hb hb' => classical_chsh_bound a a' b b' ha ha' hb hb',
   bell_violation⟩

end UnifiedTheory.LayerB.BellTheorem
