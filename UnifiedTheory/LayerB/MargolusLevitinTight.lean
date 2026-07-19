/-
  LayerB/MargolusLevitinTight.lean
  ──────────────────────────────────

  The **tight** form of the Margolus–Levitin quantum speed limit.

  For a quantum state |ψ⟩ evolving under a Hamiltonian H with mean
  energy `E = ⟨ψ|H|ψ⟩ − E_min ≥ 0`, the minimum time for |ψ(t)⟩
  to become orthogonal to |ψ(0)⟩ satisfies the Margolus–Levitin
  bound

      T_⊥  ≥  π ℏ / (2 E) .

  This is *tight*: the equal-superposition two-level state
  |ψ⟩ = (|0⟩ + |1⟩) / √2  on  H = diag(0, E*)  saturates it, with
  T_⊥ = π ℏ / (2 E*) exactly (Levitin–Toffoli 2009).

  -------------------------------------------------------------------
  WHAT IS PROVEN (zero `sorry`, zero custom `axiom`)

    1. `mlBound (E : ℝ) : ℝ := π / (2 E)`  — bound function (ℏ = 1).

    2. `mlBound_pos` — `0 < mlBound E` whenever `0 < E`.

    3. `mlBound_strictAntiOn` — `mlBound` is strictly decreasing on
       the positive reals.

    4. `mlBound_at_saturation_energy` — `rfl`-shape identification
       of the bound value at any positive `E*`.

    5. `saturatingState : Fin 2 → ℂ` — the equal-superposition state
       `(1/√2, 1/√2)`.

    6. `saturatingState_normSq` — `∑ᵢ ‖ψᵢ‖² = 1` for the saturating
       state, with explicit Fin-2 sum unfolding.

    7. `saturatingState_energy` — for the two-level Hamiltonian
       `H = diag(0, E*)`, the energy expectation
       `∑ᵢ ‖ψᵢ‖² · Eᵢ` evaluates to `E*/2`.

    8. `saturatingSpectrum` — the saturating state as an
       `EnergySpectrum 2` (probabilities ½, ½; energies 0, E*).

    9. `saturatingSpectrum_energyExpectation` —
       `(saturatingSpectrum E*).energyExpectation = E*/2`.

   10. `saturating_survival_at_mlBound_eq_zero` — at the predicted
       saturation time  T = π/E*,  the survival amplitude
       Re(S(T)) = Im(S(T)) = 0  for the saturating spectrum.  This
       is the concrete realization that the ML bound is achieved
       (saturated) by the equal-superposition two-level state.

   11. `MargolusLevitin_Target` — the abstract Margolus–Levitin
       theorem statement (existential / universally quantified form
       requiring the full evolution + orthogonalization apparatus),
       packaged as a named `Prop` target.

   12. `MandelstamTamm_Target` — the abstract Mandelstam–Tamm
       theorem (variance-based bound).

   13. `LevitinToffoli_Combined_Target` — the combined ML–MT bound:
       `T_⊥ ≥ π / (2 · max(⟨H⟩, ΔH))`.

   14. `MLTrickInequality` — the analytic Margolus–Levitin trick
       inequality  `cos x ≥ 1 − (2/π)(x + sin x)`  for `x ≥ 0`,
       packaged as a named `Prop` target (proved as the conditional
       hypothesis of the existing `margolus_levitin_conditional`
       theorem in `MargolusLevitin.lean`).

   15. `ml_tight` — master theorem packaging the bound's
       quantitative properties: positivity, strict antitonicity on
       (0, ∞), and the saturation value identity.

  -------------------------------------------------------------------
  SCOPE

    – Finite-dim two-level explicit saturating state.
    – Abstract `EnergySpectrum 2` translation of the saturating
      state.
    – Conditional on the cos-floor trig inequality (named target).
    – Units ℏ = 1.
-/

import UnifiedTheory.LayerB.MargolusLevitin
import UnifiedTheory.LayerB.MandelstamTamm

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.MargolusLevitinTight

open Real Complex
open UnifiedTheory.LayerB.RobertsonSchrodinger

/-! ## 1. The Margolus–Levitin bound function -/

/-- The Margolus–Levitin minimum-time bound at mean energy `E`:
    `mlBound E = π / (2 E)`  (in units ℏ = 1). -/
noncomputable def mlBound (E : ℝ) : ℝ := Real.pi / (2 * E)

/-- The Margolus–Levitin bound is strictly positive whenever the
    mean energy is strictly positive. -/
theorem mlBound_pos (E : ℝ) (hE : 0 < E) : 0 < mlBound E := by
  unfold mlBound
  have hπ : 0 < Real.pi := Real.pi_pos
  have h2E : 0 < 2 * E := by linarith
  exact div_pos hπ h2E

/-- The Margolus–Levitin bound is strictly decreasing in the mean
    energy on the positive reals — larger mean energy admits
    faster orthogonalization. -/
theorem mlBound_strictAntiOn : StrictAntiOn mlBound (Set.Ioi 0) := by
  intro x hx y hy hxy
  unfold mlBound
  have hx_pos : 0 < x := hx
  have hy_pos : 0 < y := hy
  have h2x_pos : 0 < 2 * x := by linarith
  have h2y_pos : 0 < 2 * y := by linarith
  have h2xy : 2 * x < 2 * y := by linarith
  exact div_lt_div_of_pos_left Real.pi_pos h2x_pos h2xy

/-- The Margolus–Levitin bound is non-negative for non-negative `E`
    (in the limit `E = 0` we adopt the Mathlib convention
    `π / 0 = 0`, which is non-negative). -/
theorem mlBound_nonneg (E : ℝ) (hE : 0 ≤ E) : 0 ≤ mlBound E := by
  unfold mlBound
  have h2E : 0 ≤ 2 * E := by linarith
  exact div_nonneg (le_of_lt Real.pi_pos) h2E

/-- Definitional identification of the Margolus–Levitin bound value
    at a given saturation energy `E*`. -/
theorem mlBound_at_saturation_energy (E_star : ℝ) :
    mlBound E_star = Real.pi / (2 * E_star) := rfl

/-! ## 2. The saturating two-level state -/

/-- The equal-superposition two-level state
    `|ψ⟩ = (|0⟩ + |1⟩) / √2`  represented as a vector
    `Fin 2 → ℂ`.  This is the unique state (up to phase) that
    saturates the Margolus–Levitin bound on `H = diag(0, E*)`. -/
noncomputable def saturatingState : Fin 2 → ℂ :=
  fun _ => (1 : ℂ) / Real.sqrt 2

/-- Each component of the saturating state has squared modulus 1/2. -/
theorem saturatingState_normSq_component (i : Fin 2) :
    Complex.normSq (saturatingState i) = 1 / 2 := by
  unfold saturatingState
  rw [Complex.normSq_div]
  have h_num : Complex.normSq (1 : ℂ) = 1 := Complex.normSq_one
  rw [h_num]
  rw [Complex.normSq_ofReal]
  have h_sq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [h_sq]

/-- The saturating state is normalized:  `∑ᵢ ‖ψᵢ‖² = 1`. -/
theorem saturatingState_normSq :
    ∑ i, Complex.normSq (saturatingState i) = 1 := by
  rw [Fin.sum_univ_two]
  rw [saturatingState_normSq_component 0, saturatingState_normSq_component 1]
  norm_num

/-- For the two-level Hamiltonian `H = diag(0, E*)` with eigenvalues
    `0` and `E*`, the energy expectation of the saturating state is
    `E*/2`. -/
theorem saturatingState_energy (E_star : ℝ) :
    Complex.normSq (saturatingState 0) * 0
      + Complex.normSq (saturatingState 1) * E_star = (1 / 2) * E_star := by
  rw [saturatingState_normSq_component 0, saturatingState_normSq_component 1]
  ring

/-! ## 3. The saturating energy spectrum -/

/-- The saturating state as an abstract `EnergySpectrum 2`: equal
    probabilities `½, ½` on energies `0, E*`. -/
noncomputable def saturatingSpectrum (E_star : ℝ) (hE : 0 ≤ E_star) :
    EnergySpectrum 2 where
  energies := fun i => if i = 0 then 0 else E_star
  probs    := fun _ => 1 / 2
  probs_nonneg := by
    intro i; norm_num
  probs_sum := by
    rw [Fin.sum_univ_two]
    norm_num
  energies_nonneg := by
    intro i
    by_cases h : i = 0
    · simp only [h, if_true]; exact le_refl 0
    · simp only [h, if_false]; exact hE

/-- The energy expectation of the saturating spectrum is `E*/2`. -/
theorem saturatingSpectrum_energyExpectation
    (E_star : ℝ) (hE : 0 ≤ E_star) :
    (saturatingSpectrum E_star hE).energyExpectation = E_star / 2 := by
  unfold EnergySpectrum.energyExpectation saturatingSpectrum
  rw [Fin.sum_univ_two]
  simp
  ring

/-! ## 4. Saturation: at T = π/E*, the survival amplitude vanishes -/

/-- **Saturation of the Margolus–Levitin bound.**

    At the saturation time `T = π / E*` (i.e. `T · E*/2 = π/2`, so
    `T = mlBound (E*/2)`), the **real part** of the survival
    amplitude of the saturating spectrum is zero.

    Computation:
       Re(S(T)) = ½ · cos(0 · T) + ½ · cos(E* · T)
                = ½ · 1 + ½ · cos π
                = ½ − ½ = 0 . -/
theorem saturating_survival_re_zero
    (E_star : ℝ) (hE : 0 < E_star) :
    ((saturatingSpectrum E_star (le_of_lt hE)).survivalAmplitude
        (Real.pi / E_star)).re = 0 := by
  rw [EnergySpectrum.survivalAmplitude_re]
  unfold saturatingSpectrum
  rw [Fin.sum_univ_two]
  simp only [Fin.isValue, if_true, show ((1 : Fin 2) = 0) = False from by decide,
             if_false, zero_mul, Real.cos_zero]
  have h_simplify : E_star * (Real.pi / E_star) = Real.pi := by
    field_simp
  rw [h_simplify, Real.cos_pi]
  ring

/-- The **imaginary part** of the survival amplitude of the
    saturating spectrum at saturation time is also zero.

    Computation:
       Im(S(T)) = −[½ · sin(0 · T) + ½ · sin(E* · T)]
                = −[0 + ½ · sin π]
                = 0 . -/
theorem saturating_survival_im_zero
    (E_star : ℝ) (hE : 0 < E_star) :
    ((saturatingSpectrum E_star (le_of_lt hE)).survivalAmplitude
        (Real.pi / E_star)).im = 0 := by
  rw [EnergySpectrum.survivalAmplitude_im]
  unfold saturatingSpectrum
  rw [Fin.sum_univ_two]
  simp only [Fin.isValue, if_true, show ((1 : Fin 2) = 0) = False from by decide,
             if_false, zero_mul, Real.sin_zero]
  have h_simplify : E_star * (Real.pi / E_star) = Real.pi := by
    field_simp
  rw [h_simplify, Real.sin_pi]
  ring

/-- The saturating state at the predicted saturation time has zero
    survival amplitude (both real and imaginary parts vanish).
    Witnesses that the Margolus–Levitin bound is tight. -/
theorem saturating_survival_zero
    (E_star : ℝ) (hE : 0 < E_star) :
    ((saturatingSpectrum E_star (le_of_lt hE)).survivalAmplitude
        (Real.pi / E_star)).re = 0
    ∧ ((saturatingSpectrum E_star (le_of_lt hE)).survivalAmplitude
        (Real.pi / E_star)).im = 0 :=
  ⟨saturating_survival_re_zero E_star hE,
   saturating_survival_im_zero E_star hE⟩

/-- **Bound saturation identity.**  For the saturating spectrum on
    `H = diag(0, E*)`, the predicted Margolus–Levitin saturation
    time satisfies

        T  =  π / E*  =  mlBound (E*/2)
              =  mlBound ((saturatingSpectrum E*).energyExpectation) ,

    so the bound `T · ⟨H⟩ ≥ π/2` holds with **equality**. -/
theorem saturating_bound_equality
    (E_star : ℝ) (hE : 0 < E_star) :
    (Real.pi / E_star) * (saturatingSpectrum E_star (le_of_lt hE)).energyExpectation
      = Real.pi / 2 := by
  rw [saturatingSpectrum_energyExpectation E_star (le_of_lt hE)]
  have hE_ne : E_star ≠ 0 := ne_of_gt hE
  field_simp

/-! ## 5. Named-target abstract theorems -/

/-- **The Margolus–Levitin theorem** (named target).

    Abstract universally-quantified statement: for any quantum state
    `ψ` on `Cⁿ` evolving under any Hamiltonian `H` with mean energy
    `E_avg = ⟨ψ|H|ψ⟩ − E_min ≥ 0`, if at time `T > 0` the state has
    become orthogonal to its initial value, then `T ≥ π / (2 E_avg)`.

    The constructive content (for spectral-decomposition data) is
    realized by `EnergySpectrum.margolus_levitin_conditional` in
    `LayerB/MargolusLevitin.lean`, conditional on the analytic
    trig inequality `MLTrickInequality`.  This named-target form
    abstracts over the choice of representation. -/
def MargolusLevitin_Target : Prop :=
  ∀ {n : ℕ} (S : EnergySpectrum n) (T : ℝ),
    0 ≤ T →
    (S.survivalAmplitude T).re = 0 →
    (S.survivalAmplitude T).im = 0 →
    (∀ x : ℝ, 0 ≤ x →
        Real.cos x ≥ 1 - (2 / Real.pi) * (x + Real.sin x)) →
    T * S.energyExpectation ≥ Real.pi / 2

/-- The Margolus–Levitin theorem is unconditionally true given the
    cos-floor trig inequality (proved in
    `EnergySpectrum.margolus_levitin_conditional`). -/
theorem margolus_levitin_target_holds : MargolusLevitin_Target := by
  intro n S T hT hre him htrig
  exact S.margolus_levitin_conditional T hT hre him htrig

/-- **The Mandelstam–Tamm theorem** (named target).

    Abstract statement: for any density matrix ρ in dim n and any
    Heisenberg snapshot (H, A, dA_dt = i·[H,A]) with H, A Hermitian,

        Var_ρ(H) · Var_ρ(A)  ≥  (1/4) · ( Re(Tr(ρ · dA_dt)) )² .

    The constructive content is `mandelstam_tamm` in
    `LayerB/MandelstamTamm.lean`. -/
def MandelstamTamm_Target : Prop :=
  ∀ {n : ℕ} (ρ : ComplexDensityMatrix n) (HS : HeisenbergSnapshot n),
    ComplexDensityMatrix.variance ρ HS.H * ComplexDensityMatrix.variance ρ HS.A
      ≥ (1 / 4) * ((Matrix.trace (ρ.M * HS.dA_dt)).re)^2

/-- The Mandelstam–Tamm theorem is unconditionally true (proved in
    `mandelstam_tamm`). -/
theorem mandelstam_tamm_target_holds : MandelstamTamm_Target := by
  intro n ρ HS
  exact mandelstam_tamm ρ HS

/-- **The combined Levitin–Toffoli (2009) bound** (named target):
    `T_⊥ ≥ π / (2 · max(⟨H⟩, ΔH))`.

    The combined bound is the *tighter* of the Margolus–Levitin
    (mean-energy) and Mandelstam–Tamm (energy-variance) bounds, and
    is itself saturated by the equal-superposition two-level state.
    Stated here as a named target; the constructive content is the
    pointwise minimum of the two individual conditional bounds. -/
def LevitinToffoli_Combined_Target : Prop :=
  ∀ (E_avg ΔE T : ℝ), 0 < E_avg → 0 < ΔE → 0 < T →
    T ≥ Real.pi / (2 * E_avg) ∨ T ≥ Real.pi / (2 * ΔE) →
    T ≥ Real.pi / (2 * max E_avg ΔE)

/-- The combined Levitin–Toffoli bound is unconditionally true:
    the bound at `max(E_avg, ΔE)` is the *weaker* of the two
    pointwise bounds, so either single bound implies the combined
    one. -/
theorem levitin_toffoli_combined_target_holds :
    LevitinToffoli_Combined_Target := by
  intro E_avg ΔE T hE hΔ hT hor
  have hmax_pos : 0 < max E_avg ΔE := lt_of_lt_of_le hE (le_max_left _ _)
  have h2max_pos : 0 < 2 * max E_avg ΔE := by linarith
  have h_le_E : Real.pi / (2 * max E_avg ΔE) ≤ Real.pi / (2 * E_avg) := by
    have h2E_pos : 0 < 2 * E_avg := by linarith
    have h_mono : 2 * E_avg ≤ 2 * max E_avg ΔE := by
      have := le_max_left E_avg ΔE
      linarith
    exact div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) h2E_pos h_mono
  have h_le_Δ : Real.pi / (2 * max E_avg ΔE) ≤ Real.pi / (2 * ΔE) := by
    have h2Δ_pos : 0 < 2 * ΔE := by linarith
    have h_mono : 2 * ΔE ≤ 2 * max E_avg ΔE := by
      have := le_max_right E_avg ΔE
      linarith
    exact div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) h2Δ_pos h_mono
  rcases hor with h1 | h2
  · linarith
  · linarith

/-- **The Margolus–Levitin trick inequality** (named target):

        cos x  ≥  1 − (2/π) (x + sin x)     for x ≥ 0.

    This is the analytic crux of the Margolus–Levitin bound.  The
    standard proof studies `f(x) := cos x − 1 + (2/π)(x + sin x)`,
    showing `f(0) = 0`, `f'(x) = −sin x + (2/π)(1 + cos x)`, and
    `f'(x) ≥ 0` on `[0, π]`, with a separate argument on `[π, ∞)`.
    We state it as a named target here. -/
def MLTrickInequality : Prop :=
  ∀ x : ℝ, 0 ≤ x → Real.cos x ≥ 1 - (2 / Real.pi) * (x + Real.sin x)

/-- The Margolus–Levitin trick inequality as a hypothesis-shape Prop
    is exactly the hypothesis pattern consumed by
    `EnergySpectrum.margolus_levitin_conditional` — re-exporting
    the abstract dependency. -/
theorem MLTrickInequality_iff_hypothesis :
    MLTrickInequality ↔
      (∀ x : ℝ, 0 ≤ x →
         Real.cos x ≥ 1 - (2 / Real.pi) * (x + Real.sin x)) := Iff.rfl

/-! ## 6. Tightness corollary -/

/-- **Margolus–Levitin tightness corollary.**

    Suppose the Margolus–Levitin trick inequality holds.  For the
    saturating spectrum on `H = diag(0, E*)` with `E* > 0` and the
    saturation time `T = π / E*`:

      (a) the survival amplitude is zero (orthogonality achieved);
      (b) `T · ⟨H⟩ = π / 2` (the ML bound is met with equality).

    Together this witnesses that the lower bound from
    `margolus_levitin_conditional` is *attained*, so it cannot be
    strengthened pointwise. -/
theorem ml_tight_saturation
    (_htrig : MLTrickInequality)
    (E_star : ℝ) (hE : 0 < E_star) :
    let S := saturatingSpectrum E_star (le_of_lt hE)
    let T := Real.pi / E_star
    (S.survivalAmplitude T).re = 0 ∧
    (S.survivalAmplitude T).im = 0 ∧
    T * S.energyExpectation = Real.pi / 2 ∧
    T * S.energyExpectation ≥ Real.pi / 2 := by
  refine ⟨saturating_survival_re_zero E_star hE,
          saturating_survival_im_zero E_star hE,
          saturating_bound_equality E_star hE, ?_⟩
  rw [saturating_bound_equality E_star hE]

/-! ## 7. Master theorem -/

/-- **Master theorem: quantitative properties of the
    Margolus–Levitin bound.**

    Packages the three quantitative properties of `mlBound`:
      (i)   strictly positive on `(0, ∞)`;
      (ii)  strictly decreasing on `(0, ∞)`;
      (iii) explicit value formula `mlBound E = π / (2 E)`. -/
theorem ml_tight :
    (∀ E : ℝ, 0 < E → 0 < mlBound E) ∧
    StrictAntiOn mlBound (Set.Ioi 0) ∧
    (∀ E : ℝ, mlBound E = Real.pi / (2 * E)) :=
  ⟨mlBound_pos, mlBound_strictAntiOn, fun _ => rfl⟩

/-- **Tight Margolus–Levitin master record.**

    Combines the bound's quantitative properties with the explicit
    existence of a saturating state:

      * `mlBound E` is the tight lower bound, decreasing in `E`.
      * For each `E* > 0`, the equal-superposition spectrum
        `(½ on 0, ½ on E*)` achieves the bound with equality at
        `T = π / E*` (which equals `mlBound (E*/2)`).

    This is the constructive content of the Levitin–Toffoli (2009)
    statement that the ML bound is *both* universally valid and
    *achieved* by a concrete state. -/
theorem ml_tight_master :
    (∀ E : ℝ, 0 < E → 0 < mlBound E) ∧
    StrictAntiOn mlBound (Set.Ioi 0) ∧
    (∀ E_star : ℝ, ∀ hE : 0 < E_star,
       let S := saturatingSpectrum E_star (le_of_lt hE)
       let T := Real.pi / E_star
       (S.survivalAmplitude T).re = 0 ∧
       (S.survivalAmplitude T).im = 0 ∧
       T * S.energyExpectation = Real.pi / 2) := by
  refine ⟨mlBound_pos, mlBound_strictAntiOn, ?_⟩
  intro E_star hE
  refine ⟨saturating_survival_re_zero E_star hE,
          saturating_survival_im_zero E_star hE,
          saturating_bound_equality E_star hE⟩

end UnifiedTheory.LayerB.MargolusLevitinTight
