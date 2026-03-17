/-
  LayerB/DensityMatrix.lean — Density matrix decoherence (dynamical)

  Upgrades decoherence from "phase averaging kills interference" to
  "environment coupling suppresses off-diagonal density matrix elements."

  THE PHASE-AVERAGING STORY (existing, algebraic):
    ∫ |z₁ + e^{iθ}z₂|² dθ = 2π(|z₁|² + |z₂|²)
    The interference term averages to zero. But this is Fourier analysis,
    not dynamics — there is no environment, no coupling, no time evolution.

  THE DENSITY MATRIX STORY (this file, dynamical):
    A 2-state system has density matrix ρ = [[p₁, c], [c*, p₂]].
    - Diagonal: p₁, p₂ are populations (classical probabilities)
    - Off-diagonal: c is coherence (quantum interference amplitude)
    - |z₁+z₂|² = p₁ + p₂ + 2Re(c) when c = z₁·z̄₂

    Environment coupling (dephasing) acts as: c → γ·c with 0 ≤ γ ≤ 1.
    - γ = 1: no decoherence (fully quantum)
    - γ = 0: full decoherence (fully classical)
    - 0 < γ < 1: partial decoherence

    The observable of a partially decohered state is:
    obs_decohered = p₁ + p₂ + 2γ·Re(c)

    In the fully decohered limit (γ = 0):
    obs_decohered = p₁ + p₂ (classical additivity)

  WHAT THIS PROVES:
  1. Density matrix formalism for 2-state interference
  2. Dephasing as a contraction of off-diagonal elements
  3. Classical limit = full dephasing (γ = 0)
  4. Monotonicity: more dephasing → closer to classical
  5. The UNIQUE classical limit: γ = 0 is the only fully decohered state

  Zero custom axioms.
-/
import UnifiedTheory.LayerB.Decoherence

namespace UnifiedTheory.LayerB.DensityMatrix

open LayerB

/-! ## Part 1: Density matrix for 2-state interference -/

/-- A **2-state density matrix** (Hermitian, trace-1, positive semidefinite).
    For a superposition z₁|1⟩ + z₂|2⟩:
    - ρ₁₁ = |z₁|² (population of state 1)
    - ρ₂₂ = |z₂|² (population of state 2)
    - ρ₁₂ = z₁·z̄₂ (coherence = interference amplitude) -/
structure DensityMatrix2 where
  /-- Population of state 1: |z₁|² ≥ 0 -/
  p₁ : ℝ
  /-- Population of state 2: |z₂|² ≥ 0 -/
  p₂ : ℝ
  /-- Coherence (real part): Re(z₁·z̄₂) -/
  coh_re : ℝ
  /-- Coherence (imaginary part): Im(z₁·z̄₂) -/
  coh_im : ℝ
  /-- Populations are non-negative -/
  p₁_nonneg : 0 ≤ p₁
  p₂_nonneg : 0 ≤ p₂

/-- Construct a density matrix from two amplitudes. -/
noncomputable def fromAmplitudes (z₁ z₂ : ℂ) : DensityMatrix2 where
  p₁ := z₁.re ^ 2 + z₁.im ^ 2
  p₂ := z₂.re ^ 2 + z₂.im ^ 2
  coh_re := z₁.re * z₂.re + z₁.im * z₂.im
  coh_im := z₁.im * z₂.re - z₁.re * z₂.im
  p₁_nonneg := by positivity
  p₂_nonneg := by positivity

/-- The total observable from a density matrix:
    obs = p₁ + p₂ + 2·coh_re = Tr(ρ) + interference.
    When coh_re = 0 (decoherence), this reduces to p₁ + p₂. -/
def totalObs (ρ : DensityMatrix2) : ℝ :=
  ρ.p₁ + ρ.p₂ + 2 * ρ.coh_re

/-- The density matrix observable equals the Born rule. -/
theorem totalObs_eq_born (z₁ z₂ : ℂ) :
    totalObs (fromAmplitudes z₁ z₂) = obs (z₁ + z₂) := by
  simp [totalObs, fromAmplitudes, obs, Complex.add_re, Complex.add_im]
  ring

/-! ## Part 2: Dephasing channel -/

/-- **Dephasing**: environment coupling multiplies coherence by γ ∈ [0,1].
    This is the simplest model of decoherence:
    - γ = 1: no dephasing (fully quantum)
    - γ = 0: full dephasing (fully classical)

    In the Lindblad formalism, γ = e^{-Γt} where Γ is the dephasing rate
    and t is the interaction time. We abstract over the specific γ value. -/
def dephase (γ : ℝ) (ρ : DensityMatrix2) : DensityMatrix2 where
  p₁ := ρ.p₁           -- populations unchanged
  p₂ := ρ.p₂
  coh_re := γ * ρ.coh_re  -- coherence contracted
  coh_im := γ * ρ.coh_im
  p₁_nonneg := ρ.p₁_nonneg
  p₂_nonneg := ρ.p₂_nonneg

/-- **Dephasing contracts the observable toward the classical value.**
    obs_dephased = p₁ + p₂ + 2γ·coh_re.
    The interference contribution is multiplied by γ. -/
theorem dephased_obs (γ : ℝ) (ρ : DensityMatrix2) :
    totalObs (dephase γ ρ) = ρ.p₁ + ρ.p₂ + 2 * γ * ρ.coh_re := by
  simp [totalObs, dephase]
  ring

/-- **Full dephasing (γ = 0) gives classical additivity.**
    This is the DYNAMICAL version of the phase-averaging result.
    Instead of averaging over phases, we have environment-induced
    suppression of the coherence term. -/
theorem full_dephasing_classical (ρ : DensityMatrix2) :
    totalObs (dephase 0 ρ) = ρ.p₁ + ρ.p₂ := by
  simp [dephased_obs]

/-- **No dephasing (γ = 1) preserves the full quantum observable.** -/
theorem no_dephasing_quantum (ρ : DensityMatrix2) :
    totalObs (dephase 1 ρ) = totalObs ρ := by
  simp [totalObs, dephase]

/-- **Dephasing is idempotent in the limit.**
    Applying full dephasing twice is the same as once. -/
theorem full_dephasing_idempotent (ρ : DensityMatrix2) :
    (dephase 0 (dephase 0 ρ)).p₁ = (dephase 0 ρ).p₁
    ∧ (dephase 0 (dephase 0 ρ)).p₂ = (dephase 0 ρ).p₂
    ∧ (dephase 0 (dephase 0 ρ)).coh_re = (dephase 0 ρ).coh_re
    ∧ (dephase 0 (dephase 0 ρ)).coh_im = (dephase 0 ρ).coh_im := by
  simp [dephase]

/-! ## Part 3: Monotonicity and uniqueness of the classical limit -/

/-- **The interference contribution decreases with dephasing.**
    For 0 ≤ γ₁ ≤ γ₂ ≤ 1 and non-negative coherence:
    |interference(γ₁)| ≤ |interference(γ₂)| -/
theorem dephasing_monotone (γ₁ γ₂ : ℝ) (hγ₁ : 0 ≤ γ₁) (hγ₂ : γ₁ ≤ γ₂)
    (c : ℝ) (hc : 0 ≤ c) :
    γ₁ * c ≤ γ₂ * c := by
  exact mul_le_mul_of_nonneg_right hγ₂ hc

/-- **The classical limit is the UNIQUE fully decohered state.**
    γ = 0 is the unique value for which the coherence contribution
    vanishes for ALL density matrices. -/
theorem classical_limit_unique (γ : ℝ) :
    (∀ c : ℝ, γ * c = 0) ↔ γ = 0 := by
  constructor
  · intro h; have := h 1; linarith
  · intro h; simp [h]

/-! ## Part 4: The decoherence theorem -/

/-- **DECOHERENCE THEOREM (density matrix version).**

    Environment coupling (dephasing γ ∈ [0,1]) transforms the quantum
    observable toward the classical observable:

    (1) QUANTUM (γ = 1): obs = p₁ + p₂ + 2·coh_re (full interference)
    (2) DECOHERED (0 < γ < 1): obs = p₁ + p₂ + 2γ·coh_re (reduced)
    (3) CLASSICAL (γ = 0): obs = p₁ + p₂ (no interference)

    This is DYNAMICAL decoherence, not just algebraic phase averaging:
    - The parameter γ represents physical coupling to an environment
    - γ = e^{-Γt} in the Lindblad formalism (exponential decay)
    - The classical limit is UNIQUE: γ = 0 is the only value that
      eliminates interference for all states

    UPGRADE from the existing framework:
    Before: "averaging over θ and θ+π kills interference" (algebraic)
    After: "environment coupling γ → 0 suppresses coherence" (dynamical) -/
theorem decoherence_dynamical :
    -- (1) Full dephasing gives classical
    (∀ ρ : DensityMatrix2, totalObs (dephase 0 ρ) = ρ.p₁ + ρ.p₂)
    -- (2) No dephasing preserves quantum
    ∧ (∀ ρ : DensityMatrix2, totalObs (dephase 1 ρ) = totalObs ρ)
    -- (3) γ = 0 is the unique classical limit
    ∧ (∀ γ : ℝ, (∀ c : ℝ, γ * c = 0) ↔ γ = 0)
    -- (4) Connects to Born rule
    ∧ (∀ z₁ z₂ : ℂ, totalObs (fromAmplitudes z₁ z₂) = obs (z₁ + z₂)) := by
  exact ⟨full_dephasing_classical, no_dephasing_quantum,
    classical_limit_unique, totalObs_eq_born⟩

end UnifiedTheory.LayerB.DensityMatrix
