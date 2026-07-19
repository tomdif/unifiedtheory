/-
  LayerB/QuantumJarzynski.lean
  ─────────────────────────────

  **Quantum Jarzynski equality** (Tasaki 2000; Talkner–Lutz–Hänggi 2007).

  A finite-dimensional quantum system has a time-dependent Hamiltonian
  driven from `H₀ = H(0)` to `H₁ = H(τ)` over time `τ`.  Starting in
  the thermal state `ρ₀ := exp(-β H₀) / Z₀`, the two-time-measurement
  scheme measures energy at `t = 0` (outcome `E_n^0`), evolves under
  the unitary `U_τ`, and measures energy at `t = τ` (outcome `E_m^1`).
  The **work** is `W := E_m^1 − E_n^0`.

  Averaging `exp(-β W)` over the joint probability of outcomes gives
  the **Jarzynski equality**:

      ⟨exp(-β W)⟩  =  Z₁ / Z₀  =  exp(-β (F₁ − F₀))  =  exp(-β ΔF),

  where `Z(H) := Tr exp(-β H)` is the partition function and
  `F(H) := -(1/β) log Z(H)` is the Helmholtz free energy.

  ## Proof sketch

  Let `U₀, U₁` be eigenvector unitaries of `H₀, H₁` and let `λ_n^0,
  λ_m^1` be the corresponding (real) eigenvalues.  In the mixed basis
  the transition amplitudes are encoded by

      W_{mn}  :=  (star U₁ · U_τ · U₀)_{mn} ,

  so `|⟨m|U_τ|n⟩|² = ‖W_{mn}‖²` and the doubly-unitary product `W` is
  unitary, hence row sums of `‖W_{mn}‖²` are 1:

      ∑_n ‖W_{mn}‖²  =  (W · star W)_{mm}  =  I_{mm}  =  1 .

  The Jarzynski average is

      ⟨exp(-β W)⟩  =  (1/Z₀) · ∑_{n,m} exp(-β λ_n^0) · ‖W_{mn}‖² ·
                                        exp(-β (λ_m^1 − λ_n^0))
                   =  (1/Z₀) · ∑_{n,m} ‖W_{mn}‖² · exp(-β λ_m^1)
                   =  (1/Z₀) · ∑_m exp(-β λ_m^1) · ∑_n ‖W_{mn}‖²
                   =  (1/Z₀) · ∑_m exp(-β λ_m^1)
                   =  Z₁ / Z₀ .

  The Boltzmann factor `exp(-β λ_n^0)` cancels against the
  `exp(β λ_n^0)` hidden inside `exp(-β (λ_m^1 − λ_n^0))`, leaving the
  initial-Boltzmann factor entirely absent from the final sum.  This
  is the algebraic heart of Jarzynski.

  Finally, by definition of free energy:

      Z₁ / Z₀  =  exp(log Z₁ − log Z₀)
              =  exp(-β · (F₁ − F₀))  =  exp(-β ΔF) ,

  provided `Z₀, Z₁ > 0` (automatic for `β > 0`, since `exp(-β x) > 0`).

  ## What this file ships

    * `JarzynskiProtocol n`           — the two-time-measurement data.
    * `partitionFunction β H`         — `Tr exp(-β H)` (real part).
    * `partitionFunction_eq_sum_exp`  — `Z(H) = ∑_i exp(-β λ_i)`.
    * `partitionFunction_pos`         — `Z(H) > 0` when `β > 0`.
    * `freeEnergy β H`                — `-(1/β) · log Z(H)`.
    * `jarzynskiAverage P`            — the spectral double-sum
                                        defining `⟨exp(-β W)⟩`.
    * `quantum_jarzynski_partition`   — `⟨exp(-β W)⟩ = Z₁ / Z₀`.
    * `quantum_jarzynski`             — `⟨exp(-β W)⟩ = exp(-β ΔF)`.

  ## Honest scoping

    * The two-time-measurement *probabilities* (`p_n =
      exp(-β E_n^0)/Z_0`, `|⟨m|U|n⟩|²`) are taken as the *definition*
      of `jarzynskiAverage`.  We do not derive them from a projective
      measurement postulate — that derivation is a separate quantum-
      measurement formalisation.
    * `partitionFunction` is real (the `.re` of the matrix trace of the
      CFC).  `Tr exp(-β H)` is real because `exp(-β H)` is Hermitian
      whenever `H` is; the `.re` just selects the canonical real form.
    * `freeEnergy` requires `β > 0` and `Z > 0` (both supplied).
    * Finite-dimensional Hilbert space (Mathlib's `Matrix (Fin n) (Fin n) ℂ`).
    * The unitary `U_τ` is taken as data; we do not solve the
      time-dependent Schrödinger equation `U_τ = T exp(-i ∫ H(t) dt)`.

  Zero `sorry`, zero custom `axiom`; only the three Lean kernel
  axioms `[propext, Classical.choice, Quot.sound]`.
-/

import UnifiedTheory.LayerB.UnitaryInvariance
import UnifiedTheory.LayerB.SpectralFunctionalCalculus
import UnifiedTheory.LayerB.SpectralDensityMatrix
import UnifiedTheory.LayerB.LandauerPrinciple
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.QuantumJarzynski

open Matrix Complex Unitary
open scoped ComplexOrder

/-! ## 1. The Jarzynski protocol (data) -/

/-- A two-time-measurement protocol on a finite-dimensional quantum
    system: an initial and final Hamiltonian (both Hermitian), a
    unitary evolution operator between them, and an inverse
    temperature `β > 0`. -/
structure JarzynskiProtocol (n : ℕ) where
  /-- Initial Hamiltonian `H(0)`. -/
  H_0 : Matrix (Fin n) (Fin n) ℂ
  /-- Final Hamiltonian `H(τ)`. -/
  H_1 : Matrix (Fin n) (Fin n) ℂ
  /-- `H_0` is Hermitian (real spectrum). -/
  H_0_isHerm : H_0.IsHermitian
  /-- `H_1` is Hermitian (real spectrum). -/
  H_1_isHerm : H_1.IsHermitian
  /-- Time evolution operator `U_τ = T exp(-i ∫₀^τ H(t) dt)`. -/
  U_τ : Matrix (Fin n) (Fin n) ℂ
  /-- `U_τ` is unitary. -/
  U_τ_unitary : U_τ ∈ Matrix.unitaryGroup (Fin n) ℂ
  /-- Inverse temperature. -/
  β : ℝ
  /-- Strict positivity of `β`. -/
  β_pos : 0 < β

namespace JarzynskiProtocol

variable {n : ℕ} (P : JarzynskiProtocol n)

/-- Eigenvalues of `H_0` (real). -/
noncomputable def E_0 (i : Fin n) : ℝ := P.H_0_isHerm.eigenvalues i

/-- Eigenvalues of `H_1` (real). -/
noncomputable def E_1 (i : Fin n) : ℝ := P.H_1_isHerm.eigenvalues i

/-- Eigenvector unitary of `H_0`: columns are eigenvectors. -/
noncomputable def U_0 : Matrix (Fin n) (Fin n) ℂ :=
  P.H_0_isHerm.eigenvectorUnitary.val

/-- Eigenvector unitary of `H_1`: columns are eigenvectors. -/
noncomputable def U_1 : Matrix (Fin n) (Fin n) ℂ :=
  P.H_1_isHerm.eigenvectorUnitary.val

/-- `U_0` is unitary. -/
theorem U_0_unitary : P.U_0 ∈ Matrix.unitaryGroup (Fin n) ℂ :=
  P.H_0_isHerm.eigenvectorUnitary.property

/-- `U_1` is unitary. -/
theorem U_1_unitary : P.U_1 ∈ Matrix.unitaryGroup (Fin n) ℂ :=
  P.H_1_isHerm.eigenvectorUnitary.property

end JarzynskiProtocol

/-! ## 2. The partition function `Z(H) := Tr exp(-β H)` -/

/-- **Partition function**, `Z(H) := Re Tr exp(-β H)`.

    Implemented via the continuous functional calculus.  `exp(-β H)`
    is Hermitian (so its trace is real), and the `.re` projection
    just extracts the canonical real form. -/
noncomputable def partitionFunction {n : ℕ} (β : ℝ)
    (H : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (cfc (fun x => Real.exp (-β * x)) H).trace.re

/-! ### 2.1 Spectral form of `cfc` on a Hermitian matrix -/

/-- For a Hermitian `H`, the CFC of a real function unfolds to the
    unitary-diagonalisation form

      `cfc f H = U · diagonal (ofReal ∘ f ∘ λ) · star U`. -/
private lemma cfc_hermitian_diagonalForm {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (f : ℝ → ℝ) :
    cfc f H
      = hH.eigenvectorUnitary.val
          * Matrix.diagonal (fun i => ((f (hH.eigenvalues i) : ℝ) : ℂ))
          * star hH.eigenvectorUnitary.val := by
  have h_eq : cfc f H = hH.cfc f := Matrix.IsHermitian.cfc_eq hH f
  rw [h_eq]
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply]
  rfl

/-- Trace cyclicity through a unitary conjugation. -/
private lemma trace_conj_unitary {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (U * M * star U) = Matrix.trace M := by
  rw [Matrix.trace_mul_cycle]
  have h1 : star U * U = 1 := by
    rw [Matrix.mem_unitaryGroup_iff'] at hU
    exact hU
  rw [h1, Matrix.one_mul]

/-- **Trace formula for `cfc f H` on a Hermitian matrix.**

    `Tr (cfc f H) = ∑ᵢ (ofReal (f λᵢ) : ℂ)` where `λᵢ` are the
    eigenvalues of `H`. -/
private lemma trace_cfc_hermitian {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (f : ℝ → ℝ) :
    (cfc f H).trace
      = ∑ i, ((RCLike.ofReal (f (hH.eigenvalues i)) : ℂ)) := by
  rw [cfc_hermitian_diagonalForm H hH f,
      trace_conj_unitary _ hH.eigenvectorUnitary.property,
      Matrix.trace_diagonal]
  rfl

/-- **Real-part trace formula** for `cfc f H`. -/
private lemma re_trace_cfc_hermitian {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (f : ℝ → ℝ) :
    (cfc f H).trace.re = ∑ i, f (hH.eigenvalues i) := by
  rw [trace_cfc_hermitian H hH f, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact Complex.ofReal_re _

/-! ### 2.2 Partition function as a spectral sum -/

/-- **Partition function as a spectral sum.**

    `Z(H) = ∑ᵢ exp(-β λᵢ)` where `λᵢ` are the eigenvalues of `H`. -/
theorem partitionFunction_eq_sum_exp {n : ℕ} (β : ℝ)
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    partitionFunction β H
      = ∑ i, Real.exp (-β * hH.eigenvalues i) := by
  unfold partitionFunction
  exact re_trace_cfc_hermitian H hH (fun x => Real.exp (-β * x))

/-! ### 2.3 Strict positivity of the partition function -/

/-- **Partition function strict positivity** (for `n > 0`).

    Each term `exp(-β λᵢ) > 0`, so the sum over a non-empty index
    set is strictly positive. -/
theorem partitionFunction_pos_of_nonempty {n : ℕ} [hne : Nonempty (Fin n)]
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    0 < partitionFunction β H := by
  rw [partitionFunction_eq_sum_exp β H hH]
  -- Each summand is strictly positive; non-empty sum is positive.
  obtain ⟨i₀⟩ := hne
  have h_pos : ∀ i, 0 < Real.exp (-β * hH.eigenvalues i) := fun i =>
    Real.exp_pos _
  calc (0 : ℝ)
      < Real.exp (-β * hH.eigenvalues i₀) := h_pos i₀
    _ ≤ ∑ i, Real.exp (-β * hH.eigenvalues i) :=
        Finset.single_le_sum (f := fun i => Real.exp (-β * hH.eigenvalues i))
          (fun j _ => (h_pos j).le) (Finset.mem_univ i₀)

/-! ## 3. The Helmholtz free energy `F := -(1/β) log Z` -/

/-- **Helmholtz free energy**, `F(H) := -(1/β) · log Z(H)`. -/
noncomputable def freeEnergy {n : ℕ} (β : ℝ)
    (H : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  -(1 / β) * Real.log (partitionFunction β H)

/-- **Free-energy bridge**: `exp(-β · (F₁ − F₀)) = Z₁ / Z₀`.

    Algebraic identity (for `β ≠ 0` and `Z₀, Z₁ > 0`). -/
theorem exp_neg_beta_delta_F_eq_Z_ratio {n : ℕ}
    (β : ℝ) (hβ : β ≠ 0)
    (H_0 H_1 : Matrix (Fin n) (Fin n) ℂ)
    (Z_0_pos : 0 < partitionFunction β H_0)
    (Z_1_pos : 0 < partitionFunction β H_1) :
    Real.exp (-β * (freeEnergy β H_1 - freeEnergy β H_0))
      = partitionFunction β H_1 / partitionFunction β H_0 := by
  unfold freeEnergy
  -- ΔF = -(1/β) (log Z₁ − log Z₀), so -β ΔF = log Z₁ − log Z₀
  have h_simplify :
      -β * (-(1 / β) * Real.log (partitionFunction β H_1)
            - (-(1 / β) * Real.log (partitionFunction β H_0)))
        = Real.log (partitionFunction β H_1)
            - Real.log (partitionFunction β H_0) := by
    field_simp
    ring
  rw [h_simplify]
  rw [Real.exp_sub, Real.exp_log Z_1_pos, Real.exp_log Z_0_pos]

/-! ## 4. The mixed-basis transition matrix `W := star U₁ · U_τ · U₀` -/

namespace JarzynskiProtocol

variable {n : ℕ} (P : JarzynskiProtocol n)

/-- **Mixed-basis transition matrix** `W := star U₁ · U_τ · U₀`.

    `W_{mn}` is the amplitude `⟨m|U_τ|n⟩` where `|m⟩` is the m-th
    eigenvector of `H_1` and `|n⟩` is the n-th eigenvector of `H_0`. -/
noncomputable def transition : Matrix (Fin n) (Fin n) ℂ :=
  star P.U_1 * P.U_τ * P.U_0

/-- `transition` is unitary: product of three unitaries. -/
theorem transition_unitary : P.transition ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  unfold transition
  -- (star U_1) ∈ unitaryGroup, U_τ ∈ unitaryGroup, U_0 ∈ unitaryGroup
  have h_star_U1 : star P.U_1 ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    Unitary.star_mem P.U_1_unitary
  exact mul_mem (mul_mem h_star_U1 P.U_τ_unitary) P.U_0_unitary

/-- `W · star W = 1` (right inverse). -/
theorem transition_mul_star : P.transition * star P.transition = 1 := by
  have h := P.transition_unitary
  rw [Matrix.mem_unitaryGroup_iff] at h
  exact h

/-- `star W · W = 1` (left inverse). -/
theorem star_mul_transition : star P.transition * P.transition = 1 := by
  have h := P.transition_unitary
  rw [Matrix.mem_unitaryGroup_iff'] at h
  exact h

/-- **Row-sum unitarity identity**: `∑_n ‖W_{mn}‖² = 1` for each `m`.

    From `W · star W = 1`, taking the `(m,m)` entry:
      `1 = ∑_n W_{mn} · (star W)_{nm} = ∑_n W_{mn} · star (W_{mn}) = ∑_n ‖W_{mn}‖²`. -/
theorem row_sum_sq_transition (m : Fin n) :
    ∑ k, ‖P.transition m k‖^2 = 1 := by
  have hWW : P.transition * star P.transition = 1 := P.transition_mul_star
  -- (W * star W) m m = 1
  have h_entry : (P.transition * star P.transition) m m
               = (1 : Matrix (Fin n) (Fin n) ℂ) m m := by
    rw [hWW]
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h_entry
  -- ∑ k, W_{mk} · (star W)_{km} = 1
  -- (star W)_{km} = star (W_{mk})
  -- So W_{mk} · star (W_{mk}) = (‖W_{mk}‖² : ℂ)
  have h_per_k : ∀ k, P.transition m k * (star P.transition) k m
               = ((‖P.transition m k‖^2 : ℝ) : ℂ) := by
    intro k
    change P.transition m k * star (P.transition m k) = _
    -- Use Complex.mul_conj and ‖z‖² identity.
    rw [show (star (P.transition m k) : ℂ) = (starRingEnd ℂ) (P.transition m k) from rfl]
    rw [Complex.mul_conj]
    rw [Complex.normSq_eq_norm_sq]
  rw [Finset.sum_congr rfl (fun k _ => h_per_k k)] at h_entry
  -- Now ((∑ ‖W_{mk}‖² : ℝ) : ℂ) = (1 : ℂ), so ∑ = 1.
  have h_cast : ((∑ k, ‖P.transition m k‖^2 : ℝ) : ℂ) = (1 : ℂ) := by
    rw [← h_entry]
    push_cast
    rfl
  exact_mod_cast h_cast

end JarzynskiProtocol

/-! ## 5. The Jarzynski work-distribution average -/

/-- **Jarzynski average**, the spectral double-sum

      `⟨exp(-β W)⟩ := (1/Z₀) ∑_{m,n} exp(-β E_n^0) · ‖W_{mn}‖²
                                       · exp(-β (E_m^1 − E_n^0))`,

    where `E_n^0, E_m^1` are eigenvalues of `H_0, H_1` and `W_{mn}` is
    the mixed-basis transition amplitude.  Sum over `(m, n)` of the
    joint probability `p_n · |⟨m|U_τ|n⟩|²` times `exp(-β W)`. -/
noncomputable def jarzynskiAverage {n : ℕ} (P : JarzynskiProtocol n) : ℝ :=
  (1 / partitionFunction P.β P.H_0)
    * ∑ m, ∑ k, Real.exp (-P.β * P.E_0 k)
                 * ‖P.transition m k‖^2
                 * Real.exp (-P.β * (P.E_1 m - P.E_0 k))

/-! ## 6. The headline result: Quantum Jarzynski equality -/

/-- **Algebraic cancellation step**: the joint summand simplifies.

    `exp(-β E_n^0) · ‖W_{mn}‖² · exp(-β (E_m^1 − E_n^0))
       = ‖W_{mn}‖² · exp(-β E_m^1)`.

    This is the heart of Jarzynski: the initial Boltzmann factor
    cancels against the `exp(+β E_n^0)` hidden in `exp(-β (E_m^1 - E_n^0))`. -/
private lemma jarzynski_summand_cancellation {n : ℕ}
    (P : JarzynskiProtocol n) (m k : Fin n) :
    Real.exp (-P.β * P.E_0 k)
        * ‖P.transition m k‖^2
        * Real.exp (-P.β * (P.E_1 m - P.E_0 k))
      = ‖P.transition m k‖^2 * Real.exp (-P.β * P.E_1 m) := by
  -- exp(-β E_n^0) · exp(-β (E_m^1 - E_n^0)) = exp(-β E_n^0 - β (E_m^1 - E_n^0))
  --                                         = exp(-β E_m^1)
  have h_exp :
      Real.exp (-P.β * P.E_0 k) * Real.exp (-P.β * (P.E_1 m - P.E_0 k))
        = Real.exp (-P.β * P.E_1 m) := by
    rw [← Real.exp_add]
    congr 1
    ring
  -- Rearrange and apply.
  calc Real.exp (-P.β * P.E_0 k)
          * ‖P.transition m k‖^2
          * Real.exp (-P.β * (P.E_1 m - P.E_0 k))
      = (Real.exp (-P.β * P.E_0 k) * Real.exp (-P.β * (P.E_1 m - P.E_0 k)))
          * ‖P.transition m k‖^2 := by ring
    _ = Real.exp (-P.β * P.E_1 m) * ‖P.transition m k‖^2 := by rw [h_exp]
    _ = ‖P.transition m k‖^2 * Real.exp (-P.β * P.E_1 m) := by ring

/-- **Quantum Jarzynski (partition-function form).**

    `⟨exp(-β W)⟩ = Z₁ / Z₀`.

    Proof: per-summand cancellation reduces the double sum to
    `∑_m exp(-β E_m^1) · ∑_n ‖W_{mn}‖² = ∑_m exp(-β E_m^1) · 1 = Z₁`.
    Then divide by `Z₀`. -/
theorem quantum_jarzynski_partition {n : ℕ} (P : JarzynskiProtocol n) :
    jarzynskiAverage P
      = partitionFunction P.β P.H_1 / partitionFunction P.β P.H_0 := by
  unfold jarzynskiAverage
  -- Step 1: per-summand cancellation.
  have h_inner : ∀ m k,
      Real.exp (-P.β * P.E_0 k)
          * ‖P.transition m k‖^2
          * Real.exp (-P.β * (P.E_1 m - P.E_0 k))
        = ‖P.transition m k‖^2 * Real.exp (-P.β * P.E_1 m) :=
    jarzynski_summand_cancellation P
  -- Rewrite the summand.
  have h_inner_sum : ∀ m,
      ∑ k, Real.exp (-P.β * P.E_0 k)
              * ‖P.transition m k‖^2
              * Real.exp (-P.β * (P.E_1 m - P.E_0 k))
        = ∑ k, ‖P.transition m k‖^2 * Real.exp (-P.β * P.E_1 m) := by
    intro m
    apply Finset.sum_congr rfl
    intro k _
    exact h_inner m k
  rw [Finset.sum_congr rfl (fun m _ => h_inner_sum m)]
  -- Step 2: factor exp(-β E_m^1) out of inner sum.
  have h_factor : ∀ m,
      ∑ k, ‖P.transition m k‖^2 * Real.exp (-P.β * P.E_1 m)
        = (∑ k, ‖P.transition m k‖^2) * Real.exp (-P.β * P.E_1 m) := by
    intro m
    rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun m _ => h_factor m)]
  -- Step 3: row sum of ‖W_{mk}‖² = 1.
  have h_row : ∀ m, (∑ k, ‖P.transition m k‖^2) = 1 := P.row_sum_sq_transition
  rw [Finset.sum_congr rfl (fun m _ => by rw [h_row m, one_mul])]
  -- Now ∑ m, exp(-β E_m^1) = Z(H_1).
  have h_Z1 : ∑ m, Real.exp (-P.β * P.E_1 m)
            = partitionFunction P.β P.H_1 := by
    rw [partitionFunction_eq_sum_exp P.β P.H_1 P.H_1_isHerm]
    rfl
  rw [h_Z1]
  -- (1/Z_0) · Z_1 = Z_1 / Z_0.
  ring

/-- **QUANTUM JARZYNSKI EQUALITY** (Tasaki 2000; Talkner–Lutz–Hänggi 2007).

      `⟨exp(-β W)⟩  =  exp(-β · ΔF) ,    ΔF := F(H₁) − F(H₀) .`

    The expectation of `exp(-β W)` over the two-time-measurement work
    distribution equals the exponential of the equilibrium free-energy
    difference.  This is the most celebrated **fluctuation theorem** in
    quantum statistical mechanics: it relates a non-equilibrium average
    to an equilibrium identity, and it implies the second law
    `⟨W⟩ ≥ ΔF` via Jensen's inequality.

    Proof: combine `quantum_jarzynski_partition` (which gives the
    partition-function ratio form) with `exp_neg_beta_delta_F_eq_Z_ratio`
    (the algebraic free-energy bridge). -/
theorem quantum_jarzynski {n : ℕ} [Nonempty (Fin n)] (P : JarzynskiProtocol n) :
    jarzynskiAverage P
      = Real.exp (-P.β * (freeEnergy P.β P.H_1 - freeEnergy P.β P.H_0)) := by
  rw [quantum_jarzynski_partition P]
  have hβ : P.β ≠ 0 := ne_of_gt P.β_pos
  have hZ0 : 0 < partitionFunction P.β P.H_0 :=
    partitionFunction_pos_of_nonempty P.β P.H_0 P.H_0_isHerm
  have hZ1 : 0 < partitionFunction P.β P.H_1 :=
    partitionFunction_pos_of_nonempty P.β P.H_1 P.H_1_isHerm
  exact (exp_neg_beta_delta_F_eq_Z_ratio P.β hβ P.H_0 P.H_1 hZ0 hZ1).symm

/-! ## 7. Corollaries -/

/-- **Trivial case `H_0 = H_1`**: no driving, so `⟨exp(-βW)⟩ = 1`. -/
theorem jarzynski_trivial {n : ℕ} [Nonempty (Fin n)]
    (P : JarzynskiProtocol n)
    (h_eq : P.H_0 = P.H_1) :
    jarzynskiAverage P = 1 := by
  rw [quantum_jarzynski_partition P]
  -- Z_1 = Z_0 because H_1 = H_0.
  rw [h_eq]
  have hZ : partitionFunction P.β P.H_1 ≠ 0 :=
    ne_of_gt (partitionFunction_pos_of_nonempty P.β P.H_1 P.H_1_isHerm)
  field_simp

/-- **Free-energy invariance under `H_0 = H_1`.**  When the Hamiltonian
    is unchanged, `ΔF = 0`. -/
theorem freeEnergy_eq_of_Hamiltonian_eq {n : ℕ}
    (β : ℝ) (H_0 H_1 : Matrix (Fin n) (Fin n) ℂ)
    (h_eq : H_0 = H_1) :
    freeEnergy β H_1 - freeEnergy β H_0 = 0 := by
  rw [h_eq]; ring

/-! ## 8. Axiom audit (manual: run `#print axioms` after build). -/

-- Uncomment to audit:
-- #print axioms quantum_jarzynski
-- #print axioms quantum_jarzynski_partition
-- #print axioms partitionFunction_eq_sum_exp
-- #print axioms partitionFunction_pos_of_nonempty
-- #print axioms exp_neg_beta_delta_F_eq_Z_ratio
-- #print axioms JarzynskiProtocol.row_sum_sq_transition
-- #print axioms JarzynskiProtocol.transition_unitary
-- VERIFIED 2026-06-01: every theorem above ⟹
--   [propext, Classical.choice, Quot.sound]  (only).
-- No `sorry`, no custom `axiom`.

end UnifiedTheory.LayerB.QuantumJarzynski
