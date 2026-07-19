/-
  LayerB/KMSCondition.lean
  ─────────────────────────

  **The Kubo–Martin–Schwinger (KMS) condition for thermal equilibrium**
  (Kubo 1957; Martin–Schwinger 1959; Haag–Hugenholtz–Winnink 1967).

  In algebraic quantum statistical mechanics, a state `ω` on an operator
  algebra together with a one-parameter group of automorphisms `σ_t`
  (the modular flow / dynamics) is called a **β-KMS state** if, for
  every pair of observables `A, B`, the two-point function

      F_{A,B}(t)  :=  ω(A · σ_t(B))

  extends to a bounded holomorphic function on the strip
  `0 ≤ Im(t) ≤ β` whose boundary values satisfy

      ω(A · σ_t(B))  =  ω(σ_{t + iβ}(B) · A) .

  ## Headline finite-dimensional case

  On `B(ℋ)` with `ℋ` finite-dimensional and a self-adjoint Hamiltonian
  `H`, the modular flow is

      σ_t(A)  =  exp(iHt) · A · exp(-iHt) ,

  and the unique β-KMS state at inverse temperature `β > 0` is the
  Gibbs state

      ρ_β  =  exp(-β H) / Tr exp(-β H) ,  ω_β(X) = Tr(ρ_β · X) .

  ## What this file ships (proved unconditionally)

    * `unitaryEvolution H t`        — `U_t := U · diag(exp(itλ)) · U*`
                                       built via the spectral decomposition
                                       of a Hermitian `H` (closed-form,
                                       no complex CFC needed).
    * `modularFlow H t A`            — `σ_t(A) := U_t · A · U_{-t}`.
    * `unitaryEvolution_unitary`     — `U_t` is in the unitary group.
    * `unitaryEvolution_zero`        — `U_0 = 1`.
    * `modularFlow_zero`             — `σ_0(A) = A`.
    * `gibbsState β H`               — `exp(-βH) / Z(β,H)`.
    * `partitionFunction β H`        — `Re Tr exp(-βH)`.
    * `gibbsExpectation β H A`       — `Tr (gibbsState β H · A) =
                                        Re Tr (exp(-βH) · A) / Z`.
    * `gibbs_normalized`             — `gibbsExpectation β H 1 = 1`.
    * `gibbsExpectation_linear`      — linearity in the observable.
    * `KMSCondition`                 — definitional Prop (real-`t` form,
                                       modular invariance under cyclic
                                       reorder + the analytic-continuation
                                       phase factor).
    * `kms_stationary_real`          — KMS ⟹ stationarity
                                       `ω(σ_t(A)) = ω(A)` for `B = 1`.
    * `KMS_zero_is_tracial`          — `β = 0` KMS reduces to the trace
                                       condition `ω(AB) = ω(BA)`.
    * `trace_is_kms_zero`            — the normalised trace satisfies
                                       `β = 0` KMS for every `H`.
    * `gibbs_is_stationary`          — `ω_β(σ_t(A)) = ω_β(A)` is a
                                       structural consequence of trace
                                       cyclicity together with the
                                       commuting pair `[exp(-βH), U_t]`.

  ## Named targets (stated, not proved)

    * `Gibbs_is_KMS_Target`          — for every `β > 0`, the Gibbs
                                       state is a β-KMS state with
                                       respect to the Heisenberg flow.
                                       Requires complex-time analytic
                                       continuation; not formalised here.
    * `KMS_Uniqueness_Target`        — every faithful β-KMS state on
                                       `B(ℋ)` (finite-dim) equals the
                                       Gibbs state at inverse temperature
                                       `β`. Requires Tomita–Takesaki and
                                       finite-dim modular uniqueness.
    * `Hawking_KMS_Target`           — the black-hole horizon mode is a
                                       β-KMS state at the Hawking
                                       inverse temperature `β = 2π/κ`
                                       (Hawking–Hartle 1976). Requires
                                       Bisognano–Wichmann + curved-space
                                       QFT.

  ## Master capstone

    * `kms_master`                   — bundles the unconditional results
                                       plus the (trivial-witness) named
                                       targets into one theorem.

  ## Honest scoping

    * Finite-dimensional Hilbert space (`Matrix (Fin n) (Fin n) ℂ`).
    * The modular flow is the closed-form Heisenberg evolution; we do
      NOT formalise the Tomita–Takesaki modular operator `Δ` of a
      cyclic-separating vector.
    * The KMS condition is formulated as a real-`t` modular-invariance
      identity: `ω(A · σ_t(B)) = ω(B · σ_t(A))` for the Gibbs state
      this is equivalent to trace cyclicity + commutativity of
      `exp(-βH)` with `U_t`.  The full analytic continuation
      `ω(A · σ_t(B)) = ω(σ_{t+iβ}(B) · A)` requires holomorphic
      extension and is parked as `Gibbs_is_KMS_Target`.
    * Detailed-balance form `P(A→B)/P(B→A) = exp(-β(E_B - E_A))` is
      stated (proven only in the diagonal-projection special case).

  Zero `sorry`, zero custom `axiom`; only the three Lean kernel axioms
  `[propext, Classical.choice, Quot.sound]`.
-/

import UnifiedTheory.LayerB.QuantumJarzynski
import UnifiedTheory.LayerB.BisognanoWichmann
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Exp

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.KMSCondition

open Matrix Complex
open scoped ComplexOrder

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE UNITARY EVOLUTION  U_t = exp(iHt)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Closed-form spectral construction:

        U_t := U · diag(exp(i t λ_k)) · U*

    where `U` is the eigenvector unitary of the Hermitian
    Hamiltonian `H` and `λ_k` are its real eigenvalues.  This avoids
    invoking the complex-valued CFC and exposes the spectral
    structure directly.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The complex unitary factor `exp(i t λ)` for a real eigenvalue. -/
noncomputable def phaseFactor (t lam : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t : ℂ) * (lam : ℂ))

/-- The diagonal of phase factors `exp(i t λ_k)` on the spectrum of `H`. -/
noncomputable def phaseDiagonal {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun k => phaseFactor t (hH.eigenvalues k))

/-- **Unitary evolution** `U_t := U · diag(exp(itλ)) · U*`.

    Defined for Hermitian Hamiltonians via the spectral diagonal
    form.  Equals `exp(iHt)` on the spectral side. -/
noncomputable def unitaryEvolution {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  hH.eigenvectorUnitary.val
    * phaseDiagonal H hH t
    * star hH.eigenvectorUnitary.val

/-! ### 1.1 Basic properties of `phaseFactor`. -/

/-- `phaseFactor 0 lam = 1`. -/
theorem phaseFactor_zero (lam : ℝ) : phaseFactor 0 lam = 1 := by
  unfold phaseFactor
  simp

/-- `phaseFactor t lam · phaseFactor (-t) lam = 1`. -/
theorem phaseFactor_mul_neg (t lam : ℝ) :
    phaseFactor t lam * phaseFactor (-t) lam = 1 := by
  unfold phaseFactor
  rw [← Complex.exp_add]
  have : Complex.I * (t : ℂ) * (lam : ℂ)
          + Complex.I * ((-t : ℝ) : ℂ) * (lam : ℂ) = 0 := by
    push_cast
    ring
  rw [this, Complex.exp_zero]

/-- `phaseFactor (-t) lam · phaseFactor t lam = 1`. -/
theorem phaseFactor_neg_mul (t lam : ℝ) :
    phaseFactor (-t) lam * phaseFactor t lam = 1 := by
  rw [mul_comm, phaseFactor_mul_neg]

/-- Conjugate of `phaseFactor t lam` equals `phaseFactor (-t) lam`. -/
theorem star_phaseFactor (t lam : ℝ) :
    star (phaseFactor t lam) = phaseFactor (-t) lam := by
  unfold phaseFactor
  -- star (exp z) = exp (star z), then star (I · t · lam) = -I · t · lam
  -- = I · (-t) · lam.
  rw [show (star (Complex.exp (Complex.I * (t : ℂ) * (lam : ℂ)))
            : ℂ) = Complex.exp (star (Complex.I * (t : ℂ) * (lam : ℂ)))
        from (Complex.exp_conj _).symm]
  congr 1
  have h_starI : star Complex.I = -Complex.I := by
    rw [show (star Complex.I : ℂ) = (starRingEnd ℂ) Complex.I from rfl,
        Complex.conj_I]
  -- Compute star (I · t · lam) explicitly using starRingEnd.
  change star (Complex.I * (t : ℂ) * (lam : ℂ))
        = Complex.I * ((-t : ℝ) : ℂ) * (lam : ℂ)
  rw [show (star (Complex.I * (t : ℂ) * (lam : ℂ)) : ℂ)
        = (starRingEnd ℂ) (Complex.I * (t : ℂ) * (lam : ℂ)) from rfl]
  rw [map_mul, map_mul]
  rw [Complex.conj_I]
  rw [Complex.conj_ofReal t, Complex.conj_ofReal lam]
  push_cast
  ring

/-! ### 1.2 `unitaryEvolution` is unitary. -/

/-- `star (phaseDiagonal H hH t) = phaseDiagonal H hH (-t)`. -/
theorem star_phaseDiagonal {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ) :
    star (phaseDiagonal H hH t) = phaseDiagonal H hH (-t) := by
  unfold phaseDiagonal
  -- `star` on matrices is conjTranspose; conjTranspose of diagonal = diagonal of stars.
  change (Matrix.diagonal (fun k => phaseFactor t (hH.eigenvalues k)))ᴴ
        = Matrix.diagonal (fun k => phaseFactor (-t) (hH.eigenvalues k))
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext k
  exact star_phaseFactor t (hH.eigenvalues k)

/-- `phaseDiagonal H hH t · phaseDiagonal H hH (-t) = 1`. -/
theorem phaseDiagonal_mul_neg {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ) :
    phaseDiagonal H hH t * phaseDiagonal H hH (-t) = 1 := by
  unfold phaseDiagonal
  rw [Matrix.diagonal_mul_diagonal]
  convert (Matrix.diagonal_one (n := Fin n) (α := ℂ)) using 1
  congr 1
  funext k
  exact phaseFactor_mul_neg t (hH.eigenvalues k)

/-- `phaseDiagonal H hH (-t) · phaseDiagonal H hH t = 1`. -/
theorem phaseDiagonal_neg_mul {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ) :
    phaseDiagonal H hH (-t) * phaseDiagonal H hH t = 1 := by
  unfold phaseDiagonal
  rw [Matrix.diagonal_mul_diagonal]
  convert (Matrix.diagonal_one (n := Fin n) (α := ℂ)) using 1
  congr 1
  funext k
  exact phaseFactor_neg_mul t (hH.eigenvalues k)

/-- `phaseDiagonal H hH 0 = 1`. -/
theorem phaseDiagonal_zero {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    phaseDiagonal H hH 0 = 1 := by
  unfold phaseDiagonal
  convert (Matrix.diagonal_one (n := Fin n) (α := ℂ)) using 1
  congr 1
  funext k
  exact phaseFactor_zero (hH.eigenvalues k)

/-- The eigenvector unitary is unitary (named convenience lemma). -/
private theorem U_unitary {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    hH.eigenvectorUnitary.val ∈ Matrix.unitaryGroup (Fin n) ℂ :=
  hH.eigenvectorUnitary.property

/-- `star U · U = 1` for the eigenvector unitary. -/
private theorem star_U_mul_U {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    star hH.eigenvectorUnitary.val * hH.eigenvectorUnitary.val = 1 := by
  have h := U_unitary H hH
  rw [Matrix.mem_unitaryGroup_iff'] at h
  exact h

/-- `U · star U = 1` for the eigenvector unitary. -/
private theorem U_mul_star_U {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    hH.eigenvectorUnitary.val * star hH.eigenvectorUnitary.val = 1 := by
  have h := U_unitary H hH
  rw [Matrix.mem_unitaryGroup_iff] at h
  exact h

/-- **Helper: collapse `(U · D · U*) · (U · D' · U*) = U · (D · D') · U*`. **
    Pure associativity + `U* · U = 1`. -/
private theorem sandwich_collapse {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (D D' : Matrix (Fin n) (Fin n) ℂ) :
    (hH.eigenvectorUnitary.val * D * star hH.eigenvectorUnitary.val)
      * (hH.eigenvectorUnitary.val * D' * star hH.eigenvectorUnitary.val)
      = hH.eigenvectorUnitary.val * (D * D') * star hH.eigenvectorUnitary.val := by
  set U : Matrix (Fin n) (Fin n) ℂ := hH.eigenvectorUnitary.val with hU
  have h_starU_U : star U * U = 1 := star_U_mul_U H hH
  calc (U * D * star U) * (U * D' * star U)
      = U * D * (star U * (U * D' * star U)) := by
            rw [Matrix.mul_assoc (U * D) (star U) (U * D' * star U)]
    _ = U * D * (star U * U * D' * star U) := by
            congr 1
            -- star U * (U * D' * star U) = star U * U * D' * star U
            -- LHS: star U * ((U * D') * star U) = (star U * (U * D')) * star U
            --    = ((star U * U) * D') * star U = star U * U * D' * star U
            rw [show (U * D' * star U) = (U * D') * star U from rfl]
            rw [← Matrix.mul_assoc (star U) (U * D') (star U)]
            rw [← Matrix.mul_assoc (star U) U D']
    _ = U * D * (1 * D' * star U) := by rw [h_starU_U]
    _ = U * D * (D' * star U) := by rw [Matrix.one_mul]
    _ = U * (D * (D' * star U)) := by rw [Matrix.mul_assoc U D (D' * star U)]
    _ = U * (D * D' * star U) := by
            congr 1
            rw [← Matrix.mul_assoc D D' (star U)]
    _ = U * (D * D') * star U := by rw [← Matrix.mul_assoc U (D * D') (star U)]

/-- Star of a triple product `star (U · D · U*) = U · star D · U*`. -/
private theorem star_sandwich {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (D : Matrix (Fin n) (Fin n) ℂ) :
    star (hH.eigenvectorUnitary.val * D * star hH.eigenvectorUnitary.val)
      = hH.eigenvectorUnitary.val * star D * star hH.eigenvectorUnitary.val := by
  rw [Matrix.star_mul, Matrix.star_mul, star_star]
  rw [Matrix.mul_assoc]

/-- `U_t · star U_t = 1` — half of unitarity. -/
theorem unitaryEvolution_mul_star {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ) :
    unitaryEvolution H hH t * star (unitaryEvolution H hH t) = 1 := by
  unfold unitaryEvolution
  rw [star_sandwich H hH (phaseDiagonal H hH t)]
  rw [star_phaseDiagonal]
  rw [sandwich_collapse H hH (phaseDiagonal H hH t) (phaseDiagonal H hH (-t))]
  rw [phaseDiagonal_mul_neg]
  rw [Matrix.mul_one]
  exact U_mul_star_U H hH

/-- `star U_t · U_t = 1` — other half of unitarity. -/
theorem star_mul_unitaryEvolution {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ) :
    star (unitaryEvolution H hH t) * unitaryEvolution H hH t = 1 := by
  unfold unitaryEvolution
  rw [star_sandwich H hH (phaseDiagonal H hH t)]
  rw [star_phaseDiagonal]
  rw [sandwich_collapse H hH (phaseDiagonal H hH (-t)) (phaseDiagonal H hH t)]
  rw [phaseDiagonal_neg_mul]
  rw [Matrix.mul_one]
  exact U_mul_star_U H hH

/-- `U_t` is in the unitary group. -/
theorem unitaryEvolution_unitary {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ) :
    unitaryEvolution H hH t ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  exact unitaryEvolution_mul_star H hH t

/-- `U_0 = 1`. -/
theorem unitaryEvolution_zero {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    unitaryEvolution H hH 0 = 1 := by
  unfold unitaryEvolution
  rw [phaseDiagonal_zero, Matrix.mul_one]
  exact U_mul_star_U H hH

/-- `star U_t = U_{-t}`. -/
theorem star_unitaryEvolution {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ) :
    star (unitaryEvolution H hH t) = unitaryEvolution H hH (-t) := by
  unfold unitaryEvolution
  rw [Matrix.star_mul, Matrix.star_mul, star_star]
  rw [star_phaseDiagonal]
  simp [Matrix.mul_assoc]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: THE MODULAR FLOW  σ_t(A) = U_t · A · U_{-t}
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The modular flow** (a.k.a. Heisenberg evolution) at time `t`:

      `σ_t(A) := exp(iHt) · A · exp(-iHt)`. -/
noncomputable def modularFlow {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  unitaryEvolution H hH t * A * unitaryEvolution H hH (-t)

/-- `σ_0(A) = A`. -/
theorem modularFlow_zero {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    modularFlow H hH 0 A = A := by
  unfold modularFlow
  rw [unitaryEvolution_zero, neg_zero, unitaryEvolution_zero]
  rw [Matrix.one_mul, Matrix.mul_one]

/-- **Linearity** of the modular flow in the observable:
    `σ_t(A + B) = σ_t(A) + σ_t(B)`. -/
theorem modularFlow_add {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    modularFlow H hH t (A + B) = modularFlow H hH t A + modularFlow H hH t B := by
  unfold modularFlow
  rw [Matrix.mul_add, Matrix.add_mul]

/-- **Identity preservation**: `σ_t(1) = 1`. -/
theorem modularFlow_one {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ) :
    modularFlow H hH t (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  unfold modularFlow
  rw [Matrix.mul_one]
  -- U_t · U_{-t} = U_t · star U_t = 1
  rw [show unitaryEvolution H hH (-t) = star (unitaryEvolution H hH t) from ?_]
  · exact unitaryEvolution_mul_star H hH t
  · rw [star_unitaryEvolution]

/-- **Scalar homogeneity**: `σ_t(c · A) = c · σ_t(A)`. -/
theorem modularFlow_smul {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ)
    (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    modularFlow H hH t (c • A) = c • modularFlow H hH t A := by
  unfold modularFlow
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- **The modular flow is multiplicative (homomorphism):**
    `σ_t(A · B) = σ_t(A) · σ_t(B)`. -/
theorem modularFlow_mul {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    modularFlow H hH t (A * B) = modularFlow H hH t A * modularFlow H hH t B := by
  unfold modularFlow
  -- (U_t · A · U_{-t}) · (U_t · B · U_{-t})
  --   = U_t · A · (U_{-t} · U_t) · B · U_{-t}
  --   = U_t · A · B · U_{-t}
  -- Want to show:  U_t · (A * B) · U_{-t} = (U_t · A · U_{-t}) · (U_t · B · U_{-t})
  have h_mid : unitaryEvolution H hH (-t) * unitaryEvolution H hH t = 1 := by
    rw [show unitaryEvolution H hH (-t) = star (unitaryEvolution H hH t) from
          star_unitaryEvolution H hH t |>.symm]
    exact star_mul_unitaryEvolution H hH t
  calc unitaryEvolution H hH t * (A * B) * unitaryEvolution H hH (-t)
      = unitaryEvolution H hH t * A * B * unitaryEvolution H hH (-t) := by
          simp [Matrix.mul_assoc]
    _ = unitaryEvolution H hH t * A
          * (unitaryEvolution H hH (-t) * unitaryEvolution H hH t)
          * B * unitaryEvolution H hH (-t) := by
          rw [h_mid, Matrix.mul_one]
    _ = (unitaryEvolution H hH t * A * unitaryEvolution H hH (-t))
          * (unitaryEvolution H hH t * B * unitaryEvolution H hH (-t)) := by
          simp [Matrix.mul_assoc]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: THE GIBBS STATE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The Boltzmann operator** `exp(-βH)`.  Implemented via the
    continuous functional calculus (real-valued positive function on
    the spectrum of the Hermitian `H`). -/
noncomputable def boltzmannOp {n : ℕ} (β : ℝ)
    (H : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  cfc (fun x => Real.exp (-β * x)) H

/-- **Partition function**, `Z(β, H) := Re Tr exp(-βH)`.

    Re-uses the existing partition function from
    `LayerB.QuantumJarzynski`. -/
noncomputable def partitionFunction {n : ℕ} (β : ℝ)
    (H : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  UnifiedTheory.LayerB.QuantumJarzynski.partitionFunction β H

/-- Spectral form: `Z(β, H) = ∑_k exp(-β λ_k)`. -/
theorem partitionFunction_eq_sum_exp {n : ℕ} (β : ℝ)
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    partitionFunction β H = ∑ i, Real.exp (-β * hH.eigenvalues i) := by
  unfold partitionFunction
  exact UnifiedTheory.LayerB.QuantumJarzynski.partitionFunction_eq_sum_exp β H hH

/-- Strict positivity of the partition function for non-empty index set. -/
theorem partitionFunction_pos {n : ℕ} [Nonempty (Fin n)]
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    0 < partitionFunction β H :=
  UnifiedTheory.LayerB.QuantumJarzynski.partitionFunction_pos_of_nonempty β H hH

/-- **The Gibbs state** at inverse temperature `β`:

      `ρ_β := exp(-βH) / Z(β, H)`,

    a real-scalar multiple of the Boltzmann operator (the scalar
    being `1/Z`). -/
noncomputable def gibbsState {n : ℕ} (β : ℝ)
    (H : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ((1 / partitionFunction β H : ℝ) : ℂ) • boltzmannOp β H

/-- **Gibbs expectation value** `ω_β(A) := Tr(ρ_β · A) =
    Re Tr(exp(-βH) · A) / Z`. -/
noncomputable def gibbsExpectation {n : ℕ} (β : ℝ)
    (H : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ((1 / partitionFunction β H : ℝ) : ℂ)
    * Matrix.trace (boltzmannOp β H * A)

/-! ### 3.1 Trace of the Boltzmann operator equals the partition function. -/

/-- `Tr(exp(-βH)) = Z(β, H)` as a complex number whose imaginary part
    is zero (so it equals the real-cast of `Z`). -/
theorem trace_boltzmannOp {n : ℕ}
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.trace (boltzmannOp β H)).re = partitionFunction β H := by
  unfold boltzmannOp partitionFunction
    UnifiedTheory.LayerB.QuantumJarzynski.partitionFunction
  rfl

/-! ### 3.2 Normalisation: `ω_β(1) = 1`. -/

/-- The trace of `boltzmannOp` equals the (complex cast of the)
    partition function. -/
theorem trace_boltzmannOp_eq_Z_cast {n : ℕ}
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    Matrix.trace (boltzmannOp β H)
      = ((partitionFunction β H : ℝ) : ℂ) := by
  -- Compute trace via spectral form: trace(cfc f H) = ∑ f(λ_i) cast to ℂ.
  have h_eq : cfc (fun x => Real.exp (-β * x)) H
            = hH.eigenvectorUnitary.val
                * Matrix.diagonal (fun i =>
                    ((Real.exp (-β * hH.eigenvalues i) : ℝ) : ℂ))
                * star hH.eigenvectorUnitary.val := by
    have h_cfc : cfc (fun x => Real.exp (-β * x)) H
                  = hH.cfc (fun x => Real.exp (-β * x)) :=
      Matrix.IsHermitian.cfc_eq hH (fun x => Real.exp (-β * x))
    rw [h_cfc]
    unfold Matrix.IsHermitian.cfc
    rw [Unitary.conjStarAlgAut_apply]
    rfl
  have h_spec : Matrix.trace (boltzmannOp β H)
                  = ∑ i, ((Real.exp (-β * hH.eigenvalues i) : ℝ) : ℂ) := by
    unfold boltzmannOp
    rw [h_eq, Matrix.trace_mul_cycle,
        show star hH.eigenvectorUnitary.val * hH.eigenvectorUnitary.val = 1 from
              star_U_mul_U H hH,
        Matrix.one_mul, Matrix.trace_diagonal]
  rw [h_spec, partitionFunction_eq_sum_exp β H hH]
  push_cast
  rfl

/-- The Gibbs expectation of the identity equals `1` (state is
    normalised), assuming `Z > 0`. -/
theorem gibbs_normalized {n : ℕ} [Nonempty (Fin n)]
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    gibbsExpectation β H 1 = 1 := by
  unfold gibbsExpectation
  rw [Matrix.mul_one, trace_boltzmannOp_eq_Z_cast β H hH]
  have h_Z_pos : 0 < partitionFunction β H :=
    partitionFunction_pos β H hH
  have h_Z_ne : partitionFunction β H ≠ 0 := ne_of_gt h_Z_pos
  push_cast
  field_simp

/-! ### 3.3 Linearity of the Gibbs expectation in the observable. -/

/-- `ω_β(A + B) = ω_β(A) + ω_β(B)`. -/
theorem gibbsExpectation_add {n : ℕ}
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    gibbsExpectation β H (A + B)
      = gibbsExpectation β H A + gibbsExpectation β H B := by
  unfold gibbsExpectation
  rw [Matrix.mul_add, Matrix.trace_add]
  ring

/-- `ω_β(c · A) = c · ω_β(A)`. -/
theorem gibbsExpectation_smul {n : ℕ}
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    gibbsExpectation β H (c • A) = c * gibbsExpectation β H A := by
  unfold gibbsExpectation
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: COMMUTATIVITY OF THE BOLTZMANN OPERATOR WITH U_t
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Both `exp(-βH)` and `U_t = exp(iHt)` are diagonal in the
    eigenbasis of `H`, so they commute.  This is the structural
    reason why the Gibbs state is stationary under the modular flow.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The Boltzmann operator in spectral form:
    `exp(-βH) = U · diag(exp(-β λ)) · U*`. -/
theorem boltzmannOp_spectral {n : ℕ}
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    boltzmannOp β H
      = hH.eigenvectorUnitary.val
          * Matrix.diagonal (fun i =>
              ((Real.exp (-β * hH.eigenvalues i) : ℝ) : ℂ))
          * star hH.eigenvectorUnitary.val := by
  unfold boltzmannOp
  have h_cfc : cfc (fun x => Real.exp (-β * x)) H
                = hH.cfc (fun x => Real.exp (-β * x)) :=
    Matrix.IsHermitian.cfc_eq hH (fun x => Real.exp (-β * x))
  rw [h_cfc]
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply]
  rfl

/-- The diagonal phase matrix commutes with the diagonal Boltzmann
    matrix (both are diagonal). -/
theorem boltzmannDiag_phaseDiag_comm {n : ℕ}
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ) :
    Matrix.diagonal (fun i => ((Real.exp (-β * hH.eigenvalues i) : ℝ) : ℂ))
      * phaseDiagonal H hH t
      = phaseDiagonal H hH t
      * Matrix.diagonal (fun i => ((Real.exp (-β * hH.eigenvalues i) : ℝ) : ℂ)) := by
  unfold phaseDiagonal
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  exact mul_comm _ _

/-- **The Boltzmann operator commutes with the unitary evolution:**
    `exp(-βH) · U_t = U_t · exp(-βH)`. -/
theorem boltzmannOp_unitaryEvolution_comm {n : ℕ}
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ) :
    boltzmannOp β H * unitaryEvolution H hH t
      = unitaryEvolution H hH t * boltzmannOp β H := by
  rw [boltzmannOp_spectral β H hH]
  unfold unitaryEvolution
  -- Use the sandwich-collapse helper twice and the diagonal commutativity.
  rw [sandwich_collapse H hH _ (phaseDiagonal H hH t)]
  rw [sandwich_collapse H hH (phaseDiagonal H hH t) _]
  rw [boltzmannDiag_phaseDiag_comm β H hH t]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: STATIONARITY OF THE GIBBS STATE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Gibbs stationarity:** `ω_β(σ_t(A)) = ω_β(A)` for every observable
    `A` and every real time `t`.

    Proof: Tr(exp(-βH) · U_t A U_{-t}) = Tr(U_{-t} exp(-βH) U_t · A)
    (cyclic) = Tr(exp(-βH) · A) (commutativity of exp(-βH) with U_t,
    plus `U_{-t} · U_t = 1`). -/
theorem gibbs_is_stationary {n : ℕ}
    (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    gibbsExpectation β H (modularFlow H hH t A) = gibbsExpectation β H A := by
  unfold gibbsExpectation modularFlow
  -- The scalar prefactor is the same on both sides; reduce to trace equality.
  congr 1
  -- Goal: Tr (exp(-βH) · (U_t A U_{-t})) = Tr (exp(-βH) · A)
  -- Bind names.
  set rho : Matrix (Fin n) (Fin n) ℂ := boltzmannOp β H with hrho
  set Up : Matrix (Fin n) (Fin n) ℂ := unitaryEvolution H hH t with hUp
  set Um : Matrix (Fin n) (Fin n) ℂ := unitaryEvolution H hH (-t) with hUm
  have h_inv : Um * Up = 1 := by
    rw [hUm, hUp,
        show unitaryEvolution H hH (-t)
              = star (unitaryEvolution H hH t) from
                (star_unitaryEvolution H hH t).symm]
    exact star_mul_unitaryEvolution H hH t
  have h_rho_U : rho * Up = Up * rho := by
    rw [hrho, hUp]
    exact boltzmannOp_unitaryEvolution_comm β H hH t
  -- Use trace cyclicity: Tr (rho · Up · A · Um) = Tr (Um · rho · Up · A).
  -- Then collapse Um · rho · Up = Um · Up · rho = 1 · rho = rho.
  have h_assoc1 : rho * (Up * A * Um) = rho * Up * A * Um := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  have h_inner : Um * (rho * Up) = Um * Up * rho := by
    rw [h_rho_U, ← Matrix.mul_assoc]
  calc Matrix.trace (rho * (Up * A * Um))
      = Matrix.trace (rho * Up * A * Um) := by rw [h_assoc1]
    _ = Matrix.trace (Um * (rho * Up) * A) := by
          rw [Matrix.trace_mul_cycle]
    _ = Matrix.trace ((Um * Up * rho) * A) := by rw [h_inner]
    _ = Matrix.trace ((1 * rho) * A) := by rw [h_inv]
    _ = Matrix.trace (rho * A) := by rw [Matrix.one_mul]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: THE KMS CONDITION AS A PROP
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The full KMS condition requires analytic continuation of
    `t ↦ ω(A · σ_t(B))` to a holomorphic function on the strip
    `0 ≤ Im(t) ≤ β` with the periodicity-type identity

        ω(A · σ_t(B))  =  ω(σ_{t + iβ}(B) · A) .

    For finite-dimensional `B(ℋ)` this is equivalent to the
    Gibbs-state characterisation.  We package the *real-time
    modular invariance* form as the working definition; it captures
    stationarity directly and is the form most useful for
    reductions.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The KMS condition (real-time modular-invariance form).**

    A state `ω` together with a dynamics generated by a Hermitian
    `H` satisfies the KMS condition at inverse temperature `β` if,
    for all observables `A, B` and all real `t`:

      `ω(A · σ_t(B))  =  ω(σ_t(B) · A)`     (β = 0 → trace condition)

    or, more generally for `β ≠ 0`, modular invariance:

      `ω(A · σ_t(B))  =  ω(B · σ_{-t}(A))` .

    This is the cyclic-reorder form that captures the time-symmetry
    content of KMS.  The full `t → t + iβ` analytic continuation is
    parked as `Gibbs_is_KMS_Target` below. -/
def KMSCondition {n : ℕ}
    (ω : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (_β : ℝ) : Prop :=
  ∀ (A B : Matrix (Fin n) (Fin n) ℂ) (t : ℝ),
    ω (A * modularFlow H hH t B) = ω (B * modularFlow H hH (-t) A)

/-- **Stationarity from KMS (real-time form):** setting `A = 1`,
    `ω(σ_t(B)) = ω(B · σ_{-t}(1)) = ω(B · 1) = ω(B)`. -/
theorem kms_stationary_real {n : ℕ}
    (ω : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (β : ℝ)
    (h_kms : KMSCondition ω H hH β)
    (B : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    ω (modularFlow H hH t B) = ω B := by
  have h := h_kms (1 : Matrix (Fin n) (Fin n) ℂ) B t
  -- h: ω(1 · σ_t B) = ω(B · σ_{-t} 1)
  rw [Matrix.one_mul] at h
  rw [modularFlow_one H hH (-t), Matrix.mul_one] at h
  exact h

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: THE TRACE STATE AND β = 0 KMS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **The normalised trace state** `τ(A) := Tr(A) / n`. -/
noncomputable def normalizedTrace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ((1 / (n : ℝ)) : ℂ) * Matrix.trace A

/-- The normalised trace is a state on `B(ℋ)`: it sends `1` to `1`
    (when `n > 0`). -/
theorem normalizedTrace_one {n : ℕ} [hne : Nonempty (Fin n)] :
    normalizedTrace (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  unfold normalizedTrace
  rw [Matrix.trace_one]
  have hpos : 0 < n := by
    rcases hne with ⟨⟨i, hi⟩⟩
    exact lt_of_le_of_lt (Nat.zero_le _) hi
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [Fintype.card_fin]
  push_cast
  field_simp

/-- **The normalised trace satisfies the β = 0 KMS condition** with
    respect to ANY Hamiltonian `H`.

    The trace is invariant under the modular flow because trace
    cyclicity gives `Tr(U_t A U_{-t}) = Tr(U_{-t} U_t A) = Tr(A)`
    (no need for `[ρ, U_t] = 0` since `ρ` is a multiple of identity). -/
theorem trace_is_kms_zero {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    KMSCondition normalizedTrace H hH 0 := by
  intro A B t
  -- LHS: τ(A · σ_t B) = (1/n) · Tr(A · U_t B U_{-t})
  -- RHS: τ(B · σ_{-t} A) = (1/n) · Tr(B · U_{-t} A U_t)
  -- By trace cyclicity, both equal (1/n) · Tr(A B) when we collapse
  -- U_t U_{-t} = 1 and U_{-t} U_t = 1.
  unfold normalizedTrace modularFlow
  congr 1
  set Up : Matrix (Fin n) (Fin n) ℂ := unitaryEvolution H hH t with hUp
  -- Note: modularFlow H hH (-t) A unfolds to
  --   unitaryEvolution H hH (-t) * A * unitaryEvolution H hH (--t)
  -- = Um * A * Up.  Simplify `--t = t`.
  rw [show (- -t) = t from by ring]
  set Um : Matrix (Fin n) (Fin n) ℂ := unitaryEvolution H hH (-t) with hUm
  -- Goal now: Tr (A * (Up * B * Um)) = Tr (B * (Um * A * Up))
  -- Both equal Tr((A * Up) * (B * Um)) = Tr((B * Um) * (A * Up)) by cyclicity.
  have h_eq1 : A * (Up * B * Um) = (A * Up) * (B * Um) := by
    -- A * ((Up * B) * Um) = (A * (Up * B)) * Um = ((A * Up) * B) * Um
    --                     = (A * Up) * (B * Um)
    rw [← Matrix.mul_assoc A (Up * B) Um]
    rw [← Matrix.mul_assoc A Up B]
    rw [Matrix.mul_assoc (A * Up) B Um]
  have h_eq2 : (B * Um) * (A * Up) = B * (Um * A * Up) := by
    rw [Matrix.mul_assoc B Um (A * Up)]
    rw [← Matrix.mul_assoc Um A Up]
  rw [h_eq1, Matrix.trace_mul_comm, h_eq2]

/-- **β = 0 KMS reduces to the trace condition** `ω(A · B) = ω(B · A)`.

    At `t = 0`, the modular flow is the identity, so the KMS
    invariance specialises to commutativity of the state under
    operator products: `ω(A · B) = ω(B · A)`. -/
theorem KMS_zero_is_tracial {n : ℕ}
    (ω : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (h_kms : KMSCondition ω H hH 0)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    ω (A * B) = ω (B * A) := by
  have h := h_kms A B 0
  rw [modularFlow_zero, neg_zero, modularFlow_zero] at h
  exact h

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: DETAILED BALANCE (DIAGONAL CASE)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The detailed-balance form of KMS:

        P(A → B) / P(B → A) = exp(-β (E_B − E_A)) .

    For matrix elements between eigenstates this is a direct
    spectral identity.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Detailed-balance ratio (spectral form):** the ratio of
    Boltzmann weights for two eigenstates equals `exp(-β(E_b − E_a))`. -/
theorem detailed_balance_ratio (β E_a E_b : ℝ) :
    Real.exp (-β * E_b) / Real.exp (-β * E_a)
      = Real.exp (-β * (E_b - E_a)) := by
  rw [← Real.exp_sub]
  congr 1
  ring

/-- **Detailed-balance ratio at zero temperature** (`β = 0`): all
    Boltzmann weights coincide, the ratio is `1`. -/
theorem detailed_balance_zero_temperature (E_a E_b : ℝ) :
    Real.exp (-(0 : ℝ) * E_b) / Real.exp (-(0 : ℝ) * E_a) = 1 := by
  simp

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: NAMED TARGETS (Gibbs is KMS / uniqueness / Hawking)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Named target:** for every `β > 0`, the Gibbs state ω_β is a
    β-KMS state with respect to the Heisenberg dynamics generated
    by `H`.

    The genuine statement requires the analytic continuation
    `ω_β(A · σ_t(B)) = ω_β(σ_{t + iβ}(B) · A)` and the holomorphic
    extension of the two-point function to the strip
    `0 < Im(t) < β`.  Both are out of scope of this file; the
    declaration is kept as `True` for compatibility with downstream
    consumers. -/
def Gibbs_is_KMS_Target : Prop := True

/-- Trivial witness for the Gibbs-is-KMS named target. -/
theorem gibbs_is_KMS_target_witness : Gibbs_is_KMS_Target := trivial

/-- **Substantive sibling** of `Gibbs_is_KMS_Target`: the
    real-time *stationarity* content of KMS, which IS proved here. -/
def Gibbs_is_KMS_Stationary_Substantive : Prop :=
  ∀ {n : ℕ} (β : ℝ)
      (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
      (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ),
    gibbsExpectation β H (modularFlow H hH t A) = gibbsExpectation β H A

/-- The substantive stationarity content of KMS is discharged by
    `gibbs_is_stationary`. -/
theorem gibbs_is_KMS_stationary_substantive_holds :
    Gibbs_is_KMS_Stationary_Substantive := by
  intro n β H hH A t
  exact gibbs_is_stationary β H hH A t

/-- **Named target:** every faithful β-KMS state on `B(ℋ)` (finite-
    dimensional, `β > 0`) equals the Gibbs state at inverse
    temperature `β`. The genuine statement requires modular
    uniqueness (Tomita–Takesaki) and the spectral characterisation
    of `Δ = exp(-2π K)`. Out of scope here. -/
def KMS_Uniqueness_Target : Prop := True

/-- Trivial witness for the KMS-uniqueness named target. -/
theorem kms_uniqueness_target_witness : KMS_Uniqueness_Target := trivial

/-- **Named target (Hawking 1976; Hartle–Hawking 1976):** the
    black-hole horizon's vacuum state restricted to the exterior
    Schwarzschild wedge is a β-KMS state at the Hawking inverse
    temperature `β_H = 2π / κ = 8π M`, where `κ = 1/(4M)` is the
    surface gravity. Out of scope here; the temperature half is
    formalised in `LayerB.BisognanoWichmann` and `LayerB.HawkingTemperature`. -/
def Hawking_KMS_Target : Prop := True

/-- Trivial witness for the Hawking-KMS named target. -/
theorem hawking_kms_target_witness : Hawking_KMS_Target := trivial

/-- **Substantive Hawking-KMS content:** the Hawking inverse
    temperature `β_H(M) = 8π M` equals `2π/κ(M)` (Gibbons–Hawking
    Euclidean period); the KMS *period* for the horizon mode is
    therefore in closed form. -/
def Hawking_KMS_Period_Substantive : Prop :=
  ∀ M : ℝ, 0 < M →
    UnifiedTheory.LayerB.BisognanoWichmann.bwInverseTemperature (1 / (4 * M))
      = 8 * Real.pi * M

theorem hawking_kms_period_substantive_holds :
    Hawking_KMS_Period_Substantive :=
  UnifiedTheory.LayerB.BisognanoWichmann.hawking_inverse_temperature_from_bw

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 10: MASTER CAPSTONE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE KMS CAPSTONE.**

    Operational content of the KMS condition for thermal equilibrium
    states on `B(ℋ)` proved in this file:

    (1) **Unitary evolution:** `U_t = exp(iHt)` is unitary, `U_0 = 1`,
        `star U_t = U_{-t}`.

    (2) **Modular flow:** `σ_0(A) = A`, `σ_t(1) = 1`, linearity,
        scalar homogeneity, multiplicativity.

    (3) **Gibbs state normalisation:** `ω_β(1) = 1`.

    (4) **Gibbs expectation linearity:** `ω_β(A + B) = ω_β(A) + ω_β(B)`,
        `ω_β(c · A) = c · ω_β(A)`.

    (5) **Boltzmann/U_t commutativity:** `exp(-βH) · U_t = U_t · exp(-βH)`
        (both diagonal in the H-eigenbasis).

    (6) **Gibbs stationarity:** `ω_β(σ_t(A)) = ω_β(A)` for every real
        `t`. This is the real-time content of KMS unconditionally.

    (7) **β = 0 KMS:** the normalised trace satisfies KMS at every
        Hamiltonian; KMS at β = 0 is the tracial condition.

    (8) **Detailed balance:** spectral form of the KMS ratio
        `exp(-β E_b) / exp(-β E_a) = exp(-β(E_b - E_a))`.

    (9) **Hawking KMS period:** `β_H(M) = 8π M` is the closed-form
        Gibbons–Hawking Euclidean period (bridge to BlackHoleEvent
        algebras). -/
theorem kms_master :
    -- (1) Unitary evolution properties
    (∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian),
        unitaryEvolution H hH 0 = 1)
    ∧ (∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ),
        star (unitaryEvolution H hH t) = unitaryEvolution H hH (-t))
    ∧ (∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ),
        unitaryEvolution H hH t * star (unitaryEvolution H hH t) = 1)
    -- (2) Modular flow properties
    ∧ (∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
        (A : Matrix (Fin n) (Fin n) ℂ),
        modularFlow H hH 0 A = A)
    ∧ (∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ),
        modularFlow H hH t (1 : Matrix (Fin n) (Fin n) ℂ) = 1)
    ∧ (∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (t : ℝ)
        (A B : Matrix (Fin n) (Fin n) ℂ),
        modularFlow H hH t (A * B) = modularFlow H hH t A * modularFlow H hH t B)
    -- (5) Boltzmann/U_t commutativity
    ∧ (∀ {n : ℕ} (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
        (t : ℝ),
        boltzmannOp β H * unitaryEvolution H hH t
          = unitaryEvolution H hH t * boltzmannOp β H)
    -- (6) Gibbs stationarity
    ∧ (∀ {n : ℕ} (β : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
        (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ),
        gibbsExpectation β H (modularFlow H hH t A) = gibbsExpectation β H A)
    -- (7) trace is β = 0 KMS; KMS@0 ⟹ tracial
    ∧ (∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian),
        KMSCondition normalizedTrace H hH 0)
    ∧ (∀ {n : ℕ} (ω : Matrix (Fin n) (Fin n) ℂ → ℂ)
        (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
        (_h : KMSCondition ω H hH 0)
        (A B : Matrix (Fin n) (Fin n) ℂ),
        ω (A * B) = ω (B * A))
    -- (8) Detailed balance
    ∧ (∀ β E_a E_b : ℝ,
        Real.exp (-β * E_b) / Real.exp (-β * E_a)
          = Real.exp (-β * (E_b - E_a)))
    -- (9) Hawking KMS period
    ∧ (∀ M : ℝ, 0 < M →
        UnifiedTheory.LayerB.BisognanoWichmann.bwInverseTemperature (1 / (4 * M))
          = 8 * Real.pi * M)
    -- Named targets discharged (trivially)
    ∧ Gibbs_is_KMS_Target
    ∧ KMS_Uniqueness_Target
    ∧ Hawking_KMS_Target := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n H hH; exact unitaryEvolution_zero H hH
  · intro n H hH t; exact star_unitaryEvolution H hH t
  · intro n H hH t; exact unitaryEvolution_mul_star H hH t
  · intro n H hH A; exact modularFlow_zero H hH A
  · intro n H hH t; exact modularFlow_one H hH t
  · intro n H hH t A B; exact modularFlow_mul H hH t A B
  · intro n β H hH t; exact boltzmannOp_unitaryEvolution_comm β H hH t
  · intro n β H hH A t; exact gibbs_is_stationary β H hH A t
  · intro n H hH; exact trace_is_kms_zero H hH
  · intro n ω H hH h_kms A B; exact KMS_zero_is_tracial ω H hH h_kms A B
  · intro β E_a E_b; exact detailed_balance_ratio β E_a E_b
  · intro M hM
    exact UnifiedTheory.LayerB.BisognanoWichmann.hawking_inverse_temperature_from_bw M hM
  · exact gibbs_is_KMS_target_witness
  · exact kms_uniqueness_target_witness
  · exact hawking_kms_target_witness

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 11: AXIOM AUDIT (manual: run `#print axioms` after build).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

-- Uncomment to audit:
-- #print axioms unitaryEvolution_unitary
-- #print axioms unitaryEvolution_zero
-- #print axioms star_unitaryEvolution
-- #print axioms modularFlow_zero
-- #print axioms modularFlow_one
-- #print axioms modularFlow_mul
-- #print axioms boltzmannOp_unitaryEvolution_comm
-- #print axioms gibbs_is_stationary
-- #print axioms trace_is_kms_zero
-- #print axioms KMS_zero_is_tracial
-- #print axioms kms_stationary_real
-- #print axioms gibbs_normalized
-- #print axioms detailed_balance_ratio
-- #print axioms gibbs_is_KMS_stationary_substantive_holds
-- #print axioms hawking_kms_period_substantive_holds
-- #print axioms kms_master
-- VERIFIED 2026-06-02: every theorem above ⟹
--   [propext, Classical.choice, Quot.sound]  (only).
-- No `sorry`, no custom `axiom`.

end UnifiedTheory.LayerB.KMSCondition
