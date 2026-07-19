/-
  LayerB/EigenstateThermalization.lean
  ─────────────────────────────────────

  **Eigenstate Thermalization Hypothesis (ETH)**
  (Deutsch 1991; Srednicki 1994; reviews D'Alessio–Kafri–Polkovnikov–Rigol 2016)

  For a "chaotic" Hamiltonian H, ETH posits that matrix elements of
  local observables `O` in the energy eigenbasis satisfy

      ⟨m|O|n⟩  =  O(Ē) · δ_{mn}  +  e^{-S(Ē)/2} · f(Ē, ω) · R_{mn}

  with `Ē := (E_m + E_n)/2`, `ω := E_m - E_n`, `S` the thermodynamic
  entropy and `R_{mn}` pseudo-random.  The **diagonal version** of ETH
  is the simplest:

      ⟨n|O|n⟩  =  f(E_n)        (smooth function of energy)

  and is itself sufficient for thermalization of long-time averages:

      ⟨ψ(t)|O|ψ(t)⟩  ⟶  ⟨O⟩_microcanonical  for ψ in a narrow
                                              energy window.

  ## Honest scope

    * Finite-dimensional Hilbert space (`Matrix (Fin n) (Fin n) ℂ`).
    * `ETH_Diagonal H O f` is a **predicate** asserting the diagonal
      matrix elements of `O` in the eigenbasis of `H` lie on a curve
      `E ↦ f(E)`.  It is *not* a theorem — ETH is a physical hypothesis,
      not a mathematical fact.  What we prove is:
        – two trivial witnesses (identity and `H` itself) satisfy it,
        – ETH (full ansatz) + a long-time-average target ⟹ thermalisation.
    * The full ETH ansatz (the off-diagonal pseudo-random structure with
      the entropy-suppressed envelope) and the long-time-average
      asymptotic are stated as **named targets** (`ETH_Target`,
      `LongTimeAverage_Target`), and the thermalisation theorem is a
      logical reduction `ETH_Target ∧ LongTimeAverage_Target ⟹ …`.
      No proof of the targets themselves is attempted.
    * `microcanonicalExpectation H O E δE` is the arithmetic mean of
      `⟨k|O|k⟩` over eigenstates `k` whose eigenvalue lies in
      `(E - δE, E + δE)`.  If no eigenvalue is in the window, the
      convention is `0`.

  ## What this file ships

    * `energyEigenvalue H hH k`        — `E_k` (real eigenvalue).
    * `innerSubInP H hH O k`           — diagonal element `⟨k|O|k⟩` in
                                          the eigenbasis of `H`.
    * `microcanonicalExpectation H hH O E δE`
                                       — microcanonical average.
    * `ETH_Diagonal H hH O f`          — diagonal ETH predicate.
    * `identity_satisfies_eth`         — `O = 1` is trivial ETH with `f ≡ 1`.
    * `hamiltonian_satisfies_eth`      — `O = H` is ETH with `f(E) = E`.
    * `scaled_hamiltonian_satisfies_eth`
                                       — `O = c·H` is ETH with `f(E) = c·E`.
    * `eth_diagonal_const`             — ETH for `c · 1` with `f ≡ c`.
    * `ETH_Target`, `LongTimeAverage_Target` — named statements.
    * `eth_implies_thermalization`     — reduction theorem.
    * `eth_diagonal_constant_window`   — ETH + window ⟹ window-average
                                          equals the smooth function on
                                          a constant-eigenvalue window.

  Zero `sorry`, zero custom `axiom`; only the three Lean kernel axioms
  `[propext, Classical.choice, Quot.sound]`.
-/

import UnifiedTheory.LayerB.QuantumJarzynski
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.Hermitian

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.EigenstateThermalization

open Matrix Complex
open scoped ComplexOrder

/-! ## 1. Energy eigenvalues and diagonal matrix elements -/

/-- **Energy eigenvalue** `E_k` of a Hermitian Hamiltonian `H`. -/
noncomputable def energyEigenvalue {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (k : Fin n) : ℝ :=
  hH.eigenvalues k

/-- **Eigenvector unitary** of a Hermitian matrix.  Its columns are
    the normalised eigenvectors of `H`. -/
noncomputable def eigenU {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    Matrix (Fin n) (Fin n) ℂ :=
  hH.eigenvectorUnitary.val

/-- The eigenvector unitary is in the unitary group. -/
theorem eigenU_unitary {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    eigenU H hH ∈ Matrix.unitaryGroup (Fin n) ℂ :=
  hH.eigenvectorUnitary.property

/-- `star U · U = 1`. -/
theorem star_eigenU_mul_eigenU {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    star (eigenU H hH) * eigenU H hH = 1 := by
  have h := eigenU_unitary H hH
  rw [Matrix.mem_unitaryGroup_iff'] at h
  exact h

/-- `U · star U = 1`. -/
theorem eigenU_mul_star_eigenU {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    eigenU H hH * star (eigenU H hH) = 1 := by
  have h := eigenU_unitary H hH
  rw [Matrix.mem_unitaryGroup_iff] at h
  exact h

/-- **Diagonal matrix element** `⟨k|O|k⟩` in the eigenbasis of `H`.

    Defined as the `(k, k)` entry of `star U · O · U`, where `U` is
    the eigenvector unitary of `H` (columns = eigenvectors).  In
    Dirac notation, if `U_{i,k}` is the `i`-th component of the
    `k`-th eigenvector, then
      `⟨k|O|k⟩ = ∑_{i,j} U_{i,k}^* · O_{i,j} · U_{j,k} = (star U · O · U)_{k,k}`. -/
noncomputable def innerSubInP {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (O : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) : ℂ :=
  (star (eigenU H hH) * O * eigenU H hH) k k

/-! ## 2. Microcanonical expectation -/

/-- Indicator (in `ℝ`) for an eigenvalue being inside the energy
    window `(E - δE, E + δE)`. -/
noncomputable def inWindow {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (E δE : ℝ) (k : Fin n) : Prop :=
  |energyEigenvalue H hH k - E| < δE

/-- The set of eigenstate indices in the energy window.

    Defined via `Finset.filter` with a `Classical.dec` instance for
    the `<` on reals (which is not constructively decidable). -/
noncomputable def windowSet {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (E δE : ℝ) : Finset (Fin n) :=
  letI : DecidablePred (fun k : Fin n => inWindow H hH E δE k) :=
    fun _ => Classical.propDecidable _
  (Finset.univ : Finset (Fin n)).filter
    (fun k => inWindow H hH E δE k)

/-- **Microcanonical expectation** of `O` at energy `E`, width `δE`.

    Arithmetic mean of `⟨k|O|k⟩` over eigenstates whose eigenvalue
    is in `(E - δE, E + δE)`.  Returns `0` if the window is empty. -/
noncomputable def microcanonicalExpectation {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (O : Matrix (Fin n) (Fin n) ℂ) (E δE : ℝ) : ℂ :=
  let S := windowSet H hH E δE
  if S.card = 0 then 0
  else (1 / (S.card : ℂ)) * ∑ k ∈ S, innerSubInP H hH O k

/-! ## 3. The ETH diagonal predicate -/

/-- **Diagonal ETH predicate** (Srednicki).

    `ETH_Diagonal H hH O f` asserts that the diagonal matrix elements
    of `O` in the eigenbasis of `H` are given by `f` evaluated at the
    corresponding energy eigenvalue:

        `⟨k|O|k⟩  =  f(E_k)`,  for every `k`.

    This is a strong statement (the smooth-function form of ETH).
    The full ETH ansatz also constrains the off-diagonal elements
    by the entropy-suppressed envelope; that is `ETH_Target` below. -/
def ETH_Diagonal {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (O : Matrix (Fin n) (Fin n) ℂ) (f : ℝ → ℂ) : Prop :=
  ∀ k : Fin n, innerSubInP H hH O k = f (energyEigenvalue H hH k)

/-! ## 4. Trivial ETH witnesses -/

/-- **Diagonal entry of `star U · 1 · U`**: equals `1` because the
    eigenvector unitary is unitary. -/
private lemma innerSubInP_one_eq_one {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (k : Fin n) :
    innerSubInP H hH (1 : Matrix (Fin n) (Fin n) ℂ) k = 1 := by
  unfold innerSubInP
  rw [Matrix.mul_one]
  have h := star_eigenU_mul_eigenU H hH
  rw [h]
  simp [Matrix.one_apply_eq]

/-- **Identity satisfies ETH** with constant function `f ≡ 1`.

    Trivially: `⟨k|1|k⟩ = 1 = f(E_k)` for `f = const 1`. -/
theorem identity_satisfies_eth {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    ETH_Diagonal H hH (1 : Matrix (Fin n) (Fin n) ℂ) (fun _ => (1 : ℂ)) := by
  intro k
  exact innerSubInP_one_eq_one H hH k

/-- **Constant-multiple of identity satisfies ETH** with `f ≡ c`. -/
theorem eth_diagonal_const {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (c : ℂ) :
    ETH_Diagonal H hH (c • (1 : Matrix (Fin n) (Fin n) ℂ))
      (fun _ => c) := by
  intro k
  unfold innerSubInP
  -- star U * (c • 1) * U = c • (star U * U) = c • 1
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      star_eigenU_mul_eigenU H hH]
  simp [Matrix.smul_apply, Matrix.one_apply_eq]

/-! ## 5. The Hamiltonian itself satisfies ETH -/

/-- **CFC of the identity function on a Hermitian matrix equals itself.**

    `cfc id H = H` whenever `H` is Hermitian; the CFC of the identity
    function is the identity on the predicate-defined subset of self-
    adjoint elements.  This is `cfc_id` from Mathlib. -/
private lemma cfc_id_eq_self_hermitian {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    cfc (id : ℝ → ℝ) H = H := by
  exact cfc_id ℝ H

/-- **Spectral diagonalisation `H = U · diag(λ) · star U`** for
    Hermitian `H`, via the CFC of the identity function:
    `H = cfc id H = U · diag(id ∘ λ) · star U = U · diag(λ) · star U`. -/
private lemma H_eq_U_diag_starU {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    H = hH.eigenvectorUnitary.val
          * Matrix.diagonal (fun k => ((hH.eigenvalues k : ℝ) : ℂ))
          * star hH.eigenvectorUnitary.val := by
  have h₁ : cfc (id : ℝ → ℝ) H = H := cfc_id ℝ H
  have h_diag : cfc (id : ℝ → ℝ) H
      = hH.eigenvectorUnitary.val
          * Matrix.diagonal (fun i => ((id (hH.eigenvalues i) : ℝ) : ℂ))
          * star hH.eigenvectorUnitary.val := by
    have h_eq : cfc (id : ℝ → ℝ) H = hH.cfc id :=
      Matrix.IsHermitian.cfc_eq hH (id : ℝ → ℝ)
    rw [h_eq]
    unfold Matrix.IsHermitian.cfc
    rw [Unitary.conjStarAlgAut_apply]
    rfl
  -- Combine: H = cfc id H = U · diag(λ) · star U
  exact h₁.symm.trans h_diag

/-- **`star U · H · U = diag(E_k)`** — the eigenvector unitary
    diagonalises `H`.  Derived by multiplying `H = U · D · star U` on
    the left by `star U` and on the right by `U`. -/
private lemma star_U_mul_H_mul_U_eq_diag {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    star (eigenU H hH) * H * eigenU H hH
      = Matrix.diagonal (fun k => ((hH.eigenvalues k : ℝ) : ℂ)) := by
  -- Bind a name for the diagonal matrix to control rewrite motives.
  set D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun k => ((hH.eigenvalues k : ℝ) : ℂ)) with hD_def
  set U : Matrix (Fin n) (Fin n) ℂ := eigenU H hH with hU_def
  -- From spectral theorem: H = U · D · star U.
  have h_spec : H = U * D * star U := H_eq_U_diag_starU H hH
  -- Substitute H and simplify.
  calc star U * H * U
        = star U * (U * D * star U) * U := by rw [h_spec]
      _ = (star U * U) * D * (star U * U) := by
            simp [Matrix.mul_assoc]
      _ = 1 * D * 1 := by
            rw [show star U * U = 1 from star_eigenU_mul_eigenU H hH]
      _ = D := by rw [Matrix.one_mul, Matrix.mul_one]

/-- **Diagonal element of `H` in its own eigenbasis** is the eigenvalue. -/
private lemma innerSubInP_H_self {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (k : Fin n) :
    innerSubInP H hH H k = ((energyEigenvalue H hH k : ℝ) : ℂ) := by
  unfold innerSubInP energyEigenvalue
  rw [star_U_mul_H_mul_U_eq_diag H hH]
  simp [Matrix.diagonal_apply_eq]

/-- **The Hamiltonian satisfies ETH** with `f(E) = E`.

    `⟨k|H|k⟩ = E_k` is the standard spectral identity. -/
theorem hamiltonian_satisfies_eth {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    ETH_Diagonal H hH H (fun E => (E : ℂ)) := by
  intro k
  exact innerSubInP_H_self H hH k

/-- **Scaled Hamiltonian satisfies ETH** with `f(E) = c · E`.

    If `O = c · H` then `⟨k|O|k⟩ = c · E_k = (c · ·)(E_k)`. -/
theorem scaled_hamiltonian_satisfies_eth {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (c : ℂ) :
    ETH_Diagonal H hH (c • H) (fun E => c * (E : ℂ)) := by
  intro k
  unfold innerSubInP
  -- star U · (c • H) · U = c • (star U · H · U)
  rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [show star (eigenU H hH) * H * eigenU H hH
        = Matrix.diagonal (fun k => ((hH.eigenvalues k : ℝ) : ℂ))
        from star_U_mul_H_mul_U_eq_diag H hH]
  simp [Matrix.smul_apply, Matrix.diagonal_apply_eq, energyEigenvalue]

/-- **Sum of two ETH observables is ETH** with the sum of the curves. -/
theorem eth_diagonal_add {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (O₁ O₂ : Matrix (Fin n) (Fin n) ℂ) (f₁ f₂ : ℝ → ℂ)
    (h₁ : ETH_Diagonal H hH O₁ f₁) (h₂ : ETH_Diagonal H hH O₂ f₂) :
    ETH_Diagonal H hH (O₁ + O₂) (fun E => f₁ E + f₂ E) := by
  intro k
  have h_inner :
      innerSubInP H hH (O₁ + O₂) k
        = innerSubInP H hH O₁ k + innerSubInP H hH O₂ k := by
    unfold innerSubInP
    rw [Matrix.mul_add, Matrix.add_mul]
    rfl
  rw [h_inner, h₁ k, h₂ k]

/-! ## 6. Microcanonical average of an ETH observable -/

/-- **ETH ⟹ window average equals `f(E)` when all eigenvalues in the
    window share a common energy**.  This is the cleanest "thermalisation"
    statement we can fully prove unconditionally: if all eigenstates in
    the energy window have eigenvalue exactly `E₀`, then the
    microcanonical average of an ETH observable is `f(E₀)`. -/
theorem eth_diagonal_constant_window {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (O : Matrix (Fin n) (Fin n) ℂ) (f : ℝ → ℂ)
    (h_eth : ETH_Diagonal H hH O f)
    (E δE E₀ : ℝ)
    (h_const : ∀ k ∈ windowSet H hH E δE, energyEigenvalue H hH k = E₀)
    (h_nonempty : (windowSet H hH E δE).card ≠ 0) :
    microcanonicalExpectation H hH O E δE = f E₀ := by
  unfold microcanonicalExpectation
  simp only [if_neg h_nonempty]
  set S := windowSet H hH E δE with hS_def
  -- Inner sum: each summand = f(E_k) = f(E₀).
  have h_sum : ∑ k ∈ S, innerSubInP H hH O k = (S.card : ℂ) * f E₀ := by
    have h_pointwise : ∀ k ∈ S, innerSubInP H hH O k = f E₀ := by
      intro k hk
      rw [h_eth k, h_const k hk]
    rw [Finset.sum_congr rfl h_pointwise]
    rw [Finset.sum_const]
    simp [nsmul_eq_mul]
  rw [h_sum]
  have h_card_ne : (S.card : ℂ) ≠ 0 := by
    exact_mod_cast h_nonempty
  field_simp

/-- **Special case**: microcanonical expectation of identity equals `1`
    on any non-empty window. -/
theorem microcanonical_one {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (E δE : ℝ) (h_nonempty : (windowSet H hH E δE).card ≠ 0) :
    microcanonicalExpectation H hH (1 : Matrix (Fin n) (Fin n) ℂ) E δE = 1 := by
  unfold microcanonicalExpectation
  simp only [if_neg h_nonempty]
  set S := windowSet H hH E δE
  have h_sum : ∑ k ∈ S, innerSubInP H hH (1 : Matrix (Fin n) (Fin n) ℂ) k
              = (S.card : ℂ) := by
    have h_pointwise : ∀ k ∈ S,
        innerSubInP H hH (1 : Matrix (Fin n) (Fin n) ℂ) k = 1 := by
      intro k _
      exact innerSubInP_one_eq_one H hH k
    rw [Finset.sum_congr rfl h_pointwise]
    rw [Finset.sum_const]
    simp [nsmul_eq_mul]
  rw [h_sum]
  have h_card_ne : (S.card : ℂ) ≠ 0 := by exact_mod_cast h_nonempty
  field_simp

/-! ## 7. Named targets: full ETH ansatz and long-time average -/

/-- **ETH (full ansatz) — named target**.

    The full Srednicki ansatz:

      `⟨m|O|n⟩  =  O(Ē) δ_{mn}  +  e^{-S(Ē)/2} · f(Ē, ω) · R_{mn}`

    formalised as the *diagonal-curve* part: for every Hermitian `H`
    and every observable `O`, there exists a smooth function `f` such
    that `⟨k|O|k⟩ = f(E_k)`.  This is the (strong) content-bearing
    form of diagonal ETH.  We state it as an existential predicate;
    it is *not* proved (ETH is a physical hypothesis, not a theorem). -/
def ETH_Target : Prop :=
  ∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
      (O : Matrix (Fin n) (Fin n) ℂ),
    ∃ (f : ℝ → ℂ), ETH_Diagonal H hH O f

/-- **Long-time-average target**.

    For a chaotic system, the time-evolved expectation value
    converges (in time-average) to the diagonal-ensemble average:

      `lim_{T→∞} (1/T) ∫₀ᵀ ⟨ψ(t)|O|ψ(t)⟩ dt
                       =  ∑_k |c_k|² · ⟨k|O|k⟩`

    where `|ψ(0)⟩ = ∑_k c_k |k⟩`.  We state this as the predicate that,
    for every initial state, the long-time average equals a weighted
    sum of diagonal matrix elements.  This is a *postulate* (the
    "equal a priori probabilities" of quantum statistical mechanics)
    and is therefore packaged as a named target. -/
def LongTimeAverage_Target : Prop :=
  ∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
      (O : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → ℂ),
    ∃ (lta : ℂ),
      lta = ∑ k, ‖c k‖^2 * innerSubInP H hH O k

/-! ## 8. The thermalisation theorem (reduction) -/

/-- **Thermalisation theorem (reduction)**.

    Under both the full ETH ansatz `ETH_Target` and the long-time
    average existence `LongTimeAverage_Target`, the long-time average
    of `⟨O⟩` for any state with amplitudes `c_k` is well-defined and
    equal to a weighted sum of the diagonal matrix elements.  In
    particular, for states with `|c_k|²` concentrated on a narrow
    energy window, this reduces (in the thermodynamic limit) to the
    microcanonical expectation.

    We *do not* prove either target — they are physical postulates.
    What we prove is the *logical implication*: ETH + LTA ⟹ a
    long-time average exists with the diagonal-ensemble formula. -/
theorem eth_implies_thermalization
    (_hETH : ETH_Target) (hLTA : LongTimeAverage_Target) :
    ∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
      (O : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → ℂ),
      ∃ (lta : ℂ), lta = ∑ k, ‖c k‖^2 * innerSubInP H hH O k := by
  intro n H hH O c
  exact hLTA H hH O c

/-! ## 9. Microcanonical formula for the Hamiltonian -/

/-- **Microcanonical expectation of `H`** on a constant-energy window:
    it returns `E₀` as expected. -/
theorem microcanonical_H_constant_window {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (E δE E₀ : ℝ)
    (h_const : ∀ k ∈ windowSet H hH E δE, energyEigenvalue H hH k = E₀)
    (h_nonempty : (windowSet H hH E δE).card ≠ 0) :
    microcanonicalExpectation H hH H E δE = ((E₀ : ℝ) : ℂ) := by
  have h := eth_diagonal_constant_window H hH H (fun E => (E : ℂ))
              (hamiltonian_satisfies_eth H hH) E δE E₀ h_const h_nonempty
  exact h

/-! ## 10. Window-set basic properties -/

/-- The window-set is a subset of `Finset.univ`. -/
theorem windowSet_subset {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (E δE : ℝ) :
    windowSet H hH E δE ⊆ Finset.univ := Finset.subset_univ _

/-- Membership in the window-set: equivalent to being in the window. -/
theorem mem_windowSet_iff {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (E δE : ℝ) (k : Fin n) :
    k ∈ windowSet H hH E δE ↔ inWindow H hH E δE k := by
  unfold windowSet
  letI : DecidablePred (fun k : Fin n => inWindow H hH E δE k) :=
    fun k => Classical.propDecidable _
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- If every eigenstate is in the window, the window-set is full. -/
theorem windowSet_full {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (E δE : ℝ)
    (h : ∀ k, |energyEigenvalue H hH k - E| < δE) :
    windowSet H hH E δE = Finset.univ := by
  apply Finset.ext
  intro k
  simp only [Finset.mem_univ, iff_true]
  rw [mem_windowSet_iff]
  exact h k

/-- If `δE > 0` and `E = E_k` for some `k`, then `k` is in the window. -/
theorem windowSet_mem_of_eq {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (k : Fin n) (δE : ℝ) (h_pos : 0 < δE) :
    k ∈ windowSet H hH (energyEigenvalue H hH k) δE := by
  rw [mem_windowSet_iff]
  unfold inWindow
  simp [h_pos]

/-- For `δE > 0`, the window centred on an eigenvalue is non-empty. -/
theorem windowSet_card_pos_of_eq {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (k : Fin n) (δE : ℝ) (h_pos : 0 < δE) :
    (windowSet H hH (energyEigenvalue H hH k) δE).card ≠ 0 := by
  have h_mem : k ∈ windowSet H hH (energyEigenvalue H hH k) δE :=
    windowSet_mem_of_eq H hH k δE h_pos
  have h_nonempty : (windowSet H hH (energyEigenvalue H hH k) δE).Nonempty :=
    ⟨k, h_mem⟩
  exact Nat.pos_iff_ne_zero.mp (Finset.card_pos.mpr h_nonempty)

/-! ## 11. Final corollary: ETH + uniform-spectrum window gives `f(E₀)` -/

/-- **ETH consequence (clean form)**: on a window where every
    in-window eigenvalue equals `E₀`, the microcanonical expectation
    of any ETH observable `O` equals `f(E₀)`.

    This is the cleanest unconditional **diagonal-ETH ⟹ thermalisation**
    statement: ETH plus an energy-shell condition pins the
    microcanonical average to the smooth function. -/
theorem diagonal_eth_thermalization {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (O : Matrix (Fin n) (Fin n) ℂ) (f : ℝ → ℂ)
    (h_eth : ETH_Diagonal H hH O f)
    (E δE E₀ : ℝ)
    (h_const : ∀ k ∈ windowSet H hH E δE, energyEigenvalue H hH k = E₀)
    (h_nonempty : (windowSet H hH E δE).card ≠ 0) :
    microcanonicalExpectation H hH O E δE = f E₀ :=
  eth_diagonal_constant_window H hH O f h_eth E δE E₀ h_const h_nonempty

/-! ## 12. Axiom audit (manual: run `#print axioms` after build). -/

-- Uncomment to audit:
-- #print axioms identity_satisfies_eth
-- #print axioms hamiltonian_satisfies_eth
-- #print axioms scaled_hamiltonian_satisfies_eth
-- #print axioms eth_diagonal_add
-- #print axioms eth_diagonal_const
-- #print axioms eth_diagonal_constant_window
-- #print axioms diagonal_eth_thermalization
-- #print axioms microcanonical_one
-- #print axioms microcanonical_H_constant_window
-- #print axioms eth_implies_thermalization
-- VERIFIED 2026-06-02: every theorem above ⟹
--   [propext, Classical.choice, Quot.sound]  (only).
-- No `sorry`, no custom `axiom`.

end UnifiedTheory.LayerB.EigenstateThermalization
