/-
  LayerB/ReehSchlieder.lean — Reeh–Schlieder cyclicity (finite-dim toy)

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT — REEH–SCHLIEDER THEOREM (Reeh & Schlieder 1961)

  In algebraic quantum field theory, an observable algebra `A(O)` is
  associated with each open spacetime region `O`. The vacuum state
  `|Ω⟩` lives in a Hilbert space `H` that carries a representation of
  the global net.

  **Reeh–Schlieder cyclicity**: for every open spacetime region `O`,
  the subspace `{A|Ω⟩ : A ∈ A(O)}` is *dense* in the full Hilbert
  space `H`.

  Operationally: every global state can be approximated arbitrarily
  well by acting on the vacuum with operators localised in any region
  `O`, no matter how small. This is the QFT manifestation of
  "entanglement everywhere".

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT THIS FILE SHIPS

  The full Reeh–Schlieder theorem requires Tomita–Takesaki modular
  theory, type III von Neumann algebras, and analyticity of the
  energy spectrum — all beyond scope here. What we formalise is the
  finite-dimensional STRUCTURAL backbone:

      For the FULL matrix algebra `End(ℂⁿ)` and ANY nonzero
      vector `ψ ∈ ℂⁿ`, the orbit `{A ψ : A ∈ End(ℂⁿ)}` is the whole
      of `ℂⁿ`.

  In finite dimensions "dense" collapses to "equal to" (closed sets
  in a finite-dim normed space are already closed), so the statement
  becomes a clean equality of sets and is provable by a one-shot
  rank-1 construction:

      Given a nonzero target `φ` and a witness coordinate `i₀` with
      `ψ i₀ ≠ 0`, take

          a := vecMulVec φ (Pi.single i₀ (1 / ψ i₀)).

      Then `a *ᵥ ψ = ((Pi.single i₀ (1 / ψ i₀)) ⬝ᵥ ψ) • φ
                   = ((1 / ψ i₀) * ψ i₀) • φ
                   = 1 • φ = φ`.

  This is the same outer-product construction that exhibits the
  vacuum as cyclic for the full algebra in the genuine QFT case;
  what changes there is that one must (a) restrict `A` to a *local*
  subalgebra, and (b) take a closure. Both are infinite-dimensional
  steps; the finite-dim algebra IS its own closure and the full
  algebra trivially contains the rank-1 outer product.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPING

  We DO formalise:
    • `IsCyclic` for a subalgebra of `Matrix (Fin n) (Fin n) ℂ`.
    • `full_algebra_cyclic_for_nonzero`: every nonzero `ψ` is cyclic
      for `Set.univ`.
    • `reeh_schlieder_toy`: the unwrapped surjectivity statement —
      for every nonzero `ψ` and every target `φ`, there is `a` with
      `a *ᵥ ψ = φ`.
    • `zero_not_cyclic`: the only way cyclicity fails for the full
      algebra is when `ψ = 0` (genuine non-triviality of the
      hypothesis `ψ ≠ 0`, for `n ≥ 1`).

  We do NOT formalise (parked as named target propositions):
    • Genuine Reeh–Schlieder over a Hilbert space.
    • The role of *local* subalgebras (regions of spacetime).
    • Modular operators / Tomita–Takesaki / Type III factors.
    • Analyticity of the energy spectrum.

  Zero `sorry`. Zero custom `axiom`.
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Logic.Function.Basic

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.ReehSchlieder

open Matrix

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: CYCLIC VECTORS FOR A MATRIX SUBALGEBRA
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A vector `ψ ∈ ℂⁿ` is **cyclic** for a set of matrices `A` when
    `{a *ᵥ ψ : a ∈ A}` is all of `ℂⁿ`, i.e. every vector `φ` is
    reached by some `a ∈ A`.

    In finite dimensions the topological notion ("dense") collapses
    to this set-theoretic surjectivity: the orbit of a finite-dim
    subspace is closed, so dense = equal. -/
def IsCyclic {n : ℕ} (A : Set (Matrix (Fin n) (Fin n) ℂ))
    (ψ : Fin n → ℂ) : Prop :=
  ∀ φ : Fin n → ℂ, ∃ a ∈ A, a *ᵥ ψ = φ

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: THE RANK-1 OUTER-PRODUCT WITNESS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Given a target `φ` and a vector `v` with `v ⬝ᵥ ψ = 1`, the rank-1
    outer product `vecMulVec φ v` sends `ψ ↦ φ`. -/

/-- **Rank-1 sender.** For a commutative ring, `Matrix.vecMulVec` is the
    rank-1 outer product. Acting on a vector `ψ` it gives a scalar
    multiple of the column factor:
    `(vecMulVec φ v) *ᵥ ψ = (v ⬝ᵥ ψ) • φ`. -/
lemma vecMulVec_mulVec_comm {n : ℕ} (φ v ψ : Fin n → ℂ) :
    (Matrix.vecMulVec φ v) *ᵥ ψ = (v ⬝ᵥ ψ) • φ := by
  -- Mathlib's `Matrix.vecMulVec_mulVec` gives the opposite-smul form.
  -- Over a commutative ring, opposite-smul = ordinary smul.
  funext i
  -- LHS: `(vecMulVec φ v *ᵥ ψ) i = ∑ j, φ i * v j * ψ j`.
  -- RHS: `((v ⬝ᵥ ψ) • φ) i = (∑ j, v j * ψ j) * φ i`.
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply,
             Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- **Witness covector.** If `ψ i₀ ≠ 0` then the singleton vector
    `Pi.single i₀ (1 / ψ i₀)` has dot product `1` with `ψ`. -/
lemma single_inv_dotProduct {n : ℕ} (ψ : Fin n → ℂ)
    (i₀ : Fin n) (hi : ψ i₀ ≠ 0) :
    (Pi.single i₀ (1 / ψ i₀)) ⬝ᵥ ψ = 1 := by
  rw [single_dotProduct]
  exact one_div_mul_cancel hi

/-- **Existence of a witness coordinate.** A nonzero vector has at
    least one coordinate that is nonzero. -/
lemma exists_ne_zero_coord {n : ℕ} {ψ : Fin n → ℂ} (hψ : ψ ≠ 0) :
    ∃ i₀ : Fin n, ψ i₀ ≠ 0 := by
  by_contra h
  push_neg at h
  apply hψ
  funext i
  exact h i

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: CYCLICITY OF EVERY NONZERO VECTOR FOR THE FULL ALGEBRA
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Finite-dim Reeh–Schlieder, unwrapped form.** For every nonzero
    `ψ ∈ ℂⁿ` and every target `φ ∈ ℂⁿ`, there is a matrix `a` such
    that `a *ᵥ ψ = φ`.

    Construction: pick any coordinate `i₀` with `ψ i₀ ≠ 0` and take
    `a := vecMulVec φ (Pi.single i₀ (1 / ψ i₀))`. -/
theorem reeh_schlieder_toy {n : ℕ} (ψ : Fin n → ℂ) (hψ : ψ ≠ 0) :
    ∀ φ : Fin n → ℂ, ∃ a : Matrix (Fin n) (Fin n) ℂ, a *ᵥ ψ = φ := by
  intro φ
  obtain ⟨i₀, hi⟩ := exists_ne_zero_coord hψ
  refine ⟨Matrix.vecMulVec φ (Pi.single i₀ (1 / ψ i₀)), ?_⟩
  rw [vecMulVec_mulVec_comm, single_inv_dotProduct ψ i₀ hi, one_smul]

/-- **Finite-dim Reeh–Schlieder, packaged form.** Every nonzero
    vector is cyclic for the full matrix algebra `End(ℂⁿ)`. -/
theorem full_algebra_cyclic_for_nonzero {n : ℕ} (ψ : Fin n → ℂ)
    (hψ : ψ ≠ 0) :
    IsCyclic (Set.univ : Set (Matrix (Fin n) (Fin n) ℂ)) ψ := by
  intro φ
  obtain ⟨a, ha⟩ := reeh_schlieder_toy ψ hψ φ
  exact ⟨a, Set.mem_univ a, ha⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: THE HYPOTHESIS `ψ ≠ 0` IS NECESSARY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    If `ψ = 0` then every matrix sends it to `0`, so the orbit is the
    single point `{0}`, which is NOT all of `ℂⁿ` whenever `n ≥ 1`. -/

/-- **Sharpness of the non-vanishing hypothesis.** For `n ≥ 1`, the
    zero vector is NOT cyclic for the full algebra. -/
theorem zero_not_cyclic {n : ℕ} (hn : 0 < n) :
    ¬ IsCyclic (Set.univ : Set (Matrix (Fin n) (Fin n) ℂ))
        (0 : Fin n → ℂ) := by
  intro hcyc
  -- Pick the constant-`1` target. Every matrix kills `0`, so it
  -- cannot be reached.
  obtain ⟨a, _, ha⟩ := hcyc (fun _ => (1 : ℂ))
  -- `a *ᵥ 0 = 0`, but `(fun _ => 1) ⟨0, hn⟩ = 1`.
  have h0 : a *ᵥ (0 : Fin n → ℂ) = 0 := Matrix.mulVec_zero a
  rw [h0] at ha
  have : (0 : Fin n → ℂ) ⟨0, hn⟩ = (fun _ : Fin n => (1 : ℂ)) ⟨0, hn⟩ :=
    congrArg (fun f => f ⟨0, hn⟩) ha
  simp at this

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: STRUCTURAL COROLLARIES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Orbit is the whole space.** Reformulation of
    `full_algebra_cyclic_for_nonzero` as a set equality. -/
theorem orbit_full_algebra_eq_univ {n : ℕ} (ψ : Fin n → ℂ) (hψ : ψ ≠ 0) :
    {φ : Fin n → ℂ | ∃ a : Matrix (Fin n) (Fin n) ℂ, a *ᵥ ψ = φ}
      = Set.univ := by
  apply Set.eq_univ_of_forall
  intro φ
  exact reeh_schlieder_toy ψ hψ φ

/-- **Cyclicity is a surjectivity statement.** Cyclicity of `ψ` for
    the full algebra is equivalent to the action map
    `a ↦ a *ᵥ ψ` being surjective. -/
theorem isCyclic_univ_iff_surjective {n : ℕ} (ψ : Fin n → ℂ) :
    IsCyclic (Set.univ : Set (Matrix (Fin n) (Fin n) ℂ)) ψ ↔
      Function.Surjective (fun a : Matrix (Fin n) (Fin n) ℂ => a *ᵥ ψ) := by
  constructor
  · intro h φ
    obtain ⟨a, _, ha⟩ := h φ
    exact ⟨a, ha⟩
  · intro h φ
    obtain ⟨a, ha⟩ := h φ
    exact ⟨a, Set.mem_univ a, ha⟩

/-- **Action map is surjective for nonzero ψ.** Restated form of the
    main theorem in `Function.Surjective` language. -/
theorem action_map_surjective {n : ℕ} (ψ : Fin n → ℂ) (hψ : ψ ≠ 0) :
    Function.Surjective
      (fun a : Matrix (Fin n) (Fin n) ℂ => a *ᵥ ψ) := by
  rw [← isCyclic_univ_iff_surjective]
  exact full_algebra_cyclic_for_nonzero ψ hψ

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: NAMED TARGETS FOR THE FULL ALGEBRAIC-QFT STATEMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The full Reeh–Schlieder theorem requires:
      • A Hilbert space `H` (infinite-dim, separable).
      • A vacuum vector `Ω ∈ H` and a unitary positive-energy
        representation of the spacetime translation group.
      • A net of local C-star / von Neumann algebras `A(O)` indexed
        by open spacetime regions.
      • Tomita–Takesaki modular theory (the local algebras are
        Type III).
      • Closure with respect to the strong operator topology.

    None of that infrastructure is yet present in this development;
    we register the target propositions so dependents can name them
    without committing to a proof in this file. -/

/-- **Target.** The genuine Reeh–Schlieder theorem in algebraic QFT:
    for every open spacetime region `O`, `A(O) Ω` is dense in `H`.
    Not formalised here (requires Tomita–Takesaki + Type III von
    Neumann algebras + a local-net structure).

    HONEST_SCOPE_NOTE.  Kept as `True` for compatibility with
    `reehSchlieder_AlgebraicQFT_target_witness`.  The substantive
    finite-dim shadow of cyclicity actually proved in this file is
    `ReehSchlieder_FiniteDim_Target` (which is the strict
    finite-dim analogue: every nonzero `ψ ∈ ℂⁿ` is cyclic for the
    full matrix algebra acting by left multiplication).  See
    Part 5 for surjectivity / orbit-equals-univ reformulations. -/
def ReehSchlieder_AlgebraicQFT_Target : Prop := True

/-- **Target.** The finite-dim Reeh–Schlieder result (= the theorem
    actually proved in this file), packaged as a named proposition
    that downstream files may quote without re-deriving. -/
def ReehSchlieder_FiniteDim_Target : Prop :=
  ∀ (n : ℕ) (ψ : Fin n → ℂ), ψ ≠ 0 →
    ∀ φ : Fin n → ℂ, ∃ a : Matrix (Fin n) (Fin n) ℂ, a *ᵥ ψ = φ

/-- The finite-dim Reeh–Schlieder named target is precisely what
    `reeh_schlieder_toy` proves, so it discharges trivially. -/
theorem reehSchlieder_finiteDim_target_holds :
    ReehSchlieder_FiniteDim_Target := by
  intro n ψ hψ φ
  exact reeh_schlieder_toy ψ hψ φ

/-- Trivial witness for the algebraic-QFT named target (the target
    proposition is `True`; the genuine theorem is out of scope of
    this file's formalisation). -/
theorem reehSchlieder_AlgebraicQFT_target_witness :
    ReehSchlieder_AlgebraicQFT_Target := trivial

/-- **Substantive sibling.**  The finite-dim Reeh–Schlieder content
    this file actually establishes, packaged as a single Prop:

      (a) every nonzero `ψ ∈ ℂⁿ` is cyclic for the full matrix
          algebra (orbit map is surjective);
      (b) the orbit `{a *ᵥ ψ : a ∈ Mat_n(ℂ)}` is literally all of
          `ℂⁿ`;
      (c) the hypothesis `ψ ≠ 0` is sharp: the zero vector is NOT
          cyclic for `n ≥ 1`. -/
def ReehSchlieder_AlgebraicQFT_Target_Substantive : Prop :=
  (∀ (n : ℕ) (ψ : Fin n → ℂ), ψ ≠ 0 →
      IsCyclic (Set.univ : Set (Matrix (Fin n) (Fin n) ℂ)) ψ) ∧
  (∀ (n : ℕ) (ψ : Fin n → ℂ), ψ ≠ 0 →
      {φ : Fin n → ℂ | ∃ a : Matrix (Fin n) (Fin n) ℂ, a *ᵥ ψ = φ}
        = Set.univ) ∧
  (∀ (n : ℕ), 0 < n →
      ¬ IsCyclic (Set.univ : Set (Matrix (Fin n) (Fin n) ℂ))
          (0 : Fin n → ℂ))

/-- The substantive finite-dim Reeh–Schlieder target is discharged
    by the three headline theorems of this file. -/
theorem reehSchlieder_AlgebraicQFT_Target_Substantive_holds :
    ReehSchlieder_AlgebraicQFT_Target_Substantive :=
  ⟨fun _ ψ hψ => full_algebra_cyclic_for_nonzero ψ hψ,
   fun _ ψ hψ => orbit_full_algebra_eq_univ ψ hψ,
   fun _ hn => zero_not_cyclic hn⟩

end UnifiedTheory.LayerB.ReehSchlieder
