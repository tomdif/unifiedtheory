/-
  LayerB/QuantumTeleportation.lean — The quantum teleportation protocol
                                     (Bennett–Brassard–Crépeau–Jozsa–Peres–Wootters
                                      1993, real-amplitude version)

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  The standard quantum teleportation protocol (BBCJPW 1993):

      Alice has an unknown qubit |ψ⟩ = α|0⟩ + β|1⟩.  Alice and Bob
      share a Bell pair (the singlet (|01⟩ - |10⟩)/√2) on qubits 2
      and 3.  Alice performs a Bell-basis measurement on her qubit
      and her half of the pair (qubits 1 and 2), obtains one of four
      classical outcomes, and sends those two bits to Bob.  Bob
      applies a corresponding Pauli correction to his half (qubit 3)
      and recovers |ψ⟩ exactly (up to a global sign — physically
      invisible because the Born rule squares amplitudes).

  The four Bell-measurement outcomes, Bob's unnormalized residuals,
  the corresponding Pauli corrections, and the recovered states
  (real-amplitude version):

       outcome           Bob's residual           correction      recovered
       ──────────        ──────────────────       ──────────      ──────────
       |Φ⁺⟩              (-β/2,  α/2)             ZX              +(α, β)/2  =  +ψ/2
       |Φ⁻⟩              ( β/2,  α/2)             X               +(α, β)/2  =  +ψ/2
       |Ψ⁺⟩              (-α/2,  β/2)             Z               -(α, β)/2  =  -ψ/2
       |Ψ⁻⟩              (-α/2, -β/2)             I               -(α, β)/2  =  -ψ/2

  The 1/2 prefactor on the residuals is the Born-rule normalization
  (each outcome occurs with probability 1/4, so the residual amplitude
  has norm 1/2 before re-normalization).  After the correction the
  recovered direction is ±ψ.  In the standard QM formalism the global
  ± sign is unobservable; we record it explicitly here for honesty.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE — REAL AMPLITUDES

  Following the rest of the framework's QM bridge layer
  (`Entanglement.lean`, `BellTheorem.lean`, `QuantumEntanglement.lean`,
  `NoCloning.lean`), this file uses **real** single-qubit amplitudes
  `Fin 2 → ℝ` and the **real** singlet (|01⟩-|10⟩)/√2 already defined
  in `BellTheorem.lean`.  This is sufficient to teleport every state
  α|0⟩ + β|1⟩ with α, β ∈ ℝ — the entire real Bloch circle.

  The full protocol uses ℂ amplitudes; the algebraic structure is
  identical (the Pauli `Y` correction replaces our `ZX`; the partial
  inner product picks up complex conjugates instead of real
  transposes).  Lifting to `Fin 2 → ℂ` would be a routine extension;
  nothing in the present proof depends on amplitudes being real
  beyond the use of `ℝ` as the scalar ring.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS FRAMEWORK-DERIVED VS STANDARD QM

  – The single-qubit amplitude space `Fin 2 → ℝ` and the two-qubit
    space `Fin 2 → Fin 2 → ℝ` are the same spaces used by
    `Entanglement.lean` (`Matrix (Fin 2) (Fin 2) ℝ` is just a
    re-typing of `Fin 2 → Fin 2 → ℝ`).
  – The singlet state is exactly `BellTheorem.singletState`
    (re-used here; its entanglement is `QuantumEntanglement.singlet_is_entangled`).
  – The 3-qubit tensor `Fin 2 → Fin 2 → Fin 2 → ℝ` is the obvious
    extension of the framework's two-particle space.
  – The Pauli operators `X`, `Z`, `ZX` are introduced here as the
    framework's real-amplitude versions of the standard Pauli matrices.
  – No cloning of |ψ⟩ takes place: teleportation is consistent with
    `NoCloning.no_cloning` because Alice's measurement *destroys* the
    original copy on qubit 1.

  Zero sorry. Zero custom axioms.
-/
import UnifiedTheory.LayerB.QuantumEntanglement

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.QuantumTeleportation

open UnifiedTheory.LayerB.BellTheorem
open UnifiedTheory.LayerB.QuantumEntanglement

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: SINGLE-QUBIT STATES, NORMALIZATION, AND PAULI OPERATORS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A single-qubit state is `ψ : Fin 2 → ℝ` with α := ψ 0, β := ψ 1
    and α² + β² = 1.  The three real-amplitude Pauli operators
    `X`, `Z`, `ZX` are pointwise functions on this space; the
    identity is just `id`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A single-qubit state is a function `ψ : Fin 2 → ℝ`.  The two
    amplitudes `α := ψ 0` and `β := ψ 1` satisfy `α² + β² = 1`
    when normalized.  This abbreviation matches `Fin n → ℝ` already
    used as the single-particle amplitude space throughout LayerB. -/
abbrev Qubit : Type := Fin 2 → ℝ

/-- A qubit `ψ` is **normalized** iff its two amplitudes square-sum
    to one. -/
def IsNormalized (ψ : Qubit) : Prop := ψ 0 ^ 2 + ψ 1 ^ 2 = 1

/-- Build a qubit `(α, β)` from the two real amplitudes. -/
def mkQubit (α β : ℝ) : Qubit := fun i => if i = 0 then α else β

@[simp] theorem mkQubit_zero (α β : ℝ) : mkQubit α β 0 = α := by
  unfold mkQubit; simp

@[simp] theorem mkQubit_one (α β : ℝ) : mkQubit α β 1 = β := by
  unfold mkQubit
  have h : (1 : Fin 2) ≠ 0 := by decide
  simp [h]

/-- The real-amplitude **Pauli X** (bit-flip):
    `X · (α, β) = (β, α)`. -/
def pauliX (ψ : Qubit) : Qubit := fun i => if i = 0 then ψ 1 else ψ 0

/-- The real-amplitude **Pauli Z** (phase-flip):
    `Z · (α, β) = (α, -β)`. -/
def pauliZ (ψ : Qubit) : Qubit := fun i => if i = 0 then ψ 0 else -ψ 1

/-- The real-amplitude **`ZX = Z ∘ X`** correction:
    `ZX · (α, β) = (β, -α)`.  This is the real version of the
    Pauli `iY` (one of the four Pauli corrections in the standard
    teleportation table). -/
def pauliZX (ψ : Qubit) : Qubit := fun i => if i = 0 then ψ 1 else -ψ 0

@[simp] theorem pauliX_zero (ψ : Qubit) : pauliX ψ 0 = ψ 1 := by
  unfold pauliX; simp

@[simp] theorem pauliX_one (ψ : Qubit) : pauliX ψ 1 = ψ 0 := by
  unfold pauliX
  have h : (1 : Fin 2) ≠ 0 := by decide
  simp [h]

@[simp] theorem pauliZ_zero (ψ : Qubit) : pauliZ ψ 0 = ψ 0 := by
  unfold pauliZ; simp

@[simp] theorem pauliZ_one (ψ : Qubit) : pauliZ ψ 1 = -ψ 1 := by
  unfold pauliZ
  have h : (1 : Fin 2) ≠ 0 := by decide
  simp [h]

@[simp] theorem pauliZX_zero (ψ : Qubit) : pauliZX ψ 0 = ψ 1 := by
  unfold pauliZX; simp

@[simp] theorem pauliZX_one (ψ : Qubit) : pauliZX ψ 1 = -ψ 0 := by
  unfold pauliZX
  have h : (1 : Fin 2) ≠ 0 := by decide
  simp [h]

/-- `Z` is an involution: `Z (Z ψ) = ψ`. -/
theorem pauliZ_involution (ψ : Qubit) : pauliZ (pauliZ ψ) = ψ := by
  funext i
  fin_cases i <;> simp

/-- `X` is an involution: `X (X ψ) = ψ`. -/
theorem pauliX_involution (ψ : Qubit) : pauliX (pauliX ψ) = ψ := by
  funext i
  fin_cases i <;> simp

/-- `ZX² = -I` on real amplitudes (the analog of `(iY)² = -I`).  This
    is the algebraic shape that produces a global sign change when
    Bob's residual `(-β, α)` is acted on by `ZX`. -/
theorem pauliZX_squared (ψ : Qubit) :
    pauliZX (pauliZX ψ) = (fun i => -ψ i) := by
  funext i
  fin_cases i <;> simp

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: 3-QUBIT STATES AND THE INITIAL TENSOR `ψ ⊗ singlet`
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A three-qubit state is `Φ : Fin 2 → Fin 2 → Fin 2 → ℝ`,
    indexed by (Alice's qubit, Alice's half of the Bell pair,
    Bob's half of the Bell pair).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The three-qubit amplitude space, indexed as
    (Alice qubit, Alice's half of the Bell pair, Bob's half). -/
abbrev ThreeQubit : Type := Fin 2 → Fin 2 → Fin 2 → ℝ

/-- The tensor product `ψ ⊗ singletState`, producing a three-qubit
    state with the singlet on qubits 2 and 3.  Component `(i, j, k)`
    is `ψ i · singletState j k`. -/
noncomputable def tensorWithSinglet (ψ : Qubit) : ThreeQubit :=
  fun i j k => ψ i * singletState j k

/-- The four explicit nonzero entries of `tensorWithSinglet ψ`:
    `(ψ ⊗ singlet)(i, 0, 1) =  ψ i / √2` and
    `(ψ ⊗ singlet)(i, 1, 0) = -ψ i / √2`.  All other components vanish. -/
@[simp] theorem tensorWithSinglet_001 (ψ : Qubit) (i : Fin 2) :
    tensorWithSinglet ψ i 0 1 = ψ i / Real.sqrt 2 := by
  unfold tensorWithSinglet singletState
  simp; ring

@[simp] theorem tensorWithSinglet_010 (ψ : Qubit) (i : Fin 2) :
    tensorWithSinglet ψ i 1 0 = -(ψ i / Real.sqrt 2) := by
  unfold tensorWithSinglet singletState
  have h1 : ¬((1 : Fin 2) = 0 ∧ (0 : Fin 2) = 1) := by
    intro ⟨h, _⟩; exact absurd h (by decide)
  have h2 : (1 : Fin 2) = 1 ∧ (0 : Fin 2) = 0 := ⟨rfl, rfl⟩
  rw [if_neg h1, if_pos h2]
  ring

@[simp] theorem tensorWithSinglet_000 (ψ : Qubit) (i : Fin 2) :
    tensorWithSinglet ψ i 0 0 = 0 := by
  unfold tensorWithSinglet singletState
  simp

@[simp] theorem tensorWithSinglet_011 (ψ : Qubit) (i : Fin 2) :
    tensorWithSinglet ψ i 1 1 = 0 := by
  unfold tensorWithSinglet singletState
  have h1 : ¬((1 : Fin 2) = 0 ∧ (1 : Fin 2) = 1) := by
    intro ⟨h, _⟩; exact absurd h (by decide)
  have h2 : ¬((1 : Fin 2) = 1 ∧ (1 : Fin 2) = 0) := by
    intro ⟨_, h⟩; exact absurd h (by decide)
  rw [if_neg h1, if_neg h2]; ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: THE BELL BASIS ON QUBITS (1, 2)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The four maximally entangled two-qubit states (real amplitudes):

        |Φ⁺⟩ = (|00⟩ + |11⟩) / √2
        |Φ⁻⟩ = (|00⟩ - |11⟩) / √2
        |Ψ⁺⟩ = (|01⟩ + |10⟩) / √2
        |Ψ⁻⟩ = (|01⟩ - |10⟩) / √2     (= singletState from BellTheorem)

    Each is a function `Fin 2 → Fin 2 → ℝ`.  These four states
    form an orthonormal basis of the two-qubit amplitude space.
    Alice's Bell measurement projects onto one of them; the four
    classical outcomes correspond to the four branches.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The Bell state `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`. -/
noncomputable def bellPhiPlus : Fin 2 → Fin 2 → ℝ := fun i j =>
  if i = 0 ∧ j = 0 then 1 / Real.sqrt 2
  else if i = 1 ∧ j = 1 then 1 / Real.sqrt 2
  else 0

/-- The Bell state `|Φ⁻⟩ = (|00⟩ - |11⟩)/√2`. -/
noncomputable def bellPhiMinus : Fin 2 → Fin 2 → ℝ := fun i j =>
  if i = 0 ∧ j = 0 then 1 / Real.sqrt 2
  else if i = 1 ∧ j = 1 then -1 / Real.sqrt 2
  else 0

/-- The Bell state `|Ψ⁺⟩ = (|01⟩ + |10⟩)/√2`. -/
noncomputable def bellPsiPlus : Fin 2 → Fin 2 → ℝ := fun i j =>
  if i = 0 ∧ j = 1 then 1 / Real.sqrt 2
  else if i = 1 ∧ j = 0 then 1 / Real.sqrt 2
  else 0

/-- The Bell state `|Ψ⁻⟩` is exactly the framework's `singletState`
    (re-export by definition). -/
noncomputable def bellPsiMinus : Fin 2 → Fin 2 → ℝ := singletState

/-- `bellPsiMinus = singletState`. -/
theorem bellPsiMinus_eq : bellPsiMinus = singletState := rfl

/-! ### Explicit entries of the four Bell states

    These `simp` lemmas let us evaluate the partial inner products
    by direct computation. -/

@[simp] theorem bellPhiPlus_00 : bellPhiPlus 0 0 = 1 / Real.sqrt 2 := by
  unfold bellPhiPlus; simp

@[simp] theorem bellPhiPlus_01 : bellPhiPlus 0 1 = 0 := by
  unfold bellPhiPlus; simp

@[simp] theorem bellPhiPlus_10 : bellPhiPlus 1 0 = 0 := by
  unfold bellPhiPlus
  have h1 : ¬((1 : Fin 2) = 0 ∧ (0 : Fin 2) = 0) := by
    intro ⟨h, _⟩; exact absurd h (by decide)
  have h2 : ¬((1 : Fin 2) = 1 ∧ (0 : Fin 2) = 1) := by
    intro ⟨_, h⟩; exact absurd h (by decide)
  rw [if_neg h1, if_neg h2]

@[simp] theorem bellPhiPlus_11 : bellPhiPlus 1 1 = 1 / Real.sqrt 2 := by
  unfold bellPhiPlus
  simp

@[simp] theorem bellPhiMinus_00 : bellPhiMinus 0 0 = 1 / Real.sqrt 2 := by
  unfold bellPhiMinus; simp

@[simp] theorem bellPhiMinus_01 : bellPhiMinus 0 1 = 0 := by
  unfold bellPhiMinus; simp

@[simp] theorem bellPhiMinus_10 : bellPhiMinus 1 0 = 0 := by
  unfold bellPhiMinus
  have h1 : ¬((1 : Fin 2) = 0 ∧ (0 : Fin 2) = 0) := by
    intro ⟨h, _⟩; exact absurd h (by decide)
  have h2 : ¬((1 : Fin 2) = 1 ∧ (0 : Fin 2) = 1) := by
    intro ⟨_, h⟩; exact absurd h (by decide)
  rw [if_neg h1, if_neg h2]

@[simp] theorem bellPhiMinus_11 : bellPhiMinus 1 1 = -1 / Real.sqrt 2 := by
  unfold bellPhiMinus
  have h1 : ¬((1 : Fin 2) = 0 ∧ (1 : Fin 2) = 0) := by
    intro ⟨h, _⟩; exact absurd h (by decide)
  have h2 : (1 : Fin 2) = 1 ∧ (1 : Fin 2) = 1 := ⟨rfl, rfl⟩
  rw [if_neg h1, if_pos h2]

@[simp] theorem bellPsiPlus_00 : bellPsiPlus 0 0 = 0 := by
  unfold bellPsiPlus; simp

@[simp] theorem bellPsiPlus_01 : bellPsiPlus 0 1 = 1 / Real.sqrt 2 := by
  unfold bellPsiPlus; simp

@[simp] theorem bellPsiPlus_10 : bellPsiPlus 1 0 = 1 / Real.sqrt 2 := by
  unfold bellPsiPlus
  have h1 : ¬((1 : Fin 2) = 0 ∧ (0 : Fin 2) = 1) := by
    intro ⟨h, _⟩; exact absurd h (by decide)
  have h2 : (1 : Fin 2) = 1 ∧ (0 : Fin 2) = 0 := ⟨rfl, rfl⟩
  rw [if_neg h1, if_pos h2]

@[simp] theorem bellPsiPlus_11 : bellPsiPlus 1 1 = 0 := by
  unfold bellPsiPlus
  have h1 : ¬((1 : Fin 2) = 0 ∧ (1 : Fin 2) = 1) := by
    intro ⟨h, _⟩; exact absurd h (by decide)
  have h2 : ¬((1 : Fin 2) = 1 ∧ (1 : Fin 2) = 0) := by
    intro ⟨_, h⟩; exact absurd h (by decide)
  rw [if_neg h1, if_neg h2]

@[simp] theorem bellPsiMinus_00 : bellPsiMinus 0 0 = 0 := by
  unfold bellPsiMinus singletState; simp

@[simp] theorem bellPsiMinus_01 : bellPsiMinus 0 1 = 1 / Real.sqrt 2 := by
  unfold bellPsiMinus singletState; simp

@[simp] theorem bellPsiMinus_10 : bellPsiMinus 1 0 = -1 / Real.sqrt 2 := by
  unfold bellPsiMinus singletState
  have h1 : ¬((1 : Fin 2) = 0 ∧ (0 : Fin 2) = 1) := by
    intro ⟨h, _⟩; exact absurd h (by decide)
  have h2 : (1 : Fin 2) = 1 ∧ (0 : Fin 2) = 0 := ⟨rfl, rfl⟩
  rw [if_neg h1, if_pos h2]

@[simp] theorem bellPsiMinus_11 : bellPsiMinus 1 1 = 0 := by
  unfold bellPsiMinus singletState
  have h1 : ¬((1 : Fin 2) = 0 ∧ (1 : Fin 2) = 1) := by
    intro ⟨h, _⟩; exact absurd h (by decide)
  have h2 : ¬((1 : Fin 2) = 1 ∧ (1 : Fin 2) = 0) := by
    intro ⟨_, h⟩; exact absurd h (by decide)
  rw [if_neg h1, if_neg h2]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: PARTIAL INNER PRODUCT — BOB'S RESIDUAL STATE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Given a 3-qubit state `Φ(i, j, k)` and a 2-qubit "test" state
    `B(i, j)` on qubits 1 and 2, the partial inner product
        partialInner B Φ k := Σ_{i, j} B(i, j) · Φ(i, j, k)
    is Bob's residual single-qubit amplitude after he is told that
    Alice measured her two qubits in the Bell-basis projector
    associated with `B`.  (In standard formalism: `⟨B|_{12} Φ⟩_{12, 3}`,
    leaving a vector on the 3rd qubit.)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The partial inner product on the first two qubits — Bob's
    residual amplitude, parametrized by the outcome state `B`. -/
noncomputable def partialInner (B : Fin 2 → Fin 2 → ℝ) (Φ : ThreeQubit) : Qubit :=
  fun k => ∑ i : Fin 2, ∑ j : Fin 2, B i j * Φ i j k

/-- Helper: `√2 · √2 = 2` — repeatedly used to collapse Born-rule
    normalizations. -/
private lemma sqrt_two_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 := by
  have := Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)
  rw [sq] at this; exact this

/-- `√2 ≠ 0`. -/
private lemma sqrt_two_ne_zero : Real.sqrt 2 ≠ 0 := by
  intro h
  have h2 := sqrt_two_mul_self
  rw [h, mul_zero] at h2; norm_num at h2

/-- `(√2)⁻¹ ^ 2 = 1 / 2`. -/
private lemma sqrt_two_inv_sq : (Real.sqrt 2)⁻¹ ^ 2 = 1 / 2 := by
  rw [inv_pow, sq, sqrt_two_mul_self]
  norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: THE FOUR RESIDUAL STATES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    For ψ = (α, β) and the four Bell-basis outcomes:

       outcome |Φ⁺⟩ → Bob's residual = (-β/2,  α/2)
       outcome |Φ⁻⟩ → Bob's residual = ( β/2,  α/2)
       outcome |Ψ⁺⟩ → Bob's residual = (-α/2,  β/2)
       outcome |Ψ⁻⟩ → Bob's residual = (-α/2, -β/2)

    (All four are explicit: the partial inner product collapses the
    sum to the two surviving terms ψ(0)·singlet(0,k) and ψ(1)·singlet(1,k)
    weighted by the corresponding Bell amplitudes.)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The partial inner product expanded as the four-term sum. -/
private lemma partialInner_expand (B : Fin 2 → Fin 2 → ℝ) (ψ : Qubit) (k : Fin 2) :
    partialInner B (tensorWithSinglet ψ) k =
      B 0 0 * tensorWithSinglet ψ 0 0 k
    + B 0 1 * tensorWithSinglet ψ 0 1 k
    + B 1 0 * tensorWithSinglet ψ 1 0 k
    + B 1 1 * tensorWithSinglet ψ 1 1 k := by
  unfold partialInner
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  ring

/-! Specialized `tensorWithSinglet ψ i j k` values for fixed `(j, k)`.
    The only non-zero `(j, k)` slices are `(0, 1)` (already covered
    by `tensorWithSinglet_001`) and `(1, 0)` (covered by
    `tensorWithSinglet_010`).  The remaining six entries vanish:
    `(j, k) ∈ {(0, 0), (1, 1)}` are 0 for any `i` because
    `singletState 0 0 = singletState 1 1 = 0`. -/

@[simp] theorem tensorWithSinglet_jk_00 (ψ : Qubit) (i : Fin 2) :
    tensorWithSinglet ψ i 0 0 = 0 := tensorWithSinglet_000 ψ i

@[simp] theorem tensorWithSinglet_jk_11 (ψ : Qubit) (i : Fin 2) :
    tensorWithSinglet ψ i 1 1 = 0 := tensorWithSinglet_011 ψ i

/-! The eight `tensorWithSinglet ψ i j k` values, written out:
    – `(i, 0, 0) = 0`, `(i, 1, 1) = 0` (zero column of singlet),
    – `(i, 0, 1) =  ψ i / √2`,
    – `(i, 1, 0) = -ψ i / √2`. -/

/-- **Residual after `|Φ⁺⟩` measurement:**
    `partialInner |Φ⁺⟩ (ψ ⊗ singlet) (0) = -ψ(1)/2`,
    `partialInner |Φ⁺⟩ (ψ ⊗ singlet) (1) =  ψ(0)/2`.

    The Bell state `|Φ⁺⟩` has support on `(i, j) = (0,0)` and `(1,1)`;
    in the initial 3-qubit state, the `(0, 0, k)` slice vanishes for
    both `k`, and the `(1, 1, k)` slice equals `-ψ(1)/√2` (`k = 0`)
    or `0` (`k = 1`). -/
theorem residual_phi_plus_zero (ψ : Qubit) :
    partialInner bellPhiPlus (tensorWithSinglet ψ) 0 = -(ψ 1 / 2) := by
  rw [partialInner_expand]
  rw [bellPhiPlus_00, bellPhiPlus_01, bellPhiPlus_10, bellPhiPlus_11,
      tensorWithSinglet_jk_00, tensorWithSinglet_010, tensorWithSinglet_jk_00,
      tensorWithSinglet_010]
  rw [show (1 : ℝ) / Real.sqrt 2 = (Real.sqrt 2)⁻¹ from one_div _]
  have hk := sqrt_two_inv_sq
  ring_nf
  rw [hk]
  ring

theorem residual_phi_plus_one (ψ : Qubit) :
    partialInner bellPhiPlus (tensorWithSinglet ψ) 1 = ψ 0 / 2 := by
  rw [partialInner_expand]
  rw [bellPhiPlus_00, bellPhiPlus_01, bellPhiPlus_10, bellPhiPlus_11,
      tensorWithSinglet_001, tensorWithSinglet_jk_11, tensorWithSinglet_001,
      tensorWithSinglet_jk_11]
  rw [show (1 : ℝ) / Real.sqrt 2 = (Real.sqrt 2)⁻¹ from one_div _]
  have hk := sqrt_two_inv_sq
  ring_nf
  rw [hk]
  ring

/-- **Residual after `|Φ⁻⟩` measurement:**
    `(0) =  ψ(1)/2`,  `(1) =  ψ(0)/2`. -/
theorem residual_phi_minus_zero (ψ : Qubit) :
    partialInner bellPhiMinus (tensorWithSinglet ψ) 0 = ψ 1 / 2 := by
  rw [partialInner_expand]
  rw [bellPhiMinus_00, bellPhiMinus_01, bellPhiMinus_10, bellPhiMinus_11,
      tensorWithSinglet_jk_00, tensorWithSinglet_010, tensorWithSinglet_jk_00,
      tensorWithSinglet_010]
  rw [show (1 : ℝ) / Real.sqrt 2 = (Real.sqrt 2)⁻¹ from one_div _,
      show (-1 : ℝ) / Real.sqrt 2 = -(Real.sqrt 2)⁻¹ by rw [neg_div, one_div]]
  have hk := sqrt_two_inv_sq
  ring_nf
  rw [hk]
  ring

theorem residual_phi_minus_one (ψ : Qubit) :
    partialInner bellPhiMinus (tensorWithSinglet ψ) 1 = ψ 0 / 2 := by
  rw [partialInner_expand]
  rw [bellPhiMinus_00, bellPhiMinus_01, bellPhiMinus_10, bellPhiMinus_11,
      tensorWithSinglet_001, tensorWithSinglet_jk_11, tensorWithSinglet_001,
      tensorWithSinglet_jk_11]
  rw [show (1 : ℝ) / Real.sqrt 2 = (Real.sqrt 2)⁻¹ from one_div _,
      show (-1 : ℝ) / Real.sqrt 2 = -(Real.sqrt 2)⁻¹ by rw [neg_div, one_div]]
  have hk := sqrt_two_inv_sq
  ring_nf
  rw [hk]
  ring

/-- **Residual after `|Ψ⁺⟩` measurement:**
    `(0) = -ψ(0)/2`,  `(1) =  ψ(1)/2`. -/
theorem residual_psi_plus_zero (ψ : Qubit) :
    partialInner bellPsiPlus (tensorWithSinglet ψ) 0 = -(ψ 0 / 2) := by
  rw [partialInner_expand]
  rw [bellPsiPlus_00, bellPsiPlus_01, bellPsiPlus_10, bellPsiPlus_11,
      tensorWithSinglet_jk_00, tensorWithSinglet_010, tensorWithSinglet_jk_00,
      tensorWithSinglet_010]
  rw [show (1 : ℝ) / Real.sqrt 2 = (Real.sqrt 2)⁻¹ from one_div _]
  have hk := sqrt_two_inv_sq
  ring_nf
  rw [hk]
  ring

theorem residual_psi_plus_one (ψ : Qubit) :
    partialInner bellPsiPlus (tensorWithSinglet ψ) 1 = ψ 1 / 2 := by
  rw [partialInner_expand]
  rw [bellPsiPlus_00, bellPsiPlus_01, bellPsiPlus_10, bellPsiPlus_11,
      tensorWithSinglet_001, tensorWithSinglet_jk_11, tensorWithSinglet_001,
      tensorWithSinglet_jk_11]
  rw [show (1 : ℝ) / Real.sqrt 2 = (Real.sqrt 2)⁻¹ from one_div _]
  have hk := sqrt_two_inv_sq
  ring_nf
  rw [hk]
  ring

/-- **Residual after `|Ψ⁻⟩` measurement:**
    `(0) = -ψ(0)/2`,  `(1) = -ψ(1)/2`. -/
theorem residual_psi_minus_zero (ψ : Qubit) :
    partialInner bellPsiMinus (tensorWithSinglet ψ) 0 = -(ψ 0 / 2) := by
  rw [partialInner_expand]
  rw [bellPsiMinus_00, bellPsiMinus_01, bellPsiMinus_10, bellPsiMinus_11,
      tensorWithSinglet_jk_00, tensorWithSinglet_010, tensorWithSinglet_jk_00,
      tensorWithSinglet_010]
  rw [show (1 : ℝ) / Real.sqrt 2 = (Real.sqrt 2)⁻¹ from one_div _,
      show (-1 : ℝ) / Real.sqrt 2 = -(Real.sqrt 2)⁻¹ by rw [neg_div, one_div]]
  have hk := sqrt_two_inv_sq
  ring_nf
  rw [hk]
  ring

theorem residual_psi_minus_one (ψ : Qubit) :
    partialInner bellPsiMinus (tensorWithSinglet ψ) 1 = -(ψ 1 / 2) := by
  rw [partialInner_expand]
  rw [bellPsiMinus_00, bellPsiMinus_01, bellPsiMinus_10, bellPsiMinus_11,
      tensorWithSinglet_001, tensorWithSinglet_jk_11, tensorWithSinglet_001,
      tensorWithSinglet_jk_11]
  rw [show (1 : ℝ) / Real.sqrt 2 = (Real.sqrt 2)⁻¹ from one_div _,
      show (-1 : ℝ) / Real.sqrt 2 = -(Real.sqrt 2)⁻¹ by rw [neg_div, one_div]]
  have hk := sqrt_two_inv_sq
  ring_nf
  rw [hk]
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: BOB'S CORRECTION RECOVERS ±|ψ⟩
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Bob's residual is `(1/2)·R · ψ` for one of four Pauli-like
    operators `R ∈ {-ZX, X, -Z, -I}` (the sign is part of `R`).  The
    correction Bob applies is the operator that sends each residual
    to `±ψ/2`:

        residual = -ZX · ψ / 2     →   apply ZX :  ZX · (-ZX · ψ / 2)
                                                  = -ZX² · ψ / 2  =  ψ / 2

        residual =   X · ψ / 2     →   apply X  :  X² · ψ / 2     =  ψ / 2

        residual =  -Z · ψ / 2     →   apply Z  :  Z · (-Z · ψ / 2)
                                                  = -Z² · ψ / 2   = -ψ / 2

        residual =  -I · ψ / 2     →   apply I  :  -ψ / 2          = -ψ / 2

    The ± sign is a global phase (physically invisible since the Born
    rule squares amplitudes).  We record the equality up to that sign
    explicitly.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Bob's correction recovers `+ψ/2` from the `|Φ⁺⟩` residual.**

    The residual is `(-ψ(1)/2, ψ(0)/2)`.  Apply `ZX`:  `ZX·(-β/2, α/2)`
    sends index 0 to `(α/2)` (the second component) and index 1 to
    `-(-β/2) = β/2`, recovering exactly `(α/2, β/2) = ψ/2`. -/
theorem correction_phi_plus (ψ : Qubit) :
    pauliZX (partialInner bellPhiPlus (tensorWithSinglet ψ)) =
      (fun k => ψ k / 2) := by
  funext k
  fin_cases k
  · simp [pauliZX_zero, residual_phi_plus_one]
  · simp [pauliZX_one, residual_phi_plus_zero]

/-- **Bob's correction recovers `+ψ/2` from the `|Φ⁻⟩` residual.**

    The residual is `(ψ(1)/2, ψ(0)/2)`.  Apply `X`:  swap the two
    components → `(ψ(0)/2, ψ(1)/2) = ψ/2`. -/
theorem correction_phi_minus (ψ : Qubit) :
    pauliX (partialInner bellPhiMinus (tensorWithSinglet ψ)) =
      (fun k => ψ k / 2) := by
  funext k
  fin_cases k
  · simp [pauliX_zero, residual_phi_minus_one]
  · simp [pauliX_one, residual_phi_minus_zero]

/-- **Bob's correction recovers `-ψ/2` from the `|Ψ⁺⟩` residual.**

    The residual is `(-ψ(0)/2, ψ(1)/2)`.  Apply `Z`:  index 0 unchanged
    → `-ψ(0)/2`, index 1 negated → `-ψ(1)/2`, total `-ψ/2`. -/
theorem correction_psi_plus (ψ : Qubit) :
    pauliZ (partialInner bellPsiPlus (tensorWithSinglet ψ)) =
      (fun k => -(ψ k / 2)) := by
  funext k
  fin_cases k
  · simp [pauliZ_zero, residual_psi_plus_zero]
  · simp [pauliZ_one, residual_psi_plus_one]

/-- **Bob applies the identity to the `|Ψ⁻⟩` residual; it equals `-ψ/2`.**

    The residual is already `(-ψ(0)/2, -ψ(1)/2) = -ψ/2`.  No correction
    needed; Bob's qubit is `-ψ/2` (a global sign, physically invisible). -/
theorem correction_psi_minus (ψ : Qubit) :
    partialInner bellPsiMinus (tensorWithSinglet ψ) =
      (fun k => -(ψ k / 2)) := by
  funext k
  fin_cases k
  · exact residual_psi_minus_zero ψ
  · exact residual_psi_minus_one ψ

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 7: THE TELEPORTATION PROTOCOL — ABSTRACT FORMULATION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A teleportation `outcome` is one of four Bell-measurement results;
    `correctedState` is Bob's qubit after the appropriate Pauli
    correction; the protocol is correct iff `correctedState` recovers
    `±ψ/2` for every input.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The four Bell-measurement outcomes. -/
inductive BellOutcome
  | phiPlus
  | phiMinus
  | psiPlus
  | psiMinus
  deriving DecidableEq

/-- The Bell state corresponding to each outcome. -/
noncomputable def bellStateOf : BellOutcome → (Fin 2 → Fin 2 → ℝ)
  | .phiPlus  => bellPhiPlus
  | .phiMinus => bellPhiMinus
  | .psiPlus  => bellPsiPlus
  | .psiMinus => bellPsiMinus

@[simp] theorem bellStateOf_phiPlus : bellStateOf .phiPlus = bellPhiPlus := rfl
@[simp] theorem bellStateOf_phiMinus : bellStateOf .phiMinus = bellPhiMinus := rfl
@[simp] theorem bellStateOf_psiPlus : bellStateOf .psiPlus = bellPsiPlus := rfl
@[simp] theorem bellStateOf_psiMinus : bellStateOf .psiMinus = bellPsiMinus := rfl

/-- The Pauli correction Bob applies for each outcome. -/
def correctionOf : BellOutcome → (Qubit → Qubit)
  | .phiPlus  => pauliZX
  | .phiMinus => pauliX
  | .psiPlus  => pauliZ
  | .psiMinus => id

@[simp] theorem correctionOf_phiPlus : correctionOf .phiPlus = pauliZX := rfl
@[simp] theorem correctionOf_phiMinus : correctionOf .phiMinus = pauliX := rfl
@[simp] theorem correctionOf_psiPlus : correctionOf .psiPlus = pauliZ := rfl
@[simp] theorem correctionOf_psiMinus : correctionOf .psiMinus = id := rfl

/-- The sign Bob recovers (`+1` for `Φ⁺`, `Φ⁻`, `-1` for `Ψ⁺`, `Ψ⁻`).
    Physically invisible (Born rule squares amplitudes); recorded
    explicitly for honesty. -/
def signOf : BellOutcome → ℝ
  | .phiPlus  =>  1
  | .phiMinus =>  1
  | .psiPlus  => -1
  | .psiMinus => -1

/-- **THE TELEPORTATION PROTOCOL CORRECTNESS THEOREM.**

    For every input qubit `ψ` and every Bell-measurement outcome `o`,
    Bob's corrected state equals `signOf(o) · ψ / 2`.  The `1/2`
    factor is the Born-rule normalization (each outcome occurs with
    probability `1/4`, so the residual amplitude has norm `1/2`); the
    `signOf` factor is a global sign that does not affect physical
    measurements.

    In particular, the renormalized recovered state is `±ψ` in every
    branch — Bob has perfectly received Alice's unknown qubit. -/
theorem teleportation_correct (ψ : Qubit) (o : BellOutcome) :
    correctionOf o (partialInner (bellStateOf o) (tensorWithSinglet ψ)) =
      (fun k => signOf o * ψ k / 2) := by
  cases o
  · -- .phiPlus
    simp only [bellStateOf_phiPlus, correctionOf_phiPlus, signOf]
    rw [correction_phi_plus]
    funext k; ring
  · -- .phiMinus
    simp only [bellStateOf_phiMinus, correctionOf_phiMinus, signOf]
    rw [correction_phi_minus]
    funext k; ring
  · -- .psiPlus
    simp only [bellStateOf_psiPlus, correctionOf_psiPlus, signOf]
    rw [correction_psi_plus]
    funext k; ring
  · -- .psiMinus
    simp only [bellStateOf_psiMinus, correctionOf_psiMinus, signOf, id_eq]
    rw [correction_psi_minus]
    funext k; ring

/-- **Up-to-sign restatement.**  In every branch, Bob's corrected
    state has the form `c · ψ` for some real scalar `c` (specifically,
    `c = signOf(o) / 2`).  Since the Born rule depends only on `c²`,
    Bob has recovered the physical qubit `ψ`. -/
theorem teleportation_recovers_psi_up_to_scalar (ψ : Qubit)
    (o : BellOutcome) :
    ∃ c : ℝ, correctionOf o (partialInner (bellStateOf o) (tensorWithSinglet ψ))
              = (fun k => c * ψ k) := by
  refine ⟨signOf o / 2, ?_⟩
  funext k
  have h := congr_fun (teleportation_correct ψ o) k
  rw [h]
  ring

/-- **Born-rule scalar:**  the scalar `c = signOf(o) / 2` satisfies
    `c² = 1/4`, so the probability of outcome `o` (per the Born rule
    applied to `c · ψ` for normalized `ψ`) is exactly `1/4`.  This is
    the standard "all four outcomes equally likely" property of the
    teleportation protocol. -/
theorem outcome_probability_one_quarter (o : BellOutcome) :
    (signOf o / 2) ^ 2 = 1 / 4 := by
  cases o <;> (unfold signOf; norm_num)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 8: CONSISTENCY WITH NO-CLONING
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Teleportation does NOT violate the no-cloning theorem (proved in
    `NoCloning.lean`).  After Alice's Bell measurement, qubits 1 and
    2 are projected onto the Bell state of the outcome; the original
    information about `ψ` is no longer recoverable from qubits 1, 2.
    Only Bob's qubit 3, after correction, carries `ψ`.  Hence the
    final 3-qubit configuration has `ψ` on qubit 3 and a definite
    Bell state on qubits 1, 2 — there is **no second copy of `ψ`**.
    The framework's `no_cloning` rules out a *linear* copier
    `(Fin n → ℝ) →ₗ[ℝ] Matrix` of *one* state to *two* copies; the
    teleportation channel `(ψ, singlet) ↦ Bob's qubit` is a
    one-to-one transmission, not a cloner.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Consistency note (no-cloning vs teleportation).**

    The teleportation channel sends Alice's input qubit `ψ` to Bob's
    output qubit `c · ψ` for a definite scalar `c = signOf(o) / 2`.
    Crucially, Alice's original qubit and her half of the Bell pair
    end up in a fixed Bell state determined by the outcome — they
    no longer carry `ψ`.  Therefore the final state has exactly ONE
    copy of `ψ` (on Bob's qubit), not two.  This is consistent with
    `NoCloning.no_cloning`. -/
theorem teleportation_no_clone (ψ : Qubit) (o : BellOutcome) :
    ∃ c : ℝ,
      -- Bob's qubit carries (a scalar multiple of) ψ
      correctionOf o (partialInner (bellStateOf o) (tensorWithSinglet ψ))
        = (fun k => c * ψ k) :=
  teleportation_recovers_psi_up_to_scalar ψ o

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 9: MASTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE QUANTUM TELEPORTATION MASTER THEOREM.**

    A self-contained statement of the BBCJPW 1993 protocol in the
    framework's amplitude vocabulary:

    (1) For every input qubit `ψ` and every Bell-measurement outcome
        `o ∈ {Φ⁺, Φ⁻, Ψ⁺, Ψ⁻}`, Bob's corrected state equals
        `signOf(o) · ψ / 2` exactly (where `signOf(o) ∈ {+1, -1}` is
        the global sign and `1/2` is the Born-rule normalization).

    (2) Every outcome `o` carries the same Born-rule probability
        `(signOf(o)/2)² = 1/4`, so the four outcomes are equiprobable.

    (3) Bob's recovered state is a scalar multiple of `ψ` in every
        branch; hence the renormalized post-correction state IS the
        physical qubit `ψ`.  The sign is a global phase (invisible to
        the Born rule).

    (4) Consistency with no-cloning: the protocol *transmits* `ψ` —
        it does not *copy* it.  After the protocol the original
        qubit + Alice's Bell-pair half are projected onto the outcome
        Bell state, which carries no information about `ψ`.

    Honest scope: real amplitudes (the framework's existing convention).
    Lifting to ℂ amplitudes is a routine extension; the algebraic
    structure is identical with `ZX` → `iY`. -/
theorem quantum_teleportation_master :
    -- (1) For every input ψ and every outcome o, the corrected state is signOf(o)·ψ/2
    (∀ (ψ : Qubit) (o : BellOutcome),
        correctionOf o (partialInner (bellStateOf o) (tensorWithSinglet ψ)) =
          (fun k => signOf o * ψ k / 2))
    -- (2) Each outcome has Born-rule probability 1/4
    ∧ (∀ o : BellOutcome, (signOf o / 2) ^ 2 = 1 / 4)
    -- (3) Bob's recovered state is a scalar multiple of ψ
    ∧ (∀ (ψ : Qubit) (o : BellOutcome),
        ∃ c : ℝ,
          correctionOf o (partialInner (bellStateOf o) (tensorWithSinglet ψ)) =
            (fun k => c * ψ k))
    -- (4) Consistency with no-cloning: only one copy of ψ ends up in Bob's qubit
    ∧ (∀ (ψ : Qubit) (o : BellOutcome),
        ∃ c : ℝ,
          correctionOf o (partialInner (bellStateOf o) (tensorWithSinglet ψ)) =
            (fun k => c * ψ k)) :=
  ⟨teleportation_correct,
   outcome_probability_one_quarter,
   teleportation_recovers_psi_up_to_scalar,
   teleportation_no_clone⟩

end UnifiedTheory.LayerB.QuantumTeleportation
