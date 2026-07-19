/-
  LayerB/TeleportationFidelity.lean — Operational fidelity bounds for
                                       qubit teleportation
                                       (Massar–Popescu 1995, real-amplitude
                                        4-state version)

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED

  Massar and Popescu (1995) — and in the modern density-matrix
  formulation Horodecki–Horodecki–Horodecki (1999) — showed that the
  average fidelity any classical "measure-and-prepare" strategy can
  achieve in transmitting an unknown qubit is bounded:

      F̄_classical ≤ 2/3

  while the quantum teleportation protocol with the singlet achieves
  perfect transmission F̄ = 1.  Entanglement is the operational
  resource that breaks the classical fidelity ceiling.

  The general 2/3 bound is averaged over the Haar measure on pure
  qubits, which requires non-trivial measure theory in Lean.  This
  file ships the **honest discrete scope** using the four BB84
  (real-amplitude) states `{|0⟩, |1⟩, |+⟩, |−⟩}`:

      F̄_4state := (1/4) · Σ_{i = 1..4} ⟨ψᵢ | Bob_out(ψᵢ) ⟩²

  Key results (all unconditional, zero sorry, zero custom axiom):

  (1) `bb84_avg_fidelity_const_le_half`
      Any **constant** classical strategy `f ≡ c` (the limiting case
      of "0-bit classical communication" — Bob produces the same
      state regardless of any classical message) achieves at most
      `F̄ ≤ 1/2` over the four BB84 states.

  (2) `bb84_avg_fidelity_singlet_eq_one`
      Singlet-based teleportation achieves `F̄ = 1` over the four
      BB84 states in **every** Bell-measurement branch.  The
      renormalized recovered state is exactly `±ψ`, and the squared
      inner product is `1`.

  (3) `entanglement_beats_classical_fidelity`
      Combining (1) and (2): the singlet's quantum-teleportation
      fidelity strictly exceeds the constant-classical bound.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPING

  – Following the framework convention (`QuantumTeleportation.lean`,
    `BellTheorem.lean`, `Entanglement.lean`, `NoCloning.lean`), we
    use **real** single-qubit amplitudes `Fin 2 → ℝ`.

  – The general Haar-averaged 2/3 bound requires:
      (a) an honest Haar measure on the qubit Bloch sphere,
      (b) a characterization of all measure-and-prepare channels,
      (c) integration against the Haar measure,
    each of which is a multi-week formalization in Mathlib.  The
    4-BB84 average is the discrete analog and captures the same
    operational content: a *finite* probe of the teleportation
    channel beats the cleanest classical-without-entanglement baseline.

  – The constant-strategy bound `1/2` is tight for "0-bit" classical
    strategies (Bob has no information about ψ at all).  The
    standard 1-bit "measure in computational basis, prepare the
    outcome" strategy attains the better bound `3/4` on the same
    4 BB84 states, by a longer case analysis on the measurement
    basis; we leave that strengthening to future work.

  – The quantum bound `F̄ = 1` lands in **every** Bell-measurement
    branch (the protocol of `QuantumTeleportation.lean` is correct
    in every branch).

  Zero sorry. Zero custom axioms.
-/
import UnifiedTheory.LayerB.QuantumTeleportation

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.TeleportationFidelity

open UnifiedTheory.LayerB.BellTheorem
open UnifiedTheory.LayerB.QuantumEntanglement
open UnifiedTheory.LayerB.QuantumTeleportation

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE FOUR BB84 REAL-AMPLITUDE STATES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The four real-amplitude BB84 states are:

        |0⟩ = (1, 0)                    (computational basis up)
        |1⟩ = (0, 1)                    (computational basis down)
        |+⟩ = (1/√2,  1/√2)             (Hadamard basis up)
        |−⟩ = (1/√2, -1/√2)             (Hadamard basis down)

    Each is normalized: α² + β² = 1.  The four states come in two
    mutually unbiased pairs:  {|0⟩, |1⟩}  and  {|+⟩, |−⟩}.
    The cross-basis inner products all have squared value 1/2.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The four BB84 real-amplitude single-qubit states, indexed by
    `Fin 4`:
      0 → |0⟩,  1 → |1⟩,  2 → |+⟩,  3 → |−⟩. -/
noncomputable def bb84States : Fin 4 → Qubit
  | 0 => mkQubit 1 0
  | 1 => mkQubit 0 1
  | 2 => mkQubit (1 / Real.sqrt 2) (1 / Real.sqrt 2)
  | 3 => mkQubit (1 / Real.sqrt 2) (-(1 / Real.sqrt 2))

@[simp] theorem bb84States_0_zero : bb84States 0 0 = 1 := by
  unfold bb84States; simp
@[simp] theorem bb84States_0_one : bb84States 0 1 = 0 := by
  unfold bb84States; simp
@[simp] theorem bb84States_1_zero : bb84States 1 0 = 0 := by
  unfold bb84States; simp
@[simp] theorem bb84States_1_one : bb84States 1 1 = 1 := by
  unfold bb84States; simp
@[simp] theorem bb84States_2_zero : bb84States 2 0 = 1 / Real.sqrt 2 := by
  unfold bb84States; simp
@[simp] theorem bb84States_2_one : bb84States 2 1 = 1 / Real.sqrt 2 := by
  unfold bb84States; simp
@[simp] theorem bb84States_3_zero : bb84States 3 0 = 1 / Real.sqrt 2 := by
  unfold bb84States; simp
@[simp] theorem bb84States_3_one : bb84States 3 1 = -(1 / Real.sqrt 2) := by
  unfold bb84States; simp

/-- `√2 · √2 = 2`. -/
private lemma sqrt_two_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 := by
  have := Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)
  rw [sq] at this; exact this

/-- `(1 / √2) ^ 2 = 1/2`. -/
private lemma inv_sqrt_two_sq : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
  rw [div_pow, one_pow, sq, sqrt_two_mul_self]

/-- `(-(1 / √2)) ^ 2 = 1/2`. -/
private lemma neg_inv_sqrt_two_sq : (-(1 / Real.sqrt 2)) ^ 2 = 1 / 2 := by
  rw [neg_pow]; simp

/-- Each BB84 state is normalized: `ψ(0)² + ψ(1)² = 1`. -/
theorem bb84States_normalized (i : Fin 4) :
    bb84States i 0 ^ 2 + bb84States i 1 ^ 2 = 1 := by
  fin_cases i <;> simp <;> norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: SINGLE-QUBIT INNER PRODUCT AND FIDELITY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The single-qubit inner product is just the dot product on
    `Fin 2 → ℝ`.  The fidelity between two normalized qubits is
    `|⟨ψ|φ⟩|²`, which on real amplitudes is `(ψ₀φ₀ + ψ₁φ₁)²`.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The real single-qubit inner product. -/
def qubitInner (ψ φ : Qubit) : ℝ := ψ 0 * φ 0 + ψ 1 * φ 1

@[simp] theorem qubitInner_self (ψ : Qubit) :
    qubitInner ψ ψ = ψ 0 ^ 2 + ψ 1 ^ 2 := by
  unfold qubitInner; ring

/-- The single-qubit fidelity `|⟨ψ|φ⟩|²` between two real qubits. -/
def qubitFidelity (ψ φ : Qubit) : ℝ := (qubitInner ψ φ) ^ 2

@[simp] theorem qubitFidelity_normalized (ψ : Qubit)
    (hψ : ψ 0 ^ 2 + ψ 1 ^ 2 = 1) :
    qubitFidelity ψ ψ = 1 := by
  unfold qubitFidelity; rw [qubitInner_self]; rw [hψ]; ring

/-- Fidelity is symmetric. -/
theorem qubitFidelity_comm (ψ φ : Qubit) :
    qubitFidelity ψ φ = qubitFidelity φ ψ := by
  unfold qubitFidelity qubitInner; ring

/-! Fidelity is between 0 and 1 for the BB84 states paired against
    any normalized qubit — we only need the special cases below. -/

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: THE BB84 AVERAGE FIDELITY OF A STRATEGY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A classical strategy is, in the most general form, a probabilistic
    measure-and-prepare channel `Qubit → Qubit` (mixing over a finite
    family of outputs).  At the simplest deterministic level it is
    just a function.  We define the BB84 average fidelity for any
    such function.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The BB84 average fidelity of a strategy `f : Qubit → Qubit`,
    averaged uniformly over the four BB84 input states. -/
noncomputable def bb84AvgFidelity (f : Qubit → Qubit) : ℝ :=
  (1 / 4) * ∑ i : Fin 4, qubitFidelity (bb84States i) (f (bb84States i))

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: THE CLASSICAL BOUND FOR CONSTANT STRATEGIES (0-BIT)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A **constant** classical strategy outputs the same qubit `c`
    regardless of the input.  This is the limiting "0-bit" classical
    strategy: Bob receives no information about ψ from Alice.  We
    prove that this achieves at most `F̄ = 1/2` averaged over the
    four BB84 states.

    The proof:  Σ_i ⟨ψᵢ|c⟩² for the four BB84 states ψᵢ equals
    `(c₀)² + (c₁)² + (c₀ + c₁)²/2 + (c₀ − c₁)²/2`
    = `2·(c₀² + c₁²)`.  Hence the average is `(c₀² + c₁²) / 2`.
    For a normalized output `c₀² + c₁² = 1`, the average is exactly
    `1/2`; for an unnormalized output the bound still holds because
    `(c₀² + c₁²) ≤ 1` is the constraint Bob's local preparation
    must satisfy (Bob's output is a single-qubit pure state).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The sum Σ ⟨ψᵢ|c⟩² over the 4 BB84 states equals
    `2·(c₀² + c₁²)`. -/
theorem bb84_sum_fidelity_const (c : Qubit) :
    ∑ i : Fin 4, qubitFidelity (bb84States i) c
      = 2 * (c 0 ^ 2 + c 1 ^ 2) := by
  rw [show (Finset.univ : Finset (Fin 4))
        = {0, 1, 2, 3} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  unfold qubitFidelity qubitInner
  simp only [Fin.isValue, bb84States_0_zero, one_mul, bb84States_0_one, zero_mul,
    add_zero, bb84States_1_zero, bb84States_1_one, zero_add, bb84States_2_zero,
    one_div, bb84States_2_one, bb84States_3_zero, bb84States_3_one, neg_mul]
  have hk : Real.sqrt 2 * Real.sqrt 2 = 2 := sqrt_two_mul_self
  field_simp
  ring_nf
  have hk2 : (Real.sqrt 2) ^ 2 = 2 := by rw [sq]; exact hk
  nlinarith [hk, hk2, sq_nonneg (c 0), sq_nonneg (c 1)]

/-- **CLASSICAL CONSTANT-STRATEGY FIDELITY BOUND**:  any constant
    classical strategy `f ≡ c` whose output `c` is a normalized qubit
    achieves at most `1/2` average fidelity over the four BB84
    states.  This is the limit of "0-bit classical communication" —
    Bob has no information about Alice's input qubit, only her
    pre-agreed choice of output. -/
theorem bb84_avg_fidelity_const_le_half (c : Qubit)
    (hc : c 0 ^ 2 + c 1 ^ 2 = 1) :
    bb84AvgFidelity (fun _ => c) ≤ 1 / 2 := by
  unfold bb84AvgFidelity
  rw [bb84_sum_fidelity_const c]
  rw [hc]
  norm_num

/-- **CLASSICAL CONSTANT-STRATEGY FIDELITY EQUALITY**:  any
    normalized constant strategy actually *achieves* exactly `1/2`
    average fidelity.  Hence the `1/2` bound is *tight* for constant
    strategies. -/
theorem bb84_avg_fidelity_const_eq_half (c : Qubit)
    (hc : c 0 ^ 2 + c 1 ^ 2 = 1) :
    bb84AvgFidelity (fun _ => c) = 1 / 2 := by
  unfold bb84AvgFidelity
  rw [bb84_sum_fidelity_const c, hc]
  norm_num

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: SINGLET TELEPORTATION ACHIEVES F̄ = 1 ON THE 4 BB84 STATES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The quantum-teleportation theorem in `QuantumTeleportation.lean`
    gives, for every input ψ and every Bell outcome o, Bob's
    corrected state as `signOf(o) · ψ k / 2`.  The unnormalized
    inner product of this with ψ is `signOf(o) · ‖ψ‖² / 2`, and the
    squared value is `‖ψ‖⁴ / 4 = 1/4` for normalized ψ.

    To turn this into a **fidelity = 1** statement we must
    renormalize Bob's output by the (Born-rule) prefactor `1/2`.
    The renormalized output is `signOf(o) · ψ`, whose fidelity with
    ψ is exactly `(±‖ψ‖²)² = 1`.

    We define the **renormalized branch strategy** that takes an
    input ψ, runs the protocol, and outputs the renormalized
    corrected state.  Average BB84 fidelity is then 1 in every
    branch.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The renormalized output of the singlet-teleportation protocol
    in Bell-measurement branch `o`.  The Born-rule prefactor `1/2`
    is undone, leaving Bob with `signOf(o) · ψ`. -/
noncomputable def singletTeleportationOutput (o : BellOutcome) (ψ : Qubit) : Qubit :=
  fun k => signOf o * ψ k

/-- In every Bell-measurement branch `o`, the renormalized
    teleportation output `signOf(o)·ψ` has perfect single-qubit
    fidelity with the input `ψ`, provided `ψ` is normalized. -/
theorem singletTeleportationOutput_fidelity_eq_one
    (o : BellOutcome) (ψ : Qubit)
    (hψ : ψ 0 ^ 2 + ψ 1 ^ 2 = 1) :
    qubitFidelity ψ (singletTeleportationOutput o ψ) = 1 := by
  unfold qubitFidelity qubitInner singletTeleportationOutput
  have hsign : signOf o ^ 2 = 1 := by
    cases o <;> (unfold signOf; norm_num)
  have hnorm : ψ 0 * (signOf o * ψ 0) + ψ 1 * (signOf o * ψ 1)
              = signOf o * (ψ 0 ^ 2 + ψ 1 ^ 2) := by ring
  rw [hnorm, hψ, mul_one]
  exact hsign

/-- **QUANTUM SINGLET-TELEPORTATION FIDELITY = 1 ON BB84**:
    in every Bell-measurement branch `o`, the renormalized
    singlet-teleportation protocol achieves perfect average fidelity
    over the four BB84 states. -/
theorem bb84_avg_fidelity_singlet_eq_one (o : BellOutcome) :
    bb84AvgFidelity (singletTeleportationOutput o) = 1 := by
  unfold bb84AvgFidelity
  have h_each : ∀ i : Fin 4,
      qubitFidelity (bb84States i) (singletTeleportationOutput o (bb84States i)) = 1 := by
    intro i
    exact singletTeleportationOutput_fidelity_eq_one o _ (bb84States_normalized i)
  rw [show (Finset.univ : Finset (Fin 4))
        = {0, 1, 2, 3} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [h_each 0, h_each 1, h_each 2, h_each 3]
  norm_num

/-- **Reformulation via the protocol primitives.**  Bob's corrected
    state for input ψ and branch o is
    `correctionOf o (partialInner (bellStateOf o) (tensorWithSinglet ψ))`,
    which equals `signOf(o) · ψ k / 2`.  The renormalized output
    `singletTeleportationOutput o ψ` is `signOf(o) · ψ`, i.e., the
    raw corrected state scaled by `2`.  Hence the renormalized
    strategy used in `bb84_avg_fidelity_singlet_eq_one` is the same
    as `2 · (Bob's corrected output)`, which is the standard
    re-normalization of the Born-rule branch state. -/
theorem singletTeleportationOutput_via_protocol
    (ψ : Qubit) (o : BellOutcome) :
    singletTeleportationOutput o ψ =
      (fun k => 2 * (correctionOf o
        (partialInner (bellStateOf o) (tensorWithSinglet ψ)) k)) := by
  funext k
  unfold singletTeleportationOutput
  have h := congr_fun (teleportation_correct ψ o) k
  rw [h]
  ring

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6: OPERATIONAL ENTANGLEMENT WITNESS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Combining Part 4 and Part 5:
       constant-classical strategies:  F̄ ≤ 1/2
       singlet-quantum teleportation:  F̄ = 1
    Hence entanglement (the shared singlet) is the operational
    resource that lifts the classical fidelity ceiling.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **OPERATIONAL ENTANGLEMENT WITNESS**: the singlet's
    teleportation fidelity over the four BB84 states (`1`) strictly
    exceeds any constant-classical strategy bound (`1/2`).  Hence
    entanglement is an operational resource: it enables strictly
    higher transmission fidelity than any 0-bit classical strategy.

    *Stronger* classical bounds (e.g., the standard 1-bit
    measure-and-prepare 3/4 bound, or the Haar-averaged 2/3 bound)
    would tighten the gap but the qualitative conclusion is the
    same:  classical strategies are *strictly bounded* away from
    fidelity 1, while the singlet teleportation attains 1 exactly. -/
theorem entanglement_beats_classical_fidelity
    (c : Qubit) (hc : c 0 ^ 2 + c 1 ^ 2 = 1)
    (o : BellOutcome) :
    bb84AvgFidelity (fun _ => c) < bb84AvgFidelity (singletTeleportationOutput o) := by
  rw [bb84_avg_fidelity_const_eq_half c hc,
      bb84_avg_fidelity_singlet_eq_one o]
  norm_num

/-- **HEADLINE — MASSAR–POPESCU IN DISCRETE FORM (real amplitudes,
    4 BB84 states):**

    (1) Any constant (0-bit classical) strategy achieves at most
        `F̄ ≤ 1/2` average fidelity over the 4 BB84 inputs, with
        equality when the constant output is normalized.

    (2) Singlet-based quantum teleportation achieves exactly
        `F̄ = 1` over the 4 BB84 inputs in every Bell-measurement
        branch.

    (3) Hence the quantum (singlet) protocol strictly beats the
        constant-classical baseline, giving an *operational*
        meaning to entanglement: it is the resource that lifts
        the classical fidelity ceiling.

    Honest scope: 4 BB84 real-amplitude states (not full Haar),
    constant classical strategies (not full measure-and-prepare).
    These restrictions match the framework's existing real-amplitude
    LayerB scope.  The qualitative inequality `classical < quantum`
    is unconditional on the choice of inputs and on the choice of
    Bell-measurement branch. -/
theorem teleportation_fidelity_master :
    (∀ c : Qubit, c 0 ^ 2 + c 1 ^ 2 = 1 →
        bb84AvgFidelity (fun _ => c) = 1 / 2)
    ∧ (∀ o : BellOutcome,
        bb84AvgFidelity (singletTeleportationOutput o) = 1)
    ∧ (∀ (c : Qubit) (_hc : c 0 ^ 2 + c 1 ^ 2 = 1) (o : BellOutcome),
        bb84AvgFidelity (fun _ => c) < bb84AvgFidelity (singletTeleportationOutput o)) :=
  ⟨bb84_avg_fidelity_const_eq_half,
   bb84_avg_fidelity_singlet_eq_one,
   fun c hc o => entanglement_beats_classical_fidelity c hc o⟩

end UnifiedTheory.LayerB.TeleportationFidelity
