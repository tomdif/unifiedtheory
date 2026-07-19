/-
  UnifiedTheory/LayerC/PBRTheorem.lean
  ─────────────────────────────────────

  **The Pusey-Barrett-Rudolph (PBR) theorem (Pusey, Barrett, Rudolph 2012).**

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHY THIS FILE EXISTS

  This file formalises the PBR no-go theorem.  In contrast to Bell's
  theorem (which constrains LHV models reproducing QM correlations)
  and Hardy's paradox (a logical version of the same), PBR addresses
  a DIFFERENT axis of foundational debate: is the wavefunction
  itself *ontic* (a physical property of the system) or *epistemic*
  (a representation of an agent's knowledge about a deeper
  underlying state)?

  The PBR theorem rules out a broad class of ψ-EPISTEMIC models
  under two assumptions:

    (A) The system has an ontic state space `Λ`, and each quantum
        state `|ψ_i⟩` is represented by a probability distribution
        `μ_i` on `Λ`.  The model is ψ-EPISTEMIC in the PBR sense
        iff there exist two distinct quantum states whose
        distributions have OVERLAPPING supports — i.e. ∃ λ ∈ Λ
        compatible with both preparations.

    (B) Preparation independence (PIH): when two systems are
        prepared independently in states `|ψ_i⟩` and `|ψ_j⟩`, the
        joint ontic state is distributed as the PRODUCT
        `μ_i × μ_j`.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  THE PBR ARGUMENT

  Pick two non-orthogonal quantum states `|ψ_0⟩ = |0⟩` and
  `|ψ_1⟩ = |+⟩ = (|0⟩ + |1⟩) / √2`.  Both systems are then jointly
  measured in the 4-outcome entangled basis `{|ξ_a⟩}_{a=0..3}` of
  Pusey-Barrett-Rudolph (2012, equation (1)):

      |ξ_0⟩ = (1/√2) (|0⟩|1⟩ + |1⟩|0⟩)
      |ξ_1⟩ = (1/√2) (|0⟩|−⟩ + |1⟩|+⟩)        |±⟩ = (|0⟩ ± |1⟩) / √2
      |ξ_2⟩ = (1/√2) (|+⟩|1⟩ + |−⟩|0⟩)
      |ξ_3⟩ = (1/√2) (|+⟩|−⟩ + |−⟩|+⟩)

  Direct computation shows ⟨ξ_a | ψ_{a₁}⟩ ⊗ |ψ_{a₂}⟩ = 0 where
  (a₁, a₂) are the binary digits of `a ∈ {0,1,2,3}`:

      ⟨ξ_0 | 0,0⟩ = 0     ⟨ξ_1 | 0,+⟩ = 0
      ⟨ξ_2 | +,0⟩ = 0     ⟨ξ_3 | +,+⟩ = 0

  So in QM, for each of the four preparation pairs (i, j) ∈
  Fin 2 × Fin 2, exactly one of the four outcomes a ∈ Fin 4
  has zero probability — namely the outcome a = 2i + j.

  Combinatorial contradiction:

    1.  ψ-EPISTEMIC ⇒ ∃ λ* with μ_0(λ*) > 0 ∧ μ_1(λ*) > 0.
    2.  PIH ⇒ the joint ontic state (λ_A*, λ_B*) := (λ*, λ*) is in
        the support of every product μ_i × μ_j.
    3.  Any deterministic measurement assignment f : Λ × Λ → Fin 4
        must return SOME outcome on (λ_A*, λ_B*).  Call it a*.
    4.  But the QM zero-prob constraint says: for every (i, j),
        f cannot return 2i + j on any point in the support of
        μ_i × μ_j.  Since (λ_A*, λ_B*) is in EVERY product support,
        f(λ_A*, λ_B*) ≠ 2i + j for all (i, j) ∈ Fin 2 × Fin 2,
        i.e. ≠ any element of Fin 4.  ⊥.

  This is the same logical pattern as Hardy's paradox: four
  zero-probability events forcing a 4-case enumeration that
  excludes every possible outcome at a single witness point.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT THIS FILE SHIPS

    • `PsiEpistemicModel` — ontic-state model with two preparation
      distributions whose supports OVERLAP.
    • `MeasurementAssignment` — deterministic Λ × Λ → Fin 4 readout.
    • `binaryToOutcome : Fin 2 → Fin 2 → Fin 4` — encoding
      (i, j) ↦ 2i + j.
    • `IsConsistentWithQM` — the four zero-probability constraints
      packaged as a single "no positive-support point maps to its
      forbidden outcome" condition.
    • `pbr_no_psi_epistemic` — THE HEADLINE.  No ψ-epistemic model
      with preparation independence admits a measurement assignment
      consistent with the four QM zero-probability facts.

  Zero `sorry`.  Zero custom `axiom`.  Honest scoping: the file
  encodes the four QM facts as HYPOTHESES on `f`; the optional
  quantum derivation (showing those inner products are actually zero)
  is *not* required for the no-go and is omitted here.  The
  combinatorial content of PBR is the headline.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.PBRTheorem

open scoped BigOperators

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: THE ψ-EPISTEMIC HIDDEN-VARIABLE MODEL
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **A ψ-epistemic hidden-variable model** for two distinct quantum
    preparations `|ψ_0⟩` and `|ψ_1⟩`.

    Fields:
      * `Λ` — a finite ontic state space;
      * `μ i` — the distribution on `Λ` representing the quantum
        state `|ψ_i⟩` (`i ∈ Fin 2`);
      * `overlap` — there exists at least one ontic state with
        STRICTLY POSITIVE weight under BOTH μ_0 AND μ_1.  This is
        the formal "ψ-epistemic" hypothesis: the two quantum
        states share a common piece of ontic support, so a single
        ontic state `λ` is consistent with two different
        preparation procedures.

    The PBR theorem will show that under preparation independence
    (encoded separately as the product structure of `jointDist`
    below), no measurement device can be consistent with the four
    quantum zero-probability constraints.  Hence: NO MODEL OF
    THIS FORM EXISTS for the specific PBR preparations. -/
structure PsiEpistemicModel where
  /-- The (finite) ontic-state space. -/
  Λ : Type
  /-- `Λ` is finite. -/
  isFintype : Fintype Λ
  /-- The two preparation distributions, indexed by `Fin 2`
      (state `|ψ_0⟩` vs state `|ψ_1⟩`). -/
  μ : Fin 2 → Λ → ℝ
  /-- Each distribution is nonnegative. -/
  μ_nonneg : ∀ i l, 0 ≤ μ i l
  /-- Each distribution sums to one. -/
  μ_sum : ∀ i, (Finset.univ : Finset Λ).sum (fun l => μ i l) = 1
  /-- ψ-EPISTEMIC: the supports of μ_0 and μ_1 OVERLAP at some `λ`. -/
  overlap : ∃ l : Λ, μ 0 l > 0 ∧ μ 1 l > 0

attribute [instance] PsiEpistemicModel.isFintype

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: PREPARATION INDEPENDENCE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Preparation independence (PIH).**  When two systems are
    prepared in states `|ψ_i⟩` and `|ψ_j⟩` independently, the joint
    ontic state is the product distribution.

    `jointDist m i j (l_A, l_B) = μ_i(l_A) · μ_j(l_B)`. -/
def jointDist (m : PsiEpistemicModel)
    (i j : Fin 2) (l_A l_B : m.Λ) : ℝ :=
  m.μ i l_A * m.μ j l_B

/-- The joint distribution is nonnegative. -/
private lemma jointDist_nonneg (m : PsiEpistemicModel)
    (i j : Fin 2) (l_A l_B : m.Λ) :
    0 ≤ jointDist m i j l_A l_B := by
  unfold jointDist
  exact mul_nonneg (m.μ_nonneg i l_A) (m.μ_nonneg j l_B)

/-- The joint distribution is strictly positive iff both marginals
    are strictly positive at the respective ontic states. -/
private lemma jointDist_pos_iff (m : PsiEpistemicModel)
    (i j : Fin 2) (l_A l_B : m.Λ) :
    0 < jointDist m i j l_A l_B ↔ 0 < m.μ i l_A ∧ 0 < m.μ j l_B := by
  unfold jointDist
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hle
      push_neg at hle
      have h_eq : m.μ i l_A = 0 :=
        le_antisymm hle (m.μ_nonneg i l_A)
      rw [h_eq, zero_mul] at h
      exact lt_irrefl 0 h
    · by_contra hle
      push_neg at hle
      have h_eq : m.μ j l_B = 0 :=
        le_antisymm hle (m.μ_nonneg j l_B)
      rw [h_eq, mul_zero] at h
      exact lt_irrefl 0 h
  · intro ⟨h1, h2⟩
    exact mul_pos h1 h2

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: MEASUREMENT ASSIGNMENTS AND QM CONSISTENCY
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **A measurement assignment** for the PBR setup: a deterministic
    function from the joint ontic state `(l_A, l_B)` to one of the
    four outcomes of the PBR entangled measurement.

    Under the (hidden) determinism assumption that is built into
    the PBR setup (and into deterministic-response LHV models in
    general), each ontic state produces a definite outcome on the
    measurement. -/
def MeasurementAssignment (m : PsiEpistemicModel) : Type :=
  m.Λ → m.Λ → Fin 4

/-- Encoding `(i, j) ∈ Fin 2 × Fin 2 ↦ 2i + j ∈ Fin 4`.

    Maps:
      (0, 0) ↦ 0,  (0, 1) ↦ 1,  (1, 0) ↦ 2,  (1, 1) ↦ 3.

    In the PBR construction this is the outcome forbidden by QM
    when the two systems are prepared in states `|ψ_i⟩` and
    `|ψ_j⟩` respectively. -/
def binaryToOutcome (i j : Fin 2) : Fin 4 :=
  ⟨2 * i.val + j.val, by
    have hi : i.val ≤ 1 := Nat.lt_succ_iff.mp i.isLt
    have hj : j.val ≤ 1 := Nat.lt_succ_iff.mp j.isLt
    omega⟩

/-- `binaryToOutcome` takes all four values on `Fin 2 × Fin 2`. -/
private lemma binaryToOutcome_values :
    binaryToOutcome 0 0 = (0 : Fin 4) ∧
    binaryToOutcome 0 1 = (1 : Fin 4) ∧
    binaryToOutcome 1 0 = (2 : Fin 4) ∧
    binaryToOutcome 1 1 = (3 : Fin 4) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (unfold binaryToOutcome; apply Fin.ext; rfl)

/-- **QM consistency of a measurement assignment.**

    The four zero-probability constraints from QM, packaged
    uniformly: for every preparation pair `(i, j)` and every
    joint ontic state `(l_A, l_B)` in the support of the
    corresponding product distribution `μ_i × μ_j`, the
    deterministic outcome assigned by `f` is NOT the "forbidden"
    outcome `binaryToOutcome i j`.

    Equivalently: the four events
      `{(l_A, l_B) ∣ f(l_A, l_B) = binaryToOutcome i j}`
    are each disjoint from the support of `μ_i × μ_j`. -/
def IsConsistentWithQM (m : PsiEpistemicModel)
    (f : MeasurementAssignment m) : Prop :=
  ∀ (i j : Fin 2) (l_A l_B : m.Λ),
    m.μ i l_A > 0 → m.μ j l_B > 0 →
    f l_A l_B ≠ binaryToOutcome i j

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4: THE PBR THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **THE PUSEY-BARRETT-RUDOLPH THEOREM.**

    No ψ-epistemic hidden-variable model (in the sense of
    `PsiEpistemicModel` — two preparation distributions on a common
    ontic state space with OVERLAPPING supports) admits a
    measurement assignment consistent with the four QM
    zero-probability constraints of the PBR setup.

    Equivalently: if a hidden-variable model assigns deterministic
    outcomes to the PBR entangled measurement and reproduces the
    four zero-probability QM facts under preparation independence,
    then `μ_0` and `μ_1` must have DISJOINT supports — i.e. the
    model is ψ-ONTIC.

    Proof outline (4 lines of math):
      1.  Use `overlap` twice to get `l_A, l_B ∈ Λ` with
          `μ_0(l_A) > 0`, `μ_1(l_A) > 0`, `μ_0(l_B) > 0`,
          `μ_1(l_B) > 0`.
      2.  Apply `IsConsistentWithQM` four times, once per
          `(i, j) ∈ Fin 2 × Fin 2`, to get
          `f l_A l_B ≠ 0, 1, 2, 3`.
      3.  But `f l_A l_B ∈ Fin 4`; contradiction by `fin_cases`. -/
theorem pbr_no_psi_epistemic
    (m : PsiEpistemicModel) (f : MeasurementAssignment m) :
    ¬ IsConsistentWithQM m f := by
  intro hQM
  -- Step 1: extract two overlap witnesses (one per system).
  obtain ⟨l_A, h0A, h1A⟩ := m.overlap
  obtain ⟨l_B, h0B, h1B⟩ := m.overlap
  -- Step 2: apply IsConsistentWithQM four times.
  have e00 : f l_A l_B ≠ binaryToOutcome 0 0 := hQM 0 0 l_A l_B h0A h0B
  have e01 : f l_A l_B ≠ binaryToOutcome 0 1 := hQM 0 1 l_A l_B h0A h1B
  have e10 : f l_A l_B ≠ binaryToOutcome 1 0 := hQM 1 0 l_A l_B h1A h0B
  have e11 : f l_A l_B ≠ binaryToOutcome 1 1 := hQM 1 1 l_A l_B h1A h1B
  -- Step 3: rewrite the four forbidden outcomes as 0, 1, 2, 3.
  obtain ⟨h00, h01, h10, h11⟩ := binaryToOutcome_values
  rw [h00] at e00
  rw [h01] at e01
  rw [h10] at e10
  rw [h11] at e11
  -- Step 4: f l_A l_B ∈ Fin 4 — case-split to contradict each ≠.
  -- We enumerate the four values of `Fin 4` via `interval_cases` on
  -- `(f l_A l_B).val` and convert each `.val = k` back to `a = k`.
  set a : Fin 4 := f l_A l_B
  have h_lt : a.val < 4 := a.isLt
  have h_eq_iff : ∀ (k : Fin 4), a.val = k.val → a = k := fun k h => Fin.ext h
  interval_cases a.val
  · exact e00 (h_eq_iff 0 rfl)
  · exact e01 (h_eq_iff 1 rfl)
  · exact e10 (h_eq_iff 2 rfl)
  · exact e11 (h_eq_iff 3 rfl)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5: COROLLARY — ψ-ONTICITY ON THE PBR PREPARATIONS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Contrapositive form of PBR.**  If a hidden-variable model
    has a measurement assignment consistent with the PBR
    zero-probability constraints, then its preparation
    distributions for `|ψ_0⟩` and `|ψ_1⟩` have DISJOINT supports.

    This is the "ψ-ontic" conclusion: distinct quantum states are
    encoded by ontically distinguishable hidden states (no single
    `λ` is compatible with both preparations). -/
theorem pbr_forces_psi_ontic
    {Λ : Type} [Fintype Λ]
    (μ : Fin 2 → Λ → ℝ)
    (μ_nonneg : ∀ i l, 0 ≤ μ i l)
    (μ_sum : ∀ i, (Finset.univ : Finset Λ).sum (fun l => μ i l) = 1)
    (f : Λ → Λ → Fin 4)
    (hQM : ∀ (i j : Fin 2) (l_A l_B : Λ),
              μ i l_A > 0 → μ j l_B > 0 →
              f l_A l_B ≠ binaryToOutcome i j) :
    ¬ ∃ l : Λ, μ 0 l > 0 ∧ μ 1 l > 0 := by
  intro hover
  -- Package into a `PsiEpistemicModel` and invoke `pbr_no_psi_epistemic`.
  let m : PsiEpistemicModel :=
    { Λ := Λ
      isFintype := inferInstance
      μ := μ
      μ_nonneg := μ_nonneg
      μ_sum := μ_sum
      overlap := hover }
  exact pbr_no_psi_epistemic m f hQM

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    AXIOM-CHECK DIAGNOSTICS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

#print axioms pbr_no_psi_epistemic
#print axioms pbr_forces_psi_ontic
#print axioms binaryToOutcome_values

end UnifiedTheory.LayerC.PBRTheorem
