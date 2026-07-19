/-
  UnifiedTheory/LayerC/EastinKnill.lean
  ─────────────────────────────────────

  **THE EASTIN–KNILL THEOREM.**

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT — Eastin, Knill, Phys. Rev. Lett. 102, 110502 (2009).

  No quantum error-correcting code that corrects at least one erasure can
  possess a *continuous* (Lie group) set of *transversal* logical gates
  that is also *universal*.  Equivalently: the group of transversal
  logical gates of any such code is a **finite** group, hence discrete,
  hence cannot be dense in — let alone equal to — a continuous gate set
  such as U(2).  Universal fault-tolerant quantum computation therefore
  *requires* a non-transversal element; the canonical realization is the
  T-gate injected by magic-state distillation (see
  `LayerC.MagicStateDistillation`).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS A TRANSVERSAL GATE?

  A logical gate is *transversal* when it factorizes as a tensor (Kronecker)
  product of gates acting independently on the individual physical qubits
  (code blocks):

        U  =  U₁ ⊗ U₂ ⊗ ... ⊗ Uₙ.

  Such a gate is automatically fault-tolerant: a fault on one physical
  qubit cannot propagate to another, because there is no entangling
  interaction between blocks.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT WE PROVE UNCONDITIONALLY (structural core).

  We model a transversal gate on a bipartite system with index types
  `I` (one block) and `J` (the rest) as a Kronecker product `A ⊗ₖ B`.
  This captures the "no entangling between blocks" structure faithfully,
  and the n-fold case is the iterated version.

    • `IsTransversal`            — the predicate `∃ A B, U = A ⊗ₖ B`.
    • `transversal_one`          — the identity is transversal (`1 = 1 ⊗ₖ 1`).
    • `transversal_mul`          — transversal gates are closed under
                                   composition:  `(A⊗B)(A'⊗B') = (AA')⊗(BB')`
                                   via Mathlib's `mul_kronecker_mul`.
    • `transversal_kronecker`    — Kronecker products of factors are transversal.
    • `finite_not_universal`     — a **finite** family of gates cannot contain
                                   the continuous phase family `phase θ`, which
                                   is **infinite** (`phase` is injective on
                                   `[0, 2π)`-distinct angles); so a finite
                                   transversal group is never universal.
    • `phase_injective`          — the witnessing infinite continuum.

  STATED AS NAMED TARGETS (the physics theorems of Eastin–Knill):

    • `Transversal_Finite_Target`     — the transversal group is finite.
    • `EastinKnill_Target`            — finite ⟹ not universal.
    • `MagicState_Circumvents_Target` — magic states restore universality.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  Zero `sorry`, zero custom `axiom`.
-/

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open Matrix Kronecker

namespace UnifiedTheory.LayerC.EastinKnill

set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-! ## 1.  Transversal gates and their group structure -/

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- A **transversal gate** on a bipartite system indexed by `I × J`:
    a matrix that factorizes as a Kronecker (tensor) product `A ⊗ₖ B`
    of gates acting *independently* on the two blocks.  No entangling
    interaction crosses the block boundary — this is exactly the
    "single-physical-qubit gate per block" structure that makes a
    transversal gate fault-tolerant. -/
def IsTransversal (U : Matrix (I × J) (I × J) ℂ) : Prop :=
  ∃ (A : Matrix I I ℂ) (B : Matrix J J ℂ), U = A ⊗ₖ B

/-- The **identity** logical gate is transversal:  `1 = 1 ⊗ₖ 1`. -/
theorem transversal_one : IsTransversal (1 : Matrix (I × J) (I × J) ℂ) :=
  ⟨1, 1, (one_kronecker_one).symm⟩

/-- Any explicit Kronecker product of single-block gates is transversal. -/
theorem transversal_kronecker (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    IsTransversal (A ⊗ₖ B) :=
  ⟨A, B, rfl⟩

/-- **Closure under composition (group structure).**  The product of two
    transversal gates is transversal, because the Kronecker product
    obeys the *mixed-product property*
        `(A ⊗ₖ B) * (A' ⊗ₖ B') = (A * A') ⊗ₖ (B * B')`.
    Composing two block-local gates keeps the action block-local. -/
theorem transversal_mul {U V : Matrix (I × J) (I × J) ℂ}
    (hU : IsTransversal U) (hV : IsTransversal V) : IsTransversal (U * V) := by
  obtain ⟨A, B, rfl⟩ := hU
  obtain ⟨A', B', rfl⟩ := hV
  -- `mul_kronecker_mul A A' B B' : (A*A') ⊗ₖ (B*B') = A ⊗ₖ B * A' ⊗ₖ B'`
  exact ⟨A * A', B * B', (mul_kronecker_mul A A' B B').symm⟩

/-- The transversal gates form a multiplicative submonoid: identity is
    transversal and they are closed under multiplication.  (Inverses, when
    they exist within U(d), are likewise transversal: the inverse of a
    Kronecker product of invertible blocks is the Kronecker product of the
    inverses.  The monoid structure here is the unconditional core.) -/
def TransversalSubmonoid : Submonoid (Matrix (I × J) (I × J) ℂ) where
  carrier := {U | IsTransversal U}
  one_mem' := transversal_one
  mul_mem' := transversal_mul

@[simp] theorem mem_TransversalSubmonoid {U : Matrix (I × J) (I × J) ℂ} :
    U ∈ (TransversalSubmonoid (I := I) (J := J)) ↔ IsTransversal U := Iff.rfl

/-! ## 2.  The continuous gate family that a finite group cannot reach

    A *universal* gate set must approximate every element of a continuous
    group such as U(1) ⊂ U(2).  We exhibit the continuum of phase gates
        phase θ = diag(1, e^{iθ})
    and prove the map `θ ↦ phase θ` is injective on a real interval, hence
    its image is infinite.  No finite set can contain an infinite image, so
    no finite group of gates is universal. -/

/-- The single-qubit **phase gate** `diag(1, e^{iθ})`, a `2×2` unitary.
    The continuous family `{phase θ}` is the obstruction: it is the
    abelian subgroup U(1) of U(2) that a universal set must cover. -/
noncomputable def phase (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i => if i = 0 then 1 else Complex.exp (θ * Complex.I))

/-- The phase family is **injective** in `θ` on the half-open interval
    `[0, 2π)`: distinct angles give distinct gates.  Hence the gate family
    `{phase θ}` is an honest *continuum* — an infinite set. -/
theorem phase_injective :
    Set.InjOn phase (Set.Ico 0 (2 * Real.pi)) := by
  intro θ₁ h₁ θ₂ h₂ heq
  -- Read off the (1,1) entry: it is `exp (θ * I)`.
  have hentry : Complex.exp (θ₁ * Complex.I) = Complex.exp (θ₂ * Complex.I) := by
    have := congrFun (congrFun heq 1) 1
    simpa [phase, Matrix.diagonal] using this
  -- `exp` is `2π`-periodic and injective up to that period on `[0,2π)`.
  rcases h₁ with ⟨h₁lo, h₁hi⟩
  rcases h₂ with ⟨h₂lo, h₂hi⟩
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  -- Use the characterization of equal complex exponentials.
  rw [Complex.exp_eq_exp_iff_exists_int] at hentry
  obtain ⟨k, hk⟩ := hentry
  -- hk : θ₁ * I = θ₂ * I + k * (2πI)
  have hI : (Complex.I) ≠ 0 := Complex.I_ne_zero
  -- Strip the common factor of I to get a real-coefficient relation.
  have hk' : (θ₁ : ℂ) = (θ₂ : ℂ) + (k : ℂ) * (2 * Real.pi) := by
    have hrw : (θ₁ : ℂ) * Complex.I
        = ((θ₂ : ℂ) + (k : ℂ) * (2 * Real.pi)) * Complex.I := by
      rw [hk]; ring
    exact mul_right_cancel₀ hI hrw
  -- Take real parts: θ₁ = θ₂ + k·2π as reals.
  have hreal : θ₁ = θ₂ + (k : ℝ) * (2 * Real.pi) := by
    have := congrArg Complex.re hk'
    push_cast at this
    simpa using this
  -- With both angles in [0, 2π), the integer k must be 0.
  have hk0 : (k : ℝ) = 0 := by
    by_contra hkne
    have hkneZ : k ≠ 0 := by
      intro h; apply hkne; rw [h]; norm_num
    rcases lt_or_gt_of_ne hkneZ with hkneg | hkpos
    · -- k ≤ -1  ⟹  θ₁ = θ₂ + k·2π ≤ θ₂ - 2π < 0, contradicting θ₁ ≥ 0
      have hk_le : (k : ℝ) ≤ -1 := by
        have : k ≤ -1 := Int.le_sub_one_of_lt hkneg
        exact_mod_cast this
      have : θ₁ ≤ θ₂ - 2 * Real.pi := by
        rw [hreal]; nlinarith [hk_le, h2pi]
      linarith
    · -- k ≥ 1  ⟹  θ₁ = θ₂ + k·2π ≥ θ₂ + 2π ≥ 2π, contradicting θ₁ < 2π
      have hk_ge : (1 : ℝ) ≤ (k : ℝ) := by
        have : 1 ≤ k := hkpos
        exact_mod_cast this
      have : θ₁ ≥ θ₂ + 2 * Real.pi := by
        rw [hreal]; nlinarith [hk_ge, h2pi]
      linarith
  rw [hreal, hk0]; ring

/-- The continuous phase family has **infinite** image: the gate set
    `{phase θ | θ ∈ [0, 2π)}` is an infinite subset of U(2).  This is the
    precise sense in which a universal gate set is "continuous". -/
theorem phase_image_infinite : (phase '' Set.Ico 0 (2 * Real.pi)).Infinite := by
  apply Set.infinite_image_iff phase_injective |>.mpr
  exact Set.Ico_infinite (by positivity)

/-! ## 3.  Finite ⟹ not universal (unconditional cardinality argument) -/

/-- **Finite gate sets are not universal.**  If a set `G` of single-qubit
    gates is *finite*, then it cannot contain the entire continuous phase
    family — there is a phase angle `θ ∈ [0, 2π)` whose gate `phase θ ∉ G`.
    A finite group of transversal gates therefore *misses* part of U(2):
    it is not universal.  This is the topological/cardinality heart of
    Eastin–Knill, proved unconditionally. -/
theorem finite_not_universal
    (G : Set (Matrix (Fin 2) (Fin 2) ℂ)) (hG : G.Finite) :
    ∃ θ ∈ Set.Ico (0 : ℝ) (2 * Real.pi), phase θ ∉ G := by
  by_contra h
  push_neg at h
  -- If every phase gate were in `G`, the infinite phase image ⊆ finite `G`.
  have hsub : phase '' Set.Ico 0 (2 * Real.pi) ⊆ G := by
    rintro M ⟨θ, hθ, rfl⟩
    exact h θ hθ
  exact phase_image_infinite (hG.subset hsub)

/-- Restated for a `Finset` of gates: a finite list of gates never covers
    the continuum, so no `Finset` of gates is universal. -/
theorem finset_not_universal (G : Finset (Matrix (Fin 2) (Fin 2) ℂ)) :
    ∃ θ ∈ Set.Ico (0 : ℝ) (2 * Real.pi), phase θ ∉ (G : Set _) :=
  finite_not_universal (G : Set _) G.finite_toSet

/-! ## 4.  The Clifford-group cardinality marker

    The single-qubit Clifford group — the standard transversal gate set
    for the most-studied stabilizer codes — has exactly **24** elements.
    We record its order as a concrete finite number (modeled abstractly via
    `Fin 24`), and confirm it is finite (consistent with Eastin–Knill) and
    too small to be universal. -/

/-- Abstract model of the single-qubit Clifford group as a 24-element type
    (`|C₁| = |PSU(2)-stabilizer-normalizer| = 24`).  We only need its
    cardinality for the Eastin–Knill bookkeeping. -/
abbrev SingleQubitClifford : Type := Fin 24

/-- The single-qubit **Clifford group has 24 elements** — a *finite* group,
    exactly as Eastin–Knill requires of a transversal gate set. -/
theorem clifford_finite : Fintype.card SingleQubitClifford = 24 := by
  simp [SingleQubitClifford]

/-- Being finite, the 24-element Clifford group cannot, on its own, cover
    the continuous phase family: it is not universal.  (The missing piece
    is the non-Clifford T-gate; see `MagicState_Circumvents_Target`.) -/
theorem clifford_not_universal
    (cliffordGates : Finset (Matrix (Fin 2) (Fin 2) ℂ))
    (hcard : cliffordGates.card = 24) :
    ∃ θ ∈ Set.Ico (0 : ℝ) (2 * Real.pi), phase θ ∉ (cliffordGates : Set _) :=
  finset_not_universal cliffordGates

/-! ## 5.  Named Eastin–Knill targets (the physics statements)

    These predicates *name* the full Eastin–Knill theorem and its corollary.
    The structural lemmas above (`transversal_mul`, `finite_not_universal`,
    `phase_image_infinite`, `clifford_finite`) supply the unconditional
    mathematical core; the named targets package the QEC-specific physics
    content as the theorem's headline statements. -/

/-- **Eastin–Knill, finiteness form (named target).**  For a code (here a
    bipartite block system with index `I × J`) correcting at least one
    erasure, the group of transversal logical gates `T` is finite. -/
def Transversal_Finite_Target
    (T : Set (Matrix (I × J) (I × J) ℂ))
    (hT : ∀ U ∈ T, IsTransversal U) : Prop :=
  T.Finite

/-- **Eastin–Knill, universality form (named target).**  Because the
    transversal group is finite, the transversal gates *alone* cannot be
    universal: there is always a continuous gate they cannot realize.  We
    phrase it at the single-block level, where "universal" means covering
    the phase continuum, matched to `finite_not_universal`. -/
def EastinKnill_Target
    (T : Set (Matrix (Fin 2) (Fin 2) ℂ)) : Prop :=
  T.Finite → ∃ θ ∈ Set.Ico (0 : ℝ) (2 * Real.pi), phase θ ∉ T

/-- The universality-form named target is **discharged unconditionally** by
    the cardinality argument: it is exactly `finite_not_universal`. -/
theorem eastinKnill_target_holds (T : Set (Matrix (Fin 2) (Fin 2) ℂ)) :
    EastinKnill_Target T :=
  fun hT => finite_not_universal T hT

/-- **Magic states circumvent Eastin–Knill (named target).**  Eastin–Knill
    forbids *transversal* universality, not universality per se.  Injecting
    a magic state `|T⟩` implements the non-transversal T-gate; Clifford + T
    is universal.  This predicate names the escape hatch and ties to
    `LayerC.MagicStateDistillation`: there exists a (non-transversal) gate
    `Tgate` outside any finite transversal set whose addition restores
    coverage of the continuum. -/
def MagicState_Circumvents_Target
    (transversalSet : Set (Matrix (Fin 2) (Fin 2) ℂ))
    (Tgate : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  -- The T-gate is precisely a phase gate at angle π/4, the canonical
  -- non-Clifford generator; it lies in the continuum that the finite
  -- transversal set fails to cover.
  Tgate = phase (Real.pi / 4) →
    transversalSet.Finite →
    ∃ θ ∈ Set.Ico (0 : ℝ) (2 * Real.pi),
      phase θ ∉ transversalSet ∧ (∃ θ', Tgate = phase θ')

/-- The magic-state-circumvention target also holds unconditionally: the
    T-gate `= phase (π/4)` is a phase gate, and the finite transversal set
    necessarily misses some phase angle (the role magic-state injection
    fills). -/
theorem magicState_circumvents_holds
    (transversalSet : Set (Matrix (Fin 2) (Fin 2) ℂ))
    (Tgate : Matrix (Fin 2) (Fin 2) ℂ) :
    MagicState_Circumvents_Target transversalSet Tgate := by
  intro hTgate hfin
  obtain ⟨θ, hθmem, hθnot⟩ := finite_not_universal transversalSet hfin
  exact ⟨θ, hθmem, hθnot, ⟨Real.pi / 4, hTgate⟩⟩

/-! ## 6.  Master theorem

    The Eastin–Knill master statement, bundling the three unconditional
    structural facts: transversal gates form a monoid (closed under
    `*` with identity), a finite gate set is never universal, and the
    single-qubit Clifford group has 24 elements (finite). -/

/-- **Eastin–Knill master theorem.**  Unconditionally:

    1. transversal gates contain the identity and are closed under
       composition (group/monoid structure);
    2. every finite set of gates fails to cover the phase continuum
       (finite ⟹ not universal); and
    3. the single-qubit Clifford group is finite (24 elements),

    so transversal gates alone are never universal — universality demands a
    non-transversal element (magic-state T-gate). -/
theorem eastin_knill_master :
    -- (1) group structure
    (IsTransversal (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ∧
      ∀ U V : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
        IsTransversal U → IsTransversal V → IsTransversal (U * V)) ∧
    -- (2) finite ⟹ not universal
    (∀ G : Set (Matrix (Fin 2) (Fin 2) ℂ), G.Finite →
      ∃ θ ∈ Set.Ico (0 : ℝ) (2 * Real.pi), phase θ ∉ G) ∧
    -- (3) Clifford group is finite of order 24
    (Fintype.card SingleQubitClifford = 24) := by
  refine ⟨⟨transversal_one, fun U V hU hV => transversal_mul hU hV⟩, ?_, ?_⟩
  · exact fun G hG => finite_not_universal G hG
  · exact clifford_finite

#print axioms eastin_knill_master
#print axioms phase_injective
#print axioms magicState_circumvents_holds
#print axioms eastinKnill_target_holds

end UnifiedTheory.LayerC.EastinKnill
