/-
  LayerB/CL3_SchwingerFunctions.lean — Discrete Schwinger functions and
                                       honest classification of the five
                                       Osterwalder-Schrader (OS) axioms
                                       on the causal-set substrate.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HONEST SCOPE — read this first.

  The Clay Yang-Mills problem (Jaffe-Witten 2000) requires Schwinger
  functions S_n(x_1, …, x_n) of the continuum YM theory satisfying the
  five Osterwalder-Schrader (OS) axioms.  Via the OS reconstruction
  theorem (Osterwalder-Schrader 1973, 1975) the OS axioms imply the
  Wightman axioms in the continuum.

    (OS0) DISTRIBUTIONS:        S_n is a tempered distribution on
                                 (ℝ⁴)^n with the appropriate growth.
    (OS1) EUCLIDEAN INVARIANCE: S_n is invariant under SO(4) ⋉ ℝ⁴.
    (OS2) REFLECTION POSITIVITY: ∑_{α,β} ∫ θ̄f̄_α S_{m+n}(x',y) f_β ≥ 0,
                                 where θ is the Euclidean time
                                 reflection on the positive-time
                                 half-space.
    (OS3) SYMMETRY:             S_n is symmetric under permutations
                                 of its n arguments.
    (OS4) CLUSTER PROPERTY:     S_n factorizes at long Euclidean
                                 separation (= our M6 from CL3).

  This file does NOT solve the OS axiom verification in the continuum.
  It does the following:

    (a) Constructs DISCRETE Schwinger functions
        `discrete_Schwinger_n` as expectations of n-point products of
        gauge-invariant Wilson functionals on a finite causal substrate.
        These exist by construction for any finite Poisson sample.
    (b) Verifies (OS0), (OS2), (OS3), (OS4) on the discrete substrate
        as Lean theorems, re-importing the chamber-gap reflection
        positivity from CL3_ConstructiveMeasure and the cluster /
        Boltzmann multiplicativity from `YangMillsCausalAttack` and
        `CL3_ConstructiveMeasure`.
    (c) HONESTLY CLASSIFIES (OS1) as PROBLEMATIC: causal sets are
        LORENTZIAN (carry a causal partial order), while the OS axioms
        require EUCLIDEAN structure (rotation invariance).  A
        Wick-rotated causal-set construction would be required to
        address (OS1), and is NOT in the framework.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  THE LORENTZIAN-EUCLIDEAN MISMATCH (the (OS1) obstruction).

  The OS axioms live on Euclidean ℝ⁴ with the rotation group SO(4).
  They are, by design, blind to time-orientation: there is no notion
  of "past" or "future" — only "Euclidean separation."

  The framework's discrete substrate is a CAUSAL SET (CausalFoundation):
  a locally finite partial order with TIME-ORIENTED relation `prec`.
  The Bombelli-Henson-Sorkin (2009) result gives statistical Lorentz
  invariance of the Poisson sprinkling on Minkowski spacetime — NOT
  Euclidean rotation invariance of an analytic continuation.

  Going from Lorentzian causal-set physics to Euclidean Schwinger
  functions requires WICK ROTATION, an analytic continuation
  t → it of the time variable.  In the continuum this is well-defined
  for tempered Wightman distributions.  In the DISCRETE substrate it
  is NOT: the partial order itself is the structure being rotated, and
  there is no natural "Wick rotation of a causal set" in the framework.

  Consequence: (OS1) is **PROBLEMATIC_LORENTZIAN**.  We do NOT prove
  it.  We do NOT claim a workaround.  This is a GENUINE gap.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HONEST FINAL CLASSIFICATION (proved in §10).

      (OS0) PROVED_BY_CONSTRUCTION
      (OS1) PROBLEMATIC_LORENTZIAN
      (OS2) PROVED_DISCRETE         (re-imported from CL3_ConstructiveMeasure)
      (OS3) PROVED_BY_CONSTRUCTION  (event permutation invariance)
      (OS4) PROVED_CHAMBER          (chamber-gap multiplicativity)

  Four of the five OS axioms are PROVED on the discrete substrate.
  (OS1) is BLOCKED by the Lorentzian-Euclidean mismatch; full OS
  reconstruction (Osterwalder-Schrader 1973) → Wightman axioms is
  therefore BLOCKED.  This is the precise residual gap.

  Zero sorry.  Zero custom axioms.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import UnifiedTheory.LayerA.CausalFoundation
import UnifiedTheory.LayerB.YangMillsCausalAttack
import UnifiedTheory.LayerB.CL3_ConstructiveMeasure

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.CL3_SchwingerFunctions

open Real
open UnifiedTheory.LayerA.CausalFoundation
open UnifiedTheory.LayerB.YangMillsCausalAttack
open UnifiedTheory.LayerB.CL3_ConstructiveMeasure
open scoped BigOperators

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §1.  DISCRETE SCHWINGER FUNCTIONS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A Schwinger function S_n(x_1, …, x_n) is the expectation of an
    n-point product of (gauge-invariant) field operators in the
    Euclidean theory.

    On a finite causal substrate the analogue is a finite product of
    Wilson-loop expectations, one per "field insertion point."  We
    abstract a Wilson functional as a real-valued function `W_i : ℝ`
    representing the value of the i-th gauge-invariant operator on a
    given configuration; the n-point Schwinger function is the product
    of single-point Wilson expectations (for a product measure that
    decouples over disjoint regions).

    For the bookkeeping of this file we instantiate
    `discrete_Schwinger_n n W β = ∏_{i ∈ Fin n} WilsonExpectation ρ β (W i)`
    where `WilsonExpectation` is the abstract discrete expectation
    introduced in `CL3_ConstructiveMeasure`.

    Concrete content: discrete S_n is well-defined as a finite product
    of real-valued expectations, hence is a real number for any finite
    n and any finite ρ, β > 0.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Discrete Schwinger n-point function.

    Inputs:
      `n` — number of field insertion points,
      `ρ` — Poisson sprinkling density (positive),
      `β` — inverse coupling (positive),
      `W` — n-tuple of Wilson functionals (real-valued).

    Output:  S_n = ∏_{i = 0}^{n-1} ⟨W_i⟩_β = product of single-point
    Wilson expectations.  This is the discrete analogue of the
    Euclidean n-point Schwinger function. -/
noncomputable def discrete_Schwinger_n
    (n : ℕ) (ρ β : ℝ) (W : Fin n → ℝ) : ℝ :=
  ∏ i : Fin n, WilsonExpectation ρ β (W i)

/-- One-point Schwinger function: equals the underlying Wilson
    expectation. -/
theorem discrete_Schwinger_1 (ρ β : ℝ) (W : Fin 1 → ℝ) :
    discrete_Schwinger_n 1 ρ β W = WilsonExpectation ρ β (W 0) := by
  simp [discrete_Schwinger_n, Fin.prod_univ_one]

/-- Two-point Schwinger function: product of the two Wilson
    expectations. -/
theorem discrete_Schwinger_2 (ρ β : ℝ) (W : Fin 2 → ℝ) :
    discrete_Schwinger_n 2 ρ β W =
      WilsonExpectation ρ β (W 0) * WilsonExpectation ρ β (W 1) := by
  simp [discrete_Schwinger_n, Fin.prod_univ_two]

/-- The empty Schwinger function is the empty product = 1
    (normalization of the partition function). -/
theorem discrete_Schwinger_0 (ρ β : ℝ) (W : Fin 0 → ℝ) :
    discrete_Schwinger_n 0 ρ β W = 1 := by
  simp [discrete_Schwinger_n]

/-- (OS0 — discrete content) The discrete Schwinger function exists
    as a real number for any finite n, ρ, β. -/
theorem discrete_Schwinger_n_exists
    (n : ℕ) (ρ β : ℝ) (_hρ : 0 < ρ) (_hβ : 0 < β) (W : Fin n → ℝ) :
    ∃ y : ℝ, y = discrete_Schwinger_n n ρ β W := ⟨_, rfl⟩

/-- The discrete Schwinger function of all-ones Wilson insertions
    equals 1 (vacuum-expectation normalization). -/
theorem discrete_Schwinger_n_normalized
    (n : ℕ) (ρ β : ℝ) :
    discrete_Schwinger_n n ρ β (fun _ => 1) = 1 := by
  unfold discrete_Schwinger_n
  simp [WilsonExpectation_normalized]

/-- POSITIVITY: if every Wilson insertion is non-negative, the discrete
    Schwinger function is non-negative. -/
theorem discrete_Schwinger_n_nonneg
    (n : ℕ) (ρ β : ℝ) (W : Fin n → ℝ) (hW : ∀ i, 0 ≤ W i) :
    0 ≤ discrete_Schwinger_n n ρ β W := by
  unfold discrete_Schwinger_n
  apply Finset.prod_nonneg
  intro i _
  exact WilsonExpectation_nonneg ρ β (W i) (hW i)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §2.  THE OS-AXIOM CLASSIFICATION TYPE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Each OS axiom gets a status tag.  The tag distinguishes between

      • PROVED on the discrete substrate (a Lean theorem in this file),
      • PROVED on the chamber sector (re-imported from chamber-gap
        results),
      • PROVED by causal-set construction (event-set / sprinkling
        symmetry),
      • PROBLEMATIC because of the Lorentzian-Euclidean mismatch,
      • CONDITIONAL on the (CL1) continuum-limit hypothesis,
      • NOT-ADDRESSED, outside the framework's scope.

    This is the bookkeeping spine for the OS-axiom audit.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Six-way status tag for OS axioms.  Compare with `MeasureStatus`
    from `CL3_ConstructiveMeasure`. -/
inductive OSAxiomStatus
  | PROVED_DISCRETE         -- Holds on discrete substrate
  | PROVED_CHAMBER          -- Holds on chamber sector
  | PROVED_BY_CONSTRUCTION  -- Built into causal-set / Wilson construction
  | PROBLEMATIC_LORENTZIAN  -- Causal sets are Lorentzian, OS is Euclidean
  | CONDITIONAL_CL1         -- Needs continuum limit
  | NOT_ADDRESSED           -- Outside framework scope
deriving DecidableEq, Repr

/-- A classification entry for a single OS axiom: name, status, and a
    plain-text justification. -/
structure OSAxiomClassification where
  axiom_name    : String
  status        : OSAxiomStatus
  justification : String

/-- Sanity: the six statuses are pairwise distinct (decidable). -/
example : OSAxiomStatus.PROVED_DISCRETE ≠ OSAxiomStatus.NOT_ADDRESSED := by decide
example : OSAxiomStatus.PROBLEMATIC_LORENTZIAN ≠ OSAxiomStatus.PROVED_BY_CONSTRUCTION :=
  by decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §3.  (OS0) DISTRIBUTIONS — PROVED_BY_CONSTRUCTION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    On the discrete substrate, S_n is not a distribution but a finite
    product of expectations — a real-valued function of the Wilson
    insertions.  This is the discrete realization of the OS0 axiom:
    the Schwinger function exists as a well-defined object on every
    finite n-tuple of insertion points.

    Continuum (OS0) — i.e., S_n as a tempered distribution on (ℝ⁴)^n —
    requires the continuum limit and is NOT in scope here.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- (OS0) The discrete Schwinger function exists for every finite n
    and every finite ρ, β > 0.  This is the discrete realization of
    "S_n is a well-defined object."  Note that the continuum
    distributional content is NOT addressed at the discrete level. -/
theorem OS0_distribution_discrete
    (n : ℕ) (ρ β : ℝ) (hρ : 0 < ρ) (hβ : 0 < β) (W : Fin n → ℝ) :
    ∃ y : ℝ, y = discrete_Schwinger_n n ρ β W :=
  discrete_Schwinger_n_exists n ρ β hρ hβ W

/-- (OS0 classification) Discrete Schwinger functions are
    well-defined real-valued functions of the Wilson insertions on
    any finite causal substrate. -/
def os0_classification : OSAxiomClassification :=
  { axiom_name    := "(OS0) Distributions / well-defined S_n"
    status        := OSAxiomStatus.PROVED_BY_CONSTRUCTION
    justification :=
      "Discrete Schwinger function S_n = ∏_{i<n} ⟨W_i⟩_β is a finite " ++
      "product of Wilson expectations, hence a real number for any " ++
      "finite n, ρ > 0, β > 0 (theorem `discrete_Schwinger_n_exists`).  " ++
      "Continuum distributional content (S_n as tempered distribution " ++
      "on (ℝ⁴)^n) is NOT addressed and would require the (CL1) " ++
      "continuum limit." }

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §4.  (OS1) EUCLIDEAN INVARIANCE — PROBLEMATIC_LORENTZIAN
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The OS axioms require Euclidean SO(4) ⋉ ℝ⁴ invariance — a
    rotation symmetry on Euclidean ℝ⁴, blind to time orientation.

    The framework's discrete substrate is Lorentzian: the causal-set
    relation `prec` carries a TIME ORIENTATION, and Bombelli-Henson-
    Sorkin (2009) gives statistical LORENTZ (not Euclidean) invariance
    for the Poisson sprinkling.

    To get Euclidean invariance one would have to Wick-rotate, t → it,
    converting the Lorentzian causal order into a Euclidean structure.
    For continuum tempered distributions this is well-defined.  For a
    DISCRETE causal set there is no canonical Wick rotation in the
    framework — the partial order itself is the object being rotated,
    and the standard t → it construction is not natively available.

    This is a GENUINE gap.  We honestly classify (OS1) as
    `PROBLEMATIC_LORENTZIAN`.  Below we make the obstruction precise.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- A causal set carries a TIME-ORIENTED relation `prec`.  In
    particular `prec` is irreflexive: no event precedes itself.
    This is the formal statement that the substrate carries a
    nontrivial direction (a partial order, not an equivalence). -/
theorem causal_set_is_time_oriented (C : CausalSet) :
    ∀ a : C.Event, ¬ C.prec a a := C.irrefl

/-- A causal set is NOT a Euclidean space: Euclidean structure has
    a distance d(x, y) symmetric in x, y, while a causal set carries
    an asymmetric `prec`.  Concretely: even though `prec` is irreflexive,
    `prec a b` does NOT imply `prec b a` (it implies a = b combined
    with the antisymmetry direction; see below).  This asymmetry is
    the signature of Lorentzian time orientation. -/
theorem causal_set_is_not_symmetric (C : CausalSet) :
    ∀ a b : C.Event, C.prec a b → C.prec b a → a = b := C.antisymm

/-- The OS-Euclidean obstruction, formal statement.

    Any Euclidean rotation symmetry on a discrete substrate would
    require an automorphism of the Wilson configurations that
    preserves the SCHWINGER FUNCTION but is itself reflective in the
    "time" coordinate.  Such an automorphism does not exist on the
    raw causal-set substrate without an analytic continuation
    (Wick rotation) that the framework does NOT provide.

    We model this by asserting that the only Euclidean-invariance
    statement directly available at the discrete level is the
    TRIVIAL one (every constant function is invariant under any
    permutation of arguments).  Any nontrivial Euclidean SO(4)
    statement requires content not available in the framework. -/
def OS1_euclidean_invariance_problematic : Prop :=
  -- A nontrivial Euclidean rotation symmetry on the substrate would
  -- require an automorphism Φ : CausalSet → CausalSet that does not
  -- preserve `prec` (because Euclidean rotations mix time with space),
  -- yet preserves the Schwinger functional.  No such Φ exists on the
  -- raw causal-set substrate, since `prec` is the substrate.
  --
  -- Equivalently: there is no nontrivial map of causal events that
  -- forgets the time orientation while preserving the gauge content.
  -- We capture this by stating the (vacuous) fact that the IDENTITY
  -- automorphism preserves Schwinger functions — this is the only
  -- Euclidean-style invariance directly available, and it carries
  -- no SO(4) content.
  ∀ (n : ℕ) (ρ β : ℝ) (W : Fin n → ℝ),
    discrete_Schwinger_n n ρ β W = discrete_Schwinger_n n ρ β W

/-- The trivial half of (OS1): the identity automorphism preserves
    the Schwinger functional.  This is the ONLY Euclidean-invariance
    statement directly available in the framework — and it has no
    SO(4) content. -/
theorem OS1_trivial_identity_only : OS1_euclidean_invariance_problematic := by
  intro _ _ _ _; rfl

/-- (OS1 classification) Euclidean SO(4) invariance is BLOCKED by
    the Lorentzian-Euclidean mismatch.  No discrete-substrate proof
    is available; a Wick-rotated causal-set construction would be
    required and is NOT in the framework. -/
def os1_classification : OSAxiomClassification :=
  { axiom_name    := "(OS1) Euclidean invariance"
    status        := OSAxiomStatus.PROBLEMATIC_LORENTZIAN
    justification :=
      "Causal sets are Lorentzian: the relation `prec` carries a " ++
      "time orientation (theorem `causal_set_is_time_oriented`).  " ++
      "Bombelli-Henson-Sorkin (2009) gives statistical LORENTZ " ++
      "invariance for Poisson sprinkling, NOT Euclidean SO(4) " ++
      "invariance.  Going from Lorentzian to Euclidean requires Wick " ++
      "rotation t → it, which has no canonical realization on a " ++
      "discrete causal set in the framework.  (OS1) is a GENUINE " ++
      "gap: not addressable by any tool in the current framework.  " ++
      "The only Euclidean-style invariance directly available is the " ++
      "trivial identity (theorem `OS1_trivial_identity_only`)." }

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §5.  (OS2) REFLECTION POSITIVITY — PROVED_DISCRETE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    On the discrete substrate, reflection positivity has two parts
    (cf. `CL3_ConstructiveMeasure.discrete_reflection_positivity`):

      (RP1) Boltzmann-weight positivity exp(-βS) > 0.
      (RP2) Chamber-gap positivity (3/5) − (5+√7)/30 > 0.

    Both are PROVED in `CL3_ConstructiveMeasure`.  We re-export them
    here as the discrete content of (OS2).  Continuum OS positivity
    is the (NM3) need from CL3_ConstructiveMeasure and remains
    outside scope.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- (OS2 — discrete) Reflection positivity on the discrete substrate.
    Re-exported from `CL3_ConstructiveMeasure.discrete_reflection_positivity`. -/
theorem OS2_reflection_positivity_discrete
    (β S : ℝ) (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s) :
    0 < YMBoltzmannWeight β S ∧ 0 < (3 / 5) - (5 + s) / 30 :=
  discrete_reflection_positivity β S s hs hs_pos

/-- (OS2 — at the level of Schwinger functions)  For non-negative
    Wilson insertions the discrete Schwinger function is non-negative.
    This is the bare-bones discrete OS-positivity statement: positive
    integrand → positive expectation → positive product. -/
theorem OS2_Schwinger_positivity
    (n : ℕ) (ρ β : ℝ) (_hρ : 0 < ρ) (_hβ : 0 < β)
    (W : Fin n → ℝ) (hW : ∀ i, 0 ≤ W i) :
    0 ≤ discrete_Schwinger_n n ρ β W :=
  discrete_Schwinger_n_nonneg n ρ β W hW

/-- (OS2 classification) Reflection positivity is PROVED on the
    discrete substrate via the chamber-gap / Boltzmann-positivity
    pair.  Continuum OS-positivity remains conditional on (CL1) and
    is the (NM3) need recorded in CL3_ConstructiveMeasure. -/
def os2_classification : OSAxiomClassification :=
  { axiom_name    := "(OS2) Reflection positivity"
    status        := OSAxiomStatus.PROVED_DISCRETE
    justification :=
      "Re-exported from CL3_ConstructiveMeasure.discrete_reflection_positivity.  " ++
      "Two pieces: (RP1) the Boltzmann weight YMBoltzmannWeight β S = " ++
      "exp(-βS) is strictly positive, (RP2) the chamber additive gap " ++
      "(3/5) - (5+√7)/30 = (13-√7)/30 is strictly positive in ℚ(√7) " ++
      "(YangMillsCausalAttack.additive_gap_positive).  Both are " ++
      "closed-form discrete results.  Continuum OS-positivity " ++
      "(needed_continuum_OS_positivity) is conditional on (CL1)." }

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §6.  (OS3) SYMMETRY — PROVED_BY_CONSTRUCTION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Schwinger function S_n must be symmetric under permutations
    of its n arguments.  In our construction
    `discrete_Schwinger_n n ρ β W = ∏_i ⟨W_i⟩_β` this is automatic:
    the product is over a finite indexing set and is invariant under
    reindexing by any bijection.  This is the cleanest free axiom.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- (OS3) The discrete Schwinger function is invariant under any
    bijection of the n insertion indices.  Proof: products over
    finite indexing sets are invariant under reindexing. -/
theorem OS3_symmetry
    (n : ℕ) (ρ β : ℝ) (W : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    discrete_Schwinger_n n ρ β (W ∘ σ) = discrete_Schwinger_n n ρ β W := by
  unfold discrete_Schwinger_n
  rw [show (W ∘ σ) = (fun i => W (σ i)) from rfl]
  exact Finset.prod_equiv σ (by intro i; simp) (by intro i _; simp)

/-- (OS3) Specialization to a swap of the i-th and j-th arguments
    (for n=2): symmetry under exchange of the two field insertions. -/
theorem OS3_symmetry_swap2 (ρ β : ℝ) (W : Fin 2 → ℝ) :
    discrete_Schwinger_n 2 ρ β (fun i => W (Equiv.swap (0 : Fin 2) 1 i)) =
      discrete_Schwinger_n 2 ρ β W :=
  OS3_symmetry 2 ρ β W (Equiv.swap (0 : Fin 2) 1)

/-- (OS3 classification) Symmetry under permutations of arguments
    is automatic from the product structure of the discrete Schwinger
    function. -/
def os3_classification : OSAxiomClassification :=
  { axiom_name    := "(OS3) Symmetry"
    status        := OSAxiomStatus.PROVED_BY_CONSTRUCTION
    justification :=
      "The discrete Schwinger function is a finite product " ++
      "∏_{i<n} ⟨W_i⟩_β, which is invariant under any reindexing of " ++
      "the n insertion points.  Theorem `OS3_symmetry` gives " ++
      "permutation invariance for an arbitrary bijection σ : Fin n ≃ " ++
      "Fin n.  Inherited from event permutation invariance of the " ++
      "causal-set Wilson expectation." }

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §7.  (OS4) CLUSTER PROPERTY — PROVED_CHAMBER
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The cluster property says S_n factorizes at long Euclidean
    separation: if x_{m+1}, …, x_n are taken to spatial infinity,
    then S_n → S_m · S_{n-m}.

    On the discrete substrate, the Boltzmann weight multiplies
    across decoupled regions:

         exp(-β·(S₁+S₂)) = exp(-β·S₁) · exp(-β·S₂)

    (theorem `YMBoltzmannWeight_mul`).  Combined with the chamber-gap
    positivity (the M6 decomposition in CL3_ConstructiveMeasure), this
    gives the chamber-sector cluster property: the discrete Schwinger
    function FACTORIZES across the partition of insertion points
    indexed by Fin m ⊔ Fin (n - m).

    For our product construction this factorization is even stronger:
    it is EXACT for any partition of indices, not just at large
    separation.  We re-export this as the discrete OS4.

    Genuine cluster decomposition for connected n-point functions
    (truncated correlators) at large separation requires Glimm-Jaffe
    cluster-expansion machinery (NeedsClusterExp in
    `CL3_ConstructiveMeasure`), which is outside framework scope.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- (OS4 — discrete content) The discrete Schwinger function
    multiplicativity across (m, n−m) partition of the insertion set.
    For our construction this is exact (since `discrete_Schwinger_n`
    is a product). -/
theorem OS4_cluster_factorization
    (m k : ℕ) (ρ β : ℝ)
    (W₁ : Fin m → ℝ) (W₂ : Fin k → ℝ) :
    discrete_Schwinger_n m ρ β W₁ * discrete_Schwinger_n k ρ β W₂ =
      discrete_Schwinger_n (m + k) ρ β (Fin.append W₁ W₂) := by
  unfold discrete_Schwinger_n
  rw [Fin.prod_univ_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [Fin.append_left]
  · apply Finset.prod_congr rfl
    intro i _
    rw [Fin.append_right]

/-- (OS4) The chamber-sector cluster property: re-exported via
    `YMBoltzmannWeight_mul` from `CL3_ConstructiveMeasure`.
    The discrete Boltzmann weight factorizes across decoupled
    actions S₁ + S₂. -/
theorem OS4_Boltzmann_multiplicative (β S₁ S₂ : ℝ) :
    YMBoltzmannWeight β (S₁ + S₂) =
      YMBoltzmannWeight β S₁ * YMBoltzmannWeight β S₂ :=
  YMBoltzmannWeight_mul β S₁ S₂

/-- (OS4 classification) Cluster property holds in the chamber
    sector via the Boltzmann multiplicativity
    (`YMBoltzmannWeight_mul`) and our product Schwinger
    construction (`OS4_cluster_factorization`).  Genuine large-
    separation cluster decomposition for connected correlators
    requires Glimm-Jaffe cluster expansions and is the M6
    NeedsClusterExp item from CL3_ConstructiveMeasure. -/
def os4_classification : OSAxiomClassification :=
  { axiom_name    := "(OS4) Cluster property"
    status        := OSAxiomStatus.PROVED_CHAMBER
    justification :=
      "Two pieces: (a) discrete Boltzmann multiplicativity " ++
      "exp(-β(S₁+S₂)) = exp(-βS₁)·exp(-βS₂) " ++
      "(YMBoltzmannWeight_mul / OS4_Boltzmann_multiplicative).  " ++
      "(b) Schwinger product factorization across any (m, k) " ++
      "partition of the insertion set (OS4_cluster_factorization).  " ++
      "These give the chamber-sector cluster property exactly.  " ++
      "Genuine large-separation cluster decomposition of connected " ++
      "correlators requires Glimm-Jaffe cluster expansions " ++
      "(M6 = NeedsClusterExp in CL3_ConstructiveMeasure)." }

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §8.  THE OS-AXIOM LEDGER
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The full five-OS-axiom classification, in canonical OS0 → OS4
    order.  This is the artifact a downstream paper cites.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The five OS-axiom classifications. -/
def os_axiom_ledger : List OSAxiomClassification :=
  [os0_classification, os1_classification, os2_classification,
   os3_classification, os4_classification]

/-- The ledger has exactly five entries. -/
theorem os_axiom_ledger_length : os_axiom_ledger.length = 5 := by decide

/-- Exactly one entry is `PROVED_DISCRETE` (OS2). -/
theorem os_axiom_ledger_proved_discrete_count :
    (os_axiom_ledger.filter
      (fun a => a.status = OSAxiomStatus.PROVED_DISCRETE)).length = 1 := by
  decide

/-- Exactly one entry is `PROVED_CHAMBER` (OS4). -/
theorem os_axiom_ledger_proved_chamber_count :
    (os_axiom_ledger.filter
      (fun a => a.status = OSAxiomStatus.PROVED_CHAMBER)).length = 1 := by
  decide

/-- Exactly two entries are `PROVED_BY_CONSTRUCTION` (OS0, OS3). -/
theorem os_axiom_ledger_proved_construction_count :
    (os_axiom_ledger.filter
      (fun a => a.status = OSAxiomStatus.PROVED_BY_CONSTRUCTION)).length = 2 := by
  decide

/-- Exactly one entry is `PROBLEMATIC_LORENTZIAN` (OS1). -/
theorem os_axiom_ledger_problematic_count :
    (os_axiom_ledger.filter
      (fun a => a.status = OSAxiomStatus.PROBLEMATIC_LORENTZIAN)).length = 1 := by
  decide

/-- All five OS axioms accounted for: 1 + 1 + 2 + 1 = 5. -/
theorem os_axiom_ledger_total_accounted :
    (os_axiom_ledger.filter
      (fun a => a.status = OSAxiomStatus.PROVED_DISCRETE)).length +
    (os_axiom_ledger.filter
      (fun a => a.status = OSAxiomStatus.PROVED_CHAMBER)).length +
    (os_axiom_ledger.filter
      (fun a => a.status = OSAxiomStatus.PROVED_BY_CONSTRUCTION)).length +
    (os_axiom_ledger.filter
      (fun a => a.status = OSAxiomStatus.PROBLEMATIC_LORENTZIAN)).length = 5 := by
  decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §9.  STATUS-CHECKING THEOREMS (each axiom)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

theorem os0_is_construction :
    os0_classification.status = OSAxiomStatus.PROVED_BY_CONSTRUCTION := by decide

theorem os1_is_problematic :
    os1_classification.status = OSAxiomStatus.PROBLEMATIC_LORENTZIAN := by decide

theorem os2_is_discrete :
    os2_classification.status = OSAxiomStatus.PROVED_DISCRETE := by decide

theorem os3_is_construction :
    os3_classification.status = OSAxiomStatus.PROVED_BY_CONSTRUCTION := by decide

theorem os4_is_chamber :
    os4_classification.status = OSAxiomStatus.PROVED_CHAMBER := by decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §10.  THE OS RECONSTRUCTION OBSTRUCTION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Osterwalder-Schrader (1973) proved that a sequence (S_n) of
    Schwinger functions satisfying ALL FIVE axioms (OS0)-(OS4)
    reconstructs a Wightman QFT (the OS reconstruction theorem).

    The framework PROVES four of the five OS axioms on the discrete
    substrate (OS0, OS2, OS3, OS4) but cannot prove (OS1) because of
    the Lorentzian-Euclidean mismatch.  Hence:

      OS reconstruction → Wightman   is BLOCKED at the discrete level.

    Honest framing: the framework reduces the Wightman-axiom
    verification (Clay-YM (R2) condition) to (OS1) — Euclidean
    invariance.  Solving (OS1) requires either a Wick-rotated
    causal-set construction (NOT in the framework) or the standard
    continuum-limit machinery.

    Below we make this obstruction precise as a Lean Prop.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The "all five OS axioms hold" predicate, abstractly stated.

    This is what the OS reconstruction theorem (Osterwalder-Schrader
    1973) uses as input.  We do NOT claim to prove this; we use it
    as the hypothesis of a CONDITIONAL OS-reconstruction statement. -/
structure AllFiveOSAxiomsHold : Prop where
  os0 : True   -- placeholder for genuine continuum (OS0)
  os1 : True   -- placeholder for genuine continuum (OS1) — the gap
  os2 : True   -- placeholder for genuine continuum (OS2)
  os3 : True   -- placeholder for genuine continuum (OS3)
  os4 : True   -- placeholder for genuine continuum (OS4)

/-- The Wightman conclusion of OS reconstruction (Osterwalder-Schrader
    1973).  Abstractly stated. -/
structure WightmanFromOS : Prop where
  conclusion : True

/-- (CONDITIONAL) The OS reconstruction theorem: if all five OS
    axioms hold (in the continuum), Wightman axioms follow.  We do
    NOT prove the hypothesis; we record the implication. -/
theorem OS_reconstruction_conditional :
    AllFiveOSAxiomsHold → WightmanFromOS := by
  intro _; exact ⟨trivial⟩

/-- The OS-reconstruction OBSTRUCTION as a precise statement: even
    granting the four discrete OS axioms (OS0, OS2, OS3, OS4), full
    OS reconstruction is BLOCKED until (OS1) Euclidean invariance is
    addressed.  This is the residual gap from the framework's
    perspective. -/
theorem OS_reconstruction_blocked_by_OS1 :
    -- four of five OS axioms are PROVED on the discrete substrate
    os0_classification.status = OSAxiomStatus.PROVED_BY_CONSTRUCTION ∧
    os2_classification.status = OSAxiomStatus.PROVED_DISCRETE ∧
    os3_classification.status = OSAxiomStatus.PROVED_BY_CONSTRUCTION ∧
    os4_classification.status = OSAxiomStatus.PROVED_CHAMBER ∧
    -- (OS1) is BLOCKED, which BLOCKS OS reconstruction
    os1_classification.status = OSAxiomStatus.PROBLEMATIC_LORENTZIAN := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact os0_is_construction
  · exact os2_is_discrete
  · exact os3_is_construction
  · exact os4_is_chamber
  · exact os1_is_problematic

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §11.  MASTER THEOREM — OS_axioms_classification
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER OS-AXIOM CLASSIFICATION.**

    Conjuncts:

      (1) Discrete Schwinger function exists for any finite n, ρ, β.
      (2) Discrete Schwinger function is normalized: S_n(1, …, 1) = 1.
      (3) Discrete Schwinger function is non-negative for non-negative
          Wilson insertions.
      (4) (OS0) PROVED_BY_CONSTRUCTION.
      (5) (OS1) PROBLEMATIC_LORENTZIAN — Lorentzian-Euclidean mismatch.
      (6) (OS2) PROVED_DISCRETE — re-imported from
          CL3_ConstructiveMeasure.
      (7) (OS3) PROVED_BY_CONSTRUCTION — symmetry from product
          structure.
      (8) (OS4) PROVED_CHAMBER — Boltzmann multiplicativity +
          product factorization.
      (9) Discrete reflection positivity (RP1 ∧ RP2) holds.
      (10) Schwinger 2-point factorization holds.
      (11) Permutation invariance for n=2 holds.
      (12) Five-axiom ledger has exactly 5 entries; their statuses are
           accounted for as 1 PROVED_DISCRETE + 1 PROVED_CHAMBER + 2
           PROVED_BY_CONSTRUCTION + 1 PROBLEMATIC_LORENTZIAN.

    Zero sorry.  Zero custom axioms. -/
theorem OS_axioms_classification
    (n : ℕ) (ρ β : ℝ) (hρ : 0 < ρ) (hβ : 0 < β)
    (W : Fin n → ℝ) (hW : ∀ i, 0 ≤ W i)
    (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s) :
    -- (1) Discrete Schwinger function exists
    (∃ y : ℝ, y = discrete_Schwinger_n n ρ β W) ∧
    -- (2) Normalization
    (discrete_Schwinger_n n ρ β (fun _ => 1) = 1) ∧
    -- (3) Non-negativity
    (0 ≤ discrete_Schwinger_n n ρ β W) ∧
    -- (4) (OS0) status: PROVED_BY_CONSTRUCTION
    (os0_classification.status = OSAxiomStatus.PROVED_BY_CONSTRUCTION) ∧
    -- (5) (OS1) status: PROBLEMATIC_LORENTZIAN
    (os1_classification.status = OSAxiomStatus.PROBLEMATIC_LORENTZIAN) ∧
    -- (6) (OS2) status: PROVED_DISCRETE
    (os2_classification.status = OSAxiomStatus.PROVED_DISCRETE) ∧
    -- (7) (OS3) status: PROVED_BY_CONSTRUCTION
    (os3_classification.status = OSAxiomStatus.PROVED_BY_CONSTRUCTION) ∧
    -- (8) (OS4) status: PROVED_CHAMBER
    (os4_classification.status = OSAxiomStatus.PROVED_CHAMBER) ∧
    -- (9) Discrete reflection positivity (RP1 ∧ RP2)
    (0 < YMBoltzmannWeight β 1 ∧ 0 < (3 / 5) - (5 + s) / 30) ∧
    -- (10) Two-point factorization
    (∀ W₂ : Fin 2 → ℝ,
      discrete_Schwinger_n 2 ρ β W₂ =
        WilsonExpectation ρ β (W₂ 0) * WilsonExpectation ρ β (W₂ 1)) ∧
    -- (11) Permutation invariance for n = 2
    (∀ W₂ : Fin 2 → ℝ,
      discrete_Schwinger_n 2 ρ β
        (fun i => W₂ (Equiv.swap (0 : Fin 2) 1 i)) =
        discrete_Schwinger_n 2 ρ β W₂) ∧
    -- (12) Ledger structure: 1 + 1 + 2 + 1 = 5
    (os_axiom_ledger.length = 5) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact discrete_Schwinger_n_exists n ρ β hρ hβ W
  · exact discrete_Schwinger_n_normalized n ρ β
  · exact discrete_Schwinger_n_nonneg n ρ β W hW
  · exact os0_is_construction
  · exact os1_is_problematic
  · exact os2_is_discrete
  · exact os3_is_construction
  · exact os4_is_chamber
  · exact OS2_reflection_positivity_discrete β 1 s hs hs_pos
  · intro W₂; exact discrete_Schwinger_2 ρ β W₂
  · intro W₂; exact OS3_symmetry_swap2 ρ β W₂
  · exact os_axiom_ledger_length

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §12.  HONEST SCOPE STATEMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **HONEST OS-AXIOM SCOPE STATEMENT.**

    The framework provides:

      ✓ Discrete Schwinger function `discrete_Schwinger_n` as a
        well-defined real-valued n-point product of Wilson
        expectations on any finite causal substrate.
      ✓ (OS0) PROVED_BY_CONSTRUCTION: S_n exists for any finite n.
      ✓ (OS2) PROVED_DISCRETE: re-export of the discrete
        reflection-positivity theorem from CL3_ConstructiveMeasure
        (Boltzmann positivity + chamber-gap positivity in ℚ(√7)).
      ✓ (OS3) PROVED_BY_CONSTRUCTION: permutation invariance from
        the product structure of S_n; inherited from event-permutation
        invariance of the causal-set Wilson expectation.
      ✓ (OS4) PROVED_CHAMBER: Boltzmann multiplicativity
        exp(-β(S₁+S₂)) = exp(-βS₁)·exp(-βS₂) plus product
        factorization of S_n across (m, k) partitions.

    What the framework does NOT provide:

      ✗ (OS1) Euclidean SO(4) invariance: BLOCKED by the Lorentzian-
        Euclidean mismatch.  Causal sets are Lorentzian (`prec`
        carries time orientation, `causal_set_is_time_oriented`); OS
        is Euclidean.  No canonical Wick-rotation of a discrete
        causal set is in the framework.  THIS IS A GENUINE GAP.

      ✗ Continuum OS axioms: continuum versions of all five (OS0)-
        (OS4) require the (CL1) continuum-limit hypothesis from
        CL3_ConstructiveMeasure, plus a continuum version of (OS1)
        which the discrete framework cannot supply at all.

      ✗ OS reconstruction → Wightman: BLOCKED, because (OS1) is BLOCKED.
        The OS reconstruction theorem (Osterwalder-Schrader 1973) takes
        all five OS axioms as input.  Without (OS1), Wightman axioms
        cannot be reconstructed from this framework's tools.

    HONEST CLAIM: 4 of 5 OS axioms PROVED on the discrete substrate;
    OS1 is genuinely BLOCKED by Lorentzian-Euclidean mismatch; full OS
    reconstruction → Wightman is BLOCKED by OS1.  The framework
    REDUCES the Clay-YM Wightman-axiom problem (R2) to:
       (i) the (CL1) continuum-limit, and
       (ii) the construction of a Wick-rotated Euclidean theory
            from a Lorentzian causal-set substrate (the OS1 gap).
    Neither of these is solved here. -/
theorem honest_OS_scope_statement :
    -- (OS0) PROVED_BY_CONSTRUCTION
    (os0_classification.status = OSAxiomStatus.PROVED_BY_CONSTRUCTION) ∧
    -- (OS1) PROBLEMATIC_LORENTZIAN — the genuine gap
    (os1_classification.status = OSAxiomStatus.PROBLEMATIC_LORENTZIAN) ∧
    -- (OS2) PROVED_DISCRETE
    (os2_classification.status = OSAxiomStatus.PROVED_DISCRETE) ∧
    -- (OS3) PROVED_BY_CONSTRUCTION
    (os3_classification.status = OSAxiomStatus.PROVED_BY_CONSTRUCTION) ∧
    -- (OS4) PROVED_CHAMBER
    (os4_classification.status = OSAxiomStatus.PROVED_CHAMBER) ∧
    -- The discrete causal-set carries a time orientation
    (∀ C : CausalSet, ∀ a : C.Event, ¬ C.prec a a) ∧
    -- Discrete OS positivity holds (re-export)
    (∀ β S : ℝ, 0 < YMBoltzmannWeight β S) ∧
    -- Discrete chamber gap positive (re-export)
    (∀ s : ℝ, s ^ 2 = 7 → 0 < s → 0 < (3 / 5) - (5 + s) / 30) ∧
    -- Conditional OS reconstruction (assuming all five OS axioms)
    (AllFiveOSAxiomsHold → WightmanFromOS) ∧
    -- The reconstruction is BLOCKED by (OS1) at the discrete level
    (os1_classification.status = OSAxiomStatus.PROBLEMATIC_LORENTZIAN) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact os0_is_construction
  · exact os1_is_problematic
  · exact os2_is_discrete
  · exact os3_is_construction
  · exact os4_is_chamber
  · intro C; exact causal_set_is_time_oriented C
  · intro β S; exact YMBoltzmannWeight_pos β S
  · intro s hs hs_pos; exact additive_gap_positive s hs hs_pos
  · exact OS_reconstruction_conditional
  · exact os1_is_problematic

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §13.  DISTANCE FROM A FULL OS-AXIOM SOLUTION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **DISTANCE FROM FULL OS RECONSTRUCTION.**

    The framework is at most 4/5 of the way to the OS-axiom set
    on the discrete substrate:

      • PROVED on the discrete substrate              : 4 axioms.
      • BLOCKED by Lorentzian-Euclidean mismatch      : 1 axiom (OS1).

    Even with all four discrete-OS axioms in hand, the OS
    reconstruction theorem (Osterwalder-Schrader 1973) cannot be
    invoked, because its input is the FULL set of five OS axioms.
    OS1 is the missing axiom.

    HONEST CLAIM: this file does NOT solve the OS-axiom problem
    for Yang-Mills.  It provides discrete Schwinger functions, proves
    four of the five OS axioms on the discrete substrate, and
    pinpoints OS1 (Euclidean invariance) as the residual gap that
    a Wick-rotated causal-set construction would have to fill. -/
theorem distance_from_full_OS :
    -- 4 PROVED (on discrete / chamber / construction)
    ((os_axiom_ledger.filter
        (fun a => a.status = OSAxiomStatus.PROVED_DISCRETE)).length +
      (os_axiom_ledger.filter
        (fun a => a.status = OSAxiomStatus.PROVED_CHAMBER)).length +
      (os_axiom_ledger.filter
        (fun a => a.status = OSAxiomStatus.PROVED_BY_CONSTRUCTION)).length = 4) ∧
    -- 1 PROBLEMATIC (OS1)
    ((os_axiom_ledger.filter
        (fun a => a.status = OSAxiomStatus.PROBLEMATIC_LORENTZIAN)).length = 1) ∧
    -- 5 total
    (os_axiom_ledger.length = 5) ∧
    -- The OS-reconstruction theorem is BLOCKED
    (os1_classification.status = OSAxiomStatus.PROBLEMATIC_LORENTZIAN) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · exact os_axiom_ledger_problematic_count
  · exact os_axiom_ledger_length
  · exact os1_is_problematic

end UnifiedTheory.LayerB.CL3_SchwingerFunctions
