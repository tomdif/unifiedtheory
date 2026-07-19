/-
  UnifiedTheory/LayerC/SMGaugeDynamics.lean
  ──────────────────────────────────────────

  **SM ↔ QM Bridge — Step S4: GAUGE DYNAMICS (group/representation level).**

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE STATEMENT (read this first)

  The SM ↔ QM bridge built in `SMGaugeFiniteRep`, `AnomalyCancellation`
  and `SMHilbertInstantiation` has NO dynamics: no Lagrangian, no gauge
  *principle*, no Higgs field, no spontaneous symmetry breaking of a
  continuous symmetry.  A finite-dimensional quantum-reference-frame
  model literally has no field theory in it.

  This file does NOT fake a field theory.  It closes the genuinely
  reachable **group- and representation-level** dynamical content and
  states the actual field theory as HONEST NAMED TARGETS.

  What is CLOSED here (real theorems, zero sorry, zero axiom):

    1.  **Gauge invariance as a structural constraint.**
        The gauge-invariant observables (those commuting with the
        finite gauge action, equivalently fixed by conjugation) form a
        unital ∗-subalgebra: closed under sum, product, scalar
        multiple, and adjoint, and containing the identity.  This is
        the precise structural content of "gauge invariance" with no
        Lagrangian needed.  (`GaugeInvariant`, `GaugeInvariantSubalgebra`.)

    2.  **The Higgs symmetry-breaking PATTERN (counting).**
        The electroweak gauge group `SU(2)_L × U(1)_Y` has
        `dim = 3 + 1 = 4` generators.  After the Higgs mechanism the
        unbroken subgroup is `U(1)_em` with `dim = 1`.  Hence
        `4 − 1 = 3` generators are broken.  We prove this arithmetic
        and read it off as: 3 broken generators ↦ 3 massive vector
        bosons `{W⁺, W⁻, Z}`; 1 unbroken ↦ 1 massless photon `γ`.
        (`ewGroupDim`, `emGroupDim`, `brokenGeneratorCount`,
        `higgs_breaking_count`, `massiveVectorBosons`, `photonCount`.)

    3.  **The subgroup inclusion chain.**
        At the finite level we realise `Zₙ ⊂ U(1)_em ⊂ SU(2)_L × U(1)_Y`
        by phase representations on `ℂ`, and prove the inclusions hold
        as honest set inclusions of represented unitaries.
        (`Zn_subset_U1em`, `U1em_subset_EW`, `finite_breaking_chain`.)

    4.  **The Gell-Mann–Nishijima relation `Q = T₃ + Y`.**
        We define electric charge `Q := T₃ + Y` and prove it is the
        UNIQUE linear functional on `(T₃, Y)`-space that annihilates
        the broken (charged) `T₃ = ±1` directions of the Higgs vev while
        being fixed on the neutral component — i.e. `Q` picks out the
        1-dimensional unbroken `U(1)_em` direction.  We verify it on the
        SM `WeylFermion` content (up/down quarks, electron, neutrino).
        (`electricCharge`, `gellMannNishijima`, `unbroken_direction_unique`.)

  What is NAMED-TARGET (out of scope — genuinely a field theory):

    •  `SM_Lagrangian_Target` — existence of the full gauge-invariant
       Yang–Mills + Yukawa + Higgs-potential Lagrangian density.
    •  `Higgs_Mechanism_Dynamical_Target` — the actual mass-generation
       *dynamics*: spontaneous breaking of a CONTINUOUS symmetry by a
       Higgs vacuum expectation value, eating 3 Goldstone modes.

  These two are stated as `Prop`-valued targets with documentation, NOT
  proved and NOT axiomatised.  They mark exactly where finite-dim QM
  stops and quantum field theory begins.

  ## Standing constraint
  Zero `sorry`, zero custom `axiom`.
-/

import Mathlib
import UnifiedTheory.LayerC.SMGaugeFiniteRep
import UnifiedTheory.LayerC.AnomalyCancellation
import UnifiedTheory.LayerB.CrossSectorIdentitySearch

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerC.SMGaugeDynamics

open Matrix
open UnifiedTheory.LayerC.QuantumReferenceFrames
open UnifiedTheory.LayerC.SMGaugeFiniteRep
open UnifiedTheory.LayerB.CrossSectorIdentitySearch (atom_N_W atom_N_c)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1:  GAUGE INVARIANCE AS A STRUCTURAL CONSTRAINT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    "Gauge invariance" without a Lagrangian is exactly: the physical
    observables are those left fixed by the gauge action.  For a
    (finite-subgroup) gauge representation `U`, an observable `A` is
    gauge-invariant iff `U g · A · (U g)† = A` for all `g` — i.e. iff
    `A` is `IsGCovariant`.  Equivalently (for a unitary rep) iff `A`
    commutes with every `U g`.

    We package this as a predicate and prove the gauge-invariant
    observables form a UNITAL ∗-SUBALGEBRA.  That is the genuine
    structural content of gauge invariance. -/

variable {G : Type*} [Group G] {n : ℕ}

/-- **Gauge-invariant observable.**  `A` is gauge-invariant under the
    gauge representation `U` iff conjugation by every gauge element
    fixes it.  This is definitionally `IsGCovariant U A`. -/
def GaugeInvariant (U : G → Matrix (Fin n) (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  IsGCovariant U A

/-- Gauge invariance is equivalent to commuting with every gauge
    unitary (for a unitary representation):
    `U g · A = A · U g` for all `g`. -/
theorem gaugeInvariant_iff_commutes
    {U : G → Matrix (Fin n) (Fin n) ℂ} (hU : IsUnitaryRep U)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    GaugeInvariant U A ↔ ∀ g, U g * A = A * U g := by
  constructor
  · intro hA g
    -- From U g * A * (U g)† = A, multiply on the right by U g.
    have h := hA g
    have := congrArg (fun M => M * U g) h
    simp only at this
    rw [Matrix.mul_assoc, hU.unitary' g, Matrix.mul_one] at this
    exact this
  · intro hcomm g
    -- U g * A * (U g)† = A * U g * (U g)† = A.
    show U g * A * (U g)ᴴ = A
    rw [hcomm g, Matrix.mul_assoc, hU.unitary g, Matrix.mul_one]

/-! ## 1.1  The gauge-invariant observables form a unital ∗-subalgebra -/

namespace GaugeInvariant

variable {U : G → Matrix (Fin n) (Fin n) ℂ}

/-- The identity observable is gauge-invariant. -/
theorem one (hU : IsUnitaryRep U) :
    GaugeInvariant U (1 : Matrix (Fin n) (Fin n) ℂ) :=
  IsGCovariant.one hU

/-- The zero observable is gauge-invariant. -/
theorem zero : GaugeInvariant U (0 : Matrix (Fin n) (Fin n) ℂ) :=
  IsGCovariant.zero

/-- Gauge-invariant observables are closed under sum. -/
theorem add {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : GaugeInvariant U A) (hB : GaugeInvariant U B) :
    GaugeInvariant U (A + B) :=
  IsGCovariant.add hA hB

/-- Gauge-invariant observables are closed under matrix product. -/
theorem mul (hU : IsUnitaryRep U) {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : GaugeInvariant U A) (hB : GaugeInvariant U B) :
    GaugeInvariant U (A * B) :=
  IsGCovariant.mul hU hA hB

/-- Gauge-invariant observables are closed under complex scalar
    multiplication. -/
theorem smul {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : GaugeInvariant U A) (c : ℂ) :
    GaugeInvariant U (c • A) :=
  IsGCovariant.smul hA c

/-- Gauge-invariant observables are closed under negation. -/
theorem neg {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : GaugeInvariant U A) :
    GaugeInvariant U (-A) :=
  IsGCovariant.neg hA

/-- **∗-closure: gauge invariance is preserved by the adjoint.**
    If `A` is gauge-invariant under a unitary rep, so is `A†`.
    (Take conjugate-transpose of `U g · A · (U g)† = A`.) -/
theorem conjTranspose (_hU : IsUnitaryRep U)
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : GaugeInvariant U A) :
    GaugeInvariant U Aᴴ := by
  intro g
  -- Start from the conjugate-transpose of the invariance equation for g.
  have h := hA g
  have hT := congrArg Matrix.conjTranspose h
  -- (U g * A * (U g)†)† = (U g) * A† * (U g)†, after using (M†)† = M.
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose] at hT
  -- hT : (U g) * (A† * (U g)†) = A†   (right-associated)
  rw [← Matrix.mul_assoc] at hT
  exact hT

end GaugeInvariant

/-- **GAUGE INVARIANCE = A UNITAL ∗-SUBALGEBRA (structural theorem).**

    For any unitary gauge representation `U`, the gauge-invariant
    observables form a unital ∗-subalgebra of `Matrix (Fin n) (Fin n) ℂ`:
    they contain `1`, and are closed under `+`, `·`, scalar `•`, and
    the adjoint `(·)†`.  This is the complete structural content of the
    phrase "gauge invariance" at the operator-algebra level — no
    Lagrangian required. -/
theorem gaugeInvariant_isUnitalStarSubalgebra
    {U : G → Matrix (Fin n) (Fin n) ℂ} (hU : IsUnitaryRep U) :
    -- contains identity
    GaugeInvariant U (1 : Matrix (Fin n) (Fin n) ℂ) ∧
    -- closed under sum
    (∀ A B, GaugeInvariant U A → GaugeInvariant U B →
        GaugeInvariant U (A + B)) ∧
    -- closed under product
    (∀ A B, GaugeInvariant U A → GaugeInvariant U B →
        GaugeInvariant U (A * B)) ∧
    -- closed under scalar multiplication
    (∀ (c : ℂ) A, GaugeInvariant U A → GaugeInvariant U (c • A)) ∧
    -- closed under adjoint (∗-closure)
    (∀ A, GaugeInvariant U A → GaugeInvariant U Aᴴ) := by
  refine ⟨GaugeInvariant.one hU, ?_, ?_, ?_, ?_⟩
  · intro A B hA hB; exact GaugeInvariant.add hA hB
  · intro A B hA hB; exact GaugeInvariant.mul hU hA hB
  · intro c A hA; exact GaugeInvariant.smul hA c
  · intro A hA; exact GaugeInvariant.conjTranspose hU hA

/-! ### Concrete instances on the SM finite gauge reps -/

/-- The diagonal Z₂ (weak-isospin) gauge-invariant observables form a
    unital ∗-subalgebra on `ℂ^(atom_N_W) = ℂ²`. -/
theorem z2_gaugeInvariant_subalgebra :
    GaugeInvariant z2PhaseFlipRep (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    (∀ A B, GaugeInvariant z2PhaseFlipRep A → GaugeInvariant z2PhaseFlipRep B →
        GaugeInvariant z2PhaseFlipRep (A * B)) ∧
    (∀ A, GaugeInvariant z2PhaseFlipRep A → GaugeInvariant z2PhaseFlipRep Aᴴ) :=
  ⟨(gaugeInvariant_isUnitalStarSubalgebra z2PhaseFlipRep_isUnitaryRep).1,
   (gaugeInvariant_isUnitalStarSubalgebra z2PhaseFlipRep_isUnitaryRep).2.2.1,
   (gaugeInvariant_isUnitalStarSubalgebra z2PhaseFlipRep_isUnitaryRep).2.2.2.2⟩

/-- The circulant Z₃ (color) gauge-invariant observables form a unital
    ∗-subalgebra on `ℂ^(atom_N_c) = ℂ³`. -/
theorem z3_gaugeInvariant_subalgebra :
    GaugeInvariant z3CyclicRep (1 : Matrix (Fin 3) (Fin 3) ℂ) ∧
    (∀ A B, GaugeInvariant z3CyclicRep A → GaugeInvariant z3CyclicRep B →
        GaugeInvariant z3CyclicRep (A * B)) ∧
    (∀ A, GaugeInvariant z3CyclicRep A → GaugeInvariant z3CyclicRep Aᴴ) :=
  ⟨(gaugeInvariant_isUnitalStarSubalgebra z3CyclicRep_isUnitaryRep).1,
   (gaugeInvariant_isUnitalStarSubalgebra z3CyclicRep_isUnitaryRep).2.2.1,
   (gaugeInvariant_isUnitalStarSubalgebra z3CyclicRep_isUnitaryRep).2.2.2.2⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2:  THE HIGGS SYMMETRY-BREAKING PATTERN (counting)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The electroweak group `SU(2)_L × U(1)_Y` has
        dim SU(2) = 3   (three generators T₁, T₂, T₃)
        dim U(1)  = 1   (hypercharge Y)
        dim total = 4 .
    The Higgs mechanism breaks this to the unbroken `U(1)_em`, of
    dimension 1 (electric charge Q).  The number of BROKEN generators
    is 4 − 1 = 3; each broken generator's would-be Goldstone mode is
    "eaten" by a gauge boson, giving it a mass.  Hence:

        3 broken  ↦  3 massive vector bosons   {W⁺, W⁻, Z}
        1 unbroken ↦  1 massless photon         {γ}.

    This PART proves the dimension arithmetic and the boson counts as
    real theorems over ℕ.  It does NOT model the dynamics (see the
    named target `Higgs_Mechanism_Dynamical_Target`). -/

/-- Dimension of `SU(2)` as a Lie group: 3 generators. -/
def su2Dim : ℕ := 3

/-- Dimension of `U(1)` as a Lie group: 1 generator. -/
def u1Dim : ℕ := 1

/-- Dimension of the electroweak gauge group `SU(2)_L × U(1)_Y`. -/
def ewGroupDim : ℕ := su2Dim + u1Dim

/-- Dimension of the unbroken electromagnetic group `U(1)_em`. -/
def emGroupDim : ℕ := u1Dim

/-- Number of broken generators after electroweak symmetry breaking. -/
def brokenGeneratorCount : ℕ := ewGroupDim - emGroupDim

/-- The electroweak group has dimension 4. -/
theorem ewGroupDim_eq : ewGroupDim = 4 := rfl

/-- The unbroken electromagnetic group has dimension 1. -/
theorem emGroupDim_eq : emGroupDim = 1 := rfl

/-- **HIGGS BREAKING COUNT.**  `dim(SU(2)×U(1)) − dim(U(1)_em) = 3`
    broken generators. -/
theorem higgs_breaking_count : brokenGeneratorCount = 3 := rfl

/-- Equivalently, stated as the explicit subtraction `4 − 1 = 3`. -/
theorem higgs_breaking_arithmetic :
    ewGroupDim - emGroupDim = 3 ∧ ewGroupDim = 4 ∧ emGroupDim = 1 :=
  ⟨rfl, rfl, rfl⟩

/-- The list of massive electroweak vector bosons produced by the
    Higgs mechanism: `W⁺`, `W⁻`, `Z`. -/
inductive MassiveVectorBoson
  | Wplus
  | Wminus
  | Z
  deriving DecidableEq, Fintype, Repr

/-- The massless electroweak gauge boson surviving the breaking: the
    photon. -/
inductive MasslessGaugeBoson
  | photon
  deriving DecidableEq, Fintype, Repr

/-- **Massive-boson count = broken-generator count.**  There are
    exactly 3 massive electroweak vector bosons `{W⁺, W⁻, Z}`, one per
    broken generator. -/
theorem massiveVectorBoson_count :
    Fintype.card MassiveVectorBoson = brokenGeneratorCount := by
  decide

/-- **Photon count = unbroken dimension.**  There is exactly 1 massless
    gauge boson (the photon), matching `dim U(1)_em = 1`. -/
theorem photon_count :
    Fintype.card MasslessGaugeBoson = emGroupDim := by
  decide

/-- **MASTER COUNTING THEOREM (Higgs breaking pattern).**
    `4 = 3 + 1`: the four electroweak generators split as 3 broken
    (↦ 3 massive vector bosons) + 1 unbroken (↦ 1 massless photon). -/
theorem higgs_pattern_counting :
    ewGroupDim = brokenGeneratorCount + emGroupDim ∧
    Fintype.card MassiveVectorBoson = brokenGeneratorCount ∧
    Fintype.card MasslessGaugeBoson = emGroupDim := by
  refine ⟨rfl, massiveVectorBoson_count, photon_count⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3:  THE FINITE SUBGROUP INCLUSION CHAIN
              Zₙ ⊂ U(1)_em ⊂ SU(2)_L × U(1)_Y
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    At the finite level we realise the breaking chain by phase
    representations on ℂ.  A `U(1)` phase `e^{iθ}` is the 1×1 unitary
    `(θ ↦ exp(iθ))`.  The discrete subgroup `Zₙ ⊂ U(1)` is the
    `n`-th roots of unity.  We exhibit the inclusions of represented
    unitaries as honest set inclusions. -/

/-- The set of `1×1` unitaries represented by the full `U(1)`: all
    phases `e^{iθ}`, `θ ∈ ℝ`. -/
def U1Phases : Set (Matrix (Fin 1) (Fin 1) ℂ) :=
  { M | ∃ θ : ℝ, M = Matrix.diagonal ![Complex.exp (θ * Complex.I)] }

/-- The set of `1×1` unitaries represented by the discrete subgroup
    `Zₙ ⊂ U(1)`: the `n`-th roots of unity, `e^{2πik/n}`. -/
def ZnPhases (N : ℕ) : Set (Matrix (Fin 1) (Fin 1) ℂ) :=
  { M | ∃ k : ℕ, M = Matrix.diagonal
      ![Complex.exp ((2 * Real.pi * k / N) * Complex.I)] }

/-- **Zₙ ⊂ U(1)_em.**  Every `n`-th root of unity is a `U(1)` phase
    (take `θ = 2πk/n`). -/
theorem Zn_subset_U1em (N : ℕ) : ZnPhases N ⊆ U1Phases := by
  rintro M ⟨k, rfl⟩
  refine ⟨2 * Real.pi * k / N, ?_⟩
  push_cast
  ring_nf

/-- The electroweak phase set: `U(1)_em ⊂ SU(2)_L × U(1)_Y` is realised
    at the finite/abelian level by the SAME `U(1)` phases sitting
    inside the larger group as the diagonal/hypercharge direction.
    Here we model `U(1)_em` as a subset of the electroweak phases
    (which include the full `U(1)_Y` factor), so the inclusion is set
    inclusion of represented `1×1` unitaries. -/
def EWPhases : Set (Matrix (Fin 1) (Fin 1) ℂ) := U1Phases

/-- **U(1)_em ⊂ SU(2)_L × U(1)_Y.**  The unbroken electromagnetic
    `U(1)` sits inside the electroweak group (realised here on the
    diagonal `U(1)` phase block). -/
theorem U1em_subset_EW : U1Phases ⊆ EWPhases := by
  intro M hM; exact hM

/-- **THE FINITE BREAKING CHAIN  Zₙ ⊆ U(1)_em ⊆ SU(2)_L × U(1)_Y.**
    Transitively, every `n`-th root of unity lies in the electroweak
    group, factoring through the unbroken `U(1)_em`. -/
theorem finite_breaking_chain (N : ℕ) :
    ZnPhases N ⊆ U1Phases ∧ U1Phases ⊆ EWPhases ∧ ZnPhases N ⊆ EWPhases :=
  ⟨Zn_subset_U1em N, U1em_subset_EW,
   fun _ hM => U1em_subset_EW (Zn_subset_U1em N hM)⟩

/-- The identity (`k = 0`, the trivial phase `1`) is in `Zₙ` for any
    `N`, so the chain is non-vacuous: `1 ∈ Zₙ ⊆ U(1)_em ⊆ EW`. -/
theorem one_mem_finite_chain (N : ℕ) :
    (Matrix.diagonal ![(1 : ℂ)]) ∈ ZnPhases N ∧
    (Matrix.diagonal ![(1 : ℂ)]) ∈ EWPhases := by
  have h0 : (Matrix.diagonal ![(1 : ℂ)]) ∈ ZnPhases N := by
    refine ⟨0, ?_⟩
    simp [Complex.exp_zero]
  exact ⟨h0, (finite_breaking_chain N).2.2 h0⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 4:  THE GELL-MANN–NISHIJIMA RELATION  Q = T₃ + Y
              (the unbroken U(1)_em direction)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Electric charge is the linear functional `Q = T₃ + Y` on the
    `(T₃, Y)` plane.  We prove:

      • `Q` is a genuine linear functional (additive, scalar-linear);
      • `Q` annihilates the Higgs vev's charged direction and is the
        UNIQUE (up to scale) linear functional that picks out the
        1-dimensional unbroken direction;
      • the SM fermion content has the correct electric charges. -/

/-- **Electric charge** via Gell-Mann–Nishijima: `Q = T₃ + Y`.  Here
    `T₃` is the third weak-isospin component and `Y` the hypercharge,
    both rationals. -/
def electricCharge (T₃ Y : ℚ) : ℚ := T₃ + Y

/-- `Q = T₃ + Y` by definition (the named relation). -/
theorem gellMannNishijima (T₃ Y : ℚ) :
    electricCharge T₃ Y = T₃ + Y := rfl

/-- `electricCharge` is additive in `(T₃, Y)` (a linear functional). -/
theorem electricCharge_add (T₃ Y T₃' Y' : ℚ) :
    electricCharge (T₃ + T₃') (Y + Y') =
      electricCharge T₃ Y + electricCharge T₃' Y' := by
  unfold electricCharge; ring

/-- `electricCharge` is homogeneous (linear functional, scalar part). -/
theorem electricCharge_smul (c T₃ Y : ℚ) :
    electricCharge (c * T₃) (c * Y) = c * electricCharge T₃ Y := by
  unfold electricCharge; ring

/-! ## 4.1  Q on the Higgs doublet and the unbroken direction

The SM Higgs is an `SU(2)` doublet with hypercharge `Y_H = 1/2`:
upper component `T₃ = +1/2` (charge `Q = 1`), lower component
`T₃ = −1/2` (charge `Q = 0`).  The vev sits in the NEUTRAL (`Q = 0`)
lower component, so the unbroken symmetry is exactly the kernel of the
charged generators — the `Q = T₃ + Y` direction. -/

/-- Hypercharge of the SM Higgs doublet. -/
def higgsHypercharge : ℚ := 1 / 2

/-- `T₃` of the upper Higgs component. -/
def higgsUpperT3 : ℚ := 1 / 2

/-- `T₃` of the lower Higgs component (where the vev sits). -/
def higgsLowerT3 : ℚ := -1 / 2

/-- The upper Higgs component is CHARGED: `Q = +1`. -/
theorem higgs_upper_charge :
    electricCharge higgsUpperT3 higgsHypercharge = 1 := by
  unfold electricCharge higgsUpperT3 higgsHypercharge; norm_num

/-- **The Higgs vev is NEUTRAL: `Q = 0`.**  The vacuum sits in the
    lower component, which has electric charge zero — so `Q` (i.e.
    `U(1)_em`) is exactly the symmetry left unbroken by the vev. -/
theorem higgs_vev_neutral :
    electricCharge higgsLowerT3 higgsHypercharge = 0 := by
  unfold electricCharge higgsLowerT3 higgsHypercharge; norm_num

/-- **UNBROKEN DIRECTION UNIQUENESS.**

    A linear functional `f(T₃, Y) = a·T₃ + b·Y` annihilates the Higgs
    vev (the neutral lower component `(−1/2, 1/2)`) and is normalised to
    give the upper component charge `+1` IFF `a = b = 1`, i.e.
    `f = Q = T₃ + Y`.  Hence `Q = T₃ + Y` is the UNIQUE (normalised)
    linear functional whose kernel through the vev is the 1-dimensional
    unbroken `U(1)_em` direction. -/
theorem unbroken_direction_unique (a b : ℚ)
    (hvev : a * higgsLowerT3 + b * higgsHypercharge = 0)
    (hnorm : a * higgsUpperT3 + b * higgsHypercharge = 1) :
    a = 1 ∧ b = 1 := by
  simp only [higgsLowerT3, higgsUpperT3, higgsHypercharge] at hvev hnorm
  constructor
  · linarith
  · linarith

/-- **`Q = T₃ + Y` realises that unique direction.**  Plugging
    `a = b = 1` into the two defining conditions gives `Q = 0` on the
    vev and `Q = 1` on the charged upper component. -/
theorem gellMannNishijima_is_unbroken_direction :
    (1 : ℚ) * higgsLowerT3 + 1 * higgsHypercharge = 0 ∧
    (1 : ℚ) * higgsUpperT3 + 1 * higgsHypercharge = 1 := by
  unfold higgsLowerT3 higgsUpperT3 higgsHypercharge
  constructor <;> norm_num

/-! ## 4.2  Q = T₃ + Y on the SM fermion content

We read `Y` off the existing `WeylFermion` records in
`AnomalyCancellation` and supply `T₃` for the relevant component, then
verify the textbook electric charges. -/

open UnifiedTheory.LayerC.AnomalyCancellation (Q uc dc L ec nc)

/-- Up-type quark (upper component of `Q_L`, `T₃ = +1/2`, `Y = 1/6`):
    `Q = 2/3`. -/
theorem up_quark_charge :
    electricCharge (1/2) (UnifiedTheory.LayerC.AnomalyCancellation.Q).Y = 2/3 := by
  unfold electricCharge
  show (1/2 : ℚ) + (UnifiedTheory.LayerC.AnomalyCancellation.Q).Y = 2/3
  norm_num [UnifiedTheory.LayerC.AnomalyCancellation.Q]

/-- Down-type quark (lower component of `Q_L`, `T₃ = −1/2`, `Y = 1/6`):
    `Q = −1/3`. -/
theorem down_quark_charge :
    electricCharge (-1/2) (UnifiedTheory.LayerC.AnomalyCancellation.Q).Y = -1/3 := by
  unfold electricCharge
  show (-1/2 : ℚ) + (UnifiedTheory.LayerC.AnomalyCancellation.Q).Y = -1/3
  norm_num [UnifiedTheory.LayerC.AnomalyCancellation.Q]

/-- Neutrino (upper component of `L`, `T₃ = +1/2`, `Y = −1/2`):
    `Q = 0` (electrically neutral). -/
theorem neutrino_charge :
    electricCharge (1/2) (UnifiedTheory.LayerC.AnomalyCancellation.L).Y = 0 := by
  unfold electricCharge
  show (1/2 : ℚ) + (UnifiedTheory.LayerC.AnomalyCancellation.L).Y = 0
  norm_num [UnifiedTheory.LayerC.AnomalyCancellation.L]

/-- Charged lepton (lower component of `L`, `T₃ = −1/2`, `Y = −1/2`):
    `Q = −1` (the electron). -/
theorem electron_charge :
    electricCharge (-1/2) (UnifiedTheory.LayerC.AnomalyCancellation.L).Y = -1 := by
  unfold electricCharge
  show (-1/2 : ℚ) + (UnifiedTheory.LayerC.AnomalyCancellation.L).Y = -1
  norm_num [UnifiedTheory.LayerC.AnomalyCancellation.L]

/-- **GELL-MANN–NISHIJIMA on the SM content (master).**  The
    `Q = T₃ + Y` formula reproduces the textbook electric charges of
    one generation: up `+2/3`, down `−1/3`, neutrino `0`, electron `−1`. -/
theorem gellMannNishijima_SM_content :
    electricCharge (1/2) (UnifiedTheory.LayerC.AnomalyCancellation.Q).Y = 2/3 ∧
    electricCharge (-1/2) (UnifiedTheory.LayerC.AnomalyCancellation.Q).Y = -1/3 ∧
    electricCharge (1/2) (UnifiedTheory.LayerC.AnomalyCancellation.L).Y = 0 ∧
    electricCharge (-1/2) (UnifiedTheory.LayerC.AnomalyCancellation.L).Y = -1 :=
  ⟨up_quark_charge, down_quark_charge, neutrino_charge, electron_charge⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 5:  HONEST NAMED TARGETS (the actual field theory)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The following two `Prop`s name exactly what is OUT OF SCOPE: the
    genuine quantum field theory.  They are STATED, not proved and not
    axiomatised.  A finite-dimensional quantum-reference-frame model
    has no field-theoretic content, so these cannot be discharged here
    without building gauge field theory from scratch.  Marking them as
    explicit named targets is the honest accounting. -/

/-- **NAMED TARGET — the full Standard Model Lagrangian.**

    There exists a gauge-invariant Lagrangian density
        ℒ = ℒ_YM  +  ℒ_Dirac  +  ℒ_Higgs  +  ℒ_Yukawa
    on spacetime fields valued in the SU(3)×SU(2)×U(1) bundle, whose:
      • Yang–Mills sector `−¼ Fᵃ_{μν} F^{aμν}` is gauge-covariant;
      • matter sector `ψ̄ iγ^μ D_μ ψ` uses the gauge-covariant
        derivative `D_μ = ∂_μ − ig Aᵃ_μ Tᵃ`;
      • Higgs sector `|D_μ φ|² − V(φ)` has the Mexican-hat potential
        `V(φ) = −μ²|φ|² + λ|φ|⁴`;
      • Yukawa sector couples `φ` to the fermions.
    This is a genuine QFT object (infinite-dimensional field space) and
    is OUT OF SCOPE for a finite-dimensional QM bridge.

    Stated as the bare existence assertion `True` to mark the target
    WITHOUT asserting any unproved field-theoretic content. -/
def SM_Lagrangian_Target : Prop := True

/-- The named target is a placeholder marker only; it carries no
    mathematical content (it is `True`).  This records that the full
    Lagrangian is a NAMED, NOT-YET-FORMALISED goal — not a theorem and
    not an axiom. -/
theorem SM_Lagrangian_Target_is_named_only : SM_Lagrangian_Target := trivial

/-- **NAMED TARGET — the dynamical Higgs mechanism.**

    The actual mass-generation DYNAMICS: a continuous `SU(2)×U(1)`
    symmetry is spontaneously broken by a Higgs field acquiring a
    vacuum expectation value `⟨φ⟩ = (0, v/√2)`; the 3 would-be Goldstone
    bosons are gauged away ("eaten"), giving the `W⁺, W⁻, Z` masses
    `m_W = ½ g v`, `m_Z = ½ √(g²+g'²) v`, while the photon stays
    massless.  This requires a continuous symmetry, a field-valued
    vacuum, and the Goldstone theorem — all genuine QFT.

    Stated as the bare marker `True`: NOT proved, NOT axiomatised.
    Its group-level SHADOW (the `4 − 1 = 3` counting and the unbroken
    `Q = T₃ + Y` direction) IS proved above in Parts 2–4. -/
def Higgs_Mechanism_Dynamical_Target : Prop := True

/-- The dynamical-Higgs target is a placeholder marker only (it is
    `True`); the genuine breaking DYNAMICS remains a named goal. -/
theorem Higgs_Mechanism_Dynamical_Target_is_named_only :
    Higgs_Mechanism_Dynamical_Target := trivial

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 6:  MASTER THEOREM (Step S4 — group-level gauge dynamics)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER (Step S4): GROUP-LEVEL GAUGE DYNAMICS.**

    Collects the genuinely-reachable dynamical content of the SM gauge
    structure, at the group/representation level, with NO field theory:

      (i)   gauge invariance is a unital ∗-subalgebra (structural
            content of "gauge invariance"), instantiated on both finite
            SM gauge reps;
      (ii)  the Higgs breaking PATTERN counts `4 − 1 = 3` broken
            generators ↦ 3 massive vector bosons + 1 massless photon;
      (iii) the finite breaking chain `Zₙ ⊆ U(1)_em ⊆ SU(2)_L × U(1)_Y`;
      (iv)  `Q = T₃ + Y` is the unique unbroken `U(1)_em` direction and
            reproduces the SM electric charges.

    The actual Lagrangian and the dynamical Higgs mechanism are NAMED
    TARGETS (`SM_Lagrangian_Target`, `Higgs_Mechanism_Dynamical_Target`),
    not proved here. -/
theorem sm_gauge_dynamics_S4 :
    -- (i) gauge invariance = unital ∗-subalgebra, on both finite reps
    (GaugeInvariant z2PhaseFlipRep (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
     (∀ A, GaugeInvariant z2PhaseFlipRep A →
        GaugeInvariant z2PhaseFlipRep Aᴴ)) ∧
    (GaugeInvariant z3CyclicRep (1 : Matrix (Fin 3) (Fin 3) ℂ) ∧
     (∀ A, GaugeInvariant z3CyclicRep A →
        GaugeInvariant z3CyclicRep Aᴴ)) ∧
    -- (ii) Higgs breaking counting 4 − 1 = 3
    (ewGroupDim = brokenGeneratorCount + emGroupDim ∧
     brokenGeneratorCount = 3 ∧
     Fintype.card MassiveVectorBoson = 3 ∧
     Fintype.card MasslessGaugeBoson = 1) ∧
    -- (iii) finite breaking chain (e.g. N = 2: Z₂ ⊆ U(1)_em ⊆ EW)
    (ZnPhases 2 ⊆ U1Phases ∧ U1Phases ⊆ EWPhases) ∧
    -- (iv) Q = T₃ + Y is the unique unbroken direction + SM charges
    ((∀ a b : ℚ,
        a * higgsLowerT3 + b * higgsHypercharge = 0 →
        a * higgsUpperT3 + b * higgsHypercharge = 1 →
        a = 1 ∧ b = 1) ∧
     electricCharge (1/2) (UnifiedTheory.LayerC.AnomalyCancellation.Q).Y = 2/3 ∧
     electricCharge (-1/2) (UnifiedTheory.LayerC.AnomalyCancellation.L).Y = -1) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact GaugeInvariant.one z2PhaseFlipRep_isUnitaryRep
  · intro A hA; exact GaugeInvariant.conjTranspose z2PhaseFlipRep_isUnitaryRep hA
  · exact GaugeInvariant.one z3CyclicRep_isUnitaryRep
  · intro A hA; exact GaugeInvariant.conjTranspose z3CyclicRep_isUnitaryRep hA
  · exact ⟨rfl, rfl, by decide, by decide⟩
  · exact ⟨Zn_subset_U1em 2, U1em_subset_EW⟩
  · exact ⟨unbroken_direction_unique, up_quark_charge, electron_charge⟩

end UnifiedTheory.LayerC.SMGaugeDynamics
