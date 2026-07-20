/-
  Audit/KFCausalSetWeakHandednessBridge.lean

  FROM CAUSAL ORIENTATION TO A WEYL-PROJECTED WEAK VERTEX

  This module closes the finite algebraic part of the bridge from the causal-set
  orientation channel to a standard chiral weak vertex.  It does four things.

  * It constructs an explicit two-Weyl-sector Dirac space with the standard
    gamma-five grading, P_L = (1-gamma-five)/2 and P_R = (1+gamma-five)/2.
  * It constructs the standard complexified su(2) doublet generators and proves
    their commutators.
  * It locks the weak projector to the cylinder orientation sign by

        P_weak(Xi) = (1-Xi gamma-five)/2.

    Xi=+1 gives P_L and Xi=-1 gives P_R.  The resulting vertex is exactly
    transported by every projective refinement.
  * It proves parity covariance: reflection flips both Xi and gamma-five, so
    their product, and hence the relationally left-handed interaction, is
    unchanged.

  The result is deliberately scoped.  Positive relational chirality gives a
  nonzero weak vertex that annihilates every right-handed state at every
  refinement depth.  The reflected datum gives the mirror theorem.  The
  preceding no-go theorem still says that the present reflection-fixed vacuum
  cannot choose one member of this pair.  Thus this is a derivation of
  left-handedness conditional only on a nonzero oriented branch, not yet a
  derivation that the symmetric vacuum dynamically chooses nature's branch.

  Zero sorry.  Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetChiralityGenerationNoGo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetWeakHandednessBridge

noncomputable section

open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalSetOrientationRestriction
open UnifiedTheory.Audit.KFCausalSetChiralGrowth
open UnifiedTheory.Audit.KFCausalSetMicroscopicSpectatorAction
open UnifiedTheory.Audit.KFCausalSetRelationalChiralitySelection
open UnifiedTheory.Audit.KFCausalSetChiralityGenerationNoGo
open UnifiedTheory.Audit.KFOrientationInfiniteCylinderDecoherence

/-! ## 1. An explicit gamma-five grading -/

/-- The defining two-dimensional representation of the complexified weak
algebra. -/
abbrev WeakDoublet := Fin 2 → ℂ

/-- A two-component Weyl spinor carrying a weak doublet.  The first index is
the Lorentz/Weyl spin index; the second is weak isospin. -/
abbrev WeylWeakDoublet := Fin 2 → WeakDoublet

/-- A Dirac chirality pair of Weyl spinors, each carrying a weak doublet.
The three indices are chirality, Weyl-spin, and weak-isospin respectively.
Chirality slot zero is the standard left Weyl sector and slot one the standard
right Weyl sector. -/
abbrev DiracWeakSpinor := Fin 2 → WeylWeakDoublet

/-- Standard gamma-five convention: eigenvalue `-1` on left Weyl spinors and
`+1` on right Weyl spinors. -/
def gammaFive (psi : DiracWeakSpinor) : DiracWeakSpinor :=
  fun chirality spin isospin ↦
    if chirality = 0 then -psi chirality spin isospin
    else psi chirality spin isospin

/-- Standard left Weyl projector. -/
def leftWeylProjector (psi : DiracWeakSpinor) : DiracWeakSpinor :=
  fun chirality spin isospin ↦
    if chirality = 0 then psi chirality spin isospin else 0

/-- Standard right Weyl projector. -/
def rightWeylProjector (psi : DiracWeakSpinor) : DiracWeakSpinor :=
  fun chirality spin isospin ↦
    if chirality = 0 then 0 else psi chirality spin isospin

theorem gammaFive_involutive (psi : DiracWeakSpinor) :
    gammaFive (gammaFive psi) = psi := by
  ext chirality spin isospin
  fin_cases chirality <;> simp [gammaFive]

theorem leftWeylProjector_formula (psi : DiracWeakSpinor) :
    leftWeylProjector psi = fun chirality spin isospin ↦
      (1 / 2 : ℂ) *
        (psi chirality spin isospin - gammaFive psi chirality spin isospin) := by
  ext chirality spin isospin
  fin_cases chirality <;>
    simp [leftWeylProjector, gammaFive] <;> ring

theorem rightWeylProjector_formula (psi : DiracWeakSpinor) :
    rightWeylProjector psi = fun chirality spin isospin ↦
      (1 / 2 : ℂ) *
        (psi chirality spin isospin + gammaFive psi chirality spin isospin) := by
  ext chirality spin isospin
  fin_cases chirality <;>
    simp [rightWeylProjector, gammaFive] <;> ring

theorem leftWeylProjector_idempotent (psi : DiracWeakSpinor) :
    leftWeylProjector (leftWeylProjector psi) = leftWeylProjector psi := by
  ext chirality spin isospin
  fin_cases chirality <;> simp [leftWeylProjector]

theorem rightWeylProjector_idempotent (psi : DiracWeakSpinor) :
    rightWeylProjector (rightWeylProjector psi) = rightWeylProjector psi := by
  ext chirality spin isospin
  fin_cases chirality <;> simp [rightWeylProjector]

theorem weylProjectors_complementary (psi : DiracWeakSpinor) :
    (fun chirality spin isospin ↦
      leftWeylProjector psi chirality spin isospin +
        rightWeylProjector psi chirality spin isospin) = psi := by
  ext chirality spin isospin
  fin_cases chirality <;>
    simp [leftWeylProjector, rightWeylProjector]

theorem weylProjectors_orthogonal_left_right (psi : DiracWeakSpinor) :
    leftWeylProjector (rightWeylProjector psi) = 0 := by
  ext chirality spin isospin
  fin_cases chirality <;>
    simp [leftWeylProjector, rightWeylProjector]

theorem weylProjectors_orthogonal_right_left (psi : DiracWeakSpinor) :
    rightWeylProjector (leftWeylProjector psi) = 0 := by
  ext chirality spin isospin
  fin_cases chirality <;>
    simp [leftWeylProjector, rightWeylProjector]

/-! ## 2. The complexified su(2) weak generators -/

/-- Weak-isospin raising generator `T+`. -/
def weakRaising : WeakDoublet →ₗ[ℂ] WeakDoublet where
  toFun doublet isospin := if isospin = 0 then doublet 1 else 0
  map_add' first second := by
    ext isospin
    fin_cases isospin <;> simp
  map_smul' scalar doublet := by
    ext isospin
    fin_cases isospin <;> simp

/-- Weak-isospin lowering generator `T-`. -/
def weakLowering : WeakDoublet →ₗ[ℂ] WeakDoublet where
  toFun doublet isospin := if isospin = 0 then 0 else doublet 0
  map_add' first second := by
    ext isospin
    fin_cases isospin <;> simp
  map_smul' scalar doublet := by
    ext isospin
    fin_cases isospin <;> simp

/-- The Cartan generator `T3=diag(1/2,-1/2)`. -/
def weakThird : WeakDoublet →ₗ[ℂ] WeakDoublet where
  toFun doublet isospin :=
    if isospin = 0 then (1 / 2 : ℂ) * doublet 0
    else -(1 / 2 : ℂ) * doublet 1
  map_add' first second := by
    ext isospin
    fin_cases isospin <;> simp <;> ring
  map_smul' scalar doublet := by
    ext isospin
    fin_cases isospin <;> simp <;> ring

/-- `[T3,T+] = T+`. -/
theorem weakThird_raising_commutator :
    weakThird.comp weakRaising - weakRaising.comp weakThird = weakRaising := by
  apply LinearMap.ext
  intro doublet
  ext isospin
  fin_cases isospin <;>
    simp [weakThird, weakRaising, LinearMap.comp_apply] <;> ring

/-- `[T3,T-] = -T-`. -/
theorem weakThird_lowering_commutator :
    weakThird.comp weakLowering - weakLowering.comp weakThird = -weakLowering := by
  apply LinearMap.ext
  intro doublet
  ext isospin
  fin_cases isospin <;>
    simp [weakThird, weakLowering, LinearMap.comp_apply] <;> ring

/-- `[T+,T-] = 2T3`.  These three exact relations identify the standard
complexified `su(2)`/`sl(2)` weak-doublet representation. -/
theorem weakRaising_lowering_commutator :
    weakRaising.comp weakLowering - weakLowering.comp weakRaising =
      (2 : ℂ) • weakThird := by
  apply LinearMap.ext
  intro doublet
  ext isospin
  fin_cases isospin <;>
    simp [weakThird, weakRaising, weakLowering, LinearMap.comp_apply]

/-! ## 3. Causal-orientation locking of the Weyl projector -/

/-- The causal Weyl projector

`P_weak(Xi) = (1-Xi gammaFive)/2`.

For a pure cylinder endpoint `Xi` is exactly `+1` or `-1`. -/
def causalWeylProjector (xi : ℝ) (psi : DiracWeakSpinor) :
    DiracWeakSpinor :=
  fun chirality spin isospin ↦
    (1 / 2 : ℂ) *
      (psi chirality spin isospin -
        (xi : ℂ) * gammaFive psi chirality spin isospin)

theorem causalWeylProjector_one (psi : DiracWeakSpinor) :
    causalWeylProjector 1 psi = leftWeylProjector psi := by
  rw [leftWeylProjector_formula]
  ext chirality spin isospin
  simp [causalWeylProjector]

theorem causalWeylProjector_neg_one (psi : DiracWeakSpinor) :
    causalWeylProjector (-1) psi = rightWeylProjector psi := by
  rw [rightWeylProjector_formula]
  ext chirality spin isospin
  simp [causalWeylProjector]

/-- Gamma five has eigenvalue `-1` on the image of the left projector. -/
theorem gammaFive_leftWeylProjector (psi : DiracWeakSpinor) :
    gammaFive (leftWeylProjector psi) =
      fun chirality spin isospin ↦
        -leftWeylProjector psi chirality spin isospin := by
  ext chirality spin isospin
  fin_cases chirality <;>
    simp [gammaFive, leftWeylProjector]

/-- Gamma five has eigenvalue `+1` on the image of the right projector. -/
theorem gammaFive_rightWeylProjector (psi : DiracWeakSpinor) :
    gammaFive (rightWeylProjector psi) = rightWeylProjector psi := by
  ext chirality spin isospin
  fin_cases chirality <;>
    simp [gammaFive, rightWeylProjector]

/-- Gamma five measured relative to the causal orientation. -/
def relativeGammaFive (xi : ℝ) (psi : DiracWeakSpinor) :
    DiracWeakSpinor :=
  fun chirality spin isospin ↦
    (xi : ℂ) * gammaFive psi chirality spin isospin

/-- The causally selected projector always lands in the relative `-1`
eigenspace.  Thus either absolute branch is left-handed relative to its own
causal orientation. -/
theorem causalWeylProjector_is_relative_left
    (xi : ℝ) (hSign : xi = 1 ∨ xi = -1) (psi : DiracWeakSpinor) :
    relativeGammaFive xi (causalWeylProjector xi psi) =
      fun chirality spin isospin ↦
        -causalWeylProjector xi psi chirality spin isospin := by
  rcases hSign with rfl | rfl
  · rw [causalWeylProjector_one]
    ext chirality spin isospin
    rw [show relativeGammaFive 1 (leftWeylProjector psi) chirality spin isospin =
        gammaFive (leftWeylProjector psi) chirality spin isospin by
      simp [relativeGammaFive]]
    rw [gammaFive_leftWeylProjector]
  · rw [causalWeylProjector_neg_one]
    ext chirality spin isospin
    simp [relativeGammaFive, gammaFive_rightWeylProjector]

/-- The two scalar response conditions for an affine function of a grading
determine its coefficients uniquely.  Acting as identity on eigenvalue `-1`
and as zero on eigenvalue `+1` forces `(1-G)/2`. -/
theorem affine_relative_left_coefficients_unique
    (a b : ℂ) (hMinus : a - b = 1) (hPlus : a + b = 0) :
    a = 1 / 2 ∧ b = -1 / 2 := by
  constructor
  · calc
      a = (1 / 2 : ℂ) * ((a - b) + (a + b)) := by ring
      _ = 1 / 2 := by rw [hMinus, hPlus]; ring
  · calc
      b = (1 / 2 : ℂ) * ((a + b) - (a - b)) := by ring
      _ = -1 / 2 := by rw [hMinus, hPlus]; ring

/-- **Uniqueness of the locking law within the affine grading algebra.**
Any affine response `a I + b (Xi gamma-five)` that retains the relative-left
eigenspace and kills the relative-right eigenspace is exactly the causal Weyl
projector. -/
theorem causalWeylProjector_unique_affine
    (a b : ℂ) (hMinus : a - b = 1) (hPlus : a + b = 0)
    (xi : ℝ) (psi : DiracWeakSpinor) :
    (fun chirality spin isospin ↦
      a * psi chirality spin isospin +
        b * relativeGammaFive xi psi chirality spin isospin) =
      causalWeylProjector xi psi := by
  obtain ⟨rfl, rfl⟩ :=
    affine_relative_left_coefficients_unique a b hMinus hPlus
  ext chirality spin isospin
  simp [causalWeylProjector, relativeGammaFive]
  ring

theorem causalWeylProjector_idempotent_of_sign
    (xi : ℝ) (hSign : xi = 1 ∨ xi = -1) (psi : DiracWeakSpinor) :
    causalWeylProjector xi (causalWeylProjector xi psi) =
      causalWeylProjector xi psi := by
  rcases hSign with rfl | rfl
  · rw [causalWeylProjector_one, causalWeylProjector_one,
      leftWeylProjector_idempotent]
  · rw [causalWeylProjector_neg_one, causalWeylProjector_neg_one,
      rightWeylProjector_idempotent]

/-- Parity exchanges the two Weyl sectors. -/
def spinorReflection (psi : DiracWeakSpinor) : DiracWeakSpinor :=
  fun chirality spin isospin ↦
    if chirality = 0 then psi 1 spin isospin else psi 0 spin isospin

theorem spinorReflection_involutive (psi : DiracWeakSpinor) :
    spinorReflection (spinorReflection psi) = psi := by
  ext chirality spin isospin
  fin_cases chirality <;> simp [spinorReflection]

/-- Parity anticommutes with the gamma-five grading. -/
theorem gammaFive_spinorReflection (psi : DiracWeakSpinor) :
    gammaFive (spinorReflection psi) =
      fun chirality spin isospin ↦
        -spinorReflection (gammaFive psi) chirality spin isospin := by
  ext chirality spin isospin
  fin_cases chirality <;>
    simp [gammaFive, spinorReflection]

/-- The causal projector is parity covariant because both the orientation sign
and gamma-five reverse. -/
theorem causalWeylProjector_reflection
    (xi : ℝ) (psi : DiracWeakSpinor) :
    causalWeylProjector (-xi) (spinorReflection psi) =
      spinorReflection (causalWeylProjector xi psi) := by
  ext chirality spin isospin
  fin_cases chirality <;>
    simp [causalWeylProjector, gammaFive, spinorReflection]

/-! ## 4. Weak vertices and exact handedness -/

/-- Lift a weak-doublet generator to both Weyl sectors. -/
def liftWeakGenerator (generator : WeakDoublet →ₗ[ℂ] WeakDoublet)
    (psi : DiracWeakSpinor) : DiracWeakSpinor :=
  fun chirality spin ↦ generator (psi chirality spin)

/-- The weak vertex obtained after causal-orientation projection. -/
def causalWeakVertex (xi : ℝ)
    (generator : WeakDoublet →ₗ[ℂ] WeakDoublet)
    (psi : DiracWeakSpinor) : DiracWeakSpinor :=
  liftWeakGenerator generator (causalWeylProjector xi psi)

/-- Standard left-projected weak vertex. -/
def leftWeakVertex (generator : WeakDoublet →ₗ[ℂ] WeakDoublet)
    (psi : DiracWeakSpinor) : DiracWeakSpinor :=
  liftWeakGenerator generator (leftWeylProjector psi)

/-- Mirror right-projected weak vertex. -/
def rightWeakVertex (generator : WeakDoublet →ₗ[ℂ] WeakDoublet)
    (psi : DiracWeakSpinor) : DiracWeakSpinor :=
  liftWeakGenerator generator (rightWeylProjector psi)

theorem causalWeakVertex_one
    (generator : WeakDoublet →ₗ[ℂ] WeakDoublet)
    (psi : DiracWeakSpinor) :
    causalWeakVertex 1 generator psi = leftWeakVertex generator psi := by
  simp [causalWeakVertex, leftWeakVertex, causalWeylProjector_one]

theorem causalWeakVertex_neg_one
    (generator : WeakDoublet →ₗ[ℂ] WeakDoublet)
    (psi : DiracWeakSpinor) :
    causalWeakVertex (-1) generator psi = rightWeakVertex generator psi := by
  simp [causalWeakVertex, rightWeakVertex, causalWeylProjector_neg_one]

/-- Every standard left weak vertex annihilates every right Weyl state. -/
theorem leftWeakVertex_annihilates_right
    (generator : WeakDoublet →ₗ[ℂ] WeakDoublet)
    (psi : DiracWeakSpinor) :
    leftWeakVertex generator (rightWeylProjector psi) = 0 := by
  rw [leftWeakVertex, weylProjectors_orthogonal_left_right]
  ext chirality spin isospin
  simp [liftWeakGenerator]

/-- Projecting an already-left state does not change the left weak vertex. -/
theorem leftWeakVertex_absorbs_left
    (generator : WeakDoublet →ₗ[ℂ] WeakDoublet)
    (psi : DiracWeakSpinor) :
    leftWeakVertex generator (leftWeylProjector psi) =
      leftWeakVertex generator psi := by
  simp [leftWeakVertex, leftWeylProjector_idempotent]

theorem rightWeakVertex_annihilates_left
    (generator : WeakDoublet →ₗ[ℂ] WeakDoublet)
    (psi : DiracWeakSpinor) :
    rightWeakVertex generator (leftWeylProjector psi) = 0 := by
  rw [rightWeakVertex, weylProjectors_orthogonal_right_left]
  ext chirality spin isospin
  simp [liftWeakGenerator]

theorem rightWeakVertex_absorbs_right
    (generator : WeakDoublet →ₗ[ℂ] WeakDoublet)
    (psi : DiracWeakSpinor) :
    rightWeakVertex generator (rightWeylProjector psi) =
      rightWeakVertex generator psi := by
  simp [rightWeakVertex, rightWeylProjector_idempotent]

/-- A lower-isospin state in the left Weyl sector. -/
def leftLowerWeakState : DiracWeakSpinor :=
  fun chirality spin isospin ↦
    if chirality = 0 ∧ spin = 0 ∧ isospin = 1 then 1 else 0

/-- A lower-isospin state in the right Weyl sector. -/
def rightLowerWeakState : DiracWeakSpinor :=
  fun chirality spin isospin ↦
    if chirality ≠ 0 ∧ spin = 0 ∧ isospin = 1 then 1 else 0

theorem leftChargedWeakVertex_nonzero :
    leftWeakVertex weakRaising leftLowerWeakState ≠ 0 := by
  intro hZero
  have hComponent := congr_fun (congr_fun (congr_fun hZero 0) 0) 0
  norm_num [leftWeakVertex, liftWeakGenerator, leftWeylProjector,
    weakRaising, leftLowerWeakState] at hComponent

theorem rightChargedWeakVertex_nonzero :
    rightWeakVertex weakRaising rightLowerWeakState ≠ 0 := by
  intro hZero
  have hComponent := congr_fun (congr_fun (congr_fun hZero 1) 0) 0
  norm_num [rightWeakVertex, liftWeakGenerator, rightWeylProjector,
    weakRaising, rightLowerWeakState] at hComponent

/-- Exact algebraic specification of a nonzero purely left-handed weak
interaction. -/
def IsNontrivialPurelyLeftHanded
    (vertex : DiracWeakSpinor → DiracWeakSpinor) : Prop :=
  (∀ psi, vertex (rightWeylProjector psi) = 0) ∧
  (∀ psi, vertex (leftWeylProjector psi) = vertex psi) ∧
  vertex leftLowerWeakState ≠ 0

/-- Mirror specification. -/
def IsNontrivialPurelyRightHanded
    (vertex : DiracWeakSpinor → DiracWeakSpinor) : Prop :=
  (∀ psi, vertex (leftWeylProjector psi) = 0) ∧
  (∀ psi, vertex (rightWeylProjector psi) = vertex psi) ∧
  vertex rightLowerWeakState ≠ 0

theorem standard_charged_current_is_nontrivial_purely_left :
    IsNontrivialPurelyLeftHanded (leftWeakVertex weakRaising) := by
  exact ⟨leftWeakVertex_annihilates_right weakRaising,
    leftWeakVertex_absorbs_left weakRaising,
    leftChargedWeakVertex_nonzero⟩

theorem mirror_charged_current_is_nontrivial_purely_right :
    IsNontrivialPurelyRightHanded (rightWeakVertex weakRaising) := by
  exact ⟨rightWeakVertex_annihilates_left weakRaising,
    rightWeakVertex_absorbs_right weakRaising,
    rightChargedWeakVertex_nonzero⟩

/-! ## 5. The sequential-growth promotion theorem -/

/-- Cylinder sign after an arbitrary number of projective refinements. -/
def refinedCylinderSign
    (action : VacuumSpectatorCausalAction)
    (data : RelationalProfileTriple) (steps : ℕ) : ℝ :=
  inducedCylinderChiralitySign
    (relationallySelectedCausalSetGrowthLaw action data)
    (OrientationCylinderCoarseGraining.refineBy
      chiralRankTwoCoarseGraining steps)

/-- Weak vertex read from the refined causal cylinder. -/
def refinedCausalWeakVertex
    (action : VacuumSpectatorCausalAction)
    (data : RelationalProfileTriple) (steps : ℕ)
    (generator : WeakDoublet →ₗ[ℂ] WeakDoublet) :
    DiracWeakSpinor → DiracWeakSpinor :=
  causalWeakVertex (refinedCylinderSign action data steps) generator

theorem refinedCylinderSign_of_pos
    (action : VacuumSpectatorCausalAction)
    {data : RelationalProfileTriple} (hPositive : 0 < data.chirality)
    (steps : ℕ) :
    refinedCylinderSign action data steps = 1 := by
  unfold refinedCylinderSign
  rw [inducedCylinderChiralitySign_refineBy]
  exact relationallySelected_cylinderSign_of_pos action hPositive

theorem refinedCylinderSign_of_neg
    (action : VacuumSpectatorCausalAction)
    {data : RelationalProfileTriple} (hNegative : data.chirality < 0)
    (steps : ℕ) :
    refinedCylinderSign action data steps = -1 := by
  unfold refinedCylinderSign
  rw [inducedCylinderChiralitySign_refineBy]
  exact relationallySelected_cylinderSign_of_neg action hNegative

/-- The weak vertex itself, not just its sign, is unchanged by refinement. -/
theorem refinedCausalWeakVertex_transport
    (action : VacuumSpectatorCausalAction)
    (data : RelationalProfileTriple) (firstSteps secondSteps : ℕ)
    (generator : WeakDoublet →ₗ[ℂ] WeakDoublet) :
    refinedCausalWeakVertex action data firstSteps generator =
      refinedCausalWeakVertex action data secondSteps generator := by
  unfold refinedCausalWeakVertex refinedCylinderSign
  rw [inducedCylinderChiralitySign_refineBy,
    inducedCylinderChiralitySign_refineBy]

theorem refinedCausalWeakVertex_of_pos
    (action : VacuumSpectatorCausalAction)
    {data : RelationalProfileTriple} (hPositive : 0 < data.chirality)
    (steps : ℕ) (generator : WeakDoublet →ₗ[ℂ] WeakDoublet) :
    refinedCausalWeakVertex action data steps generator =
      leftWeakVertex generator := by
  unfold refinedCausalWeakVertex
  rw [refinedCylinderSign_of_pos action hPositive]
  funext psi
  exact causalWeakVertex_one generator psi

theorem refinedCausalWeakVertex_of_neg
    (action : VacuumSpectatorCausalAction)
    {data : RelationalProfileTriple} (hNegative : data.chirality < 0)
    (steps : ℕ) (generator : WeakDoublet →ₗ[ℂ] WeakDoublet) :
    refinedCausalWeakVertex action data steps generator =
      rightWeakVertex generator := by
  unfold refinedCausalWeakVertex
  rw [refinedCylinderSign_of_neg action hNegative]
  funext psi
  exact causalWeakVertex_neg_one generator psi

/-- **Left-handed weak-interaction theorem.**  A positive nonzero relational
orientation produces, at every refinement depth, the standard nonzero charged
`su(2)` vertex.  It annihilates all right Weyl states and acts only through the
left projector. -/
theorem positive_relational_growth_derives_left_handed_weak_interaction
    (action : VacuumSpectatorCausalAction)
    {data : RelationalProfileTriple} (hPositive : 0 < data.chirality) :
    ∀ steps : ℕ,
      IsNontrivialPurelyLeftHanded
        (refinedCausalWeakVertex action data steps weakRaising) := by
  intro steps
  rw [refinedCausalWeakVertex_of_pos action hPositive]
  exact standard_charged_current_is_nontrivial_purely_left

/-- The reflected oriented branch produces the exact mirror interaction. -/
theorem negative_relational_growth_derives_right_handed_mirror
    (action : VacuumSpectatorCausalAction)
    {data : RelationalProfileTriple} (hNegative : data.chirality < 0) :
    ∀ steps : ℕ,
      IsNontrivialPurelyRightHanded
        (refinedCausalWeakVertex action data steps weakRaising) := by
  intro steps
  rw [refinedCausalWeakVertex_of_neg action hNegative]
  exact mirror_charged_current_is_nontrivial_purely_right

/-- For every nonzero relational orientation, sequential growth derives exactly
one of the two nonzero purely chiral weak vertices and transports it through all
refinements. -/
theorem nonzero_relational_growth_derives_purely_chiral_weak_interaction
    (action : VacuumSpectatorCausalAction)
    (data : RelationalProfileTriple) (hNonzero : data.chirality ≠ 0) :
    ((0 < data.chirality ∧
        ∀ steps : ℕ,
          IsNontrivialPurelyLeftHanded
            (refinedCausalWeakVertex action data steps weakRaising))
      ∨ (data.chirality < 0 ∧
        ∀ steps : ℕ,
          IsNontrivialPurelyRightHanded
            (refinedCausalWeakVertex action data steps weakRaising))) := by
  rcases lt_or_gt_of_ne hNonzero with hNegative | hPositive
  · exact Or.inr ⟨hNegative,
      negative_relational_growth_derives_right_handed_mirror action hNegative⟩
  · exact Or.inl ⟨hPositive,
      positive_relational_growth_derives_left_handed_weak_interaction action hPositive⟩

/-- The explicit positive cubic witness gives a fully concrete left-handed
model at all depths.  This is a constructed oriented branch, not a proof that
the reflection-fixed vacuum selects it. -/
theorem positiveWitness_derives_left_handed_weak_interaction
    (action : VacuumSpectatorCausalAction) :
    ∀ steps : ℕ,
      IsNontrivialPurelyLeftHanded
        (refinedCausalWeakVertex action positiveRelationalWitness steps
          weakRaising) := by
  exact positive_relational_growth_derives_left_handed_weak_interaction
    action (by rw [positiveRelationalWitness_chirality]; norm_num)

/-! ## 6. Exact parity covariance and the honest frontier -/

theorem liftWeakGenerator_reflection
    (generator : WeakDoublet →ₗ[ℂ] WeakDoublet)
    (psi : DiracWeakSpinor) :
    liftWeakGenerator generator (spinorReflection psi) =
      spinorReflection (liftWeakGenerator generator psi) := by
  ext chirality spin isospin
  fin_cases chirality
  · change generator (psi 1 spin) isospin =
      generator (psi 1 spin) isospin
    rfl
  · change generator (psi 0 spin) isospin =
      generator (psi 0 spin) isospin
    rfl

theorem causalWeakVertex_reflection
    (xi : ℝ) (generator : WeakDoublet →ₗ[ℂ] WeakDoublet)
    (psi : DiracWeakSpinor) :
    causalWeakVertex (-xi) generator (spinorReflection psi) =
      spinorReflection (causalWeakVertex xi generator psi) := by
  unfold causalWeakVertex
  rw [causalWeylProjector_reflection,
    liftWeakGenerator_reflection]

theorem refinedCylinderSign_reflection
    (action : VacuumSpectatorCausalAction)
    (data : RelationalProfileTriple) (hNonzero : data.chirality ≠ 0)
    (steps : ℕ) :
    refinedCylinderSign action data.reflection steps =
      -refinedCylinderSign action data steps := by
  rcases lt_or_gt_of_ne hNonzero with hNegative | hPositive
  · rw [refinedCylinderSign_of_neg action hNegative]
    have hReflectedPositive : 0 < data.reflection.chirality := by
      rw [RelationalProfileTriple.chirality_reflection]
      linarith
    rw [refinedCylinderSign_of_pos action hReflectedPositive]
    norm_num
  · rw [refinedCylinderSign_of_pos action hPositive]
    have hReflectedNegative : data.reflection.chirality < 0 := by
      rw [RelationalProfileTriple.chirality_reflection]
      linarith
    rw [refinedCylinderSign_of_neg action hReflectedNegative]

/-- Reflecting relational geometry and the spinor together preserves the
causally locked weak law.  The law is left-handed relative to orientation,
without requiring an absolute naming of one reflected universe. -/
theorem refinedCausalWeakVertex_reflection_covariant
    (action : VacuumSpectatorCausalAction)
    (data : RelationalProfileTriple) (hNonzero : data.chirality ≠ 0)
    (steps : ℕ) (generator : WeakDoublet →ₗ[ℂ] WeakDoublet)
    (psi : DiracWeakSpinor) :
    refinedCausalWeakVertex action data.reflection steps generator
        (spinorReflection psi) =
      spinorReflection
        (refinedCausalWeakVertex action data steps generator psi) := by
  unfold refinedCausalWeakVertex
  rw [refinedCylinderSign_reflection action data hNonzero steps]
  exact causalWeakVertex_reflection
    (refinedCylinderSign action data steps) generator psi

/-- Final promotion contract.  The positive oriented branch gives the exact
standard left-handed charged current at every depth, reflection gives its
right-handed mirror, and the current symmetric vacuum cannot covariantly pick
between them.  Therefore the only remaining step to an unconditional statement
about nature is dynamical generation (or spontaneous selection) of a nonzero
oriented branch. -/
theorem left_handed_weak_interaction_promotion_frontier :
    (∀ action : VacuumSpectatorCausalAction,
      ∀ steps : ℕ,
        IsNontrivialPurelyLeftHanded
          (refinedCausalWeakVertex action positiveRelationalWitness steps
            weakRaising))
      ∧ (∀ select : VacuumSpectatorCausalAction → Fin 2,
        ¬(∀ action,
          select (vacuumSpectatorActionReflection action) =
            reflectedMicroscopicChirality (select action))) := by
  exact ⟨positiveWitness_derives_left_handed_weak_interaction,
    no_reflection_covariant_vacuum_chirality_selector⟩

#print axioms gammaFive_involutive
#print axioms weakRaising_lowering_commutator
#print axioms causalWeylProjector_unique_affine
#print axioms causalWeylProjector_reflection
#print axioms positive_relational_growth_derives_left_handed_weak_interaction
#print axioms nonzero_relational_growth_derives_purely_chiral_weak_interaction
#print axioms refinedCausalWeakVertex_reflection_covariant
#print axioms left_handed_weak_interaction_promotion_frontier

end

end UnifiedTheory.Audit.KFCausalSetWeakHandednessBridge
