/-
  Audit/KFOrientationInfiniteCylinderDecoherence.lean

  PROJECTIVE QUANTUM GROWTH AND THE INFINITE CYLINDER ALGEBRA

  This file attacks the next promotion frontier after the finite associator
  decoherence functional.  It first treats an arbitrary finite branching type.
  A normalized complex growth law assigns an amplitude to each extension of
  each finite prefix, with the amplitudes of all immediate extensions summing
  to one.  Products of those transition amplitudes give a rank-one
  decoherence functional at every finite depth.

  The central theorem is exact projective consistency: summing the fine
  decoherence functional over every extension of two events recovers the
  coarse functional.  Cylinder-event presentations are then quotiented by
  this refinement equivalence, producing a normalized strongly positive
  functional on the infinite cylinder algebra.

  The final section instantiates the construction with the orientation phase
  and proves that its depth-one restriction is exactly the finite kernel from
  `KFOrientationGrowthDecoherence`.

  Scope: the concrete instance is the binary associator-growth sector.  The
  generic theorem applies to any finite branching alphabet equipped with a
  normalized complex transition law, but this file does not identify that
  alphabet with every one-element extension of an arbitrary causal set.
-/

import UnifiedTheory.Audit.KFOrientationGrowthDecoherence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFOrientationInfiniteCylinderDecoherence

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFOrientationUnlabeledRefinement
open UnifiedTheory.Audit.KFOrientationSpinOne
open UnifiedTheory.Audit.KFOrientationHistoryRigidity

/-! ## 1. Generic finite-depth complex growth -/

/-- A depth-`n` growth path records its first `n` finite branch choices. -/
abbrev GrowthPath (Branch : Type*) (n : ℕ) := Fin n → Branch

/-- A state-dependent complex transition law whose immediate extension
amplitudes sum to one at every finite prefix. -/
structure NormalizedComplexGrowthLaw (Branch : Type*) [Fintype Branch] where
  transition : ∀ n : ℕ, GrowthPath Branch n → Branch → ℂ
  normalized : ∀ (n : ℕ) (pathPrefix : GrowthPath Branch n),
    ∑ branch, transition n pathPrefix branch = 1

/-- Split a path of depth `n+1` into its last branch and its depth-`n`
prefix. -/
def growthExtensionEquiv (Branch : Type*) (n : ℕ) :
    Branch × GrowthPath Branch n ≃ GrowthPath Branch (n + 1) :=
  Fin.snocEquiv (fun _ : Fin (n + 1) => Branch)

/-- Refine a finite event by including every one-step extension of each path
in the event. -/
def refineGrowthEvent {Branch : Type*} [Fintype Branch] [DecidableEq Branch]
    {n : ℕ} (event : Finset (GrowthPath Branch n)) :
    Finset (GrowthPath Branch (n + 1)) :=
  (Finset.univ ×ˢ event).map (growthExtensionEquiv Branch n).toEmbedding

theorem refineGrowthEvent_univ {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch] (n : ℕ) :
    refineGrowthEvent (Finset.univ : Finset (GrowthPath Branch n)) =
      Finset.univ := by
  ext path
  constructor
  · intro _
    exact Finset.mem_univ path
  · intro _
    let source := (growthExtensionEquiv Branch n).symm path
    apply Finset.mem_map.mpr
    exact ⟨source, by simp [source],
      (growthExtensionEquiv Branch n).apply_symm_apply path⟩

/-- Product of local transition amplitudes along a complete finite path. -/
def finitePathAmplitude {Branch : Type*} [Fintype Branch]
    (law : NormalizedComplexGrowthLaw Branch) :
    ∀ n : ℕ, GrowthPath Branch n → ℂ
  | 0, _ => 1
  | n + 1, path =>
      law.transition n (Fin.init path) (path (Fin.last n)) *
        finitePathAmplitude law n (Fin.init path)

@[simp]
theorem finitePathAmplitude_zero {Branch : Type*} [Fintype Branch]
    (law : NormalizedComplexGrowthLaw Branch)
    (path : GrowthPath Branch 0) :
    finitePathAmplitude law 0 path = 1 := rfl

@[simp]
theorem finitePathAmplitude_snoc {Branch : Type*} [Fintype Branch]
    (law : NormalizedComplexGrowthLaw Branch) (n : ℕ)
    (pathPrefix : GrowthPath Branch n) (branch : Branch) :
    finitePathAmplitude law (n + 1) (Fin.snoc pathPrefix branch) =
      law.transition n pathPrefix branch *
        finitePathAmplitude law n pathPrefix := by
  simp [finitePathAmplitude]

/-- The total amplitude of all one-step extensions of an event equals the
total amplitude of the event itself. -/
theorem finitePathAmplitude_sum_refine {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch]
    (law : NormalizedComplexGrowthLaw Branch) (n : ℕ)
    (event : Finset (GrowthPath Branch n)) :
    ∑ path ∈ refineGrowthEvent event,
        finitePathAmplitude law (n + 1) path =
      ∑ pathPrefix ∈ event, finitePathAmplitude law n pathPrefix := by
  simp only [refineGrowthEvent, Finset.sum_map, Finset.sum_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro pathPrefix _
  have hApply (branch : Branch) :
      (growthExtensionEquiv Branch n).toEmbedding (branch, pathPrefix) =
        Fin.snoc pathPrefix branch := by
    rfl
  simp_rw [hApply, finitePathAmplitude_snoc]
  rw [← Finset.sum_mul, law.normalized, one_mul]

/-- At every finite depth the sum of all complete-path amplitudes is one. -/
theorem finitePathAmplitude_sum_univ {Branch : Type*}
    [Fintype Branch]
    (law : NormalizedComplexGrowthLaw Branch) (n : ℕ) :
    ∑ path : GrowthPath Branch n, finitePathAmplitude law n path = 1 := by
  classical
  induction n with
  | zero => simp [finitePathAmplitude]
  | succ n ih =>
      rw [← refineGrowthEvent_univ (Branch := Branch) n]
      rw [finitePathAmplitude_sum_refine,
        ih]

/-- Finite-depth rank-one decoherence kernel generated by the path
amplitudes. -/
def finiteDepthDecoherence {Branch : Type*} [Fintype Branch]
    (law : NormalizedComplexGrowthLaw Branch) (n : ℕ) :
    GrowthDecoherenceFunctional (GrowthPath Branch n) :=
  amplitudeDecoherence (finitePathAmplitude law n)

theorem finiteDepthDecoherence_hermitian {Branch : Type*}
    [Fintype Branch] (law : NormalizedComplexGrowthLaw Branch) (n : ℕ) :
    IsHermitianGrowthFunctional (finiteDepthDecoherence law n) := by
  exact amplitudeDecoherence_hermitian _

theorem finiteDepthDecoherence_stronglyPositive {Branch : Type*}
    [Fintype Branch] (law : NormalizedComplexGrowthLaw Branch) (n : ℕ) :
    IsStronglyPositiveGrowthFunctional (finiteDepthDecoherence law n) := by
  exact amplitudeDecoherence_stronglyPositive _

theorem finiteDepthEventDecoherence_stronglyPositive {Branch : Type*}
    [Fintype Branch] (law : NormalizedComplexGrowthLaw Branch) (n : ℕ) :
    IsStronglyPositiveGrowthFunctional
      (growthEventDecoherence (finiteDepthDecoherence law n)) := by
  exact amplitude_growthEventDecoherence_stronglyPositive _

theorem finiteDepthDecoherence_normalized {Branch : Type*}
    [Fintype Branch]
    (law : NormalizedComplexGrowthLaw Branch) (n : ℕ) :
    IsNormalizedGrowthFunctional (finiteDepthDecoherence law n) := by
  classical
  unfold IsNormalizedGrowthFunctional
  change growthEventDecoherence (finiteDepthDecoherence law n)
    Finset.univ Finset.univ = 1
  unfold finiteDepthDecoherence
  rw [amplitude_growthEventDecoherence_eq,
    finitePathAmplitude_sum_univ law n]
  simp

/-! ## 2. Exact one-step projective consistency -/

/-- Marginalizing both fine events over one growth step recovers the coarse
event decoherence exactly. -/
theorem finiteDepthDecoherence_projective {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch]
    (law : NormalizedComplexGrowthLaw Branch) (n : ℕ)
    (event₁ event₂ : Finset (GrowthPath Branch n)) :
    growthEventDecoherence (finiteDepthDecoherence law (n + 1))
        (refineGrowthEvent event₁) (refineGrowthEvent event₂) =
      growthEventDecoherence (finiteDepthDecoherence law n) event₁ event₂ := by
  unfold finiteDepthDecoherence
  rw [amplitude_growthEventDecoherence_eq,
    amplitude_growthEventDecoherence_eq,
    finitePathAmplitude_sum_refine,
    finitePathAmplitude_sum_refine]

/-- Package the finite-depth laws and their exact marginal compatibility. -/
theorem normalized_projective_growth_family {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch]
    (law : NormalizedComplexGrowthLaw Branch) :
    (∀ n, IsNormalizedGrowthFunctional (finiteDepthDecoherence law n))
      ∧ (∀ n, IsHermitianGrowthFunctional (finiteDepthDecoherence law n))
      ∧ (∀ n, IsStronglyPositiveGrowthFunctional
          (growthEventDecoherence (finiteDepthDecoherence law n)))
      ∧ (∀ (n) (event₁ event₂ : Finset (GrowthPath Branch n)),
          growthEventDecoherence (finiteDepthDecoherence law (n + 1))
              (refineGrowthEvent event₁) (refineGrowthEvent event₂) =
            growthEventDecoherence (finiteDepthDecoherence law n)
              event₁ event₂) := by
  exact ⟨finiteDepthDecoherence_normalized law,
    finiteDepthDecoherence_hermitian law,
    finiteDepthEventDecoherence_stronglyPositive law,
    finiteDepthDecoherence_projective law⟩

/-! ## 3. Arbitrary-depth refinement -/

/-- Refine an event through `steps` successive complete branching layers. -/
def refineGrowthEventBy {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch] {n : ℕ}
    (event : Finset (GrowthPath Branch n)) :
    ∀ steps : ℕ, Finset (GrowthPath Branch (n + steps))
  | 0 => event
  | steps + 1 => refineGrowthEvent (refineGrowthEventBy event steps)

@[simp]
theorem refineGrowthEventBy_zero {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch] {n : ℕ}
    (event : Finset (GrowthPath Branch n)) :
    refineGrowthEventBy event 0 = event := rfl

@[simp]
theorem refineGrowthEventBy_succ {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch] {n : ℕ}
    (event : Finset (GrowthPath Branch n)) (steps : ℕ) :
    refineGrowthEventBy event (steps + 1) =
      refineGrowthEvent (refineGrowthEventBy event steps) := rfl

/-- Projective consistency holds across an arbitrary finite separation of
depths, not only adjacent layers. -/
theorem finiteDepthDecoherence_projective_by {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch]
    (law : NormalizedComplexGrowthLaw Branch) (n : ℕ)
    (event₁ event₂ : Finset (GrowthPath Branch n)) :
    ∀ steps : ℕ,
      growthEventDecoherence (finiteDepthDecoherence law (n + steps))
          (refineGrowthEventBy event₁ steps)
          (refineGrowthEventBy event₂ steps) =
        growthEventDecoherence (finiteDepthDecoherence law n) event₁ event₂
  | 0 => rfl
  | steps + 1 => by
      rw [refineGrowthEventBy_succ, refineGrowthEventBy_succ]
      change growthEventDecoherence
          (finiteDepthDecoherence law ((n + steps) + 1))
          (refineGrowthEvent (refineGrowthEventBy event₁ steps))
          (refineGrowthEvent (refineGrowthEventBy event₂ steps)) = _
      rw [finiteDepthDecoherence_projective law (n + steps)]
      exact finiteDepthDecoherence_projective_by law n event₁ event₂ steps

/-! ## 4. Cylinder presentations and refinement equivalence -/

/-- A presentation of an event in the infinite trajectory space by a finite
depth and a finite set of allowed prefixes. -/
structure CylinderPresentation (Branch : Type*) where
  depth : ℕ
  event : Finset (GrowthPath Branch depth)

/-- One-step refinement changes the presentation but not the represented
infinite cylinder event. -/
def CylinderPresentation.refine {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch]
    (cylinder : CylinderPresentation Branch) :
    CylinderPresentation Branch where
  depth := cylinder.depth + 1
  event := refineGrowthEvent cylinder.event

/-- Directed generator of cylinder refinement equivalence. -/
def cylinderRefinementRel {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch]
    (first second : CylinderPresentation Branch) : Prop :=
  second = first.refine

/-- Equivalence closure of finite cylinder refinement. -/
def cylinderEquivalent {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch] :
    CylinderPresentation Branch → CylinderPresentation Branch → Prop :=
  Relation.EqvGen cylinderRefinementRel

theorem cylinderEquivalent_equivalence {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch] :
    Equivalence (@cylinderEquivalent Branch _ _) := by
  exact Relation.EqvGen.is_equivalence _

/-- The infinite cylinder-event type is the quotient of finite presentations
by arbitrary finite chains of refinement and inverse refinement. -/
def InfiniteCylinderEvent (Branch : Type*)
    [Fintype Branch] [DecidableEq Branch] :=
  Quotient (Relation.EqvGen.setoid
    (@cylinderRefinementRel Branch _ _))

/-- Infinite branch histories on which cylinder events are evaluated. -/
abbrev InfiniteGrowthTrajectory (Branch : Type*) := ℕ → Branch

/-- First `n` branch values of an infinite trajectory. -/
def trajectoryPrefix {Branch : Type*}
    (trajectory : InfiniteGrowthTrajectory Branch) (n : ℕ) :
    GrowthPath Branch n :=
  fun i => trajectory i.val

theorem trajectoryPrefix_snoc {Branch : Type*}
    (trajectory : InfiniteGrowthTrajectory Branch) (n : ℕ) :
    Fin.snoc (trajectoryPrefix trajectory n) (trajectory n) =
      trajectoryPrefix trajectory (n + 1) := by
  ext i
  by_cases h : i.val < n
  · simp [Fin.snoc, h, trajectoryPrefix]
  · have hi : i = Fin.last n := Fin.eq_last_of_not_lt h
    rw [hi]
    simp [trajectoryPrefix]

theorem mem_refineGrowthEvent_iff {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch] {n : ℕ}
    (event : Finset (GrowthPath Branch n))
    (path : GrowthPath Branch (n + 1)) :
    path ∈ refineGrowthEvent event ↔ Fin.init path ∈ event := by
  constructor
  · intro h
    rcases Finset.mem_map.mp h with ⟨source, hSource, hSourceEq⟩
    have hEvent : source.2 ∈ event := (Finset.mem_product.mp hSource).2
    have hSymm := congrArg
      (fun finePath => ((growthExtensionEquiv Branch n).symm finePath).2)
      hSourceEq
    have hInit : source.2 = Fin.init path := by
      simpa [growthExtensionEquiv] using hSymm
    simpa [← hInit] using hEvent
  · intro h
    let source := (growthExtensionEquiv Branch n).symm path
    apply Finset.mem_map.mpr
    refine ⟨source, ?_, (growthExtensionEquiv Branch n).apply_symm_apply path⟩
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hSource : source.2 = Fin.init path := by
      rfl
    simpa [hSource] using h

/-- Semantic membership of an infinite trajectory in a finite cylinder
presentation. -/
def CylinderPresentation.Realizes {Branch : Type*}
    (cylinder : CylinderPresentation Branch)
    (trajectory : InfiniteGrowthTrajectory Branch) : Prop :=
  trajectoryPrefix trajectory cylinder.depth ∈ cylinder.event

/-- One-step refinement preserves the represented set of infinite
trajectories exactly. -/
theorem CylinderPresentation.realizes_refine_iff {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch]
    (cylinder : CylinderPresentation Branch)
    (trajectory : InfiniteGrowthTrajectory Branch) :
    cylinder.refine.Realizes trajectory ↔ cylinder.Realizes trajectory := by
  change trajectoryPrefix trajectory (cylinder.depth + 1) ∈
      refineGrowthEvent cylinder.event ↔
    trajectoryPrefix trajectory cylinder.depth ∈ cylinder.event
  rw [mem_refineGrowthEvent_iff]
  rfl

theorem CylinderPresentation.realizes_iff_of_equivalent {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch]
    {first second : CylinderPresentation Branch}
    (hEquivalent : cylinderEquivalent first second)
    (trajectory : InfiniteGrowthTrajectory Branch) :
    first.Realizes trajectory ↔ second.Realizes trajectory := by
  induction hEquivalent with
  | rel first second hStep =>
      subst second
      exact (CylinderPresentation.realizes_refine_iff first trajectory).symm
  | refl => rfl
  | symm first second _ ih => exact ih.symm
  | trans first second third _ _ ih₁₂ ih₂₃ => exact ih₁₂.trans ih₂₃

/-- Membership is therefore well-defined directly on the quotient cylinder
event, making its interpretation as an event of infinite trajectories
literal rather than informal. -/
def InfiniteCylinderEvent.Realizes {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch]
    (event : InfiniteCylinderEvent Branch)
    (trajectory : InfiniteGrowthTrajectory Branch) : Prop :=
  Quotient.lift
    (fun cylinder : CylinderPresentation Branch =>
      cylinder.Realizes trajectory)
    (fun _ _ hEquivalent =>
      propext (CylinderPresentation.realizes_iff_of_equivalent
        hEquivalent trajectory)) event

/-! ## 5. The normalized strongly positive infinite-cylinder functional -/

/-- Total amplitude assigned to a finite cylinder presentation. -/
def cylinderPresentationAmplitude {Branch : Type*}
    [Fintype Branch]
    (law : NormalizedComplexGrowthLaw Branch)
    (cylinder : CylinderPresentation Branch) : ℂ :=
  ∑ path ∈ cylinder.event,
    finitePathAmplitude law cylinder.depth path

theorem cylinderPresentationAmplitude_refine {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch]
    (law : NormalizedComplexGrowthLaw Branch)
    (cylinder : CylinderPresentation Branch) :
    cylinderPresentationAmplitude law cylinder.refine =
      cylinderPresentationAmplitude law cylinder := by
  exact finitePathAmplitude_sum_refine law cylinder.depth cylinder.event

theorem cylinderPresentationAmplitude_eq_of_equivalent {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch]
    (law : NormalizedComplexGrowthLaw Branch)
    {first second : CylinderPresentation Branch}
    (hEquivalent : cylinderEquivalent first second) :
    cylinderPresentationAmplitude law first =
      cylinderPresentationAmplitude law second := by
  induction hEquivalent with
  | rel first second hStep =>
      subst second
      exact (cylinderPresentationAmplitude_refine law first).symm
  | refl => rfl
  | symm first second _ ih => exact ih.symm
  | trans first second third _ _ ih₁₂ ih₂₃ => exact ih₁₂.trans ih₂₃

/-- Projective consistency descends the finite amplitudes to the infinite
cylinder-event quotient. -/
def infiniteCylinderAmplitude {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch]
    (law : NormalizedComplexGrowthLaw Branch) :
    InfiniteCylinderEvent Branch → ℂ :=
  Quotient.lift (cylinderPresentationAmplitude law)
    (fun _ _ hEquivalent =>
      cylinderPresentationAmplitude_eq_of_equivalent law hEquivalent)

/-- The infinite-cylinder decoherence functional is the Gram kernel of the
projective-limit cylinder amplitudes. -/
def infiniteCylinderDecoherence {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch]
    (law : NormalizedComplexGrowthLaw Branch) :
    GrowthDecoherenceFunctional (InfiniteCylinderEvent Branch) :=
  amplitudeDecoherence (infiniteCylinderAmplitude law)

/-- Canonical presentation of the total infinite trajectory event. -/
def totalInfiniteCylinderEvent (Branch : Type*)
    [Fintype Branch] [DecidableEq Branch] :
    InfiniteCylinderEvent Branch :=
  Quotient.mk _
    ({ depth := 0
       event := Finset.univ } : CylinderPresentation Branch)

theorem infiniteCylinderAmplitude_total {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch]
    (law : NormalizedComplexGrowthLaw Branch) :
    infiniteCylinderAmplitude law (totalInfiniteCylinderEvent Branch) = 1 := by
  simp [infiniteCylinderAmplitude, totalInfiniteCylinderEvent,
    cylinderPresentationAmplitude, finitePathAmplitude]

theorem infiniteCylinderDecoherence_hermitian {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch]
    (law : NormalizedComplexGrowthLaw Branch) :
    IsHermitianGrowthFunctional (infiniteCylinderDecoherence law) := by
  exact amplitudeDecoherence_hermitian _

/-- Strong positivity now ranges over arbitrary finite families of events in
the infinite cylinder quotient. -/
theorem infiniteCylinderDecoherence_stronglyPositive {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch]
    (law : NormalizedComplexGrowthLaw Branch) :
    IsStronglyPositiveGrowthFunctional
      (infiniteCylinderDecoherence law) := by
  exact amplitudeDecoherence_stronglyPositive _

/-- Infinite normalization is `D(Omega,Omega)=1`; unlike finite atomic
normalization it does not sum over the infinite event type. -/
theorem infiniteCylinderDecoherence_normalized {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch]
    (law : NormalizedComplexGrowthLaw Branch) :
    infiniteCylinderDecoherence law
        (totalInfiniteCylinderEvent Branch)
        (totalInfiniteCylinderEvent Branch) = 1 := by
  simp [infiniteCylinderDecoherence, amplitudeDecoherence,
    infiniteCylinderAmplitude_total law]

/-- The infinite functional evaluated on two presentations of the same depth
is exactly the corresponding finite-depth event functional. -/
theorem infiniteCylinderDecoherence_restricts_finite {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch]
    (law : NormalizedComplexGrowthLaw Branch) (n : ℕ)
    (event₁ event₂ : Finset (GrowthPath Branch n)) :
    infiniteCylinderDecoherence law
        (Quotient.mk _
          ({ depth := n, event := event₁ } : CylinderPresentation Branch))
        (Quotient.mk _
          ({ depth := n, event := event₂ } : CylinderPresentation Branch)) =
      growthEventDecoherence (finiteDepthDecoherence law n) event₁ event₂ := by
  unfold infiniteCylinderDecoherence infiniteCylinderAmplitude
    cylinderPresentationAmplitude finiteDepthDecoherence
  rw [amplitude_growthEventDecoherence_eq]
  rfl

/-- Canonical quotient event represented at a specified finite depth. -/
def finiteCylinderEvent {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch]
    (n : ℕ) (event : Finset (GrowthPath Branch n)) :
    InfiniteCylinderEvent Branch :=
  Quotient.mk _ ({ depth := n, event := event } : CylinderPresentation Branch)

theorem finiteCylinderEvent_refine_eq {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch]
    (n : ℕ) (event : Finset (GrowthPath Branch n)) :
    finiteCylinderEvent (n + 1) (refineGrowthEvent event) =
      finiteCylinderEvent n event := by
  apply Quotient.sound
  exact Relation.EqvGen.symm _ _
    (Relation.EqvGen.rel _ _ rfl)

/-- Finite additivity on same-depth cylinder presentations.  Any two cylinder
events can be brought to such a common depth by refinement. -/
theorem infiniteCylinderDecoherence_union_left_sameDepth {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch]
    (law : NormalizedComplexGrowthLaw Branch) (n : ℕ)
    (event₁ event₂ event₃ : Finset (GrowthPath Branch n))
    (hDisjoint : Disjoint event₁ event₂) :
    infiniteCylinderDecoherence law
        (finiteCylinderEvent n (event₁ ∪ event₂))
        (finiteCylinderEvent n event₃) =
      infiniteCylinderDecoherence law
          (finiteCylinderEvent n event₁) (finiteCylinderEvent n event₃) +
        infiniteCylinderDecoherence law
          (finiteCylinderEvent n event₂) (finiteCylinderEvent n event₃) := by
  unfold finiteCylinderEvent
  rw [infiniteCylinderDecoherence_restricts_finite,
    infiniteCylinderDecoherence_restricts_finite,
    infiniteCylinderDecoherence_restricts_finite]
  exact growthEventDecoherence_union_left _ _ _ _ hDisjoint

theorem infiniteCylinderDecoherence_union_right_sameDepth {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch]
    (law : NormalizedComplexGrowthLaw Branch) (n : ℕ)
    (event₁ event₂ event₃ : Finset (GrowthPath Branch n))
    (hDisjoint : Disjoint event₂ event₃) :
    infiniteCylinderDecoherence law
        (finiteCylinderEvent n event₁)
        (finiteCylinderEvent n (event₂ ∪ event₃)) =
      infiniteCylinderDecoherence law
          (finiteCylinderEvent n event₁) (finiteCylinderEvent n event₂) +
        infiniteCylinderDecoherence law
          (finiteCylinderEvent n event₁) (finiteCylinderEvent n event₃) := by
  unfold finiteCylinderEvent
  rw [infiniteCylinderDecoherence_restricts_finite,
    infiniteCylinderDecoherence_restricts_finite,
    infiniteCylinderDecoherence_restricts_finite]
  exact growthEventDecoherence_union_right _ _ _ _ hDisjoint

/-- Quantum measure induced on the infinite cylinder quotient. -/
def infiniteCylinderQuantumMeasure {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch]
    (law : NormalizedComplexGrowthLaw Branch)
    (event : InfiniteCylinderEvent Branch) : ℝ :=
  (infiniteCylinderDecoherence law event event).re

theorem infiniteCylinderQuantumMeasure_nonneg {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch]
    (law : NormalizedComplexGrowthLaw Branch)
    (event : InfiniteCylinderEvent Branch) :
    0 ≤ infiniteCylinderQuantumMeasure law event := by
  let z : ℂ := infiniteCylinderAmplitude law event
  change 0 ≤ (z * star z).re
  have hEq : z * star z = ((Complex.normSq z : ℝ) : ℂ) := by
    have h := Complex.mul_conj z
    change z * star z = ((Complex.normSq z : ℝ) : ℂ)
    convert h using 1
  rw [hEq]
  simp only [Complex.ofReal_re]
  exact Complex.normSq_nonneg z

theorem infiniteCylinderQuantumMeasure_total {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch]
    (law : NormalizedComplexGrowthLaw Branch) :
    infiniteCylinderQuantumMeasure law
      (totalInfiniteCylinderEvent Branch) = 1 := by
  unfold infiniteCylinderQuantumMeasure
  rw [infiniteCylinderDecoherence_normalized]
  rfl

/-- The infinite cylinder quantum measure obeys Sorkin's grade-two sum rule
on pairwise-disjoint cylinder events represented at any common finite depth. -/
theorem infiniteCylinderQuantumMeasure_gradeTwo_sameDepth {Branch : Type*}
    [Fintype Branch] [DecidableEq Branch]
    (law : NormalizedComplexGrowthLaw Branch) (n : ℕ)
    (event₁ event₂ event₃ : Finset (GrowthPath Branch n))
    (h₁₂ : Disjoint event₁ event₂)
    (h₁₃ : Disjoint event₁ event₃)
    (h₂₃ : Disjoint event₂ event₃) :
    infiniteCylinderQuantumMeasure law
        (finiteCylinderEvent n ((event₁ ∪ event₂) ∪ event₃)) =
      infiniteCylinderQuantumMeasure law
          (finiteCylinderEvent n (event₁ ∪ event₂)) +
        infiniteCylinderQuantumMeasure law
          (finiteCylinderEvent n (event₁ ∪ event₃)) +
        infiniteCylinderQuantumMeasure law
          (finiteCylinderEvent n (event₂ ∪ event₃)) -
        infiniteCylinderQuantumMeasure law
          (finiteCylinderEvent n event₁) -
        infiniteCylinderQuantumMeasure law
          (finiteCylinderEvent n event₂) -
        infiniteCylinderQuantumMeasure law
          (finiteCylinderEvent n event₃) := by
  unfold infiniteCylinderQuantumMeasure finiteCylinderEvent
  rw [infiniteCylinderDecoherence_restricts_finite,
    infiniteCylinderDecoherence_restricts_finite,
    infiniteCylinderDecoherence_restricts_finite,
    infiniteCylinderDecoherence_restricts_finite,
    infiniteCylinderDecoherence_restricts_finite,
    infiniteCylinderDecoherence_restricts_finite,
    infiniteCylinderDecoherence_restricts_finite]
  exact amplitude_growthQuantumMeasure_gradeTwo
    (finitePathAmplitude law n) event₁ event₂ event₃ h₁₂ h₁₃ h₂₃

/-- Capstone for the generic infinite-cylinder construction. -/
theorem normalized_stronglyPositive_infiniteCylinder_family
    {Branch : Type*} [Fintype Branch] [DecidableEq Branch]
    (law : NormalizedComplexGrowthLaw Branch) :
    (∀ n, IsNormalizedGrowthFunctional (finiteDepthDecoherence law n))
      ∧ (∀ (n) (event₁ event₂ : Finset (GrowthPath Branch n)),
          growthEventDecoherence (finiteDepthDecoherence law (n + 1))
              (refineGrowthEvent event₁) (refineGrowthEvent event₂) =
            growthEventDecoherence (finiteDepthDecoherence law n)
              event₁ event₂)
      ∧ IsHermitianGrowthFunctional (infiniteCylinderDecoherence law)
      ∧ IsStronglyPositiveGrowthFunctional (infiniteCylinderDecoherence law)
      ∧ infiniteCylinderDecoherence law
          (totalInfiniteCylinderEvent Branch)
          (totalInfiniteCylinderEvent Branch) = 1
      ∧ (∀ event : InfiniteCylinderEvent Branch,
          0 ≤ infiniteCylinderQuantumMeasure law event) := by
  exact ⟨finiteDepthDecoherence_normalized law,
    finiteDepthDecoherence_projective law,
    infiniteCylinderDecoherence_hermitian law,
    infiniteCylinderDecoherence_stronglyPositive law,
    infiniteCylinderDecoherence_normalized law,
    infiniteCylinderQuantumMeasure_nonneg law⟩

/-! ## 6. Orientation instantiation and recovery of the finite model -/

/-- A projectively normalized representative of the orientation branch
amplitudes.  It differs from the earlier `(1,-i s)/sqrt(2)` ket by one
global unit phase, so it has the same decoherence kernel while its two
components sum exactly to one. -/
def orientationProjectiveBranchAmplitude
    (history : UnlabeledOrientationHistory) (route : Fin 2) : ℂ :=
  if route = 0 then
    (1 + Complex.I * (unlabeledOrientationSign history : ℂ)) / 2
  else
    (1 - Complex.I * (unlabeledOrientationSign history : ℂ)) / 2

theorem orientationProjectiveBranchAmplitude_sum
    (history : UnlabeledOrientationHistory) :
    ∑ route : Fin 2, orientationProjectiveBranchAmplitude history route = 1 := by
  rw [Fin.sum_univ_two]
  norm_num [orientationProjectiveBranchAmplitude, Fin.ext_iff]
  ring

/-- Homogeneous all-depth binary growth law selected by one unlabeled causal
orientation history.  The generic construction above also permits prefix-
dependent laws; homogeneity is the instance that extends the finite model. -/
def orientationProjectiveGrowthLaw
    (history : UnlabeledOrientationHistory) :
    NormalizedComplexGrowthLaw (Fin 2) where
  transition := fun _ _ route =>
    orientationProjectiveBranchAmplitude history route
  normalized := by
    intro _ _
    exact orientationProjectiveBranchAmplitude_sum history

/-- Canonical equivalence between a single route and a depth-one path. -/
def depthOnePathEquiv : Fin 2 ≃ GrowthPath (Fin 2) 1 where
  toFun route := fun _ => route
  invFun path := path 0
  left_inv route := rfl
  right_inv path := by
    funext i
    fin_cases i
    rfl

theorem orientationProjectiveBranchDecoherence_eq_unlabeledKernel
    (history : UnlabeledOrientationHistory) :
    (fun first second =>
      amplitudeDecoherence (orientationProjectiveBranchAmplitude history)
        first second) = unlabeledHistoryKernel history := by
  ext first second
  fin_cases first <;> fin_cases second
  all_goals
    generalize hEndpoint : unlabeledEndpoint history = endpoint
    fin_cases endpoint <;>
      norm_num [amplitudeDecoherence,
        orientationProjectiveBranchAmplitude, unlabeledHistoryKernel,
        balancedHistoryKernel, unlabeledOrientationSign, hEndpoint,
        endpointParameter, Fin.ext_iff, Complex.I_sq] <;>
      ring_nf <;>
      norm_num [Complex.I_sq]

@[simp]
theorem orientationFinitePathAmplitude_one
    (history : UnlabeledOrientationHistory) (route : Fin 2) :
    finitePathAmplitude (orientationProjectiveGrowthLaw history) 1
        (depthOnePathEquiv route) =
      orientationProjectiveBranchAmplitude history route := by
  simp [finitePathAmplitude, orientationProjectiveGrowthLaw,
    depthOnePathEquiv]

theorem orientationFiniteDepthOne_eq_growthDecoherence
    (history : UnlabeledOrientationHistory) :
    (fun first second =>
      finiteDepthDecoherence (orientationProjectiveGrowthLaw history) 1
        (depthOnePathEquiv first) (depthOnePathEquiv second)) =
      orientationGrowthDecoherence history := by
  have hLeft :
      (fun first second =>
        finiteDepthDecoherence (orientationProjectiveGrowthLaw history) 1
          (depthOnePathEquiv first) (depthOnePathEquiv second)) =
        unlabeledHistoryKernel history := by
    ext first second
    change amplitudeDecoherence
        (finitePathAmplitude (orientationProjectiveGrowthLaw history) 1)
        (depthOnePathEquiv first) (depthOnePathEquiv second) =
      unlabeledHistoryKernel history first second
    unfold amplitudeDecoherence
    rw [orientationFinitePathAmplitude_one,
      orientationFinitePathAmplitude_one]
    exact congrFun (congrFun
      (orientationProjectiveBranchDecoherence_eq_unlabeledKernel history)
      first) second
  exact hLeft.trans
    (orientationGrowthDecoherence_eq_unlabeledHistoryKernel history).symm

/-- The singleton cylinder event associated with one depth-one route. -/
def orientationRouteCylinder (route : Fin 2) :
    InfiniteCylinderEvent (Fin 2) :=
  Quotient.mk _
    ({ depth := 1
       event := {depthOnePathEquiv route} } :
      CylinderPresentation (Fin 2))

/-- Restricting the infinite-cylinder functional to its two depth-one route
cylinders recovers the exact finite associator decoherence kernel. -/
theorem orientationInfiniteCylinder_restricts_finite
    (history : UnlabeledOrientationHistory) :
    (fun first second =>
      infiniteCylinderDecoherence (orientationProjectiveGrowthLaw history)
        (orientationRouteCylinder first) (orientationRouteCylinder second)) =
      orientationGrowthDecoherence history := by
  ext first second
  unfold orientationRouteCylinder
  rw [infiniteCylinderDecoherence_restricts_finite]
  simp only [growthEventDecoherence, Finset.sum_singleton]
  exact congrFun (congrFun
    (orientationFiniteDepthOne_eq_growthDecoherence history) first) second

/-- Therefore the infinite projective family reduces to the extremal
unlabeled-history kernel selected by the causal orientation endpoint. -/
theorem orientationInfiniteCylinder_restricts_unlabeledKernel
    (history : UnlabeledOrientationHistory) :
    (fun first second =>
      infiniteCylinderDecoherence (orientationProjectiveGrowthLaw history)
        (orientationRouteCylinder first) (orientationRouteCylinder second)) =
      unlabeledHistoryKernel history := by
  rw [orientationInfiniteCylinder_restricts_finite]
  exact orientationGrowthDecoherence_eq_unlabeledHistoryKernel history

/-- **Orientation infinite-cylinder promotion theorem.**  The binary
orientation law is normalized and projectively consistent at every finite
depth, descends to a Hermitian strongly positive normalized functional on
infinite cylinder events, and recovers exactly the finite orientation model
on depth-one route cylinders. -/
theorem orientation_infiniteCylinder_promotion
    (history : UnlabeledOrientationHistory) :
    (∀ n, IsNormalizedGrowthFunctional
      (finiteDepthDecoherence (orientationProjectiveGrowthLaw history) n))
      ∧ (∀ (n) (event₁ event₂ : Finset (GrowthPath (Fin 2) n)),
          growthEventDecoherence
              (finiteDepthDecoherence
                (orientationProjectiveGrowthLaw history) (n + 1))
              (refineGrowthEvent event₁) (refineGrowthEvent event₂) =
            growthEventDecoherence
              (finiteDepthDecoherence
                (orientationProjectiveGrowthLaw history) n)
              event₁ event₂)
      ∧ IsHermitianGrowthFunctional
          (infiniteCylinderDecoherence
            (orientationProjectiveGrowthLaw history))
      ∧ IsStronglyPositiveGrowthFunctional
          (infiniteCylinderDecoherence
            (orientationProjectiveGrowthLaw history))
      ∧ infiniteCylinderDecoherence
          (orientationProjectiveGrowthLaw history)
          (totalInfiniteCylinderEvent (Fin 2))
          (totalInfiniteCylinderEvent (Fin 2)) = 1
      ∧ (fun first second =>
          infiniteCylinderDecoherence
            (orientationProjectiveGrowthLaw history)
            (orientationRouteCylinder first)
            (orientationRouteCylinder second)) =
          unlabeledHistoryKernel history := by
  exact ⟨finiteDepthDecoherence_normalized _,
    finiteDepthDecoherence_projective _,
    infiniteCylinderDecoherence_hermitian _,
    infiniteCylinderDecoherence_stronglyPositive _,
    infiniteCylinderDecoherence_normalized _,
    orientationInfiniteCylinder_restricts_unlabeledKernel history⟩

#print axioms finitePathAmplitude_sum_refine
#print axioms finitePathAmplitude_sum_univ
#print axioms finiteDepthDecoherence_projective
#print axioms normalized_projective_growth_family
#print axioms finiteDepthDecoherence_projective_by
#print axioms CylinderPresentation.realizes_iff_of_equivalent
#print axioms cylinderPresentationAmplitude_eq_of_equivalent
#print axioms infiniteCylinderDecoherence_stronglyPositive
#print axioms infiniteCylinderDecoherence_normalized
#print axioms infiniteCylinderDecoherence_union_left_sameDepth
#print axioms infiniteCylinderQuantumMeasure_nonneg
#print axioms infiniteCylinderQuantumMeasure_gradeTwo_sameDepth
#print axioms normalized_stronglyPositive_infiniteCylinder_family
#print axioms orientationFiniteDepthOne_eq_growthDecoherence
#print axioms orientationInfiniteCylinder_restricts_finite
#print axioms orientation_infiniteCylinder_promotion

end

end UnifiedTheory.Audit.KFOrientationInfiniteCylinderDecoherence
