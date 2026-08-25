/-
  Audit/KFCausalSetCompleteChiralBornTrajectoryExtension.lean

  FINITE-MARGINAL AND PHYSICAL-SUPPORT BRIDGES FOR THE COMPLETE-CHIRAL
  BORN TRAJECTORY MEASURE

  The Ionescu--Tulcea trajectory measure is built from the same normalized
  stage weights as the finite complete-chiral Born path law.  This module
  proves the missing identification: every finite cylinder singleton has
  exactly its pre-existing finite-path probability.  It then proves that
  almost every infinite trajectory is physical at every finite depth.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetCompleteChiralBornTrajectoryMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetCompleteChiralBornTrajectoryExtension

noncomputable section

open scoped BigOperators ENNReal
open Set MeasureTheory ProbabilityTheory Preorder
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetCompleteChiralBornWeights
open UnifiedTheory.Audit.KFCausalSetCompleteChiralBornPathLaw
open UnifiedTheory.Audit.KFCausalSetCompleteChiralBornTrajectoryMeasure

/-! ## 1. Exact finite cylinder marginals -/

/-- At rank zero, restricting the trajectory measure to its initial
coordinate recovers the supplied initial Born measure. -/
theorem completeChiralBornTrajectoryMeasure_map_frestrictLe_zero
    (chirality : Fin 2) :
    (completeChiralBornTrajectoryMeasure chirality).map
        (Preorder.frestrictLe 0) =
      (completeChiralInitialBornMeasure chirality).map
        (MeasurableEquiv.piUnique
          (fun i : Finset.Iic 0 => CausalSetGrowthBranch i)).symm := by
  unfold completeChiralBornTrajectoryMeasure
  rw [Kernel.trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe 0),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self]
  simp

/-- Split a history through rank `n + 1` into its history through rank `n`
and its newest branch. -/
def splitIicSuccHistory (n : ℕ)
    (history : ∀ i : Finset.Iic (n + 1), CausalSetGrowthBranch i) :
    (∀ i : Finset.Iic n, CausalSetGrowthBranch i) ×
      CausalSetGrowthBranch (n + 1) :=
  (frestrictLe₂ n.le_succ history,
    history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)

/-- Equality of a complete prefix through `n + 1` is equivalent to equality
of its older prefix and newest coordinate. -/
theorem frestrictLe_succ_eq_iff_splitIicSuccHistory
    (n : ℕ)
    (trajectory : ∀ k, CausalSetGrowthBranch k)
    (history : ∀ i : Finset.Iic (n + 1), CausalSetGrowthBranch i) :
    frestrictLe (n + 1) trajectory = history ↔
      (frestrictLe n trajectory, trajectory (n + 1)) =
        splitIicSuccHistory n history := by
  constructor
  · intro h
    subst history
    rfl
  · intro h
    funext i
    by_cases hi : i.1 ≤ n
    · have hPrefix :
          frestrictLe n trajectory = frestrictLe₂ n.le_succ history :=
        congrArg Prod.fst h
      simpa [frestrictLe, frestrictLe₂] using
        congrFun hPrefix ⟨i.1, Finset.mem_Iic.mpr hi⟩
    · have hiLast : i.1 = n + 1 := by
        have hiBound : i.1 ≤ n + 1 := Finset.mem_Iic.mp i.property
        omega
      have hiEq :
          i = ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ :=
        Subtype.ext hiLast
      subst i
      have hLast :
          trajectory (n + 1) =
            history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ :=
        congrArg Prod.snd h
      simpa [frestrictLe] using hLast

/-- Restricting to a singleton history through `n + 1` is the same cylinder
as restricting to the corresponding older-history/newest-branch pair. -/
theorem completeChiralBornTrajectoryMeasure_map_frestrictLe_succ_singleton
    (chirality : Fin 2) (n : ℕ)
    (history : ∀ i : Finset.Iic (n + 1), CausalSetGrowthBranch i) :
    (completeChiralBornTrajectoryMeasure chirality).map
        (frestrictLe (n + 1)) {history} =
      (completeChiralBornTrajectoryMeasure chirality).map
        (fun trajectory =>
          (frestrictLe n trajectory, trajectory (n + 1)))
        {splitIicSuccHistory n history} := by
  rw [Measure.map_apply (measurable_frestrictLe (n + 1))
      (MeasurableSet.singleton history),
    Measure.map_apply (by fun_prop)
      (MeasurableSet.singleton (splitIicSuccHistory n history))]
  apply congrArg (completeChiralBornTrajectoryMeasure chirality)
  ext trajectory
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  exact frestrictLe_succ_eq_iff_splitIicSuccHistory n trajectory history

/-- Every finite cylinder singleton of the Ionescu--Tulcea measure has exactly
the probability assigned by the pre-existing complete-chiral finite path
law.  The indexing says that a history through coordinate `n` is a ranked
path of depth `n + 1`. -/
theorem completeChiralBornTrajectoryMeasure_finiteCylinder_singleton :
    ∀ (chirality : Fin 2) (n : ℕ)
      (history : ∀ i : Finset.Iic n, CausalSetGrowthBranch i),
      (completeChiralBornTrajectoryMeasure chirality).map
          (frestrictLe n) {history} =
        ENNReal.ofReal
          (completeChiralFinitePathProbability chirality (n + 1)
            (rankedGrowthPathOfIic n history)) := by
  intro chirality n
  induction n with
  | zero =>
      intro history
      rw [completeChiralBornTrajectoryMeasure_map_frestrictLe_zero]
      rw [Measure.map_apply (by fun_prop)
        (MeasurableSet.singleton history)]
      let zeroIndex : Finset.Iic 0 :=
        ⟨0, Finset.mem_Iic.mpr le_rfl⟩
      have hPreimage :
          (⇑(MeasurableEquiv.piUnique
              (fun i : Finset.Iic 0 => CausalSetGrowthBranch i)).symm) ⁻¹'
              ({history} : Set
                (∀ i : Finset.Iic 0, CausalSetGrowthBranch i)) =
            ({history zeroIndex} : Set (CausalSetGrowthBranch 0)) := by
        ext child
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · intro h
          have hAtZero := congrFun h zeroIndex
          simpa using hAtZero
        · intro h
          funext i
          have hi : i = zeroIndex :=
            Subsingleton.elim _ _
          subst i
          simpa using h
      rw [hPreimage]
      change
        (completeChiralStageBornPMF chirality 0 PUnit.unit).toMeasure
            {history zeroIndex} = _
      rw [PMF.toMeasure_apply_singleton]
      · simp [completeChiralStageBornPMF_apply, zeroIndex,
          rankedGrowthPathOfIic, completeChiralFinitePathProbability]
      · exact MeasurableSet.of_discrete
  | succ n ih =>
      intro history
      let olderHistory :
          (∀ i : Finset.Iic n, CausalSetGrowthBranch i) :=
        frestrictLe₂ n.le_succ history
      let child : CausalSetGrowthBranch (n + 1) :=
        history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩
      have hOlderHistory :
          olderHistory =
            (fun (i : Finset.Iic n) => history
              ⟨i, Finset.mem_Iic.mpr
                (le_trans (Finset.mem_Iic.mp i.property)
                  (Nat.le_succ n))⟩) := by
        funext i
        rfl
      have hSplit :
          splitIicSuccHistory n history = (olderHistory, child) := rfl
      rw [completeChiralBornTrajectoryMeasure_map_frestrictLe_succ_singleton]
      rw [hSplit]
      unfold completeChiralBornTrajectoryMeasure
      rw [← Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure]
      rw [show {(olderHistory, child)} =
          {olderHistory} ×ˢ {child} by ext x; simp]
      rw [Measure.compProd_apply_prod
        (MeasurableSet.singleton olderHistory)
        (MeasurableSet.singleton child)]
      rw [lintegral_singleton]
      rw [completeChiralBornKernel_apply_singleton]
      change
        ENNReal.ofReal
            (completeChiralStageBornWeight chirality (n + 1)
              (rankedGrowthPathOfIic n olderHistory) child) *
            (completeChiralBornTrajectoryMeasure chirality).map
              (frestrictLe n) {olderHistory} = _
      rw [ih olderHistory]
      rw [mul_comm]
      rw [← ENNReal.ofReal_mul
        (completeChiralFinitePathProbability_nonneg chirality (n + 1)
          (rankedGrowthPathOfIic n olderHistory))]
      rw [hOlderHistory]
      simp [completeChiralFinitePathProbability,
        rankedGrowthPathOfIic, child]

/-! ## 2. Almost-sure physical support -/

/-- Nonphysical finite paths have exactly zero complete-chiral Born
probability. -/
theorem completeChiralFinitePathProbability_eq_zero_of_not_physical
    (chirality : Fin 2) (n : ℕ)
    (path : RankedGrowthPath CausalSetGrowthBranch n)
    (hNotPhysical : ¬ IsPhysicalCausalGrowthPath n path) :
    completeChiralFinitePathProbability chirality n path = 0 := by
  have hNonneg :=
    completeChiralFinitePathProbability_nonneg chirality n path
  apply le_antisymm _ hNonneg
  apply le_of_not_gt
  intro hPos
  exact hNotPhysical
    ((completeChiralFinitePathProbability_pos_iff_physical
      chirality n path).1 hPos)

/-- Physicality of every finite prefix of an infinite complete-chiral
trajectory. -/
def IsCompleteChiralPhysicalTrajectory
    (trajectory : ∀ n, CausalSetGrowthBranch n) : Prop :=
  ∀ n : ℕ,
    IsPhysicalCausalGrowthPath (n + 1)
      (rankedGrowthPathOfIic n (frestrictLe n trajectory))

/-- At each fixed depth, the nonphysical prefix cylinders are null. -/
theorem completeChiralBornTrajectoryMeasure_physicalAtDepth_ae
    (chirality : Fin 2) (n : ℕ) :
    ∀ᵐ trajectory ∂completeChiralBornTrajectoryMeasure chirality,
      IsPhysicalCausalGrowthPath (n + 1)
        (rankedGrowthPathOfIic n (frestrictLe n trajectory)) := by
  rw [ae_iff]
  let bad : Set (∀ i : Finset.Iic n, CausalSetGrowthBranch i) :=
    {history | ¬ IsPhysicalCausalGrowthPath (n + 1)
      (rankedGrowthPathOfIic n history)}
  change completeChiralBornTrajectoryMeasure chirality
      ((frestrictLe n) ⁻¹' bad) = 0
  apply (measure_preimage_eq_zero_iff_of_countable
    (Set.to_countable bad)).2
  intro history hBad
  rw [← Measure.map_apply (measurable_frestrictLe n)
    (MeasurableSet.singleton history)]
  rw [completeChiralBornTrajectoryMeasure_finiteCylinder_singleton]
  rw [completeChiralFinitePathProbability_eq_zero_of_not_physical
    chirality (n + 1) (rankedGrowthPathOfIic n history) hBad]
  simp

/-- Almost every Ionescu--Tulcea trajectory generated by the complete-chiral
Born kernels is physical at every finite depth. -/
theorem completeChiralBornTrajectoryMeasure_ae_physical
    (chirality : Fin 2) :
    ∀ᵐ trajectory ∂completeChiralBornTrajectoryMeasure chirality,
      IsCompleteChiralPhysicalTrajectory trajectory := by
  change
    ∀ᵐ trajectory ∂completeChiralBornTrajectoryMeasure chirality,
      ∀ n : ℕ,
        IsPhysicalCausalGrowthPath (n + 1)
          (rankedGrowthPathOfIic n (frestrictLe n trajectory))
  rw [ae_all_iff]
  exact completeChiralBornTrajectoryMeasure_physicalAtDepth_ae chirality

/-- The measurable event of trajectories that are physical at every finite
depth. -/
def completeChiralPhysicalTrajectories :
    Set (∀ n, CausalSetGrowthBranch n) :=
  {trajectory | IsCompleteChiralPhysicalTrajectory trajectory}

theorem measurableSet_completeChiralPhysicalTrajectories :
    MeasurableSet completeChiralPhysicalTrajectories := by
  rw [show completeChiralPhysicalTrajectories =
      ⋂ n : ℕ, (frestrictLe n) ⁻¹'
        {history | IsPhysicalCausalGrowthPath (n + 1)
          (rankedGrowthPathOfIic n history)} by
    ext trajectory
    simp [completeChiralPhysicalTrajectories,
      IsCompleteChiralPhysicalTrajectory]]
  exact MeasurableSet.iInter fun n =>
    MeasurableSet.preimage MeasurableSet.of_discrete
      (measurable_frestrictLe n)

/-- Equivalently, the measurable event of complete physical trajectories has
probability one. -/
theorem completeChiralBornTrajectoryMeasure_physicalTrajectories_eq_one
    (chirality : Fin 2) :
    completeChiralBornTrajectoryMeasure chirality
        completeChiralPhysicalTrajectories = 1 := by
  apply (mem_ae_iff_prob_eq_one
    measurableSet_completeChiralPhysicalTrajectories).1
  simpa [completeChiralPhysicalTrajectories] using
    completeChiralBornTrajectoryMeasure_ae_physical chirality

#print axioms completeChiralBornTrajectoryMeasure_finiteCylinder_singleton
#print axioms completeChiralBornTrajectoryMeasure_physicalAtDepth_ae
#print axioms completeChiralBornTrajectoryMeasure_ae_physical
#print axioms completeChiralBornTrajectoryMeasure_physicalTrajectories_eq_one

end

end UnifiedTheory.Audit.KFCausalSetCompleteChiralBornTrajectoryExtension
