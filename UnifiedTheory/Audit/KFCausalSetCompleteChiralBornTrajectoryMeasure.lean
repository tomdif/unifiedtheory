/-
  Audit/KFCausalSetCompleteChiralBornTrajectoryMeasure.lean

  INFINITE TRAJECTORY MEASURE FROM THE COMPLETE-CHIRAL BORN LAW

  The finite path law is a projective family of honest probabilities.  This
  module realizes its history-dependent transition weights as Markov kernels
  and applies the Ionescu--Tulcea theorem to obtain a probability measure on
  complete infinite causal-growth trajectories.  The stagewise Born kernel is
  recovered as the regular conditional distribution of the next branch given
  the complete finite history.

  This closes the probability-extension step.  It does not select an
  observation map or prove the stoppable Gate 3 repair inequalities.

  Zero sorry. Zero custom axioms.
-/

import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import UnifiedTheory.Audit.KFCausalSetCompleteChiralBornPathLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetCompleteChiralBornTrajectoryMeasure

noncomputable section

open scoped BigOperators ENNReal
open Set MeasureTheory ProbabilityTheory
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetCompleteChiralBornWeights
open UnifiedTheory.Audit.KFCausalSetCompleteChiralBornPathLaw

/-! ## 1. Discrete branch probability kernels -/

instance causalSetGrowthBranchMeasurableSpace (n : ℕ) :
    MeasurableSpace (CausalSetGrowthBranch n) := ⊤

instance causalSetGrowthBranchNonempty (n : ℕ) :
    Nonempty (CausalSetGrowthBranch n) :=
  ⟨Quotient.mk _ (cardinalCausalAntichain (n + 1))⟩

/-- Convert coordinates indexed by `0,...,n` into the recursively represented
rank-`n+1` path consumed by the causal growth law. -/
def rankedGrowthPathOfIic :
    ∀ n : ℕ, (∀ i : Finset.Iic n, CausalSetGrowthBranch i) →
      RankedGrowthPath CausalSetGrowthBranch (n + 1)
  | 0, history =>
      (PUnit.unit, history ⟨0, Finset.mem_Iic.mpr le_rfl⟩)
  | n + 1, history =>
      (rankedGrowthPathOfIic n
          (fun i => history ⟨i, Finset.mem_Iic.mpr
            (le_trans (Finset.mem_Iic.mp i.property) (Nat.le_succ n))⟩),
        history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)

/-- The normalized PMF of the next causal branch at a given finite history. -/
def completeChiralStageBornPMF
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    PMF (CausalSetGrowthBranch n) :=
  PMF.ofFintype
    (fun child => ENNReal.ofReal
      (completeChiralStageBornWeight chirality n pathPrefix child))
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · rw [completeChiralStageBornWeight_sum_one]
        simp
      · intro child _
        exact completeChiralStageBornWeight_nonneg
          chirality n pathPrefix child)

@[simp]
theorem completeChiralStageBornPMF_apply
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) :
    completeChiralStageBornPMF chirality n pathPrefix child =
      ENNReal.ofReal
        (completeChiralStageBornWeight chirality n pathPrefix child) := rfl

/-- The PMF support is exactly the physical one-element extension graph. -/
theorem completeChiralStageBornPMF_pos_iff_physical
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) :
    0 < completeChiralStageBornPMF chirality n pathPrefix child ↔
      IsPhysicalCausalGrowthStep n pathPrefix child := by
  rw [completeChiralStageBornPMF_apply, ENNReal.ofReal_pos]
  exact completeChiralStageBornWeight_pos_iff_physical
    chirality n pathPrefix child

/-- Initial distribution of the rank-zero branch. -/
def completeChiralInitialBornMeasure (chirality : Fin 2) :
    Measure (CausalSetGrowthBranch 0) :=
  (completeChiralStageBornPMF chirality 0 PUnit.unit).toMeasure

instance completeChiralInitialBornMeasure_isProbabilityMeasure
    (chirality : Fin 2) :
    IsProbabilityMeasure (completeChiralInitialBornMeasure chirality) := by
  unfold completeChiralInitialBornMeasure
  infer_instance

/-- History-dependent Markov kernel selecting the branch at rank `n+1` from
the full trajectory through rank `n`. -/
def completeChiralBornKernel (chirality : Fin 2) (n : ℕ) :
    Kernel
      (∀ i : Finset.Iic n, CausalSetGrowthBranch i)
      (CausalSetGrowthBranch (n + 1)) :=
  Kernel.ofFunOfCountable fun history =>
    (completeChiralStageBornPMF chirality (n + 1)
      (rankedGrowthPathOfIic n history)).toMeasure

instance completeChiralBornKernel_isMarkov
    (chirality : Fin 2) (n : ℕ) :
    IsMarkovKernel (completeChiralBornKernel chirality n) := by
  constructor
  intro history
  change IsProbabilityMeasure
    ((completeChiralStageBornPMF chirality (n + 1)
      (rankedGrowthPathOfIic n history)).toMeasure)
  infer_instance

/-- Point probabilities of the history-dependent kernel are exactly the
normalized complete-chiral squared-amplitude weights. -/
theorem completeChiralBornKernel_apply_singleton
    (chirality : Fin 2) (n : ℕ)
    (history : ∀ i : Finset.Iic n, CausalSetGrowthBranch i)
    (child : CausalSetGrowthBranch (n + 1)) :
    completeChiralBornKernel chirality n history {child} =
      ENNReal.ofReal
        (completeChiralStageBornWeight chirality (n + 1)
          (rankedGrowthPathOfIic n history) child) := by
  change
    (completeChiralStageBornPMF chirality (n + 1)
      (rankedGrowthPathOfIic n history)).toMeasure {child} = _
  rw [PMF.toMeasure_apply_singleton]
  · rfl
  · exact MeasurableSet.of_discrete

/-- A next branch has positive conditional probability exactly when it is a
physical one-element extension of the realized finite history. -/
theorem completeChiralBornKernel_singleton_pos_iff_physical
    (chirality : Fin 2) (n : ℕ)
    (history : ∀ i : Finset.Iic n, CausalSetGrowthBranch i)
    (child : CausalSetGrowthBranch (n + 1)) :
    0 < completeChiralBornKernel chirality n history {child} ↔
      IsPhysicalCausalGrowthStep (n + 1)
        (rankedGrowthPathOfIic n history) child := by
  rw [completeChiralBornKernel_apply_singleton, ENNReal.ofReal_pos]
  exact completeChiralStageBornWeight_pos_iff_physical
    chirality (n + 1) (rankedGrowthPathOfIic n history) child

/-! ## 2. Ionescu--Tulcea infinite causal-growth law -/

/-- The canonical probability measure on complete rank-dependent causal
growth trajectories induced by the complete-chiral Born transition law. -/
def completeChiralBornTrajectoryMeasure (chirality : Fin 2) :
    Measure (∀ n, CausalSetGrowthBranch n) :=
  Kernel.trajMeasure
    (completeChiralInitialBornMeasure chirality)
    (completeChiralBornKernel chirality)

instance completeChiralBornTrajectoryMeasure_isProbabilityMeasure
    (chirality : Fin 2) :
    IsProbabilityMeasure (completeChiralBornTrajectoryMeasure chirality) := by
  unfold completeChiralBornTrajectoryMeasure
  letI : IsProbabilityMeasure (completeChiralInitialBornMeasure chirality) :=
    completeChiralInitialBornMeasure_isProbabilityMeasure chirality
  letI : ∀ n, IsMarkovKernel (completeChiralBornKernel chirality n) :=
    fun n => completeChiralBornKernel_isMarkov chirality n
  infer_instance

/-- The infinite causal-growth law has total mass one. -/
@[simp]
theorem completeChiralBornTrajectoryMeasure_univ
    (chirality : Fin 2) :
    completeChiralBornTrajectoryMeasure chirality Set.univ = 1 :=
  measure_univ

/-- The stagewise complete-chiral Born kernel is the regular conditional law
of the next causal branch given the full history through the current rank. -/
theorem completeChiralBornTrajectory_condDistrib_next
    (chirality : Fin 2) (n : ℕ) :
    condDistrib
        (fun trajectory => trajectory (n + 1))
        (Preorder.frestrictLe n)
        (completeChiralBornTrajectoryMeasure chirality)
      =ᵐ[(completeChiralBornTrajectoryMeasure chirality).map
          (Preorder.frestrictLe n)]
        completeChiralBornKernel chirality n := by
  exact Kernel.condDistrib_trajMeasure

#print axioms completeChiralBornTrajectoryMeasure_univ
#print axioms completeChiralBornTrajectory_condDistrib_next
#print axioms completeChiralBornKernel_singleton_pos_iff_physical

end

end UnifiedTheory.Audit.KFCausalSetCompleteChiralBornTrajectoryMeasure
