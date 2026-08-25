/-
  Audit/KFCausalSetHarmonicBornTrajectoryMeasure.lean

  IONESCU--TULCEA MEASURE FOR THE ACTION-SELECTED HARMONIC BORN LAW

  The canonical harmonic Born-shell law is already Born normalized at every
  finite parent.  This module packages its squared transition amplitudes as
  discrete Markov kernels, applies Ionescu--Tulcea, identifies every finite
  cylinder singleton with the existing `finiteBornPathWeight`, and proves
  that almost every infinite trajectory is physical at every finite depth.

  The trajectory measure therefore uses the same harmonic coupling schedule
  selected by the canonical vacuum spectator action.  It does not assert
  full positive support after the nonlinear radial correction: zero leakage
  away from the physical extension graph is sufficient for the almost-sure
  physical-history theorem proved here.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetCompleteChiralBornTrajectoryMeasure
import UnifiedTheory.Audit.KFCausalSetIntrinsicPairCouplingSelection
import UnifiedTheory.Audit.KFCausalBornNormalizationTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetHarmonicBornTrajectoryMeasure

noncomputable section

open scoped BigOperators ENNReal
open Set MeasureTheory ProbabilityTheory Preorder
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalBornShellGeneralLaw
open UnifiedTheory.Audit.KFCausalBornNormalizationTransfer
open UnifiedTheory.Audit.KFCausalSetMultiplicityCorrectedRunning
open UnifiedTheory.Audit.KFCausalSetMicroscopicSpectatorAction
open UnifiedTheory.Audit.KFCausalSetIntrinsicPairCouplingSelection
open UnifiedTheory.Audit.KFCausalSetCompleteChiralBornTrajectoryMeasure

/-! ## 1. A reusable trajectory constructor for a Born-normalized law -/

/-- The normalized next-branch PMF of an arbitrary Born-normalized causal
growth law. -/
def causalBornStagePMF
    (law : RankedBornNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    PMF (CausalSetGrowthBranch n) :=
  PMF.ofFintype
    (fun child => ENNReal.ofReal
      (Complex.normSq (law.transition n pathPrefix child)))
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · rw [law.bornNormalized]
        simp
      · intro child _
        exact Complex.normSq_nonneg _)

@[simp]
theorem causalBornStagePMF_apply
    (law : RankedBornNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (n : ℕ) (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) :
    causalBornStagePMF law n pathPrefix child =
      ENNReal.ofReal
        (Complex.normSq (law.transition n pathPrefix child)) := rfl

/-- Initial coordinate law at the first causal birth. -/
def causalBornInitialMeasure
    (law : RankedBornNormalizedComplexGrowthLaw CausalSetGrowthBranch) :
    Measure (CausalSetGrowthBranch 0) :=
  (causalBornStagePMF law 0 PUnit.unit).toMeasure

instance causalBornInitialMeasure_isProbabilityMeasure
    (law : RankedBornNormalizedComplexGrowthLaw CausalSetGrowthBranch) :
    IsProbabilityMeasure (causalBornInitialMeasure law) := by
  unfold causalBornInitialMeasure
  infer_instance

/-- History-dependent next-coordinate kernel of a Born-normalized law. -/
def causalBornKernel
    (law : RankedBornNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (n : ℕ) :
    Kernel
      (∀ i : Finset.Iic n, CausalSetGrowthBranch i)
      (CausalSetGrowthBranch (n + 1)) :=
  Kernel.ofFunOfCountable fun history =>
    (causalBornStagePMF law (n + 1)
      (rankedGrowthPathOfIic n history)).toMeasure

instance causalBornKernel_isMarkov
    (law : RankedBornNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (n : ℕ) : IsMarkovKernel (causalBornKernel law n) := by
  constructor
  intro history
  change IsProbabilityMeasure
    ((causalBornStagePMF law (n + 1)
      (rankedGrowthPathOfIic n history)).toMeasure)
  infer_instance

theorem causalBornKernel_apply_singleton
    (law : RankedBornNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (n : ℕ)
    (history : ∀ i : Finset.Iic n, CausalSetGrowthBranch i)
    (child : CausalSetGrowthBranch (n + 1)) :
    causalBornKernel law n history {child} =
      ENNReal.ofReal
        (Complex.normSq
          (law.transition (n + 1) (rankedGrowthPathOfIic n history) child)) := by
  change
    (causalBornStagePMF law (n + 1)
      (rankedGrowthPathOfIic n history)).toMeasure {child} = _
  rw [PMF.toMeasure_apply_singleton]
  · rfl
  · exact MeasurableSet.of_discrete

/-- Ionescu--Tulcea trajectory measure of an arbitrary Born-normalized causal
growth law. -/
def causalBornTrajectoryMeasure
    (law : RankedBornNormalizedComplexGrowthLaw CausalSetGrowthBranch) :
    Measure (∀ n, CausalSetGrowthBranch n) :=
  Kernel.trajMeasure (causalBornInitialMeasure law) (causalBornKernel law)

instance causalBornTrajectoryMeasure_isProbabilityMeasure
    (law : RankedBornNormalizedComplexGrowthLaw CausalSetGrowthBranch) :
    IsProbabilityMeasure (causalBornTrajectoryMeasure law) := by
  unfold causalBornTrajectoryMeasure
  letI : IsProbabilityMeasure (causalBornInitialMeasure law) :=
    causalBornInitialMeasure_isProbabilityMeasure law
  letI : ∀ n, IsMarkovKernel (causalBornKernel law n) :=
    fun n => causalBornKernel_isMarkov law n
  infer_instance

/-! ## 2. Exact finite cylinder marginals -/

/-- At coordinate zero, the trajectory marginal is the supplied initial
measure. -/
theorem causalBornTrajectoryMeasure_map_frestrictLe_zero
    (law : RankedBornNormalizedComplexGrowthLaw CausalSetGrowthBranch) :
    (causalBornTrajectoryMeasure law).map (frestrictLe 0) =
      (causalBornInitialMeasure law).map
        (MeasurableEquiv.piUnique
          (fun i : Finset.Iic 0 => CausalSetGrowthBranch i)).symm := by
  unfold causalBornTrajectoryMeasure
  rw [Kernel.trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe 0),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self]
  simp

/-- Split a history through coordinate `n+1` into its older prefix and newest
coordinate. -/
def splitCausalIicSuccHistory (n : ℕ)
    (history : ∀ i : Finset.Iic (n + 1), CausalSetGrowthBranch i) :
    (∀ i : Finset.Iic n, CausalSetGrowthBranch i) ×
      CausalSetGrowthBranch (n + 1) :=
  (frestrictLe₂ n.le_succ history,
    history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)

theorem frestrictLe_succ_eq_iff_splitCausalIicSuccHistory
    (n : ℕ) (trajectory : ∀ k, CausalSetGrowthBranch k)
    (history : ∀ i : Finset.Iic (n + 1), CausalSetGrowthBranch i) :
    frestrictLe (n + 1) trajectory = history ↔
      (frestrictLe n trajectory, trajectory (n + 1)) =
        splitCausalIicSuccHistory n history := by
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
      have hiEq : i = ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ :=
        Subtype.ext hiLast
      subst i
      have hLast : trajectory (n + 1) =
          history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ :=
        congrArg Prod.snd h
      simpa [frestrictLe] using hLast

theorem causalBornTrajectoryMeasure_map_frestrictLe_succ_singleton
    (law : RankedBornNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (n : ℕ)
    (history : ∀ i : Finset.Iic (n + 1), CausalSetGrowthBranch i) :
    (causalBornTrajectoryMeasure law).map
        (frestrictLe (n + 1)) {history} =
      (causalBornTrajectoryMeasure law).map
        (fun trajectory =>
          (frestrictLe n trajectory, trajectory (n + 1)))
        {splitCausalIicSuccHistory n history} := by
  rw [Measure.map_apply (measurable_frestrictLe (n + 1))
      (MeasurableSet.singleton history),
    Measure.map_apply (by fun_prop)
      (MeasurableSet.singleton (splitCausalIicSuccHistory n history))]
  apply congrArg (causalBornTrajectoryMeasure law)
  ext trajectory
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  exact frestrictLe_succ_eq_iff_splitCausalIicSuccHistory
    n trajectory history

theorem finiteBornPathWeight_nonneg
    (law : RankedBornNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    (n : ℕ) (path : RankedGrowthPath CausalSetGrowthBranch n) :
    0 ≤ finiteBornPathWeight law n path :=
  Complex.normSq_nonneg _

/-- Every finite cylinder singleton has exactly its pre-existing finite Born
path weight. -/
theorem causalBornTrajectoryMeasure_finiteCylinder_singleton :
    ∀ (law : RankedBornNormalizedComplexGrowthLaw CausalSetGrowthBranch)
      (n : ℕ) (history : ∀ i : Finset.Iic n, CausalSetGrowthBranch i),
      (causalBornTrajectoryMeasure law).map (frestrictLe n) {history} =
        ENNReal.ofReal
          (finiteBornPathWeight law (n + 1)
            (rankedGrowthPathOfIic n history)) := by
  intro law n
  induction n with
  | zero =>
      intro history
      rw [causalBornTrajectoryMeasure_map_frestrictLe_zero]
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
          have hi : i = zeroIndex := Subsingleton.elim _ _
          subst i
          simpa using h
      rw [hPreimage]
      change (causalBornStagePMF law 0 PUnit.unit).toMeasure
          {history zeroIndex} = _
      rw [PMF.toMeasure_apply_singleton]
      · simp [causalBornStagePMF_apply, zeroIndex,
          rankedGrowthPathOfIic, finiteBornPathWeight,
          finiteBornPathAmplitude]
      · exact MeasurableSet.of_discrete
  | succ n ih =>
      intro history
      let olderHistory :
          (∀ i : Finset.Iic n, CausalSetGrowthBranch i) :=
        frestrictLe₂ n.le_succ history
      let child : CausalSetGrowthBranch (n + 1) :=
        history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩
      have hSplit :
          splitCausalIicSuccHistory n history =
            (olderHistory, child) := rfl
      rw [causalBornTrajectoryMeasure_map_frestrictLe_succ_singleton]
      rw [hSplit]
      unfold causalBornTrajectoryMeasure
      rw [← Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure]
      rw [show {(olderHistory, child)} =
          {olderHistory} ×ˢ {child} by ext x; simp]
      rw [Measure.compProd_apply_prod
        (MeasurableSet.singleton olderHistory)
        (MeasurableSet.singleton child)]
      rw [lintegral_singleton]
      rw [causalBornKernel_apply_singleton]
      change
        ENNReal.ofReal
            (Complex.normSq
              (law.transition (n + 1)
                (rankedGrowthPathOfIic n olderHistory) child)) *
            (causalBornTrajectoryMeasure law).map
              (frestrictLe n) {olderHistory} = _
      rw [ih olderHistory]
      rw [mul_comm]
      rw [← ENNReal.ofReal_mul
        (finiteBornPathWeight_nonneg law (n + 1)
          (rankedGrowthPathOfIic n olderHistory))]
      simp [finiteBornPathWeight, finiteBornPathAmplitude,
        rankedGrowthPathOfIic, olderHistory, child,
        frestrictLe₂, Complex.normSq_mul]
      rfl

/-! ## 3. The action-selected harmonic specialization -/

def harmonicBornTrajectoryMeasure (chirality : Fin 2) :
    Measure (∀ n, CausalSetGrowthBranch n) :=
  causalBornTrajectoryMeasure
    (canonicalHarmonicBornNormalizedGrowthLaw chirality)

instance harmonicBornTrajectoryMeasure_isProbabilityMeasure
    (chirality : Fin 2) :
    IsProbabilityMeasure (harmonicBornTrajectoryMeasure chirality) := by
  unfold harmonicBornTrajectoryMeasure
  infer_instance

@[simp]
theorem harmonicBornTrajectoryMeasure_univ (chirality : Fin 2) :
    harmonicBornTrajectoryMeasure chirality Set.univ = 1 :=
  measure_univ

/-- Required exact finite-cylinder identification. -/
theorem harmonicBornTrajectoryMeasure_finiteCylinder_singleton
    (chirality : Fin 2) (n : ℕ)
    (history : ∀ i : Finset.Iic n, CausalSetGrowthBranch i) :
    (harmonicBornTrajectoryMeasure chirality).map
        (frestrictLe n) {history} =
      ENNReal.ofReal
        (finiteBornPathWeight
          (canonicalHarmonicBornNormalizedGrowthLaw chirality) (n + 1)
          (rankedGrowthPathOfIic n history)) := by
  exact causalBornTrajectoryMeasure_finiteCylinder_singleton
    (canonicalHarmonicBornNormalizedGrowthLaw chirality) n history

/-- Nonphysical branches have zero harmonic Born probability. -/
theorem harmonicBornTransition_eq_zero_of_not_physical
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n)
    (hNotPhysical : ¬ IsPhysicalCausalGrowthStep n pathPrefix child) :
    (canonicalHarmonicBornNormalizedGrowthLaw chirality).transition
        n pathPrefix child = 0 := by
  exact (canonicalHarmonicCriticalBornShell_all_rank chirality).2.2
    n pathPrefix child hNotPhysical

theorem harmonicBornKernel_singleton_eq_zero_of_not_physical
    (chirality : Fin 2) (n : ℕ)
    (history : ∀ i : Finset.Iic n, CausalSetGrowthBranch i)
    (child : CausalSetGrowthBranch (n + 1))
    (hNotPhysical : ¬ IsPhysicalCausalGrowthStep (n + 1)
      (rankedGrowthPathOfIic n history) child) :
    causalBornKernel (canonicalHarmonicBornNormalizedGrowthLaw chirality)
        n history {child} = 0 := by
  rw [causalBornKernel_apply_singleton,
    harmonicBornTransition_eq_zero_of_not_physical
      chirality (n + 1) (rankedGrowthPathOfIic n history) child hNotPhysical]
  simp

/-- A nonphysical finite path has zero Born weight. -/
theorem harmonicFiniteBornPathWeight_eq_zero_of_not_physical
    (chirality : Fin 2) :
    ∀ (n : ℕ) (path : RankedGrowthPath CausalSetGrowthBranch n),
      ¬ IsPhysicalCausalGrowthPath n path →
        finiteBornPathWeight
          (canonicalHarmonicBornNormalizedGrowthLaw chirality) n path = 0
  | 0, path => by
      intro hNotPhysical
      exact (hNotPhysical trivial).elim
  | n + 1, path => by
      intro hNotPhysical
      change ¬ (IsPhysicalCausalGrowthPath n path.1 ∧
        IsPhysicalCausalGrowthStep n path.1 path.2) at hNotPhysical
      rcases not_and_or.mp hNotPhysical with hPrefix | hStep
      · have hPrefixZero :=
          harmonicFiniteBornPathWeight_eq_zero_of_not_physical
            chirality n path.1 hPrefix
        change Complex.normSq
          (finiteBornPathAmplitude
            (canonicalHarmonicBornNormalizedGrowthLaw chirality)
            n path.1) = 0 at hPrefixZero
        simp only [finiteBornPathWeight, finiteBornPathAmplitude,
          Complex.normSq_mul]
        rw [hPrefixZero, zero_mul]
      · have hStepZero := harmonicBornTransition_eq_zero_of_not_physical
          chirality n path.1 path.2 hStep
        simp only [finiteBornPathWeight, finiteBornPathAmplitude,
          Complex.normSq_mul]
        rw [hStepZero, Complex.normSq_zero, mul_zero]

/-- Physicality of every finite prefix of an infinite causal trajectory. -/
def IsPhysicalInfiniteCausalGrowthTrajectory
    (trajectory : ∀ n, CausalSetGrowthBranch n) : Prop :=
  ∀ n : ℕ,
    IsPhysicalCausalGrowthPath (n + 1)
      (rankedGrowthPathOfIic n (frestrictLe n trajectory))

/-- At each fixed depth, nonphysical prefixes form a null cylinder event. -/
theorem harmonicBornTrajectory_physicalAtDepth_ae
    (chirality : Fin 2) (n : ℕ) :
    ∀ᵐ trajectory ∂harmonicBornTrajectoryMeasure chirality,
      IsPhysicalCausalGrowthPath (n + 1)
        (rankedGrowthPathOfIic n (frestrictLe n trajectory)) := by
  rw [ae_iff]
  let bad : Set (∀ i : Finset.Iic n, CausalSetGrowthBranch i) :=
    {history | ¬ IsPhysicalCausalGrowthPath (n + 1)
      (rankedGrowthPathOfIic n history)}
  change harmonicBornTrajectoryMeasure chirality
      ((frestrictLe n) ⁻¹' bad) = 0
  apply (measure_preimage_eq_zero_iff_of_countable
    (Set.to_countable bad)).2
  intro history hBad
  rw [← Measure.map_apply (measurable_frestrictLe n)
    (MeasurableSet.singleton history)]
  rw [harmonicBornTrajectoryMeasure_finiteCylinder_singleton]
  rw [harmonicFiniteBornPathWeight_eq_zero_of_not_physical
    chirality (n + 1) (rankedGrowthPathOfIic n history) hBad]
  simp

/-- Almost every Ionescu--Tulcea trajectory generated by the harmonic Born
law is physical at every finite depth. -/
theorem harmonicBornTrajectory_physical_ae (chirality : Fin 2) :
    ∀ᵐ trajectory ∂harmonicBornTrajectoryMeasure chirality,
      IsPhysicalInfiniteCausalGrowthTrajectory trajectory := by
  change ∀ᵐ trajectory ∂harmonicBornTrajectoryMeasure chirality,
    ∀ n, IsPhysicalCausalGrowthPath (n + 1)
      (rankedGrowthPathOfIic n (frestrictLe n trajectory))
  rw [ae_all_iff]
  exact harmonicBornTrajectory_physicalAtDepth_ae chirality

/-- No-argument coupling/trajectory capstone: the same canonical action that
selects the harmonic schedule supplies a probability measure with exact
finite Born marginals and almost-sure physical support. -/
theorem canonicalAction_harmonicBornTrajectory_capstone :
    microscopicSpectatorPairCoupling
        canonicalVacuumSpectatorCausalAction = harmonicCriticalPairCoupling
      ∧ (∀ chirality : Fin 2,
          harmonicBornTrajectoryMeasure chirality Set.univ = 1)
      ∧ (∀ (chirality : Fin 2) (n : ℕ)
          (history : ∀ i : Finset.Iic n, CausalSetGrowthBranch i),
          (harmonicBornTrajectoryMeasure chirality).map
              (frestrictLe n) {history} =
            ENNReal.ofReal
              (finiteBornPathWeight
                (canonicalHarmonicBornNormalizedGrowthLaw chirality) (n + 1)
                (rankedGrowthPathOfIic n history)))
      ∧ (∀ chirality : Fin 2,
          ∀ᵐ trajectory ∂harmonicBornTrajectoryMeasure chirality,
            IsPhysicalInfiniteCausalGrowthTrajectory trajectory) := by
  exact ⟨microscopicSpectatorPairCoupling_eq_harmonic
      canonicalVacuumSpectatorCausalAction,
    harmonicBornTrajectoryMeasure_univ,
    harmonicBornTrajectoryMeasure_finiteCylinder_singleton,
    harmonicBornTrajectory_physical_ae⟩

#print axioms causalBornTrajectoryMeasure_finiteCylinder_singleton
#print axioms harmonicBornTrajectoryMeasure_finiteCylinder_singleton
#print axioms harmonicBornTrajectory_physical_ae
#print axioms canonicalAction_harmonicBornTrajectory_capstone

end

end UnifiedTheory.Audit.KFCausalSetHarmonicBornTrajectoryMeasure
