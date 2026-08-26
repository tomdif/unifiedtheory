/-
  Audit/KFGate6HarmonicBornBinaryQQGReadout.lean

  A NONCONSTANT TYPED HARMONIC-TRAJECTORY -> QQG READOUT

  The generic Gate 6 adapter correctly leaves its cosmological readout as
  data.  Here we construct one concrete, measurable, nonconstant example.  It
  reads the first genuine causal choice and sends the gregarious/timid branch
  to two distinct positive QQG scenarios.

  This removes the bare type/measurability existence problem.  It does not
  claim that this binary map is the physically correct cosmological coarse
  graining, nor that either scenario satisfies the still-external QQG
  emergence hypotheses or observational constraints.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFGate6ActionSelectedHarmonicBornInitialMeasureAdapter
import UnifiedTheory.Audit.KFCausalSetHarmonicBornRankOneAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFGate6HarmonicBornBinaryQQGReadout

noncomputable section

open Set MeasureTheory ProbabilityTheory Preorder
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetChiralGrowth
open UnifiedTheory.Audit.KFCausalBornNormalizationTransfer
open UnifiedTheory.Audit.KFCausalSetCompleteChiralBornTrajectoryMeasure
open UnifiedTheory.Audit.KFCausalSetHarmonicBornTrajectoryMeasure
open UnifiedTheory.Audit.KFCausalSetHarmonicBornRankOneAudit
open UnifiedTheory.Audit.KFGate6ActionSelectedHarmonicBornInitialMeasureAdapter
open UnifiedTheory.Cosmology.QQG

local instance qqgScenarioMeasurableSpace : MeasurableSpace QQGScenario := ⊤

/-! ## 1. Two explicit positive QQG scenarios -/

def binaryQQGLowScenario : QQGScenario where
  lam₀ := 1
  μ₀ := 1
  N := 1
  N_e := 50
  lam₀_pos := by norm_num
  μ₀_pos := by norm_num
  N_pos := by norm_num
  N_e_pos := by norm_num

def binaryQQGHighScenario : QQGScenario where
  lam₀ := 1
  μ₀ := 1
  N := 1
  N_e := 60
  lam₀_pos := by norm_num
  μ₀_pos := by norm_num
  N_pos := by norm_num
  N_e_pos := by norm_num

theorem binaryQQGScenarios_ne :
    binaryQQGLowScenario ≠ binaryQQGHighScenario := by
  intro h
  have hN := congrArg QQGScenario.N_e h
  norm_num [binaryQQGLowScenario, binaryQQGHighScenario] at hN

/-! ## 2. First-branch readout -/

/-- The first genuinely stochastic causal branch chooses one of the two QQG
parameter records. -/
def harmonicRankOneQQGReadout
    (trajectory : ∀ n : ℕ, CausalSetGrowthBranch n) : QQGScenario :=
  if trajectory 1 = rankOneGregariousChild then binaryQQGLowScenario
  else binaryQQGHighScenario

theorem harmonicRankOneQQGReadout_measurable :
    Measurable harmonicRankOneQQGReadout := by
  apply (measurable_of_finite
    (fun child : CausalSetGrowthBranch 1 =>
      if child = rankOneGregariousChild then binaryQQGLowScenario
      else binaryQQGHighScenario)).comp
  exact measurable_pi_apply 1

def binaryQQGAdmissibleSector : Set QQGScenario :=
  {binaryQQGLowScenario, binaryQQGHighScenario}

theorem binaryQQGAdmissibleSector_measurable :
    MeasurableSet binaryQQGAdmissibleSector :=
  MeasurableSet.of_discrete

theorem harmonicRankOneQQGReadout_mem_admissible
    (trajectory : ∀ n : ℕ, CausalSetGrowthBranch n) :
    harmonicRankOneQQGReadout trajectory ∈ binaryQQGAdmissibleSector := by
  by_cases h : trajectory 1 = rankOneGregariousChild
  · simp [harmonicRankOneQQGReadout, binaryQQGAdmissibleSector, h]
  · simp [harmonicRankOneQQGReadout, binaryQQGAdmissibleSector, h]

/-- This is a fully typed instance of the previously external readout record.
Its admissible sector is precisely the two explicitly displayed positive QQG
parameter records. -/
def harmonicBinaryQQGCosmologicalReadoutBridge (chirality : Fin 2) :
    Gate6ActionSelectedHarmonicBornCosmologicalReadoutBridge chirality
      QQGScenario binaryQQGAdmissibleSector where
  readout := harmonicRankOneQQGReadout
  readoutMeasurable := harmonicRankOneQQGReadout_measurable
  admissibleMeasurable := binaryQQGAdmissibleSector_measurable
  almostEveryTrajectoryAdmissible :=
    Filter.Eventually.of_forall harmonicRankOneQQGReadout_mem_admissible

/-! ## 3. The readout is not a constant-map loophole -/

def trajectoryWithRankOneChild (child : CausalSetGrowthBranch 1) :
    ∀ n : ℕ, CausalSetGrowthBranch n :=
  fun n => if h : n = 1 then
    cast (congrArg CausalSetGrowthBranch h.symm) child
  else Classical.choice (causalSetGrowthBranchNonempty n)

@[simp]
theorem trajectoryWithRankOneChild_at_one
    (child : CausalSetGrowthBranch 1) :
    trajectoryWithRankOneChild child 1 = child := by
  simp [trajectoryWithRankOneChild]

theorem harmonicRankOneQQGReadout_gregarious :
    harmonicRankOneQQGReadout
        (trajectoryWithRankOneChild rankOneGregariousChild) =
      binaryQQGLowScenario := by
  simp [harmonicRankOneQQGReadout]

theorem harmonicRankOneQQGReadout_timid :
    harmonicRankOneQQGReadout
        (trajectoryWithRankOneChild rankOneTimidChild) =
      binaryQQGHighScenario := by
  have h : rankOneTimidChild ≠ rankOneGregariousChild :=
    Ne.symm rankOne_children_ne
  simp [harmonicRankOneQQGReadout, h]

theorem harmonicRankOneQQGReadout_nonconstant :
    ∃ first second : ∀ n : ℕ, CausalSetGrowthBranch n,
      harmonicRankOneQQGReadout first ≠ harmonicRankOneQQGReadout second := by
  refine ⟨trajectoryWithRankOneChild rankOneGregariousChild,
    trajectoryWithRankOneChild rankOneTimidChild, ?_⟩
  rw [harmonicRankOneQQGReadout_gregarious,
    harmonicRankOneQQGReadout_timid]
  exact binaryQQGScenarios_ne

/-- The induced pushforward is an honest probability measure supported on the
displayed binary QQG sector. -/
def harmonicBinaryQQGInitialMeasure (chirality : Fin 2) :
    Gate6AdmissibleCosmologicalInitialMeasure
      QQGScenario binaryQQGAdmissibleSector :=
  (harmonicBinaryQQGCosmologicalReadoutBridge chirality).toAdmissibleCosmologicalInitialMeasure

/-! ## 4. Exact binary pushforward law -/

/-- The unique finite history through coordinate one whose newest child is
`child`.  Coordinate zero is forced, so this cylinder is exactly the event
that the first genuine causal choice equals `child`. -/
def rankOneCylinderHistory (child : CausalSetGrowthBranch 1) :
    ∀ i : Finset.Iic 1, CausalSetGrowthBranch i :=
  frestrictLe 1 (trajectoryWithRankOneChild child)

@[simp]
theorem rankOneCylinderHistory_at_one
    (child : CausalSetGrowthBranch 1) :
    rankOneCylinderHistory child
        ⟨1, Finset.mem_Iic.mpr le_rfl⟩ = child := by
  simp [rankOneCylinderHistory, frestrictLe]

theorem frestrictLe_one_eq_rankOneCylinderHistory_iff
    (trajectory : ∀ n : ℕ, CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch 1) :
    frestrictLe 1 trajectory = rankOneCylinderHistory child ↔
      trajectory 1 = child := by
  constructor
  · intro h
    have hOne := congrFun h ⟨1, Finset.mem_Iic.mpr le_rfl⟩
    simpa [frestrictLe] using hOne
  · intro h
    funext i
    have hiBound : i.1 ≤ 1 := Finset.mem_Iic.mp i.property
    have hi : i.1 = 0 ∨ i.1 = 1 := by
      omega
    rcases hi with hi | hi
    · have hiSubtype : i = ⟨0, Finset.mem_Iic.mpr (by omega)⟩ :=
        Subtype.ext hi
      rw [hiSubtype]
      change trajectory 0 = trajectoryWithRankOneChild child 0
      exact
        (unlabeledCardinalCausalOrder_one_unique (trajectory 0)).trans
          (unlabeledCardinalCausalOrder_one_unique
            (trajectoryWithRankOneChild child 0)).symm
    · have hiSubtype : i = ⟨1, Finset.mem_Iic.mpr le_rfl⟩ :=
        Subtype.ext hi
      rw [hiSubtype]
      simpa [rankOneCylinderHistory, frestrictLe] using h

/-- The forced root coordinate has Born probability one.  Only squared
modulus is needed here, so coherent phase uniqueness is irrelevant. -/
theorem canonicalHarmonicBorn_rankZero_probability
    (chirality : Fin 2)
    (child : CausalSetGrowthBranch 0) :
    Complex.normSq
      ((canonicalHarmonicBornNormalizedGrowthLaw chirality).transition
        0 PUnit.unit child) = 1 := by
  have hNormalized :=
    (canonicalHarmonicBornNormalizedGrowthLaw chirality).bornNormalized
      0 PUnit.unit
  calc
    Complex.normSq
        ((canonicalHarmonicBornNormalizedGrowthLaw chirality).transition
          0 PUnit.unit child) =
      ∑ other : CausalSetGrowthBranch 0,
        Complex.normSq
          ((canonicalHarmonicBornNormalizedGrowthLaw chirality).transition
            0 PUnit.unit other) := by
          symm
          apply Fintype.sum_eq_single child
          intro other hDifferent
          exact (hDifferent
            ((unlabeledCardinalCausalOrder_one_unique other).trans
              (unlabeledCardinalCausalOrder_one_unique child).symm)).elim
    _ = 1 := hNormalized

/-- Exact trajectory mass of the gregarious first causal choice. -/
theorem harmonicBornTrajectoryMeasure_rankOne_gregarious
    (chirality : Fin 2) :
    harmonicBornTrajectoryMeasure chirality
        {trajectory | trajectory 1 = rankOneGregariousChild} = 1 / 2 := by
  let history := rankOneCylinderHistory rankOneGregariousChild
  calc
    harmonicBornTrajectoryMeasure chirality
        {trajectory | trajectory 1 = rankOneGregariousChild} =
      (harmonicBornTrajectoryMeasure chirality).map
        (frestrictLe 1) {history} := by
          rw [Measure.map_apply (measurable_frestrictLe 1)
            (MeasurableSet.singleton history)]
          apply congrArg (harmonicBornTrajectoryMeasure chirality)
          ext trajectory
          simp only [Set.mem_setOf_eq, Set.mem_preimage,
            Set.mem_singleton_iff]
          exact
            (frestrictLe_one_eq_rankOneCylinderHistory_iff
              trajectory rankOneGregariousChild).symm
    _ = ENNReal.ofReal
        (finiteBornPathWeight
          (canonicalHarmonicBornNormalizedGrowthLaw chirality) 2
          (rankedGrowthPathOfIic 1 history)) :=
      harmonicBornTrajectoryMeasure_finiteCylinder_singleton
        chirality 1 history
    _ = 1 / 2 := by
      simp only [finiteBornPathWeight, finiteBornPathAmplitude,
        rankedGrowthPathOfIic]
      simp only [one_mul]
      rw [show history ⟨1, Finset.mem_Iic.mpr le_rfl⟩ =
          rankOneGregariousChild by
        exact rankOneCylinderHistory_at_one rankOneGregariousChild]
      rw [Complex.normSq_mul,
        canonicalHarmonicBorn_rankZero_probability,
        canonicalHarmonicBorn_rankOne_gregarious_probability]
      rw [one_mul]
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num

/-- The low QQG singleton inherits exactly the gregarious rank-one mass. -/
theorem harmonicBinaryQQGInitialMeasure_low
    (chirality : Fin 2) :
    (harmonicBinaryQQGInitialMeasure chirality).measure
        {binaryQQGLowScenario} = 1 / 2 := by
  change (harmonicBornTrajectoryMeasure chirality).map
    harmonicRankOneQQGReadout {binaryQQGLowScenario} = 1 / 2
  rw [Measure.map_apply harmonicRankOneQQGReadout_measurable
    (MeasurableSet.singleton binaryQQGLowScenario)]
  have hPreimage :
      harmonicRankOneQQGReadout ⁻¹' ({binaryQQGLowScenario} : Set QQGScenario) =
        {trajectory | trajectory 1 = rankOneGregariousChild} := by
    ext trajectory
    by_cases h : trajectory 1 = rankOneGregariousChild
    · simp [harmonicRankOneQQGReadout, h]
    · simp [harmonicRankOneQQGReadout, h, binaryQQGScenarios_ne.symm]
  rw [hPreimage, harmonicBornTrajectoryMeasure_rankOne_gregarious]

/-- The high QQG singleton is the complementary binary outcome and therefore
also has exact mass one half. -/
theorem harmonicBinaryQQGInitialMeasure_high
    (chirality : Fin 2) :
    (harmonicBinaryQQGInitialMeasure chirality).measure
        {binaryQQGHighScenario} = 1 / 2 := by
  change (harmonicBornTrajectoryMeasure chirality).map
    harmonicRankOneQQGReadout {binaryQQGHighScenario} = 1 / 2
  rw [Measure.map_apply harmonicRankOneQQGReadout_measurable
    (MeasurableSet.singleton binaryQQGHighScenario)]
  have hPreimage :
      harmonicRankOneQQGReadout ⁻¹'
          ({binaryQQGHighScenario} : Set QQGScenario) =
        {trajectory | trajectory 1 ≠ rankOneGregariousChild} := by
    ext trajectory
    by_cases h : trajectory 1 = rankOneGregariousChild
    · simp [harmonicRankOneQQGReadout, h, binaryQQGScenarios_ne]
    · simp [harmonicRankOneQQGReadout, h]
  rw [hPreimage]
  rw [show {trajectory | trajectory 1 ≠ rankOneGregariousChild} =
      ({trajectory | trajectory 1 = rankOneGregariousChild} :
        Set (∀ n : ℕ, CausalSetGrowthBranch n))ᶜ by ext; simp]
  have hMeasurable :
      MeasurableSet
        ({trajectory | trajectory 1 = rankOneGregariousChild} :
          Set (∀ n : ℕ, CausalSetGrowthBranch n)) :=
    (MeasurableSet.singleton rankOneGregariousChild).preimage
      (measurable_pi_apply 1)
  have hFinite :
      harmonicBornTrajectoryMeasure chirality
          {trajectory | trajectory 1 = rankOneGregariousChild} ≠ ⊤ := by
    rw [harmonicBornTrajectoryMeasure_rankOne_gregarious]
    norm_num
  rw [measure_compl hMeasurable hFinite, measure_univ,
    harmonicBornTrajectoryMeasure_rankOne_gregarious]
  norm_num

#print axioms harmonicRankOneQQGReadout_nonconstant
#print axioms harmonicBinaryQQGInitialMeasure
#print axioms harmonicBornTrajectoryMeasure_rankOne_gregarious
#print axioms harmonicBinaryQQGInitialMeasure_low
#print axioms harmonicBinaryQQGInitialMeasure_high

end

end UnifiedTheory.Audit.KFGate6HarmonicBornBinaryQQGReadout
