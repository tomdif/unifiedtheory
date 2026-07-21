/-
  Audit/KFCausalSetChiralityChargePartitionNoGo.lean

  THE FIRST CHARGE PARTITION IS NOT DECOHERENT

  A probability statement about accumulated chirality evidence is licensed by
  the closed quantum growth law only on a decoherent history partition.  This
  module checks that prerequisite at the first nontrivial source ensemble:
  one birth above the two-antichain, from parent rank two to child rank three.

  The three source bins have distinct evidence charges

      0, artanh(1/4), artanh(2/5).

  Nevertheless, the harmonic decoherence functional has the exact nonzero
  empty/full entry `-784/2113`.  More strongly, both nontrivial threshold cuts
  of the ordered charge profile have nonzero cross-decoherence.  Hence neither
  the fine charge-value partition nor either one-step charge-concentration
  event carries a classical probability under the unextended source
  functional.

  Projective consistency transports this obstruction through every exhaustive
  cylinder refinement whenever the local partition is realized as a cylinder
  partition.  Refinement cannot repair it.  The finite-rank typicality program
  therefore already needs the separately named protected common-chirality
  factorization (or another genuinely decohering record construction).

  This is a cylinder-algebra obstruction.  It does not assign a quantum
  measure to the infinite charge-divergence tail event.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetChiralityEvidenceAsymptotics
import UnifiedTheory.Audit.KFCausalSetSourceInterferenceRefinement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetChiralityChargePartitionNoGo

noncomputable section

open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetMultiplicityCorrectedRunning
open UnifiedTheory.Audit.KFCausalSetSourceQuantumEnsemble
open UnifiedTheory.Audit.KFCausalSetSourceInterferenceRefinement
open UnifiedTheory.Audit.KFCausalSetChiralityEvidenceAsymptotics

/-! ## 1. The rank-two-to-rank-three charge profile -/

/-- Evidence charge of one source bin above the two-antichain. -/
def antichainTwoSourceBinCharge (bin : Fin 3) : ℝ :=
  chiralityEvidenceCharge (antichainTwoSourceBinParameter bin)

theorem antichainTwoSourceBinCharge_exact :
    antichainTwoSourceBinCharge 0 = 0
      ∧ antichainTwoSourceBinCharge 1 = Real.artanh (1 / 4)
      ∧ antichainTwoSourceBinCharge 2 = Real.artanh (2 / 5) := by
  norm_num [antichainTwoSourceBinCharge, chiralityEvidenceCharge,
    antichainTwoSourceBinParameter]

/-- The three charges are strictly ordered. -/
theorem antichainTwoSourceBinCharge_strict :
    antichainTwoSourceBinCharge 0 < antichainTwoSourceBinCharge 1
      ∧ antichainTwoSourceBinCharge 1 < antichainTwoSourceBinCharge 2 := by
  rw [antichainTwoSourceBinCharge_exact.1,
    antichainTwoSourceBinCharge_exact.2.1,
    antichainTwoSourceBinCharge_exact.2.2]
  constructor
  · rw [← Real.artanh_zero]
    exact Real.artanh_lt_artanh (by norm_num) (by norm_num) (by norm_num)
  · exact Real.artanh_lt_artanh (by norm_num) (by norm_num) (by norm_num)

theorem antichainTwoSourceBinCharge_injective :
    Function.Injective antichainTwoSourceBinCharge := by
  intro first second hCharge
  have hInterior : ∀ bin : Fin 3,
      2 * antichainTwoSourceBinParameter bin ∈ Set.Ioo (-1 : ℝ) 1 := by
    intro bin
    fin_cases bin <;> norm_num [antichainTwoSourceBinParameter]
  have hScaled :
      2 * antichainTwoSourceBinParameter first =
        2 * antichainTwoSourceBinParameter second := by
    apply Real.strictMonoOn_artanh.injOn
      (hInterior first) (hInterior second)
    exact hCharge
  fin_cases first <;> fin_cases second
  all_goals try rfl
  all_goals norm_num [antichainTwoSourceBinParameter] at hScaled

/-- Exact pairwise decoherence across distinct values of a retained label. -/
def IsExactlyDecoherentAcrossValues {History : Type*}
    (value : History → ℝ) (D : GrowthDecoherenceFunctional History) : Prop :=
  ∀ first second, value first ≠ value second → D first second = 0

/-! ## 2. The finest charge partition already fails -/

/-- The charge-value partition is not exactly decoherent.  Because the charge
map is injective here, this is the finest possible charge partition. -/
theorem harmonicAntichainTwo_chargeValuePartition_not_decoherent
    (chirality : Fin 2) :
    ¬IsExactlyDecoherentAcrossValues antichainTwoSourceBinCharge
      (harmonicAntichainTwoSourceBinDecoherence chirality) := by
  intro hDecoherent
  have hChargeNe :
      antichainTwoSourceBinCharge 0 ≠
        antichainTwoSourceBinCharge 2 := by
    intro hEqual
    have hBin : (0 : Fin 3) = 2 :=
      antichainTwoSourceBinCharge_injective hEqual
    have hVal := congrArg Fin.val hBin
    norm_num at hVal
  exact harmonicAntichainTwoSourceBinDecoherence_zero_two_ne_zero chirality
    (hDecoherent 0 2 hChargeNe)

/-! ## 3. Both nontrivial one-step threshold cuts fail -/

/-- Low-charge cell for a threshold between the first two charge values. -/
def lowChargeCell₀ : Finset (Fin 3) := {0}

/-- Complementary high-charge cell for the first threshold. -/
def highChargeCell₀ : Finset (Fin 3) := {1, 2}

/-- Low-charge cell for a threshold between the last two charge values. -/
def lowChargeCell₁ : Finset (Fin 3) := {0, 1}

/-- Complementary high-charge cell for the second threshold. -/
def highChargeCell₁ : Finset (Fin 3) := {2}

theorem harmonicAntichainTwo_decoherence_zero_one_re
    (chirality : Fin 2) :
    (harmonicAntichainTwoSourceBinDecoherence chirality 0 1).re = 0 := by
  have hInterference :=
    harmonicAntichainTwoSourceBinInterference_zero_one chirality
  change (2 * (harmonicAntichainTwoSourceBinDecoherence chirality 0 1).re = 0) at hInterference
  linarith

theorem harmonicAntichainTwo_decoherence_one_two_re
    (chirality : Fin 2) :
    (harmonicAntichainTwoSourceBinDecoherence chirality 1 2).re = 0 := by
  have hInterference :=
    harmonicAntichainTwoSourceBinInterference_one_two chirality
  change (2 * (harmonicAntichainTwoSourceBinDecoherence chirality 1 2).re = 0) at hInterference
  linarith

/-- Threshold `charge = 0` versus `charge > 0` is not decoherent. -/
theorem harmonicAntichainTwo_firstChargeThreshold_not_decoherent
    (chirality : Fin 2) :
    growthEventDecoherence
        (harmonicAntichainTwoSourceBinDecoherence chirality)
        lowChargeCell₀ highChargeCell₀ ≠ 0 := by
  intro hZero
  have hReal := congrArg Complex.re hZero
  simp [lowChargeCell₀, highChargeCell₀, growthEventDecoherence] at hReal
  rw [harmonicAntichainTwo_decoherence_zero_one_re,
    harmonicAntichainTwoSourceBinDecoherence_zero_two] at hReal
  norm_num at hReal

/-- Threshold below the fully linked bin is likewise not decoherent. -/
theorem harmonicAntichainTwo_secondChargeThreshold_not_decoherent
    (chirality : Fin 2) :
    growthEventDecoherence
        (harmonicAntichainTwoSourceBinDecoherence chirality)
        lowChargeCell₁ highChargeCell₁ ≠ 0 := by
  intro hZero
  have hReal := congrArg Complex.re hZero
  simp [lowChargeCell₁, highChargeCell₁, growthEventDecoherence] at hReal
  rw [harmonicAntichainTwo_decoherence_one_two_re,
    harmonicAntichainTwoSourceBinDecoherence_zero_two] at hReal
  norm_num at hReal

/-! ## 4. Projective transport preserves the obstruction -/

/-- If either local charge-threshold pair is realized by two cylinder events,
then exhaustive projective continuation preserves its nonzero cross entry at
every later depth. -/
theorem realizedChargeThreshold_not_decoherent_allRefinements
    (chirality : Fin 2) {depth : ℕ}
    (localLow localHigh : Finset (Fin 3))
    (hLocalNonzero : growthEventDecoherence
      (harmonicAntichainTwoSourceBinDecoherence chirality)
      localLow localHigh ≠ 0)
    (cylinderLow cylinderHigh :
      Finset (RankedGrowthPath CausalSetGrowthBranch depth))
    (hRealizes : growthEventDecoherence
        (finiteRankedDepthDecoherence
          (harmonicCriticalCausalSetGrowthLaw chirality) depth)
        cylinderLow cylinderHigh =
      growthEventDecoherence
        (harmonicAntichainTwoSourceBinDecoherence chirality)
        localLow localHigh)
    (steps : ℕ) :
    growthEventDecoherence
        (finiteRankedDepthDecoherence
          (harmonicCriticalCausalSetGrowthLaw chirality) (depth + steps))
        (refineRankedGrowthEventBy cylinderLow steps)
        (refineRankedGrowthEventBy cylinderHigh steps) ≠ 0 := by
  rw [finiteRankedDepthDecoherence_projective_by, hRealizes]
  exact hLocalNonzero

/-- Smallest-rank structural verdict: all three charge values are distinct,
the finest value partition fails, both nontrivial threshold cuts fail, and any
cylinder realization carries the failure through all refinements. -/
theorem rankTwoToThree_chargePartition_verdict :
    Function.Injective antichainTwoSourceBinCharge
      ∧ (∀ chirality : Fin 2,
        ¬IsExactlyDecoherentAcrossValues antichainTwoSourceBinCharge
          (harmonicAntichainTwoSourceBinDecoherence chirality))
      ∧ (∀ chirality : Fin 2,
        growthEventDecoherence
          (harmonicAntichainTwoSourceBinDecoherence chirality)
          lowChargeCell₀ highChargeCell₀ ≠ 0)
      ∧ (∀ chirality : Fin 2,
        growthEventDecoherence
          (harmonicAntichainTwoSourceBinDecoherence chirality)
          lowChargeCell₁ highChargeCell₁ ≠ 0) := by
  exact ⟨antichainTwoSourceBinCharge_injective,
    harmonicAntichainTwo_chargeValuePartition_not_decoherent,
    harmonicAntichainTwo_firstChargeThreshold_not_decoherent,
    harmonicAntichainTwo_secondChargeThreshold_not_decoherent⟩

#print axioms antichainTwoSourceBinCharge_injective
#print axioms harmonicAntichainTwo_chargeValuePartition_not_decoherent
#print axioms harmonicAntichainTwo_firstChargeThreshold_not_decoherent
#print axioms harmonicAntichainTwo_secondChargeThreshold_not_decoherent
#print axioms realizedChargeThreshold_not_decoherent_allRefinements
#print axioms rankTwoToThree_chargePartition_verdict

end

end UnifiedTheory.Audit.KFCausalSetChiralityChargePartitionNoGo
