/-
  Audit/KFCausalCSpecHarmonicBornIncidenceEquivariance.lean

  A TYPED INCIDENCE-ACTION / CAUSAL-BORN READOUT SQUARE

  Gate-4 recovery produces permutations of the three intrinsic CSpec
  directions, while the finite Gate-5 state has sixteen computational
  outcomes.  This module constructs a canonical, nontrivial action of those
  direction permutations on the sixteen outcomes: identify one generation
  with four qubit coordinates, permute the first three directional qubits,
  and leave the fourth qubit fixed.

  An `IncidenceEquivariantHarmonicReadout` then states the exact missing
  compatibility data.  At each site it supplies a permutation of the finite
  causal children, proves that the readout square commutes, and proves that
  the conditional harmonic stage PMF is preserved.  From those data we prove
  invariance of the pushed-forward PMF, the causal Born weights, the
  positive-square-root substrate amplitudes, and the localized
  computational-effect expectations.

  The compatibility record is intentionally not manufactured from recovery:
  the present Gate-4 stage has no map from an incidence edge to causal-growth
  children.  Thus this file closes the finite typed implication while keeping
  existence of a physically correct equivariant coarse graining explicit.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecHarmonicBornPMFProvenance
import UnifiedTheory.LayerC.SMTensorDecomposition

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecHarmonicBornIncidenceEquivariance

noncomputable section

open scoped BigOperators ENNReal
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalBornShellGeneralLaw
open UnifiedTheory.Audit.KFCausalBornNormalizationTransfer
open UnifiedTheory.Audit.KFCausalBornObservedWeight
open UnifiedTheory.Audit.KFCausalSetHarmonicBornTrajectoryMeasure
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornLocalNet
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornPMFProvenance
open UnifiedTheory.LayerC.SMHilbertInstantiation
open UnifiedTheory.LayerC.SMTensorDecomposition

universe u

/-! ## 1. The canonical direction action on sixteen outcomes -/

/-- One generation as three directional qubits and one spectator qubit.
The cardinal identity is `16 = 8 * 2 = (2 ^ 3) * 2`. -/
def singleGenerationDirectionalQubitEquiv :
    Fin singleGenDim ≃ ((Direction → Fin 2) × Fin 2) :=
  (finCongr singleGenDim_eq_qubit_pow_4).trans <|
    (finCongr (by decide : (2 ^ 4 : ℕ) = 8 * 2)).trans <|
      (finProdFinEquiv (m := 8) (n := 2)).symm.trans <|
        Equiv.prodCongr
          (finFunctionFinEquiv (m := 2) (n := 3)).symm
          (Equiv.refl (Fin 2))

/-- A direction permutation acts by reindexing the first three qubits and
fixes the fourth qubit. -/
def directionalQubitAction
    (permutation : Equiv.Perm Direction) :
    Equiv.Perm ((Direction → Fin 2) × Fin 2) :=
  Equiv.prodCongr
    (Equiv.arrowCongr permutation (Equiv.refl (Fin 2)))
    (Equiv.refl (Fin 2))

/-- Conjugate the directional-qubit action through the canonical sixteen-state
index equivalence. -/
def singleGenerationDirectionAction
    (permutation : Equiv.Perm Direction) :
    Equiv.Perm (Fin singleGenDim) :=
  singleGenerationDirectionalQubitEquiv.trans <|
    (directionalQubitAction permutation).trans
      singleGenerationDirectionalQubitEquiv.symm

@[simp]
theorem singleGenerationDirectionAction_coordinates
    (permutation : Equiv.Perm Direction)
    (outcome : Fin singleGenDim) :
    singleGenerationDirectionalQubitEquiv
        (singleGenerationDirectionAction permutation outcome) =
      directionalQubitAction permutation
        (singleGenerationDirectionalQubitEquiv outcome) := by
  simp [singleGenerationDirectionAction]

@[simp]
theorem directionalQubitAction_apply
    (permutation : Equiv.Perm Direction)
    (qubits : Direction → Fin 2) (spectator : Fin 2) :
    directionalQubitAction permutation (qubits, spectator) =
      (qubits ∘ permutation.symm, spectator) := by
  rfl

/-! ## 2. Exact compatibility data -/

/-- The finite readout square required to make recovered incidence transport
act on the causal Born state.  `branchAction` is data on actual finite causal
children; its two laws say that observation intertwines the action and that
the selected conditional stage PMF is invariant under it. -/
structure IncidenceEquivariantHarmonicReadout
    {site : Type u}
    (chirality : Fin 2)
    (transport : site → Equiv.Perm Direction)
    (R : HarmonicSingleGenerationReadout site) where
  branchAction :
    (i : site) → Equiv.Perm (CausalSetGrowthBranch (R.rankAt i))
  observe_commutes :
    ∀ (i : site) (child : CausalSetGrowthBranch (R.rankAt i)),
      R.observe (R.rankAt i) (branchAction i child) =
        singleGenerationDirectionAction (transport i)
          (R.observe (R.rankAt i) child)
  stagePMF_preserved :
    ∀ (i : site) (child : CausalSetGrowthBranch (R.rankAt i)),
      causalBornStagePMF (canonicalHarmonicBornLaw chirality)
          (R.rankAt i) (R.parentSchedule (R.rankAt i))
          (branchAction i child) =
        causalBornStagePMF (canonicalHarmonicBornLaw chirality)
          (R.rankAt i) (R.parentSchedule (R.rankAt i)) child

namespace IncidenceEquivariantHarmonicReadout

variable {site : Type u}
variable {chirality : Fin 2}
variable {transport : site → Equiv.Perm Direction}
variable {R : HarmonicSingleGenerationReadout site}

/-! ## 3. Pushforward and Born invariance -/

/-- The commuting square and branch-PMF preservation force invariance of the
readout pushforward PMF under the induced sixteen-outcome action. -/
theorem mapped_stagePMF_invariant
    (E : IncidenceEquivariantHarmonicReadout chirality transport R)
    (i : site) (outcome : Fin singleGenDim) :
    (causalBornStagePMF (canonicalHarmonicBornLaw chirality)
        (R.rankAt i) (R.parentSchedule (R.rankAt i))).map
        (R.observe (R.rankAt i))
        (singleGenerationDirectionAction (transport i) outcome) =
      (causalBornStagePMF (canonicalHarmonicBornLaw chirality)
        (R.rankAt i) (R.parentSchedule (R.rankAt i))).map
        (R.observe (R.rankAt i)) outcome := by
  classical
  simp only [PMF.map_apply, tsum_fintype]
  let p := causalBornStagePMF (canonicalHarmonicBornLaw chirality)
    (R.rankAt i) (R.parentSchedule (R.rankAt i))
  let action := E.branchAction i
  let outcomeAction := singleGenerationDirectionAction (transport i)
  let summand := fun (target : Fin singleGenDim)
      (child : CausalSetGrowthBranch (R.rankAt i)) =>
    @ite ENNReal (target = R.observe (R.rankAt i) child)
      (Classical.propDecidable _) (p child) 0
  change
    (∑ child, summand (outcomeAction outcome) child) =
      ∑ child, summand outcome child
  calc
    (∑ child, summand (outcomeAction outcome) child) =
      (∑ child, summand (outcomeAction outcome) (action child)) := by
            exact Fintype.sum_equiv action.symm
              (fun child => summand (outcomeAction outcome) child)
              (fun child => summand (outcomeAction outcome) (action child))
              (fun child => by simp)
    _ = (∑ child,
        @ite ENNReal
          (outcomeAction outcome =
            outcomeAction (R.observe (R.rankAt i) child))
          (Classical.propDecidable _) (p child) 0) := by
            apply Finset.sum_congr rfl
            intro child _
            unfold summand
            rw [E.observe_commutes, E.stagePMF_preserved]
    _ = ∑ child, summand outcome child := by
            apply Finset.sum_congr rfl
            intro child _
            unfold summand
            rw [outcomeAction.injective.eq_iff]

/-- Consequently, the real causal Born weights used to form the local state
are invariant under recovered incidence transport. -/
theorem harmonicReadoutWeight_invariant
    (E : IncidenceEquivariantHarmonicReadout chirality transport R)
    (i : site) (outcome : Fin singleGenDim) :
    harmonicReadoutWeight chirality R i
        (singleGenerationDirectionAction (transport i) outcome) =
      harmonicReadoutWeight chirality R i outcome := by
  apply (ENNReal.ofReal_eq_ofReal_iff
    (harmonicReadoutWeight_nonneg chirality R i
      (singleGenerationDirectionAction (transport i) outcome))
    (harmonicReadoutWeight_nonneg chirality R i outcome)).mp
  rw [← harmonicCausalBornStagePMF_map_readout_apply chirality R i]
  rw [← harmonicCausalBornStagePMF_map_readout_apply chirality R i]
  exact E.mapped_stagePMF_invariant i outcome

/-- The positive-square-root amplitudes inherit the same invariance. -/
theorem harmonicReadoutSubstrateState_amp_invariant
    (E : IncidenceEquivariantHarmonicReadout chirality transport R)
    (i : site) (outcome : Fin singleGenDim) :
    (harmonicReadoutSubstrateState chirality R i).amp
        (singleGenerationDirectionAction (transport i) outcome) =
      (harmonicReadoutSubstrateState chirality R i).amp outcome := by
  simp only [harmonicReadoutSubstrateState]
  rw [E.harmonicReadoutWeight_invariant]

/-- Equivariance reaches the operational interface: localized computational
effects in the causal Born state have invariant expectations. -/
theorem local_computational_expectation_invariant
    [Fintype site] [Nonempty site]
    (E : IncidenceEquivariantHarmonicReadout chirality transport R)
    (i : site) (outcome : Fin singleGenDim) :
    (harmonicLocalStateFunctional chirality R i
        (computationalEffectAt i
          (singleGenerationDirectionAction (transport i) outcome))).re =
      (harmonicLocalStateFunctional chirality R i
        (computationalEffectAt i outcome)).re := by
  rw [harmonicLocalStateFunctional_computationalEffect]
  rw [harmonicLocalStateFunctional_computationalEffect]
  exact E.harmonicReadoutWeight_invariant i outcome

/-! ## 4. Axiom audit -/

#print axioms singleGenerationDirectionAction_coordinates
#print axioms mapped_stagePMF_invariant
#print axioms harmonicReadoutWeight_invariant
#print axioms harmonicReadoutSubstrateState_amp_invariant
#print axioms local_computational_expectation_invariant

end IncidenceEquivariantHarmonicReadout

end

end UnifiedTheory.Audit.KFCausalCSpecHarmonicBornIncidenceEquivariance
