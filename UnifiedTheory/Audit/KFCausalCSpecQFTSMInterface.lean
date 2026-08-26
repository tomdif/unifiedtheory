/-
  Audit/KFCausalCSpecQFTSMInterface.lean

  Finite recovered-CSpec to Hilbert/Born interface for Gate 5.

  This file packages two previously separate proved layers:

  * a `PhysicalHauptvermutungRecoveredStage`, whose incidence transport is
    already forced to be the canonical CSpec transport; and
  * independently supplied normalized real-amplitude single-generation
    substrate states indexed by the recovered sites, whose rank-one density
    matrices already obey the finite Born rule in Hilbert dimension
    `singleGenDim = 16`.

  The local state field is deliberately an explicit input.  Nothing here
  derives those states from recovery or microscopic causal-growth amplitudes,
  relates them equivariantly to incidence transport, or supplies a continuum
  Hilbert space, local QFT net, spin-statistics theorem, gauge-field dynamics,
  or Standard-Model infrared limit.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
import UnifiedTheory.LayerC.SMBornRuleGeneralN
import UnifiedTheory.LayerC.SMHilbertInstantiation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecQFTSMInterface

universe u

open scoped BigOperators
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecGlobalization
open UnifiedTheory.LayerC.SMBornRuleGeneralN
open UnifiedTheory.LayerC.SMHilbertInstantiation

/-- A recovered finite CSpec stage carrying one normalized real-amplitude
single-generation state at each site.

The state is data, not a proposition or a placeholder.  Its normalization is
part of `SubstrateState`; its physical derivation from the microscopic growth
law remains an explicit later bridge. -/
structure RecoveredCSpecHilbertFiber
    {site : Type u} [Fintype site] [Nonempty site]
    (countWindow curvatureBias spectralLocality : site → ℝ)
    (scale total : ℝ)
    (edge : site → E4)
    (candidate : site → Equiv.Perm Direction) : Type u where
  recovered :
    PhysicalHauptvermutungRecoveredStage
      countWindow curvatureBias spectralLocality scale total edge candidate
  localState : site → SubstrateState singleGenDim

namespace RecoveredCSpecHilbertFiber

variable {site : Type u} [Fintype site] [Nonempty site]
variable {countWindow curvatureBias spectralLocality : site → ℝ}
variable {scale total : ℝ}
variable {edge : site → E4}
variable {candidate : site → Equiv.Perm Direction}

/-- The local state is carried by the framework-selected single-generation
dimension, which is exactly `16`. -/
theorem single_generation_dimension
    : singleGenDim = 16 :=
  singleGenDim_eq_sixteen

/-- Recovery forces the candidate transport at every site to be the canonical
four-state incidence transport. -/
theorem candidate_transport
    (F : RecoveredCSpecHilbertFiber
      countWindow curvatureBias spectralLocality scale total edge candidate)
    (i : site) :
    candidate i = fourState.perm (edge i) :=
  F.recovered.candidate_transport i

/-- At every recovered site and every computational-basis outcome, the
Hilbert-space Born weight of the local rank-one density matrix is exactly the
squared local substrate amplitude. -/
theorem born_weight_eq_amp_sq
    (F : RecoveredCSpecHilbertFiber
      countWindow curvatureBias spectralLocality scale total edge candidate)
    (i : site) (k : Fin singleGenDim) :
    ((substrateToDensityMatrix singleGenDim (F.localState i)).M *
          computationalProjector singleGenDim k).trace.re =
      (F.localState i).amp k ^ 2 :=
  (sm_born_rule_general_n_bridge (F.localState i)).1 k

/-- The computational-basis Born weights of every local recovered-site state
sum exactly to one. -/
theorem born_weights_normalized
    (F : RecoveredCSpecHilbertFiber
      countWindow curvatureBias spectralLocality scale total edge candidate)
    (i : site) :
    ∑ k,
        ((substrateToDensityMatrix singleGenDim (F.localState i)).M *
            computationalProjector singleGenDim k).trace.re = 1 :=
  (sm_born_rule_general_n_bridge (F.localState i)).2

/-- Bundled finite Gate 5 packaging result: one object contains an exactly
recovered CSpec stage and independently supplied normalized local states.  The
conclusion records canonical incidence transport alongside their Hilbert Born
weights; it does not assert that transport acts on those states. -/
theorem transport_and_born
    (F : RecoveredCSpecHilbertFiber
      countWindow curvatureBias spectralLocality scale total edge candidate) :
    (∀ i, candidate i = fourState.perm (edge i)) ∧
      (∀ i k,
        ((substrateToDensityMatrix singleGenDim (F.localState i)).M *
              computationalProjector singleGenDim k).trace.re =
          (F.localState i).amp k ^ 2) ∧
      (∀ i,
        ∑ k,
            ((substrateToDensityMatrix singleGenDim (F.localState i)).M *
                computationalProjector singleGenDim k).trace.re = 1) := by
  exact
    ⟨F.candidate_transport,
      F.born_weight_eq_amp_sq,
      F.born_weights_normalized⟩

#print axioms single_generation_dimension
#print axioms candidate_transport
#print axioms born_weight_eq_amp_sq
#print axioms born_weights_normalized
#print axioms transport_and_born

end RecoveredCSpecHilbertFiber

end UnifiedTheory.Audit.KFCausalCSpecQFTSMInterface
