/-
  Audit/KFTOEGate1OrderCouplingSelection.lean

  A CONCRETE ORDER-AMPLITUDE INPUT FOR GATE 1

  Gate 1 deliberately accepts its unresolved coupling-selection input as a
  proposition.  This module supplies a concrete proposition: on the full
  precursor of the two-antichain, the effective-pair raw amplitude agrees
  with the canonical effective-pair amplitude in both chiral sectors.

  The realized-signature identifiability theorem proves that this amplitude
  condition is equivalent to equality with the canonical effective coupling.
  The existing Gate 1 complex bridge can therefore be instantiated with a
  typed physical statement rather than an arbitrary placeholder.  The module
  does not claim to derive the amplitude condition from causal order alone.
-/

import UnifiedTheory.Audit.KFCausalSetOrderCouplingIdentifiability
import UnifiedTheory.Audit.KFTOESevenGateAttack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFTOEGate1OrderCouplingSelection

noncomputable section

open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
open UnifiedTheory.Audit.KFCausalSetOrderCouplingIdentifiability
open UnifiedTheory.Audit.KFTOESevenGateAttack

/-! ## 1. A concrete two-antichain selection proposition -/

/-- The raw effective-pair amplitude on the full precursor of the concrete
two-antichain. -/
def fullTwoAntichainEffectivePairAmplitude
    (g : ℝ) (chirality : Fin 2) : ℂ :=
  (rideoutSorkinSignatureAmplitude
    (effectivePairChiralSignatureWeight g chirality)).amplitude
      (cardinalCausalAntichain 2)
      (fullCausalPastSet (cardinalCausalAntichain 2))

@[simp]
theorem fullTwoAntichainEffectivePairAmplitude_eq
    (g : ℝ) (chirality : Fin 2) :
    fullTwoAntichainEffectivePairAmplitude g chirality = -(g : ℂ) := by
  exact effectivePairChiral_fullTwoAntichain_amplitude g chirality

/-- Concrete Gate 1 selection input: both chiral sectors assign the canonical
effective-pair amplitude to the full precursor of the two-antichain. -/
def CanonicalTwoAntichainAmplitudeSelection (g : ℝ) : Prop :=
  ∀ chirality : Fin 2,
    fullTwoAntichainEffectivePairAmplitude g chirality =
      fullTwoAntichainEffectivePairAmplitude
        (effectivePairCoupling canonicalPairCoupling) chirality

/-- The concrete order-amplitude input contains exactly the claimed coupling
selection: it holds precisely for the canonical effective coupling. -/
theorem canonicalTwoAntichainAmplitudeSelection_iff
    (g : ℝ) :
    CanonicalTwoAntichainAmplitudeSelection g ↔
      g = effectivePairCoupling canonicalPairCoupling := by
  constructor
  · intro hSelection
    have hAmplitude := hSelection (0 : Fin 2)
    exact
      (fullTwoAntichainAmplitude_selects_canonicalEffectivePairCoupling
        g (0 : Fin 2)).mp hAmplitude
  · rintro rfl chirality
    rfl

/-! ## 2. Instantiation of the existing Gate 1 bridge -/

/-- Once the concrete two-antichain amplitude condition is supplied, the
existing complex signed-fiber certificate closes the correspondingly typed
Gate 1 physical-selection bridge. -/
theorem gate1_complexPhysicalSelectionBridge_closed_of_twoAntichainSelection
    {g : ℝ} (hSelection : CanonicalTwoAntichainAmplitudeSelection g) :
    Gate1ComplexPhysicalSelectionBridgeClosed
      (CanonicalTwoAntichainAmplitudeSelection g) := by
  exact gate1_complexPhysicalSelectionBridge_closed_of_orderCoupling hSelection

/-- Equivalent coupling-equality form of the concrete Gate 1 bridge hook. -/
theorem gate1_complexPhysicalSelectionBridge_closed_of_effectivePairCoupling_eq
    {g : ℝ} (hCoupling :
      g = effectivePairCoupling canonicalPairCoupling) :
    Gate1ComplexPhysicalSelectionBridgeClosed
      (CanonicalTwoAntichainAmplitudeSelection g) := by
  apply gate1_complexPhysicalSelectionBridge_closed_of_twoAntichainSelection
  exact (canonicalTwoAntichainAmplitudeSelection_iff g).2 hCoupling

/-- Conversely, closure of this concretely instantiated Gate 1 bridge exposes
an actual equality of effective couplings, rather than merely returning an
opaque proposition. -/
theorem effectivePairCoupling_eq_canonical_of_gate1_complexBridge
    {g : ℝ}
    (hGate : Gate1ComplexPhysicalSelectionBridgeClosed
      (CanonicalTwoAntichainAmplitudeSelection g)) :
    g = effectivePairCoupling canonicalPairCoupling := by
  exact (canonicalTwoAntichainAmplitudeSelection_iff g).1
    hGate.couplingSelected

/-- At the already instantiated canonical effective coupling, the concrete
amplitude-selection proposition and hence the Gate 1 bridge are closed.  This
is a consistency specialization, not a derivation of the canonical value for
an otherwise unknown candidate. -/
theorem canonicalEffectivePairCoupling_gate1_complexBridge_closed :
    Gate1ComplexPhysicalSelectionBridgeClosed
      (CanonicalTwoAntichainAmplitudeSelection
        (effectivePairCoupling canonicalPairCoupling)) := by
  apply gate1_complexPhysicalSelectionBridge_closed_of_effectivePairCoupling_eq
  rfl

#print axioms canonicalTwoAntichainAmplitudeSelection_iff
#print axioms gate1_complexPhysicalSelectionBridge_closed_of_twoAntichainSelection
#print axioms effectivePairCoupling_eq_canonical_of_gate1_complexBridge
#print axioms canonicalEffectivePairCoupling_gate1_complexBridge_closed

end

end UnifiedTheory.Audit.KFTOEGate1OrderCouplingSelection
