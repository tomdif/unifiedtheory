/- The actual transverse translations commute with pure-clock transport.
Consequently all maximal physical transverse momentum graphs are invariant,
and their pure-clock momentum compositions commute on the actual domains. -/
import UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum
import UnifiedTheory.Audit.KFCausalClockFloorKineticDefect
import UnifiedTheory.Audit.KFCausalClosedOperatorUnitaryCommutation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockTransverse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum
open UnifiedTheory.Audit.KFCausalClockFloorPureClockTransport
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum
open UnifiedTheory.Audit.KFCausalClockFloorKineticDefect (transverse_graph_iff)
open UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback
open UnifiedTheory.Audit.KFCausalDirectionalTranslationMomentum (spectralMomentum_graph_derivative)
open UnifiedTheory.Audit.KFCausalClosedOperatorUnitaryCommutation

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

def shift (v : Transverse) : Configuration ≃ᵐ Configuration :=
  (Homeomorph.addRight (0,v)).toMeasurableEquiv

theorem shift_apply (v : Transverse) (x : Configuration) : shift v x = (x.1,x.2+v) := by
  change (x.1+0,x.2+v) = _
  rw [add_zero]

theorem shift_preserves (v : Transverse) : MeasurePreserving (shift v) :=
  measurePreserving_add_right volume (0,v)

def translation (v : Transverse) : Hilbert ≃ₗᵢ[ℂ] Hilbert :=
  unitaryPullback (shift v) (shift_preserves v)

theorem translation_coe (v : Transverse) (f : Hilbert) :
    translation v f =ᵐ[volume] fun x => f (x.1,x.2+v) := by
  filter_upwards [unitaryPullback_coe (shift v) (shift_preserves v) f] with x hx
  simpa only [Function.comp_apply,shift_apply] using hx

theorem euclidean_translation (v : Transverse) (t : ℝ) (f : Hilbert) :
    euclideanPullback (translation (t • v) f) =
      KFCausalFourierTranslation.translation (t • transverseVector v) (euclideanPullback f) := by
  apply Lp.ext
  filter_upwards [euclideanPullback_coe (translation (t • v) f),
    split_preserves_volume.quasiMeasurePreserving.ae (translation_coe (t • v) f),
    KFCausalFourierTranslation.translation_coe (t • transverseVector v) (euclideanPullback f),
    (KFCausalFourierTranslation.shift_preserves_volume (t • transverseVector v)).quasiMeasurePreserving.ae
      (euclideanPullback_coe f)] with x he ht hs hf
  dsimp only [Function.comp_apply] at he hf
  change euclideanPullback f (x+t • transverseVector v) = f (split (x+t • transverseVector v)) at hf
  rw [he,ht,hs,hf,split_transverse_add]

variable (ε : ℝ) (hε : 0 < ε)

theorem transport_translation (v : Transverse) (t : ℝ) (f : Hilbert) :
    transport ε hε t (translation v f) = translation v (transport ε hε t f) := by
  apply Lp.ext
  filter_upwards [transport_coe ε hε t (translation v f),translation_coe v (transport ε hε t f),
    (flow_quasiMeasurePreserving ε hε t).ae (translation_coe v f),
    (shift_preserves v).quasiMeasurePreserving.ae (transport_coe ε hε t f)] with x hw ht hf hg
  simp only [shift_apply] at hg
  rw [hw,ht,hg]
  dsimp only [transportFunction]
  rw [hf]
  rfl

omit ε hε in
theorem transverse_graph_derivative (h : ℝ) (hh : h ≠ 0) (v : Transverse) (f g : Hilbert) :
    (f,g) ∈ (transverseMomentum h v).graph ↔
      HasDerivAt (fun t : ℝ => translation (t • v) f) ((Complex.I/(h:ℂ)) • g) 0 := by
  rw [transverse_graph_iff,spectralMomentum_graph_derivative h hh]
  constructor
  · intro hd
    have he := ((euclideanPullback.symm : FrequencyHilbert →L[ℂ] Hilbert).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
    change HasDerivAt (fun t => euclideanPullback.symm
      (KFCausalFourierTranslation.translation (t • transverseVector v) (euclideanPullback f)))
      (euclideanPullback.symm ((Complex.I/(h:ℂ)) • euclideanPullback g)) 0 at he
    simpa only [Function.comp_def,← euclidean_translation,map_smul,LinearIsometryEquiv.symm_apply_apply] using he
  · intro hd
    have he := ((euclideanPullback : Hilbert →L[ℂ] FrequencyHilbert).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
    change HasDerivAt (fun t => euclideanPullback (translation (t • v) f))
      (euclideanPullback ((Complex.I/(h:ℂ)) • g)) 0 at he
    simpa only [Function.comp_def,euclidean_translation,map_smul] using he

theorem transverse_transport (h : ℝ) (hh : h ≠ 0) (v : Transverse) (t : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (transverseMomentum h v).graph) :
    (transport ε hε t f,transport ε hε t g) ∈ (transverseMomentum h v).graph := by
  apply (transverse_graph_derivative h hh v _ _).mpr
  have hd := ((transport ε hε t : Hilbert →L[ℂ] Hilbert).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    ((transverse_graph_derivative h hh v f g).mp hfg)
  change HasDerivAt (fun u => transport ε hε t (translation (u • v) f))
    (transport ε hε t ((Complex.I/(h:ℂ)) • g)) 0 at hd
  simpa only [Function.comp_def,transport_translation,map_smul] using hd

theorem transverse_interchange (h : ℝ) (hh : h ≠ 0) (v : Transverse) (f g b k : Hilbert)
    (hg : (f,g) ∈ (transverseMomentum h v).graph) (hb : (f,b) ∈ (pureMomentum ε hε h).graph) :
    (b,k) ∈ (transverseMomentum h v).graph ↔ (g,k) ∈ (pureMomentum ε hε h).graph :=
  graph_interchange (pureGroup ε hε) (transverseMomentum h v) (transverseMomentum_closed h v)
    (transverse_transport ε hε h hh v) h hh f g b k hg hb

theorem transverse_core (h : ℝ) (hh : h ≠ 0) (v : Transverse) :
    (regularGraph (pureGroup ε hε) (transverseMomentum h v) h).topologicalClosure = (transverseMomentum h v).graph :=
  regular_graph_core (pureGroup ε hε) (transverseMomentum h v) (transverseMomentum_closed h v)
    (transverse_transport ε hε h hh v) h

#print axioms shift_apply
#print axioms shift_preserves
#print axioms translation_coe
#print axioms euclidean_translation
#print axioms transport_translation
#print axioms transverse_graph_derivative
#print axioms transverse_transport
#print axioms transverse_interchange
#print axioms transverse_core
end
end UnifiedTheory.Audit.KFCausalClockFloorPureClockTransverse
