/- The radial form expectation and the bare canonical position
characteristic are identified on the actual evolved boosted states.
The proved charged-tail estimate supplies uniform cutoff approximation. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialEvolution
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialEhrenfest
import UnifiedTheory.Audit.KFCausalNeutralPositionCutoffCharacteristic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralPositionRadialCharacteristic
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState evolvedState_norm)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState (referenceState referenceState_embedding)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution (evolution)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff (action)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialEvolution (error expectation_error_bound)
open UnifiedTheory.Audit.KFCausalNeutralPositionCharge (frequency)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k s : ℝ) (p : Configuration)
local notation "ψ" => evolvedState ε a h hε ha hne hh m g k s p

def bare (v t : ℝ) : ℂ := inner ℂ (ψ t) (KFCausalNeutralPositionCharge.action v (ψ t))

def radial (δ : ℝ) (hδ : 0 < δ) (v t : ℝ) : ℂ := inner ℂ (ψ t) (action h δ v hδ (ψ t))

theorem bare_canonical (v t : ℝ) :
    bare ε a h hε ha hne hh m g k s p v t =
      KFCausalCanonicalWeylAlgebra.characteristic volume h (ψ t) (frequency v,(0:Configuration)) := by
  unfold KFCausalCanonicalWeylAlgebra.characteristic
  rw [KFCausalNeutralPositionCutoffCharacteristic.operator_phase]
  rfl

theorem bare_norm (v t : ℝ) : ‖bare ε a h hε ha hne hh m g k s p v t‖ ≤ 1 := by
  exact (norm_inner_le_norm _ _).trans_eq (by rw [(KFCausalNeutralPositionCharge.action v).norm_map,
    evolvedState_norm,one_mul])

theorem radial_reference (δ : ℝ) (hδ : 0 < δ) (v t : ℝ) :
    radial ε a h hε ha hne hh m g k s p δ hδ v t =
      KFCausalNeutralPositionRadialEhrenfest.characteristic ε hε h δ v hδ hh hne m g k s t
        (referenceState ε a h hε ha hne hh m g k s p) := by
  exact (congrArg (fun f : Hilbert => inner ℂ f (action h δ v hδ f))
    (congrArg (evolution ε hε h hne hh m g k s t)
      (referenceState_embedding ε a h hε ha hne hh m g k s p))).symm

theorem approximation_error (δ : ℝ) (hδ : 0 < δ) (v t : ℝ) :
    ‖radial ε a h hε ha hne hh m g k s p δ hδ v t-bare ε a h hε ha hne hh m g k s p v t‖ ≤
      ‖error ε a h hε ha hne hh m g k s p δ hδ v t‖ :=
  expectation_error_bound ε a h hε ha hne hh m g k s p δ hδ v t

omit h hne hh in
theorem uniform_approximation (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
    (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T η : ℝ) (hη : 0 < η) :
    ∃ D : ℝ, 0 < D ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ δ : ℝ, ∀ hδ : 0 < δ, δ < D →
      ∀ v t : ℝ, |t-s| ≤ T →
        ‖radial ε a (h n) hε ha (hne n) (hh n) m g k s p δ hδ v t-
          bare ε a (h n) hε ha (hne n) (hh n) m g k s p v t‖ < η := by
  obtain ⟨D,hD,N,hN⟩ := KFCausalNeutralPositionRadialEvolution.uniform_window
    ε a hε ha m g k s p hm hg hk h hne hh hz T η hη
  exact ⟨D,hD,N,fun n hn δ hδ hd v t ht =>
    (approximation_error ε a (h n) hε ha (hne n) (hh n) m g k s p δ hδ v t).trans_lt
      (hN n hn δ hδ hd v t ht)⟩

#print axioms bare_canonical
#print axioms bare_norm
#print axioms radial_reference
#print axioms approximation_error
#print axioms uniform_approximation

end
end UnifiedTheory.Audit.KFCausalNeutralPositionRadialCharacteristic
