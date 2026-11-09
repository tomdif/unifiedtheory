/- An exact criterion for clock recovery in the full finite-energy dynamics:
the localized negative coupled spectral tails must be eventually tight.
The criterion is proved; propagation of its tail condition is not assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorPointwiseSpectralEscape

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorNegativeTailCriterion
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding)
open KFCausalClockFloorFastTimeEnergy (physicalTime)
open KFCausalClockFloorWeightedClockControl (weighted)
open KFCausalClockFloorDefectOperator (defectOperator)
open KFCausalClockFloorLocalizedSpectralSplit (lowerOrbit orbit_split)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "E" => KFCausalClockFloorAveragedEvolution.evolution ε hε h hne hb m g k
local notation "D" => defectOperator ε hε
local notation "N" => lowerOrbit ε hε h hne

def EventuallyTight (s : ℝ) (f : Hilbert) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, ∀ᶠ t in atTop, ‖N R (E s t f)‖^2 < δ

theorem recovery_implies_tail_limit (s R : ℝ) (f : Hilbert)
    (hd : Tendsto (fun t => ‖D (E s t f)‖) atTop (𝓝 0)) :
    Tendsto (fun t => ‖N R (E s t f)‖^2) atTop (𝓝 0) := by
  let A : Hilbert →L[ℂ] Hilbert :=
    (KFCausalClockFloorBoundedInverse.inverseL ε hε).comp
      (ContinuousLinearMap.id ℂ Hilbert-D)
  have he (x : Hilbert) : weighted ε hε x=A (D x) := rfl
  have hw : Tendsto (fun t => ‖weighted ε hε (E s t f)‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) (fun t => ?_)
      (by simpa only [mul_zero] using hd.const_mul ‖A‖)
    rw [he]
    exact A.le_opNorm _
  apply squeeze_zero (fun _ => sq_nonneg _) (fun t => ?_)
    (by simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0)] using hw.pow 2)
  have hs := orbit_split ε hε h hne R (E s t f)
  nlinarith only [hs,sq_nonneg
    ‖KFCausalClockFloorLocalizedSpectrum.orbitObservation ε hε h hne R (E s t f)‖]

theorem recovery_of_eventually_tight (hk : 0 < k) (a : ℝ) (ha : 0 < a) (v : V)
    (htight : EventuallyTight ε hε h hne hb m g k (physicalTime a) (J v)) :
    Tendsto (fun t => ‖D (E (physicalTime a) t (J v))‖) atTop (𝓝 0) := by
  by_contra hd
  have he := (KFCausalClockFloorPointwiseSpectralEscape.recovery_or_pointwise_escape
    ε hε h hne hb m g k hk a ha v).resolve_left hd
  let τ : ℕ → ℝ := he.choose
  let c : ℝ := he.choose_spec.choose
  have hc : 0 < c := he.choose_spec.choose_spec.1
  have hτ : Tendsto τ atTop atTop := he.choose_spec.choose_spec.2.1
  obtain ⟨R,hR⟩ := htight (c/2) (by positivity)
  have hnegative := he.choose_spec.choose_spec.2.2.2 R
  obtain ⟨n,hn,hsmall⟩ := (hnegative.and (hτ.eventually hR)).exists
  linarith only [hc,hn,hsmall]

theorem recovery_iff_eventually_tight (hk : 0 < k) (a : ℝ) (ha : 0 < a) (v : V) :
    Tendsto (fun t => ‖D (E (physicalTime a) t (J v))‖) atTop (𝓝 0) ↔
      EventuallyTight ε hε h hne hb m g k (physicalTime a) (J v) := by
  constructor
  · intro hd δ hδ
    exact ⟨0,(recovery_implies_tail_limit ε hε h hne hb m g k (physicalTime a) 0 (J v) hd).eventually
      (gt_mem_nhds hδ)⟩
  · exact recovery_of_eventually_tight ε hε h hne hb m g k hk a ha v

#print axioms recovery_implies_tail_limit
#print axioms recovery_of_eventually_tight
#print axioms recovery_iff_eventually_tight
end
end UnifiedTheory.Audit.KFCausalClockFloorNegativeTailCriterion
