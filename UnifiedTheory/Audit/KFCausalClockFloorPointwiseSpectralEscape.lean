/- A single sequence of actual physical times exhibits the negative
spectral escape forced by a positive residual. No momentum moment is used.
The conclusion is subsequential, not a full-time spectral limit. -/
import UnifiedTheory.Audit.KFCausalClockFloorActualSpectralEscape
import UnifiedTheory.Audit.KFCausalClockFloorSpectralThresholds
import UnifiedTheory.Audit.KFCausalSmallAverageSelection

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPointwiseSpectralEscape
noncomputable section
open Filter MeasureTheory
open scoped Topology
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding)
open KFCausalClockFloorFastTimeEnergy (physicalTime physicalTime_tendsto)
open KFCausalClockFloorActualObservationAverages (actualAverage)
open KFCausalClockFloorLocalizedSpectrum (orbitObservation)
open KFCausalClockFloorLocalizedSpectralSplit (lowerOrbit orbit_split)
open KFCausalClockFloorWeightedClockControl (weighted)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "E" => KFCausalClockFloorAveragedEvolution.evolution ε hε h hne hb m g k
local notation "P" => KFCausalClockFloorMovingFreeze.actual ε hε h hne hb m g k
local notation "rho" => KFCausalClockFloorResidualDefect.residual ε hε h hne hb m g k
local notation "B" => orbitObservation ε hε h hne
local notation "N" => lowerOrbit ε hε h hne
local notation "AA" => actualAverage ε hε h hne hb m g k

theorem arbitrarily_late_small (hk : 0 < k) (a : ℝ) (ha : 0 < a) (v : V)
    (R T δ : ℝ) (hδ : 0 < δ) :
    ∃ t : ℝ, T ≤ t ∧ ‖B R (E (physicalTime a) t (J v))‖^2 < δ := by
  obtain ⟨U,L,hp⟩ := KFCausalClockFloorSelectedSpectrum.exists_windows
    ε hε h hne hb m g k hk a ha v
  have havg := KFCausalClockFloorActualSpectralEscape.sequence_upper_limit
    ε hε h hne hb m g k hk a R v U L hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.2.2.1
  obtain ⟨n,hn,hT⟩ := ((havg.eventually (gt_mem_nhds hδ)).and
    ((physicalTime_tendsto.comp hp.2.1).eventually (eventually_ge_atTop T))).exists
  have hc := (((B R).continuous.comp_continuousOn
    (KFCausalClockFloorActualObservationAverages.actual_continuousOn
      ε hε h hne hb m g k a (U n) (L n) (hp.1 n).1 (hp.1 n).2.le (J v))).norm).pow 2
  obtain ⟨r,hr,hsmall⟩ := KFCausalSmallAverageSelection.exists_lt
    (fun r => ‖B R (P a (U n) (r*L n) (J v))‖^2) hc δ hn
  refine ⟨physicalTime (U n+r*L n),?_,hsmall⟩
  apply hT.trans
  apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) ≤ 2)
  exact Real.log_le_log (hp.1 n).1 (le_add_of_nonneg_right (mul_nonneg hr.1 (hp.1 n).2.le))

theorem exists_upper_sequence (hk : 0 < k) (a : ℝ) (ha : 0 < a) (v : V) :
    ∃ τ : ℕ → ℝ, Tendsto τ atTop atTop ∧ (∀ n, physicalTime a ≤ τ n) ∧
      (∀ n : ℕ, ‖B (-(n:ℝ)) (E (physicalTime a) (τ n) (J v))‖^2 < 1/((n:ℝ)+1)) ∧
      ∀ R : ℝ, Tendsto (fun n => ‖B R (E (physicalTime a) (τ n) (J v))‖^2) atTop (𝓝 0) := by
  have hex (n : ℕ) := arbitrarily_late_small ε hε h hne hb m g k hk a ha v
    (-(n:ℝ)) (max (physicalTime a) (n:ℝ)) (1/((n:ℝ)+1)) (by positivity)
  choose τ hτ hsmall using hex
  refine ⟨τ,tendsto_atTop_mono (fun n => (le_max_right _ _).trans (hτ n))
    tendsto_natCast_atTop_atTop,fun n => (le_max_left _ _).trans (hτ n),hsmall,?_⟩
  intro R
  apply squeeze_zero' (Eventually.of_forall (fun n => sq_nonneg _)) _
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_ge_atTop (-R))] with n hn
  exact (KFCausalClockFloorSpectralThresholds.orbit_antitone ε hε h hne (-(n:ℝ)) R
    (by linarith) _).trans (hsmall n).le

theorem exists_pointwise_escape (hk : 0 < k) (a : ℝ) (ha : 0 < a) (v : V)
    (hp : 0 < rho (physicalTime a) (J v)) :
    ∃ τ : ℕ → ℝ, Tendsto τ atTop atTop ∧ (∀ n, physicalTime a ≤ τ n) ∧
      (∀ n : ℕ, ‖B (-(n:ℝ)) (E (physicalTime a) (τ n) (J v))‖^2 < 1/((n:ℝ)+1)) ∧
      (∀ R : ℝ, Tendsto (fun n => ‖B R (E (physicalTime a) (τ n) (J v))‖^2) atTop (𝓝 0)) ∧
      ∃ c : ℝ, 0 < c ∧
        (∀ n, 2*c ≤ ‖weighted ε hε (E (physicalTime a) (τ n) (J v))‖^2) ∧
        (∀ᶠ n : ℕ in atTop, c ≤ ‖N (-(n:ℝ)) (E (physicalTime a) (τ n) (J v))‖^2) ∧
        ∀ R : ℝ, ∀ᶠ n in atTop, c ≤ ‖N R (E (physicalTime a) (τ n) (J v))‖^2 := by
  have hweight := KFCausalClockFloorPersistentWeightedClock.persistent_weight
    ε hε h hne hb m g k (physicalTime a) (J v) hp
  let η : ℝ := hweight.choose
  have hη : 0 < η := hweight.choose_spec.1
  apply Exists.imp _ (exists_upper_sequence ε hε h hne hb m g k hk a ha v)
  intro τ ht
  have hw (n : ℕ) : η^2 ≤ ‖weighted ε hε (E (physicalTime a) (τ n) (J v))‖^2 :=
    pow_le_pow_left₀ hη.le (hweight.choose_spec.2 (τ n) (ht.2.1 n)) 2
  refine ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2,η^2/2,by positivity,?_,?_,?_⟩
  · intro n
    linarith only [hw n]
  · filter_upwards [(tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds (show 0 < η^2/2 by positivity))] with n hn
    have hs := orbit_split ε hε h hne (-(n:ℝ)) (E (physicalTime a) (τ n) (J v))
    have hu := ht.2.2.1 n
    linarith only [hs,hu,hn,hw n]
  · intro R
    filter_upwards [(ht.2.2.2 R).eventually (gt_mem_nhds (show 0 < η^2/2 by positivity))] with n hn
    have hs := orbit_split ε hε h hne R (E (physicalTime a) (τ n) (J v))
    linarith only [hs,hn,hw n]

theorem recovery_or_pointwise_escape (hk : 0 < k) (a : ℝ) (ha : 0 < a) (v : V) :
    Tendsto (fun t => ‖KFCausalClockFloorDefectOperator.defectOperator ε hε
      (E (physicalTime a) t (J v))‖) atTop (𝓝 0) ∨
    ∃ (τ : ℕ → ℝ) (c : ℝ), 0 < c ∧ Tendsto τ atTop atTop ∧
      (∀ R : ℝ, Tendsto (fun n => ‖B R (E (physicalTime a) (τ n) (J v))‖^2) atTop (𝓝 0)) ∧
      ∀ R : ℝ, ∀ᶠ n in atTop, c ≤ ‖N R (E (physicalTime a) (τ n) (J v))‖^2 := by
  by_cases hr : rho (physicalTime a) (J v)=0
  · exact Or.inl ((KFCausalClockFloorResidualDefect.recovery_iff ε hε h hne hb m g k
      (physicalTime a) (J v)).mpr hr)
  · right
    apply Exists.imp _ (exists_pointwise_escape ε hε h hne hb m g k hk a ha v
      (lt_of_le_of_ne (KFCausalClockFloorResidualDefect.residual_bounds ε hε h hne hb m g k
        (physicalTime a) (physicalTime a) (J v)).1 (Ne.symm hr)))
    intro τ ht
    apply Exists.imp _ ht.2.2.2.2
    intro c hc
    exact ⟨hc.1,ht.1,ht.2.2.2.1,hc.2.2.2⟩

#print axioms arbitrarily_late_small
#print axioms exists_upper_sequence
#print axioms exists_pointwise_escape
#print axioms recovery_or_pointwise_escape
end
end UnifiedTheory.Audit.KFCausalClockFloorPointwiseSpectralEscape
