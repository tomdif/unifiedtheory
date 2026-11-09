/- A failure of clock recovery forces nonzero averaged localized mass
below every fixed coupled longitudinal momentum threshold on the same
derived full frozen windows. No failure or recovery branch is asserted. -/
import UnifiedTheory.Audit.KFCausalClockFloorLocalizedSpectralSplit
import UnifiedTheory.Audit.KFCausalClockFloorSelectedWeightedClock

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorSelectedNegativeEscape
noncomputable section
open Filter MeasureTheory
open scoped Topology
open KFCausalClockFloorWeightedClockControl (weighted)
open KFCausalClockFloorLocalizedSpectrum (orbitObservation)
open KFCausalClockFloorLocalizedSpectralSplit (lowerOrbit orbit_split)
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding)
open KFCausalClockFloorFastTimeEnergy (physicalTime)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "H" => weighted ε hε
local notation "B" => orbitObservation ε hε h hne
local notation "N" => lowerOrbit ε hε h hne
local notation "F" => KFCausalClockFloorFrozenFastEvolution.evolution ε hε h hne hb m g k
local notation "aState" => KFCausalClockFloorFrozenComparison.actual ε hε h hne hb m g k
local notation "P" => KFCausalClockFloorMovingFreeze.actual ε hε h hne hb m g k
local notation "Q" => KFCausalClockFloorMovingFreeze.frozen ε hε h hne hb m g k
local notation "rho" => KFCausalClockFloorResidualDefect.residual ε hε h hne hb m g k

def lowerAverage (a U L R : ℝ) (v : V) : ℝ :=
  (∫ t in 0..L, ‖N R (J (F U t (aState a U v)))‖^2)/L

theorem interval_mass (U L R η : ℝ) (hL : 0 ≤ L) (hη : 0 ≤ η) (v : V)
    (hbound : ∀ t ∈ Set.Icc (0:ℝ) L, η ≤ ‖H (J (F U t v))‖) :
    η^2*L ≤ (∫ t in 0..L, ‖B R (J (F U t v))‖^2)+
      (∫ t in 0..L, ‖N R (J (F U t v))‖^2) := by
  exact KFCausalClockFloorLocalizedSpectralSplit.curve_mass ε hε h hne L R η hL hη
    (fun t => J (F U t v)) ((J).continuous.comp
      (KFCausalClockFloorFrozenFastEvolution.evolution_continuous ε hε h hne hb m g k U v)) hbound

theorem sequence_negative_mass (hk : 0 < k) (a : ℝ) (v : V) (U L : ℕ → ℝ)
    (hpos : ∀ n, 0 < U n ∧ 0 < L n) (hU : Tendsto U atTop atTop) (hLength : Tendsto L atTop atTop)
    (herr : TendstoUniformlyOn (fun n r => P a (U n) (r*L n) (J v)-Q a (U n) (r*L n) (J v))
      (fun _ => 0) atTop (Set.Icc 0 1))
    (hp : 0 < rho (physicalTime a) (J v)) :
    ∃ c : ℝ, 0 < c ∧ ∀ R : ℝ, ∀ᶠ n in atTop,
      c ≤ lowerAverage ε hε h hne hb m g k a (U n) (L n) R v := by
  obtain ⟨η,hη,hlower⟩ := KFCausalClockFloorSelectedWeightedClock.sequence_lower_bound
    ε hε h hne hb m g k a (J v) U L (fun n => ⟨(hpos n).1,(hpos n).2.le⟩) hU herr hp
  refine ⟨η^2/2,by positivity,fun R => ?_⟩
  have hend : Tendsto (fun n => P a (U n) (L n) (J v)-Q a (U n) (L n) (J v)) atTop (𝓝 0) := by
    simpa only [one_mul] using herr.tendsto_at (show (1:ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one,le_rfl⟩)
  have htotal := KFCausalClockFloorSelectedSpectrum.sequence_total_limit ε hε h hne hb m g k
    hk a R v U L (fun n => ⟨(hpos n).1,(hpos n).2.le⟩) hU hend
  have havg := htotal.div_atTop hLength
  filter_upwards [hlower,havg.eventually (gt_mem_nhds (show 0 < η^2/2 by positivity))] with n hn hsmall
  have hm := interval_mass ε hε h hne hb m g k (U n) (L n) R η (hpos n).2.le hη.le
    (aState a (U n) v) (fun t ht => by
      have hr : t/L n ∈ Set.Icc (0:ℝ) 1 :=
        ⟨div_nonneg ht.1 (hpos n).2.le,(div_le_one (hpos n).2).mpr ht.2⟩
      have he := hn (t/L n) hr
      rw [div_mul_cancel₀ _ (hpos n).2.ne',
        ← KFCausalClockFloorSelectedWeightedClock.frozen_embedding] at he
      exact he)
  have hs := (div_lt_iff₀ (hpos n).2).mp hsmall
  apply (le_div_iff₀ (hpos n).2).mpr
  nlinarith only [hm,hs]

theorem exists_negative_escape (hk : 0 < k) (a : ℝ) (ha : 0 < a) (v : V)
    (hr : 0 < rho (physicalTime a) (J v)) :
    ∃ U L : ℕ → ℝ, (∀ n, 0 < U n ∧ 0 < L n) ∧ Tendsto U atTop atTop ∧ Tendsto L atTop atTop ∧
      Tendsto (fun n => (L n)^2/U n) atTop atTop ∧ Tendsto (fun n => L n/U n) atTop (𝓝 0) ∧
      TendstoUniformlyOn (fun n r => P a (U n) (r*L n) (J v)-Q a (U n) (r*L n) (J v))
        (fun _ => 0) atTop (Set.Icc 0 1) ∧
      (∀ R : ℝ, Tendsto (fun n => ∫ t in 0..L n,
        ‖B R (J (F (U n) t (aState a (U n) v)))‖^2) atTop (𝓝 0)) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ R : ℝ, ∀ᶠ n in atTop,
        c ≤ lowerAverage ε hε h hne hb m g k a (U n) (L n) R v := by
  apply Exists.imp _ (KFCausalClockFloorSelectedSpectrum.exists_windows ε hε h hne hb m g k hk a ha v)
  intro U hx
  apply Exists.imp _ hx
  intro L hp
  refine ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2.1,hp.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.2,?_⟩
  exact sequence_negative_mass ε hε h hne hb m g k hk a v U L hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.2.2.1 hr

theorem recovery_or_negative_escape (hk : 0 < k) (a : ℝ) (ha : 0 < a) (v : V) :
    Tendsto (fun t => ‖KFCausalClockFloorDefectOperator.defectOperator ε hε
      (KFCausalClockFloorAveragedEvolution.evolution ε hε h hne hb m g k (physicalTime a) t (J v))‖)
      atTop (𝓝 0) ∨
    ∃ U L : ℕ → ℝ, (∀ n, 0 < U n ∧ 0 < L n) ∧ Tendsto U atTop atTop ∧ Tendsto L atTop atTop ∧
      Tendsto (fun n => (L n)^2/U n) atTop atTop ∧ Tendsto (fun n => L n/U n) atTop (𝓝 0) ∧
      TendstoUniformlyOn (fun n r => P a (U n) (r*L n) (J v)-Q a (U n) (r*L n) (J v))
        (fun _ => 0) atTop (Set.Icc 0 1) ∧
      (∀ R : ℝ, Tendsto (fun n => ∫ t in 0..L n,
        ‖B R (J (F (U n) t (aState a (U n) v)))‖^2) atTop (𝓝 0)) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ R : ℝ, ∀ᶠ n in atTop,
        c ≤ lowerAverage ε hε h hne hb m g k a (U n) (L n) R v := by
  by_cases hr : rho (physicalTime a) (J v)=0
  · exact Or.inl ((KFCausalClockFloorResidualDefect.recovery_iff ε hε h hne hb m g k
      (physicalTime a) (J v)).mpr hr)
  · exact Or.inr (exists_negative_escape ε hε h hne hb m g k hk a ha v
      (lt_of_le_of_ne (KFCausalClockFloorResidualDefect.residual_bounds ε hε h hne hb m g k
        (physicalTime a) (physicalTime a) (J v)).1 (Ne.symm hr)))

#print axioms interval_mass
#print axioms sequence_negative_mass
#print axioms exists_negative_escape
#print axioms recovery_or_negative_escape
end
end UnifiedTheory.Audit.KFCausalClockFloorSelectedNegativeEscape
