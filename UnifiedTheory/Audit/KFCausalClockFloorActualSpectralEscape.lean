/- The spectral escape alternative now concerns averages along the
actual physical trajectory. The normalized windows are in fast time. -/
import UnifiedTheory.Audit.KFCausalClockFloorActualObservationAverages
import UnifiedTheory.Audit.KFCausalClockFloorSelectedNegativeEscape

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorActualSpectralEscape
noncomputable section
open Filter MeasureTheory
open scoped Topology
open KFCausalClockFloorAveragedFormTransport (FormSpace embedding)
open KFCausalClockFloorFastTimeEnergy (physicalTime)
open KFCausalClockFloorActualObservationAverages (actualAverage frozenAverage)
open KFCausalClockFloorLocalizedSpectrum (orbitObservation)
open KFCausalClockFloorLocalizedSpectralSplit (lowerOrbit)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "P" => KFCausalClockFloorMovingFreeze.actual ε hε h hne hb m g k
local notation "Q" => KFCausalClockFloorMovingFreeze.frozen ε hε h hne hb m g k
local notation "rho" => KFCausalClockFloorResidualDefect.residual ε hε h hne hb m g k
local notation "B" => orbitObservation ε hε h hne
local notation "N" => lowerOrbit ε hε h hne
local notation "AA" => actualAverage ε hε h hne hb m g k
local notation "FA" => frozenAverage ε hε h hne hb m g k

theorem sequence_upper_limit (hk : 0 < k) (a R : ℝ) (v : V) (U L : ℕ → ℝ)
    (hpos : ∀ n, 0 < U n ∧ 0 < L n) (hU : Tendsto U atTop atTop) (hLength : Tendsto L atTop atTop)
    (herr : TendstoUniformlyOn (fun n r => P a (U n) (r*L n) (J v)-Q a (U n) (r*L n) (J v))
      (fun _ => 0) atTop (Set.Icc 0 1)) :
    Tendsto (fun n => AA (B R) a (U n) (L n) (J v)) atTop (𝓝 0) := by
  have he := KFCausalClockFloorActualObservationAverages.comparison_limit ε hε h hne hb m g k
    (B R) a (J v) U L (fun n => ⟨(hpos n).1,(hpos n).2.le⟩) herr
  have hend : Tendsto (fun n => P a (U n) (L n) (J v)-Q a (U n) (L n) (J v)) atTop (𝓝 0) := by
    simpa only [one_mul] using herr.tendsto_at (show (1:ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one,le_rfl⟩)
  have ht := KFCausalClockFloorSelectedSpectrum.sequence_total_limit ε hε h hne hb m g k
    hk a R v U L (fun n => ⟨(hpos n).1,(hpos n).2.le⟩) hU hend
  have hf : Tendsto (fun n => FA (B R) a (U n) (L n) (J v)) atTop (𝓝 0) :=
    (ht.div_atTop hLength).congr' (Eventually.of_forall (fun n =>
      (KFCausalClockFloorActualObservationAverages.frozen_form_average ε hε h hne hb m g k
        (B R) a (U n) (L n) (hpos n).2.ne' v).symm))
  simpa only [sub_add_cancel,add_zero] using he.add hf

theorem sequence_negative_mass (hk : 0 < k) (a : ℝ) (v : V) (U L : ℕ → ℝ)
    (hpos : ∀ n, 0 < U n ∧ 0 < L n) (hU : Tendsto U atTop atTop) (hLength : Tendsto L atTop atTop)
    (herr : TendstoUniformlyOn (fun n r => P a (U n) (r*L n) (J v)-Q a (U n) (r*L n) (J v))
      (fun _ => 0) atTop (Set.Icc 0 1)) (hp : 0 < rho (physicalTime a) (J v)) :
    ∃ c : ℝ, 0 < c ∧ ∀ R : ℝ, ∀ᶠ n in atTop,
      c ≤ AA (N R) a (U n) (L n) (J v) := by
  obtain ⟨c,hc,hnegative⟩ := KFCausalClockFloorSelectedNegativeEscape.sequence_negative_mass
    ε hε h hne hb m g k hk a v U L hpos hU hLength herr hp
  refine ⟨c/2,by positivity,fun R => ?_⟩
  have he := KFCausalClockFloorActualObservationAverages.comparison_limit ε hε h hne hb m g k
    (N R) a (J v) U L (fun n => ⟨(hpos n).1,(hpos n).2.le⟩) herr
  filter_upwards [hnegative R,he.eventually (lt_mem_nhds (show -(c/2)<0 by linarith))] with n hn heN
  have hf := KFCausalClockFloorActualObservationAverages.frozen_form_average ε hε h hne hb m g k
    (N R) a (U n) (L n) (hpos n).2.ne' v
  change FA (N R) a (U n) (L n) (J v)=
    KFCausalClockFloorSelectedNegativeEscape.lowerAverage ε hε h hne hb m g k a (U n) (L n) R v at hf
  rw [← hf] at hn
  linarith only [hn,heN]

theorem exists_actual_escape (hk : 0 < k) (a : ℝ) (ha : 0 < a) (v : V)
    (hr : 0 < rho (physicalTime a) (J v)) :
    ∃ U L : ℕ → ℝ, (∀ n, 0 < U n ∧ 0 < L n) ∧ Tendsto U atTop atTop ∧ Tendsto L atTop atTop ∧
      Tendsto (fun n => (L n)^2/U n) atTop atTop ∧ Tendsto (fun n => L n/U n) atTop (𝓝 0) ∧
      (∀ R : ℝ, Tendsto (fun n => AA (B R) a (U n) (L n) (J v)) atTop (𝓝 0)) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ R : ℝ, ∀ᶠ n in atTop, c ≤ AA (N R) a (U n) (L n) (J v) := by
  apply Exists.imp _ (KFCausalClockFloorSelectedSpectrum.exists_windows ε hε h hne hb m g k hk a ha v)
  intro U hx
  apply Exists.imp _ hx
  intro L hp
  refine ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2.1,?_,?_⟩
  · intro R
    exact sequence_upper_limit ε hε h hne hb m g k hk a R v U L hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.2.2.1
  · exact sequence_negative_mass ε hε h hne hb m g k hk a v U L
      hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.2.2.1 hr

theorem recovery_or_actual_escape (hk : 0 < k) (a : ℝ) (ha : 0 < a) (v : V) :
    Tendsto (fun t => ‖KFCausalClockFloorDefectOperator.defectOperator ε hε
      (KFCausalClockFloorAveragedEvolution.evolution ε hε h hne hb m g k (physicalTime a) t (J v))‖)
      atTop (𝓝 0) ∨
    ∃ U L : ℕ → ℝ, (∀ n, 0 < U n ∧ 0 < L n) ∧ Tendsto U atTop atTop ∧ Tendsto L atTop atTop ∧
      Tendsto (fun n => (L n)^2/U n) atTop atTop ∧ Tendsto (fun n => L n/U n) atTop (𝓝 0) ∧
      (∀ R : ℝ, Tendsto (fun n => AA (B R) a (U n) (L n) (J v)) atTop (𝓝 0)) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ R : ℝ, ∀ᶠ n in atTop, c ≤ AA (N R) a (U n) (L n) (J v) := by
  by_cases hr : rho (physicalTime a) (J v)=0
  · exact Or.inl ((KFCausalClockFloorResidualDefect.recovery_iff ε hε h hne hb m g k
      (physicalTime a) (J v)).mpr hr)
  · exact Or.inr (exists_actual_escape ε hε h hne hb m g k hk a ha v
      (lt_of_le_of_ne (KFCausalClockFloorResidualDefect.residual_bounds ε hε h hne hb m g k
        (physicalTime a) (physicalTime a) (J v)).1 (Ne.symm hr)))

#print axioms sequence_upper_limit
#print axioms sequence_negative_mass
#print axioms exists_actual_escape
#print axioms recovery_or_actual_escape
end
end UnifiedTheory.Audit.KFCausalClockFloorActualSpectralEscape
