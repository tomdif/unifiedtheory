/- Full-time negative spectral escape is necessary for a positive clock
residual, for every Hilbert initial state. The exact negative-tail
criterion no longer requires finite initial energy. -/
import UnifiedTheory.Audit.KFCausalClockFloorFullTimeSpectrum
import UnifiedTheory.Audit.KFCausalClockFloorNegativeTailCriterion

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFullTimeNegativeEscape
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorDefectOperator (defectOperator)
open KFCausalClockFloorWeightedClockControl (weighted)
open KFCausalClockFloorLocalizedSpectralSplit (lowerOrbit orbit_split)
open KFCausalClockFloorLocalizedSpectrum (orbitObservation)
open KFCausalClockFloorNegativeTailCriterion (EventuallyTight recovery_implies_tail_limit)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "E" => KFCausalClockFloorAveragedEvolution.evolution ε hε h hne hb m g k
local notation "rho" => KFCausalClockFloorResidualDefect.residual ε hε h hne hb m g k
local notation "D" => defectOperator ε hε
local notation "N" => lowerOrbit ε hε h hne
local notation "B" => orbitObservation ε hε h hne

theorem lower_mass_asymptotic (hk : 0 < k) (s R : ℝ) (f : Hilbert) :
    Tendsto (fun t => ‖N R (E s t f)‖^2-‖weighted ε hε (E s t f)‖^2) atTop (𝓝 0) := by
  have hu := ((KFCausalClockFloorFullTimeSpectrum.upper_decay ε hε h hne hb m g k hk s R f).norm.pow 2).neg
  simp only [norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),neg_zero] at hu
  apply hu.congr' (Eventually.of_forall (fun t => ?_))
  have hs := orbit_split ε hε h hne R (E s t f)
  linarith only [hs]

theorem persistent_negative_mass (hk : 0 < k) (s : ℝ) (f : Hilbert) (hp : 0 < rho s f) :
    ∃ c : ℝ, 0 < c ∧
      (∀ t, s ≤ t → 2*c ≤ ‖weighted ε hε (E s t f)‖^2) ∧
      ∀ R : ℝ, ∀ᶠ t in atTop, c ≤ ‖N R (E s t f)‖^2 := by
  have hw := KFCausalClockFloorPersistentWeightedClock.persistent_weight ε hε h hne hb m g k s f hp
  let η : ℝ := hw.choose
  have hη : 0 < η := hw.choose_spec.1
  have hs (t : ℝ) (ht : s ≤ t) : η^2 ≤ ‖weighted ε hε (E s t f)‖^2 :=
    pow_le_pow_left₀ hη.le (hw.choose_spec.2 t ht) 2
  refine ⟨η^2/2,by positivity,fun t ht => by linarith only [hs t ht],fun R => ?_⟩
  filter_upwards [(lower_mass_asymptotic ε hε h hne hb m g k hk s R f).eventually
    (lt_mem_nhds (show -(η^2/2)<0 by
      have hpos : 0 < η^2/2 := by positivity
      linarith only [hpos])),
    eventually_ge_atTop s] with t ht hst
  linarith only [ht,hs t hst]

theorem recovery_or_full_time_escape (hk : 0 < k) (s : ℝ) (f : Hilbert) :
    Tendsto (fun t => ‖D (E s t f)‖) atTop (𝓝 0) ∨
      ∃ c : ℝ, 0 < c ∧ ∀ R : ℝ, ∀ᶠ t in atTop, c ≤ ‖N R (E s t f)‖^2 := by
  by_cases hr : rho s f=0
  · exact Or.inl ((KFCausalClockFloorResidualDefect.recovery_iff ε hε h hne hb m g k s f).mpr hr)
  · right
    apply Exists.imp _ (persistent_negative_mass ε hε h hne hb m g k hk s f
      (lt_of_le_of_ne (KFCausalClockFloorResidualDefect.residual_bounds ε hε h hne hb m g k s s f).1
        (Ne.symm hr)))
    intro c hc
    exact ⟨hc.1,hc.2.2⟩

theorem recovery_iff_eventually_tight (hk : 0 < k) (s : ℝ) (f : Hilbert) :
    Tendsto (fun t => ‖D (E s t f)‖) atTop (𝓝 0) ↔
      EventuallyTight ε hε h hne hb m g k s f := by
  constructor
  · intro hd δ hδ
    exact ⟨0,(recovery_implies_tail_limit ε hε h hne hb m g k s 0 f hd).eventually (gt_mem_nhds hδ)⟩
  · intro htight
    by_contra hd
    have he := (recovery_or_full_time_escape ε hε h hne hb m g k hk s f).resolve_left hd
    let c : ℝ := he.choose
    have hc : 0 < c := he.choose_spec.1
    obtain ⟨R,hR⟩ := htight (c/2) (by positivity)
    obtain ⟨t,ht,hsmall⟩ := ((he.choose_spec.2 R).and hR).exists
    linarith only [hc,ht,hsmall]

theorem recovery_iff_one_threshold (hk : 0 < k) (s : ℝ) (f : Hilbert) :
    Tendsto (fun t => ‖D (E s t f)‖) atTop (𝓝 0) ↔
      ∃ R : ℝ, Tendsto (fun t => ‖N R (E s t f)‖^2) atTop (𝓝 0) := by
  constructor
  · intro hd
    exact ⟨0,recovery_implies_tail_limit ε hε h hne hb m g k s 0 f hd⟩
  · rintro ⟨R,hR⟩
    apply (recovery_iff_eventually_tight ε hε h hne hb m g k hk s f).mpr
    intro δ hδ
    exact ⟨R,hR.eventually (gt_mem_nhds hδ)⟩

#print axioms lower_mass_asymptotic
#print axioms persistent_negative_mass
#print axioms recovery_or_full_time_escape
#print axioms recovery_iff_eventually_tight
#print axioms recovery_iff_one_threshold
end
end UnifiedTheory.Audit.KFCausalClockFloorFullTimeNegativeEscape
