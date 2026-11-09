/- Long-time escape of the actual positive physical phase-space law.
The result concerns bounded joint phase regions, not clock half-spaces. -/
import UnifiedTheory.Audit.KFCausalWindowedPhaseSpaceEscape
import UnifiedTheory.Audit.KFCausalPhysicalWindowedLaw
import UnifiedTheory.Audit.KFCausalClockFloorAllChargeWeakEscape

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPhaseSpaceEscape
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block BlockHilbert)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (euclideanPullback)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalPhysicalWindowedLaw

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "U" => evolution ε hε h hne hb m g k

theorem euclidean_weak_decay (hk : 0 < k) (s : ℝ) (f : Hilbert) (z : BlockHilbert 6) :
    Tendsto (fun t => inner ℂ (euclideanPullback (U s t f)) z) atTop (𝓝 0) := by
  have ht := KFCausalClockFloorAllChargeWeakEscape.weak_decay ε hε h hne hb m g k hk
    s f (euclideanPullback.symm z)
  have he (t : ℝ) : inner ℂ (euclideanPullback (U s t f)) z =
      inner ℂ (U s t f) (euclideanPullback.symm z) := by
    simpa only [LinearIsometryEquiv.apply_symm_apply] using
      euclideanPullback.inner_map_map (U s t f) (euclideanPullback.symm z)
  simpa only [he] using ht

theorem region_mass_decay (hk : 0 < k) (s : ℝ) (f : Hilbert) (w : BlockHilbert 6)
    (A : Set (Block 6 × Block 6)) (hAm : MeasurableSet A)
    (hA : volume ((KFCausalWindowedPhaseSpaceLaw.phaseCoordinates 6 h) ⁻¹' A) < ∞) :
    Tendsto (fun t => law h (U s t f) w A) atTop (𝓝 0) := by
  exact KFCausalWindowedPhaseSpaceEscape.law_region_decay 6 h
    (fun t => euclideanPullback (U s t f)) w ‖f‖
    (fun t => by simp only [LinearIsometryEquiv.norm_map,le_refl])
    (euclidean_weak_decay ε hε h hne hb m g k hk s f) A hAm hA

theorem compact_mass_decay (hk : 0 < k) (s : ℝ) (f : Hilbert) (w : BlockHilbert 6)
    (A : Set (Block 6 × Block 6)) (hA : IsCompact A) :
    Tendsto (fun t => law h (U s t f) w A) atTop (𝓝 0) := by
  exact KFCausalWindowedPhaseSpaceEscape.law_compact_decay 6 h hne
    (fun t => euclideanPullback (U s t f)) w ‖f‖
    (fun t => by simp only [LinearIsometryEquiv.norm_map,le_refl])
    (euclidean_weak_decay ε hε h hne hb m g k hk s f) A hA

theorem bounded_mass_decay (hk : 0 < k) (s : ℝ) (f : Hilbert) (w : BlockHilbert 6)
    (A : Set (Block 6 × Block 6)) (hA : Bornology.IsBounded A) :
    Tendsto (fun t => law h (U s t f) w A) atTop (𝓝 0) := by
  exact KFCausalWindowedPhaseSpaceEscape.law_bounded_decay 6 h hne
    (fun t => euclideanPullback (U s t f)) w ‖f‖
    (fun t => by simp only [LinearIsometryEquiv.norm_map,le_refl])
    (euclidean_weak_decay ε hε h hne hb m g k hk s f) A hA

theorem evolved_probability (s t : ℝ) (f : Hilbert) (w : BlockHilbert 6)
    (hf : ‖f‖ = 1) (hw : ‖w‖ = 1) : IsProbabilityMeasure (law h (U s t f) w) :=
  law_probability h (U s t f) w ((U s t).norm_map f |>.trans hf) hw

theorem outside_bounded_probability (hk : 0 < k) (s : ℝ) (f : Hilbert) (w : BlockHilbert 6)
    (hf : ‖f‖ = 1) (hw : ‖w‖ = 1)
    (A : Set (Block 6 × Block 6)) (hAm : MeasurableSet A) (hA : Bornology.IsBounded A) :
    Tendsto (fun t => law h (U s t f) w Aᶜ) atTop (𝓝 1) := by
  have he (t : ℝ) : law h (U s t f) w Aᶜ = 1-law h (U s t f) w A := by
    letI := evolved_probability ε hε h hne hb m g k s t f w hf hw
    exact prob_compl_eq_one_sub hAm
  simp_rw [he]
  have ht := bounded_mass_decay ε hε h hne hb m g k hk s f w A hA
  simpa only [tsub_zero] using
    ENNReal.Tendsto.sub (a := 1) tendsto_const_nhds ht (Or.inl ENNReal.one_ne_top)

#print axioms euclidean_weak_decay
#print axioms region_mass_decay
#print axioms compact_mass_decay
#print axioms bounded_mass_decay
#print axioms evolved_probability
#print axioms outside_bounded_probability

end
end UnifiedTheory.Audit.KFCausalClockFloorPhaseSpaceEscape
