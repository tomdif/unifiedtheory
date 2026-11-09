/- Exact measurement criterion for recovery along the full physical
evolution, and the escape channel that any failure of recovery must use. -/
import UnifiedTheory.Audit.KFCausalPhysicalWindowedClock
import UnifiedTheory.Audit.KFCausalClockFloorSharpEscapeCriterion
import UnifiedTheory.Audit.KFCausalClockFloorPhaseSpaceEscape
import UnifiedTheory.Audit.KFCausalClockFloorStrictQuantumLimit
import UnifiedTheory.Audit.KFCausalClockFloorLeftTightness

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorWindowedRecovery
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block BlockHilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalPhysicalWindowedClock
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator)
open UnifiedTheory.Audit.KFCausalPhysicalWindowedLaw (law)

def clockRegion (S : ℝ) : Set (Block 6 × Block 6) := {z | z.1 0 ≤ S}

theorem clockRegion_measurable (S : ℝ) : MeasurableSet (clockRegion S) :=
  measurableSet_le (by fun_prop) measurable_const

theorem clockLaw_region (h : ℝ) (f : Hilbert) (w : BlockHilbert 6) (S : ℝ) :
    clockLaw h f w (Set.Iic S) = law h f w (clockRegion S) := by
  rw [clockLaw,Measure.map_apply (by fun_prop) measurableSet_Iic]
  rfl

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "U" => evolution ε hε h hne hb m g k
local notation "D" => defectOperator ε hε

theorem recovery_iff (s : ℝ) (f : Hilbert) (hf : ‖f‖ = 1)
    (w : BlockHilbert 6) (hw : ‖w‖ = 1) :
    (∀ S, Tendsto (fun t => law h (U s t f) w (clockRegion S)) atTop (𝓝 0)) ↔
      Tendsto (fun t => ‖D (U s t f)‖) atTop (𝓝 0) := by
  have hn (t : ℝ) : ‖U s t f‖ = 1 := ((U s t).norm_map f).trans hf
  have he := (clock_escape_iff atTop h (fun t => U s t f) hn w hw).trans
    (KFCausalClockFloorSharpEscapeCriterion.sharp_escape_iff_defect ε hε atTop
      (fun t => U s t f) 1 (fun t => (hn t).le))
  simpa only [clockLaw_region] using he

theorem expectation_recovery_iff (s : ℝ) (f : Hilbert) (hf : ‖f‖ = 1)
    (w : BlockHilbert 6) (hw : ‖w‖ = 1) :
    (∀ S, Tendsto (fun t => law h (U s t f) w (clockRegion S)) atTop (𝓝 0)) ↔
      Tendsto (fun t => (inner ℂ (U s t f) (D (U s t f))).re) atTop (𝓝 0) :=
  (recovery_iff ε hε h hne hb m g k s f hf w hw).trans
    (KFCausalClockFloorStrictQuantumLimit.zero_limit_iff_defect_norm
      ε hε h hne hb m g k s f).symm

theorem window_independence (s : ℝ) (f : Hilbert) (hf : ‖f‖ = 1)
    (v w : BlockHilbert 6) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    (∀ S, Tendsto (fun t => law h (U s t f) v (clockRegion S)) atTop (𝓝 0)) ↔
      (∀ S, Tendsto (fun t => law h (U s t f) w (clockRegion S)) atTop (𝓝 0)) :=
  (recovery_iff ε hε h hne hb m g k s f hf v hv).trans
    (recovery_iff ε hε h hne hb m g k s f hf w hw).symm

theorem recovery_or_phase_leakage (hk : 0 < k) (s : ℝ) (f : Hilbert) (hf : ‖f‖ = 1)
    (w : BlockHilbert 6) (hw : ‖w‖ = 1) :
    Tendsto (fun t => ‖D (U s t f)‖) atTop (𝓝 0) ∨
      ∃ (S : ℝ) (η : ℝ≥0∞), 0 < η ∧ ∀ R T : ℝ, ∃ t : ℝ, T ≤ t ∧
        η < law h (U s t f) w (clockRegion S \ Metric.closedBall 0 R) := by
  classical
  by_cases hd : Tendsto (fun t => ‖D (U s t f)‖) atTop (𝓝 0)
  · exact Or.inl hd
  right
  have hn : ¬ ∀ S, Tendsto (fun t => law h (U s t f) w (clockRegion S)) atTop (𝓝 0) :=
    fun ht => hd ((recovery_iff ε hε h hne hb m g k s f hf w hw).mp ht)
  push_neg at hn
  obtain ⟨S,hS⟩ := hn
  rw [ENNReal.tendsto_nhds_zero] at hS
  push_neg at hS
  obtain ⟨δ,hδ,hfreq⟩ := hS
  refine ⟨S,δ/2,ENNReal.half_pos hδ.ne',?_⟩
  intro R T
  have hball := KFCausalClockFloorPhaseSpaceEscape.bounded_mass_decay
    ε hε h hne hb m g k hk s f w (Metric.closedBall 0 R) Metric.isBounded_closedBall
  have he := ENNReal.tendsto_nhds_zero.mp hball (δ/2) (ENNReal.half_pos hδ.ne')
  have ht := hfreq.and_eventually (he.and (eventually_ge_atTop T))
  obtain ⟨t,hlarge,hsmall,hT⟩ := ht.exists
  refine ⟨t,hT,?_⟩
  by_contra hnot
  have hlo : law h (U s t f) w (clockRegion S \ Metric.closedBall 0 R) ≤ δ/2 := le_of_not_gt hnot
  have hcover : clockRegion S ⊆ Metric.closedBall 0 R ∪ (clockRegion S \ Metric.closedBall 0 R) := by
    intro z hz
    by_cases hbz : z ∈ Metric.closedBall 0 R
    · exact Or.inl hbz
    · exact Or.inr ⟨hz,hbz⟩
  have hu := (measure_mono (μ := law h (U s t f) w) hcover).trans (measure_union_le _ _)
  have hl := (add_le_add hsmall hlo).trans_eq (ENNReal.add_halves δ)
  exact (not_lt_of_ge (hu.trans hl)) hlarge

theorem window_uniform_left_tail (s : ℝ) (f : Hilbert) (hf : ‖f‖ = 1)
    (w : BlockHilbert 6) (hw : ‖w‖ = 1) (η : ℝ) (hη : 0 < η) :
    ∃ L : ℝ, ∀ t, s ≤ t → law h (U s t f) w (clockRegion L) ≤ ENNReal.ofReal η := by
  letI := position_probability 6 0 w hw
  obtain ⟨R,hR⟩ := (ENNReal.tendsto_nhds_zero.mp
    (KFCausalProbabilityWindowEscape.window_tail
      (KFCausalWindowedPositionMarginal.positionLaw 6 0 w))
    (ENNReal.ofReal (η/2)) (ENNReal.ofReal_pos.mpr (by linarith))).exists
  obtain ⟨L,hL⟩ := KFCausalClockFloorLeftTightness.uniform_left_tail
    ε hε h hne hb m g k s f (η/2) (by linarith)
  refine ⟨L-R,fun t ht => ?_⟩
  have hn : ‖U s t f‖ = 1 := ((U s t).norm_map f).trans hf
  have hu := clockLaw_upper h (U s t f) w hn hw (L-R) R
  rw [clockLaw_region,sub_add_cancel,KFCausalClockFloorSharpEscapeCriterion.sharp_mass] at hu
  exact hu.trans ((add_le_add (ENNReal.ofReal_le_ofReal (hL t ht).le) hR).trans_eq (by
    rw [← ENNReal.ofReal_add (by linarith : 0 ≤ η/2) (by linarith : 0 ≤ η/2)]
    congr 1
    ring))

theorem recovery_or_bounded_clock_leakage (hk : 0 < k) (s : ℝ) (f : Hilbert) (hf : ‖f‖ = 1)
    (w : BlockHilbert 6) (hw : ‖w‖ = 1) :
    Tendsto (fun t => ‖D (U s t f)‖) atTop (𝓝 0) ∨
      ∃ (L S : ℝ) (η : ℝ≥0∞), 0 < η ∧ ∀ R T : ℝ, ∃ t : ℝ, T ≤ t ∧
        η < law h (U s t f) w
          ((clockRegion S \ clockRegion L) \ Metric.closedBall 0 R) := by
  obtain hd | ⟨S,δ,hδ,hescape⟩ := recovery_or_phase_leakage ε hε h hne hb m g k hk s f hf w hw
  · exact Or.inl hd
  right
  obtain ⟨t₀,_,ht₀⟩ := hescape 0 s
  letI := KFCausalClockFloorPhaseSpaceEscape.evolved_probability ε hε h hne hb m g k s t₀ f w hf hw
  have hδtop : δ ≠ ∞ := (ht₀.trans (measure_lt_top _ _)).ne_top
  have hδreal : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδtop
  obtain ⟨L,hL⟩ := window_uniform_left_tail ε hε h hne hb m g k s f hf w hw
    (δ.toReal/2) (by positivity)
  have hhalf : ENNReal.ofReal (δ.toReal/2) = δ/2 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2),ENNReal.ofReal_toReal hδtop]
    norm_num
  refine ⟨L,S,δ/2,ENNReal.half_pos hδ.ne',?_⟩
  intro R T
  obtain ⟨t,ht,hlarge⟩ := hescape R (max T s)
  refine ⟨t,(le_max_left T s).trans ht,?_⟩
  have hsmall := hL t ((le_max_right T s).trans ht)
  rw [hhalf] at hsmall
  by_contra hnot
  have hrem : law h (U s t f) w
      ((clockRegion S \ clockRegion L) \ Metric.closedBall 0 R) ≤ δ/2 := le_of_not_gt hnot
  have hc : clockRegion S \ Metric.closedBall 0 R ⊆ clockRegion L ∪
      ((clockRegion S \ clockRegion L) \ Metric.closedBall 0 R) := by
    intro z hz
    by_cases hl : z ∈ clockRegion L
    · exact Or.inl hl
    · exact Or.inr ⟨⟨hz.1,hl⟩,hz.2⟩
  have hu := (measure_mono (μ := law h (U s t f) w) hc).trans (measure_union_le _ _)
  exact (not_lt_of_ge (hu.trans ((add_le_add hsmall hrem).trans_eq (ENNReal.add_halves δ)))) hlarge

#print axioms clockRegion_measurable
#print axioms clockLaw_region
#print axioms recovery_iff
#print axioms expectation_recovery_iff
#print axioms window_independence
#print axioms recovery_or_phase_leakage
#print axioms window_uniform_left_tail
#print axioms recovery_or_bounded_clock_leakage

end
end UnifiedTheory.Audit.KFCausalClockFloorWindowedRecovery
