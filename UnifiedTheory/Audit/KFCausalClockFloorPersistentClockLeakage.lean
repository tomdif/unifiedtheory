/- Failure of actual clock recovery forces persistent, rather than only
recurrent, windowed probability in one bounded clock band outside every
fixed phase-space ball. This does not establish that failure occurs. -/
import UnifiedTheory.Audit.KFCausalClockFloorResidualDefect
import UnifiedTheory.Audit.KFCausalClockFloorWindowedRecovery

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPersistentClockLeakage
noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (BlockHilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator)
open UnifiedTheory.Audit.KFCausalClockFloorResidualDefect (residual residual_bounds)
open UnifiedTheory.Audit.KFCausalClockFloorWindowedRecovery (clockRegion clockLaw_region window_uniform_left_tail)
open UnifiedTheory.Audit.KFCausalPhysicalWindowedClock
open UnifiedTheory.Audit.KFCausalPhysicalWindowedLaw (law)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect)
open UnifiedTheory.Audit.KFCausalClockFloorDefectLocalization (lowProjection)
open UnifiedTheory.Audit.KFCausalClockFloorSharpEscapeCriterion (sharp_mass defect_cutoff_bound)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "U" => evolution ε hε h hne hb m g k
local notation "D" => defectOperator ε hε

theorem persistent_clock_mass (s : ℝ) (f : Hilbert) (hf : ‖f‖ = 1)
    (w : BlockHilbert 6) (hw : ‖w‖ = 1)
    (hp : 0 < residual ε hε h hne hb m g k s f) :
    ∃ (S η : ℝ), 0 < η ∧ ∀ t : ℝ,
      ENNReal.ofReal η < law h (U s t f) w (clockRegion S) := by
  let δ := residual ε hε h hne hb m g k s f
  have hn (t : ℝ) : ‖U s t f‖ = 1 := ((U s t).norm_map f).trans hf
  obtain ⟨S,hS⟩ := ((KFCausalClockFloorDefectLimits.defect_large_clock_limit ε hε.le).eventually
    (gt_mem_nhds (half_pos hp))).exists
  have hproj (t : ℝ) : δ/2 < ‖lowProjection S (U s t f)‖ := by
    have hd := (residual_bounds ε hε h hne hb m g k s t f).2
    have hc := defect_cutoff_bound ε hε S (U s t f)
    rw [hn t,mul_one] at hc
    change defect ε S < δ/2 at hS
    change δ ≤ _ at hd
    linarith
  let a := (δ/2)^2
  have ha : 0 < a := sq_pos_of_pos (half_pos hp)
  letI := position_probability 6 0 w hw
  obtain ⟨R,hR⟩ := (ENNReal.tendsto_nhds_zero.mp
    (KFCausalProbabilityWindowEscape.window_tail
      (KFCausalWindowedPositionMarginal.positionLaw 6 0 w))
    (ENNReal.ofReal (a/2)) (ENNReal.ofReal_pos.mpr (half_pos ha))).exists
  refine ⟨S+R,a/2,half_pos ha,fun t => ?_⟩
  have hs : ENNReal.ofReal a <
      KFCausalClockPositionLaw.clockPositionLaw (U s t f) (Set.Iic S) := by
    rw [sharp_mass]
    apply (ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos ((half_pos hp).trans (hproj t)))).mpr
    exact pow_lt_pow_left₀ (hproj t) (half_pos hp).le (by norm_num)
  have hu := sharp_clock_upper h (U s t f) w (hn t) hw S R
  rw [clockLaw_region] at hu
  by_contra hn'
  have hl := le_of_not_gt hn'
  have he : ENNReal.ofReal (a/2)+ENNReal.ofReal (a/2) = ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_add (half_pos ha).le (half_pos ha).le]
    congr 1
    ring
  exact (not_lt_of_ge (hu.trans ((add_le_add hl hR).trans_eq he))) hs

theorem recovery_or_persistent_escape (hk : 0 < k) (s : ℝ) (f : Hilbert) (hf : ‖f‖ = 1)
    (w : BlockHilbert 6) (hw : ‖w‖ = 1) :
    Tendsto (fun t => ‖D (U s t f)‖) atTop (𝓝 0) ∨
      ∃ (L S η : ℝ), L < S ∧ 0 < η ∧ ∀ R : ℝ, ∀ᶠ t : ℝ in atTop,
        ENNReal.ofReal η < law h (U s t f) w
          ((clockRegion S \ clockRegion L) \ Metric.closedBall 0 R) := by
  classical
  by_cases hd : Tendsto (fun t => ‖D (U s t f)‖) atTop (𝓝 0)
  · exact Or.inl hd
  right
  have hp : 0 < residual ε hε h hne hb m g k s f :=
    lt_of_le_of_ne (residual_bounds ε hε h hne hb m g k s s f).1
      (fun hz => hd ((KFCausalClockFloorResidualDefect.recovery_iff ε hε h hne hb m g k s f).mpr hz.symm))
  obtain ⟨S,η,hη,hS⟩ := persistent_clock_mass ε hε h hne hb m g k s f hf w hw hp
  obtain ⟨L,hL⟩ := window_uniform_left_tail ε hε h hne hb m g k s f hf w hw
    (η/3) (by positivity)
  have hLS : L < S := by
    by_contra hn
    have hc : clockRegion S ⊆ clockRegion L := fun _ hx => hx.trans (le_of_not_gt hn)
    have hu := (measure_mono (μ := law h (U s s f) w) hc).trans (hL s le_rfl)
    have hη' : ENNReal.ofReal (η/3) ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal (by linarith)
    exact (not_lt_of_ge (hu.trans hη')) (hS s)
  refine ⟨L,S,η/3,hLS,by positivity,?_⟩
  intro R
  have hb' := KFCausalClockFloorPhaseSpaceEscape.bounded_mass_decay
    ε hε h hne hb m g k hk s f w (Metric.closedBall 0 R) Metric.isBounded_closedBall
  have he := ENNReal.tendsto_nhds_zero.mp hb' (ENNReal.ofReal (η/3))
    (ENNReal.ofReal_pos.mpr (by positivity))
  filter_upwards [he,eventually_ge_atTop s] with t hball ht
  by_contra hn
  have hrem := le_of_not_gt hn
  have hc : clockRegion S ⊆ clockRegion L ∪ Metric.closedBall 0 R ∪
      ((clockRegion S \ clockRegion L) \ Metric.closedBall 0 R) := by
    intro z hz
    by_cases hl : z ∈ clockRegion L
    · exact Or.inl (Or.inl hl)
    · by_cases hbr : z ∈ Metric.closedBall 0 R
      · exact Or.inl (Or.inr hbr)
      · exact Or.inr ⟨⟨hz,hl⟩,hbr⟩
  have hu := (measure_mono (μ := law h (U s t f) w) hc).trans (measure_union_le _ _)
  have hu' := (measure_union_le (μ := law h (U s t f) w) (clockRegion L)
    (Metric.closedBall 0 R)).trans (add_le_add (hL t ht) hball)
  have hsum : ENNReal.ofReal (η/3)+ENNReal.ofReal (η/3)+ENNReal.ofReal (η/3) =
      ENNReal.ofReal η := by
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ η/3) (by positivity : 0 ≤ η/3),
      ← ENNReal.ofReal_add (by positivity : 0 ≤ η/3+η/3) (by positivity : 0 ≤ η/3)]
    congr 1
    ring
  exact (not_lt_of_ge (hu.trans ((add_le_add hu' hrem).trans_eq hsum))) (hS t)

#print axioms persistent_clock_mass
#print axioms recovery_or_persistent_escape
end
end UnifiedTheory.Audit.KFCausalClockFloorPersistentClockLeakage
