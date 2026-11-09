/- The actual all-state asymptotic clock defect is a continuous residual.
Any failure of recovery is already witnessed by finite-energy initial
data, arbitrarily close to the failing state. No failure is asserted. -/
import UnifiedTheory.Audit.KFCausalClockFloorDefectMonotonicity
import Mathlib.Topology.Order.MonotoneConvergence

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorResidualDefect
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorDefectMonotonicity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormGeometry (embedding_dense)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "U" => evolution ε hε h hne hb m g k
local notation "D" => defectOperator ε hε
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0

def residual (s : ℝ) (f : Hilbert) : ℝ := ⨅ t : ℝ, ‖D (U s t f)‖

theorem residual_bounds (s t : ℝ) (f : Hilbert) :
    0 ≤ residual ε hε h hne hb m g k s f ∧
      residual ε hε h hne hb m g k s f ≤ ‖D (U s t f)‖ := by
  have hb' : BddBelow (Set.range (fun t => ‖D (U s t f)‖)) :=
    ⟨0,by rintro _ ⟨u,rfl⟩; exact norm_nonneg _⟩
  exact ⟨le_ciInf (fun _ => norm_nonneg _),ciInf_le hb' t⟩

theorem norm_limit (s : ℝ) (f : Hilbert) :
    Tendsto (fun t => ‖D (U s t f)‖) atTop
      (𝓝 (residual ε hε h hne hb m g k s f)) :=
  tendsto_atTop_ciInf (evolution_defect_antitone ε hε h hne hb m g k s f)
    ⟨0,by rintro _ ⟨u,rfl⟩; exact norm_nonneg _⟩

theorem recovery_iff (s : ℝ) (f : Hilbert) :
    Tendsto (fun t => ‖D (U s t f)‖) atTop (𝓝 0) ↔
      residual ε hε h hne hb m g k s f = 0 := by
  constructor
  · intro ht
    exact tendsto_nhds_unique (norm_limit ε hε h hne hb m g k s f) ht
  · intro hz
    simpa only [hz] using norm_limit ε hε h hne hb m g k s f

theorem residual_difference (s : ℝ) (f v : Hilbert) :
    |residual ε hε h hne hb m g k s f-residual ε hε h hne hb m g k s v| ≤ ‖f-v‖ := by
  apply le_of_tendsto
    (((norm_limit ε hε h hne hb m g k s f).sub
      (norm_limit ε hε h hne hb m g k s v)).abs)
  exact Eventually.of_forall (fun t => (abs_norm_sub_norm_le _ _).trans (by
    rw [← map_sub,← map_sub]
    exact (defectOperator_norm_le ε hε _).trans_eq ((U s t).norm_map (f-v))))

theorem residual_continuous (s : ℝ) : Continuous (residual ε hε h hne hb m g k s) := by
  have hl : LipschitzWith 1 (residual ε hε h hne hb m g k s) :=
    LipschitzWith.of_dist_le_mul (fun f v => by
      simpa only [Real.dist_eq,dist_eq_norm,NNReal.coe_one,one_mul] using
        residual_difference ε hε h hne hb m g k s f v)
  exact hl.continuous

theorem finite_energy_failure_near (s : ℝ) (f : Hilbert)
    (hf : ¬ Tendsto (fun t => ‖D (U s t f)‖) atTop (𝓝 0))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ v : V, ‖f-J v‖ < δ ∧
      0 < residual ε hε h hne hb m g k s (J v) := by
  have hp : 0 < residual ε hε h hne hb m g k s f :=
    lt_of_le_of_ne (residual_bounds ε hε h hne hb m g k s s f).1
      (fun hz => hf ((recovery_iff ε hε h hne hb m g k s f).mpr hz.symm))
  obtain ⟨z,⟨v,rfl⟩,hv⟩ := Metric.mem_closure_iff.mp
    (embedding_dense ε hε h hne hb m g k 0 f) (min δ (residual ε hε h hne hb m g k s f/2))
    (lt_min hδ (half_pos hp))
  rw [dist_eq_norm] at hv
  refine ⟨v,hv.trans_le (min_le_left _ _),?_⟩
  have hd := (abs_le.mp (residual_difference ε hε h hne hb m g k s f (J v))).2
  have hs := hv.trans_le (min_le_right _ _)
  linarith

theorem recovery_iff_finite_energy (s : ℝ) :
    (∀ f : Hilbert, Tendsto (fun t => ‖D (U s t f)‖) atTop (𝓝 0)) ↔
      (∀ v : V, Tendsto (fun t => ‖D (U s t (J v))‖) atTop (𝓝 0)) := by
  constructor
  · exact fun hf v => hf (J v)
  · intro hv f
    by_contra hn
    obtain ⟨v,_,hp⟩ := finite_energy_failure_near ε hε h hne hb m g k s f hn 1 zero_lt_one
    exact hp.ne' ((recovery_iff ε hε h hne hb m g k s (J v)).mp (hv v))

#print axioms residual_bounds
#print axioms norm_limit
#print axioms recovery_iff
#print axioms residual_difference
#print axioms residual_continuous
#print axioms finite_energy_failure_near
#print axioms recovery_iff_finite_energy
end
end UnifiedTheory.Audit.KFCausalClockFloorResidualDefect
