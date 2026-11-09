/- The all-state recovery question reduces to the explicit Gaussian
modulation family already constructed in the physical Hilbert space.
This is a reduction, not a proof of recovery of those trajectories. -/
import UnifiedTheory.Audit.KFCausalClockFloorResidualDefect
import UnifiedTheory.Audit.KFCausalClockFloorCoherentStates

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoherentRecoveryCriterion
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator)
open UnifiedTheory.Audit.KFCausalClockFloorResidualDefect (residual residual_continuous recovery_iff)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state dense_span)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "U" => evolution ε hε h hne hb m g k
local notation "D" => defectOperator ε hε

def recoverySpace (s : ℝ) : Submodule ℂ Hilbert where
  carrier := {f | Tendsto (fun t => D (U s t f)) atTop (𝓝 0)}
  zero_mem' := by simpa only [Set.mem_setOf_eq,map_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : Hilbert)) atTop (𝓝 0))
  add_mem' := by
    intro f v hf hv
    simpa only [Set.mem_setOf_eq,map_add,add_zero] using hf.add hv
  smul_mem' := by
    intro c f hf
    simpa only [Set.mem_setOf_eq,map_smul,smul_zero] using (tendsto_const_nhds.smul hf :
      Tendsto (fun t : ℝ => c • D (U s t f)) atTop (𝓝 (c • (0 : Hilbert))))

theorem mem_recoverySpace (s : ℝ) (f : Hilbert) :
    f ∈ recoverySpace ε hε h hne hb m g k s ↔
      Tendsto (fun t => ‖D (U s t f)‖) atTop (𝓝 0) :=
  tendsto_zero_iff_norm_tendsto_zero

theorem recoverySpace_closed (s : ℝ) :
    IsClosed (recoverySpace ε hε h hne hb m g k s : Set Hilbert) := by
  have he : (recoverySpace ε hε h hne hb m g k s : Set Hilbert) =
      {f | residual ε hε h hne hb m g k s f = 0} := by
    ext f
    exact (mem_recoverySpace ε hε h hne hb m g k s f).trans
      (recovery_iff ε hε h hne hb m g k s f)
  rw [he]
  exact isClosed_eq (residual_continuous ε hε h hne hb m g k s) continuous_const

theorem recovery_of_total_family {ι : Type*} (s : ℝ) (v : ι → Hilbert)
    (htotal : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤)
    (hv : ∀ i, Tendsto (fun t => ‖D (U s t (v i))‖) atTop (𝓝 0)) :
    ∀ f : Hilbert, Tendsto (fun t => ‖D (U s t f)‖) atTop (𝓝 0) := by
  have hi : Submodule.span ℂ (Set.range v) ≤ recoverySpace ε hε h hne hb m g k s := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact (mem_recoverySpace ε hε h hne hb m g k s (v i)).mpr (hv i)
  have hc := Submodule.topologicalClosure_mono hi
  rw [htotal,(recoverySpace_closed ε hε h hne hb m g k s).submodule_topologicalClosure_eq] at hc
  exact fun f => (mem_recoverySpace ε hε h hne hb m g k s f).mp (hc (Submodule.mem_top))

theorem recovery_iff_coherent_family (a : ℝ) (ha : 0 < a) (s : ℝ) :
    (∀ f : Hilbert, Tendsto (fun t => ‖D (U s t f)‖) atTop (𝓝 0)) ↔
      (∀ q : Joint 2 4, Tendsto (fun t => ‖D (U s t (state ε a h hε ha hne q))‖) atTop (𝓝 0)) :=
  ⟨fun hf q => hf (state ε a h hε ha hne q),
    recovery_of_total_family ε hε h hne hb m g k s _ (dense_span ε a h hε ha hne)⟩

theorem failure_has_coherent_witness (a : ℝ) (ha : 0 < a) (s : ℝ)
    (f : Hilbert) (hf : ¬ Tendsto (fun t => ‖D (U s t f)‖) atTop (𝓝 0)) :
    ∃ q : Joint 2 4, ¬ Tendsto (fun t => ‖D (U s t (state ε a h hε ha hne q))‖) atTop (𝓝 0) := by
  classical
  by_contra hn
  push_neg at hn
  exact hf ((recovery_iff_coherent_family ε hε h hne hb m g k a ha s).mpr hn f)

#print axioms mem_recoverySpace
#print axioms recoverySpace_closed
#print axioms recovery_of_total_family
#print axioms recovery_iff_coherent_family
#print axioms failure_has_coherent_witness
end
end UnifiedTheory.Audit.KFCausalClockFloorCoherentRecoveryCriterion
