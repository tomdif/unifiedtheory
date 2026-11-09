/- A graph-level inverse-defect argument for the actual unbounded clock.
The common composition domain is characterized, and both compositions
are constructed from a proved defect intertwining rule. -/
import UnifiedTheory.Audit.KFCausalClockFloorClockShiftDifference
import UnifiedTheory.Audit.KFCausalClockFloorClockOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorClockShiftCommutator
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorClockOperator
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical
open UnifiedTheory.Audit.KFCausalClockFloorClockShiftDifference

theorem clock_shifted_graph (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (g : Hilbert) :
    (shiftedDefect ε hε h hh g,(ε:ℂ) • g+
      differenceOperator ε hε h hh (shiftedDefect ε hε h hh g)) ∈ (clockOperator ε hε).graph := by
  apply (clockOperator_graph ε hε _ _).mpr
  let B := shiftedDefect ε hε h hh
  let Δ := differenceOperator ε hε h hh
  filter_upwards [Lp.coeFn_add ((ε:ℂ) • g) (Δ (B g)),Lp.coeFn_smul (ε:ℂ) g,
    differenceOperator_coe ε hε h hh (B g),shiftedDefect_physical_coe ε hε h hh g]
    with x ha hs hd hb
  change ((ε:ℂ) • g+Δ (B g)) x = (KFCausalClockFloorFlow.clock ε x.1:ℂ)*(B g) x
  change Δ (B g) x = _ at hd
  change B g x = _ at hb
  rw [ha]
  simp only [Pi.add_apply,hs,Pi.smul_apply,smul_eq_mul,hd,hb,difference]
  linear_combination -(g x)*(shiftedClock_defect ε hε h hh x)

def commonDomain (ε : ℝ) (hε : 0 < ε) (T : Hilbert →ₗ.[ℂ] Hilbert) : Set Hilbert :=
  defectOperator ε hε '' (T.domain : Set Hilbert)

theorem commonDomain_dense (ε : ℝ) (hε : 0 < ε) (T : Hilbert →ₗ.[ℂ] Hilbert)
    (hT : Dense (T.domain : Set Hilbert)) : Dense (commonDomain ε hε T) :=
  (defectOperator_denseRange ε hε).dense_image (defectOperator ε hε).continuous hT

/-- This is exactly Dom(T C); the other composition is constructed below. -/
theorem commonDomain_iff (ε : ℝ) (hε : 0 < ε) (T : Hilbert →ₗ.[ℂ] Hilbert) (f : Hilbert) :
    f ∈ commonDomain ε hε T ↔ ∃ cf : Hilbert,
      (f,cf) ∈ (clockOperator ε hε).graph ∧ cf ∈ T.domain := by
  constructor
  · rintro ⟨g,hg,rfl⟩
    exact ⟨(ε:ℂ) • g,clock_defect_graph ε hε g,T.domain.smul_mem (ε:ℂ) hg⟩
  · rintro ⟨cf,hc,ht⟩
    refine ⟨(ε:ℂ)⁻¹ • cf,T.domain.smul_mem _ ht,?_⟩
    rw [map_smul,defect_clock ε hε f cf hc,smul_smul,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hε.ne'),one_smul]

theorem commonDomain_graphs (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (T : Hilbert →ₗ.[ℂ] Hilbert)
    (hT : ∀ u v : Hilbert, (u,v) ∈ T.graph →
      (defectOperator ε hε u,shiftedDefect ε hε h hh v) ∈ T.graph)
    (f : Hilbert) (hf : f ∈ commonDomain ε hε T) :
    ∃ cf tf tcf ctf : Hilbert,
      (f,cf) ∈ (clockOperator ε hε).graph ∧ (f,tf) ∈ T.graph ∧
      (cf,tcf) ∈ T.graph ∧ (tf,ctf) ∈ (clockOperator ε hε).graph ∧
      ctf-tcf = differenceOperator ε hε h hh tf ∧ ‖ctf-tcf‖ ≤ |h| * ‖tf‖ := by
  rcases hf with ⟨u,hu,rfl⟩
  let v := T ⟨u,hu⟩
  let b := shiftedDefect ε hε h hh v
  refine ⟨(ε:ℂ) • u,b,(ε:ℂ) • v,(ε:ℂ) • v+differenceOperator ε hε h hh b,
    clock_defect_graph ε hε u,hT u v (T.mem_graph ⟨u,hu⟩),
    T.graph.smul_mem (ε:ℂ) (T.mem_graph ⟨u,hu⟩),clock_shifted_graph ε hε h hh v,?_,?_⟩
  · abel
  · simpa only [add_sub_cancel_left] using differenceOperator_norm ε hε h hh b

theorem commutator_graph (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hh : |h| ≤ 2*Real.pi*ε/3) (T : Hilbert →ₗ.[ℂ] Hilbert)
    (hT : ∀ u v : Hilbert, (u,v) ∈ T.graph →
      (defectOperator ε hε u,shiftedDefect ε hε h hh v) ∈ T.graph)
    (f cf tf tcf ctf : Hilbert)
    (hc : (f,cf) ∈ (clockOperator ε hε).graph) (ht : (f,tf) ∈ T.graph)
    (htc : (cf,tcf) ∈ T.graph) (hct : (tf,ctf) ∈ (clockOperator ε hε).graph) :
    ctf-tcf = differenceOperator ε hε h hh tf ∧ ‖ctf-tcf‖ ≤ |h| * ‖tf‖ := by
  have hf := (commonDomain_iff ε hε T f).mpr ⟨cf,hc,LinearPMap.mem_domain_of_mem_graph htc⟩
  obtain ⟨cf',tf',tcf',ctf',hc',ht',htc',hct',he,hb⟩ := commonDomain_graphs ε hε h hh T hT f hf
  have ec : cf' = cf := (clockOperator ε hε).mem_graph_snd_inj' hc' hc rfl
  have et : tf' = tf := T.mem_graph_snd_inj' ht' ht rfl
  subst cf'
  subst tf'
  have etc : tcf' = tcf := T.mem_graph_snd_inj' htc' htc rfl
  have ect : ctf' = ctf := (clockOperator ε hε).mem_graph_snd_inj' hct' hct rfl
  simpa only [etc,ect] using And.intro he hb

#print axioms clock_shifted_graph
#print axioms commonDomain_dense
#print axioms commonDomain_iff
#print axioms commonDomain_graphs
#print axioms commutator_graph

end
end UnifiedTheory.Audit.KFCausalClockFloorClockShiftCommutator
