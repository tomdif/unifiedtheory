/- The actual pure-clock identity extends to every state with both
 longitudinal and transverse shear momentum, using the proved compact
 graph core and selfadjointness. No reverse sum-domain equality is claimed. -/
import UnifiedTheory.Audit.KFCausalClockFloorPureClockTestCore
import UnifiedTheory.Audit.KFCausalSelfAdjointCoreWeakGraph
import UnifiedTheory.Audit.KFCausalClockFloorShearCommonDomain
import UnifiedTheory.Audit.KFCausalTransverseShearGraphCommutation
import UnifiedTheory.Audit.KFCausalClockFloorDefectForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockJointDomain
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum pure_selfAdjoint)
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (longitudinalMomentum longitudinal_selfAdjoint)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum shear_selfAdjoint)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockCommonDomain (clockInverse clockInverse_norm)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockTestCore (testGraph compact_graph_core)
open UnifiedTheory.Audit.KFCausalSelfAdjointCoreWeakGraph
open UnifiedTheory.Audit.KFCausalClockFloorDefectForm (defect_inner)

variable (ε : ℝ) (hε : 0 < ε)

theorem clockInverse_inner (f g : Hilbert) :
    inner ℂ (clockInverse ε hε f) g = inner ℂ f (clockInverse ε hε g) := by
  have hc : (starRingEnd ℂ) (1/(ε:ℂ)) = 1/(ε:ℂ) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_one] using Complex.conj_ofReal (1/ε)
  simp only [clockInverse,ContinuousLinearMap.smul_apply,inner_smul_left,inner_smul_right,hc,defect_inner]

theorem clockInverse_shear_graph (h : ℝ) (hh : h ≠ 0) (f j : Hilbert)
    (hj : (f,j) ∈ (shearMomentum h).graph) :
    (clockInverse ε hε f,clockInverse ε hε j) ∈ (shearMomentum h).graph :=
  (shearMomentum h).graph.smul_mem (1/(ε:ℂ))
    (KFCausalTransverseShearGraphCommutation.defect_shear_graph ε hε h hh f j hj)

theorem graph_decomposition (h : ℝ) (hh : h ≠ 0) (f l j : Hilbert)
    (hl : (f,l) ∈ (longitudinalMomentum ε hε h).graph)
    (hj : (f,j) ∈ (shearMomentum h).graph) :
    (f,l-clockInverse ε hε j) ∈ (pureMomentum ε hε h).graph := by
  apply (graph_iff_core_weak _ (pure_selfAdjoint ε hε h hh)
    (testGraph ε hε h) (compact_graph_core ε hε h hh) f (l-clockInverse ε hε j)).mpr
  rintro ⟨v,w⟩ hv
  obtain ⟨φ,hφ,rfl⟩ := hv.2
  obtain ⟨p,b,lv,jv,hp,hb,hlv,hjv,he,hbound⟩ :=
    KFCausalClockFloorShearCommonDomain.compact_four_momenta ε hε h hh φ hφ φ.hasCompactSupport
  have hw : w = b := (pureMomentum ε hε h).mem_graph_snd_inj' hv.1 hb rfl
  have hb' : b = lv-clockInverse ε hε jv := by rw [he]; abel
  have hL := (graph_iff_weak _ (longitudinal_selfAdjoint ε hε h hh) f l).mp hl _ _ hlv
  have hJ := (graph_iff_weak _ (shear_selfAdjoint h hh) (clockInverse ε hε f) (clockInverse ε hε j)).mp
    (clockInverse_shear_graph ε hε h hh f j hj) _ _ hjv
  change inner ℂ w f = inner ℂ (embedding φ) (l-clockInverse ε hε j)
  rw [hw,hb',inner_sub_left,clockInverse_inner,hL,hJ,inner_sub_right]
  rfl

theorem joint_domain (h : ℝ) (hh : h ≠ 0) (f : Hilbert)
    (hl : f ∈ (longitudinalMomentum ε hε h).domain)
    (hj : f ∈ (shearMomentum h).domain) : f ∈ (pureMomentum ε hε h).domain := by
  obtain ⟨l,hl⟩ := LinearPMap.mem_domain_iff.mp hl
  obtain ⟨j,hj⟩ := LinearPMap.mem_domain_iff.mp hj
  exact LinearPMap.mem_domain_of_mem_graph (graph_decomposition ε hε h hh f l j hl hj)

theorem outputs_identity (h : ℝ) (hh : h ≠ 0) (f b l j : Hilbert)
    (hb : (f,b) ∈ (pureMomentum ε hε h).graph)
    (hl : (f,l) ∈ (longitudinalMomentum ε hε h).graph)
    (hj : (f,j) ∈ (shearMomentum h).graph) : b = l-clockInverse ε hε j :=
  (pureMomentum ε hε h).mem_graph_snd_inj' hb (graph_decomposition ε hε h hh f l j hl hj) rfl

theorem output_norm (h : ℝ) (hh : h ≠ 0) (f b l j : Hilbert)
    (hb : (f,b) ∈ (pureMomentum ε hε h).graph)
    (hl : (f,l) ∈ (longitudinalMomentum ε hε h).graph)
    (hj : (f,j) ∈ (shearMomentum h).graph) : ‖b‖ ≤ ‖l‖+(1/ε)*‖j‖ := by
  rw [outputs_identity ε hε h hh f b l j hb hl hj]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl (clockInverse_norm ε hε j))

#print axioms clockInverse_inner
#print axioms clockInverse_shear_graph
#print axioms graph_decomposition
#print axioms joint_domain
#print axioms outputs_identity
#print axioms output_norm
end
end UnifiedTheory.Audit.KFCausalClockFloorPureClockJointDomain
