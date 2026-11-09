/- Actual operator identification of the previously explicit shear remainder.
All four momenta exist on every C1 compact physical state. This does not
assert a maximal sum-domain identity or vacuum exponential regularity. -/
import UnifiedTheory.Audit.KFCausalTransverseShearDifferential
import UnifiedTheory.Audit.KFCausalClockFloorPureClockCommonDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorShearCommonDomain
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (clockMomentum longitudinalMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalTransverseShearDifferential (compact_graph graph_representative)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalReconstruction (shearDerivative)
open UnifiedTheory.Audit.KFCausalClockFloorCompactMomentumReconstruction (compact_shear_memLp)

theorem compact_four_momenta (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (f : Configuration → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    let state : Hilbert := (hf.continuous.memLp_of_hasCompactSupport hc).toLp f
    ∃ p b l j : Hilbert,
      (state,p) ∈ (clockMomentum h).graph ∧
      (state,b) ∈ (pureMomentum ε hε h).graph ∧
      (state,l) ∈ (longitudinalMomentum ε hε h).graph ∧
      (state,j) ∈ (shearMomentum h).graph ∧
      l = b+clockInverse ε hε j ∧
      ‖b‖ ≤ ‖l‖+(1/ε)*‖j‖ := by
  let hm : MemLp f 2 (volume : Measure Configuration) := hf.continuous.memLp_of_hasCompactSupport hc
  obtain ⟨p,b,l,d,r,hp,hb,hl,hd,_,_,hld,_,_⟩ := compact_common_outputs ε hε h hh f hf hc
  let j : Hilbert := (-Complex.I*(h:ℂ)) • (compact_shear_memLp f hf hc).toLp (shearDerivative f)
  have hj : (hm.toLp f,j) ∈ (shearMomentum h).graph := compact_graph h hh f hf hc
  have he : d = clockInverse ε hε j := by
    apply Lp.ext
    filter_upwards [hd,clockInverse_coe ε hε j,
      graph_representative h hh f hm (hf.differentiable (by norm_num)) j hj] with x hx hy hz
    rw [hx,hy,hz]
  rw [he] at hld
  refine ⟨p,b,l,j,hp,hb,hl,hj,hld,?_⟩
  have hb' : b = l-clockInverse ε hε j := by rw [hld]; abel
  calc
    ‖b‖ = ‖l-clockInverse ε hε j‖ := congrArg norm hb'
    _ ≤ ‖l‖+‖clockInverse ε hε j‖ := norm_sub_le _ _
    _ ≤ ‖l‖+(1/ε)*‖j‖ := add_le_add le_rfl (clockInverse_norm ε hε j)

#print axioms compact_four_momenta
end
end UnifiedTheory.Audit.KFCausalClockFloorShearCommonDomain
