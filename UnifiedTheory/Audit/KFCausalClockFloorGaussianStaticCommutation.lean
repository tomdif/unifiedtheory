/- Centered complex clock Gaussians commute with the actual maximal static
operator. The multiplier is transported through the genuine complementary
Fourier representation; the original completed static Hamiltonian is then
identified using its proved equality with that maximal operator. -/
import UnifiedTheory.Audit.KFCausalClockFloorGaussianGrowingApproximation
import UnifiedTheory.Audit.KFCausalClockFloorDualClock
import UnifiedTheory.Audit.KFCausalClockFloorStaticHamiltonian

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGaussianStaticCommutation
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalChargeTransverseSplit (dualPhysical)
open KFCausalClockFloorGaussianGrowingTransport (action line)
open KFCausalClockFloorGaussianGrowingApproximation (action_tendsto)
open KFCausalClockFloorStaticOperator (operator graph_iff)
open KFCausalClockFloorDualClock (dualPhysical_multiplier dualJointMultiplier dualJointMultiplier_coe)
open KFCausalBoundedLpMultiplier (normalized_bound)

private theorem bounded_dual_coe (w : ℝ → ℂ) (hw : Measurable w)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ s, ‖w s‖ ≤ B) (f : Hilbert) :
    dualPhysical (KFCausalBoundedClockCharge.multiplier w hw B hB hb f) =ᵐ[volume]
      fun x => w (x (.inr 0))*(dualPhysical f) x := by
  rw [KFCausalBoundedClockCharge.multiplier_normalized,map_smul,dualPhysical_multiplier]
  filter_upwards [Lp.coeFn_smul ((B+1:ℝ):ℂ)
    (dualJointMultiplier (fun s => w s/(B+1:ℝ)) (hw.div_const _)
      (normalized_bound w B hB hb) (dualPhysical f)),
    dualJointMultiplier_coe (fun s => w s/(B+1:ℝ)) (hw.div_const _)
      (normalized_bound w B hB hb) (dualPhysical f)] with x hs hx
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,hx]
  have hn : ((B+1:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  field_simp

theorem gaussian_dual_coe (ε a : ℝ) (ha : 0 ≤ a) (y : ℝ) (f : Hilbert) :
    dualPhysical (action ε a ha y f) =ᵐ[volume]
      fun x => line ε a y (x (.inr 0))*(dualPhysical f) x := by
  exact bounded_dual_coe _ _ _ _ _ f

theorem static_graph (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a)
    (h y : ℝ) (f z : Hilbert) (hfg : (f,z) ∈ (operator ε hε h).graph) :
    (action ε a ha y f,action ε a ha y z) ∈ (operator ε hε h).graph := by
  apply (graph_iff ε hε h _ _).mpr
  filter_upwards [(graph_iff ε hε h f z).mp hfg,
    gaussian_dual_coe ε a ha y f,gaussian_dual_coe ε a ha y z] with x hx hf hz
  rw [hz,hf,hx]
  ring

theorem static_domain (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a)
    (h y : ℝ) (f : (operator ε hε h).domain) :
    action ε a ha y (f:Hilbert) ∈ (operator ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (static_graph ε hε a ha h y (f:Hilbert) _ ((operator ε hε h).mem_graph f))

theorem hamiltonian_graph (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a)
    (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (y m g k t : ℝ)
    (f z : Hilbert)
    (hfg : (f,z) ∈ (KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh hb m g k t).graph) :
    (action ε a ha y f,action ε a ha y z) ∈
      (KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh hb m g k t).graph := by
  rw [KFCausalClockFloorStaticHamiltonian.hamiltonian_eq_operator] at hfg ⊢
  exact static_graph ε hε a ha h y f z hfg

theorem static_graph_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (ε : ℝ) (hε : 0 < ε) (h y : ℝ) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hz : Tendsto a l (𝓝 0)) (f : (operator ε hε h).domain) :
    Tendsto (fun i => (action ε (a i) (ha i) y (f:Hilbert),
      action ε (a i) (ha i) y (operator ε hε h f))) l
        (𝓝 ((f:Hilbert),operator ε hε h f)) :=
  (action_tendsto ε y a ha hz (f:Hilbert)).prodMk_nhds
    (action_tendsto ε y a ha hz (operator ε hε h f))

#print axioms gaussian_dual_coe
#print axioms static_graph
#print axioms static_domain
#print axioms hamiltonian_graph
#print axioms static_graph_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorGaussianStaticCommutation
