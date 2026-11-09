/- Every C1 compactly supported physical state satisfies the canonical and
longitudinal momentum graph identities, with all weighted and shear L2
conditions derived. This is not a core theorem for the Hamiltonian or its
exponential form domain, and no evolved-state regularity is asserted. -/
import UnifiedTheory.Audit.KFCausalClockFloorCanonicalReconstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorCompactMomentumReconstruction
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (velocity)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (response)
open UnifiedTheory.Audit.KFCausalClockFloorDifferentialMomentum
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalReconstruction
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (clockMomentum longitudinalMomentum)

theorem compact_weighted_memLp (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    MemLp (weightedDifferential ε f) 2 (volume : Measure Configuration) := by
  have hh : Continuous (fun x : Configuration => (clock ε x.1:ℂ)) := by unfold clock; fun_prop
  exact (hh.mul (differential_continuous ε hε f hf)).memLp_of_hasCompactSupport
    (differential_compact ε f hc).mul_left

theorem shear_continuous (f : Configuration → ℂ) (hf : ContDiff ℝ 1 f) :
    Continuous (shearDerivative f) := by
  have hv : Continuous (fun x : Configuration => velocity x.2) := by
    apply continuous_pi
    intro i
    unfold velocity
    split_ifs <;> fun_prop
  exact ((hf.continuous_fderiv (by norm_num)).clm_apply (continuous_const.prodMk hv)).add hf.continuous

theorem compact_shear_memLp (f : Configuration → ℂ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) : MemLp (shearDerivative f) 2 (volume : Measure Configuration) := by
  apply (shear_continuous f hf).memLp_of_hasCompactSupport
  apply hc.mono'
  intro x hx
  by_contra hn
  exact hx (by simp only [shearDerivative,fderiv_of_notMem_tsupport ℝ hn,
    ContinuousLinearMap.zero_apply,image_eq_zero_of_notMem_tsupport hn,add_zero])

theorem compact_common_reconstruction (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (f : Configuration → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    let state : Hilbert := (hf.continuous.memLp_of_hasCompactSupport hc).toLp f
    ∃ l p w d r : Hilbert,
      (state,l) ∈ (longitudinalMomentum ε hε h).graph ∧
      (state,p) ∈ (clockMomentum h).graph ∧
      w =ᵐ[volume] (fun x => (clock ε x.1:ℂ)*l x) ∧
      d =ᵐ[volume] (fun x => (-Complex.I*(h:ℂ))*shearDerivative f x) ∧
      r =ᵐ[volume] (fun x => (-Complex.I*(h:ℂ))*(response ε x.1/2:ℂ)*f x) ∧
      p = w-d+r ∧ ‖r‖ ≤ |h|/2*‖state‖ ∧ ‖p‖ ≤ ‖w‖+‖d‖+|h|/2*‖state‖ := by
  let hm : MemLp f 2 (volume : Measure Configuration) := hf.continuous.memLp_of_hasCompactSupport hc
  let hw := compact_weighted_memLp ε hε f hf hc
  let hs := compact_shear_memLp f hf hc
  let hl := differential_memLp_of_weighted ε hε f hw
  let hr := correction_memLp ε hε f hm
  let l : Hilbert := (-Complex.I*(h:ℂ)) • hl.toLp (differential ε f)
  let w : Hilbert := (-Complex.I*(h:ℂ)) • hw.toLp (weightedDifferential ε f)
  let d : Hilbert := (-Complex.I*(h:ℂ)) • hs.toLp (shearDerivative f)
  let r : Hilbert := (-Complex.I*(h:ℂ)) • hr.toLp (correction ε f)
  let p : Hilbert := w-d+r
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hlg : (hm.toLp f,l) ∈ (longitudinalMomentum ε hε h).graph :=
    longitudinal_graph_controls ε hε h hh f hm hw hd
  have hpg : (hm.toLp f,p) ∈ (clockMomentum h).graph := by
    simpa only [smul_add,smul_sub] using clock_graph_controls ε hε h hh f hm hw hs hd
  refine ⟨l,p,w,d,r,hlg,hpg,weighted_output_coe ε hε h hh f hm hw hd l hlg,?_,?_,rfl,?_,?_⟩
  · filter_upwards [Lp.coeFn_smul (-Complex.I*(h:ℂ)) (hs.toLp (shearDerivative f)),
      hs.coeFn_toLp] with x hx hy
    change ((-Complex.I*(h:ℂ)) • hs.toLp (shearDerivative f)) x = _
    rw [hx]
    simp only [Pi.smul_apply,smul_eq_mul,hy]
  · filter_upwards [Lp.coeFn_smul (-Complex.I*(h:ℂ)) (hr.toLp (correction ε f)),
      hr.coeFn_toLp] with x hx hy
    change ((-Complex.I*(h:ℂ)) • hr.toLp (correction ε f)) x = _
    rw [hx]
    simp only [Pi.smul_apply,smul_eq_mul,hy,correction,mul_assoc]
  · have he := mul_le_mul_of_nonneg_left (correction_norm ε hε f hm) (abs_nonneg h)
    simpa only [r,norm_smul,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
      ← mul_assoc,mul_one_div] using he
  · exact canonical_norm_bound ε hε h hh f hm hw hs hd p hpg

#print axioms compact_weighted_memLp
#print axioms shear_continuous
#print axioms compact_shear_memLp
#print axioms compact_common_reconstruction

end
end UnifiedTheory.Audit.KFCausalClockFloorCompactMomentumReconstruction
