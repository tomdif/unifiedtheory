/- Compact C1 physical states belong to the actual shear momentum domain.
The graph output is identified with the symmetrically ordered transverse
expression, including its half-density correction. -/
import UnifiedTheory.Audit.KFCausalTransverseShearMomentum
import UnifiedTheory.Audit.KFCausalClockFloorCompactMomentumReconstruction
import UnifiedTheory.Audit.KFCausalLpDerivativeRepresentative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalTransverseShearDifferential
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalTransverseShearCoordinates
open UnifiedTheory.Audit.KFCausalTransverseShearTransport
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum
open UnifiedTheory.Audit.KFCausalCanonicalClockDerivative
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalReconstruction (shearDerivative)
open UnifiedTheory.Audit.KFCausalClockFloorCompactMomentumReconstruction (compact_shear_memLp)
open UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution (momentum_graph_iff inverse_coefficient)

def inverseFunction (f : Configuration → ℂ) (x : Configuration) : ℂ :=
  (Real.exp x.1:ℂ)*f (shearChart.symm x)

theorem inverseFunction_contDiff (f : Configuration → ℂ) (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (inverseFunction f) := by
  have hg : ContDiff ℝ 1 (fun x : Configuration => flow x.1 x.2) := by
    apply contDiff_pi.mpr
    intro i
    simp only [flow]
    split_ifs <;> unfold scale <;> fun_prop
  have he : ContDiff ℝ 1 (fun x : Configuration => (Real.exp x.1:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp contDiff_fst)
  exact he.mul (hf.comp (contDiff_fst.prodMk hg))

theorem inverseFunction_compact (f : Configuration → ℂ) (hc : HasCompactSupport f) :
    HasCompactSupport (inverseFunction f) := (hc.comp_homeomorph shearChart.symm).mul_left

theorem inverse_toLp_coe (f : Configuration → ℂ) (hf : MemLp f 2) :
    coordinates.symm (hf.toLp f) =ᵐ[volume] inverseFunction f := by
  filter_upwards [coordinates_inverse_coe (hf.toLp f),shearChart_inverse_quasiMeasurePreserving.ae hf.coeFn_toLp]
    with x hx hf'
  rw [hx,hf']
  rfl

theorem compact_domain (h : ℝ) (hh : h ≠ 0) (f : Configuration → ℂ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (hf.continuous.memLp_of_hasCompactSupport hc).toLp f ∈ (shearMomentum h).domain := by
  let hm : MemLp f 2 (volume : Measure Configuration) := hf.continuous.memLp_of_hasCompactSupport hc
  have hg := inverseFunction_contDiff f hf
  have hgc := inverseFunction_compact f hc
  let hgm : MemLp (inverseFunction f) 2 (volume : Measure Configuration) :=
    hg.continuous.memLp_of_hasCompactSupport hgc
  have he : coordinates.symm (hm.toLp f) = hgm.toLp (inverseFunction f) :=
    Lp.ext ((inverse_toLp_coe f hm).trans hgm.coeFn_toLp.symm)
  apply domain_of_clock_domains h hh (hm.toLp f) (compact_clock_domain h hh f hf hc)
  rw [he]
  exact compact_clock_domain h hh (inverseFunction f) hg hgc

theorem expression_derivative (f : Configuration → ℂ) (x : Configuration)
    (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun t : ℝ => (Real.exp t:ℂ)*f (shearFlow t x)) (shearDerivative f x) 0 := by
  have hp : HasDerivAt (fun t : ℝ => shearFlow t x) ((0,velocity x.2):Configuration) 0 := by
    simpa only [shearFlow,flow_initial] using (hasDerivAt_const 0 x.1).prodMk (flow_derivative 0 x.2)
  have hx : shearFlow 0 x = x := by change (x.1,flow 0 x.2) = x; rw [flow_initial]
  have hfx : HasFDerivAt f (fderiv ℝ f x) (shearFlow 0 x) := by rw [hx]; exact hf.hasFDerivAt
  have hd := (Real.hasDerivAt_exp 0).ofReal_comp.mul (hfx.comp_hasDerivAt 0 hp)
  simpa only [Function.comp_apply,Real.exp_zero,Complex.ofReal_one,one_mul,hx,shearDerivative,add_comm] using hd

theorem graph_representative (h : ℝ) (hh : h ≠ 0) (f : Configuration → ℂ)
    (hf : MemLp f 2 (volume : Measure Configuration)) (hs : Differentiable ℝ f)
    (g : Hilbert) (hfg : (hf.toLp f,g) ∈ (shearMomentum h).graph) :
    g =ᵐ[volume] fun x => (-Complex.I*(h:ℂ))*shearDerivative f x := by
  have hd := (momentum_graph_iff shearGroup h hh _ _).mp hfg
  have he := KFCausalLpDerivativeRepresentative.derivative_representative
    (fun t => transport t (hf.toLp f)) ((Complex.I/(h:ℂ)) • g)
    (fun t x => (Real.exp t:ℂ)*f (shearFlow t x)) (shearDerivative f)
    (fun t => transport_toLp_coe t f hf) hd (fun x => expression_derivative f x (hs x))
  filter_upwards [he,Lp.coeFn_smul (Complex.I/(h:ℂ)) g] with x hx hg
  rw [hg] at hx
  simp only [Pi.smul_apply,smul_eq_mul] at hx
  calc
    g x = ((-Complex.I*(h:ℂ))*(Complex.I/(h:ℂ)))*g x := by
      rw [mul_comm (-Complex.I*(h:ℂ)),inverse_coefficient h hh,one_mul]
    _ = (-Complex.I*(h:ℂ))*shearDerivative f x := by rw [mul_assoc,hx]

theorem compact_graph (h : ℝ) (hh : h ≠ 0) (f : Configuration → ℂ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ((hf.continuous.memLp_of_hasCompactSupport hc).toLp f,
      (-Complex.I*(h:ℂ)) • (compact_shear_memLp f hf hc).toLp (shearDerivative f)) ∈
      (shearMomentum h).graph := by
  let hm : MemLp f 2 (volume : Measure Configuration) := hf.continuous.memLp_of_hasCompactSupport hc
  let v : (shearMomentum h).domain := ⟨hm.toLp f,compact_domain h hh f hf hc⟩
  have hv := (shearMomentum h).mem_graph v
  have he : shearMomentum h v = (-Complex.I*(h:ℂ)) • (compact_shear_memLp f hf hc).toLp (shearDerivative f) := by
    apply Lp.ext
    filter_upwards [graph_representative h hh f hm (hf.differentiable (by norm_num)) _ hv,
      Lp.coeFn_smul (-Complex.I*(h:ℂ)) ((compact_shear_memLp f hf hc).toLp (shearDerivative f)),
      (compact_shear_memLp f hf hc).coeFn_toLp] with x hx hy hz
    rw [hx,hy]
    simp only [Pi.smul_apply,smul_eq_mul,hz]
  rw [he] at hv
  exact hv

#print axioms inverseFunction_contDiff
#print axioms inverseFunction_compact
#print axioms inverse_toLp_coe
#print axioms compact_domain
#print axioms expression_derivative
#print axioms graph_representative
#print axioms compact_graph
end
end UnifiedTheory.Audit.KFCausalTransverseShearDifferential
