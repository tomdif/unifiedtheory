/- A noncompact sufficient criterion for the actual physical shear graph:
the state, its canonical clock derivative and its shear differential are
in L2. Domain membership is derived through the actual shear coordinates;
it is not added as a hypothesis. Gaussian applications still require their
specific differential integrability estimates. -/
import UnifiedTheory.Audit.KFCausalTransverseShearDifferential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalTransverseShearDifferentialDomain
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (flow velocity flow_derivative)
open UnifiedTheory.Audit.KFCausalTransverseShearCoordinates (coordinates shearChart)
open UnifiedTheory.Audit.KFCausalTransverseShearDifferential
  (inverseFunction inverseFunction_contDiff inverse_toLp_coe graph_representative)
open UnifiedTheory.Audit.KFCausalCanonicalClockDerivative (clockDerivative clock_derivative_graph)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalReconstruction (shearDerivative)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum domain_of_clock_domains)

theorem inverse_memLp (f : Configuration → ℂ) (hf : MemLp f 2 (volume : Measure Configuration)) :
    MemLp (inverseFunction f) 2 (volume : Measure Configuration) :=
  (memLp_congr_ae (inverse_toLp_coe f hf)).mp (Lp.memLp (coordinates.symm (hf.toLp f)))

theorem inverse_clock_derivative (f : Configuration → ℂ) (hf : ContDiff ℝ 1 f) (x : Configuration) :
    clockDerivative (inverseFunction f) x =
      inverseFunction (clockDerivative f+shearDerivative f) x := by
  have hp := (hasDerivAt_id x.1).prodMk (flow_derivative x.1 x.2)
  have hq := ((hf.differentiable (by norm_num)) (shearChart.symm x)).hasFDerivAt.comp_hasDerivAt x.1 hp
  have hd := (Real.hasDerivAt_exp x.1).ofReal_comp.mul hq
  have hc := (((inverseFunction_contDiff f hf).differentiable (by norm_num)) x).hasFDerivAt.comp_hasDerivAt x.1
    ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))
  have he : clockDerivative (inverseFunction f) x =
      (Real.exp x.1:ℂ)*f (shearChart.symm x)+
        (Real.exp x.1:ℂ)*(fderiv ℝ f (shearChart.symm x)) ((1,velocity (flow x.1 x.2)):Configuration) :=
    hc.unique hd
  rw [he]
  have hv : ((1,velocity (flow x.1 x.2)):Configuration) =
      ((1,0):Configuration)+((0,velocity (flow x.1 x.2)):Configuration) := by simp
  rw [hv,map_add]
  simp only [inverseFunction,Pi.add_apply,clockDerivative,shearDerivative]
  rw [show (shearChart.symm x).2 = flow x.1 x.2 from rfl]
  ring

theorem inverse_clock_memLp (f : Configuration → ℂ) (hf : ContDiff ℝ 1 f)
    (hq : MemLp (clockDerivative f) 2 (volume : Measure Configuration))
    (hs : MemLp (shearDerivative f) 2 (volume : Measure Configuration)) :
    MemLp (clockDerivative (inverseFunction f)) 2 (volume : Measure Configuration) := by
  rw [funext (inverse_clock_derivative f hf)]
  exact inverse_memLp _ (hq.add hs)

theorem domain_of_differentials (h : ℝ) (hh : h ≠ 0) (f : Configuration → ℂ)
    (hf : MemLp f 2 (volume : Measure Configuration)) (hc : ContDiff ℝ 1 f)
    (hq : MemLp (clockDerivative f) 2 (volume : Measure Configuration))
    (hs : MemLp (shearDerivative f) 2 (volume : Measure Configuration)) :
    hf.toLp f ∈ (shearMomentum h).domain := by
  have hi := inverse_memLp f hf
  have he : coordinates.symm (hf.toLp f) = hi.toLp (inverseFunction f) :=
    Lp.ext ((inverse_toLp_coe f hf).trans hi.coeFn_toLp.symm)
  apply domain_of_clock_domains h hh (hf.toLp f)
    (LinearPMap.mem_domain_of_mem_graph (clock_derivative_graph h hh f hf hq (hc.differentiable (by norm_num))))
  rw [he]
  exact LinearPMap.mem_domain_of_mem_graph (clock_derivative_graph h hh (inverseFunction f) hi
    (inverse_clock_memLp f hc hq hs) ((inverseFunction_contDiff f hc).differentiable (by norm_num)))

theorem graph_of_differentials (h : ℝ) (hh : h ≠ 0) (f : Configuration → ℂ)
    (hf : MemLp f 2 (volume : Measure Configuration)) (hc : ContDiff ℝ 1 f)
    (hq : MemLp (clockDerivative f) 2 (volume : Measure Configuration))
    (hs : MemLp (shearDerivative f) 2 (volume : Measure Configuration)) :
    (hf.toLp f,(-Complex.I*(h:ℂ)) • hs.toLp (shearDerivative f)) ∈ (shearMomentum h).graph := by
  let v : (shearMomentum h).domain := ⟨hf.toLp f,domain_of_differentials h hh f hf hc hq hs⟩
  have hv := (shearMomentum h).mem_graph v
  have he : shearMomentum h v = (-Complex.I*(h:ℂ)) • hs.toLp (shearDerivative f) := by
    apply Lp.ext
    filter_upwards [graph_representative h hh f hf (hc.differentiable (by norm_num)) _ hv,
      Lp.coeFn_smul (-Complex.I*(h:ℂ)) (hs.toLp (shearDerivative f)),hs.coeFn_toLp] with x ha hb hd
    rw [ha,hb]
    simp only [Pi.smul_apply,smul_eq_mul,hd]
  rw [he] at hv
  exact hv

#print axioms inverse_memLp
#print axioms inverse_clock_derivative
#print axioms inverse_clock_memLp
#print axioms domain_of_differentials
#print axioms graph_of_differentials
end
end UnifiedTheory.Audit.KFCausalTransverseShearDifferentialDomain
