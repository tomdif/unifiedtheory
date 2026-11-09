/- Compact C1 states in charge coordinates have actual shear momentum
graphs. Every charge rotation stays in this test family. This removes the
four graph-membership assumptions for these tests, without asserting their
membership in the vacuum exponential or Hamiltonian energy domain. -/
import UnifiedTheory.Audit.KFCausalCompactFlowSlopeBound
import UnifiedTheory.Audit.KFCausalChargeShearSmoothFlow
import UnifiedTheory.Audit.KFCausalChargeShearQuarterGraphs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalChargeShearCompactDomain
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalChargeShearJointFlow
open UnifiedTheory.Audit.KFCausalChargeShearSmoothFlow
open UnifiedTheory.Audit.KFCausalChargeShearRotatedVelocity (velocity)
open UnifiedTheory.Audit.KFCausalCompactFlowSlopeBound (initialDerivative initial_memLp strong_derivative)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (JointHilbert)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearGroup shearMomentum)
open UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution (momentum_graph_iff inverse_coefficient)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow (momentumScale momentumScale_ne_zero flowEquiv flow_preserves_volume)
open UnifiedTheory.Audit.KFCausalMixedRotationMomentumGraph (linearFlow)
open UnifiedTheory.Audit.KFCausalChargeShearQuarterGraphs (reverseOutput four_graph_outputs_cancel)

structure Test where
  toFun : Space → ℂ
  smooth : ContDiff ℝ 1 toFun
  compact : HasCompactSupport toFun

instance : CoeFun Test (fun _ => Space → ℂ) := ⟨Test.toFun⟩

theorem test_memLp (f : Test) : MemLp f 2 (volume : Measure Space) :=
  f.smooth.continuous.memLp_of_hasCompactSupport f.compact

def jointState (f : Test) : JointHilbert 2 4 := (test_memLp f).toLp f
def state (f : Test) : Hilbert := chargeCoordinates.symm (jointState f)

theorem state_coe (f : Test) : chargeCoordinates (state f) =ᵐ[volume] f := by
  rw [state,LinearIsometryEquiv.apply_symm_apply]
  exact (test_memLp f).coeFn_toLp

def derivativeState (f : Test) : JointHilbert 2 4 :=
  (initial_memLp volume velocity velocity_continuous f f.smooth f.compact).toLp
    (initialDerivative velocity f)

def momentumOutput (h : ℝ) (f : Test) : Hilbert :=
  (-Complex.I*(h:ℂ)) • chargeCoordinates.symm (derivativeState f)

theorem joint_derivative (f : Test) :
    HasDerivAt (fun t => jointTransport t (jointState f)) (derivativeState f) 0 :=
  strong_derivative volume flow flow_continuous flow_zero flow_reverse velocity velocity_continuous
    flow_derivative f f.smooth f.compact (fun t => jointTransport t (jointState f))
    (fun t => jointTransport_toLp_coe t f (test_memLp f))

theorem physical_graph (h : ℝ) (hh : h ≠ 0) (f : Test) :
    (state f,momentumOutput h f) ∈ (shearMomentum h).graph := by
  apply (momentum_graph_iff shearGroup h hh _ _).mpr
  have hd := ((chargeCoordinates.symm : JointHilbert 2 4 →L[ℂ] Hilbert).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (joint_derivative f)
  have he (t : ℝ) : chargeCoordinates.symm (jointTransport t (jointState f)) =
      KFCausalTransverseShearTransport.transport t (state f) := by
    apply chargeCoordinates.injective
    rw [LinearIsometryEquiv.apply_symm_apply,physical_charge_transport]
    simp only [state,LinearIsometryEquiv.apply_symm_apply]
  change HasDerivAt (fun t => chargeCoordinates.symm (jointTransport t (jointState f)))
    (chargeCoordinates.symm (derivativeState f)) 0 at hd
  simpa only [he,momentumOutput,smul_smul,inverse_coefficient h hh,one_smul] using hd

def rotate (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f : Test) : Test where
  toFun := f ∘ flowEquiv (momentumScale h) (momentumScale_ne_zero h hh) θ
  smooth := f.smooth.comp (linearFlow (momentumScale h) (momentumScale_ne_zero h hh) θ).toContinuousLinearEquiv.contDiff
  compact := f.compact.comp_homeomorph
    (linearFlow (momentumScale h) (momentumScale_ne_zero h hh) θ).toContinuousLinearEquiv.toHomeomorph

theorem state_rotate (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f : Test) :
    KFCausalPhysicalCircleAction.action h hh θ (state f) = state (rotate h hh θ f) := by
  apply chargeCoordinates.injective
  rw [KFCausalPhysicalCircleAction.action_coordinates]
  apply Lp.ext
  filter_upwards [KFCausalMixedCircleAction.action_coe (momentumScale h) (momentumScale_ne_zero h hh) θ
      (chargeCoordinates (state f)),
    (flow_preserves_volume (momentumScale h) (momentumScale_ne_zero h hh) θ).quasiMeasurePreserving.ae
      (state_coe f),state_coe (rotate h hh θ f)] with x ha hb hc
  exact (ha.trans hb).trans hc.symm

def orbitOutput (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f : Test) : Hilbert := momentumOutput h (rotate h hh θ f)

theorem orbit_graph (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f : Test) :
    (KFCausalPhysicalCircleAction.action h hh θ (state f),orbitOutput h hh θ f) ∈ (shearMomentum h).graph := by
  rw [state_rotate]
  exact physical_graph h hh (rotate h hh θ f)

theorem four_outputs_cancel (h : ℝ) (hh : h ≠ 0) (f : Test) :
    reverseOutput h hh 0 (orbitOutput h hh 0 f) +
      reverseOutput h hh (Real.pi/2) (orbitOutput h hh (Real.pi/2) f) +
      reverseOutput h hh Real.pi (orbitOutput h hh Real.pi f) +
      reverseOutput h hh (-Real.pi/2) (orbitOutput h hh (-Real.pi/2) f) = 0 :=
  four_graph_outputs_cancel h hh (state f) _ _ _ _ f (state_coe f)
    (f.smooth.differentiable (by norm_num)) (orbit_graph h hh 0 f) (orbit_graph h hh (Real.pi/2) f)
    (orbit_graph h hh Real.pi f) (orbit_graph h hh (-Real.pi/2) f)

#print axioms test_memLp
#print axioms state_coe
#print axioms joint_derivative
#print axioms physical_graph
#print axioms state_rotate
#print axioms orbit_graph
#print axioms four_outputs_cancel
end
end UnifiedTheory.Audit.KFCausalChargeShearCompactDomain
