/- The actual straightening bijection is a homeomorphism. Its positive
half-density combines the clock Jacobian and transverse flow determinant. -/
import UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoupledCoordinateHomeomorph
noncomputable section
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow

theorem flow_joint_continuous : Continuous (fun z : ℝ×Transverse => flow z.1 z.2) := by
  apply continuous_pi
  intro i
  by_cases hi : i = 4
  · simp only [flow,hi,ite_true,scale]
    fun_prop
  · simp only [flow,hi,ite_false,scale]
    fun_prop

theorem phase_continuous (ε : ℝ) : Continuous (phase ε) :=
  continuous_iff_continuousAt.mpr (fun s => (phase_derivative ε s).continuousAt)

def coordinateHomeomorph (ε : ℝ) (hε : 0 < ε) : Configuration ≃ₜ Configuration where
  toEquiv := straightening ε hε
  continuous_toFun := by
    have hp : Continuous (fun x : Configuration => (-phase ε x.1,x.2)) :=
      ((phase_continuous ε).comp continuous_fst).neg.prodMk continuous_snd
    exact ((chart_continuous ε).comp continuous_fst).prodMk (flow_joint_continuous.comp hp)
  continuous_invFun := by
    have hs : Continuous (fun x : Configuration => (chartIso ε hε).symm x.1) :=
      (chartIso ε hε).symm.toHomeomorph.continuous.comp continuous_fst
    exact hs.prodMk (flow_joint_continuous.comp (((phase_continuous ε).comp hs).prodMk continuous_snd))

theorem coordinateHomeomorph_apply (ε : ℝ) (hε : 0 < ε) (x : Configuration) :
    coordinateHomeomorph ε hε x = (chart ε x.1,flow (-phase ε x.1) x.2) := rfl

theorem coordinateHomeomorph_symm_apply (ε : ℝ) (hε : 0 < ε) (x : Configuration) :
    (coordinateHomeomorph ε hε).symm x =
      ((chartIso ε hε).symm x.1,flow (phase ε ((chartIso ε hε).symm x.1)) x.2) := rfl

def amplitude (ε s : ℝ) : ℝ := Real.sqrt (Real.exp s+ε)*Real.exp (-phase ε s)

theorem amplitude_continuous (ε : ℝ) : Continuous (amplitude ε) := by
  unfold amplitude
  have hp := phase_continuous ε
  fun_prop

theorem amplitude_positive (ε s : ℝ) (hε : 0 < ε) : 0 < amplitude ε s := by
  unfold amplitude
  positivity

theorem amplitude_square (ε s : ℝ) (hε : 0 < ε) :
    (amplitude ε s)^2 = (Real.exp s+ε)*Real.exp (2*(-phase ε s)) := by
  rw [amplitude,mul_pow,Real.sq_sqrt (by positivity : 0 ≤ Real.exp s+ε),← Real.exp_nat_mul]
  norm_num

#print axioms flow_joint_continuous
#print axioms coordinateHomeomorph
#print axioms amplitude_positive
#print axioms amplitude_square

end
end UnifiedTheory.Audit.KFCausalCoupledCoordinateHomeomorph
