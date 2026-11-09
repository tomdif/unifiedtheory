/- Complete configuration flow of the commuting tensor longitudinal
expression a(s) P_s + exp(-s) D, where D is the transverse dilation/shear.
Its parameter is longitudinal transport time, not the physical Hamiltonian
time. Identifying the full infinite quantum Hamiltonian domain is separate. -/
import UnifiedTheory.Audit.KFCausalTransverseDilationFlow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
noncomputable section
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow

def phase (ε s : ℝ) : ℝ := s-ε*Real.exp (-s)

theorem phase_derivative (ε s : ℝ) : HasDerivAt (phase ε) (1+ε*Real.exp (-s)) s := by
  have hh := (hasDerivAt_id s).sub ((((hasDerivAt_id s).neg).exp).const_mul ε)
  convert hh using 1
  change 1+ε*Real.exp (-s) = 1-ε*(Real.exp (-s)*(-1))
  ring

theorem phase_velocity (ε s : ℝ) (hε : 0 < ε) :
    (1+ε*Real.exp (-s))/(Real.exp s+ε) = Real.exp (-s) := by
  have hn : Real.exp s+ε ≠ 0 := by positivity
  rw [Real.exp_neg]
  field_simp

def accumulated (ε : ℝ) (hε : 0 < ε) (s t : ℝ) : ℝ :=
  phase ε (logFlow ε hε s t)-phase ε s

theorem accumulated_initial (ε : ℝ) (hε : 0 < ε) (s : ℝ) : accumulated ε hε s 0 = 0 := by
  rw [accumulated,logFlow_initial,sub_self]

theorem accumulated_derivative (ε : ℝ) (hε : 0 < ε) (s t : ℝ) :
    HasDerivAt (accumulated ε hε s) (Real.exp (-logFlow ε hε s t)) t := by
  have hh := ((phase_derivative ε (logFlow ε hε s t)).comp t (logFlow_derivative ε hε s t)).sub_const (phase ε s)
  convert hh using 1
  simpa only [clockFlow,one_div,div_eq_mul_inv,one_mul] using
    (phase_velocity ε (logFlow ε hε s t) hε).symm

theorem accumulated_cocycle (ε : ℝ) (hε : 0 < ε) (s t u : ℝ) :
    accumulated ε hε s t+accumulated ε hε (logFlow ε hε s t) u = accumulated ε hε s (t+u) := by
  simp only [accumulated,logFlow_comp]
  abel

abbrev Configuration := ℝ×Transverse

def coupledFlow (ε : ℝ) (hε : 0 < ε) (t : ℝ) (x : Configuration) : Configuration :=
  (logFlow ε hε x.1 t,flow (accumulated ε hε x.1 t) x.2)

def coupledVelocity (ε : ℝ) (x : Configuration) : Configuration :=
  ((Real.exp x.1+ε)⁻¹,Real.exp (-x.1) • velocity x.2)

theorem coupledFlow_initial (ε : ℝ) (hε : 0 < ε) (x : Configuration) : coupledFlow ε hε 0 x = x := by
  simp [coupledFlow,logFlow_initial,accumulated_initial,flow_initial]

theorem coupledFlow_compose (ε : ℝ) (hε : 0 < ε) (t u : ℝ) (x : Configuration) :
    coupledFlow ε hε u (coupledFlow ε hε t x) = coupledFlow ε hε (t+u) x := by
  simp only [coupledFlow,logFlow_comp,flow_compose,accumulated_cocycle]

theorem coupledFlow_reverse (ε : ℝ) (hε : 0 < ε) (t : ℝ) (x : Configuration) :
    coupledFlow ε hε (-t) (coupledFlow ε hε t x) = x := by
  rw [coupledFlow_compose,add_neg_cancel,coupledFlow_initial]

theorem coupledFlow_derivative (ε : ℝ) (hε : 0 < ε) (t : ℝ) (x : Configuration) :
    HasDerivAt (fun u => coupledFlow ε hε u x) (coupledVelocity ε (coupledFlow ε hε t x)) t := by
  have hx := (flow_derivative (accumulated ε hε x.1 t) x.2).scomp t
    (accumulated_derivative ε hε x.1 t)
  have hs := logFlow_derivative ε hε x.1 t
  simpa only [coupledFlow,coupledVelocity,clockFlow,one_div] using hs.prodMk hx

def straightening (ε : ℝ) (hε : 0 < ε) : Configuration ≃ Configuration where
  toFun x := (chart ε x.1,flow (-phase ε x.1) x.2)
  invFun y := ((chartIso ε hε).symm y.1,flow (phase ε ((chartIso ε hε).symm y.1)) y.2)
  left_inv x := by
    have hi := (chartIso ε hε).symm_apply_apply x.1
    change (chartIso ε hε).symm (chart ε x.1) = x.1 at hi
    simp only [hi,flow_compose,neg_add_cancel,flow_initial,Prod.mk.eta]
  right_inv y := by
    have hi := (chartIso ε hε).apply_symm_apply y.1
    change chart ε ((chartIso ε hε).symm y.1) = y.1 at hi
    simp only [hi,flow_compose,add_neg_cancel,flow_initial,Prod.mk.eta]

theorem straightening_flow (ε : ℝ) (hε : 0 < ε) (t : ℝ) (x : Configuration) :
    straightening ε hε (coupledFlow ε hε t x) =
      ((straightening ε hε x).1+t,(straightening ε hε x).2) := by
  change (chart ε (logFlow ε hε x.1 t),
    flow (-phase ε (logFlow ε hε x.1 t)) (flow (accumulated ε hε x.1 t) x.2)) =
    (chart ε x.1+t,flow (-phase ε x.1) x.2)
  rw [chart_logFlow,flow_compose]
  congr 2
  unfold accumulated
  ring

#print axioms phase_velocity
#print axioms accumulated_derivative
#print axioms coupledFlow_compose
#print axioms coupledFlow_reverse
#print axioms coupledFlow_derivative
#print axioms straightening
#print axioms straightening_flow

end
end UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
