/- Optional model revision: use the same mobility 1/(exp(s)+epsilon)
for both the clock and transverse source velocities. Its accumulated
transverse phase is s(t)-s(0), and its full configuration flow is complete.
This does not change the existing coupled model or prove a finite-quantum
identification. Transport time here is not Hamiltonian evolution time. -/
import UnifiedTheory.Audit.KFCausalCoupledCoordinateHomeomorph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorFlow
noncomputable section
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalCoupledCoordinateHomeomorph (flow_joint_continuous)

def clock (ε s : ℝ) : ℝ := Real.exp s + ε
def mobility (ε s : ℝ) : ℝ := (clock ε s)⁻¹

theorem clock_above_floor (ε s : ℝ) : ε < clock ε s := by
  unfold clock
  linarith [Real.exp_pos s]

theorem mobility_positive (ε s : ℝ) (hε : 0 ≤ ε) : 0 < mobility ε s := by
  unfold mobility clock
  positivity

theorem mobility_error (ε a s : ℝ) (hε : 0 ≤ ε) (ha : 0 < a) (hs : a ≤ Real.exp s) :
    |mobility ε s - Real.exp (-s)| ≤ ε/a^2 := by
  simpa only [mobility,clock,Real.exp_neg,one_div] using
    inverse_mobility_error ε a (Real.exp s) hε ha hs

def accumulated (ε : ℝ) (hε : 0 < ε) (s t : ℝ) : ℝ := logFlow ε hε s t - s

theorem accumulated_initial (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    accumulated ε hε s 0 = 0 := by
  rw [accumulated,logFlow_initial,sub_self]

theorem accumulated_derivative (ε : ℝ) (hε : 0 < ε) (s t : ℝ) :
    HasDerivAt (accumulated ε hε s) (mobility ε (logFlow ε hε s t)) t := by
  simpa only [accumulated,mobility,clock,clockFlow,one_div] using
    (logFlow_derivative ε hε s t).sub_const s

theorem accumulated_cocycle (ε : ℝ) (hε : 0 < ε) (s t u : ℝ) :
    accumulated ε hε s t + accumulated ε hε (logFlow ε hε s t) u =
      accumulated ε hε s (t+u) := by
  simp only [accumulated,logFlow_comp]
  abel

def coupledFlow (ε : ℝ) (hε : 0 < ε) (t : ℝ) (x : Configuration) : Configuration :=
  (logFlow ε hε x.1 t,flow (accumulated ε hε x.1 t) x.2)

def coupledVelocity (ε : ℝ) (x : Configuration) : Configuration :=
  (mobility ε x.1,mobility ε x.1 • velocity x.2)

theorem coupledFlow_initial (ε : ℝ) (hε : 0 < ε) (x : Configuration) :
    coupledFlow ε hε 0 x = x := by
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
  simpa only [coupledFlow,coupledVelocity,mobility,clock,clockFlow,one_div] using hs.prodMk hx

def straightening (ε : ℝ) (hε : 0 < ε) : Configuration ≃ Configuration where
  toFun x := (chart ε x.1,flow (-x.1) x.2)
  invFun y := ((chartIso ε hε).symm y.1,flow ((chartIso ε hε).symm y.1) y.2)
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
    flow (-logFlow ε hε x.1 t) (flow (accumulated ε hε x.1 t) x.2)) =
    (chart ε x.1+t,flow (-x.1) x.2)
  rw [chart_logFlow,flow_compose]
  congr 2
  unfold accumulated
  ring

def coordinateHomeomorph (ε : ℝ) (hε : 0 < ε) : Configuration ≃ₜ Configuration where
  toEquiv := straightening ε hε
  continuous_toFun :=
    ((chart_continuous ε).comp continuous_fst).prodMk
      (flow_joint_continuous.comp (continuous_fst.neg.prodMk continuous_snd))
  continuous_invFun := by
    have hs : Continuous (fun x : Configuration => (chartIso ε hε).symm x.1) :=
      (chartIso ε hε).symm.toHomeomorph.continuous.comp continuous_fst
    exact hs.prodMk (flow_joint_continuous.comp (hs.prodMk continuous_snd))

theorem coordinateHomeomorph_symm_apply (ε : ℝ) (hε : 0 < ε) (x : Configuration) :
    (coordinateHomeomorph ε hε).symm x =
      ((chartIso ε hε).symm x.1,flow ((chartIso ε hε).symm x.1) x.2) := rfl

#print axioms clock_above_floor
#print axioms mobility_positive
#print axioms mobility_error
#print axioms accumulated_initial
#print axioms accumulated_derivative
#print axioms accumulated_cocycle
#print axioms coupledFlow_initial
#print axioms coupledFlow_compose
#print axioms coupledFlow_reverse
#print axioms coupledFlow_derivative
#print axioms straightening
#print axioms straightening_flow
#print axioms coordinateHomeomorph
#print axioms coordinateHomeomorph_symm_apply

end
end UnifiedTheory.Audit.KFCausalClockFloorFlow
