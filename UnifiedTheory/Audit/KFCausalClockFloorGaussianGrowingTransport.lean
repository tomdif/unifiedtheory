/- Actual complex clock-Gaussian multipliers, with their full natural
first-factor transports. The physical clock chart is retained, and the
adjoint reverses the vertical center. No operator-domain preservation of
the growing Hamiltonian is asserted at this stage. -/
import UnifiedTheory.Audit.KFCausalAnalyticClockSecondTransport

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorGaussianGrowingTransport
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalRegularizedLongitudinalChart (chart chart_continuous)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalAnalyticClockSecondTransport (firstShift)

def gaussian (a : ℝ) (q : ℂ) : ℂ := Complex.exp (-(a:ℂ)*q^2)
def centered (a y : ℝ) (q : ℂ) : ℂ := gaussian a (q+(y:ℂ)*Complex.I)
def line (ε a y s : ℝ) : ℂ := centered a y (chart ε s:ℂ)
def stripCap (a h y : ℝ) : ℝ := Real.exp (a*(|y|+|h|)^2)

theorem gaussian_norm (a : ℝ) (q : ℂ) :
    ‖gaussian a q‖=Real.exp (a*q.im^2-a*q.re^2) := by
  rw [gaussian,Complex.norm_exp]
  congr 1
  simp [pow_two,Complex.mul_re]
  ring

theorem centered_analytic (a y : ℝ) (q : ℂ) : AnalyticAt ℂ (centered a y) q := by
  unfold centered gaussian
  fun_prop

theorem centered_bound (a : ℝ) (ha : 0 ≤ a) (h y : ℝ) (q : ℂ) (hq : |q.im| ≤ |h|) :
    ‖centered a y q‖ ≤ stripCap a h y := by
  have hi : |q.im+y| ≤ |y|+|h| :=
    (abs_add_le _ _).trans (by linarith)
  have hs := pow_le_pow_left₀ (abs_nonneg (q.im+y)) hi 2
  rw [sq_abs] at hs
  rw [centered,gaussian_norm]
  apply Real.exp_le_exp.mpr
  simp only [Complex.add_im,Complex.add_re,Complex.mul_im,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    mul_zero,mul_one,sub_zero,add_zero]
  nlinarith [mul_le_mul_of_nonneg_left hs ha,mul_nonneg ha (sq_nonneg q.re)]

private theorem line_continuous (ε a y : ℝ) : Continuous (line ε a y) :=
  (continuous_iff_continuousAt.mpr (fun q => (centered_analytic a y q).continuousAt)).comp
    (Complex.continuous_ofReal.comp (chart_continuous ε))

private theorem line_bound (ε a : ℝ) (ha : 0 ≤ a) (y s : ℝ) :
    ‖line ε a y s‖ ≤ Real.exp (a*y^2) := by
  simpa only [stripCap,Complex.ofReal_im,abs_zero,add_zero,sq_abs] using
    centered_bound a ha 0 y (chart ε s:ℂ) (by simp)

def action (ε a : ℝ) (ha : 0 ≤ a) (y : ℝ) : Hilbert →L[ℂ] Hilbert :=
  KFCausalBoundedClockCharge.multiplier (line ε a y) (line_continuous ε a y).measurable
    (Real.exp (a*y^2)) (Real.exp_pos _).le (line_bound ε a ha y)

theorem action_coe (ε a : ℝ) (ha : 0 ≤ a) (y : ℝ) (f : Hilbert) :
    action ε a ha y f =ᵐ[volume] fun x => line ε a y x.1*f x :=
  KFCausalBoundedClockCharge.multiplier_coe _ _ _ _ _ f

theorem action_coordinates (ε a : ℝ) (ha : 0 ≤ a) (y : ℝ) (f : Hilbert) :
    chargeCoordinates (action ε a ha y f) =ᵐ[volume]
      fun x => line ε a y (x (.inr 0))*chargeCoordinates f x :=
  KFCausalBoundedClockCharge.multiplier_coordinates _ _ _ _ _ f

theorem action_norm (ε a : ℝ) (ha : 0 ≤ a) (y : ℝ) (f : Hilbert) :
    ‖action ε a ha y f‖ ≤ Real.exp (a*y^2)*‖f‖ :=
  KFCausalBoundedClockCharge.multiplier_norm _ _ _ _ _ f

theorem action_charge (ε a : ℝ) (ha : 0 ≤ a) (y h : ℝ) (hh : h ≠ 0)
    (θ : ℝ) (f : Hilbert) :
    action ε a ha y (KFCausalPhysicalCircleAction.action h hh θ f)=
      KFCausalPhysicalCircleAction.action h hh θ (action ε a ha y f) :=
  KFCausalBoundedClockCharge.multiplier_charge _ _ _ _ _ h hh θ f

private theorem line_conj (ε a y s : ℝ) :
    starRingEnd ℂ (line ε a y s)=line ε a (-y) s := by
  unfold line centered gaussian
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul,map_neg,map_pow,map_add,Complex.conj_ofReal,Complex.conj_I,
    Complex.ofReal_neg]
  ring

theorem action_pairing (ε a : ℝ) (ha : 0 ≤ a) (y : ℝ) (f g : Hilbert) :
    inner ℂ (action ε a ha y f) g=inner ℂ f (action ε a ha (-y) g) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [action_coe ε a ha y f,action_coe ε a ha (-y) g] with x hf hg
  rw [hf,hg]
  change inner ℂ (line ε a y x.1 • f x) (g x)=inner ℂ (f x) (line ε a (-y) x.1 • g x)
  rw [inner_smul_left,inner_smul_right,line_conj]

private theorem analytic_operator_eq (ε a : ℝ) (ha : 0 ≤ a) (h y r : ℝ) (hr : |r| ≤ |h|)
    (f : Hilbert) :
    KFCausalAnalyticClockSecondTransport.operator (centered a y) h (stripCap a h y)
      (fun q _ => centered_analytic a y q) (Real.exp_pos _).le
      (centered_bound a ha h y) ε r hr f=action ε a ha (y+r) f := by
  apply Lp.ext
  filter_upwards [KFCausalAnalyticClockSecondTransport.operator_coe (centered a y) h
    (stripCap a h y) (fun q _ => centered_analytic a y q) (Real.exp_pos _).le
    (centered_bound a ha h y) ε r hr f,action_coe ε a ha (y+r) f] with x h1 h2
  rw [h1,h2]
  unfold KFCausalAnalyticClockSecondTransport.line line centered
  congr 2
  push_cast
  ring

theorem forward_graph (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a)
    (h : ℝ) (hh : h ≠ 0) (y : ℝ) (i : Fin 8) (f g : Hilbert)
    (hfg : (f,g) ∈ (energyFactor ε hε h modelDirections pointField i).graph) :
    (action ε a ha y f,action ε a ha (y+firstShift h i) g) ∈
      (energyFactor ε hε h modelDirections pointField i).graph := by
  have hg := KFCausalAnalyticClockSecondTransport.forward_graph (centered a y) h
    (stripCap a h y) (fun q _ => centered_analytic a y q) (Real.exp_pos _).le
    (centered_bound a ha h y) ε hε hh i f g hfg
  rw [analytic_operator_eq,analytic_operator_eq,add_zero] at hg
  exact hg

#print axioms gaussian_norm
#print axioms centered_analytic
#print axioms centered_bound
#print axioms action_coe
#print axioms action_coordinates
#print axioms action_norm
#print axioms action_charge
#print axioms action_pairing
#print axioms forward_graph
end
end UnifiedTheory.Audit.KFCausalClockFloorGaussianGrowingTransport
