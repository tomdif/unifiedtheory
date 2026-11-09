/- The already shifted inverse-clock, moment and correction coefficients
intertwine the full half-exponential graph with their twice-shifted values.
The proof uses bounded analytic families and the actual Gaussian graph core. -/
import UnifiedTheory.Audit.KFCausalSecondShiftClockBounds
import UnifiedTheory.Audit.KFCausalCoherentMomentumOutputReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 900000

namespace UnifiedTheory.Audit.KFCausalSecondShiftClockGraphs
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalSecondShiftClockBounds
open KFCausalClockFloorExponential (longitudinalExponential)
open KFCausalClockFloorShiftedDefect (shiftedDefect)
open KFCausalClockFloorShiftedDefectPhysical (shiftedDefect_physical_coe physicalSymbol)
open KFCausalShiftedClockMomentOperator (inverseOperator momentOperator momentOperator_coe momentMultiplier)
open KFCausalCoherentMomentumOutputReduction (inverseOperator_eq)
open KFCausalGaussianVacuumSquare (original_strip double_strip)
open KFCausalClockFloorOrderedMomentumCommutator (correction)

private theorem zero_radius (ε : ℝ) (hε : 0 < ε) : |(0:ℝ)| ≤ radius ε := by
  simp only [abs_zero]
  unfold radius
  positivity

variable (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ Real.pi*ε/3)
local notation "hb₀" => original_strip ε h hε hb
local notation "hb₂" => double_strip ε h hb
local notation "h0" => zero_radius ε hε
local notation "hs" => shift_bound ε h hb

def defectFamily (y : ℝ) (hy : |y| ≤ radius ε) : Hilbert →L[ℂ] Hilbert :=
  KFCausalAnalyticClockFamily.operator (defect ε h) (radius ε) 2
    (defect_analytic ε h hε hb) (by norm_num) (defect_bound ε h hε hb) ε hε y hy

def momentFamily (a : ℝ) (ha : 0 < a) (y : ℝ) (hy : |y| ≤ radius ε) : Hilbert →L[ℂ] Hilbert :=
  KFCausalAnalyticClockFamily.operator (moment a h) (radius ε)
    (KFCausalGaussianClockMoment.bound a (Real.pi*ε/3))
    (fun q _ => moment_analytic a h q) (KFCausalGaussianClockMoment.bound_positive a _ ha).le
    (moment_bound_strip ε a h ha hb) ε hε y hy

theorem defect_zero : defectFamily ε h hε hb 0 h0 = shiftedDefect ε hε h hb₀ := by
  apply KFCausalAnalyticClockFamily.operator_eq
  intro f
  filter_upwards [shiftedDefect_physical_coe ε hε h hb₀ f] with x hx
  simpa only [defect,physicalSymbol,Complex.ofReal_zero,zero_mul,add_zero] using hx

theorem defect_second : defectFamily ε h hε hb (-h/2) hs = shiftedDefect ε hε (2*h) hb₂ := by
  apply KFCausalAnalyticClockFamily.operator_eq
  intro f
  filter_upwards [shiftedDefect_physical_coe ε hε (2*h) hb₂ f] with x hx
  rw [hx]
  unfold defect physicalSymbol
  congr 2
  push_cast
  ring

theorem moment_zero (a : ℝ) (ha : 0 < a) :
    momentFamily ε h hε hb a ha 0 h0 = momentOperator ε a (-h/2) ha := by
  apply KFCausalAnalyticClockFamily.operator_eq
  intro f
  filter_upwards [momentOperator_coe ε a (-h/2) ha f] with x hx
  simpa only [moment,momentMultiplier,KFCausalClockFloorRelativeShift.argument,
    Complex.ofReal_zero,zero_mul,add_zero] using hx

theorem moment_second (a : ℝ) (ha : 0 < a) :
    momentFamily ε h hε hb a ha (-h/2) hs = momentOperator ε a (-(2*h)/2) ha := by
  apply KFCausalAnalyticClockFamily.operator_eq
  intro f
  filter_upwards [momentOperator_coe ε a (-(2*h)/2) ha f] with x hx
  rw [hx]
  unfold moment momentMultiplier KFCausalClockFloorRelativeShift.argument
  have he : ((KFCausalRegularizedLongitudinalChart.chart ε x.1:ℂ)+(-h/2:ℝ)*Complex.I)+
      (-h/2:ℝ)*Complex.I =
        (KFCausalRegularizedLongitudinalChart.chart ε x.1:ℂ)+(-(2*h)/2:ℝ)*Complex.I := by
    push_cast
    ring
  rw [he]

theorem defect_graph (f g : Hilbert)
    (hfg : (f,g) ∈ (longitudinalExponential ε hε h (1/2)).graph) :
    (shiftedDefect ε hε h hb₀ f,shiftedDefect ε hε (2*h) hb₂ g) ∈
      (longitudinalExponential ε hε h (1/2)).graph := by
  have hg := KFCausalAnalyticClockFamily.graph (defect ε h) (radius ε) 2
    (defect_analytic ε h hε hb) (by norm_num) (defect_bound ε h hε hb) ε hε h h0 hs f g hfg
  change (defectFamily ε h hε hb 0 h0 f,defectFamily ε h hε hb (-h/2) hs g) ∈ _ at hg
  rwa [defect_zero,defect_second] at hg

theorem inverse_graph (f g : Hilbert)
    (hfg : (f,g) ∈ (longitudinalExponential ε hε h (1/2)).graph) :
    (inverseOperator ε (-h/2) hε (KFCausalClockFloorShiftedOutput.shift_bound ε h hb₀) f,
      inverseOperator ε (-(2*h)/2) hε (KFCausalClockFloorShiftedOutput.shift_bound ε (2*h) hb₂) g) ∈
        (longitudinalExponential ε hε h (1/2)).graph := by
  rw [inverseOperator_eq ε h hε hb₀,inverseOperator_eq ε (2*h) hε hb₂]
  exact (longitudinalExponential ε hε h (1/2)).graph.smul_mem (1/(ε:ℂ))
    (defect_graph ε h hε hb f g hfg)

include hb in
theorem moment_graph (a : ℝ) (ha : 0 < a) (f g : Hilbert)
    (hfg : (f,g) ∈ (longitudinalExponential ε hε h (1/2)).graph) :
    (momentOperator ε a (-h/2) ha f,momentOperator ε a (-(2*h)/2) ha g) ∈
      (longitudinalExponential ε hε h (1/2)).graph := by
  have hg := KFCausalAnalyticClockFamily.graph (moment a h) (radius ε)
    (KFCausalGaussianClockMoment.bound a (Real.pi*ε/3))
    (fun q _ => moment_analytic a h q) (KFCausalGaussianClockMoment.bound_positive a _ ha).le
    (moment_bound_strip ε a h ha hb) ε hε h h0 hs f g hfg
  change (momentFamily ε h hε hb a ha 0 h0 f,momentFamily ε h hε hb a ha (-h/2) hs g) ∈ _ at hg
  rwa [moment_zero,moment_second] at hg

theorem correction_graph (f g : Hilbert)
    (hfg : (f,g) ∈ (longitudinalExponential ε hε h (1/2)).graph) :
    (correction ε hε h hb₀ f,(1/2:ℂ) • correction ε hε (2*h) hb₂ g) ∈
      (longitudinalExponential ε hε h (1/2)).graph := by
  have hg := defect_graph ε h hε hb _ _
    ((longitudinalExponential ε hε h (1/2)).graph.sub_mem hfg (defect_graph ε h hε hb f g hfg))
  have hs' := (longitudinalExponential ε hε h (1/2)).graph.smul_mem
    (Complex.I*(h:ℂ)/(2*(ε:ℂ))) hg
  have hc : (1/2:ℂ)*(Complex.I*((2*h:ℝ):ℂ)/(2*(ε:ℂ))) = Complex.I*(h:ℂ)/(2*(ε:ℂ)) := by
    push_cast
    ring
  simpa only [Prod.sub_def,Prod.smul_mk,correction,
    KFCausalClockFloorShiftedResponseContraction.shiftedResponse,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,smul_smul,hc] using hs'

#print axioms defect_zero
#print axioms defect_second
#print axioms moment_zero
#print axioms moment_second
#print axioms defect_graph
#print axioms inverse_graph
#print axioms moment_graph
#print axioms correction_graph
end
end UnifiedTheory.Audit.KFCausalSecondShiftClockGraphs
