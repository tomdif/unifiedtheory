/- Clock-only specialization of the proved analytic strip-family graph
calculus. The operator is identified with its physical multiplier before
it is applied to the unbounded longitudinal exponential graph. -/
import UnifiedTheory.Audit.KFCausalStripFamilyPhysicalMultiplier
import UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalAnalyticClockFamily
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanClockSplit (TailSpace)
open KFCausalRegularizedLongitudinalChart (chart)
open KFCausalClockFloorExponential (longitudinalExponential)

variable (F : ℂ → ℂ) (d M : ℝ)
  (hF : ∀ q, |q.im| ≤ d → AnalyticAt ℂ F q)
  (hM : 0 ≤ M) (hB : ∀ q, |q.im| ≤ d → ‖F q‖ ≤ M)

include hF in
theorem line_continuous (y : ℝ) (hy : |y| ≤ d) :
    Continuous (fun w : ℝ × TailSpace => F ((w.1:ℂ)+(y:ℂ)*Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro w
  exact (hF _ (by simpa using hy)).continuousAt.comp (by fun_prop)

def operator (ε : ℝ) (hε : 0 < ε) (y : ℝ) (hy : |y| ≤ d) : Hilbert →L[ℂ] Hilbert :=
  KFCausalStripFamilyExponentialGraph.physicalMultiplier (fun q _ => F q) d M
    (line_continuous F d hF) hM (fun q hq _ => hB q hq) ε hε y hy

theorem operator_coe (ε : ℝ) (hε : 0 < ε) (y : ℝ) (hy : |y| ≤ d) (f : Hilbert) :
    operator F d M hF hM hB ε hε y hy f =ᵐ[volume]
      fun x => F ((chart ε x.1:ℂ)+(y:ℂ)*Complex.I)*f x := by
  have hc := KFCausalStripFamilyPhysicalMultiplier.physicalMultiplier_representative
    ε hε (fun q _ => F q) d M (line_continuous F d hF) hM
      (fun q hq _ => hB q hq) y hy f
  exact hc

theorem graph (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (h0 : |(0:ℝ)| ≤ d) (hs : |-h/2| ≤ d) (f g : Hilbert)
    (hfg : (f,g) ∈ (longitudinalExponential ε hε h (1/2)).graph) :
    (operator F d M hF hM hB ε hε 0 h0 f,
      operator F d M hF hM hB ε hε (-h/2) hs g) ∈
        (longitudinalExponential ε hε h (1/2)).graph :=
  KFCausalStripFamilyExponentialGraph.graph_multiplier (fun q _ => F q) d M
    (fun _ q hq => hF q hq) (line_continuous F d hF) hM
    (fun q hq _ => hB q hq) ε hε h h0 hs f g hfg

theorem operator_eq (ε : ℝ) (hε : 0 < ε) (y : ℝ) (hy : |y| ≤ d)
    (A : Hilbert →L[ℂ] Hilbert)
    (hA : ∀ f : Hilbert, A f =ᵐ[volume]
      fun x => F ((chart ε x.1:ℂ)+(y:ℂ)*Complex.I)*f x) :
    operator F d M hF hM hB ε hε y hy = A := by
  apply ContinuousLinearMap.ext
  intro f
  exact Lp.ext ((operator_coe F d M hF hM hB ε hε y hy f).trans (hA f).symm)

#print axioms line_continuous
#print axioms operator_coe
#print axioms graph
#print axioms operator_eq
end
end UnifiedTheory.Audit.KFCausalAnalyticClockFamily
