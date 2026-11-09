/- A single-valued analytic inverse of the regulated clock chart on
its open strip image, including a neighborhood of every point of the
required closed horizontal strip. -/
import UnifiedTheory.Audit.KFCausalComplexClockImage

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalComplexClockInverse
noncomputable section
open Set Filter Function
open scoped Topology
open UnifiedTheory.Audit.KFCausalComplexClockChart
open UnifiedTheory.Audit.KFCausalComplexClockCoercivity
open UnifiedTheory.Audit.KFCausalComplexClockImage

def complexInverse (ε : ℝ) : ℂ → ℂ := invFunOn (complexChart ε) closedStrip

theorem complexInverse_left (ε : ℝ) (hε : 0 < ε) (z : ℂ) (hz : z ∈ closedStrip) :
    complexInverse ε (complexChart ε z)=z :=
  (complexChart_injOn ε hε).leftInvOn_invFunOn hz

theorem complexInverse_right_image (ε : ℝ) (q : ℂ)
    (hq : q ∈ complexChart ε '' closedStrip) : complexChart ε (complexInverse ε q)=q :=
  invFunOn_eq hq

theorem complexInverse_mem_image (ε : ℝ) (q : ℂ)
    (hq : q ∈ complexChart ε '' closedStrip) : complexInverse ε q ∈ closedStrip :=
  invFunOn_mem hq

theorem complexInverse_analytic_image (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : q ∈ complexChart ε '' openStrip) : AnalyticAt ℂ (complexInverse ε) q := by
  obtain ⟨z,hz,rfl⟩ := hq
  have hd : deriv (complexChart ε) z ≠ 0 := by
    rw [(complexChart_derivative ε z).deriv]
    exact complexChart_derivative_ne_zero ε hε z (show |z.im| ≤ Real.pi/2 from le_of_lt hz)
  apply (analyticAt_comp_iff_of_deriv_ne_zero (complexChart_analytic ε z) hd).mp
  apply (analyticAt_id : AnalyticAt ℂ (fun x : ℂ => x) z).congr
  filter_upwards [openStrip_open.mem_nhds hz] with x hx
  exact (complexInverse_left ε hε x (show |x.im| ≤ Real.pi/2 from le_of_lt hx)).symm

theorem complexInverse_right (ε : ℝ) (hε : 0 < ε) (q : ℂ) (hq : q ∈ targetStrip ε) :
    complexChart ε (complexInverse ε q)=q := by
  obtain ⟨z,hz,he⟩ := complexChart_surjOn_strip ε hε hq
  exact complexInverse_right_image ε q ⟨z,(show |z.im| < Real.pi/2 from hz).le,he⟩

theorem complexInverse_mem (ε : ℝ) (hε : 0 < ε) (q : ℂ) (hq : q ∈ targetStrip ε) :
    complexInverse ε q ∈ openStrip := by
  obtain ⟨z,hz,rfl⟩ := complexChart_surjOn_strip ε hε hq
  rw [complexInverse_left ε hε z (show |z.im| ≤ Real.pi/2 from le_of_lt hz)]
  exact hz

theorem complexInverse_analytic (ε : ℝ) (hε : 0 < ε) (q : ℂ) (hq : q ∈ targetStrip ε) :
    AnalyticAt ℂ (complexInverse ε) q :=
  complexInverse_analytic_image ε hε q (complexChart_surjOn_strip ε hε hq)

theorem complexInverse_norm_bound (ε : ℝ) (hε : 0 < ε) (q r : ℂ)
    (hq : q ∈ targetStrip ε) (hr : r ∈ targetStrip ε) :
    ‖complexInverse ε q-complexInverse ε r‖ ≤ ‖q-r‖/ε := by
  apply (le_div_iff₀ hε).mpr
  have hb := complexChart_norm_lower ε (complexInverse ε r) (complexInverse ε q)
    (show |(complexInverse ε r).im| ≤ Real.pi/2 from le_of_lt (complexInverse_mem ε hε r hr))
    (show |(complexInverse ε q).im| ≤ Real.pi/2 from le_of_lt (complexInverse_mem ε hε q hq))
  rw [complexInverse_right ε hε q hq,complexInverse_right ε hε r hr] at hb
  nlinarith

theorem complexInverse_real (ε : ℝ) (hε : 0 < ε) (q : ℝ) :
    complexInverse ε (q:ℂ)=(KFCausalRegularizedLongitudinalChart.chartIso ε hε).symm q := by
  let s := (KFCausalRegularizedLongitudinalChart.chartIso ε hε).symm q
  have hs : (s:ℂ) ∈ closedStrip := by change |(s:ℂ).im| ≤ Real.pi/2; simp; positivity
  have he : complexChart ε (s:ℂ)=(q:ℂ) := by
    rw [complexChart_real,← KFCausalRegularizedLongitudinalChart.chartIso_apply ε hε]
    simp [s]
  rw [← he,complexInverse_left ε hε _ hs]

#print axioms complexInverse_left
#print axioms complexInverse_right_image
#print axioms complexInverse_mem_image
#print axioms complexInverse_analytic_image
#print axioms complexInverse_right
#print axioms complexInverse_mem
#print axioms complexInverse_analytic
#print axioms complexInverse_norm_bound
#print axioms complexInverse_real

end
end UnifiedTheory.Audit.KFCausalComplexClockInverse
