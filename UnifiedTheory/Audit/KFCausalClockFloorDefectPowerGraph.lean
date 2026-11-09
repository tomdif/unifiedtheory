/- Every finite defect power times a coherent state belongs to the actual
half-longitudinal-exponential domain. Its image is the analytic shifted
profile, not a postulated domain-stability assumption. -/
import UnifiedTheory.Audit.KFCausalClockFloorMultiplierGraph
import UnifiedTheory.Audit.KFCausalClockFloorDefectCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDefectPowerGraph
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
open UnifiedTheory.Audit.KFCausalClockFloorDefectCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorMultiplierGraph
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates

def multiplier (ε : ℝ) (n : ℕ) (q : ℂ) : ℂ := complexDefect ε q ^ n

theorem multiplier_analytic (ε : ℝ) (hε : 0 < ε) (n : ℕ) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) : AnalyticAt ℂ (multiplier ε n) q :=
  (complexDefect_analytic ε hε q
    (KFCausalClockFloorFullGaussian.third_strip_subset ε hε q hq)).pow n

theorem multiplier_bound (ε : ℝ) (hε : 0 < ε) (n : ℕ) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) : ‖multiplier ε n q‖ ≤ (2:ℝ)^n := by
  rw [multiplier,norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (complexDefect_norm_le_two ε hε q hq) n

variable (ε a α β p : ℝ) (b : Fin 5 → ℂ) (hε : 0 < ε)
  (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)

def state (n : ℕ) (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) : Hilbert :=
  physicalState (multiplier ε n) ε a α β p (2^n) b hε (multiplier_analytic ε hε n)
    (by positivity) (multiplier_bound ε hε n) ha hα hβ hw y hy

def profile (y : ℝ) : Space → ℂ :=
  KFCausalClockFloorCoherentFullFourier.euclideanLine ε a α β p b y ∘
    KFCausalEuclideanClockSplit.euclideanSplit

theorem state_coe (n : ℕ) (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) :
    straightening ε hε (state ε a α β p b hε ha hα hβ hw n y hy) =ᵐ[volume]
      fun x => complexDefect ε ((x 0:ℂ)+(y:ℂ)*Complex.I)^n * profile ε a α β p b y x := by
  change euclideanPullback ((coordinates ε hε).symm (coordinates ε hε
    (euclideanPullback.symm _))) =ᵐ[volume] _
  rw [LinearIsometryEquiv.symm_apply_apply,LinearIsometryEquiv.apply_symm_apply]
  exact (spectralLine_memLp (multiplier ε n) ε a α β p (2^n) b hε
    (multiplier_analytic ε hε n) (by positivity) (multiplier_bound ε hε n) ha hα hβ hw y hy).coeFn_toLp

theorem state_zero_successor (n : ℕ) (h0 : |(0:ℝ)| ≤ Real.pi*ε/3) :
    state ε a α β p b hε ha hα hβ hw (n+1) 0 h0 =
      defectOperator ε hε (state ε a α β p b hε ha hα hβ hw n 0 h0) := by
  apply (straightening ε hε).injective
  apply Lp.ext
  filter_upwards [state_coe ε a α β p b hε ha hα hβ hw (n+1) 0 h0,
    state_coe ε a α β p b hε ha hα hβ hw n 0 h0,
    straightening_defect_coe ε hε (state ε a α β p b hε ha hα hβ hw n 0 h0)] with x hx hy hd
  rw [hx,hd,hy]
  simp only [Complex.ofReal_zero,zero_mul,add_zero,complexDefect_real ε hε,pow_succ]
  ring

theorem state_half_graph (n : ℕ) (hbar : ℝ) (hh : |hbar| ≤ 2*Real.pi*ε/3)
    (h0 : |(0:ℝ)| ≤ Real.pi*ε/3) (hs : |-hbar/2| ≤ Real.pi*ε/3) :
    (state ε a α β p b hε ha hα hβ hw n 0 h0,
      state ε a α β p b hε ha hα hβ hw n (-hbar/2) hs) ∈
      (longitudinalExponential ε hε hbar (1/2)).graph :=
  physicalState_half_graph (multiplier ε n) ε a α β p (2^n) b hε
    (multiplier_analytic ε hε n) (by positivity) (multiplier_bound ε hε n)
    ha hα hβ hw hbar hh h0 hs

theorem defect_state_half_graph (n : ℕ) (hbar : ℝ) (hh : |hbar| ≤ 2*Real.pi*ε/3)
    (h0 : |(0:ℝ)| ≤ Real.pi*ε/3) (hs : |-hbar/2| ≤ Real.pi*ε/3) :
    (defectOperator ε hε (state ε a α β p b hε ha hα hβ hw n 0 h0),
      state ε a α β p b hε ha hα hβ hw (n+1) (-hbar/2) hs) ∈
      (longitudinalExponential ε hε hbar (1/2)).graph := by
  rw [← state_zero_successor ε a α β p b hε ha hα hβ hw n h0]
  exact state_half_graph ε a α β p b hε ha hα hβ hw (n+1) hbar hh h0 hs

#print axioms multiplier_analytic
#print axioms multiplier_bound
#print axioms state_coe
#print axioms state_zero_successor
#print axioms state_half_graph
#print axioms defect_state_half_graph

end
end UnifiedTheory.Audit.KFCausalClockFloorDefectPowerGraph
