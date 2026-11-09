/- The analytic clock weight D(1-D) has its shifted squared modulus
controlled by actual classical dissipation, including both clock tails. -/
import UnifiedTheory.Audit.KFCausalClockFloorDefectProductionCoercivity

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorLocalizedVacuumScalar
noncomputable section
open KFCausalComplexClockChart
open KFCausalComplexClockInverse
open KFCausalClockInverseStripBounds
open KFCausalClockFloorComplexDefect
open KFCausalRegularizedLongitudinalChart (chart chartIso)
open KFCausalClockFloorDefectTransportScalar (drift)

theorem inverse_exp_upper (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) :
    Real.exp (complexInverse ε q).re ≤ 2*Real.exp ((chartIso ε hε).symm q.re) := by
  have ht : q ∈ targetStrip ε := by change |q.im| ≤ Real.pi*ε/2; nlinarith [Real.pi_pos]
  have hr := inverse_re_ge_real ε hε q ht
  have he := congrArg Complex.re (complexInverse_right ε hε q ht)
  rw [complexChart_re] at he
  have hs : chart ε ((chartIso ε hε).symm q.re)=q.re := (chartIso ε hε).apply_symm_apply _
  unfold chart at hs
  have hl := inverse_exp_re_lower ε hε q hq
  rw [Complex.exp_re] at hl
  nlinarith only [hl,he,hs,mul_le_mul_of_nonneg_left hr hε.le]

theorem response_norm_bound (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) :
    ‖1-complexDefect ε q‖ ≤ 4*(1-realDefect ε hε q.re) := by
  have ht : q ∈ targetStrip ε := by change |q.im| ≤ Real.pi*ε/2; nlinarith [Real.pi_pos]
  have hc := complexClock_ne_zero ε hε q ht
  have hr := realClock_positive ε hε q.re
  have he : 1-complexDefect ε q = Complex.exp (complexInverse ε q)/complexClock ε q := by
    unfold complexDefect
    field_simp
    simp only [complexClock]
    ring
  have hd : 1-realDefect ε hε q.re =
      Real.exp ((chartIso ε hε).symm q.re)/realClock ε hε q.re := by
    change 1-ε/realClock ε hε q.re = _
    apply (eq_div_iff hr.ne').mpr
    field_simp
    simp only [realClock,KFCausalClockFloorFlow.clock]
    ring
  rw [he,norm_div,Complex.norm_exp,hd]
  calc
    _ ≤ (2*Real.exp ((chartIso ε hε).symm q.re))/‖complexClock ε q‖ :=
      div_le_div_of_nonneg_right (inverse_exp_upper ε hε q hq) (norm_nonneg _)
    _ ≤ (2*Real.exp ((chartIso ε hε).symm q.re))/(realClock ε hε q.re/2) :=
      div_le_div_of_nonneg_left (by positivity) (half_pos hr) (complexClock_norm_lower ε hε q hq)
    _ = _ := by ring

theorem localized_norm_square (ε : ℝ) (hε : 0 < ε) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) :
    ‖complexDefect ε q-(complexDefect ε q)^2‖^2 ≤
      64*ε*(-drift ε (realDefect ε hε q.re)) := by
  let d := realDefect ε hε q.re
  let z := complexDefect ε q
  have hd : 0 ≤ d := (realDefect_positive ε hε q.re).le
  have hd1 : d ≤ 1 := KFCausalClockFloorQuantumVelocityScalar.realDefect_le_one ε hε q.re
  have hr : 0 ≤ 1-d := sub_nonneg.mpr hd1
  have hn : ‖z-z^2‖ ≤ 8*d*(1-d) := by
    rw [show z-z^2=z*(1-z) by ring,norm_mul]
    exact (mul_le_mul (complexDefect_norm_bound ε hε q hq) (response_norm_bound ε hε q hq)
      (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hp : (1-d)^2 ≤ 1-d := by nlinarith only [hd,hd1]
  calc
    _ ≤ (8*d*(1-d))^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = 64*d^2*(1-d)^2 := by ring
    _ ≤ 64*d^2*(1-d) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by dsimp [d,drift]; field_simp

theorem physical_localized_norm_square (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hb : |h| ≤ 2*Real.pi*ε/3) (x : KFCausalCoupledLongitudinalFlow.Configuration) :
    ‖KFCausalClockFloorShiftedDefectPhysical.physicalSymbol ε h x-
      (KFCausalClockFloorShiftedDefectPhysical.physicalSymbol ε h x)^2‖^2 ≤
      64*ε*(-drift ε (KFCausalClockFloorCanonicalDefect.defect ε x.1)) := by
  have hy : |-h/2| ≤ Real.pi*ε/3 := by
    rw [abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  have he := localized_norm_square ε hε ((chart ε x.1:ℂ)+(-h/2:ℝ)*Complex.I) (by simpa using hy)
  simpa [KFCausalClockFloorShiftedDefectPhysical.physicalSymbol,
    realDefect,show (chartIso ε hε).symm (chart ε x.1)=x.1 from
      (chartIso ε hε).symm_apply_apply x.1] using he

#print axioms inverse_exp_upper
#print axioms response_norm_bound
#print axioms localized_norm_square
#print axioms physical_localized_norm_square
end
end UnifiedTheory.Audit.KFCausalClockFloorLocalizedVacuumScalar
