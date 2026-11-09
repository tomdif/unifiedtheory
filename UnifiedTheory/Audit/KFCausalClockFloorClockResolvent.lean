/- Actual bounded positive-clock approximants epsilon/(D+b), with their
physical multiplier, symmetric pairing and clock-composition graph. -/
import UnifiedTheory.Audit.KFCausalResidualResolventApproximation
import UnifiedTheory.Audit.KFCausalClockFloorClockOperator
import UnifiedTheory.Audit.KFCausalClockFloorMomentumResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorClockResolvent
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect defect_positive clock_positive)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorClockOperator
open UnifiedTheory.Audit.KFCausalClockFloorMomentumResponse (responseOperator_norm)
open UnifiedTheory.Audit.KFCausalContractiveResidualResolvent
open UnifiedTheory.Audit.KFCausalResidualResolventApproximation

variable (ε : ℝ) (hε : 0 < ε) (b : ℝ) (hb : 0 < b)
local notation "D" => defectOperator ε hε
local notation "hd" => responseOperator_norm ε hε

def physicalResolvent : Hilbert →L[ℂ] Hilbert := resolvent D hd b hb

def clockApprox : Hilbert →L[ℂ] Hilbert := (ε:ℂ) • physicalResolvent ε hε b hb

def clockSmoothing : Hilbert →L[ℂ] Hilbert := smoothing D hd b hb

def weight (x : Configuration) : ℝ := ε/(defect ε x.1+b)

include hε in
theorem weight_zero (x : Configuration) : weight ε 0 x = clock ε x.1 := by
  simp only [weight,add_zero,defect]
  have hc := (clock_positive ε x.1 hε.le).ne'
  field_simp [hε.ne',hc]

include hε hb in
theorem weight_positive (x : Configuration) : 0 < weight ε b x :=
  div_pos hε (add_pos (defect_positive ε x.1 hε) hb)

include hε hb in
theorem weight_bound (x : Configuration) : weight ε b x ≤ clock ε x.1 := by
  calc
    _ ≤ ε/defect ε x.1 := div_le_div_of_nonneg_left hε.le (defect_positive ε x.1 hε)
      (le_add_of_nonneg_right hb.le)
    _ = _ := by simpa only [weight,add_zero] using weight_zero ε hε x

include hε in
theorem weight_tendsto {ι : Type*} (a : ι → ℝ) (l : Filter ι) (ha : Tendsto a l (𝓝 0))
    (x : Configuration) : Tendsto (fun i => weight ε (a i) x) l (𝓝 (clock ε x.1)) := by
  have he : Tendsto (fun i => ε/(defect ε x.1+a i)) l (𝓝 (ε/(defect ε x.1+0))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.add ha)
    (show defect ε x.1+0 ≠ 0 by simpa using (defect_positive ε x.1 hε).ne')
  rw [← weight_zero ε hε x]
  exact he

theorem physicalResolvent_coe (f : Hilbert) : physicalResolvent ε hε b hb f =ᵐ[volume]
    fun x => f x/((defect ε x.1+b:ℝ):ℂ) := by
  let z := physicalResolvent ε hε b hb f
  have he : D z+(b:ℂ) • z = f := equation D hd b hb f
  filter_upwards [defectOperator_coe ε hε z,Lp.coeFn_add (D z) ((b:ℂ) • z),
    Lp.coeFn_smul (b:ℂ) z] with x hD ha hs
  have hx := congrArg (fun v : Hilbert => v x) he
  dsimp only at hx
  rw [ha] at hx
  simp only [Pi.add_apply,hs,Pi.smul_apply,smul_eq_mul,hD] at hx
  have hn : ((defect ε x.1+b:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (add_pos (defect_positive ε x.1 hε) hb).ne'
  apply (eq_div_iff hn).mpr
  calc
    z x*((defect ε x.1+b:ℝ):ℂ) = (defect ε x.1:ℂ)*z x+(b:ℂ)*z x := by push_cast; ring
    _ = f x := hx

theorem clockApprox_coe (f : Hilbert) : clockApprox ε hε b hb f =ᵐ[volume]
    fun x => (weight ε b x:ℂ)*f x := by
  filter_upwards [Lp.coeFn_smul (ε:ℂ) (physicalResolvent ε hε b hb f),
    physicalResolvent_coe ε hε b hb f] with x hs hr
  change ((ε:ℂ) • physicalResolvent ε hε b hb f) x = _
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,hr,weight,Complex.ofReal_div]
  ring

theorem clockApprox_norm (f : Hilbert) : ‖clockApprox ε hε b hb f‖ ≤ (ε/b)*‖f‖ := by
  change ‖(ε:ℂ) • resolvent D hd b hb f‖ ≤ _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε]
  exact (mul_le_mul_of_nonneg_left (resolvent_norm D hd b hb f) hε.le).trans_eq (by ring)

theorem clockApprox_dual (f g : Hilbert) :
    inner ℂ (clockApprox ε hε b hb f) g = inner ℂ f (clockApprox ε hε b hb g) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [clockApprox_coe ε hε b hb f,clockApprox_coe ε hε b hb g] with x hf hg
  rw [hf,hg]
  change inner ℂ ((weight ε b x:ℂ) • f x) (g x) = inner ℂ (f x) ((weight ε b x:ℂ) • g x)
  rw [inner_smul_left,inner_smul_right,Complex.conj_ofReal]

theorem clock_smoothing_graph (f : Hilbert) :
    (clockSmoothing ε hε b hb f,clockApprox ε hε b hb f) ∈ (clockOperator ε hε).graph := by
  change (smoothing D hd b hb f,(ε:ℂ) • resolvent D hd b hb f) ∈ _
  rw [← smoothing_factor]
  exact clock_defect_graph ε hε _

theorem expectation_integral (f : Hilbert) :
    (inner ℂ f (clockApprox ε hε b hb f)).re = ∫ x, weight ε b x*‖f x‖^2 := by
  have hi := L2.integrable_inner (𝕜 := ℂ) f (clockApprox ε hε b hb f)
  have hr := integral_re hi
  change (∫ x, (inner ℂ (f x) (clockApprox ε hε b hb f x)).re) =
    (∫ x, inner ℂ (f x) (clockApprox ε hε b hb f x)).re at hr
  rw [L2.inner_def,← hr]
  apply integral_congr_ae
  filter_upwards [clockApprox_coe ε hε b hb f] with x hx
  rw [hx]
  change (inner ℂ (f x) ((weight ε b x:ℂ) • f x)).re = _
  rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
  change ((weight ε b x:ℂ)*(‖f x‖:ℂ)^2).re = _
  rw [← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.ofReal_re]

#print axioms weight_zero
#print axioms weight_positive
#print axioms weight_bound
#print axioms weight_tendsto
#print axioms physicalResolvent_coe
#print axioms clockApprox_coe
#print axioms clockApprox_norm
#print axioms clockApprox_dual
#print axioms clock_smoothing_graph
#print axioms expectation_integral
end
end UnifiedTheory.Audit.KFCausalClockFloorClockResolvent
