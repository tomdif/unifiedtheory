/- Energy and graph-norm control on the actual common completed form
domain. These are estimates for the time-varying forms, not a propagator. -/
import UnifiedTheory.Audit.KFCausalRegularizedFormTransport
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalRegularizedFormTimeControl
noncomputable section
open UnifiedTheory.Audit.KFCausalRegularizedMomentumClosure
open UnifiedTheory.Audit.KFCausalRegularizedClosedForm
open UnifiedTheory.Audit.KFCausalRegularizedFormEmbedding
open UnifiedTheory.Audit.KFCausalRegularizedFormTransport

theorem norm_timeOutput_sq (s t : ℝ) (y : Output) :
    ‖timeOutput s t y‖^2 = ‖(WithLp.ofLp y).1‖^2 +
      Real.exp (2*(t-s))*‖(WithLp.ofLp y).2‖^2 := by
  rw [timeOutput_apply, WithLp.prod_norm_sq_eq_of_L2]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_pow]
  rw [show Real.exp (2*(t-s)) = Real.exp (t-s)^2 by rw [two_mul,Real.exp_add,pow_two]]

def clockPart (ε : ℝ) (hε : 0 < ε) (hbar coupling : ℝ)
    (u : FormSpace ε hε hbar coupling 0) : Hilbert :=
  (WithLp.ofLp (energyOutput ε hε hbar coupling 0 u)).1

def momentumPart (ε : ℝ) (hε : 0 < ε) (hbar coupling : ℝ)
    (u : FormSpace ε hε hbar coupling 0) : Hilbert :=
  (WithLp.ofLp (energyOutput ε hε hbar coupling 0 u)).2

def timeEnergy (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (u : FormSpace ε hε hbar coupling 0) : ℝ :=
  ‖clockPart ε hε hbar coupling u‖^2 + Real.exp (2*t)*‖momentumPart ε hε hbar coupling u‖^2

theorem timeEnergy_actual (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (u : FormSpace ε hε hbar coupling 0) :
    ‖energyOutput ε hε hbar coupling t (formTransfer ε hε hbar coupling 0 t u)‖^2 =
      timeEnergy ε hε hbar coupling t u := by
  rw [transfer_energyOutput, norm_timeOutput_sq]
  simp only [sub_zero,timeEnergy,clockPart,momentumPart]

theorem timeEnergy_nonneg (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (u : FormSpace ε hε hbar coupling 0) : 0 ≤ timeEnergy ε hε hbar coupling t u := by
  unfold timeEnergy
  positivity

theorem timeEnergy_derivative (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (u : FormSpace ε hε hbar coupling 0) :
    HasDerivAt (fun s => timeEnergy ε hε hbar coupling s u)
      (2*Real.exp (2*t)*‖momentumPart ε hε hbar coupling u‖^2) t := by
  have he := (Real.hasDerivAt_exp (2*t)).comp t ((hasDerivAt_id t).const_mul 2)
  have he' : HasDerivAt (fun s : ℝ => Real.exp (2*s)) (2*Real.exp (2*t)) t := by
    convert he using 1
    ring
  exact (he'.mul_const (‖momentumPart ε hε hbar coupling u‖^2)).const_add
    (‖clockPart ε hε hbar coupling u‖^2)

theorem timeEnergy_derivative_bounds (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (u : FormSpace ε hε hbar coupling 0) :
    0 ≤ 2*Real.exp (2*t)*‖momentumPart ε hε hbar coupling u‖^2 ∧
    2*Real.exp (2*t)*‖momentumPart ε hε hbar coupling u‖^2 ≤ 2*timeEnergy ε hε hbar coupling t u := by
  constructor
  · positivity
  · unfold timeEnergy
    nlinarith [sq_nonneg ‖clockPart ε hε hbar coupling u‖]

theorem timeEnergy_comparison (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ) (hst : s ≤ t)
    (u : FormSpace ε hε hbar coupling 0) :
    timeEnergy ε hε hbar coupling s u ≤ timeEnergy ε hε hbar coupling t u ∧
    timeEnergy ε hε hbar coupling t u ≤ Real.exp (2*(t-s))*timeEnergy ε hε hbar coupling s u := by
  have he : Real.exp (2*(t-s))*Real.exp (2*s) = Real.exp (2*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h1 : 1 ≤ Real.exp (2*(t-s)) := Real.one_le_exp (by linarith)
  have hm : Real.exp (2*s) ≤ Real.exp (2*t) := Real.exp_le_exp.mpr (by linarith)
  unfold timeEnergy
  constructor
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hm (sq_nonneg _))
  · have hc := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖clockPart ε hε hbar coupling u‖)
    rw [← he]
    nlinarith

theorem transported_form_norm (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (u : FormSpace ε hε hbar coupling 0) :
    ‖formTransfer ε hε hbar coupling 0 t u‖^2 =
      ‖embedding ε hε hbar coupling 0 u‖^2 + timeEnergy ε hε hbar coupling t u := by
  rw [form_norm_identity ε hε hbar coupling t, transfer_embedding ε hε hbar coupling 0 t,
    timeEnergy_actual ε hε hbar coupling t]

theorem transported_form_norm_comparison (ε : ℝ) (hε : 0 < ε) (hbar coupling s t : ℝ)
    (hst : s ≤ t) (u : FormSpace ε hε hbar coupling 0) :
    ‖formTransfer ε hε hbar coupling 0 s u‖^2 ≤ ‖formTransfer ε hε hbar coupling 0 t u‖^2 ∧
    ‖formTransfer ε hε hbar coupling 0 t u‖^2 ≤
      Real.exp (2*(t-s))*‖formTransfer ε hε hbar coupling 0 s u‖^2 := by
  rw [transported_form_norm ε hε hbar coupling s,transported_form_norm ε hε hbar coupling t]
  obtain ⟨hl,hu⟩ := timeEnergy_comparison ε hε hbar coupling s t hst u
  have h1 : 1 ≤ Real.exp (2*(t-s)) := Real.one_le_exp (by linarith)
  have hn := sq_nonneg ‖embedding ε hε hbar coupling 0 u‖
  constructor
  · linarith
  · nlinarith

theorem reference_norm_identity (ε : ℝ) (hε : 0 < ε) (hbar coupling : ℝ)
    (u : FormSpace ε hε hbar coupling 0) :
    ‖u‖^2 = ‖embedding ε hε hbar coupling 0 u‖^2 +
      ‖clockPart ε hε hbar coupling u‖^2 + ‖momentumPart ε hε hbar coupling u‖^2 := by
  rw [form_norm_identity ε hε hbar coupling 0, WithLp.prod_norm_sq_eq_of_L2]
  simp only [clockPart,momentumPart,add_assoc]
  rfl

theorem transported_form_coercive (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (u : FormSpace ε hε hbar coupling 0) :
    0 < min 1 (Real.exp (2*t)) ∧
    min 1 (Real.exp (2*t))*‖u‖^2 ≤ ‖formTransfer ε hε hbar coupling 0 t u‖^2 := by
  refine ⟨lt_min (by norm_num) (Real.exp_pos _), ?_⟩
  rw [transported_form_norm ε hε hbar coupling t, reference_norm_identity ε hε hbar coupling,
    timeEnergy]
  have hi := mul_le_mul_of_nonneg_right (min_le_left 1 (Real.exp (2*t)))
    (sq_nonneg ‖embedding ε hε hbar coupling 0 u‖)
  have ha := mul_le_mul_of_nonneg_right (min_le_left 1 (Real.exp (2*t)))
    (sq_nonneg ‖clockPart ε hε hbar coupling u‖)
  have hb := mul_le_mul_of_nonneg_right (min_le_right 1 (Real.exp (2*t)))
    (sq_nonneg ‖momentumPart ε hε hbar coupling u‖)
  nlinarith

#print axioms norm_timeOutput_sq
#print axioms timeEnergy_actual
#print axioms timeEnergy_derivative
#print axioms timeEnergy_derivative_bounds
#print axioms timeEnergy_comparison
#print axioms transported_form_norm
#print axioms transported_form_norm_comparison
#print axioms reference_norm_identity
#print axioms transported_form_coercive

end
end UnifiedTheory.Audit.KFCausalRegularizedFormTimeControl
