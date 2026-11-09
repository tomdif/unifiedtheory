/- Energy and graph-norm estimates on the full eight-factor completed
form domain. These control the actual time-dependent forms; constructing
a physical propagator is a separate step. -/
import UnifiedTheory.Audit.KFCausalPhysicalFormTransport
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalPhysicalFormTimeControl
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalFiniteJointGraph
open UnifiedTheory.Audit.KFCausalFiniteOutputRescaling
open UnifiedTheory.Audit.KFCausalPhysicalEnergyTransport
open UnifiedTheory.Audit.KFCausalPhysicalFormTransport

def staticPart (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum : ℝ)
    (u : FormSpace ε hε hbar hh mass2 quartic vacuum 0) : Output (Fin 8) Hilbert :=
  staticOutput (energyOutput ε hε hbar hh mass2 quartic vacuum 0 u)

def growingPart (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum : ℝ)
    (u : FormSpace ε hε hbar hh mass2 quartic vacuum 0) : Output (Fin 8) Hilbert :=
  growingOutput (energyOutput ε hε hbar hh mass2 quartic vacuum 0 u)

def timeEnergy (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum t : ℝ)
    (u : FormSpace ε hε hbar hh mass2 quartic vacuum 0) : ℝ :=
  ‖staticPart ε hε hbar hh mass2 quartic vacuum u‖^2 + Real.exp (2*t)*‖growingPart ε hε hbar hh mass2 quartic vacuum u‖^2

theorem timeEnergy_actual (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum t : ℝ)
    (u : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    ‖energyOutput ε hε hbar hh mass2 quartic vacuum t (formTransfer ε hε hbar hh mass2 quartic vacuum 0 t u)‖^2 =
      timeEnergy ε hε hbar hh mass2 quartic vacuum t u := by
  rw [transfer_energyOutput, norm_timeOutput_sq]
  simp only [sub_zero,timeEnergy,staticPart,growingPart]

theorem timeEnergy_nonneg (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum t : ℝ)
    (u : FormSpace ε hε hbar hh mass2 quartic vacuum 0) : 0 ≤ timeEnergy ε hε hbar hh mass2 quartic vacuum t u := by
  unfold timeEnergy
  positivity

theorem timeEnergy_derivative (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum t : ℝ)
    (u : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    HasDerivAt (fun s => timeEnergy ε hε hbar hh mass2 quartic vacuum s u)
      (2*Real.exp (2*t)*‖growingPart ε hε hbar hh mass2 quartic vacuum u‖^2) t := by
  have he := (Real.hasDerivAt_exp (2*t)).comp t ((hasDerivAt_id t).const_mul 2)
  have he' : HasDerivAt (fun s : ℝ => Real.exp (2*s)) (2*Real.exp (2*t)) t := by
    convert he using 1
    ring
  exact (he'.mul_const (‖growingPart ε hε hbar hh mass2 quartic vacuum u‖^2)).const_add
    (‖staticPart ε hε hbar hh mass2 quartic vacuum u‖^2)

theorem timeEnergy_derivative_bounds (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum t : ℝ)
    (u : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    0 ≤ 2*Real.exp (2*t)*‖growingPart ε hε hbar hh mass2 quartic vacuum u‖^2 ∧
    2*Real.exp (2*t)*‖growingPart ε hε hbar hh mass2 quartic vacuum u‖^2 ≤ 2*timeEnergy ε hε hbar hh mass2 quartic vacuum t u := by
  constructor
  · positivity
  · unfold timeEnergy
    nlinarith [sq_nonneg ‖staticPart ε hε hbar hh mass2 quartic vacuum u‖]

theorem timeEnergy_comparison (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s t : ℝ) (hst : s ≤ t)
    (u : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    timeEnergy ε hε hbar hh mass2 quartic vacuum s u ≤ timeEnergy ε hε hbar hh mass2 quartic vacuum t u ∧
    timeEnergy ε hε hbar hh mass2 quartic vacuum t u ≤ Real.exp (2*(t-s))*timeEnergy ε hε hbar hh mass2 quartic vacuum s u := by
  have he : Real.exp (2*(t-s))*Real.exp (2*s) = Real.exp (2*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h1 : 1 ≤ Real.exp (2*(t-s)) := Real.one_le_exp (by linarith)
  have hm : Real.exp (2*s) ≤ Real.exp (2*t) := Real.exp_le_exp.mpr (by linarith)
  unfold timeEnergy
  constructor
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hm (sq_nonneg _))
  · have hc := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖staticPart ε hε hbar hh mass2 quartic vacuum u‖)
    rw [← he]
    nlinarith

theorem transported_form_norm (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum t : ℝ)
    (u : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    ‖formTransfer ε hε hbar hh mass2 quartic vacuum 0 t u‖^2 =
      ‖embedding ε hε hbar hh mass2 quartic vacuum 0 u‖^2 + timeEnergy ε hε hbar hh mass2 quartic vacuum t u := by
  rw [form_norm_identity ε hε hbar hh mass2 quartic vacuum t, transfer_embedding ε hε hbar hh mass2 quartic vacuum 0 t,
    timeEnergy_actual ε hε hbar hh mass2 quartic vacuum t]

theorem transported_form_norm_comparison (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s t : ℝ)
    (hst : s ≤ t) (u : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    ‖formTransfer ε hε hbar hh mass2 quartic vacuum 0 s u‖^2 ≤ ‖formTransfer ε hε hbar hh mass2 quartic vacuum 0 t u‖^2 ∧
    ‖formTransfer ε hε hbar hh mass2 quartic vacuum 0 t u‖^2 ≤
      Real.exp (2*(t-s))*‖formTransfer ε hε hbar hh mass2 quartic vacuum 0 s u‖^2 := by
  rw [transported_form_norm ε hε hbar hh mass2 quartic vacuum s,transported_form_norm ε hε hbar hh mass2 quartic vacuum t]
  obtain ⟨hl,hu⟩ := timeEnergy_comparison ε hε hbar hh mass2 quartic vacuum s t hst u
  have h1 : 1 ≤ Real.exp (2*(t-s)) := Real.one_le_exp (by linarith)
  have hn := sq_nonneg ‖embedding ε hε hbar hh mass2 quartic vacuum 0 u‖
  constructor
  · linarith
  · nlinarith

theorem reference_norm_identity (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum : ℝ)
    (u : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    ‖u‖^2 = ‖embedding ε hε hbar hh mass2 quartic vacuum 0 u‖^2 +
      ‖staticPart ε hε hbar hh mass2 quartic vacuum u‖^2 + ‖growingPart ε hε hbar hh mass2 quartic vacuum u‖^2 := by
  rw [form_norm_identity ε hε hbar hh mass2 quartic vacuum 0,
    split_norm (fun i : Fin 8 => i.val<3)]
  simp only [staticPart,growingPart,staticOutput,growingOutput,add_assoc]

theorem transported_form_coercive (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum t : ℝ)
    (u : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    0 < min 1 (Real.exp (2*t)) ∧
    min 1 (Real.exp (2*t))*‖u‖^2 ≤ ‖formTransfer ε hε hbar hh mass2 quartic vacuum 0 t u‖^2 := by
  refine ⟨lt_min (by norm_num) (Real.exp_pos _), ?_⟩
  rw [transported_form_norm ε hε hbar hh mass2 quartic vacuum t, reference_norm_identity ε hε hbar hh mass2 quartic vacuum,
    timeEnergy]
  have hi := mul_le_mul_of_nonneg_right (min_le_left 1 (Real.exp (2*t)))
    (sq_nonneg ‖embedding ε hε hbar hh mass2 quartic vacuum 0 u‖)
  have ha := mul_le_mul_of_nonneg_right (min_le_left 1 (Real.exp (2*t)))
    (sq_nonneg ‖staticPart ε hε hbar hh mass2 quartic vacuum u‖)
  have hb := mul_le_mul_of_nonneg_right (min_le_right 1 (Real.exp (2*t)))
    (sq_nonneg ‖growingPart ε hε hbar hh mass2 quartic vacuum u‖)
  nlinarith

#print axioms timeEnergy_actual
#print axioms timeEnergy_nonneg
#print axioms timeEnergy_derivative
#print axioms timeEnergy_derivative_bounds
#print axioms timeEnergy_comparison
#print axioms transported_form_norm
#print axioms transported_form_norm_comparison
#print axioms reference_norm_identity
#print axioms transported_form_coercive

end
end UnifiedTheory.Audit.KFCausalPhysicalFormTimeControl
