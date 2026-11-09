/- Every finite power of the bounded clock defect preserves the actual
completed energy form. Its output is the corresponding shifted action
power, and it commutes with form transfer. -/
import UnifiedTheory.Audit.KFCausalClockFloorReferenceDefect
import UnifiedTheory.Audit.KFCausalClockFloorPowerVelocityPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPowerForm
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorReferenceDefect
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator)
open UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction (outputAction)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

theorem intertwines_power {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (J : E →L[ℂ] F)
    (A : E →L[ℂ] E) (B : F →L[ℂ] F) (hJ : ∀ x, J (A x) = B (J x)) (n : ℕ) (x : E) :
    J ((A^n) x) = (B^n) (J x) := by
  induction n with
  | zero => simp only [pow_zero,ContinuousLinearMap.one_apply]
  | succ n ih => simp only [pow_succ',ContinuousLinearMap.mul_apply,hJ,ih]

theorem compLp_power_coe {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] (μ : Measure X)
    (A : E →L[ℂ] E) (n : ℕ) (f : Lp E 2 μ) :
    ((A.compLpL 2 μ)^n) f =ᵐ[μ] fun x => (A^n) (f x) := by
  induction n with
  | zero => simp only [pow_zero,ContinuousLinearMap.one_apply]; exact Filter.EventuallyEq.rfl
  | succ n ih =>
    rw [pow_succ',ContinuousLinearMap.mul_apply]
    change A.compLp (((A.compLpL 2 μ)^n) f) =ᵐ[μ] _
    filter_upwards [A.coeFn_compLp (((A.compLpL 2 μ)^n) f),ih] with x hx hy
    rw [hx,hy,pow_succ',ContinuousLinearMap.mul_apply]

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ : ℝ)
local notation "V" => FormSpace ε hε h hh hb m g κ
local notation "J" => embedding ε hε h hh hb m g κ
local notation "A" => energyOutput ε hε h hh hb m g κ
local notation "D" => defectOperator ε hε
local notation "R" => ContinuousLinearMap.compLpL 2 angleMeasure (outputAction ε hε h hb)
local notation "T" => formTransfer ε hε h hh hb m g κ
local notation "P" => formDefect ε hε h hh hb m g κ

theorem formPower_embedding (t : ℝ) (n : ℕ) (u : V t) : J t (((P t)^n) u) = (D^n) (J t u) :=
  intertwines_power (J t) (P t) D (formDefect_embedding ε hε h hh hb m g κ t) n u

theorem formPower_output (t : ℝ) (n : ℕ) (u : V t) : A t (((P t)^n) u) = (R^n) (A t u) :=
  intertwines_power (A t) (P t) R (formDefect_output ε hε h hh hb m g κ t) n u

theorem formPower_transfer (s t : ℝ) (n : ℕ) (u : V s) :
    T s t (((P s)^n) u) = ((P t)^n) (T s t u) :=
  intertwines_power (T s t) (P s) (P t) (formDefect_transfer ε hε h hh hb m g κ s t) n u

theorem reference_power_pairing (t : ℝ) (n : ℕ) (u : V 0) :
    inner ℂ u (KFCausalClockFloorAveragedRegularity.referenceFormOperator ε hε h hh hb m g κ t
      (((P 0)^n) u)) = inner ℂ (A t (T 0 t u)) ((R^n) (A t (T 0 t u))) := by
  have hp := KFCausalClockFloorAveragedRegularity.referenceForm_represents_closed_form
    ε hε h hh hb m g κ t u (((P 0)^n) u)
  have he := (congrArg (A t) (formPower_transfer ε hε h hh hb m g κ 0 t n u)).trans
    (formPower_output ε hε h hh hb m g κ t n (T 0 t u))
  exact hp.trans (congrArg (fun v => inner ℂ (A t (T 0 t u)) v) he)

#print axioms intertwines_power
#print axioms compLp_power_coe
#print axioms formPower_embedding
#print axioms formPower_output
#print axioms formPower_transfer
#print axioms reference_power_pairing

end
end UnifiedTheory.Audit.KFCausalClockFloorPowerForm
