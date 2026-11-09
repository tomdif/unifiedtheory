/- The actual clock response on a fixed reference form space, jointly
continuous in time and state. The bounded clock commutators converge to it. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedClockResolvent
import UnifiedTheory.Audit.KFCausalAveragedOutputTimeContinuity
import UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
import UnifiedTheory.Audit.KFCausalNeutralReferencePairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorClockReferenceRate
noncomputable section
open Filter
open scoped Topology ComplexConjugate
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedClockResolvent
open UnifiedTheory.Audit.KFCausalClockFloorReferenceClockCore (clockResponse)
open UnifiedTheory.Audit.KFCausalClockFloorClockOutputForm (response response_continuous response_norm)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedOutputTransport (timeOutputLp)
open UnifiedTheory.Audit.KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open UnifiedTheory.Audit.KFCausalAveragedOutputTimeContinuity
open UnifiedTheory.Audit.KFCausalNeutralReferencePairing (coefficient coefficient_norm)

theorem coefficient_bound (h : ℝ) (hne : h ≠ 0) (q : ℂ) (M E : ℝ)
    (hq : ‖q‖ ≤ M*|h| * E) : ‖coefficient h*q‖ ≤ M*E := by
  rw [norm_mul,coefficient_norm]
  have hx := abs_pos.mpr hne
  have hd : ‖q‖/|h| ≤ M*E := (div_le_iff₀ hx).mpr (by nlinarith only [hq])
  simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using hd

private theorem output_pullback {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (A : V →L[ℂ] EnergyOutputSpace) :
    Continuous (fun p : ℝ × V => timeOutputLp 0 p.1 (A p.2)) := by
  have hp : Continuous (fun p : ℝ × V => (p.1,A p.2)) :=
    continuous_fst.prodMk (A.continuous.comp continuous_snd)
  exact (timeOutputLp_continuous 0).comp (f := fun p : ℝ × V => (p.1,A p.2)) hp

private theorem response_pullback {X : Type*} [TopologicalSpace X]
    (f : X → EnergyOutputSpace) (hf : Continuous f)
    (r : EnergyOutputSpace → EnergyOutputSpace → ℂ)
    (hr : Continuous (fun p : EnergyOutputSpace × EnergyOutputSpace => r p.1 p.2)) (c : ℂ) :
    Continuous (fun x => c*r (f x) (f x)) := continuous_const.mul (hr.comp (hf.prodMk hf))

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "𝒲" => FormSpace ε hε h hne hh m g k
local notation "A" => energyOutput ε hε h hne hh m g k
local notation "T" => formTransfer ε hε h hne hh m g k
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "B" => formApprox ε hε h hne hh m g k
local notation "S" => formSmoothing ε hε h hne hh m g k

def output (t : ℝ) (u : 𝒲 0) : EnergyOutputSpace := timeOutputLp 0 t (A 0 u)

def rate (t : ℝ) (u : 𝒲 0) : ℂ :=
  coefficient h*response ε hε h hh (output ε hε h hne hh m g k t u) (output ε hε h hne hh m g k t u)

def approxRate (b : ℝ) (hb : 0 < b) (t : ℝ) (u : 𝒲 0) : ℂ :=
  coefficient h*(inner ℂ u (Q t (B 0 b hb u))-conj (inner ℂ u (Q t (B 0 b hb u))))

theorem output_actual (t : ℝ) (u : 𝒲 0) : output ε hε h hne hh m g k t u = A t (T 0 t u) :=
  (transfer_energyOutput ε hε h hne hh m g k 0 t u).symm

theorem output_continuous : Continuous (fun p : ℝ × 𝒲 0 => output ε hε h hne hh m g k p.1 p.2) :=
  output_pullback (A 0)

theorem rate_continuous : Continuous (fun p : ℝ × 𝒲 0 => rate ε hε h hne hh m g k p.1 p.2) :=
  response_pullback _ (output_continuous ε hε h hne hh m g k) _
    (response_continuous ε hε h hh) (coefficient h)

theorem energy_continuous : Continuous (fun p : ℝ × 𝒲 0 => timeEnergy ε hε h hne hh m g k p.1 p.2) := by
  have hc := (output_continuous ε hε h hne hh m g k).norm.pow 2
  simpa only [output_actual,timeEnergy_actual] using hc

theorem rate_actual (t : ℝ) (u : 𝒲 0) : rate ε hε h hne hh m g k t u =
    coefficient h*clockResponse ε hε h hne hh m g k t (T 0 t u) (T 0 t u) := by
  simp only [rate,clockResponse,output_actual]

theorem rate_bound (t : ℝ) (u : 𝒲 0) :
    ‖rate ε hε h hne hh m g k t u‖ ≤ 2*timeEnergy ε hε h hne hh m g k t u := by
  apply coefficient_bound h hne
  have hn := response_norm ε hε h hh (output ε hε h hne hh m g k t u) (output ε hε h hne hh m g k t u)
  calc
    _ ≤ 2*|h| * ‖output ε hε h hne hh m g k t u‖*‖output ε hε h hne hh m g k t u‖ := hn
    _ = 2*|h| * timeEnergy ε hε h hne hh m g k t u := by
      rw [mul_assoc,← pow_two,output_actual,timeEnergy_actual]

theorem approxRate_pairing (b : ℝ) (hb : 0 < b) (t : ℝ) (u : 𝒲 0) :
    approxRate ε hε h hne hh m g k b hb t u = coefficient h*
      (inner ℂ (A t (T 0 t u)) (A t (B t b hb (T 0 t u)))-
        inner ℂ (A t (B t b hb (T 0 t u))) (A t (T 0 t u))) := by
  have hp := referenceForm_represents_closed_form ε hε h hne hh m g k t u (B 0 b hb u)
  have ht := congrArg (fun z : 𝒲 t => inner ℂ (A t (T 0 t u)) (A t z))
    (approx_transfer ε hε h hne hh m g k 0 t b hb u)
  have he := congrArg (fun z : ℂ => coefficient h*(z-conj z)) (hp.trans ht.symm)
  simpa only [approxRate,inner_conj_symm] using he

theorem approxRate_smoothing (b : ℝ) (hb : 0 < b) (t : ℝ) (u : 𝒲 0) :
    approxRate ε hε h hne hh m g k b hb t u = rate ε hε h hne hh m g k t (S 0 b hb u) := by
  have hp := congrArg (fun z : ℂ => coefficient h*z)
    (regularized_pairing ε hε h hne hh m g k t b hb (T 0 t u) (T 0 t u))
  have hs := congrArg (fun z : 𝒲 t => coefficient h*clockResponse ε hε h hne hh m g k t z z)
    (smoothing_transfer ε hε h hne hh m g k 0 t b hb u)
  exact (approxRate_pairing ε hε h hne hh m g k b hb t u).trans
    (hp.trans (hs.trans (rate_actual ε hε h hne hh m g k t (S 0 b hb u)).symm))

theorem approxRate_bound (b : ℝ) (hb : 0 < b) (t : ℝ) (u : 𝒲 0) :
    ‖approxRate ε hε h hne hh m g k b hb t u‖ ≤ 8*timeEnergy ε hε h hne hh m g k t u := by
  rw [approxRate_pairing]
  apply coefficient_bound h hne
  have hn := regularized_pairing_bound ε hε h hne hh m g k t b hb (T 0 t u) (T 0 t u)
  calc
    _ ≤ 8*|h| * ‖A t (T 0 t u)‖*‖A t (T 0 t u)‖ := hn
    _ = 8*|h| * timeEnergy ε hε h hne hh m g k t u := by rw [mul_assoc,← pow_two,timeEnergy_actual]

theorem approxRate_tendsto (b : ℕ → ℝ) (hb : ∀ n, 0 < b n) (hz : Tendsto b atTop (𝓝 0))
    (t : ℝ) (u : 𝒲 0) :
    Tendsto (fun n => approxRate ε hε h hne hh m g k (b n) (hb n) t u)
      atTop (𝓝 (rate ε hε h hne hh m g k t u)) := by
  have hs := smoothing_strong ε hε h hne hh m g k 0 b hb atTop hz u
  have hc := (rate_continuous ε hε h hne hh m g k).continuousAt.tendsto.comp ((tendsto_const_nhds (x := t)).prodMk_nhds hs)
  simpa only [approxRate_smoothing] using hc

#print axioms coefficient_bound
#print axioms output_actual
#print axioms output_continuous
#print axioms rate_continuous
#print axioms energy_continuous
#print axioms rate_actual
#print axioms rate_bound
#print axioms approxRate_pairing
#print axioms approxRate_smoothing
#print axioms approxRate_bound
#print axioms approxRate_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorClockReferenceRate
