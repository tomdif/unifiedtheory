/- Exact chart-phase coordinates for the full completed averaged energy.
The ordered matter and vacuum weights become time independent. Only the
two transverse kinetic weights retain exp(2*t) in the quadratic form.
This is an energy-form identity, not a transformed evolution equation. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedChartModulation
import UnifiedTheory.Audit.KFCausalClockFloorAveragedOutputTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGaugeEnergy
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalFiniteOutputRescaling (selected selected_apply)
open UnifiedTheory.Audit.KFCausalClockFloorChartModulation (modulation)
open UnifiedTheory.Audit.KFCausalClockFloorFactorChartModulation (factorScale)
open UnifiedTheory.Audit.KFCausalClockFloorClosedChartModulation (outputAction outputAction_apply)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyTransport (timeOutput timeOutput_apply)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedOutputTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)

def rate (h t : ℝ) : ℝ := -t/(Real.pi*h)

def kinetic (i : Fin 8) : Prop := 3 ≤ i.val ∧ i.val < 5
instance : DecidablePred kinetic := fun i => inferInstanceAs (Decidable (3 ≤ i.val ∧ i.val < 5))

def kineticOutput : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert := selected kinetic
def fixedOutput : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert := selected (fun i => ¬ kinetic i)
def gaugeOutput (ε h t : ℝ) : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert :=
  (outputAction ε h (rate h t)).comp (timeOutput 0 t)

abbrev EnergyOutputSpace := Lp (Output (Fin 8) Hilbert) 2 angleMeasure
def kineticOutputLp : EnergyOutputSpace →L[ℂ] EnergyOutputSpace := kineticOutput.compLpL 2 angleMeasure
def fixedOutputLp : EnergyOutputSpace →L[ℂ] EnergyOutputSpace := fixedOutput.compLpL 2 angleMeasure
def gaugeOutputLp (ε h t : ℝ) : EnergyOutputSpace →L[ℂ] EnergyOutputSpace :=
  (gaugeOutput ε h t).compLpL 2 angleMeasure

theorem rate_scale (h t : ℝ) (hne : h ≠ 0) : Real.pi*h*rate h t = -t := by
  unfold rate
  field_simp

theorem gaugeOutput_apply (ε h t : ℝ) (hne : h ≠ 0) (g : Output (Fin 8) Hilbert) (i : Fin 8) :
    gaugeOutput ε h t g i = if kinetic i then
      (Real.exp t : ℂ) • modulation ε (rate h t) (g i) else modulation ε (rate h t) (g i) := by
  change outputAction ε h (rate h t) (timeOutput 0 t g) i = _
  rw [outputAction_apply,timeOutput_apply]
  have he : (Real.exp (-t) : ℂ) * (Real.exp t : ℂ) = 1 := by
    rw [← Complex.ofReal_mul,← Real.exp_add,neg_add_cancel,Real.exp_zero,Complex.ofReal_one]
  by_cases h3 : i.val < 3
  · have h5 : i.val < 5 := by omega
    have hk : ¬ kinetic i := by simp only [kinetic]; omega
    simp only [factorScale,h3,h5,hk,if_true,if_false,one_smul]
  · by_cases h5 : i.val < 5
    · have hk : kinetic i := ⟨by omega,h5⟩
      simp only [factorScale,h3,h5,hk,if_true,if_false,one_smul,map_smul,sub_zero]
    · have hk : ¬ kinetic i := by simp only [kinetic]; omega
      simp only [factorScale,h3,h5,hk,if_false,map_smul,sub_zero,
        rate_scale h t hne,smul_smul,he,one_smul]

theorem gaugeOutput_norm_square (ε h t : ℝ) (hne : h ≠ 0) (g : Output (Fin 8) Hilbert) :
    ‖gaugeOutput ε h t g‖^2 = ‖fixedOutput g‖^2+Real.exp (2*t)*‖kineticOutput g‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,
    Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : kinetic i
  · simp only [gaugeOutput_apply ε h t hne,hi,if_true,fixedOutput,kineticOutput,selected_apply,
      not_true_eq_false,if_false,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_add,
      norm_smul,LinearIsometryEquiv.norm_map,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _),mul_pow,← Real.exp_nat_mul,Nat.cast_ofNat]
  · simp only [gaugeOutput_apply ε h t hne,hi,if_false,fixedOutput,kineticOutput,selected_apply,
      not_false_eq_true,if_true,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero,add_zero,
      LinearIsometryEquiv.norm_map]

theorem gaugeOutputLp_norm_square (ε h t : ℝ) (hne : h ≠ 0) (g : EnergyOutputSpace) :
    ‖gaugeOutputLp ε h t g‖^2 = ‖fixedOutputLp g‖^2+Real.exp (2*t)*‖kineticOutputLp g‖^2 := by
  have he : (fun θ => ‖gaugeOutputLp ε h t g θ‖^2) =ᵐ[angleMeasure]
      fun θ => ‖fixedOutputLp g θ‖^2+Real.exp (2*t)*‖kineticOutputLp g θ‖^2 := by
    filter_upwards [(gaugeOutput ε h t).coeFn_compLp g,fixedOutput.coeFn_compLp g,
      kineticOutput.coeFn_compLp g] with θ h1 h2 h3
    change ‖(gaugeOutput ε h t).compLp g θ‖^2 =
      ‖fixedOutput.compLp g θ‖^2+Real.exp (2*t)*‖kineticOutput.compLp g θ‖^2
    rw [h1,h2,h3,gaugeOutput_norm_square ε h t hne]
  have hf : Integrable (fun θ => ‖fixedOutputLp g θ‖^2) angleMeasure :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have hk : Integrable (fun θ => ‖kineticOutputLp g θ‖^2) angleMeasure :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  rw [l2_norm_square angleMeasure (gaugeOutputLp ε h t g),integral_congr_ae he,
    integral_add hf (hk.const_mul _),integral_const_mul,← l2_norm_square,← l2_norm_square]

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hb : |h| ≤ Real.pi*ε) (m q k t : ℝ)

theorem energy_graph (f : Hilbert) (g : EnergyOutputSpace)
    (hfg : (f,g) ∈ (energyOperator ε hε h hb hne m q k 0).graph) :
    (modulation ε (rate h t) f,gaugeOutputLp ε h t g) ∈
      (energyOperator ε hε h hb hne m q k t).graph := by
  have ht := energy_graph_transport ε hε h hb hne m q k 0 t (f,g) hfg
  have hm := KFCausalClockFloorAveragedChartModulation.averaged_graph ε hε h hne hb m q k t
    (rate h t) f (timeOutputLp 0 t g) ht
  have he : (outputAction ε h (rate h t)).compLp (timeOutputLp 0 t g) = gaugeOutputLp ε h t g := by
    apply Lp.ext
    filter_upwards [(outputAction ε h (rate h t)).coeFn_compLp (timeOutputLp 0 t g),
      (timeOutput 0 t).coeFn_compLp g,(gaugeOutput ε h t).coeFn_compLp g] with θ h1 h2 h3
    change (outputAction ε h (rate h t)).compLp (timeOutputLp 0 t g) θ =
      (gaugeOutput ε h t).compLp g θ
    rw [h1,h3]
    change outputAction ε h (rate h t) ((timeOutput 0 t).compLp g θ) = _
    rw [h2]
    rfl
  rwa [he] at hm

theorem full_energy_identity (u : AveragedSpace ε hε h hb hne m q k 0) :
    ∃ g : EnergyOutputSpace,
      (modulation ε (rate h t) (embedding ε hε h hb hne m q k 0 u),g) ∈
        (energyOperator ε hε h hb hne m q k t).graph ∧
      ‖g‖^2 = ‖fixedOutputLp (energyOutput ε hε h hb hne m q k 0 u)‖^2+
        Real.exp (2*t)*‖kineticOutputLp (energyOutput ε hε h hb hne m q k 0 u)‖^2 := by
  refine ⟨gaugeOutputLp ε h t (energyOutput ε hε h hb hne m q k 0 u),?_,?_⟩
  · exact energy_graph ε hε h hne hb m q k t _ _ (energy_form_graph ε hε h hb hne m q k 0 u)
  · exact gaugeOutputLp_norm_square ε h t hne _

#print axioms rate_scale
#print axioms gaugeOutput_apply
#print axioms gaugeOutput_norm_square
#print axioms gaugeOutputLp_norm_square
#print axioms energy_graph
#print axioms full_energy_identity
end
end UnifiedTheory.Audit.KFCausalClockFloorGaugeEnergy
