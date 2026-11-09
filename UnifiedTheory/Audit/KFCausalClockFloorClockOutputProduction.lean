/- Clock production in the actual eight-component energy output.
Only the last three components contribute; a nonzero vacuum output
makes production strictly positive. -/
import UnifiedTheory.Audit.KFCausalClockFloorClockProduction
import UnifiedTheory.Audit.KFCausalClockFloorVacuumOutputFaithful
import UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorClockOutputProduction
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalClockFloorClockOutputForm (deltaOutput deltaOutput_apply)
open UnifiedTheory.Audit.KFCausalClockFloorClockEnergyCommutator (factorDifference)
open UnifiedTheory.Audit.KFCausalClockFloorClockProduction (responseEnergy)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)
local notation "Y" => Output (Fin 8) Hilbert
local notation "P" => KFCausalClockFloorClockProduction.production ε hε h hh

def production (g : Y) : ℝ := (2/h)*(inner ℂ g (deltaOutput ε hε h hh g)).im

def classicalProduction (g : Y) : ℝ := ∑ i : Fin 8, if i.val<5 then 0 else responseEnergy ε hε (g i)

def responseFactor (i : Fin 8) : Hilbert →L[ℂ] Hilbert :=
  if i.val<5 then 0 else KFCausalClockFloorClockProduction.responseAction ε hε

def responseOutput : Y →L[ℂ] Y where
  toFun g := WithLp.toLp 2 (fun i => responseFactor ε hε i (g i))
  map_add' f g := by
    apply PiLp.ext
    intro i
    simp only [PiLp.add_apply,map_add]
  map_smul' c g := by
    apply PiLp.ext
    intro i
    simp only [PiLp.smul_apply,map_smul,RingHom.id_apply]
  cont := (PiLp.continuous_toLp 2 _).comp
    (continuous_pi (fun i => (responseFactor ε hε i).continuous.comp (PiLp.continuous_apply 2 _ i)))

theorem classicalProduction_pairing (g : Y) :
    classicalProduction ε hε g = (inner ℂ g (responseOutput ε hε g)).re := by
  rw [PiLp.inner_apply,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (if i.val<5 then 0 else responseEnergy ε hε (g i)) =
    (inner ℂ (g i) (responseFactor ε hε i (g i))).re
  by_cases hi : i.val<5
  · simp only [responseFactor,hi,if_true,ContinuousLinearMap.zero_apply,inner_zero_right,Complex.zero_re]
  · simp only [responseFactor,hi,if_false,KFCausalClockFloorClockProduction.responseEnergy]

theorem production_sum (g : Y) : production ε hε h hh g = ∑ i : Fin 8, if i.val<5 then 0 else P (g i) := by
  rw [production,PiLp.inner_apply,Complex.im_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val<5
  · simp only [deltaOutput_apply,factorDifference,hi,if_true,ContinuousLinearMap.zero_apply,
      inner_zero_right,Complex.zero_im,mul_zero]
  · simp only [deltaOutput_apply,factorDifference,hi,if_false,KFCausalClockFloorClockProduction.production]

theorem classicalProduction_bounds (g : Y) :
    0 ≤ classicalProduction ε hε g ∧ classicalProduction ε hε g ≤ ‖g‖^2 := by
  constructor
  · apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact le_rfl
    · exact (KFCausalClockFloorClockProduction.responseEnergy_bounds ε hε (g i)).1
  · rw [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · exact sq_nonneg _
    · exact (KFCausalClockFloorClockProduction.responseEnergy_bounds ε hε (g i)).2

include hne in
theorem production_nonnegative (g : Y) : 0 ≤ production ε hε h hh g := by
  rw [production_sum]
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact le_rfl
  · exact KFCausalClockFloorClockProduction.production_nonnegative ε hε h hne hh (g i)

include hne in
theorem production_bounds (g : Y) :
    (1/2)*classicalProduction ε hε g ≤ production ε hε h hh g ∧ production ε hε h hh g ≤ ‖g‖^2 := by
  rw [production_sum,classicalProduction,Finset.mul_sum,PiLp.norm_sq_eq_of_L2]
  constructor
  · apply Finset.sum_le_sum
    intro i _
    split_ifs
    · simp only [mul_zero,le_refl]
    · exact (KFCausalClockFloorClockProduction.production_bounds ε hε h hne hh (g i)).1
  · apply Finset.sum_le_sum
    intro i _
    split_ifs
    · exact sq_nonneg _
    · exact (KFCausalClockFloorClockProduction.production_bounds ε hε h hne hh (g i)).2

include hne in
theorem production_positive (g : Y) (hg : g 7 ≠ 0) : 0 < production ε hε h hh g := by
  rw [production_sum]
  apply Finset.sum_pos'
  · intro i _
    split_ifs
    · exact le_rfl
    · exact KFCausalClockFloorClockProduction.production_nonnegative ε hε h hne hh (g i)
  · refine ⟨7,Finset.mem_univ _,?_⟩
    simpa only [show ¬(7:Fin 8).val<5 by decide,if_false] using
      KFCausalClockFloorClockProduction.production_positive ε hε h hne hh (g 7) hg

theorem classicalProduction_continuous : Continuous (classicalProduction ε hε) := by
  apply continuous_finset_sum
  intro i _
  by_cases hi : i.val<5
  · simpa only [hi,if_true] using (continuous_const (y := (0:ℝ)) : Continuous (fun _ : Y => (0:ℝ)))
  · simpa only [hi,if_false] using (KFCausalClockFloorClockProduction.responseEnergy_continuous ε hε).comp
      (PiLp.continuous_apply 2 _ i)

theorem production_continuous : Continuous (production ε hε h hh) :=
  continuous_const.mul (Complex.continuous_im.comp (continuous_id.inner (deltaOutput ε hε h hh).continuous))

include hne in
theorem form_negative (m g k t : ℝ) (hk : 0 < k)
    (u : KFCausalClosedGraphForm.FormSpace (KFCausalClockFloorFormHamiltonian.formData ε hε h
      (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hh) m g k t))
    (hu : KFCausalClosedGraphForm.embedding (KFCausalClockFloorFormHamiltonian.formData ε hε h
      (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hh) m g k t) u ≠ 0) :
    (-2/h)*(inner ℂ
      (KFCausalClosedGraphForm.energyOutput (KFCausalClockFloorFormHamiltonian.formData ε hε h
        (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hh) m g k t) u)
      (deltaOutput ε hε h hh
        (KFCausalClosedGraphForm.energyOutput (KFCausalClockFloorFormHamiltonian.formData ε hε h
          (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hh) m g k t) u))).im < 0 := by
  have hp := production_positive ε hε h hne hh _
    (KFCausalClockFloorVacuumOutputFaithful.form_vacuum_ne_zero ε hε h _ m g k t hk u hu)
  simpa only [production,neg_div,neg_mul] using neg_neg_of_pos hp

#print axioms production_sum
#print axioms classicalProduction_pairing
#print axioms classicalProduction_bounds
#print axioms production_nonnegative
#print axioms production_bounds
#print axioms production_positive
#print axioms classicalProduction_continuous
#print axioms production_continuous
#print axioms form_negative
end
end UnifiedTheory.Audit.KFCausalClockFloorClockOutputProduction
