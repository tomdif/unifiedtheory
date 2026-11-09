/- The full eight-factor output has a strictly negative exact defect rate
whenever its vacuum component is nonzero. The actual closed graph supplies
that nonvanishing for every nonzero physical state at positive coupling. -/
import UnifiedTheory.Audit.KFCausalClockFloorStrictDefectSign
import UnifiedTheory.Audit.KFCausalStrictMultiplierPairing
import UnifiedTheory.Audit.KFCausalClockFloorVacuumOutputFaithful
import UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityOutput
import UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorStrictOutputRate
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect (shiftedDefect)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical
open UnifiedTheory.Audit.KFCausalClockFloorStrictDefectSign
open UnifiedTheory.Audit.KFCausalStrictMultiplierPairing
open UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityPairing (defect_inner_im_zero)
open UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction
open UnifiedTheory.Audit.KFCausalClockFloorVacuumOutputFaithful

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3)

include hh

theorem shifted_rate_nonpositive (f : Hilbert) :
    (-2/hbar)*(inner ℂ f (shiftedDefect ε hε hbar hb f)).im ≤ 0 :=
  multiplier_pairing_nonpositive volume (physicalSymbol ε hbar) (-2/hbar) f _
    (shiftedDefect_physical_coe ε hε hbar hb f)
    (fun x => (physicalSymbol_velocity_negative ε hbar hε hh hb x).le)

theorem shifted_rate_negative (f : Hilbert) (hf : f ≠ 0) :
    (-2/hbar)*(inner ℂ f (shiftedDefect ε hε hbar hb f)).im < 0 :=
  multiplier_pairing_negative volume (physicalSymbol ε hbar) (-2/hbar) f _
    (shiftedDefect_physical_coe ε hε hbar hb f)
    (physicalSymbol_velocity_negative ε hbar hε hh hb) hf

theorem factor_rate_nonpositive (i : Fin 8) (f : Hilbert) :
    (-2/hbar)*(inner ℂ f (factorAction ε hε hbar hb i f)).im ≤ 0 := by
  unfold factorAction
  split
  · rw [defect_inner_im_zero ε hε,mul_zero]
  · exact shifted_rate_nonpositive ε hε hbar hh hb f

theorem output_rate_negative (g : Output (Fin 8) Hilbert) (hg : g 7 ≠ 0) :
    (-2/hbar)*(inner ℂ g (outputAction ε hε hbar hb g)).im < 0 := by
  rw [PiLp.inner_apply,Complex.im_sum,Finset.mul_sum]
  have he : (-2/hbar)*(inner ℂ (g 7) (factorAction ε hε hbar hb 7 (g 7))).im < 0 :=
    shifted_rate_negative ε hε hbar hh hb (g 7) hg
  have hs := Finset.sum_lt_sum (s := Finset.univ)
    (fun i _ => factor_rate_nonpositive ε hε hbar hh hb i (g i))
    ⟨7,Finset.mem_univ 7,he⟩
  simpa only [Finset.sum_const_zero] using hs

theorem form_rate_negative (mass2 quartic vacuum t : ℝ) (hv : 0 < vacuum)
    (u : KFCausalClosedGraphForm.FormSpace
      (KFCausalClockFloorFormHamiltonian.formData ε hε hbar
        (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε hbar hb) mass2 quartic vacuum t))
    (hu : KFCausalClosedGraphForm.embedding
      (KFCausalClockFloorFormHamiltonian.formData ε hε hbar
        (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε hbar hb) mass2 quartic vacuum t) u ≠ 0) :
    (-2/hbar)*(inner ℂ
      (KFCausalClosedGraphForm.energyOutput (KFCausalClockFloorFormHamiltonian.formData ε hε hbar
        (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε hbar hb) mass2 quartic vacuum t) u)
      (outputAction ε hε hbar hb
        (KFCausalClosedGraphForm.energyOutput (KFCausalClockFloorFormHamiltonian.formData ε hε hbar
          (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε hbar hb) mass2 quartic vacuum t) u))).im < 0 :=
  output_rate_negative ε hε hbar hh hb _ (form_vacuum_ne_zero ε hε hbar _ mass2 quartic vacuum t hv u hu)

omit hh in
theorem shifted_square_coe (f : Hilbert) :
    shiftedDefect ε hε hbar hb (shiftedDefect ε hε hbar hb f) =ᵐ[volume]
      fun x => physicalSymbol ε hbar x^2*f x := by
  filter_upwards [shiftedDefect_physical_coe ε hε hbar hb (shiftedDefect ε hε hbar hb f),
    shiftedDefect_physical_coe ε hε hbar hb f] with x h2 h1
  rw [h2,h1,pow_two,mul_assoc]

theorem shifted_square_rate_nonpositive (f : Hilbert) :
    (-2/hbar)*(inner ℂ f (shiftedDefect ε hε hbar hb (shiftedDefect ε hε hbar hb f))).im ≤ 0 :=
  multiplier_pairing_nonpositive volume (fun x => physicalSymbol ε hbar x^2) (-2/hbar) f _
    (shifted_square_coe ε hε hbar hb f)
    (fun x => (physicalSymbol_square_velocity_negative ε hbar hε hh hb x).le)

theorem shifted_square_rate_negative (f : Hilbert) (hf : f ≠ 0) :
    (-2/hbar)*(inner ℂ f (shiftedDefect ε hε hbar hb (shiftedDefect ε hε hbar hb f))).im < 0 :=
  multiplier_pairing_negative volume (fun x => physicalSymbol ε hbar x^2) (-2/hbar) f _
    (shifted_square_coe ε hε hbar hb f)
    (physicalSymbol_square_velocity_negative ε hbar hε hh hb) hf

theorem factor_square_rate_nonpositive (i : Fin 8) (f : Hilbert) :
    (-2/hbar)*(inner ℂ f (factorAction ε hε hbar hb i (factorAction ε hε hbar hb i f))).im ≤ 0 := by
  unfold factorAction
  split
  · rw [KFCausalClockFloorDefectForm.defect_square_inner_im_zero ε hε,mul_zero]
  · exact shifted_square_rate_nonpositive ε hε hbar hh hb f

theorem output_square_rate_negative (g : Output (Fin 8) Hilbert) (hg : g 7 ≠ 0) :
    (-2/hbar)*(inner ℂ g (outputAction ε hε hbar hb (outputAction ε hε hbar hb g))).im < 0 := by
  rw [PiLp.inner_apply,Complex.im_sum,Finset.mul_sum]
  have he : (-2/hbar)*(inner ℂ (g 7)
      (factorAction ε hε hbar hb 7 (factorAction ε hε hbar hb 7 (g 7)))).im < 0 :=
    shifted_square_rate_negative ε hε hbar hh hb (g 7) hg
  have hs := Finset.sum_lt_sum (s := Finset.univ)
    (fun i _ => factor_square_rate_nonpositive ε hε hbar hh hb i (g i))
    ⟨7,Finset.mem_univ 7,he⟩
  simpa only [Finset.sum_const_zero] using hs

#print axioms shifted_square_coe
#print axioms shifted_square_rate_nonpositive
#print axioms shifted_square_rate_negative
#print axioms factor_square_rate_nonpositive
#print axioms output_square_rate_negative

#print axioms shifted_rate_nonpositive
#print axioms shifted_rate_negative
#print axioms factor_rate_nonpositive
#print axioms output_rate_negative
#print axioms form_rate_negative

end
end UnifiedTheory.Audit.KFCausalClockFloorStrictOutputRate
