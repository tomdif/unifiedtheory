/- Accretivity of the actual selected growing-output action. The first
three rows vanish, the two kinetic rows retain the real radial cutoff,
and the three ordered potential rows have a nonnegative real pairing.
All circle integrals are justified by the actual L2 output vectors. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaReference
import UnifiedTheory.Audit.KFCausalClockFloorAveragedSqueezeEnergy

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaOutputAccretivity
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFiniteJointGraph (Output)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorAveragedSqueezeEnergy (coordinate coordinateLp)
open KFCausalClockFloorRadialYosidaSymbol (action)
open KFCausalClockFloorRadialYosidaOrderedTransport
  (shifted shifted_zero shifted_accretive shift_bound)
open KFCausalClockFloorRadialYosidaEnergy (factorOutput)
open KFCausalClockFloorRadialYosidaReference
  (growingAction growingActionLp growingAction_apply)

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
  (hb : |h| ≤ Real.pi*ε/3)

theorem action_accretive (f : Hilbert) :
    0 ≤ (inner ℂ f (action ε hε h N hN f)).re := by
  have h0 : |(0:ℝ)| ≤ Real.pi*ε/6 := by rw [abs_zero]; positivity
  simpa only [shifted_zero] using shifted_accretive ε hε h N hN 0 h0 f

theorem coordinate_action (y : EnergyOutputSpace) (i : Fin 8) :
    coordinateLp i (growingActionLp ε hε h N hN hb y)=
      if i.val<3 then 0 else
        (factorOutput ε hε h N hN hb i).compLpL 2 angleMeasure (coordinateLp i y) := by
  apply Lp.ext
  filter_upwards [(coordinate i).coeFn_compLp (growingActionLp ε hε h N hN hb y),
    (growingAction ε hε h N hN hb).coeFn_compLp y,
    (coordinate i).coeFn_compLp y,
    (factorOutput ε hε h N hN hb i).coeFn_compLp (coordinateLp i y),
    Lp.coeFn_zero (E := Hilbert) (p := 2) (μ := angleMeasure)]
      with θ h1 h2 h3 h4 h0
  change coordinateLp i (growingActionLp ε hε h N hN hb y) θ=_
  change coordinateLp i (growingActionLp ε hε h N hN hb y) θ=
    growingActionLp ε hε h N hN hb y θ i at h1
  change growingActionLp ε hε h N hN hb y θ=growingAction ε hε h N hN hb (y θ) at h2
  change coordinateLp i y θ=y θ i at h3
  rw [h1,h2,growingAction_apply]
  split_ifs with hi
  · exact h0.symm
  · exact (h4.trans (congrArg (factorOutput ε hε h N hN hb i) h3)).symm

theorem output_pairing_le (y : Output (Fin 8) Hilbert) :
    (inner ℂ (y 3) (growingAction ε hε h N hN hb y 3)+
      inner ℂ (y 4) (growingAction ε hε h N hN hb y 4)).re ≤
      (inner ℂ y (growingAction ε hε h N hN hb y)).re := by
  have h5 := shifted_accretive ε hε h N hN (-h/2) (shift_bound ε h hb) (y 5)
  have h6 := shifted_accretive ε hε h N hN (-h/2) (shift_bound ε h hb) (y 6)
  have h7 := shifted_accretive ε hε h N hN (-h/2) (shift_bound ε h hb) (y 7)
  simp [PiLp.inner_apply,Fin.sum_univ_succ,growingAction_apply,factorOutput,
    Complex.add_re]
  linarith

theorem kinetic_pairing_le (y : EnergyOutputSpace) :
    (inner ℂ (coordinateLp 3 y) (coordinateLp 3 (growingActionLp ε hε h N hN hb y))+
      inner ℂ (coordinateLp 4 y) (coordinateLp 4 (growingActionLp ε hε h N hN hb y))).re ≤
      (inner ℂ y (growingActionLp ε hε h N hN hb y)).re := by
  let z := growingActionLp ε hε h N hN hb y
  have h3 := L2.integrable_inner (𝕜 := ℂ) (coordinateLp 3 y) (coordinateLp 3 z)
  have h4 := L2.integrable_inner (𝕜 := ℂ) (coordinateLp 4 y) (coordinateLp 4 z)
  have hz := L2.integrable_inner (𝕜 := ℂ) y z
  have hi := integral_mono_ae (h3.add h4).re hz.re (by
    filter_upwards [(growingAction ε hε h N hN hb).coeFn_compLp y,
      (coordinate 3).coeFn_compLp y,(coordinate 3).coeFn_compLp z,
      (coordinate 4).coeFn_compLp y,(coordinate 4).coeFn_compLp z]
        with θ hzθ h3y h3z h4y h4z
    change (inner ℂ (coordinateLp 3 y θ) (coordinateLp 3 z θ)+
      inner ℂ (coordinateLp 4 y θ) (coordinateLp 4 z θ)).re ≤
        (inner ℂ (y θ) (z θ)).re
    change z θ=growingAction ε hε h N hN hb (y θ) at hzθ
    change coordinateLp 3 y θ=y θ 3 at h3y
    change coordinateLp 3 z θ=z θ 3 at h3z
    change coordinateLp 4 y θ=y θ 4 at h4y
    change coordinateLp 4 z θ=z θ 4 at h4z
    rw [h3y,h3z,h4y,h4z,hzθ]
    exact output_pairing_le ε hε h N hN hb (y θ))
  rw [integral_re (h3.add h4),integral_re hz] at hi
  change (∫ θ, inner ℂ (coordinateLp 3 y θ) (coordinateLp 3 z θ)+
    inner ℂ (coordinateLp 4 y θ) (coordinateLp 4 z θ) ∂angleMeasure).re ≤
      (∫ θ, inner ℂ (y θ) (z θ) ∂angleMeasure).re at hi
  rw [integral_add h3 h4] at hi
  exact hi

theorem growing_accretive (y : EnergyOutputSpace) :
    0 ≤ (inner ℂ y (growingActionLp ε hε h N hN hb y)).re := by
  have hl := kinetic_pairing_le ε hε h N hN hb y
  have hi (i : Fin 8) :
      0 ≤ (inner ℂ (coordinateLp i y)
        ((action ε hε h N hN).compLpL 2 angleMeasure (coordinateLp i y))).re := by
    let f := coordinateLp i y
    let g := (action ε hε h N hN).compLpL 2 angleMeasure f
    have hj := L2.integrable_inner (𝕜 := ℂ) f g
    have he := integral_re hj
    change (∫ θ, (inner ℂ (f θ) (g θ)).re ∂angleMeasure)=_ at he
    change 0 ≤ (inner ℂ f g).re
    rw [L2.inner_def]
    change 0 ≤ (∫ θ, inner ℂ (f θ) (g θ) ∂angleMeasure).re
    change (∫ θ, (inner ℂ (f θ) (g θ)).re ∂angleMeasure)=
      (∫ θ, inner ℂ (f θ) (g θ) ∂angleMeasure).re at he
    rw [← he]
    apply integral_nonneg_of_ae
    filter_upwards [(action ε hε h N hN).coeFn_compLp f] with θ hθ
    change 0 ≤ (inner ℂ (f θ) (g θ)).re
    change g θ=action ε hε h N hN (f θ) at hθ
    rw [hθ]
    exact action_accretive ε hε h N hN (f θ)
  rw [coordinate_action,coordinate_action] at hl
  norm_num [factorOutput,Complex.add_re] at hl
  change (inner ℂ (coordinateLp 3 y)
    ((action ε hε h N hN).compLpL 2 angleMeasure (coordinateLp 3 y))).re+
      (inner ℂ (coordinateLp 4 y)
        ((action ε hε h N hN).compLpL 2 angleMeasure (coordinateLp 4 y))).re ≤ _ at hl
  linarith [hi 3,hi 4]

#print axioms action_accretive
#print axioms coordinate_action
#print axioms output_pairing_le
#print axioms kinetic_pairing_le
#print axioms growing_accretive
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaOutputAccretivity
