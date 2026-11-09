/- The exact clock/neutral-frequency multiplier on separable spectator states. -/
import UnifiedTheory.Audit.KFCausalPhysicalSpectatorPackets

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalSpectatorEnergyPackets
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates
open KFCausalPhysicalSpectatorPackets (one)
open KFCausalJoinedMultiplierSum (joinProduct)
open KFCausalJoinedFourierProduct (separate separate_preserves)
open KFCausalClockFloorFlow (clock)

def energy (ε c a : ℝ) (x : Block 2) : ℝ :=
  clock ε (x 0)/2 + a/clock ε (x 0)+c^2*x 1^2/(2*clock ε (x 0))

theorem energy_continuous (ε : ℝ) (hε : 0 < ε) (c a : ℝ) : Continuous (energy ε c a) := by
  unfold energy clock
  fun_prop (disch := intro x; positivity)

def output (c a : ℝ) (uC uInv v v2 : BlockHilbert 1) : BlockHilbert 2 :=
  (1/2:ℂ) • joinProduct 1 1 uC v + (a:ℂ) • joinProduct 1 1 uInv v +
    ((c^2/2:ℝ):ℂ) • joinProduct 1 1 uInv v2

theorem joined_coe (u v : BlockHilbert 1) :
    joinProduct 1 1 u v =ᵐ[volume] fun x => u (one (x 0))*v (one (x 1)) := by
  filter_upwards [KFCausalJoinedFourierProduct.join_product_coe 1 1 u v] with x hx
  have hs : separate 1 1 x = (one (x 0),one (x 1)) := by
    apply Prod.ext <;> ext j <;> fin_cases j <;> rfl
  exact hx.trans (by rw [hs])

theorem output_coe (ε c a : ℝ) (u uC uInv v v2 : BlockHilbert 1)
    (huC : uC =ᵐ[volume] fun s => (clock ε (s 0):ℂ)*u s)
    (hu : uInv =ᵐ[volume] fun s => ((clock ε (s 0))⁻¹:ℂ)*u s)
    (hv : v2 =ᵐ[volume] fun x => (x 0:ℂ)^2*v x) :
    output c a uC uInv v v2 =ᵐ[volume] fun x =>
      (energy ε c a x:ℂ)*(joinProduct 1 1 u v) x := by
  have huC' := (Measure.quasiMeasurePreserving_fst.comp
    (separate_preserves 1 1).quasiMeasurePreserving).ae huC
  have hu' := (Measure.quasiMeasurePreserving_fst.comp
    (separate_preserves 1 1).quasiMeasurePreserving).ae hu
  have hv' := (Measure.quasiMeasurePreserving_snd.comp
    (separate_preserves 1 1).quasiMeasurePreserving).ae hv
  let A := (1/2:ℂ) • joinProduct 1 1 uC v
  let D := (a:ℂ) • joinProduct 1 1 uInv v
  let E := ((c^2/2:ℝ):ℂ) • joinProduct 1 1 uInv v2
  filter_upwards [Lp.coeFn_add (A+D) E, Lp.coeFn_add A D,
    Lp.coeFn_smul (1/2:ℂ) (joinProduct 1 1 uC v),
    Lp.coeFn_smul (a:ℂ) (joinProduct 1 1 uInv v),
    Lp.coeFn_smul (((c^2/2:ℝ):ℂ)) (joinProduct 1 1 uInv v2),
    joined_coe uC v, joined_coe uInv v, joined_coe uInv v2, joined_coe u v,
    huC', hu', hv'] with x hs hs' hA hD hE h1 h2 h3 h4 huC' hu' hv'
  have hsep : separate 1 1 x = (one (x 0),one (x 1)) := by
    apply Prod.ext <;> ext j <;> fin_cases j <;> rfl
  simp only [Function.comp_apply, hsep] at huC' hu' hv'
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  change (A+D+E) x = _
  rw [hs, hs']
  dsimp only [A,D,E]
  rw [hA,hD,hE,h1,h2,h3,h4,huC',hu',hv']
  simp only [energy, one, Matrix.cons_val_zero]
  push_cast
  ring

#print axioms output_coe
end
end UnifiedTheory.Audit.KFCausalSpectatorEnergyPackets
