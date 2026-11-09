/- Exact squeeze energy and its derivative on the full completed averaged
form. All eight angle-dependent outputs are retained. This is a variation
in the squeeze parameter, not yet a virial law along physical time. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedSqueeze

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedSqueezeEnergy
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalAveragedEnergyGraph (l2_norm_square)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeEnergy (degree outputAction outputAction_norm_square)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalClockFloorAveragedSqueeze

abbrev OutputSpace := Lp (Output (Fin 8) Hilbert) 2 angleMeasure
abbrev CoordinateSpace := Lp Hilbert 2 angleMeasure

def coordinate (i : Fin 8) : Output (Fin 8) Hilbert →L[ℂ] Hilbert :=
  PiLp.proj 2 (fun _ : Fin 8 => Hilbert) i

def coordinateLp (i : Fin 8) : OutputSpace →L[ℂ] CoordinateSpace :=
  (coordinate i).compLpL 2 angleMeasure

def outputLp (a : ℝ) : OutputSpace →L[ℂ] OutputSpace :=
  (outputAction a).compLpL 2 angleMeasure

theorem outputLp_norm_square (a : ℝ) (g : OutputSpace) :
    ‖outputLp a g‖^2 = ∑ i : Fin 8, Real.exp (2*degree i*a)*‖coordinateLp i g‖^2 := by
  have he : (fun θ => ‖outputLp a g θ‖^2) =ᵐ[angleMeasure]
      fun θ => ∑ i : Fin 8, Real.exp (2*degree i*a)*‖coordinateLp i g θ‖^2 := by
    filter_upwards [(outputAction a).coeFn_compLp g,
      ae_all_iff.mpr (fun i : Fin 8 => (coordinate i).coeFn_compLp g)] with θ ho hc
    change ‖(outputAction a).compLp g θ‖^2 = _
    rw [ho,outputAction_norm_square]
    apply Finset.sum_congr rfl
    intro i _
    have hi : coordinateLp i g θ = g θ i := hc i
    rw [hi]
  have hi (i : Fin 8) : Integrable (fun θ => ‖coordinateLp i g θ‖^2) angleMeasure :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  rw [l2_norm_square angleMeasure (outputLp a g),integral_congr_ae he,
    integral_finset_sum Finset.univ (fun i _ => (hi i).const_mul _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul,← l2_norm_square]

theorem outputLp_norm_derivative (a : ℝ) (g : OutputSpace) :
    HasDerivAt (fun b => ‖outputLp b g‖^2)
      (∑ i : Fin 8, Real.exp (2*degree i*a)*(2*degree i)*‖coordinateLp i g‖^2) a := by
  have hi (i : Fin 8) :
      HasDerivAt (fun b => Real.exp (2*degree i*b)*‖coordinateLp i g‖^2)
        (Real.exp (2*degree i*a)*(2*degree i)*‖coordinateLp i g‖^2) a := by
    simpa only [id_eq,mul_one] using
      (((hasDerivAt_id a).const_mul (2*degree i)).exp.mul_const (‖coordinateLp i g‖^2))
  simpa only [outputLp_norm_square] using
    (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i))

def variation (g : OutputSpace) : ℝ :=
  2*(-‖coordinateLp 1 g‖^2-‖coordinateLp 2 g‖^2+
    ‖coordinateLp 3 g‖^2+‖coordinateLp 4 g‖^2+‖coordinateLp 5 g‖^2+2*‖coordinateLp 6 g‖^2)

theorem outputLp_norm_derivative_zero (g : OutputSpace) :
    HasDerivAt (fun b => ‖outputLp b g‖^2) (variation g) 0 := by
  convert outputLp_norm_derivative 0 g using 1
  simp [degree,variation,Fin.sum_univ_succ]
  ring

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hb : |h| ≤ Real.pi*ε)
  (m q k t : ℝ)
local notation "V" => AveragedSpace ε hε h hb hne m q k t
local notation "A" => energyOutput ε hε h hb hne m q k t

theorem full_energy_identity (a : ℝ) (u : V) :
    ‖A (averagedAction ε hε h hne hb m q k t a u)‖^2 =
      ∑ i : Fin 8, Real.exp (2*degree i*a)*‖coordinateLp i (A u)‖^2 := by
  have he : A (averagedAction ε hε h hne hb m q k t a u) = outputLp a (A u) :=
    averaged_output ε hε h hne hb m q k t a u
  exact (congrArg (fun z : OutputSpace => ‖z‖^2) he).trans (outputLp_norm_square a (A u))

theorem full_energy_variation (u : V) :
    HasDerivAt (fun a => ‖A (averagedAction ε hε h hne hb m q k t a u)‖^2)
      (variation (A u)) 0 := by
  have he : (fun a => ‖A (averagedAction ε hε h hne hb m q k t a u)‖^2) =
      (fun a => ‖outputLp a (A u)‖^2) := by
    funext a
    have ho : A (averagedAction ε hε h hne hb m q k t a u) = outputLp a (A u) :=
      averaged_output ε hε h hne hb m q k t a u
    exact congrArg (fun z : OutputSpace => ‖z‖^2) ho
  exact (outputLp_norm_derivative_zero (A u)).congr_of_eventuallyEq (Filter.EventuallyEq.of_eq he)

#print axioms outputLp_norm_square
#print axioms outputLp_norm_derivative
#print axioms outputLp_norm_derivative_zero
#print axioms full_energy_identity
#print axioms full_energy_variation

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedSqueezeEnergy
