/- Continuous coherent orbits in the complete graph-form space of the
actual eight-factor energy. The output formulas are identified with the
operators' graphs before they are used to construct the orbit lift. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoherentMomentumOrbit
import UnifiedTheory.Audit.KFCausalClockFloorCoherentMatterOrbit
import UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoherentFormOrbit
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state action_state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity
open UnifiedTheory.Audit.KFCausalClockFloorCoherentClockMomentum (momentumOutput state_clockMomentum_graph)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMomentumOrbit
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (shiftedOutput state_ordered_graph)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentShiftedOrbit (shiftedOutput_orbit_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMatterOrbit
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (commonEnergyDomain energyFactor)
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy (factorValue jointOutput)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)

def factorOutput (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (hbound : |hbar| ≤ 2*Real.pi*ε/3) (k : Joint 2 4)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) : Fin 8 → Hilbert :=
  ![clockOutput ε a hbar hε ha hh k,
    momentumOutput ε a hbar hε ha hh k (v 0),momentumOutput ε a hbar hε ha hh k (v 1),
    momentumOutput ε a hbar hε ha hh k (v 2),momentumOutput ε a hbar hε ha hh k (v 3),
    linearOutput ε a hbar hε ha hh (-hbar/2) (shift_bound ε hbar hbound) k l,
    quadraticOutput ε a hbar hε ha hh (-hbar/2) (shift_bound ε hbar hbound) k l,
    shiftedOutput ε a hbar hε ha hh hbound k]

theorem factorOutput_graph (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (hbound : |hbar| ≤ 2*Real.pi*ε/3) (k : Joint 2 4)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) :
    (state ε a hbar hε ha hh k,factorOutput ε a hbar hε ha hh hbound k v l i) ∈
      (energyFactor ε hε hbar v l i).graph := by
  fin_cases i
  · exact clockOutput_graph ε a hbar hε ha hh k
  · exact state_clockMomentum_graph ε a hbar hε ha hh k (v 0)
  · exact state_clockMomentum_graph ε a hbar hε ha hh k (v 1)
  · exact state_clockMomentum_graph ε a hbar hε ha hh k (v 2)
  · exact state_clockMomentum_graph ε a hbar hε ha hh k (v 3)
  · exact linearOutput_matter_graph ε a hbar hε ha hh hbound k l
  · exact quadraticOutput_matter_graph ε a hbar hε ha hh hbound k l
  · exact state_ordered_graph ε a hbar hε ha hh hbound k

theorem factorOutput_orbit_continuous (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (hbound : |hbar| ≤ 2*Real.pi*ε/3) (k : Joint 2 4)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) :
    Continuous (fun θ => factorOutput ε a hbar hε ha hh hbound (parameter θ k) v l i) := by
  fin_cases i
  · exact clockOutput_orbit_continuous ε a hbar hε ha hh k
  · exact momentumOutput_orbit_continuous ε a hbar hε ha hh k (v 0)
  · exact momentumOutput_orbit_continuous ε a hbar hε ha hh k (v 1)
  · exact momentumOutput_orbit_continuous ε a hbar hε ha hh k (v 2)
  · exact momentumOutput_orbit_continuous ε a hbar hε ha hh k (v 3)
  · exact linearOutput_orbit_continuous ε a hbar hε ha hh (-hbar/2) (shift_bound ε hbar hbound) k l
  · exact quadraticOutput_orbit_continuous ε a hbar hε ha hh (-hbar/2) (shift_bound ε hbar hbound) k l
  · exact shiftedOutput_orbit_continuous ε a hbar hε ha hh hbound k

theorem factorValue_eq (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (hbound : |hbar| ≤ 2*Real.pi*ε/3) (k : Joint 2 4)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) :
    factorValue ε hε hbar v l
      ⟨state ε a hbar hε ha hh k,state_commonEnergyDomain ε a hbar hε ha hh hbound k v l⟩ i =
        factorOutput ε a hbar hε ha hh hbound k v l i :=
  (energyFactor ε hε hbar v l i).mem_graph_snd_inj'
    ((energyFactor ε hε hbar v l i).mem_graph _)
    (factorOutput_graph ε a hbar hε ha hh hbound k v l i) rfl

theorem jointOutput_eq (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (hbound : |hbar| ≤ 2*Real.pi*ε/3) (k : Joint 2 4)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (mass2 quartic vacuum t : ℝ) :
    jointOutput ε hε hbar v l mass2 quartic vacuum t
      ⟨state ε a hbar hε ha hh k,state_commonEnergyDomain ε a hbar hε ha hh hbound k v l⟩ =
        WithLp.toLp 2 (fun i => energyWeight mass2 quartic vacuum t i •
          factorOutput ε a hbar hε ha hh hbound k v l i) := by
  apply PiLp.ext
  intro i
  exact congrArg (fun f => energyWeight mass2 quartic vacuum t i • f)
    (factorValue_eq ε a hbar hε ha hh hbound k v l i)

theorem jointOutput_orbit_continuous (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (hbound : |hbar| ≤ 2*Real.pi*ε/3) (k : Joint 2 4)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (mass2 quartic vacuum t : ℝ) :
    Continuous (fun θ => jointOutput ε hε hbar v l mass2 quartic vacuum t
      ⟨state ε a hbar hε ha hh (parameter θ k),
        state_commonEnergyDomain ε a hbar hε ha hh hbound (parameter θ k) v l⟩) := by
  have he := funext (fun θ => jointOutput_eq ε a hbar hε ha hh hbound (parameter θ k) v l mass2 quartic vacuum t)
  rw [he]
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 8 => Hilbert)).comp
  exact continuous_pi (fun i => continuous_const.smul
    (factorOutput_orbit_continuous ε a hbar hε ha hh hbound k v l i))

theorem state_orbit_continuous (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) : Continuous (fun θ => state ε a hbar hε ha hh (parameter θ k)) := by
  have he := funext (fun θ => action_state ε a hbar hε ha hh θ k)
  rw [← he]
  exact KFCausalPhysicalCircleAction.action_strong_continuous hbar hh _

theorem formVector_orbit_continuous (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ) (k : Joint 2 4) :
    Continuous (fun θ => formVector ε a hbar hε ha hh hbound mass2 quartic vacuum t (parameter θ k)) := by
  apply Continuous.subtype_mk
  exact (WithLp.prod_continuous_toLp 2 Hilbert (Output (Fin 8) Hilbert)).comp
    ((state_orbit_continuous ε a hbar hε ha hh k).prodMk
      (jointOutput_orbit_continuous ε a hbar hε ha hh hbound k modelDirections pointField mass2 quartic vacuum t))

theorem formVector_orbit_memLp (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ) (k : Joint 2 4) :
    MemLp (fun θ => formVector ε a hbar hε ha hh hbound mass2 quartic vacuum t (parameter (2*Real.pi*θ) k)) 2
      KFCausalUnitIntervalOrbit.angleMeasure :=
  continuous_angle_memLp _ ((formVector_orbit_continuous ε a hbar hε ha hh hbound mass2 quartic vacuum t k).comp
    (continuous_const.mul continuous_id))

#print axioms factorOutput_graph
#print axioms factorOutput_orbit_continuous
#print axioms factorValue_eq
#print axioms jointOutput_eq
#print axioms jointOutput_orbit_continuous
#print axioms state_orbit_continuous
#print axioms formVector_orbit_continuous
#print axioms formVector_orbit_memLp

end
end UnifiedTheory.Audit.KFCausalClockFloorCoherentFormOrbit
