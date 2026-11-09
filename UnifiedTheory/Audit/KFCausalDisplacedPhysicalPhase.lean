/- The physical phase coordinates of the actual displaced packets. The
translation parameters are the negatives of the position centres. The
state orbit follows the inverse classical rotation, as required for a
pullback action. This is a coordinate identity, not a quantum limit. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources
import UnifiedTheory.Audit.KFCausalClassicalPhysicalPhase

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalDisplacedPhysicalPhase
noncomputable section
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow (momentumScale)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources
open UnifiedTheory.Audit.KFCausalDisplacedBoostParameters
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalClassicalChargePhase (Phase rotate)
open UnifiedTheory.Audit.KFCausalClassicalPhysicalPhase (toPaired)

def phase (h : ℝ) (q k : Joint 2 4) : Phase :=
  (WithLp.toLp 2 (fun
    | .inl i => -(momentumScale h)*k (.inl i)
    | .inr i => -q (.inr i)),
   WithLp.toLp 2 (fun
    | .inl i => -q (.inl i)
    | .inr i => momentumScale h*k (.inr i)))

theorem position_antisymmetric (h : ℝ) (q k : Joint 2 4) (i : Fin 2) :
    (phase h q k).1 (.inl i) = -vParameter h k i := by
  change -(momentumScale h)*k (.inl i) = -(momentumScale h*k (.inl i))
  ring

theorem position_spectator (h : ℝ) (q k : Joint 2 4) (i : Fin 4) :
    (phase h q k).1 (.inr i) = -wParameter h q i := rfl

theorem momentum_antisymmetric (h : ℝ) (hh : h ≠ 0) (q k : Joint 2 4) (i : Fin 2) :
    (phase h q k).2 (.inl i) = momentumScale h*uParameter h q i := by
  change -q (.inl i) = momentumScale h*(-((momentumScale h)⁻¹*q (.inl i)))
  field_simp [KFCausalNormalizedChargeFlow.momentumScale_ne_zero h hh]

theorem momentum_spectator (h : ℝ) (q k : Joint 2 4) (i : Fin 4) :
    (phase h q k).2 (.inr i) = momentumScale h*rParameter h k i := rfl

theorem phase_parameter (h θ : ℝ) (q k : Joint 2 4) :
    phase h (parameter θ q) (parameter θ k) = rotate (-θ) (phase h q k) := by
  ext i <;> rcases i with i | i <;> fin_cases i <;>
    simp [phase,parameter,KFCausalPairedRotation.rotate,rotate] <;> ring

theorem phase_boost (h : ℝ) (hh : h ≠ 0) (p : Configuration) :
    phase h (boostQ h (h⁻¹ • p)) (boostK (h⁻¹ • p)) = (0,toPaired p) := by
  ext i <;> rcases i with i | i <;> fin_cases i <;>
    simp [phase,boostQ,boostK,antisymmetricFrequency,spectatorFrequency,momentumScale,
      toPaired,KFCausalClassicalPhysicalPhase.flatten,KFCausalPairedModeCoordinates.modeIsometry,
      KFCausalPairedModeCoordinates.modeEquiv,KFCausalPairedModeCoordinates.forward,
      Fin.cons,Fin.cases]
  all_goals norm_num [Fin.induction,Fin.induction.go]
  all_goals field_simp [hh] <;> ring_nf
  all_goals congr 1

theorem phase_boost_orbit (h : ℝ) (hh : h ≠ 0) (p : Configuration) (θ : ℝ) :
    phase h (parameter θ (boostQ h (h⁻¹ • p))) (parameter θ (boostK (h⁻¹ • p))) =
      rotate (-θ) (0,toPaired p) := by
  rw [phase_parameter,phase_boost h hh]

theorem phase_boost_orbit_independent (h h' : ℝ) (hh : h ≠ 0) (hh' : h' ≠ 0)
    (p : Configuration) (θ : ℝ) :
    phase h (parameter θ (boostQ h (h⁻¹ • p))) (parameter θ (boostK (h⁻¹ • p))) =
      phase h' (parameter θ (boostQ h' (h'⁻¹ • p))) (parameter θ (boostK (h'⁻¹ • p))) := by
  rw [phase_boost_orbit h hh,phase_boost_orbit h' hh']

#print axioms position_antisymmetric
#print axioms position_spectator
#print axioms momentum_antisymmetric
#print axioms momentum_spectator
#print axioms phase_parameter
#print axioms phase_boost
#print axioms phase_boost_orbit
#print axioms phase_boost_orbit_independent

end
end UnifiedTheory.Audit.KFCausalDisplacedPhysicalPhase
