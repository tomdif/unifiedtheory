/- The actual shear output of the shifted coherent state has a continuous
charge orbit and finite integrated squared norm. Continuity follows from
the proved finite expansion into bounded transforms of field outputs. -/
import UnifiedTheory.Audit.KFCausalCoherentShearOutputExpansion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalCoherentShearOrbit
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalCoherentShearOutputExpansion
open UnifiedTheory.Audit.KFCausalCoherentShearPolynomial (coordinate mix scaleOperator)
open UnifiedTheory.Audit.KFCausalCoherentShearMoments
open UnifiedTheory.Audit.KFCausalCoherentShearCompositions (shiftedShearOutput)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter parameter_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (sourceCoefficients)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (sourceCoefficients_continuous continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentShiftedOrbit (shiftedOutput_orbit_continuous)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
variable (hbound : |h| ≤ 2*Real.pi*ε/3)

theorem expandedOutput_orbit_continuous (k : Joint 2 4) :
    Continuous (fun θ => expandedOutput ε a h hε ha hh hbound (parameter θ k)) := by
  let R := scaleOperator ε h hε hbound
  have hp : Continuous (fun θ : ℝ => parameter θ k) :=
    parameter_continuous.comp (f := fun θ : ℝ => (θ,k)) (continuous_id.prodMk continuous_const)
  have hb (i : Fin 5) : Continuous (fun θ => sourceCoefficients h (parameter θ k) i) :=
    (continuous_apply i).comp ((sourceCoefficients_continuous h).comp hp)
  have hL := continuous_finset_sum Finset.univ (fun (i : Fin 4) _ =>
    ((hb i.castSucc).div_const 2).smul (R.continuous.comp
      (linear_orbit_continuous ε a h hε ha hh hbound k (coordinate i.castSucc))))
  have hLm := (hb 4).smul (R.continuous.comp (linear_orbit_continuous ε a h hε ha hh hbound k mix))
  have hQ := (R.continuous.comp (R.continuous.comp
    (continuous_finset_sum Finset.univ (fun (i : Fin 4) _ =>
      quadratic_orbit_continuous ε a h hε ha hh hbound k (coordinate i.castSucc))))).const_smul
        (KFCausalChargeGaussianGeometry.groundWidth h:ℂ)
  have hM := (R.continuous.comp (mixed_orbit_continuous ε a h hε ha hh hbound k)).const_smul
    (2*(KFCausalClockFloorInvariantTrial.neutralWidth h:ℂ))
  have hQm := R.continuous.comp (quadratic_orbit_continuous ε a h hε ha hh hbound k mix)
  have hN := ((R.continuous.comp hQm).sub hQm).const_smul
    (4*(KFCausalClockFloorInvariantTrial.neutralWidth h:ℂ))
  exact (((((shiftedOutput_orbit_continuous ε a h hε ha hh hbound k).add hL).add hLm).sub hQ).sub hM).sub hN
    |>.const_smul (-Complex.I*(h:ℂ))

theorem shiftedShearOutput_orbit_continuous (k : Joint 2 4) :
    Continuous (fun θ => shiftedShearOutput ε a h hε ha hh hbound (parameter θ k)) := by
  simp_rw [← expandedOutput_eq ε a h hε ha hh hbound]
  exact expandedOutput_orbit_continuous ε a h hε ha hh hbound k

theorem shiftedShearOutput_orbit_memLp (k : Joint 2 4) :
    MemLp (fun θ => shiftedShearOutput ε a h hε ha hh hbound (parameter (2*Real.pi*θ) k)) 2 angleMeasure :=
  continuous_angle_memLp _ ((shiftedShearOutput_orbit_continuous ε a h hε ha hh hbound k).comp
    (continuous_const.mul continuous_id))

theorem shiftedShearOutput_square_integrable (k : Joint 2 4) :
    Integrable (fun θ => ‖shiftedShearOutput ε a h hε ha hh hbound (parameter (2*Real.pi*θ) k)‖^2)
      angleMeasure :=
  (memLp_two_iff_integrable_sq_norm
    (shiftedShearOutput_orbit_memLp ε a h hε ha hh hbound k).aestronglyMeasurable).mp
      (shiftedShearOutput_orbit_memLp ε a h hε ha hh hbound k)

#print axioms expandedOutput_orbit_continuous
#print axioms shiftedShearOutput_orbit_continuous
#print axioms shiftedShearOutput_orbit_memLp
#print axioms shiftedShearOutput_square_integrable
end
end UnifiedTheory.Audit.KFCausalCoherentShearOrbit
