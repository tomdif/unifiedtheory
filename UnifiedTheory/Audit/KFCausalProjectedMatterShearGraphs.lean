/- Closed-graph charge integration for the two field powers, their
weighted shear outputs and the explicit field-shear commutator. -/
import UnifiedTheory.Audit.KFCausalStructuredPolynomialShearOrbit

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalProjectedMatterShearGraphs
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse (StructuredState)
open UnifiedTheory.Audit.KFCausalPolynomialImaginaryShearCurve (Weight fieldWeight slopeWeight)
open UnifiedTheory.Audit.KFCausalStructuredPolynomialShearOrbit
  (weightedInput weightedFirst weighted_continuous angle_continuous field_graph first_field_graph corrected_shear_graph)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalStructuredShearMean (meanInputAt meanShearAt)
open UnifiedTheory.Audit.KFCausalProjectedKineticResponse (integral_closed_graph)

theorem fieldPower_closed (l : Transverse →L[ℝ] ℝ) (i : Fin 2) : (fieldPower l i).IsClosed := by
  fin_cases i
  · exact KFCausalPhysicalField.physicalField_closed l
  · exact (KFCausalTransverseFieldSquare.fieldSquare_selfAdjoint l).isClosed

private theorem compact_mean_continuous (f : ℝ → ℝ → Hilbert)
    (hf : Continuous (fun v : ℝ × Interval => f v.1 v.2)) :
    Continuous (fun t : Interval => ∫ θ, f (2*Real.pi*θ) t ∂angleMeasure) := by
  have hs : Continuous (fun v : Interval × ℝ => (2*Real.pi*v.2,v.1)) :=
    (continuous_const.mul continuous_snd).prodMk continuous_fst
  have ht : Continuous (Function.uncurry (fun (t : Interval) (θ : ℝ) => f (2*Real.pi*θ) t)) := hf.comp hs
  have hc := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun (t : Interval) (θ : ℝ) => f (2*Real.pi*θ) t)
    ht
    (isCompact_Icc : IsCompact (Icc (0:ℝ) 1))
  simpa only [integral_Icc_eq_integral_Ioc,angleMeasure] using hc

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (S : StructuredState)

def meanWeightedInput (P : Weight) (t : ℝ) : Hilbert :=
  ∫ θ, weightedInput ε h hε hh hb S P (2*Real.pi*θ) t ∂angleMeasure
def meanWeightedFirst (P : Weight) (t : ℝ) : Hilbert :=
  ∫ θ, weightedFirst ε h hε hh hb S P (2*Real.pi*θ) t ∂angleMeasure

theorem mean_continuous (P : Weight) :
    Continuous (fun t : Interval => meanWeightedInput ε h hε hh hb S P t) ∧
    Continuous (fun t : Interval => meanWeightedFirst ε h hε hh hb S P t) :=
  ⟨compact_mean_continuous _ (weighted_continuous ε h hε hh hb S P).1,
    compact_mean_continuous _ (weighted_continuous ε h hε hh hb S P).2⟩

theorem mean_field_graph (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (t : Interval) :
    (meanInputAt ε h hε hh hb S t,meanWeightedInput ε h hε hh hb S (fieldWeight l i) t) ∈
      (fieldPower l i).graph :=
  integral_closed_graph _ (fieldPower_closed l i) _ _
    ((KFCausalStructuredShearMean.angle_continuous ε h hε hh hb S t).1.comp (continuous_const.mul continuous_id))
    ((angle_continuous ε h hε hh hb S (fieldWeight l i) t).1.comp (continuous_const.mul continuous_id))
    (fun θ => field_graph ε h hε hh hb S l i (2*Real.pi*θ) t)

theorem mean_first_field_graph (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (t : Interval) :
    (meanShearAt ε h hε hh hb S t,meanWeightedFirst ε h hε hh hb S (fieldWeight l i) t) ∈
      (fieldPower l i).graph :=
  integral_closed_graph _ (fieldPower_closed l i) _ _
    ((KFCausalStructuredShearMean.angle_continuous ε h hε hh hb S t).2.comp (continuous_const.mul continuous_id))
    ((angle_continuous ε h hε hh hb S (fieldWeight l i) t).2.comp (continuous_const.mul continuous_id))
    (fun θ => first_field_graph ε h hε hh hb S l i (2*Real.pi*θ) t)

theorem mean_corrected_shear_graph (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (t : Interval) :
    (meanWeightedInput ε h hε hh hb S (fieldWeight l i) t,
      meanWeightedFirst ε h hε hh hb S (fieldWeight l i) t+
        (-Complex.I*(h:ℂ)) • meanWeightedInput ε h hε hh hb S (slopeWeight l i) t) ∈
      (KFCausalTransverseShearMomentum.shearMomentum h).graph := by
  have hg : Continuous (fun θ => weightedInput ε h hε hh hb S (fieldWeight l i) (2*Real.pi*θ) t) :=
    (angle_continuous ε h hε hh hb S (fieldWeight l i) t).1.comp (continuous_const.mul continuous_id)
  have hj : Continuous (fun θ => weightedFirst ε h hε hh hb S (fieldWeight l i) (2*Real.pi*θ) t) :=
    (angle_continuous ε h hε hh hb S (fieldWeight l i) t).2.comp (continuous_const.mul continuous_id)
  have hd : Continuous (fun θ => weightedInput ε h hε hh hb S (slopeWeight l i) (2*Real.pi*θ) t) :=
    (angle_continuous ε h hε hh hb S (slopeWeight l i) t).1.comp (continuous_const.mul continuous_id)
  have he := integral_closed_graph _ (KFCausalTransverseShearMomentum.shear_selfAdjoint h hh).isClosed _ _
    hg (hj.add (hd.const_smul (-Complex.I*(h:ℂ))))
    (fun θ => corrected_shear_graph ε h hε hh hb S l i (2*Real.pi*θ) t)
  have hi := (continuous_angle_memLp _ hj).integrable (by norm_num)
  have hk := (continuous_angle_memLp _ (hd.const_smul (-Complex.I*(h:ℂ)))).integrable (by norm_num)
  change (meanWeightedInput ε h hε hh hb S (fieldWeight l i) t,
    ∫ θ, weightedFirst ε h hε hh hb S (fieldWeight l i) (2*Real.pi*θ) t+
      (-Complex.I*(h:ℂ)) • weightedInput ε h hε hh hb S (slopeWeight l i) (2*Real.pi*θ) t ∂angleMeasure) ∈ _ at he
  rw [integral_add hi hk,integral_smul] at he
  exact he

#print axioms fieldPower_closed
#print axioms mean_continuous
#print axioms mean_field_graph
#print axioms mean_first_field_graph
#print axioms mean_corrected_shear_graph
end
end UnifiedTheory.Audit.KFCausalProjectedMatterShearGraphs
