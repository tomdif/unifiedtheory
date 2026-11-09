/- Transported initial matter vectors for the full structured family.
The transport is a bounded clock multiplier independent of the seed.
This gives angle continuity without imposing common packet widths. -/
import UnifiedTheory.Audit.KFCausalTransportedSecantMean
import UnifiedTheory.Audit.KFCausalStructuredPolynomialShearOrbit

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalStructuredTransportedMatterOrbit
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse (StructuredState)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalStructuredShearInterpolation (seed amplitudeCoefficient)
open UnifiedTheory.Audit.KFCausalStructuredPolynomialShearOrbit (weightedInput weightedFirst weighted_continuous)
open UnifiedTheory.Audit.KFCausalPolynomialImaginaryShearCurve (fieldWeight slopeWeight)
open UnifiedTheory.Audit.KFCausalFieldEigenpolynomials (modes)
open UnifiedTheory.Audit.KFCausalEigenfieldShearGraphs (scalar)
open UnifiedTheory.Audit.KFCausalClockProfileCalculus (transport transport_continuous)
open UnifiedTheory.Audit.KFCausalActualTransportedField (profile)
open UnifiedTheory.Audit.KFCausalTransportedSecantMean (Endpoints endpoint)

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (S : StructuredState) (l : Transverse →L[ℝ] ℝ) (i : Fin 2)

def transportedInput (θ t : ℝ) : Hilbert :=
  ∑ k, transport (scalar (modes l i k) h • profile ε h hε hb hh) t
    (weightedInput ε h hε hh hb S (modes l i k).toWeight θ t)

theorem transported_input_eq (θ t : ℝ) : transportedInput ε h hε hh hb S l i θ t =
    KFCausalTransportedMatterInterpolation.input ε h hε hb hh l i
      (fun r => seed h hh (S.packet r) θ)
      (fun r => S.coefficient r*amplitudeCoefficient ε h hε hh (S.packet r) θ) t := by
  unfold transportedInput weightedInput KFCausalTransportedMatterInterpolation.input
    KFCausalActualTransportedField.input KFCausalTransportedShearCurve.input
  simp only [map_sum,map_smul,Finset.smul_sum]
  rw [Finset.sum_comm]

theorem transported_continuous :
    Continuous (fun v : ℝ × Interval => transportedInput ε h hε hh hb S l i v.1 v.2) := by
  unfold transportedInput
  apply continuous_finset_sum
  intro k _
  have ht : Continuous (fun v : ℝ × Interval =>
      transport (scalar (modes l i k) h • profile ε h hε hb hh) v.2) :=
    (transport_continuous _).comp (continuous_subtype_val.comp continuous_snd)
  exact ht.clm_apply (weighted_continuous ε h hε hh hb S (modes l i k).toWeight).1

theorem angle_continuous (t : Interval) :
    Continuous (fun θ => transportedInput ε h hε hh hb S l i θ t) := by
  have hc : Continuous (fun θ : ℝ => (θ,t)) := continuous_id.prodMk continuous_const
  have he := (transported_continuous ε h hε hh hb S l i).comp hc
  simpa only [Function.comp_def] using he

def endpointValues (θ : ℝ) : Endpoints :=
  (transportedInput ε h hε hh hb S l i θ 0,
   (weightedInput ε h hε hh hb S (fieldWeight l i) θ 1,
    weightedFirst ε h hε hh hb S (fieldWeight l i) θ 1+
      (-Complex.I*(h:ℂ)) • weightedInput ε h hε hh hb S (slopeWeight l i) θ 1))

theorem endpoint_sum (θ : ℝ) : endpointValues ε h hε hh hb S l i θ =
    ∑ r, (S.coefficient r*amplitudeCoefficient ε h hε hh (S.packet r) θ) •
      endpoint ε h hε hb hh l i (seed h hh (S.packet r) θ) := by
  rw [KFCausalTransportedSecantMean.finite_endpoints]
  unfold endpointValues
  rw [transported_input_eq,KFCausalFieldShearInterpolationEstimate.shear_identity]
  rfl

theorem endpoint_continuous : Continuous (endpointValues ε h hε hh hb S l i) := by
  have h0 := angle_continuous ε h hε hh hb S l i ⟨0,by constructor <;> norm_num⟩
  have h1 := KFCausalStructuredPolynomialShearOrbit.angle_continuous ε h hε hh hb S
    (fieldWeight l i) ⟨1,by constructor <;> norm_num⟩
  have hd := KFCausalStructuredPolynomialShearOrbit.angle_continuous ε h hε hh hb S
    (slopeWeight l i) ⟨1,by constructor <;> norm_num⟩
  exact h0.prodMk (h1.1.prodMk (h1.2.add (hd.1.const_smul (-Complex.I*(h:ℂ)))))

#print axioms transported_input_eq
#print axioms transported_continuous
#print axioms angle_continuous
#print axioms endpoint_sum
#print axioms endpoint_continuous
end
end UnifiedTheory.Audit.KFCausalStructuredTransportedMatterOrbit
