/- Joint strong continuity of the full squeeze energy output and of the
actual closed energy-form action. No generator domain is assumed. -/
import UnifiedTheory.Audit.KFCausalSqueezeNormalizedOutput
import UnifiedTheory.Audit.KFCausalClockFloorReferenceSqueeze

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalSqueezeEnergyContinuity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedSqueezeEnergy (OutputSpace outputLp)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeEnergy (outputAction outputAction_apply factorScale degree)
open UnifiedTheory.Audit.KFCausalSqueezeNormalizedOutput (O liftLinear lift_comp projectionLp diagonal_decomposition)
open UnifiedTheory.Audit.KFCausalSqueezeOutputContinuity (pureOutput pureLp pureLp_joint_continuous)
open UnifiedTheory.Audit.KFCausalFiniteOutputRescaling (diagonal)
open UnifiedTheory.Audit.KFCausalPairedSqueezeTransport (transport transport_initial transport_compose)
open UnifiedTheory.Audit.KFCausalPairedSqueezeContinuity (transport_joint_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorReferenceSqueeze

theorem outputLp_split (a : ℝ) (x : OutputSpace) :
    outputLp a x = ∑ i : Fin 8, factorScale a i • projectionLp i (pureLp a x) := by
  have he : outputAction a = (diagonal (factorScale a)).comp (pureOutput a : O →L[ℂ] O) := by
    apply ContinuousLinearMap.ext
    intro y
    apply PiLp.ext
    intro i
    rfl
  change liftLinear (outputAction a) x = _
  rw [he,lift_comp,diagonal_decomposition]
  simp only [map_sum,map_smul,ContinuousLinearMap.comp_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply,projectionLp,pureLp,liftLinear,LinearMap.coe_mk,AddHom.coe_mk]

theorem outputLp_joint_continuous : Continuous (fun p : ℝ × OutputSpace => outputLp p.1 p.2) := by
  simp only [outputLp_split]
  apply continuous_finset_sum
  intro i _
  have hc : Continuous (fun a : ℝ => factorScale a i) := by unfold factorScale; fun_prop
  exact (hc.comp continuous_fst).smul ((projectionLp i).continuous.comp pureLp_joint_continuous)

theorem ambient_joint_continuous :
    Continuous (fun p : ℝ × WithLp 2 (Hilbert × OutputSpace) => ambient p.1 p.2) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ Hilbert OutputSpace
  have h1 := transport_joint_continuous.comp
    (continuous_fst.prodMk (continuous_fst.comp (e.continuous.comp continuous_snd)))
  have h2 := outputLp_joint_continuous.comp
    (continuous_fst.prodMk (continuous_snd.comp (e.continuous.comp continuous_snd)))
  exact e.symm.continuous.comp (h1.prodMk h2)

private theorem continuous_section {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : ℝ × X → Y} (hf : Continuous f) (x : X) : Continuous (fun a => f (a,x)) :=
  hf.comp (continuous_id.prodMk continuous_const)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)
  (m q k t : ℝ)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport (FormSpace embedding embedding_injective)
local notation "V" => FormSpace ε hε h hne hh m q k t
local notation "R" => (fun a : ℝ => formAction ε hε h hne hh m q k a t)

theorem formAction_joint_continuous : Continuous (fun p : ℝ × V => R p.1 p.2) := by
  have hi : Continuous (fun p : ℝ × V => (p.1,p.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hc := ambient_joint_continuous.comp hi
  exact hc.subtype_mk _

theorem formAction_strong_continuous (u : V) : Continuous (fun a => R a u) :=
  continuous_section (formAction_joint_continuous ε hε h hne hh m q k t) u

theorem formAction_zero (u : V) : R 0 u = u := by
  apply embedding_injective ε hε h hne hh m q k t
  rw [formAction_embedding,transport_initial]

theorem formAction_compose (a b : ℝ) (u : V) : R b (R a u) = R (a+b) u := by
  apply embedding_injective ε hε h hne hh m q k t
  simp only [formAction_embedding,transport_compose]

#print axioms outputLp_split
#print axioms outputLp_joint_continuous
#print axioms ambient_joint_continuous
#print axioms formAction_joint_continuous
#print axioms formAction_strong_continuous
#print axioms formAction_zero
#print axioms formAction_compose
end
end UnifiedTheory.Audit.KFCausalSqueezeEnergyContinuity
