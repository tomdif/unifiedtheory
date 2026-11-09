/- Smooth representatives and physical field-square domains for the actual
ordered exponential of every coherent-span input. These regularity facts
are derived from the existing Gaussian family, not imposed on its output. -/
import UnifiedTheory.Audit.KFCausalFieldShearDifferential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoherentShiftedRegularity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (shiftedOutput state_ordered_graph)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (profile profile_smooth)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (scale scale_smooth)
open UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile (clockAmplitude clockAmplitude_smooth gaussianState_profile)
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare (fieldSquare)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "T" => orderedExponential ε hε h

include hb in
theorem smooth_output_exists (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh) :
    ∃ (g : Hilbert) (φ : Configuration → ℂ),
      (f,g) ∈ (T).graph ∧ ContDiff ℝ 1 φ ∧ g =ᵐ[volume] φ := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨k,rfl⟩
      let c := KFCausalClockFloorCoherentUnitary.amplitudeConstant h k
      let α := KFCausalChargeGaussianGeometry.groundWidth h
      let β := KFCausalClockFloorInvariantTrial.neutralWidth h
      let p := KFCausalClockFloorCoherentUnitary.clockFrequency k
      let b := KFCausalClockFloorCoherentUnitary.sourceCoefficients h k
      have hy := KFCausalClockFloorShiftedOutput.shift_bound ε h hb
      refine ⟨shiftedOutput ε a h hε ha hh hb k,
        fun x => c*profile (clockAmplitude ε a p (-h/2)) (scale ε (-h/2)) α β b x,
        state_ordered_graph ε a h hε ha hh hb k,?_,?_⟩
      · exact contDiff_const.mul (profile_smooth _ _
          (clockAmplitude_smooth ε a p (-h/2) hε hy) (scale_smooth ε (-h/2) hε hy) α β b)
      · have he := gaussianState_profile ε a α β p (-h/2) b hε ha
          (KFCausalChargeGaussianGeometry.groundWidth_positive h hh)
          (KFCausalClockFloorInvariantTrial.neutralWidth_positive h hh)
          (KFCausalClockFloorInvariantTrial.neutralWidth_bound h) hy
        filter_upwards [Lp.coeFn_smul c
          (KFCausalClockFloorCoherentSpectral.gaussianState ε a α β p b (-h/2) hε ha
            (KFCausalChargeGaussianGeometry.groundWidth_positive h hh)
            (KFCausalClockFloorInvariantTrial.neutralWidth_positive h hh)
            (KFCausalClockFloorInvariantTrial.neutralWidth_bound h) hy),he] with x hx he
        dsimp only [shiftedOutput]
        rw [hx]
        simp only [Pi.smul_apply,smul_eq_mul,he]
  | zero =>
      exact ⟨0,fun _ => 0,(T).graph.zero_mem,contDiff_const,Lp.coeFn_zero ℂ 2 volume⟩
  | add x y _ _ hx hy =>
      rcases hx with ⟨gx,φx,hgx,hsx,hex⟩
      rcases hy with ⟨gy,φy,hgy,hsy,hey⟩
      refine ⟨gx+gy,φx+φy,(T).graph.add_mem hgx hgy,hsx.add hsy,?_⟩
      filter_upwards [Lp.coeFn_add gx gy,hex,hey] with z hz hx hy
      simp only [hz,Pi.add_apply,hx,hy]
  | smul c x _ hx =>
      rcases hx with ⟨g,φ,hg,hs,he⟩
      refine ⟨c • g,c • φ,(T).graph.smul_mem c hg,hs.const_smul c,?_⟩
      filter_upwards [Lp.coeFn_smul c g,he] with z hz hx
      simp only [hz,Pi.smul_apply,hx]

include hb in
theorem actual_smooth_representative (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (g : Hilbert) (hg : (f,g) ∈ (T).graph) :
    ∃ φ : Configuration → ℂ, ContDiff ℝ 1 φ ∧ g =ᵐ[volume] φ := by
  obtain ⟨g',φ,hg',hs,he⟩ := smooth_output_exists ε a h hε ha hh hb f hf
  have eg : g = g' := (T).mem_graph_snd_inj' hg hg' rfl
  exact ⟨φ,hs,eg ▸ he⟩

include hb in
theorem actual_fieldSquare_domain (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (g : Hilbert) (hg : (f,g) ∈ (T).graph) (l : Transverse →L[ℝ] ℝ) :
    g ∈ (fieldSquare l).domain := by
  have hc := coherentSpan_le_commonEnergyDomain ε a h hε ha hh hb
    KFCausalPhysicalEnergyFactors.modelDirections l hf
  have hd := (KFCausalClockFloorCommonDomain.commonEnergyDomain_iff ε hε h
    KFCausalPhysicalEnergyFactors.modelDirections l f).mp hc (6:Fin 8)
  obtain ⟨g',hg',hd'⟩ := (KFCausalOrderedOperatorComposition.composition_domain _ _ _).mp hd
  have eg : g = g' := (T).mem_graph_snd_inj' hg hg' rfl
  exact eg ▸ hd'

#print axioms smooth_output_exists
#print axioms actual_smooth_representative
#print axioms actual_fieldSquare_domain
end
end UnifiedTheory.Audit.KFCausalCoherentShiftedRegularity
