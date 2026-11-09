/- Clock defect on the graph presentation of the complete averaged form
space, including its exact output action and compatibility with time
transfer. This is form-domain preservation, not operator-domain invariance. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedFormDefect
import UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
import UnifiedTheory.Audit.KFCausalClockFloorDefectForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorReferenceDefect
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (formData graphFormVector graphFormVector_surjective)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
  (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum : ℝ)
local notation "𝒱" => FormSpace ε hε hbar hh hbound mass2 quartic vacuum
local notation "J" => embedding ε hε hbar hh hbound mass2 quartic vacuum
local notation "A" => energyOutput ε hε hbar hh hbound mass2 quartic vacuum
local notation "D" => defectOperator ε hε
local notation "R" => ContinuousLinearMap.compLp (outputAction ε hε hbar hbound)
local notation "T" => formTransfer ε hε hbar hh hbound mass2 quartic vacuum

theorem graph_defect (t : ℝ) (u : 𝒱 t) :
    WithLp.toLp 2 (D (J t u),R (A t u)) ∈
      KFCausalClosedGraphForm.energyGraph (formData ε hε hbar hh hbound mass2 quartic vacuum t) := by
  let v := Classical.choose (graphFormVector_surjective ε hε hbar hh hbound mass2 quartic vacuum t u)
  have hv := Classical.choose_spec (graphFormVector_surjective ε hε hbar hh hbound mass2 quartic vacuum t u)
  have he : KFCausalClockFloorAveragedEnergy.embedding ε hε hbar
      (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε hbar hbound) hh mass2 quartic vacuum t v = J t u :=
    congrArg (J t) hv
  have ho : KFCausalClockFloorAveragedEnergy.energyOutput ε hε hbar
      (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε hbar hbound) hh mass2 quartic vacuum t v = A t u :=
    congrArg (A t) hv
  have hp := (graphFormVector ε hε hbar hh hbound mass2 quartic vacuum t
    (KFCausalClockFloorAveragedFormDefect.formAction ε hε hbar hh hbound mass2 quartic vacuum t v)).property
  have he' := (KFCausalClockFloorAveragedFormDefect.formAction_embedding
    ε hε hbar hh hbound mass2 quartic vacuum t v).trans (congrArg D he)
  have ho' := (KFCausalClockFloorAveragedFormDefect.formAction_output
    ε hε hbar hh hbound mass2 quartic vacuum t v).trans (congrArg R ho)
  have heq := congrArg₂ (fun (f : Hilbert) (g : KFCausalAveragedOutputRescaling.EnergyOutputSpace) =>
    WithLp.toLp 2 (f,g)) he' ho'
  exact (congrArg (fun z => z ∈ KFCausalClosedGraphForm.energyGraph
    (formData ε hε hbar hh hbound mass2 quartic vacuum t)) heq).mp hp

def formLinear (t : ℝ) : 𝒱 t →ₗ[ℂ] 𝒱 t where
  toFun u := ⟨WithLp.toLp 2 (D (J t u),R (A t u)),
    graph_defect ε hε hbar hh hbound mass2 quartic vacuum t u⟩
  map_add' u v := by
    apply embedding_injective ε hε hbar hh hbound mass2 quartic vacuum t
    change D (J t (u+v)) = J t (_+_)
    simp only [map_add]
    rfl
  map_smul' c u := by
    apply embedding_injective ε hε hbar hh hbound mass2 quartic vacuum t
    change D (J t (c • u)) = J t (c • _)
    simp only [map_smul]
    rfl

theorem formLinear_norm (t : ℝ) (u : 𝒱 t) :
    ‖formLinear ε hε hbar hh hbound mass2 quartic vacuum t u‖ ≤ 2*‖u‖ := by
  have hD := pow_le_pow_left₀ (norm_nonneg _) (defectOperator_norm_le ε hε (J t u)) 2
  have hR := pow_le_pow_left₀ (norm_nonneg _)
    (KFCausalClockFloorAveragedFormDefect.outputLp_norm ε hε hbar hbound (A t u)) 2
  have h1 := form_norm_identity ε hε hbar hh hbound mass2 quartic vacuum t
    (formLinear ε hε hbar hh hbound mass2 quartic vacuum t u)
  change ‖formLinear ε hε hbar hh hbound mass2 quartic vacuum t u‖^2 = ‖D (J t u)‖^2+‖R (A t u)‖^2 at h1
  have h0 := form_norm_identity ε hε hbar hh hbound mass2 quartic vacuum t u
  have hs (a b c d e f : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (h1 : a^2=c^2+d^2) (h0 : b^2=e^2+f^2)
      (hD : c^2 ≤ e^2) (hR : d^2 ≤ (2*f)^2) : a ≤ 2*b := by
    nlinarith only [ha,hb,h1,h0,hD,hR,sq_nonneg e]
  exact hs _ _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) h1 h0 hD hR

def formDefect (t : ℝ) : 𝒱 t →L[ℂ] 𝒱 t :=
  (formLinear ε hε hbar hh hbound mass2 quartic vacuum t).mkContinuous 2
    (formLinear_norm ε hε hbar hh hbound mass2 quartic vacuum t)

theorem formDefect_embedding (t : ℝ) (u : 𝒱 t) :
    J t (formDefect ε hε hbar hh hbound mass2 quartic vacuum t u) = D (J t u) := rfl

theorem formDefect_output (t : ℝ) (u : 𝒱 t) :
    A t (formDefect ε hε hbar hh hbound mass2 quartic vacuum t u) = R (A t u) := rfl

theorem formDefect_transfer (s t : ℝ) (u : 𝒱 s) :
    T s t (formDefect ε hε hbar hh hbound mass2 quartic vacuum s u) =
      formDefect ε hε hbar hh hbound mass2 quartic vacuum t (T s t u) := by
  apply embedding_injective ε hε hbar hh hbound mass2 quartic vacuum t
  exact (transfer_embedding ε hε hbar hh hbound mass2 quartic vacuum s t
    (formDefect ε hε hbar hh hbound mass2 quartic vacuum s u)).trans
    ((formDefect_embedding ε hε hbar hh hbound mass2 quartic vacuum s u).trans
      ((congrArg D (transfer_embedding ε hε hbar hh hbound mass2 quartic vacuum s t u)).symm.trans
        (formDefect_embedding ε hε hbar hh hbound mass2 quartic vacuum t (T s t u)).symm))

theorem reference_defect_pairing (t : ℝ) (u : 𝒱 0) :
    inner ℂ u (KFCausalClockFloorAveragedRegularity.referenceFormOperator ε hε hbar hh hbound mass2 quartic vacuum t
      (formDefect ε hε hbar hh hbound mass2 quartic vacuum 0 u)) =
      inner ℂ (A t (T 0 t u)) (R (A t (T 0 t u))) := by
  have hp := KFCausalClockFloorAveragedRegularity.referenceForm_represents_closed_form
    ε hε hbar hh hbound mass2 quartic vacuum t u
    (formDefect ε hε hbar hh hbound mass2 quartic vacuum 0 u)
  have he := (congrArg (A t) (formDefect_transfer ε hε hbar hh hbound mass2 quartic vacuum 0 t u)).trans
    (formDefect_output ε hε hbar hh hbound mass2 quartic vacuum t (T 0 t u))
  exact hp.trans (congrArg (fun v => inner ℂ (A t (T 0 t u)) v) he)

#print axioms graph_defect
#print axioms formLinear_norm
#print axioms formDefect_embedding
#print axioms formDefect_output
#print axioms formDefect_transfer
#print axioms reference_defect_pairing

end
end UnifiedTheory.Audit.KFCausalClockFloorReferenceDefect
