/- Unconditional Two-Time Form Transfer for all real couplings:
continuous linear time-transfer isomorphisms on the completed residual form
spaces SV(t), exact time-invariance of the static and potential form lifts
under residual time transfer, compatibility of the growing and residual
projections with full-form time transfer, and exact two-time energy-norm
difference identities on both the residual and full completed form spaces. -/
import UnifiedTheory.Audit.KFCausalClockFloorUnconditionalFormDomainSynthesis

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorTwoTimeFormTransfer
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace staticOutputLp growingOutputLp
  norm_timeOutputLp_sq)
open KFCausalClockFloorAveragedOutputTransport (timeOutputLp)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorGrowingRadialMultiplierForm (rootOutput)
open KFCausalClockFloorPotentialHamiltonian (growingLift growingLift_embedding)
open KFCausalClockFloorRadialResolventGrowing (growing_output_norm_sq)
open KFCausalClockFloorResidualFormSplit (staticLift potentialLift
  staticLift_embedding potentialLift_embedding residual_inner_split residual_norm_split)
open KFCausalClockFloorUnconditionalFormDomainSynthesis (residual_graph_time_transfer)

private theorem complex_split_diff (a b c d : ℂ) (t s : ℝ)
    (ht : a=c+(Real.exp (2*t):ℂ)*d) (hs : b=c+(Real.exp (2*s):ℂ)*d) :
    a-b=((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ)*d := by
  rw [ht,hs,Complex.ofReal_sub]
  ring

private theorem real_split_diff (a b c d : ℝ) (t s : ℝ)
    (ht : a=c+Real.exp (2*t)*d) (hs : b=c+Real.exp (2*s)*d) :
    a-b=(Real.exp (2*t)-Real.exp (2*s))*d := by
  rw [ht,hs]
  ring

private theorem exp_sub_zero_mul (t x : ℝ) :
    Real.exp (2*(t-0))*x=Real.exp (2*t)*x := by
  rw [sub_zero]

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "VT" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hw m g k
local notation "AJ" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hw m g k
local notation "AT" => KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hw m g k
local notation "FT" => KFCausalClockFloorAveragedFormTransport.formTransfer ε hε h hh hw m g k
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "SV" => KFCausalClockFloorStaticPotentialHamiltonian.ResidualForm ε hε h hh hw m g k
local notation "SJ" => fun t => KFCausalClosedGraphForm.embedding (SD t)
local notation "SB" => fun t => KFCausalClosedGraphForm.energyOutput (SD t)
local notation "GD" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hw m g k
local notation "GV" => KFCausalClockFloorGrowingHamiltonian.GrowingForm ε hε h hh hw m g k
local notation "GJ" => KFCausalClosedGraphForm.embedding GD
local notation "GB" => KFCausalClosedGraphForm.energyOutput GD
local notation "R" => rootOutput ε hε h hh hw m g k
local notation "TD" => KFCausalClockFloorStaticHamiltonian.formData ε hε h hh hw m g k 0
local notation "TB" => KFCausalClosedGraphForm.energyOutput TD
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "PJ" => KFCausalClosedGraphForm.embedding PD
local notation "PB" => KFCausalClosedGraphForm.energyOutput PD

theorem residualMapsGraph (t s : ℝ) :
    KFCausalClosedGraphTransport.MapsGraph (SD t) (SD s) (timeOutputLp t s) := by
  rintro ⟨f,z⟩ hz
  exact (residual_graph_time_transfer ε hε h hh hb m g k t s f z).mp hz

def residualFormTransfer (t s : ℝ) : SV t →L[ℂ] SV s :=
  KFCausalClosedGraphTransport.transfer (SD t) (SD s) (timeOutputLp t s)
    (residualMapsGraph ε hε h hh hb m g k t s)

def residualFormEquiv (t s : ℝ) : SV t ≃L[ℂ] SV s :=
  KFCausalClosedGraphTransport.transferEquiv (SD t) (SD s)
    (timeOutputLp t s) (timeOutputLp s t)
    (residualMapsGraph ε hε h hh hb m g k t s)
    (residualMapsGraph ε hε h hh hb m g k s t)

theorem residualFormTransfer_embedding (t s : ℝ) (w : SV t) :
    SJ s (residualFormTransfer ε hε h hh hb m g k t s w)=SJ t w :=
  KFCausalClosedGraphTransport.embedding_transfer (SD t) (SD s) (timeOutputLp t s)
    (residualMapsGraph ε hε h hh hb m g k t s) w

theorem residualFormTransfer_output (t s : ℝ) (w : SV t) :
    SB s (residualFormTransfer ε hε h hh hb m g k t s w)=timeOutputLp t s (SB t w) :=
  KFCausalClosedGraphTransport.output_transfer (SD t) (SD s) (timeOutputLp t s)
    (residualMapsGraph ε hε h hh hb m g k t s) w

theorem residualFormTransfer_self (t : ℝ) (w : SV t) :
    residualFormTransfer ε hε h hh hb m g k t t w=w :=
  KFCausalClosedGraphTransport.transfer_self (SD t) (timeOutputLp t t)
    (residualMapsGraph ε hε h hh hb m g k t t) w

theorem residualFormTransfer_comp (r s t : ℝ) (w : SV r) :
    residualFormTransfer ε hε h hh hb m g k s t
      (residualFormTransfer ε hε h hh hb m g k r s w)=
      residualFormTransfer ε hε h hh hb m g k r t w :=
  KFCausalClosedGraphTransport.transfer_comp (SD r) (SD s) (SD t)
    (timeOutputLp r s) (timeOutputLp s t) (timeOutputLp r t)
    (residualMapsGraph ε hε h hh hb m g k r s)
    (residualMapsGraph ε hε h hh hb m g k s t)
    (residualMapsGraph ε hε h hh hb m g k r t) w

theorem residualFormTransfer_inverse (t s : ℝ) (w : SV t) :
    residualFormTransfer ε hε h hh hb m g k s t
      (residualFormTransfer ε hε h hh hb m g k t s w)=w :=
  KFCausalClosedGraphTransport.transfer_inverse (SD t) (SD s)
    (timeOutputLp t s) (timeOutputLp s t)
    (residualMapsGraph ε hε h hh hb m g k t s)
    (residualMapsGraph ε hε h hh hb m g k s t) w

theorem staticLift_residualFormTransfer (t s : ℝ) (w : SV t) :
    staticLift ε hε h hh hw m g k s
      (residualFormTransfer ε hε h hh hb m g k t s w)=
      staticLift ε hε h hh hw m g k t w := by
  apply KFCausalClosedGraphForm.embedding_injective TD
  exact (staticLift_embedding ε hε h hh hw m g k s
    (residualFormTransfer ε hε h hh hb m g k t s w)).trans
    ((residualFormTransfer_embedding ε hε h hh hb m g k t s w).trans
      (staticLift_embedding ε hε h hh hw m g k t w).symm)

theorem potentialLift_residualFormTransfer (t s : ℝ) (w : SV t) :
    potentialLift ε hε h hh hw m g k s
      (residualFormTransfer ε hε h hh hb m g k t s w)=
      potentialLift ε hε h hh hw m g k t w := by
  apply KFCausalClosedGraphForm.embedding_injective PD
  exact (potentialLift_embedding ε hε h hh hw m g k s
    (residualFormTransfer ε hε h hh hb m g k t s w)).trans
    ((residualFormTransfer_embedding ε hε h hh hb m g k t s w).trans
      (potentialLift_embedding ε hε h hh hw m g k t w).symm)

theorem two_time_residual_inner_difference (t s : ℝ) (w1 w2 : SV s) :
    inner ℂ (SB t (residualFormTransfer ε hε h hh hb m g k s t w1))
      (SB t (residualFormTransfer ε hε h hh hb m g k s t w2))-
      inner ℂ (SB s w1) (SB s w2)=
      ((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ)*
        inner ℂ (PB (potentialLift ε hε h hh hw m g k s w1))
          (PB (potentialLift ε hε h hh hw m g k s w2)) := by
  let wt1 := residualFormTransfer ε hε h hh hb m g k s t w1
  let wt2 := residualFormTransfer ε hε h hh hb m g k s t w2
  have hst : inner ℂ (TB (staticLift ε hε h hh hw m g k t wt1))
      (TB (staticLift ε hε h hh hw m g k t wt2))=
      inner ℂ (TB (staticLift ε hε h hh hw m g k s w1))
        (TB (staticLift ε hε h hh hw m g k s w2)) :=
    congrArg₂ (inner ℂ)
      (congrArg TB (staticLift_residualFormTransfer ε hε h hh hb m g k s t w1))
      (congrArg TB (staticLift_residualFormTransfer ε hε h hh hb m g k s t w2))
  have hpt : inner ℂ (PB (potentialLift ε hε h hh hw m g k t wt1))
      (PB (potentialLift ε hε h hh hw m g k t wt2))=
      inner ℂ (PB (potentialLift ε hε h hh hw m g k s w1))
        (PB (potentialLift ε hε h hh hw m g k s w2)) :=
    congrArg₂ (inner ℂ)
      (congrArg PB (potentialLift_residualFormTransfer ε hε h hh hb m g k s t w1))
      (congrArg PB (potentialLift_residualFormTransfer ε hε h hh hb m g k s t w2))
  have ht := (residual_inner_split ε hε h hh hw m g k t wt1 wt2).trans
    (congrArg₂ (·+·) hst (congrArg ((Real.exp (2*t):ℂ)*·) hpt))
  have hs := residual_inner_split ε hε h hh hw m g k s w1 w2
  exact complex_split_diff _ _ _ _ t s ht hs

theorem two_time_residual_norm_sq_difference (t s : ℝ) (w : SV s) :
    ‖SB t (residualFormTransfer ε hε h hh hb m g k s t w)‖^2-‖SB s w‖^2=
      (Real.exp (2*t)-Real.exp (2*s))*
        ‖PB (potentialLift ε hε h hh hw m g k s w)‖^2 := by
  let wt := residualFormTransfer ε hε h hh hb m g k s t w
  have hst : ‖TB (staticLift ε hε h hh hw m g k t wt)‖^2=
      ‖TB (staticLift ε hε h hh hw m g k s w)‖^2 :=
    congrArg (fun y : EnergyOutputSpace => ‖y‖^2)
      (congrArg TB (staticLift_residualFormTransfer ε hε h hh hb m g k s t w))
  have hpt : ‖PB (potentialLift ε hε h hh hw m g k t wt)‖^2=
      ‖PB (potentialLift ε hε h hh hw m g k s w)‖^2 :=
    congrArg (fun y : EnergyOutputSpace => ‖y‖^2)
      (congrArg PB (potentialLift_residualFormTransfer ε hε h hh hb m g k s t w))
  have ht := (residual_norm_split ε hε h hh hw m g k t wt).trans
    (congrArg₂ (·+·) hst (congrArg (Real.exp (2*t)*·) hpt))
  have hs := residual_norm_split ε hε h hh hw m g k s w
  exact real_split_diff _ _ _ _ t s ht hs

def growingProject (t : ℝ) (u : VT t) : GV :=
  KFCausalClockFloorGrowingHamiltonian.referenceLift ε hε h hh hw m g k (FT t 0 u)

def residualProject (t : ℝ) (u : VT t) : SV t :=
  KFCausalClockFloorStaticPotentialHamiltonian.referenceLift ε hε h hh hw m g k t (FT t 0 u)

theorem growingProject_formTransfer (t s : ℝ) (u : VT t) :
    growingProject ε hε h hh hb m g k s (FT t s u)=
      growingProject ε hε h hh hb m g k t u :=
  congrArg (KFCausalClockFloorGrowingHamiltonian.referenceLift ε hε h hh hw m g k)
    (KFCausalClockFloorAveragedFormTransport.transfer_comp ε hε h hh hw m g k t s 0 u)

theorem residualProject_formTransfer (t s : ℝ) (u : VT t) :
    residualProject ε hε h hh hb m g k s (FT t s u)=
      residualFormTransfer ε hε h hh hb m g k t s
        (residualProject ε hε h hh hb m g k t u) := by
  apply KFCausalClosedGraphForm.embedding_injective (SD s)
  have h1 : SJ s (residualProject ε hε h hh hb m g k s (FT t s u))=AJ t u :=
    (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_embedding
      ε hε h hh hw m g k s (FT s 0 (FT t s u))).trans
      ((KFCausalClockFloorAveragedFormTransport.transfer_embedding
        ε hε h hh hw m g k s 0 (FT t s u)).trans
        (KFCausalClockFloorAveragedFormTransport.transfer_embedding
          ε hε h hh hw m g k t s u))
  have h2 : SJ s (residualFormTransfer ε hε h hh hb m g k t s
      (residualProject ε hε h hh hb m g k t u))=AJ t u :=
    (residualFormTransfer_embedding ε hε h hh hb m g k t s
      (residualProject ε hε h hh hb m g k t u)).trans
      ((KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_embedding
        ε hε h hh hw m g k t (FT t 0 u)).trans
        (KFCausalClockFloorAveragedFormTransport.transfer_embedding
          ε hε h hh hw m g k t 0 u))
  exact h1.trans h2.symm

private theorem averaged_output_norm_sq_at_time (t s : ℝ) (u : VT s) :
    ‖AT t (FT s t u)‖^2=
      ‖staticOutputLp (AT 0 (FT s 0 u))‖^2+
        Real.exp (2*t)*‖GB (growingProject ε hε h hh hb m g k s u)‖^2 := by
  let u0 := FT s 0 u
  have hft : FT s t u=FT 0 t u0 :=
    (KFCausalClockFloorAveragedFormTransport.transfer_comp ε hε h hh hw m g k s 0 t u).symm
  have hat : AT t (FT s t u)=timeOutputLp 0 t (AT 0 u0) :=
    (congrArg (AT t) hft).trans
      (KFCausalClockFloorAveragedFormTransport.transfer_energyOutput ε hε h hh hw m g k 0 t u0)
  have hnorm : ‖AT t (FT s t u)‖^2=‖timeOutputLp 0 t (AT 0 u0)‖^2 :=
    congrArg (fun y : EnergyOutputSpace => ‖y‖^2) hat
  have hgb : GB (growingProject ε hε h hh hb m g k s u)=growingOutputLp (AT 0 u0) :=
    (KFCausalClockFloorGrowingHamiltonian.referenceLift_output ε hε h hh hw m g k u0).trans
      (ContinuousLinearMap.comp_apply growingOutputLp (AT 0) u0)
  have hg_norm : ‖growingOutputLp (AT 0 u0)‖^2=
      ‖GB (growingProject ε hε h hh hb m g k s u)‖^2 :=
    congrArg (fun y : EnergyOutputSpace => ‖y‖^2) hgb.symm
  exact (hnorm.trans (norm_timeOutputLp_sq 0 t (AT 0 u0))).trans
    (congrArg (fun r : ℝ => ‖staticOutputLp (AT 0 u0)‖^2+r)
      ((exp_sub_zero_mul t (‖growingOutputLp (AT 0 u0)‖^2)).trans
        (congrArg (Real.exp (2*t)*·) hg_norm)))

theorem two_time_averaged_growing_norm_sq_difference (t s : ℝ) (u : VT s) :
    ‖AT t (FT s t u)‖^2-‖AT s u‖^2=
      (Real.exp (2*t)-Real.exp (2*s))*
        ‖GB (growingProject ε hε h hh hb m g k s u)‖^2 := by
  have ht := averaged_output_norm_sq_at_time ε hε h hh hb m g k t s u
  have hs0 := averaged_output_norm_sq_at_time ε hε h hh hb m g k s s u
  have hself : ‖AT s (FT s s u)‖^2=‖AT s u‖^2 :=
    congrArg (fun v : VT s => ‖AT s v‖^2)
      (KFCausalClockFloorAveragedFormTransport.transfer_self ε hε h hh hw m g k s u)
  have hs := hself.symm.trans hs0
  exact real_split_diff _ _ _ _ t s ht hs

theorem two_time_averaged_norm_sq_difference (t s : ℝ) (u : VT s) :
    ‖AT t (FT s t u)‖^2-‖AT s u‖^2=
      (Real.exp (2*t)-Real.exp (2*s))*
        (‖R (growingProject ε hε h hh hb m g k s u)‖^2+
          ‖PB (potentialLift ε hε h hh hw m g k s
            (residualProject ε hε h hh hb m g k s u))‖^2) := by
  have hdiff := two_time_averaged_growing_norm_sq_difference ε hε h hh hb m g k t s u
  have hg := growing_output_norm_sq ε hε h hb hh m g k
    (growingProject ε hε h hh hb m g k s u)
  have hp_eq : growingLift ε hε h hh hw m g k (growingProject ε hε h hh hb m g k s u)=
      potentialLift ε hε h hh hw m g k s (residualProject ε hε h hh hb m g k s u) := by
    apply KFCausalClosedGraphForm.embedding_injective PD
    exact (growingLift_embedding ε hε h hh hw m g k
      (growingProject ε hε h hh hb m g k s u)).trans
      ((KFCausalClockFloorGrowingHamiltonian.referenceLift_embedding
        ε hε h hh hw m g k (FT s 0 u)).trans
        ((KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_embedding
          ε hε h hh hw m g k s (FT s 0 u)).symm.trans
          (potentialLift_embedding ε hε h hh hw m g k s
            (residualProject ε hε h hh hb m g k s u)).symm))
  have hp_norm : ‖PB (growingLift ε hε h hh hw m g k (growingProject ε hε h hh hb m g k s u))‖^2=
      ‖PB (potentialLift ε hε h hh hw m g k s (residualProject ε hε h hh hb m g k s u))‖^2 :=
    congrArg (fun v => ‖PB v‖^2) hp_eq
  have hg' := hg.trans (congrArg (fun r : ℝ =>
    ‖R (growingProject ε hε h hh hb m g k s u)‖^2+r) hp_norm)
  exact hdiff.trans (congrArg ((Real.exp (2*t)-Real.exp (2*s))*·) hg')

#print axioms residualMapsGraph
#print axioms residualFormTransfer_embedding
#print axioms residualFormTransfer_output
#print axioms residualFormTransfer_self
#print axioms residualFormTransfer_comp
#print axioms residualFormTransfer_inverse
#print axioms staticLift_residualFormTransfer
#print axioms potentialLift_residualFormTransfer
#print axioms two_time_residual_inner_difference
#print axioms two_time_residual_norm_sq_difference
#print axioms growingProject_formTransfer
#print axioms residualProject_formTransfer
#print axioms two_time_averaged_growing_norm_sq_difference
#print axioms two_time_averaged_norm_sq_difference
end
end UnifiedTheory.Audit.KFCausalClockFloorTwoTimeFormTransfer
