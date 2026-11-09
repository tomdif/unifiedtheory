/- Unconditional Two-Time Form Energy Norm Bounds for all real couplings:
explicit static-plus-growing energy decompositions under residualFormTransfer
and formTransfer, two-sided exponential scaling bounds (max, min, additive,
and monotone for s ≤ t), and growing/potential energy domination by the
source-time form energy. -/
import UnifiedTheory.Audit.KFCausalClockFloorTwoTimeFormTransfer

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorTwoTimeFormNormBounds
noncomputable section
open KFCausalAveragedOutputRescaling (EnergyOutputSpace staticOutputLp growingOutputLp
  norm_timeOutputLp_sq)
open KFCausalClockFloorAveragedOutputTransport (timeOutputLp)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorGrowingRadialMultiplierForm (rootOutput)
open KFCausalClockFloorPotentialHamiltonian (growingLift growingLift_embedding)
open KFCausalClockFloorRadialResolventGrowing (growing_output_norm_sq)
open KFCausalClockFloorResidualFormSplit (staticLift potentialLift
  staticLift_embedding potentialLift_embedding residual_norm_split)
open KFCausalClockFloorTwoTimeFormTransfer (residualFormTransfer
  staticLift_residualFormTransfer potentialLift_residualFormTransfer
  growingProject residualProject)

private theorem exp_sub_zero_mul (t x : ℝ) :
    Real.exp (2*(t-0))*x=Real.exp (2*t)*x := by
  rw [sub_zero]

private theorem exp_two_sub_mul (t s : ℝ) :
    Real.exp (2*(t-s))*Real.exp (2*s)=Real.exp (2*t) := by
  rw [← Real.exp_add,show 2*(t-s)+2*s=2*t by ring]

private theorem split_le_max (Et Es A B t s : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ht : Et=A+Real.exp (2*t)*B) (hs : Es=A+Real.exp (2*s)*B) :
    Et ≤ max 1 (Real.exp (2*(t-s)))*Es := by
  have he := exp_two_sub_mul t s
  have h1 : 1 ≤ max 1 (Real.exp (2*(t-s))) := le_max_left 1 (Real.exp (2*(t-s)))
  have h2 : Real.exp (2*(t-s)) ≤ max 1 (Real.exp (2*(t-s))) := le_max_right 1 (Real.exp (2*(t-s)))
  have hBs : 0 ≤ Real.exp (2*s)*B := mul_nonneg (Real.exp_pos (2*s)).le hB
  have hA' : 1*A ≤ max 1 (Real.exp (2*(t-s)))*A := mul_le_mul_of_nonneg_right h1 hA
  have hB' : Real.exp (2*(t-s))*(Real.exp (2*s)*B) ≤
      max 1 (Real.exp (2*(t-s)))*(Real.exp (2*s)*B) := mul_le_mul_of_nonneg_right h2 hBs
  rw [ht,hs,← he,mul_assoc]
  linarith

private theorem split_ge_min (Et Es A B t s : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ht : Et=A+Real.exp (2*t)*B) (hs : Es=A+Real.exp (2*s)*B) :
    min 1 (Real.exp (2*(t-s)))*Es ≤ Et := by
  have he := exp_two_sub_mul t s
  have h1 : min 1 (Real.exp (2*(t-s))) ≤ 1 := min_le_left 1 (Real.exp (2*(t-s)))
  have h2 : min 1 (Real.exp (2*(t-s))) ≤ Real.exp (2*(t-s)) := min_le_right 1 (Real.exp (2*(t-s)))
  have hBs : 0 ≤ Real.exp (2*s)*B := mul_nonneg (Real.exp_pos (2*s)).le hB
  have hA' : min 1 (Real.exp (2*(t-s)))*A ≤ 1*A := mul_le_mul_of_nonneg_right h1 hA
  have hB' : min 1 (Real.exp (2*(t-s)))*(Real.exp (2*s)*B) ≤
      Real.exp (2*(t-s))*(Real.exp (2*s)*B) := mul_le_mul_of_nonneg_right h2 hBs
  rw [ht,hs,← he,mul_assoc]
  linarith

private theorem split_le_add (Et Es A B t s : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ht : Et=A+Real.exp (2*t)*B) (hs : Es=A+Real.exp (2*s)*B) :
    Et ≤ (1+Real.exp (2*(t-s)))*Es := by
  have he := exp_two_sub_mul t s
  have hAt : 0 ≤ Real.exp (2*(t-s))*A := mul_nonneg (Real.exp_pos (2*(t-s))).le hA
  have hBs : 0 ≤ Real.exp (2*s)*B := mul_nonneg (Real.exp_pos (2*s)).le hB
  rw [ht,hs,← he,mul_assoc]
  linarith

private theorem split_mono (Et Es A B t s : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ht : Et=A+Real.exp (2*t)*B) (hs : Es=A+Real.exp (2*s)*B) (hst : s ≤ t) :
    Es ≤ Et ∧ Et ≤ Real.exp (2*(t-s))*Es := by
  have he := exp_two_sub_mul t s
  have hr : 1 ≤ Real.exp (2*(t-s)) := Real.one_le_exp (by linarith)
  have hBs : 0 ≤ Real.exp (2*s)*B := mul_nonneg (Real.exp_pos (2*s)).le hB
  have hA' : 1*A ≤ Real.exp (2*(t-s))*A := mul_le_mul_of_nonneg_right hr hA
  have hB' : 1*(Real.exp (2*s)*B) ≤ Real.exp (2*(t-s))*(Real.exp (2*s)*B) :=
    mul_le_mul_of_nonneg_right hr hBs
  rw [ht,hs,← he,mul_assoc]
  exact ⟨by linarith,by linarith⟩

private theorem split_growing_le (Es A B t s : ℝ) (hA : 0 ≤ A)
    (hs : Es=A+Real.exp (2*s)*B) :
    Real.exp (2*t)*B ≤ Real.exp (2*(t-s))*Es := by
  have he := exp_two_sub_mul t s
  have hAt : 0 ≤ Real.exp (2*(t-s))*A := mul_nonneg (Real.exp_pos (2*(t-s))).le hA
  rw [hs,← he,mul_assoc]
  linarith

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "VT" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hw m g k
local notation "AT" => KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hw m g k
local notation "FT" => KFCausalClockFloorAveragedFormTransport.formTransfer ε hε h hh hw m g k
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "SV" => KFCausalClockFloorStaticPotentialHamiltonian.ResidualForm ε hε h hh hw m g k
local notation "SB" => fun t => KFCausalClosedGraphForm.energyOutput (SD t)
local notation "GD" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hw m g k
local notation "GB" => KFCausalClosedGraphForm.energyOutput GD
local notation "R" => rootOutput ε hε h hh hw m g k
local notation "TD" => KFCausalClockFloorStaticHamiltonian.formData ε hε h hh hw m g k 0
local notation "TB" => KFCausalClosedGraphForm.energyOutput TD
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "PB" => KFCausalClosedGraphForm.energyOutput PD

theorem residualFormTransfer_norm_sq_split (t s : ℝ) (w : SV s) :
    ‖SB t (residualFormTransfer ε hε h hh hb m g k s t w)‖^2=
      ‖TB (staticLift ε hε h hh hw m g k s w)‖^2+
        Real.exp (2*t)*‖PB (potentialLift ε hε h hh hw m g k s w)‖^2 := by
  let wt := residualFormTransfer ε hε h hh hb m g k s t w
  have hst : ‖TB (staticLift ε hε h hh hw m g k t wt)‖^2=
      ‖TB (staticLift ε hε h hh hw m g k s w)‖^2 :=
    congrArg (fun y : EnergyOutputSpace => ‖y‖^2)
      (congrArg TB (staticLift_residualFormTransfer ε hε h hh hb m g k s t w))
  have hpt : ‖PB (potentialLift ε hε h hh hw m g k t wt)‖^2=
      ‖PB (potentialLift ε hε h hh hw m g k s w)‖^2 :=
    congrArg (fun y : EnergyOutputSpace => ‖y‖^2)
      (congrArg PB (potentialLift_residualFormTransfer ε hε h hh hb m g k s t w))
  exact (residual_norm_split ε hε h hh hw m g k t wt).trans
    (congrArg₂ (·+·) hst (congrArg (Real.exp (2*t)*·) hpt))

theorem residualFormTransfer_energy_le_max (t s : ℝ) (w : SV s) :
    ‖SB t (residualFormTransfer ε hε h hh hb m g k s t w)‖^2 ≤
      max 1 (Real.exp (2*(t-s)))*‖SB s w‖^2 :=
  split_le_max _ _ _ _ t s (sq_nonneg _) (sq_nonneg _)
    (residualFormTransfer_norm_sq_split ε hε h hh hb m g k t s w)
    (residual_norm_split ε hε h hh hw m g k s w)

theorem residualFormTransfer_energy_ge_min (t s : ℝ) (w : SV s) :
    min 1 (Real.exp (2*(t-s)))*‖SB s w‖^2 ≤
      ‖SB t (residualFormTransfer ε hε h hh hb m g k s t w)‖^2 :=
  split_ge_min _ _ _ _ t s (sq_nonneg _) (sq_nonneg _)
    (residualFormTransfer_norm_sq_split ε hε h hh hb m g k t s w)
    (residual_norm_split ε hε h hh hw m g k s w)

theorem residualFormTransfer_energy_le_add (t s : ℝ) (w : SV s) :
    ‖SB t (residualFormTransfer ε hε h hh hb m g k s t w)‖^2 ≤
      (1+Real.exp (2*(t-s)))*‖SB s w‖^2 :=
  split_le_add _ _ _ _ t s (sq_nonneg _) (sq_nonneg _)
    (residualFormTransfer_norm_sq_split ε hε h hh hb m g k t s w)
    (residual_norm_split ε hε h hh hw m g k s w)

theorem residualFormTransfer_energy_mono (t s : ℝ) (hst : s ≤ t) (w : SV s) :
    ‖SB s w‖^2 ≤ ‖SB t (residualFormTransfer ε hε h hh hb m g k s t w)‖^2 ∧
      ‖SB t (residualFormTransfer ε hε h hh hb m g k s t w)‖^2 ≤
        Real.exp (2*(t-s))*‖SB s w‖^2 :=
  split_mono _ _ _ _ t s (sq_nonneg _) (sq_nonneg _)
    (residualFormTransfer_norm_sq_split ε hε h hh hb m g k t s w)
    (residual_norm_split ε hε h hh hw m g k s w) hst

theorem residualFormTransfer_potential_energy_le (t s : ℝ) (w : SV s) :
    Real.exp (2*t)*‖PB (potentialLift ε hε h hh hw m g k s w)‖^2 ≤
      Real.exp (2*(t-s))*‖SB s w‖^2 :=
  split_growing_le _ _ _ t s (sq_nonneg _)
    (residual_norm_split ε hε h hh hw m g k s w)

theorem formTransfer_norm_sq_split (t s : ℝ) (u : VT s) :
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

theorem averaged_norm_sq_split (s : ℝ) (u : VT s) :
    ‖AT s u‖^2=
      ‖staticOutputLp (AT 0 (FT s 0 u))‖^2+
        Real.exp (2*s)*‖GB (growingProject ε hε h hh hb m g k s u)‖^2 := by
  have hs0 := formTransfer_norm_sq_split ε hε h hh hb m g k s s u
  have hself : ‖AT s (FT s s u)‖^2=‖AT s u‖^2 :=
    congrArg (fun v : VT s => ‖AT s v‖^2)
      (KFCausalClockFloorAveragedFormTransport.transfer_self ε hε h hh hw m g k s u)
  exact hself.symm.trans hs0

private theorem growingProject_norm_sq_eq (s : ℝ) (u : VT s) :
    ‖GB (growingProject ε hε h hh hb m g k s u)‖^2=
      ‖R (growingProject ε hε h hh hb m g k s u)‖^2+
        ‖PB (potentialLift ε hε h hh hw m g k s
          (residualProject ε hε h hh hb m g k s u))‖^2 := by
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
  exact hg.trans (congrArg (fun r : ℝ =>
    ‖R (growingProject ε hε h hh hb m g k s u)‖^2+r) hp_norm)

theorem formTransfer_energy_le_max (t s : ℝ) (u : VT s) :
    ‖AT t (FT s t u)‖^2 ≤ max 1 (Real.exp (2*(t-s)))*‖AT s u‖^2 :=
  split_le_max _ _ _ _ t s (sq_nonneg _) (sq_nonneg _)
    (formTransfer_norm_sq_split ε hε h hh hb m g k t s u)
    (averaged_norm_sq_split ε hε h hh hb m g k s u)

theorem formTransfer_energy_ge_min (t s : ℝ) (u : VT s) :
    min 1 (Real.exp (2*(t-s)))*‖AT s u‖^2 ≤ ‖AT t (FT s t u)‖^2 :=
  split_ge_min _ _ _ _ t s (sq_nonneg _) (sq_nonneg _)
    (formTransfer_norm_sq_split ε hε h hh hb m g k t s u)
    (averaged_norm_sq_split ε hε h hh hb m g k s u)

theorem formTransfer_energy_le_add (t s : ℝ) (u : VT s) :
    ‖AT t (FT s t u)‖^2 ≤ (1+Real.exp (2*(t-s)))*‖AT s u‖^2 :=
  split_le_add _ _ _ _ t s (sq_nonneg _) (sq_nonneg _)
    (formTransfer_norm_sq_split ε hε h hh hb m g k t s u)
    (averaged_norm_sq_split ε hε h hh hb m g k s u)

theorem formTransfer_energy_mono (t s : ℝ) (hst : s ≤ t) (u : VT s) :
    ‖AT s u‖^2 ≤ ‖AT t (FT s t u)‖^2 ∧
      ‖AT t (FT s t u)‖^2 ≤ Real.exp (2*(t-s))*‖AT s u‖^2 :=
  split_mono _ _ _ _ t s (sq_nonneg _) (sq_nonneg _)
    (formTransfer_norm_sq_split ε hε h hh hb m g k t s u)
    (averaged_norm_sq_split ε hε h hh hb m g k s u) hst

theorem formTransfer_growingOutput_energy_le (t s : ℝ) (u : VT s) :
    Real.exp (2*t)*‖GB (growingProject ε hε h hh hb m g k s u)‖^2 ≤
      Real.exp (2*(t-s))*‖AT s u‖^2 :=
  split_growing_le _ _ _ t s (sq_nonneg _)
    (averaged_norm_sq_split ε hε h hh hb m g k s u)

theorem formTransfer_growing_energy_le (t s : ℝ) (u : VT s) :
    Real.exp (2*t)*
      (‖R (growingProject ε hε h hh hb m g k s u)‖^2+
        ‖PB (potentialLift ε hε h hh hw m g k s
          (residualProject ε hε h hh hb m g k s u))‖^2) ≤
      Real.exp (2*(t-s))*‖AT s u‖^2 := by
  rw [← growingProject_norm_sq_eq ε hε h hh hb m g k s u]
  exact formTransfer_growingOutput_energy_le ε hε h hh hb m g k t s u

#print axioms residualFormTransfer_norm_sq_split
#print axioms residualFormTransfer_energy_le_max
#print axioms residualFormTransfer_energy_ge_min
#print axioms residualFormTransfer_energy_le_add
#print axioms residualFormTransfer_energy_mono
#print axioms residualFormTransfer_potential_energy_le
#print axioms formTransfer_norm_sq_split
#print axioms averaged_norm_sq_split
#print axioms formTransfer_energy_le_max
#print axioms formTransfer_energy_ge_min
#print axioms formTransfer_energy_le_add
#print axioms formTransfer_energy_mono
#print axioms formTransfer_growingOutput_energy_le
#print axioms formTransfer_growing_energy_le
end
end UnifiedTheory.Audit.KFCausalClockFloorTwoTimeFormNormBounds
