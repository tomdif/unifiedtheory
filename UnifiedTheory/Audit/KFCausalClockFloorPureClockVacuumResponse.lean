/- The vacuum weak pure-clock momentum response retains a controlled
 shear term. The bound is in actual weighted shear output, not a proved
 Hamiltonian-evolution bound or positivity of the total response. -/
import UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumCommutator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumResponse
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum pure_selfAdjoint)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorJointMomentumCore (regularGraph)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumCommutator
open UnifiedTheory.Audit.KFCausalSelfAdjointCoreWeakGraph (graph_iff_weak)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator)
open UnifiedTheory.Audit.KFCausalClockFloorOrderedMomentumCommutator (correction)
open UnifiedTheory.Audit.KFCausalClockFloorVacuumMomentumResponse (multiplier)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hbound : |h| ≤ 2*Real.pi*ε/3)
local notation "B" => pureMomentum ε hε h
local notation "J" => shearMomentum h
local notation "T" => orderedExponential ε hε h
local notation "D" => defectOperator ε hε
local notation "G" => regularGraph ε hε h
local notation "responseL" => KFCausalClockFloorVacuumMomentumResponse.response ε hε h hbound

def response (g jg : Hilbert) : ℝ := (2/h)*(inner ℂ g (pureCorrection ε hε h hbound g jg)).im

omit hbound in
theorem pure_pairing_real (hne : h ≠ 0) (g bg : Hilbert) (hg : (g,bg) ∈ (B).graph) :
    (inner ℂ g bg).im = 0 := by
  have he := (graph_iff_weak _ (pure_selfAdjoint ε hε h hne) g bg).mp hg g bg hg
  have hi := congrArg Complex.im he
  have hs : (inner ℂ bg g).im = -(inner ℂ g bg).im := inner_im_symm (𝕜 := ℂ) bg g
  linarith

theorem longitudinal_pairing (hne : h ≠ 0) (g : Hilbert) :
    (2/h)*(inner ℂ g (correction ε hε h hbound g)).im = responseL g := by
  change (2/h)*(inner ℂ g ((Complex.I*(h:ℂ)/(2*(ε:ℂ))) • multiplier ε hε h hbound g)).im =
    (1/ε)*(inner ℂ g (multiplier ε hε h hbound g)).re
  have hc : Complex.I*(h:ℂ)/(2*(ε:ℂ)) = ((h/(2*ε):ℝ):ℂ)*Complex.I := by push_cast; ring
  rw [inner_smul_right,hc]
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_mul,sub_zero,add_zero,zero_add]
  field_simp [hne,hε.ne']

theorem response_split (hne : h ≠ 0) (g jg : Hilbert) :
    response ε hε h hbound g jg = responseL g-(2/h)*(inner ℂ g (shearCorrection ε hε h hbound jg)).im := by
  simp only [response,pureCorrection,inner_sub_right,Complex.sub_im,mul_sub,longitudinal_pairing ε hε h hbound hne]

theorem response_error_bound (hne : h ≠ 0) (g jg : Hilbert) :
    |response ε hε h hbound g jg-responseL g| ≤ (4/ε^2)*‖g‖*‖D (D jg)‖ := by
  rw [response_split ε hε h hbound hne g jg,sub_sub_cancel_left,abs_neg,abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hi : |(inner ℂ g (shearCorrection ε hε h hbound jg)).im| ≤
      ‖g‖*((2*|h|/ε^2)*‖D (D jg)‖) :=
    (Complex.abs_im_le_norm _).trans ((norm_inner_le_norm (𝕜 := ℂ) _ _).trans
      (mul_le_mul_of_nonneg_left (shearCorrection_bound ε hε h hbound jg) (norm_nonneg g)))
  calc
    _ ≤ (2/|h|)*(‖g‖*((2*|h|/ε^2)*‖D (D jg)‖)) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by field_simp [abs_ne_zero.mpr hne]; ring

theorem response_bounds (hne : h ≠ 0) (g jg : Hilbert) :
    -(4/ε^2)*‖g‖*‖D (D jg)‖ ≤ response ε hε h hbound g jg ∧
      response ε hε h hbound g jg ≤ (1/(2*ε))*‖g‖^2+(4/ε^2)*‖g‖*‖D (D jg)‖ := by
  have he := abs_le.mp (response_error_bound ε hε h hbound hne g jg)
  have hl := KFCausalClockFloorVacuumMomentumResponse.response_bounds ε hε h hbound g
  constructor <;> nlinarith

theorem weak_response (hne : h ≠ 0) (f g b tb bg jg : Hilbert) (hfg : (f,g) ∈ G)
    (hb : (f,b) ∈ (B).graph) (htb : (b,tb) ∈ (T).graph)
    (hbg : (g,bg) ∈ (B).graph) (hjg : (g,jg) ∈ (J).graph) :
    (-2/h)*(inner ℂ g tb).im = response ε hε h hbound g jg := by
  have he := congrArg (fun v : Hilbert => (inner ℂ g v).im)
    (commutator_graph ε hε h hbound hne f g b tb bg jg hfg hb htb hbg hjg)
  change (inner ℂ g (bg-tb)).im = (inner ℂ g (pureCorrection ε hε h hbound g jg)).im at he
  rw [inner_sub_right,Complex.sub_im,pure_pairing_real ε hε h hne g bg hbg,zero_sub] at he
  unfold response
  rw [← he]
  ring

theorem weak_response_error_bound (hne : h ≠ 0) (f g b tb bg jg : Hilbert) (hfg : (f,g) ∈ G)
    (hb : (f,b) ∈ (B).graph) (htb : (b,tb) ∈ (T).graph)
    (hbg : (g,bg) ∈ (B).graph) (hjg : (g,jg) ∈ (J).graph) :
    |(-2/h)*(inner ℂ g tb).im-responseL g| ≤ (4/ε^2)*‖g‖*‖D (D jg)‖ := by
  rw [weak_response ε hε h hbound hne f g b tb bg jg hfg hb htb hbg hjg]
  exact response_error_bound ε hε h hbound hne g jg

theorem core_response (hne : h ≠ 0) (f g : Hilbert) (hfg : (f,g) ∈ G) :
    ∃ b tb jg : Hilbert, (f,b) ∈ (B).graph ∧ (b,tb) ∈ (T).graph ∧ (g,jg) ∈ (J).graph ∧
      (-2/h)*(inner ℂ g tb).im = response ε hε h hbound g jg := by
  obtain ⟨b,tb,bg,jg,hb,htb,hbg,hjg,he⟩ := core_compositions ε hε h hbound hne f g hfg
  exact ⟨b,tb,jg,hb,htb,hjg,weak_response ε hε h hbound hne f g b tb bg jg hfg hb htb hbg hjg⟩

#print axioms pure_pairing_real
#print axioms longitudinal_pairing
#print axioms response_split
#print axioms response_error_bound
#print axioms response_bounds
#print axioms weak_response
#print axioms weak_response_error_bound
#print axioms core_response
end
end UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumResponse
