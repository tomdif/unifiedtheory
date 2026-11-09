/- Both sides of the actual rescaled shifted inverse and the limiting
growing Hamiltonian inverse are identified on their physical domains. -/
import UnifiedTheory.Audit.KFCausalClockFloorFastResolvent

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFastResolventIdentification
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorFastTimeEnergy (physicalTime)
open UnifiedTheory.Audit.KFCausalClockFloorFastResolvent
open UnifiedTheory.Audit.KFCausalClockFloorAveragedShiftedResolvent (shiftedResolvent resolventVector hamiltonian_resolvent shiftedResolvent_left)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hne hb m g k
local notation "HG" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hne hb m g k
local notation "D" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hne hb m g k
local notation "JW" => KFCausalClosedGraphForm.embedding D
local notation "R" => resolvent ε hε h hne hb m g k
local notation "R0" => limitResolvent ε hε h hne hb m g k

def actualPoint (u : ℝ) (hu : 0 < u) (f : Hilbert) : (H (physicalTime u)).domain :=
  resolventVector ε hε h hne hb m g k u (physicalTime u) hu (u • f)

theorem actualPoint_coe (u : ℝ) (hu : 0 < u) (f : Hilbert) :
    (actualPoint ε hε h hne hb m g k u hu f : Hilbert) = R u f :=
  (shiftedResolvent ε hε h hne hb m g k u (physicalTime u)).map_smul_of_tower u f

theorem actual_right_inverse (u : ℝ) (hu : 0 < u) (f : Hilbert) :
    (1/u) • H (physicalTime u) (actualPoint ε hε h hne hb m g k u hu f)+R u f = f := by
  have hp := hamiltonian_resolvent ε hε h hne hb m g k u (physicalTime u) hu (u • f)
  change H (physicalTime u) (actualPoint ε hε h hne hb m g k u hu f) =
    u • f-u • (actualPoint ε hε h hne hb m g k u hu f : Hilbert) at hp
  rw [actualPoint_coe,← smul_sub] at hp
  rw [hp,smul_smul,one_div,inv_mul_cancel₀ hu.ne',one_smul,sub_add_cancel]

theorem actual_left_inverse (u : ℝ) (hu : 0 < u) (x : (H (physicalTime u)).domain) :
    R u ((1/u) • H (physicalTime u) x+(x:Hilbert)) = x := by
  let S := shiftedResolvent ε hε h hne hb m g k u (physicalTime u)
  have he : (1/u) • H (physicalTime u) x+(x:Hilbert) =
      (1/u) • (H (physicalTime u) x+u • (x:Hilbert)) := by
    rw [smul_add,smul_smul,one_div,inv_mul_cancel₀ hu.ne',one_smul]
  change u • S ((1/u) • H (physicalTime u) x+(x:Hilbert)) = (x:Hilbert)
  rw [he,S.map_smul_of_tower,smul_smul,one_div,mul_inv_cancel₀ hu.ne',one_smul]
  exact shiftedResolvent_left ε hε h hne hb m g k u (physicalTime u) hu x

def limitPoint (f : Hilbert) : (HG).domain :=
  KFCausalResolventHamiltonian.rangeVector (KFCausalFormResolvent.resolvent JW)
    (KFCausalFormResolvent.resolvent_injective JW
      (KFCausalClosedGraphForm.embedding_injective D) (KFCausalClosedGraphForm.embedding_dense D)) f

theorem limitPoint_coe (f : Hilbert) : (limitPoint ε hε h hne hb m g k f : Hilbert) = R0 f := rfl

theorem limit_right_inverse (f : Hilbert) :
    HG (limitPoint ε hε h hne hb m g k f)+R0 f = f := by
  have hp := KFCausalResolventHamiltonian.inverseShift_apply_range (KFCausalFormResolvent.resolvent JW)
    (KFCausalFormResolvent.resolvent_injective JW
      (KFCausalClosedGraphForm.embedding_injective D) (KFCausalClosedGraphForm.embedding_dense D)) f
  change HG (limitPoint ε hε h hne hb m g k f) = f-R0 f at hp
  rw [hp,sub_add_cancel]

theorem limit_left_inverse (x : (HG).domain) : R0 (HG x+(x:Hilbert)) = x :=
  KFCausalResolventHamiltonian.inverseShift_resolvent (KFCausalFormResolvent.resolvent JW)
    (KFCausalFormResolvent.resolvent_injective JW
      (KFCausalClosedGraphForm.embedding_injective D) (KFCausalClosedGraphForm.embedding_dense D)) x

#print axioms actualPoint_coe
#print axioms actual_right_inverse
#print axioms actual_left_inverse
#print axioms limitPoint_coe
#print axioms limit_right_inverse
#print axioms limit_left_inverse
end
end UnifiedTheory.Audit.KFCausalClockFloorFastResolventIdentification
