/- Positive resolvents of the actual ordered-potential Hamiltonian preserve
its unbounded half-clock domain. The inverse-clock weighted estimate comes
from transport through the original potential-form closure; adjoint duality
constructs the half-clock graph witness. This establishes only the clock
component of static-form regularity, not transverse kinetic preservation. -/
import UnifiedTheory.Audit.KFCausalClockFloorPotentialClockAccretivity
import UnifiedTheory.Audit.KFCausalClockFloorGrowingClockResolvent

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPotentialClockResolvent
noncomputable section
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorDefectOperator (defectOperator)
open KFCausalClockFloorPureClockClockResponse (half_graph)
open KFCausalClockFloorGrowingClockResolvent (inverse_pairing inverse_selfAdjoint inverse_dense)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "L" => inverseL ε hε
local notation "D" => defectOperator ε hε
local notation "F" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hb m g k
local notation "J" => KFCausalClosedGraphForm.embedding F
local notation "G" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hb m g k

def unitResolvent : Hilbert →L[ℂ] Hilbert := KFCausalFormResolvent.resolvent J
local notation "R1" => unitResolvent ε hε h hh hb m g k

private theorem r_injective : Function.Injective R1 :=
  KFCausalFormResolvent.resolvent_injective J
    (KFCausalClosedGraphForm.embedding_injective F) (KFCausalClosedGraphForm.embedding_dense F)

private theorem r_positive (x : Hilbert) : 0 ≤ (inner ℂ (R1 x) x).re :=
  (KFCausalFormResolvent.resolvent_positive J x).trans_eq
    (congrArg Complex.re (KFCausalFormResolvent.resolvent_symmetric J x x).symm)

private theorem r_contraction (x : Hilbert) : ‖R1 x‖ ≤ ‖x‖ := by
  have hj : ‖J‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by
    simpa only [one_mul] using KFCausalClosedGraphForm.embedding_contraction F v)
  exact ((R1).le_opNorm x).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (KFCausalFormResolvent.resolvent_norm_le_one J hj) (norm_nonneg x))

private theorem shift_isUnit (a : ℝ) (ha : 0 < a) :
    IsUnit (KFCausalShiftedResolventFromOne.shift R1 a) :=
  KFCausalShiftedResolventFromOne.shift_isUnit R1 a ha (r_positive ε hε h hh hb m g k)
    (r_contraction ε hε h hh hb m g k) (KFCausalFormResolvent.resolvent_symmetric J)

def resolvent (a : ℝ) : Hilbert →L[ℂ] Hilbert := KFCausalShiftedResolventFromOne.resolvent R1 a
local notation "R" => resolvent ε hε h hh hb m g k

theorem resolves (a : ℝ) (ha : 0 < a) :
    KFCausalPositiveResolventBounds.Resolves G (R a) a :=
  KFCausalShiftedResolventFromOne.resolves R1 (r_injective ε hε h hh hb m g k) a
    (shift_isUnit ε hε h hh hb m g k a ha)

theorem weighted_resolvent_bound (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖L (R a f)‖ ≤ a⁻¹*‖L f‖ := by
  let hr := resolves ε hε h hh hb m g k a ha
  have hp := KFCausalClockFloorPotentialClockAccretivity.inverse_clock_accretive
    ε hε h hh hb m g k (KFCausalPositiveResolventBounds.point G (R a) a hr f)
  change 0 ≤ (inner ℂ (G (KFCausalPositiveResolventBounds.point G (R a) a hr f))
    (D (R a f))).re at hp
  rw [KFCausalPositiveResolventBounds.point_value,inner_sub_left,
    inner_smul_left_eq_smul,← inverse_pairing ε hε f (R a f),
    ← inverse_pairing ε hε (R a f) (R a f),
    KFCausalShiftedForm.complex_inner_square] at hp
  simp only [Complex.sub_re,Complex.real_smul,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hp
  have hl : a*‖L (R a f)‖^2 ≤ (inner ℂ (L f) (L (R a f))).re := by
    nlinarith
  by_cases hz : L (R a f) = 0
  · rw [hz,norm_zero]
    positivity
  have hn : 0 < ‖L (R a f)‖ := norm_pos_iff.mpr hz
  apply (le_inv_mul_iff₀ ha).mpr
  apply (mul_le_mul_iff_right₀ hn).mp
  have hi : (inner ℂ (L f) (L (R a f))).re ≤ ‖L f‖*‖L (R a f)‖ :=
    re_inner_le_norm (𝕜 := ℂ) (L f) (L (R a f))
  nlinarith

def weightedResolvent (a : ℝ) : Hilbert →L[ℂ] Hilbert :=
  ((L).comp (R a)).toLinearMap.extendOfNorm (L).toLinearMap

theorem weighted_intertwines (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    weightedResolvent ε hε h hh hb m g k a (L f)=L (R a f) :=
  LinearMap.extendOfNorm_eq (inverse_dense ε hε)
    ⟨a⁻¹,weighted_resolvent_bound ε hε h hh hb m g k a ha⟩ f

theorem weighted_norm_bound (a : ℝ) (ha : 0 < a) :
    ‖weightedResolvent ε hε h hh hb m g k a‖ ≤ a⁻¹ :=
  LinearMap.opNorm_extendOfNorm_le (inverse_dense ε hε) (inv_nonneg.mpr ha.le)
    (weighted_resolvent_bound ε hε h hh hb m g k a ha)

theorem dual_intertwines (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    R a (L f)=L ((weightedResolvent ε hε h hh hb m g k a).adjoint f) := by
  have he : (weightedResolvent ε hε h hh hb m g k a).comp L=(L).comp (R a) := by
    apply ContinuousLinearMap.ext
    intro x
    exact weighted_intertwines ε hε h hh hb m g k a ha x
  have hl := (inverse_selfAdjoint ε hε).isSymmetric.clm_adjoint_eq
  have hr := (KFCausalPositiveResolventBounds.resolvent_selfAdjoint G (R a) a
    (resolves ε hε h hh hb m g k a ha)
    (KFCausalClockFloorPotentialHamiltonian.hamiltonian_selfAdjoint ε hε h hh hb m g k)).isSymmetric.clm_adjoint_eq
  have hd := congrArg (fun A : Hilbert →L[ℂ] Hilbert => A.adjoint) he
  change ((weightedResolvent ε hε h hh hb m g k a).comp L).adjoint=
    ((L).comp (R a)).adjoint at hd
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_comp,hl,hr] at hd
  exact (congrArg (fun A : Hilbert →L[ℂ] Hilbert => A f) hd).symm

theorem resolvent_half_graph (a : ℝ) (ha : 0 < a) (f z : Hilbert)
    (hf : (f,z) ∈ (clockHalf ε).graph) :
    (R a f,(weightedResolvent ε hε h hh hb m g k a).adjoint z) ∈
      (clockHalf ε).graph := by
  apply (half_graph ε hε _ _).mpr
  rw [(half_graph ε hε f z).mp hf]
  exact dual_intertwines ε hε h hh hb m g k a ha z

theorem resolvent_half_domain (a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ (clockHalf ε).domain) : R a f ∈ (clockHalf ε).domain :=
  LinearPMap.mem_domain_of_mem_graph (resolvent_half_graph ε hε h hh hb m g k a ha
    f (clockHalf ε ⟨f,hf⟩) ((clockHalf ε).mem_graph ⟨f,hf⟩))

theorem resolvent_half_norm_bound (a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ (clockHalf ε).domain) :
    ‖clockHalf ε ⟨R a f,resolvent_half_domain ε hε h hh hb m g k a ha f hf⟩‖ ≤
      a⁻¹*‖clockHalf ε ⟨f,hf⟩‖ := by
  have hg := resolvent_half_graph ε hε h hh hb m g k a ha f
    (clockHalf ε ⟨f,hf⟩) ((clockHalf ε).mem_graph ⟨f,hf⟩)
  have he := (clockHalf ε).mem_graph_snd_inj' hg
    ((clockHalf ε).mem_graph ⟨R a f,resolvent_half_domain ε hε h hh hb m g k a ha f hf⟩) rfl
  change (weightedResolvent ε hε h hh hb m g k a).adjoint (clockHalf ε ⟨f,hf⟩)=
    clockHalf ε ⟨R a f,resolvent_half_domain ε hε h hh hb m g k a ha f hf⟩ at he
  rw [← he]
  apply ((weightedResolvent ε hε h hh hb m g k a).adjoint.le_opNorm _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [LinearIsometryEquiv.norm_map] using weighted_norm_bound ε hε h hh hb m g k a ha

#print axioms resolves
#print axioms weighted_resolvent_bound
#print axioms weighted_intertwines
#print axioms weighted_norm_bound
#print axioms dual_intertwines
#print axioms resolvent_half_graph
#print axioms resolvent_half_domain
#print axioms resolvent_half_norm_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorPotentialClockResolvent
