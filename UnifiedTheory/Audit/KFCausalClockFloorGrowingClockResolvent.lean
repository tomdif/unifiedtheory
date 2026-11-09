/- Every positive shifted resolvent of the actual growing Hamiltonian
preserves the unbounded half-clock domain. Inverse-clock accretivity first
gives a weighted contraction; extension along the dense inverse-half-clock
range and adjoint duality construct the half-clock graph witness. This
does not assert preservation of the static kinetic domains or a common
operator core for the full time-dependent Hamiltonian. -/
import UnifiedTheory.Audit.KFCausalClockFloorGrowingClockAccretivity
import UnifiedTheory.Audit.KFCausalClockFloorGrowingYosida
import UnifiedTheory.Audit.KFCausalClockFloorPureClockClockResponse
import Mathlib.Analysis.Normed.Operator.Extend

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGrowingClockResolvent
noncomputable section
open MeasureTheory
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf inverseClockHalf inverseClockHalf_domain
  inverseClockHalf_selfAdjoint clockHalf_selfAdjoint inverseAction_coe halfWeight)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorDefectOperator (defectOperator defectOperator_coe)
open KFCausalClockFloorPureClockClockResponse (half_graph)

variable (ε : ℝ) (hε : 0 < ε)
local notation "L" => inverseL ε hε
local notation "D" => defectOperator ε hε

theorem inverse_pairing (f g : Hilbert) :
    (ε : ℂ) * inner ℂ (L f) (L g) = inner ℂ f (D g) := by
  rw [L2.inner_def,L2.inner_def,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [inverseAction_coe ε hε f,inverseAction_coe ε hε g,
    defectOperator_coe ε hε g] with x hf hg hd
  change (L f) x = _ at hf
  change (L g) x = _ at hg
  rw [hf,hg,hd]
  have hs : (halfWeight ε x)^2 = Real.exp x.1+ε := Real.sq_sqrt (by positivity)
  have he : ε * ((halfWeight ε x)⁻¹)^2 =
      KFCausalClockFloorCanonicalDefect.defect ε x.1 := by
    rw [inv_pow,hs]
    rfl
  have hc : (ε : ℂ) * ((halfWeight ε x : ℂ)⁻¹)^2 =
      (KFCausalClockFloorCanonicalDefect.defect ε x.1 : ℂ) := by
    exact_mod_cast he
  change (ε : ℂ) * inner ℂ ((halfWeight ε x : ℂ)⁻¹ • f x)
    ((halfWeight ε x : ℂ)⁻¹ • g x) =
      inner ℂ (f x) ((KFCausalClockFloorCanonicalDefect.defect ε x.1 : ℂ) • g x)
  rw [inner_smul_left,inner_smul_right,inner_smul_right]
  simp only [map_inv₀,Complex.conj_ofReal]
  calc
    _ = ((ε:ℂ) * ((halfWeight ε x : ℂ)⁻¹)^2) * inner ℂ (f x) (g x) := by ring
    _ = _ := by rw [hc]

theorem inverse_selfAdjoint : IsSelfAdjoint L := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  have hs := LinearPMap.adjoint_isFormalAdjoint (inverseClockHalf_selfAdjoint ε).dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp (inverseClockHalf_selfAdjoint ε)] at hs
  intro f g
  exact hs ⟨f,inverseClockHalf_domain ε hε f⟩ ⟨g,inverseClockHalf_domain ε hε g⟩

theorem inverse_dense : DenseRange L := by
  apply (clockHalf_selfAdjoint ε).dense_domain.mono
  intro x hx
  exact ⟨clockHalf ε ⟨x,hx⟩,
    ((half_graph ε hε x _).mp ((clockHalf ε).mem_graph ⟨x,hx⟩)).symm⟩

variable (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hb m g k
local notation "R" => KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hb m g k

theorem weighted_resolvent_bound (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖L (R a f)‖ ≤ a⁻¹*‖L f‖ := by
  let hr := KFCausalClockFloorGrowingYosida.resolves ε hε h hh hb m g k a ha
  have hp := KFCausalClockFloorGrowingClockAccretivity.inverse_clock_accretive
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
    (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hb m g k a ha)
    (KFCausalClockFloorGrowingHamiltonian.hamiltonian_selfAdjoint ε hε h hh hb m g k)).isSymmetric.clm_adjoint_eq
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

#print axioms inverse_pairing
#print axioms inverse_selfAdjoint
#print axioms inverse_dense
#print axioms weighted_resolvent_bound
#print axioms weighted_intertwines
#print axioms weighted_norm_bound
#print axioms dual_intertwines
#print axioms resolvent_half_graph
#print axioms resolvent_half_domain
#print axioms resolvent_half_norm_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorGrowingClockResolvent
