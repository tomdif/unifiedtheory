/- At each physical time t, positive shifted resolvents of the residual
Hamiltonian (retaining the static and time-weighted ordered-potential rows)
preserve the unbounded half-clock domain, their scaled approximants converge
in the half-clock graph norm, and the intersection of the residual
Hamiltonian domain with the half-clock domain is a graph core for both
operators. -/
import UnifiedTheory.Audit.KFCausalClockFloorResidualClockAccretivity
import UnifiedTheory.Audit.KFCausalClockFloorPotentialClockCore

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorResidualClockCore
noncomputable section
open Filter
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf clockHalf_selfAdjoint)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorDefectOperator (defectOperator)
open KFCausalClockFloorPureClockClockResponse (half_graph)
open KFCausalClockFloorGrowingClockResolvent (inverse_pairing inverse_selfAdjoint inverse_dense)
open KFCausalClockFloorPotentialClockApproximation (cutoff cutoff_pos cutoff_tendsto)
open KFCausalHamiltonianCoreFromSources (graphMap sectorGraph source_graph_closure)

private theorem dense_contraction_identity {X E ι : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    (J : E → X) (hJ : DenseRange J) (S : ι → X →L[ℂ] X)
    (hS : ∀ i x, ‖S i x‖ ≤ ‖x‖) (l : Filter ι)
    (hc : ∀ w, Tendsto (fun i => S i (J w)) l (𝓝 (J w))) (x : X) :
    Tendsto (fun i => S i x) l (𝓝 x) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  obtain ⟨w,hw⟩ := hJ.exists_dist_lt x (show 0 < δ/3 from by positivity)
  have hl := Metric.tendsto_nhds.mp (hc w) (δ/3) (by positivity)
  filter_upwards [hl] with i hi
  have hd : dist (S i x) (S i (J w)) ≤ dist x (J w) := by
    simpa only [dist_eq_norm,map_sub] using hS i (x-J w)
  have ht := dist_triangle (S i x) (S i (J w)) x
  have ht' := dist_triangle (S i (J w)) (J w) x
  rw [dist_comm (J w) x] at ht'
  linarith

private theorem adjoint_contraction_identity {X ι : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    (S : ι → X →L[ℂ] X) (hS : ∀ i, ‖S i‖ ≤ 1) (l : Filter ι)
    (hc : ∀ x, Tendsto (fun i => S i x) l (𝓝 x)) (x : X) :
    Tendsto (fun i => (S i).adjoint x) l (𝓝 x) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have hd : 0 < 2*‖x‖+1 := by positivity
  have hl := Metric.tendsto_nhds.mp (hc x) (δ^2/(2*‖x‖+1)) (by positivity)
  filter_upwards [hl] with i hi
  have hn : ‖(S i).adjoint x‖ ≤ ‖x‖ := by
    apply ((S i).adjoint.le_opNorm x).trans
    simpa only [LinearIsometryEquiv.norm_map,one_mul] using
      mul_le_mul_of_nonneg_right (hS i) (norm_nonneg x)
  have hs := norm_sub_sq (𝕜 := ℂ) ((S i).adjoint x) x
  change ‖(S i).adjoint x-x‖^2 = ‖(S i).adjoint x‖^2-
    2*(inner ℂ ((S i).adjoint x) x).re+‖x‖^2 at hs
  rw [ContinuousLinearMap.adjoint_inner_left] at hs
  have hp := re_inner_le_norm (𝕜 := ℂ) x (x-S i x)
  rw [inner_sub_right,KFCausalShiftedForm.complex_inner_square] at hp
  change ‖x‖^2-(inner ℂ x (S i x)).re ≤ ‖x‖*‖x-S i x‖ at hp
  rw [norm_sub_rev x (S i x)] at hp
  rw [dist_eq_norm] at hi ⊢
  have hi' := (lt_div_iff₀ hd).mp hi
  have hnn := norm_nonneg ((S i).adjoint x)
  have hnx := norm_nonneg x
  have hne := norm_nonneg (S i x-x)
  have hnd := norm_nonneg ((S i).adjoint x-x)
  nlinarith

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k t : ℝ)
local notation "L" => inverseL ε hε
local notation "D" => defectOperator ε hε
local notation "F" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hb m g k t
local notation "J" => KFCausalClosedGraphForm.embedding F
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hb m g k t

def unitResolvent : Hilbert →L[ℂ] Hilbert := KFCausalFormResolvent.resolvent J
local notation "R1" => unitResolvent ε hε h hh hb m g k t

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
  KFCausalShiftedResolventFromOne.shift_isUnit R1 a ha (r_positive ε hε h hh hb m g k t)
    (r_contraction ε hε h hh hb m g k t) (KFCausalFormResolvent.resolvent_symmetric J)

def resolvent (a : ℝ) : Hilbert →L[ℂ] Hilbert := KFCausalShiftedResolventFromOne.resolvent R1 a
local notation "R" => resolvent ε hε h hh hb m g k t

theorem resolves (a : ℝ) (ha : 0 < a) :
    KFCausalPositiveResolventBounds.Resolves S (R a) a :=
  KFCausalShiftedResolventFromOne.resolves R1 (r_injective ε hε h hh hb m g k t) a
    (shift_isUnit ε hε h hh hb m g k t a ha)

theorem left_inverse (a : ℝ) (ha : 0 < a) (x : (S).domain) :
    R a (S x + a • (x : Hilbert)) = x :=
  KFCausalShiftedResolventFromOne.left_inverse R1 (r_injective ε hε h hh hb m g k t) a
    (shift_isUnit ε hε h hh hb m g k t a ha) x

theorem weighted_resolvent_bound (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖L (R a f)‖ ≤ a⁻¹*‖L f‖ := by
  let hr := resolves ε hε h hh hb m g k t a ha
  have hp := KFCausalClockFloorResidualClockAccretivity.residual_inverse_clock_accretive
    ε hε h hh hb m g k t (KFCausalPositiveResolventBounds.point S (R a) a hr f)
  change 0 ≤ (inner ℂ (S (KFCausalPositiveResolventBounds.point S (R a) a hr f))
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
local notation "T" => weightedResolvent ε hε h hh hb m g k t

theorem weighted_intertwines (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    T a (L f) = L (R a f) :=
  LinearMap.extendOfNorm_eq (inverse_dense ε hε)
    ⟨a⁻¹,weighted_resolvent_bound ε hε h hh hb m g k t a ha⟩ f

theorem weighted_norm_bound (a : ℝ) (ha : 0 < a) :
    ‖T a‖ ≤ a⁻¹ :=
  LinearMap.opNorm_extendOfNorm_le (inverse_dense ε hε) (inv_nonneg.mpr ha.le)
    (weighted_resolvent_bound ε hε h hh hb m g k t a ha)

theorem dual_intertwines (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    R a (L f) = L ((T a).adjoint f) := by
  have he : (T a).comp L = (L).comp (R a) := by
    apply ContinuousLinearMap.ext
    intro x
    exact weighted_intertwines ε hε h hh hb m g k t a ha x
  have hl := (inverse_selfAdjoint ε hε).isSymmetric.clm_adjoint_eq
  have hr := (KFCausalPositiveResolventBounds.resolvent_selfAdjoint S (R a) a
    (resolves ε hε h hh hb m g k t a ha)
    (KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian_selfAdjoint ε hε h hh hb m g k t)).isSymmetric.clm_adjoint_eq
  have hd := congrArg (fun A : Hilbert →L[ℂ] Hilbert => A.adjoint) he
  change ((T a).comp L).adjoint = ((L).comp (R a)).adjoint at hd
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_comp,hl,hr] at hd
  exact (congrArg (fun A : Hilbert →L[ℂ] Hilbert => A f) hd).symm

theorem resolvent_half_graph (a : ℝ) (ha : 0 < a) (f z : Hilbert)
    (hf : (f,z) ∈ (clockHalf ε).graph) :
    (R a f,(T a).adjoint z) ∈ (clockHalf ε).graph := by
  apply (half_graph ε hε _ _).mpr
  rw [(half_graph ε hε f z).mp hf]
  exact dual_intertwines ε hε h hh hb m g k t a ha z

theorem resolvent_half_domain (a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ (clockHalf ε).domain) : R a f ∈ (clockHalf ε).domain :=
  LinearPMap.mem_domain_of_mem_graph (resolvent_half_graph ε hε h hh hb m g k t a ha
    f (clockHalf ε ⟨f,hf⟩) ((clockHalf ε).mem_graph ⟨f,hf⟩))

theorem resolvent_half_norm_bound (a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ (clockHalf ε).domain) :
    ‖clockHalf ε ⟨R a f,resolvent_half_domain ε hε h hh hb m g k t a ha f hf⟩‖ ≤
      a⁻¹*‖clockHalf ε ⟨f,hf⟩‖ := by
  have hg := resolvent_half_graph ε hε h hh hb m g k t a ha f
    (clockHalf ε ⟨f,hf⟩) ((clockHalf ε).mem_graph ⟨f,hf⟩)
  have he := (clockHalf ε).mem_graph_snd_inj' hg
    ((clockHalf ε).mem_graph ⟨R a f,resolvent_half_domain ε hε h hh hb m g k t a ha f hf⟩) rfl
  change (T a).adjoint (clockHalf ε ⟨f,hf⟩) =
    clockHalf ε ⟨R a f,resolvent_half_domain ε hε h hh hb m g k t a ha f hf⟩ at he
  rw [← he]
  apply ((T a).adjoint.le_opNorm _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [LinearIsometryEquiv.norm_map] using weighted_norm_bound ε hε h hh hb m g k t a ha

def approximation (n : ℕ) : Hilbert →L[ℂ] Hilbert := cutoff n • R (cutoff n)
def weightedApproximation (n : ℕ) : Hilbert →L[ℂ] Hilbert := cutoff n • T (cutoff n)

theorem weighted_norm (n : ℕ) :
    ‖weightedApproximation ε hε h hh hb m g k t n‖ ≤ 1 := by
  rw [weightedApproximation,norm_smul,Real.norm_eq_abs,abs_of_pos (cutoff_pos n)]
  calc
    _ ≤ cutoff n * (cutoff n)⁻¹ := mul_le_mul_of_nonneg_left
      (weighted_norm_bound ε hε h hh hb m g k t (cutoff n) (cutoff_pos n)) (cutoff_pos n).le
    _ = 1 := mul_inv_cancel₀ (ne_of_gt (cutoff_pos n))

theorem approximation_strong (f : Hilbert) :
    Tendsto (fun n => approximation ε hε h hh hb m g k t n f) atTop (𝓝 f) := by
  exact (KFCausalYosidaApproximation.scaled_resolvent_strong_limit S R
    (KFCausalClosedGraphForm.hamiltonian_dense F)
    (resolves ε hε h hh hb m g k t)
    (KFCausalClosedGraphForm.hamiltonian_positive F)
    (left_inverse ε hε h hh hb m g k t) f).comp cutoff_tendsto

theorem weighted_strong (f : Hilbert) :
    Tendsto (fun n => weightedApproximation ε hε h hh hb m g k t n f) atTop (𝓝 f) := by
  apply dense_contraction_identity L (inverse_dense ε hε)
    (weightedApproximation ε hε h hh hb m g k t) _ atTop _ f
  · intro n x
    exact ((weightedApproximation ε hε h hh hb m g k t n).le_opNorm x).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (weighted_norm ε hε h hh hb m g k t n) (norm_nonneg x))
  · intro w
    have ht := (L).continuous.tendsto w |>.comp (approximation_strong ε hε h hh hb m g k t w)
    simpa only [Function.comp_def,weightedApproximation,approximation,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.map_smul_of_tower,weighted_intertwines ε hε h hh hb m g k t _ (cutoff_pos _)] using ht

theorem weighted_adjoint_strong (f : Hilbert) :
    Tendsto (fun n => (weightedApproximation ε hε h hh hb m g k t n).adjoint f) atTop (𝓝 f) :=
  adjoint_contraction_identity _ (weighted_norm ε hε h hh hb m g k t) atTop
    (weighted_strong ε hε h hh hb m g k t) f

theorem approximation_half_graph (n : ℕ) (f z : Hilbert)
    (hf : (f,z) ∈ (clockHalf ε).graph) :
    (approximation ε hε h hh hb m g k t n f,
      (weightedApproximation ε hε h hh hb m g k t n).adjoint z) ∈ (clockHalf ε).graph := by
  have hg := ((clockHalf ε).graph.restrictScalars ℝ).smul_mem (cutoff n)
    (resolvent_half_graph ε hε h hh hb m g k t (cutoff n) (cutoff_pos n) f z hf)
  have he : (weightedApproximation ε hε h hh hb m g k t n).adjoint =
      cutoff n • (T (cutoff n)).adjoint := by
    rw [weightedApproximation,← Complex.coe_smul,map_smulₛₗ]
    simp only [Complex.conj_ofReal,Complex.coe_smul]
  rw [he]
  exact hg

theorem approximation_residual_domain (n : ℕ) (f : Hilbert) :
    approximation ε hε h hh hb m g k t n f ∈ (S).domain :=
  ((S).domain.restrictScalars ℝ).smul_mem (cutoff n)
    (resolves ε hε h hh hb m g k t (cutoff n) (cutoff_pos n) f).1

theorem half_graph_convergence (f z : Hilbert) :
    Tendsto (fun n => (approximation ε hε h hh hb m g k t n f,
      (weightedApproximation ε hε h hh hb m g k t n).adjoint z)) atTop (𝓝 (f,z)) :=
  (approximation_strong ε hε h hh hb m g k t f).prodMk_nhds
    (weighted_adjoint_strong ε hε h hh hb m g k t z)

def commonDomain : Submodule ℂ Hilbert := (S).domain ⊓ (clockHalf ε).domain
def residualGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (S).graph ⊓ (clockHalf ε).domain.comap (LinearMap.fst ℂ Hilbert Hilbert)
def halfGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (clockHalf ε).graph ⊓ (S).domain.comap (LinearMap.fst ℂ Hilbert Hilbert)

theorem residual_graph_core :
    (residualGraph ε hε h hh hb m g k t).topologicalClosure = (S).graph := by
  have hd : (clockHalf ε).domain.topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp (clockHalf_selfAdjoint ε).dense_domain
  have he := source_graph_closure S (R 1) 1
    (resolves ε hε h hh hb m g k t 1 zero_lt_one)
    (left_inverse ε hε h hh hb m g k t 1 zero_lt_one)
    (KFCausalClosedGraphForm.hamiltonian_closed F)
    ⊤ (clockHalf ε).domain isClosed_univ hd (fun _ _ => trivial) (fun _ _ => trivial)
  have hm : (clockHalf ε).domain.map (graphMap (R 1) 1).toLinearMap ≤
      residualGraph ε hε h hh hb m g k t := by
    rintro p ⟨f,hf,rfl⟩
    obtain ⟨hx,hv⟩ := resolves ε hε h hh hb m g k t 1 zero_lt_one f
    exact ⟨(S).mem_graph_iff.mpr ⟨⟨R 1 f,hx⟩,rfl,hv⟩,
      resolvent_half_domain ε hε h hh hb m g k t 1 zero_lt_one f hf⟩
  have hc := Submodule.topologicalClosure_mono hm
  rw [he] at hc
  have hs : sectorGraph S ⊤ = (S).graph := by simp [sectorGraph]
  rw [hs] at hc
  exact le_antisymm (Submodule.topologicalClosure_minimal _ (fun _ hp => hp.1)
    (KFCausalClosedGraphForm.hamiltonian_closed F)) hc

theorem half_graph_core :
    (halfGraph ε hε h hh hb m g k t).topologicalClosure = (clockHalf ε).graph := by
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ (fun _ hp => hp.1)
      (clockHalf_selfAdjoint ε).isClosed
  · rintro ⟨f,z⟩ hf
    exact mem_closure_of_tendsto (half_graph_convergence ε hε h hh hb m g k t f z)
      (Eventually.of_forall fun n =>
        ⟨approximation_half_graph ε hε h hh hb m g k t n f z hf,
          approximation_residual_domain ε hε h hh hb m g k t n f⟩)

theorem common_dense : Dense (commonDomain ε hε h hh hb m g k t : Set Hilbert) := by
  have hs : ((clockHalf ε).domain : Set Hilbert) ⊆
      closure (commonDomain ε hε h hh hb m g k t : Set Hilbert) := by
    intro f hf
    exact mem_closure_of_tendsto (approximation_strong ε hε h hh hb m g k t f)
      (Eventually.of_forall fun n =>
        ⟨approximation_residual_domain ε hε h hh hb m g k t n f,
          LinearPMap.mem_domain_of_mem_graph
            (approximation_half_graph ε hε h hh hb m g k t n f
              (clockHalf ε ⟨f,hf⟩) ((clockHalf ε).mem_graph ⟨f,hf⟩))⟩)
  intro f
  exact closure_minimal hs isClosed_closure ((clockHalf_selfAdjoint ε).dense_domain f)

#print axioms resolves
#print axioms left_inverse
#print axioms weighted_resolvent_bound
#print axioms weighted_intertwines
#print axioms weighted_norm_bound
#print axioms dual_intertwines
#print axioms resolvent_half_graph
#print axioms resolvent_half_domain
#print axioms resolvent_half_norm_bound
#print axioms weighted_norm
#print axioms approximation_strong
#print axioms weighted_strong
#print axioms weighted_adjoint_strong
#print axioms approximation_half_graph
#print axioms approximation_residual_domain
#print axioms half_graph_convergence
#print axioms residual_graph_core
#print axioms half_graph_core
#print axioms common_dense
end
end UnifiedTheory.Audit.KFCausalClockFloorResidualClockCore
