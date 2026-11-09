/- Scaled positive resolvents of the actual ordered-potential Hamiltonian
converge in the half-clock graph norm. The weighted inverse-clock extension
and its adjoint converge strongly to the identity by contractivity. This
establishes half-clock graph approximation for the potential sector without
claiming a core for the full kinetic or residual Hamiltonian. -/
import UnifiedTheory.Audit.KFCausalClockFloorPotentialClockResolvent

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPotentialClockApproximation
noncomputable section
open Filter
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorGrowingClockResolvent (inverse_dense)
open KFCausalClockFloorPotentialClockResolvent

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
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "F" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hb m g k
local notation "J" => KFCausalClosedGraphForm.embedding F
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hb m g k
local notation "R1" => unitResolvent ε hε h hh hb m g k
local notation "R" => resolvent ε hε h hh hb m g k
local notation "L" => inverseL ε hε
local notation "T" => weightedResolvent ε hε h hh hb m g k

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

theorem left_inverse (a : ℝ) (ha : 0 < a) (x : (P).domain) :
    R a (P x + a • (x : Hilbert)) = x :=
  KFCausalShiftedResolventFromOne.left_inverse R1 (r_injective ε hε h hh hb m g k) a
    (shift_isUnit ε hε h hh hb m g k a ha) x

def cutoff (n : ℕ) : ℝ := (n:ℝ)+1

theorem cutoff_pos (n : ℕ) : 0 < cutoff n := by unfold cutoff; positivity

theorem cutoff_tendsto : Tendsto cutoff atTop atTop := by
  exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds

def approximation (n : ℕ) : Hilbert →L[ℂ] Hilbert := cutoff n • R (cutoff n)
def weightedApproximation (n : ℕ) : Hilbert →L[ℂ] Hilbert := cutoff n • T (cutoff n)

theorem weighted_norm (n : ℕ) :
    ‖weightedApproximation ε hε h hh hb m g k n‖ ≤ 1 := by
  rw [weightedApproximation,norm_smul,Real.norm_eq_abs,abs_of_pos (cutoff_pos n)]
  calc
    _ ≤ cutoff n * (cutoff n)⁻¹ := mul_le_mul_of_nonneg_left
      (weighted_norm_bound ε hε h hh hb m g k (cutoff n) (cutoff_pos n)) (cutoff_pos n).le
    _ = 1 := mul_inv_cancel₀ (ne_of_gt (cutoff_pos n))

theorem approximation_strong (f : Hilbert) :
    Tendsto (fun n => approximation ε hε h hh hb m g k n f) atTop (𝓝 f) := by
  exact (KFCausalYosidaApproximation.scaled_resolvent_strong_limit P R
    (KFCausalClosedGraphForm.hamiltonian_dense F)
    (resolves ε hε h hh hb m g k)
    (KFCausalClosedGraphForm.hamiltonian_positive F)
    (left_inverse ε hε h hh hb m g k) f).comp cutoff_tendsto

theorem weighted_strong (f : Hilbert) :
    Tendsto (fun n => weightedApproximation ε hε h hh hb m g k n f) atTop (𝓝 f) := by
  apply dense_contraction_identity L (inverse_dense ε hε)
    (weightedApproximation ε hε h hh hb m g k) _ atTop _ f
  · intro n x
    exact ((weightedApproximation ε hε h hh hb m g k n).le_opNorm x).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (weighted_norm ε hε h hh hb m g k n) (norm_nonneg x))
  · intro w
    have ht := (L).continuous.tendsto w |>.comp (approximation_strong ε hε h hh hb m g k w)
    simpa only [Function.comp_def,weightedApproximation,approximation,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.map_smul_of_tower,weighted_intertwines ε hε h hh hb m g k _ (cutoff_pos _)] using ht

theorem weighted_adjoint_strong (f : Hilbert) :
    Tendsto (fun n => (weightedApproximation ε hε h hh hb m g k n).adjoint f) atTop (𝓝 f) :=
  adjoint_contraction_identity _ (weighted_norm ε hε h hh hb m g k) atTop
    (weighted_strong ε hε h hh hb m g k) f

theorem approximation_half_graph (n : ℕ) (f z : Hilbert)
    (hf : (f,z) ∈ (clockHalf ε).graph) :
    (approximation ε hε h hh hb m g k n f,
      (weightedApproximation ε hε h hh hb m g k n).adjoint z) ∈ (clockHalf ε).graph := by
  have hg := ((clockHalf ε).graph.restrictScalars ℝ).smul_mem (cutoff n)
    (resolvent_half_graph ε hε h hh hb m g k (cutoff n) (cutoff_pos n) f z hf)
  have he : (weightedApproximation ε hε h hh hb m g k n).adjoint =
      cutoff n • (T (cutoff n)).adjoint := by
    rw [weightedApproximation,← Complex.coe_smul,map_smulₛₗ]
    simp only [Complex.conj_ofReal,Complex.coe_smul]
  rw [he]
  exact hg

theorem approximation_potential_domain (n : ℕ) (f : Hilbert) :
    approximation ε hε h hh hb m g k n f ∈ (P).domain :=
  ((P).domain.restrictScalars ℝ).smul_mem (cutoff n)
    (resolves ε hε h hh hb m g k (cutoff n) (cutoff_pos n) f).1

theorem half_graph_convergence (f z : Hilbert) :
    Tendsto (fun n => (approximation ε hε h hh hb m g k n f,
      (weightedApproximation ε hε h hh hb m g k n).adjoint z)) atTop (𝓝 (f,z)) :=
  (approximation_strong ε hε h hh hb m g k f).prodMk_nhds
    (weighted_adjoint_strong ε hε h hh hb m g k z)

#print axioms left_inverse
#print axioms cutoff_pos
#print axioms cutoff_tendsto
#print axioms weighted_norm
#print axioms approximation_strong
#print axioms weighted_strong
#print axioms weighted_adjoint_strong
#print axioms approximation_half_graph
#print axioms approximation_potential_domain
#print axioms half_graph_convergence
end
end UnifiedTheory.Audit.KFCausalClockFloorPotentialClockApproximation
