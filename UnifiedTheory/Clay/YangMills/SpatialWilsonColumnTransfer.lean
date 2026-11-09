/- The actual raw transfer with a spatial plaquette column omitted, and its
finite-chain dictionary. The temporal kinetic interaction is unchanged.
Temporal operator positivity is derived from its genuine Hilbert features. -/
import UnifiedTheory.Clay.YangMills.SpatialWilsonHistoryInsertion
import UnifiedTheory.Clay.YangMills.KernelPartitionNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SpatialWilsonColumnTransfer
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSingleLinkStaples SpatialPlaquetteCutGeometry
open SpatialWilsonReflectionKernel SpatialWilsonHistoryKernel SpatialWilsonHistoryInsertion
open SpatialWilsonInsertion FiniteKernelChain PositiveKernelForm KernelHilbertCompletion

variable (n : ℕ) [NeZero n]

def boundary (γ : Plaquette n → ℝ) : C(SpatialLinks (2 * n) Q, ℝ) :=
  ⟨weight n (fun p => γ p / 2),weight_continuous n _⟩

def kernelMap (γ : Plaquette n → ℝ) (β : ℝ) :
    C(SpatialLinks (2 * n) Q × SpatialLinks (2 * n) Q, ℝ) :=
  ⟨fun uv => boundary n γ uv.1 * kineticWeight character β 2 uv.1 uv.2 * boundary n γ uv.2,
    by
      have hk : Continuous (fun uv : SpatialLinks (2 * n) Q × SpatialLinks (2 * n) Q =>
          kineticWeight character β 2 uv.1 uv.2) := by
        have hχ := character_continuous
        unfold kineticWeight kineticAction
        fun_prop
      exact (((boundary n γ).continuous.comp continuous_fst).mul hk).mul
        ((boundary n γ).continuous.comp continuous_snd)⟩

def transfer (γ : Plaquette n → ℝ) (β : ℝ) :=
  CompactKernelOperator.operator (WilsonSlabOperator.measure (2 * n)) (kernelMap n γ β)

theorem boundary_pos (γ : Plaquette n → ℝ) (u : SpatialLinks (2 * n) Q) :
    0 < boundary n γ u := Real.exp_pos _

theorem kernelMap_pos (γ : Plaquette n → ℝ) (β : ℝ) (u v : SpatialLinks (2 * n) Q) :
    0 < kernelMap n γ β (u,v) :=
  mul_pos (mul_pos (boundary_pos n γ u) (Real.exp_pos _)) (boundary_pos n γ v)

theorem boundary_square (γ : Plaquette n → ℝ) (u : SpatialLinks (2 * n) Q) :
    (boundary n γ u)^2 = weight n γ u := by
  change (Real.exp (-action n (fun p => γ p / 2) u))^2 = Real.exp (-action n γ u)
  rw [pow_two, ← Real.exp_add]
  congr 1
  unfold action
  have he : (∑ p : Plaquette n, γ p / 2 * SpatialWilsonPlaquetteKernels.defect n p u) =
      (∑ p : Plaquette n, γ p * SpatialWilsonPlaquetteKernels.defect n p u) / 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [he]
  ring

theorem constant_boundary (β : ℝ) :
    boundary n (fun _ => β) = WilsonBoundaryTransfer.spatialBoundary (2 * n) β := by
  ext u
  change weight n (fun _ => β / 2) u = spatialWeight character β 2 u
  rw [constant_weight, show 2 * (β / 2) = β by ring]

theorem constant_kernelMap (β : ℝ) (u v : SpatialLinks (2 * n) Q) :
    kernelMap n (fun _ => β) β (u,v) = WilsonTemporalGauge.rawKernel character β 2 u v := by
  change boundary n (fun _ => β) u * _ * boundary n (fun _ => β) v = _
  rw [constant_boundary]
  rfl

def feature (γ : Plaquette n → ℝ) (β : ℝ) (hβ : 0 ≤ β) (u : SpatialLinks (2 * n) Q) :=
  (boundary n γ u : ℂ) • canonical
    (WilsonSlabPositivity.kineticPositiveKernel WilsonEnergyDensity.representation β 2 hβ) u

theorem feature_inner (γ : Plaquette n → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (u v : SpatialLinks (2 * n) Q) :
    inner ℂ (feature n γ β hβ u) (feature n γ β hβ v) = (kernelMap n γ β (u,v) : ℂ) := by
  rw [feature, feature, inner_smul_left, inner_smul_right, canonical_inner]
  simp only [WilsonSlabPositivity.kineticPositiveKernel, Complex.conj_ofReal]
  change (boundary n γ u : ℂ) * ((boundary n γ v : ℂ) *
    (kineticWeight character β 2 u v : ℂ)) = _
  simp only [kernelMap, ContinuousMap.coe_mk, Complex.ofReal_mul]
  ring

theorem feature_continuous (γ : Plaquette n → ℝ) (β : ℝ) (hβ : 0 ≤ β) :
    Continuous (feature n γ β hβ) := by
  apply (Complex.continuous_ofReal.comp (boundary n γ).continuous).smul
  apply WilsonSlabPositivity.continuous_canonical
  change Continuous (fun uv : SpatialLinks (2 * n) Q × SpatialLinks (2 * n) Q =>
    (kineticWeight character β 2 uv.1 uv.2 : ℂ))
  have hχ := character_continuous
  unfold kineticWeight kineticAction
  fun_prop

theorem transfer_positive (γ : Plaquette n → ℝ) (β : ℝ) (hβ : 0 ≤ β) :
    (transfer n γ β).IsPositive :=
  CompactKernelOperatorPositivity.operator_positive (WilsonSlabOperator.measure (2 * n))
    (kernelMap n γ β) (feature n γ β hβ) (feature_continuous n γ β hβ)
    (feature_inner n γ β hβ)

theorem weighted_chain (γ : Plaquette n → ℝ) (β : ℝ) (L : ℕ)
    (u : History n (Fin (L + 1))) :
    boundary n γ (u 0) * chain (kernelMap n γ β) L u * boundary n γ (u (Fin.last L)) =
      density n (Fin (L + 1)) (fun _ => γ) (fun _ : Fin L => β)
        Fin.castSucc Fin.succ u := by
  let w (t : Fin (L + 1)) := boundary n γ (u t)
  let k (t : Fin L) := kineticWeight character β 2 (u t.castSucc) (u t.succ)
  have hs := Fin.prod_univ_succ w
  have hl := Fin.prod_univ_castSucc w
  change w 0 * (∏ t : Fin L, w t.castSucc * k t * w t.succ) * w (Fin.last L) = _
  simp only [Finset.prod_mul_distrib]
  calc
    _ = (w 0 * ∏ t : Fin L, w t.succ) *
        ((∏ t : Fin L, w t.castSucc) * w (Fin.last L)) * ∏ t : Fin L, k t := by ring
    _ = (∏ t, w t)^2 * ∏ t : Fin L, k t := by rw [← hs, ← hl]; ring
    _ = _ := by
      rw [← Finset.prod_pow]
      change (∏ t, (boundary n γ (u t))^2) * _ = _
      simp only [boundary_square, density, k]

theorem endpoint_density (γ : Plaquette n → ℝ) (β : ℝ) (L : ℕ) :
    endpoint (WilsonSlabOperator.measure (2 * n)) (kernelMap n γ β) L
      (boundary n γ) (boundary n γ) =
      ∫ u, density n (Fin (L + 1)) (fun _ => γ) (fun _ : Fin L => β)
        Fin.castSucc Fin.succ u ∂measure n (Fin (L + 1)) := by
  unfold endpoint
  apply integral_congr_ae
  filter_upwards [] with u
  exact weighted_chain n γ β L u

/-- The literal all-time plaquette deletion controls the two actual raw
transfer chains with their own full spatial endpoint weights. -/
theorem column_partition_floor (q : Plaquette n) (hq : SpatialWilsonPlaquetteKernels.Crossing n q)
    (β : ℝ) (hβ : 0 ≤ β) (L : ℕ) :
    (SU2GaussianMass.mass β)^(L + 1) *
      endpoint (WilsonSlabOperator.measure (2 * n)) (kernelMap n (omitted n q β) β) L
        (boundary n (omitted n q β)) (boundary n (omitted n q β)) ≤
      endpoint (WilsonSlabOperator.measure (2 * n)) (kernelMap n (fun _ => β) β) L
        (boundary n (fun _ => β)) (boundary n (fun _ => β)) := by
  rw [endpoint_density, endpoint_density]
  simpa only [Fintype.card_fin] using partition_floor n (Fin (L + 1)) q hq β hβ
    (fun _ : Fin L => β) (fun _ => hβ) Fin.castSucc Fin.succ

end
end UnifiedTheory.Clay.YangMills.SpatialWilsonColumnTransfer
