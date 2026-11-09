/- Actual plaquette transport through a physical Wilson slab. Temporal gauge
variables remain integrated under the constructed ground slab law. The
resulting absolute Dirichlet control does not assert a relative O(a) bound
or a surviving renormalized continuum observable. -/
import UnifiedTheory.Clay.YangMills.WilsonGroundSlabEnergy
import UnifiedTheory.Clay.YangMills.WilsonBoundaryTransfer
import UnifiedTheory.Clay.YangMills.WilsonCylinderSpectralBridge
import UnifiedTheory.Clay.YangMills.WilsonGroundHeatBath
import UnifiedTheory.Clay.YangMills.WilsonGroundTranslation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonPlaquetteTransport
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonTimeSlab WilsonSlabGauge
open WilsonPositiveGroundState WilsonGroundLocalComparison
open ContinuousBoundaryMoments TransferEnergySurvival WilsonSlabContraction
open scoped Topology NNReal

/-- Chord distance in the actual unit-quaternion realization of SU(2). -/
def chord (a b : WilsonSlabOperator.Q) : ℝ := ‖(a : Quaternion ℝ) - (b : Quaternion ℝ)‖

theorem chord_nonneg (a b : WilsonSlabOperator.Q) : 0 ≤ chord a b := norm_nonneg _

theorem chord_symm (a b : WilsonSlabOperator.Q) : chord a b = chord b a := norm_sub_rev _ _

/-- The unnormalized fundamental trace defect is exactly the squared chord. -/
theorem chord_squared (a b : WilsonSlabOperator.Q) :
    (chord a b)^2 = 2 - (WilsonSingleLinkStaples.character (a * b⁻¹)).re := by
  rw [WilsonSingleLinkStaples.character_re]
  change ‖(a : Quaternion ℝ) - (b : Quaternion ℝ)‖^2 =
    2 - 2 * ((a : Quaternion ℝ) * star (b : Quaternion ℝ)).re
  rw [norm_sub_sq_real, CStarRing.norm_of_mem_unitary a.property,
    CStarRing.norm_of_mem_unitary b.property, Quaternion.inner_def]
  ring

theorem inverse_chord (a b : WilsonSlabOperator.Q) : chord a⁻¹ b⁻¹ = chord a b := by
  change ‖star (a : Quaternion ℝ) - star (b : Quaternion ℝ)‖ = _
  rw [← star_sub, Quaternion.norm_star]
  rfl

/-- Unitarity makes multiplication Lipschitz with one unit coefficient per input. -/
theorem product_chord (a b c d : WilsonSlabOperator.Q) :
    chord (a * b) (c * d) ≤ chord a c + chord b d := by
  change ‖(a : Quaternion ℝ) * (b : Quaternion ℝ) -
    (c : Quaternion ℝ) * (d : Quaternion ℝ)‖ ≤ _
  calc
    _ = ‖((a : Quaternion ℝ) - c) * b + c * ((b : Quaternion ℝ) - d)‖ := by
      congr 1
      noncomm_ring
    _ ≤ ‖((a : Quaternion ℝ) - c) * b‖ + ‖c * ((b : Quaternion ℝ) - d)‖ := norm_add_le _ _
    _ = chord a c + chord b d := by
      rw [norm_mul, norm_mul, CStarRing.norm_of_mem_unitary b.property,
        CStarRing.norm_of_mem_unitary c.property, mul_one, one_mul]
      rfl

/-- Exact four-link geometry, retaining both inverse occurrences. -/
theorem four_link_chord (a b c d a' b' c' d' : WilsonSlabOperator.Q) :
    chord (a * b * c⁻¹ * d⁻¹) (a' * b' * c'⁻¹ * d'⁻¹) ≤
      chord a a' + chord b b' + chord c c' + chord d d' := by
  have h1 := product_chord (a * b * c⁻¹) d⁻¹ (a' * b' * c'⁻¹) d'⁻¹
  have h2 := product_chord (a * b) c⁻¹ (a' * b') c'⁻¹
  have h3 := product_chord a b a' b'
  rw [inverse_chord] at h1 h2
  linarith

/-- The actual unnormalized trace has Lipschitz constant two. -/
theorem character_difference (a b : WilsonSlabOperator.Q) :
    |(WilsonSingleLinkStaples.character a).re - (WilsonSingleLinkStaples.character b).re| ≤
      2 * chord a b := by
  have h := abs_real_inner_le_norm ((a : Quaternion ℝ) - b) (1 : Quaternion ℝ)
  simp only [Quaternion.inner_def, star_one, mul_one, norm_one, Quaternion.re_sub] at h
  rw [WilsonSingleLinkStaples.character_re, WilsonSingleLinkStaples.character_re]
  calc
    _ = 2 * |(a : Quaternion ℝ).re - (b : Quaternion ℝ).re| := by rw [← mul_sub, abs_mul]; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by norm_num)

/-- Four actual temporal defects control the squared four-link trace increment. -/
theorem four_link_trace_squared (a b c d a' b' c' d' : WilsonSlabOperator.Q) :
    ((WilsonSingleLinkStaples.character (a * b * c⁻¹ * d⁻¹)).re -
      (WilsonSingleLinkStaples.character (a' * b' * c'⁻¹ * d'⁻¹)).re)^2 ≤
      16 * ((chord a a')^2 + (chord b b')^2 + (chord c c')^2 + (chord d d')^2) := by
  have h := (character_difference (a * b * c⁻¹ * d⁻¹) (a' * b' * c'⁻¹ * d'⁻¹)).trans
    (mul_le_mul_of_nonneg_left (four_link_chord a b c d a' b' c' d') (by norm_num))
  have hq := mul_self_le_mul_self (abs_nonneg _) h
  rw [← sq, sq_abs] at hq
  have hc : (chord a a' + chord b b' + chord c c' + chord d d')^2 ≤
      4 * ((chord a a')^2 + (chord b b')^2 + (chord c c')^2 + (chord d d')^2) := by
    nlinarith [sq_nonneg (chord a a' - chord b b'), sq_nonneg (chord a a' - chord c c'),
      sq_nonneg (chord a a' - chord d d'), sq_nonneg (chord b b' - chord c c'),
      sq_nonneg (chord b b' - chord d d'), sq_nonneg (chord c c' - chord d d')]
  nlinarith

variable (n : ℕ) [NeZero n]

/-- A genuine gauge-invariant slice observable from the spatial Wilson action. -/
def plaquette (x : SpatialVertex n) (i j : Fin 3) : C(Slice n, ℝ) :=
  ⟨fun u => (WilsonSingleLinkStaples.character (spatialHolonomy u x i j)).re, by
    have hc := WilsonSingleLinkStaples.character_continuous
    unfold spatialHolonomy
    fun_prop⟩

omit [NeZero n] in
theorem plaquette_gauge (x : SpatialVertex n) (i j : Fin 3)
    (h : SliceGauge n WilsonSlabOperator.Q) (u : Slice n) :
    plaquette n x i j (gaugeSlice h u) = plaquette n x i j u := by
  change (WilsonSingleLinkStaples.character (spatialHolonomy (gaugeSlice h u) x i j)).re = _
  rw [spatialHolonomy_gauge, WilsonSingleLinkStaples.character_classFunction]
  rfl

/-- The temporal defect at one actual spatial link in the actual slab variables. -/
def temporalDefect (x : SpatialVertex n) (i : Fin 3) (z : WilsonGroundSlabEnergy.Slab n) : ℝ :=
  2 - (WilsonSingleLinkStaples.character (temporalHolonomy z.1.1 z.1.2 z.2 x i)).re

omit [NeZero n] in
theorem temporalDefect_continuous (x : SpatialVertex n) (i : Fin 3) :
    Continuous (temporalDefect n x i) := by
  have hc := WilsonSingleLinkStaples.character_continuous
  unfold temporalDefect temporalHolonomy
  fun_prop

omit [NeZero n] in
theorem temporalDefect_nonneg (x : SpatialVertex n) (i : Fin 3)
    (z : WilsonGroundSlabEnergy.Slab n) : 0 ≤ temporalDefect n x i z :=
  (WilsonSlabBounds.characterDefect_bounds (temporalHolonomy z.1.1 z.1.2 z.2 x i)).1

omit [NeZero n] in
/-- The actual temporal holonomy is precisely the chord between aligned spatial links. -/
theorem temporalDefect_chord (x : SpatialVertex n) (i : Fin 3)
    (z : WilsonGroundSlabEnergy.Slab n) :
    (chord (z.1.1 (x, i)) (gaugeSlice z.2 z.1.2 (x, i)))^2 = temporalDefect n x i z := by
  rw [chord_symm, chord_squared]
  rfl

omit [NeZero n] in
/-- Pointwise temporal transport of the gauge-invariant spatial plaquette.
All four actual temporal plaquettes occur, including any repeated links. -/
theorem plaquette_increment_bound (x : SpatialVertex n) (i j : Fin 3)
    (z : WilsonGroundSlabEnergy.Slab n) :
    (plaquette n x i j z.1.1 - plaquette n x i j z.1.2)^2 ≤
      16 * (temporalDefect n x i z + temporalDefect n (spatialStep n x i) j z +
        temporalDefect n (spatialStep n x j) i z + temporalDefect n x j z) := by
  rw [← plaquette_gauge n x i j z.2 z.1.2]
  have h := four_link_trace_squared
    (z.1.1 (x, i)) (z.1.1 (spatialStep n x i, j))
    (z.1.1 (spatialStep n x j, i)) (z.1.1 (x, j))
    (gaugeSlice z.2 z.1.2 (x, i)) (gaugeSlice z.2 z.1.2 (spatialStep n x i, j))
    (gaugeSlice z.2 z.1.2 (spatialStep n x j, i)) (gaugeSlice z.2 z.1.2 (x, j))
  simp_rw [temporalDefect_chord] at h
  exact h


local instance slabBorel : BorelSpace (WilsonGroundSlabEnergy.Slab n) :=
  WilsonGroundSlabEnergy.slabBorel n

/-- The physical transfer pairing is the integral of its actual full kernel. -/
theorem transfer_pairing (β : ℝ) (f : C(Slice n, ℝ)) :
    (inner ℂ (embed (measure n) f) (transfer n β (embed (measure n) f))).re =
      ∫ uv, kernelMap n β uv * f uv.1 * f uv.2
        ∂(WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n) := by
  have ht : transfer n β (embed (measure n) f) =
      embed (measure n) (realSmoothing (measure n) (kernelMap n β) f) := by
    change transfer n β (ContinuousMap.toLp 2 (measure n) ℂ (complexify f)) =
      ContinuousMap.toLp 2 (measure n) ℂ
        (complexify (realSmoothing (measure n) (kernelMap n β) f))
    rw [complexify_realSmoothing]
    rfl
  rw [ht, WilsonCylinderSpectralBridge.embed_inner, Complex.ofReal_re]
  simp_rw [realSmoothing_integral]
  have hc : Continuous (fun uv : Slice n × Slice n => kernelMap n β uv * f uv.1 * f uv.2) :=
    (((kernelMap n β).continuous).mul (f.continuous.comp continuous_fst)).mul
      (f.continuous.comp continuous_snd)
  rw [integral_prod _ (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with v
  ring

/-- Ground-weighted observable norm is the actual stationary second moment. -/
theorem ground_norm (β : ℝ) (hβ : 0 ≤ β) (F : C(Slice n, ℝ)) :
    ‖embed (measure n) (F * ground n β hβ)‖^2 =
      GroundStateDirichlet.normSquared (measure n) (ground n β hβ) F := by
  have h := real_embedding_norm_sq (measure n) (F * ground n β hβ)
  change ‖embed (measure n) (F * ground n β hβ)‖^2 = _ at h
  rw [h]
  unfold GroundStateDirichlet.normSquared
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [ContinuousMap.mul_apply]
  ring

/-- The kernel ground-state transform and the actual normalized Hilbert transfer agree. -/
theorem ground_pairing (β : ℝ) (hβ : 0 ≤ β) (F : C(Slice n, ℝ)) :
    (inner ℂ (embed (measure n) (F * ground n β hβ))
      (normalized n β (embed (measure n) (F * ground n β hβ)))).re =
      GroundStateDirichlet.pairing (measure n) (kernelMap n β)
        (ground n β hβ) ‖transfer n β‖ F := by
  have hs (w : Hilbert n) : (inner ℂ w (normalized n β w)).re =
      ‖transfer n β‖⁻¹ * (inner ℂ w (transfer n β w)).re := by
    change (inner ℂ w ((‖transfer n β‖⁻¹ : ℝ) • transfer n β w)).re = _
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_real_right,
      Complex.smul_re, smul_eq_mul]
  rw [hs, transfer_pairing, ← integral_const_mul]
  unfold GroundStateDirichlet.pairing
  apply integral_congr_ae
  filter_upwards [] with uv
  simp only [ContinuousMap.mul_apply, GroundStateDirichlet.edgeDensity]
  ring

/-- Exact equality with the genuine Hilbert-space defect
used in the physical-time survival criterion. -/
theorem hilbert_dirichlet_eq (β : ℝ) (hβ : 0 ≤ β) (F : C(Slice n, ℝ)) :
    TransferEnergySurvival.dirichlet (normalized n β) (embed (measure n) (F * ground n β hβ)) =
      GroundStateDirichlet.dirichlet (measure n) (kernelMap n β)
        (ground n β hβ) ‖transfer n β‖ F := by
  unfold TransferEnergySurvival.dirichlet GroundStateDirichlet.dirichlet
  rw [ground_norm, ground_pairing]

/-- The actual physical-transfer Dirichlet form is half the actual slab squared increment. -/
theorem dirichlet_slab (β : ℝ) (hβ : 0 ≤ β) (F : C(Slice n, ℝ)) :
    TransferEnergySurvival.dirichlet (normalized n β) (embed (measure n) (F * ground n β hβ)) =
      (1 / 2 : ℝ) * ∫ z, (F z.1.1 - F z.1.2)^2 ∂WilsonGroundSlabEnergy.law n β hβ := by
  rw [hilbert_dirichlet_eq]
  rw [GroundStateDirichlet.dirichlet_expectation (measure n) (kernelMap n β)
    (kernelMap n β).continuous
    (fun uv => (kernel_positive WilsonSingleLinkStaples.character
      WilsonSingleLinkStaples.character_continuous β 2 uv.1 uv.2).le)
    (kernelMap_symm n β) (ground n β hβ) (ground n β hβ).continuous
    (fun u => (ground_pos n β hβ u).le) ‖transfer n β‖
    (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1
    (ground_equation n β hβ) F F.continuous]
  let H : C(Slice n × Slice n, ℝ) :=
    ⟨fun uv => (F uv.1 - F uv.2)^2,
      ((F.continuous.comp continuous_fst).sub (F.continuous.comp continuous_snd)).pow 2⟩
  exact congrArg (fun r : ℝ => (1 / 2 : ℝ) * r)
    (WilsonGroundSlabEnergy.pair_integral n β hβ H).symm

/-- Integrated transport involves exactly four true temporal plaquettes, without volume factors. -/
theorem plaquette_dirichlet_local (β : ℝ) (hβ : 0 ≤ β)
    (x : SpatialVertex n) (i j : Fin 3) :
    TransferEnergySurvival.dirichlet (normalized n β)
      (embed (measure n) (plaquette n x i j * ground n β hβ)) ≤
    8 * ((∫ z, temporalDefect n x i z ∂WilsonGroundSlabEnergy.law n β hβ) +
      (∫ z, temporalDefect n (spatialStep n x i) j z ∂WilsonGroundSlabEnergy.law n β hβ) +
      (∫ z, temporalDefect n (spatialStep n x j) i z ∂WilsonGroundSlabEnergy.law n β hβ) +
      (∫ z, temporalDefect n x j z ∂WilsonGroundSlabEnergy.law n β hβ)) := by
  have hc : Continuous (fun z : WilsonGroundSlabEnergy.Slab n =>
      (plaquette n x i j z.1.1 - plaquette n x i j z.1.2)^2) :=
    (((plaquette n x i j).continuous.comp (continuous_fst.comp continuous_fst)).sub
      ((plaquette n x i j).continuous.comp (continuous_snd.comp continuous_fst))).pow 2
  have hi (y : SpatialVertex n) (a : Fin 3) :=
    (temporalDefect_continuous n y a).integrable_of_hasCompactSupport
      (μ := WilsonGroundSlabEnergy.law n β hβ) (HasCompactSupport.of_compactSpace _)
  have hsum := ((hi x i).add (hi (spatialStep n x i) j)).add
    (hi (spatialStep n x j) i) |>.add (hi x j)
  have hb := integral_mono
    (hc.integrable_of_hasCompactSupport (μ := WilsonGroundSlabEnergy.law n β hβ)
      (HasCompactSupport.of_compactSpace _)) (hsum.const_mul 16)
    (plaquette_increment_bound n x i j)
  simp only [integral_const_mul, Pi.add_apply] at hb
  have hi12 : Integrable (fun z => temporalDefect n x i z +
      temporalDefect n (spatialStep n x i) j z) (WilsonGroundSlabEnergy.law n β hβ) :=
    (hi x i).add (hi (spatialStep n x i) j)
  have hi123 : Integrable (fun z => temporalDefect n x i z +
      temporalDefect n (spatialStep n x i) j z + temporalDefect n (spatialStep n x j) i z)
      (WilsonGroundSlabEnergy.law n β hβ) := hi12.add (hi (spatialStep n x j) i)
  rw [integral_add hi123 (hi x j), integral_add hi12 (hi (spatialStep n x j) i),
    integral_add (hi x i) (hi (spatialStep n x i) j)] at hb
  rw [dirichlet_slab]
  linarith


/-- The actual ground mean is integration against the constructed stationary law. -/
theorem ground_mean_integral (β : ℝ) (hβ : 0 ≤ β) (F : C(Slice n, ℝ)) :
    WilsonInteriorVacuum.groundMean n β hβ F =
      ∫ u, F u ∂WilsonGroundHeatBath.groundLaw n β hβ := by
  exact (GroundStateDirichlet.stationary_integral (measure n) (ground n β hβ)
    (ground n β hβ).continuous F).symm

/-- Centering uses the actual stationary Wilson ground-state measure. -/
def centered (β : ℝ) (hβ : 0 ≤ β) (F : C(Slice n, ℝ)) : C(Slice n, ℝ) :=
  F - ContinuousMap.const _ (WilsonInteriorVacuum.groundMean n β hβ F)

def centeredAmplitude (β : ℝ) (hβ : 0 ≤ β) (F : C(Slice n, ℝ)) : Hilbert n :=
  embed (measure n) (centered n β hβ F * ground n β hβ)

def groundVariance (β : ℝ) (hβ : 0 ≤ β) (F : C(Slice n, ℝ)) : ℝ :=
  ∫ u, (F u - WilsonInteriorVacuum.groundMean n β hβ F)^2
    ∂WilsonGroundHeatBath.groundLaw n β hβ

theorem centered_mean_zero (β : ℝ) (hβ : 0 ≤ β) (F : C(Slice n, ℝ)) :
    WilsonInteriorVacuum.groundMean n β hβ (centered n β hβ F) = 0 := by
  let m := WilsonInteriorVacuum.groundMean n β hβ F
  have hiF : Integrable (fun u => (ground n β hβ u)^2 * F u) (measure n) :=
    (((ground n β hβ).continuous.pow 2).mul F.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiC : Integrable (fun u => (ground n β hβ u)^2 * m) (measure n) :=
    (((ground n β hβ).continuous.pow 2).mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ u, (ground n β hβ u)^2 * (F u - m) ∂measure n) = 0
  simp_rw [mul_sub]
  rw [integral_sub hiF hiC, integral_mul_const, ground_square_integral, one_mul]
  exact sub_self _

/-- This amplitude has no vacuum component. -/
theorem centered_orthogonal (β : ℝ) (hβ : 0 ≤ β) (F : C(Slice n, ℝ)) :
    inner ℂ (WilsonVacuumConvergence.vacuum n β hβ) (centeredAmplitude n β hβ F) = 0 := by
  change inner ℂ (embed (measure n) (ground n β hβ))
    (embed (measure n) (centered n β hβ F * ground n β hβ)) = 0
  rw [WilsonCylinderSpectralBridge.embed_inner]
  have hm : (∫ u, ground n β hβ u *
      (centered n β hβ F * ground n β hβ) u ∂measure n) = 0 := by
    calc
      _ = WilsonInteriorVacuum.groundMean n β hβ (centered n β hβ F) := by
        apply integral_congr_ae
        filter_upwards [] with u
        simp only [ContinuousMap.mul_apply]
        ring
      _ = 0 := centered_mean_zero n β hβ F
  rw [hm, Complex.ofReal_zero]

/-- The actual surviving size is precisely the stationary variance. -/
theorem centered_norm (β : ℝ) (hβ : 0 ≤ β) (F : C(Slice n, ℝ)) :
    ‖centeredAmplitude n β hβ F‖^2 = groundVariance n β hβ F := by
  unfold centeredAmplitude
  rw [ground_norm]
  unfold groundVariance WilsonGroundHeatBath.groundLaw
  rw [GroundStateDirichlet.stationary_integral (measure n) (ground n β hβ)
    (ground n β hβ).continuous]
  rfl

/-- Subtracting any constant leaves the actual physical Dirichlet form unchanged. -/
theorem dirichlet_sub_const (β : ℝ) (hβ : 0 ≤ β) (F : C(Slice n, ℝ)) (c : ℝ) :
    TransferEnergySurvival.dirichlet (normalized n β)
      (embed (measure n) ((F - ContinuousMap.const _ c) * ground n β hβ)) =
    TransferEnergySurvival.dirichlet (normalized n β)
      (embed (measure n) (F * ground n β hβ)) := by
  rw [dirichlet_slab, dirichlet_slab]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply]
  ring

theorem centered_dirichlet (β : ℝ) (hβ : 0 ≤ β) (F : C(Slice n, ℝ)) :
    TransferEnergySurvival.dirichlet (normalized n β) (centeredAmplitude n β hβ F) =
      TransferEnergySurvival.dirichlet (normalized n β)
        (embed (measure n) (F * ground n β hβ)) :=
  dirichlet_sub_const n β hβ F (WilsonInteriorVacuum.groundMean n β hβ F)

/-- Nonnegativity follows directly from the constructed actual slab law. -/
theorem dirichlet_nonneg (β : ℝ) (hβ : 0 ≤ β) (F : C(Slice n, ℝ)) :
    0 ≤ TransferEnergySurvival.dirichlet (normalized n β)
      (embed (measure n) (F * ground n β hβ)) := by
  rw [dirichlet_slab]
  exact mul_nonneg (by norm_num) (integral_nonneg (fun _ => sq_nonneg _))


/-- Translation symmetry removes the spatial-volume loss from this actual
physical-transfer estimate. This is an absolute, not a relative, bound. -/
theorem plaquette_dirichlet_bound (β : ℝ) (hβ : 0 < β)
    (x : SpatialVertex n) (i j : Fin 3) :
    TransferEnergySurvival.dirichlet (normalized n β)
      (embed (measure n) (plaquette n x i j * ground n β hβ.le)) ≤
      192 * WilsonGroundSlabEnergy.envelope β := by
  have h1 := WilsonGroundTranslation.temporal_mean_bound n β hβ x i
  have h2 := WilsonGroundTranslation.temporal_mean_bound n β hβ (spatialStep n x i) j
  have h3 := WilsonGroundTranslation.temporal_mean_bound n β hβ (spatialStep n x j) i
  have h4 := WilsonGroundTranslation.temporal_mean_bound n β hβ x j
  have h := plaquette_dirichlet_local n β hβ.le x i j
  change (∫ z, temporalDefect n x i z ∂WilsonGroundSlabEnergy.law n β hβ.le) ≤ _ at h1
  change (∫ z, temporalDefect n (spatialStep n x i) j z
    ∂WilsonGroundSlabEnergy.law n β hβ.le) ≤ _ at h2
  change (∫ z, temporalDefect n (spatialStep n x j) i z
    ∂WilsonGroundSlabEnergy.law n β hβ.le) ≤ _ at h3
  change (∫ z, temporalDefect n x j z ∂WilsonGroundSlabEnergy.law n β hβ.le) ≤ _ at h4
  linarith

/-- The same quantitative bound applies to the actual vacuum-orthogonal amplitude. -/
theorem centered_plaquette_bound (β : ℝ) (hβ : 0 < β)
    (x : SpatialVertex n) (i j : Fin 3) :
    TransferEnergySurvival.dirichlet (normalized n β)
      (centeredAmplitude n β hβ.le (plaquette n x i j)) ≤
      192 * WilsonGroundSlabEnergy.envelope β := by
  rw [centered_dirichlet]
  exact plaquette_dirichlet_bound n β hβ x i j

/-- The denominator needed for spectral survival is the actual ground variance.
The theorem supplies no positive lower bound or physical scaling for it. -/
theorem plaquette_rayleigh_bound (β : ℝ) (hβ : 0 < β)
    (x : SpatialVertex n) (i j : Fin 3)
    (hvar : 0 < groundVariance n β hβ.le (plaquette n x i j)) :
    TransferEnergySurvival.dirichlet (normalized n β)
        (centeredAmplitude n β hβ.le (plaquette n x i j)) /
      ‖centeredAmplitude n β hβ.le (plaquette n x i j)‖^2 ≤
    (192 * WilsonGroundSlabEnergy.envelope β) /
      groundVariance n β hβ.le (plaquette n x i j) := by
  rw [centered_norm]
  exact div_le_div_of_nonneg_right (centered_plaquette_bound n β hβ x i j) hvar.le

omit [NeZero n] in
/-- Absolute physical Dirichlet defects vanish at weak coupling even when
spatial periods, plaquettes and directions vary. No relative O(a) estimate follows. -/
theorem centered_plaquette_tendsto {ι : Type*} {l : Filter ι}
    (N : ι → ℕ) [∀ k, NeZero (N k)] (β : ι → ℝ≥0)
    (x : ∀ k, SpatialVertex (N k)) (i j : ι → Fin 3)
    (hβ : Filter.Tendsto (fun k => (β k : ℝ)) l Filter.atTop) :
    Filter.Tendsto (fun k =>
      TransferEnergySurvival.dirichlet (normalized (N k) (β k))
        (centeredAmplitude (N k) (β k) (β k).coe_nonneg
          (plaquette (N k) (x k) (i k) (j k)))) l (nhds 0) := by
  have ht := (WilsonGroundSlabEnergy.envelope_tendsto.comp hβ).const_mul (192 : ℝ)
  simp only [mul_zero] at ht
  apply squeeze_zero' _ _ ht
  · exact Filter.Eventually.of_forall (fun k => by
      rw [centered_dirichlet]
      exact dirichlet_nonneg (N k) (β k) (β k).coe_nonneg _)
  · filter_upwards [hβ.eventually (Filter.eventually_gt_atTop (0 : ℝ))] with k hk
    exact centered_plaquette_bound (N k) (β k) hk (x k) (i k) (j k)


/-- Scalar renormalization multiplies the actual physical defect quadratically. -/
theorem dirichlet_rescale (β : ℝ) (hβ : 0 ≤ β) (F : C(Slice n, ℝ)) (c : ℝ) :
    TransferEnergySurvival.dirichlet (normalized n β)
      (embed (measure n) ((c • F) * ground n β hβ)) =
    c^2 * TransferEnergySurvival.dirichlet (normalized n β)
      (embed (measure n) (F * ground n β hβ)) := by
  rw [dirichlet_slab, dirichlet_slab]
  simp only [ContinuousMap.smul_apply, smul_eq_mul]
  simp_rw [show ∀ a b : ℝ, (c * a - c * b)^2 = c^2 * (a - b)^2 by
    intros; ring]
  rw [integral_const_mul]
  ring

theorem norm_rescale (β : ℝ) (hβ : 0 ≤ β) (F : C(Slice n, ℝ)) (c : ℝ) :
    ‖embed (measure n) ((c • F) * ground n β hβ)‖^2 =
      c^2 * ‖embed (measure n) (F * ground n β hβ)‖^2 := by
  rw [ground_norm, ground_norm]
  unfold GroundStateDirichlet.normSquared
  simp only [ContinuousMap.smul_apply, smul_eq_mul]
  simp_rw [show ∀ a b : ℝ, a^2 * (c * b)^2 = c^2 * (a^2 * b^2) by
    intros; ring]
  rw [integral_const_mul]

/-- A nonzero scalar renormalization cannot improve the relative physical
Dirichlet defect. This also applies with F equal to the actual centered observable. -/
theorem rayleigh_rescale (β : ℝ) (hβ : 0 ≤ β) (F : C(Slice n, ℝ))
    (c : ℝ) (hc : c ≠ 0) :
    TransferEnergySurvival.dirichlet (normalized n β)
        (embed (measure n) ((c • F) * ground n β hβ)) /
      ‖embed (measure n) ((c • F) * ground n β hβ)‖^2 =
    TransferEnergySurvival.dirichlet (normalized n β)
        (embed (measure n) (F * ground n β hβ)) /
      ‖embed (measure n) (F * ground n β hβ)‖^2 := by
  rw [dirichlet_rescale, norm_rescale]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hc)

end
end UnifiedTheory.Clay.YangMills.WilsonPlaquetteTransport
