/- The normalized Euclidean surface law on the quaternion unit sphere is
constructed and identified with the repository's actual compact Haar measure.
The proof uses linear-isometry invariance of cone volume and Haar uniqueness.
The first-coordinate law is reduced to an explicit four-dimensional cone volume;
its one-dimensional semicircle density still requires a separate slicing proof.
No Wilson conditional-action identity or continuum theorem is assumed here. -/
import UnifiedTheory.Clay.YangMills.SU2QuaternionEquivalence
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2HaarSphere
noncomputable section
open MeasureTheory SU2QuaternionEquivalence RegulatedGauge
open scoped Pointwise ENNReal

instance quaternionMeasurableSpace : MeasurableSpace (Quaternion ℝ) := borel (Quaternion ℝ)
instance quaternionBorelSpace : BorelSpace (Quaternion ℝ) := ⟨rfl⟩

abbrev QuaternionSphere := Metric.sphere (0 : Quaternion ℝ) 1

theorem mem_unitary_iff_norm_one (q : Quaternion ℝ) : q ∈ unitary (Quaternion ℝ) ↔ ‖q‖ = 1 := by
  constructor
  · exact CStarRing.norm_of_mem_unitary
  · intro h
    have hn : Quaternion.normSq q = 1 := by
      rw [Quaternion.normSq_eq_norm_mul_self, h, one_mul]
    constructor
    · rw [Quaternion.star_mul_self, hn]
      rfl
    · rw [Quaternion.self_mul_star, hn]
      rfl

/-- Unit quaternions are exactly the Euclidean unit sphere. -/
def sphereEquivalence : UnitQuaternion ≃ₜ QuaternionSphere :=
  (Homeomorph.refl (Quaternion ℝ)).subtype (fun q => by
    simpa only [Metric.mem_sphere, dist_zero_right] using mem_unitary_iff_norm_one q)

/-- Restrict a real linear isometry to the unit sphere. -/
def sphereRotation (e : Quaternion ℝ ≃ₗᵢ[ℝ] Quaternion ℝ) :
    QuaternionSphere ≃ₜ QuaternionSphere :=
  e.toHomeomorph.subtype (fun q => by
    simp only [Metric.mem_sphere, dist_zero_right]
    change ‖q‖ = 1 ↔ ‖e q‖ = 1
    rw [e.norm_map])

def leftIsometry (g : UnitQuaternion) : Quaternion ℝ ≃ₗᵢ[ℝ] Quaternion ℝ where
  toFun q := (g : Quaternion ℝ) * q
  invFun q := (g⁻¹ : UnitQuaternion) * q
  left_inv q := by
    change ((g⁻¹ : UnitQuaternion) : Quaternion ℝ) * ((g : Quaternion ℝ) * q) = q
    rw [← mul_assoc, ← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one, one_mul]
  right_inv q := by
    change (g : Quaternion ℝ) * (((g⁻¹ : UnitQuaternion) : Quaternion ℝ) * q) = q
    rw [← mul_assoc, ← Submonoid.coe_mul, mul_inv_cancel, Submonoid.coe_one, one_mul]
  map_add' _ _ := mul_add _ _ _
  map_smul' _ _ := mul_smul_comm _ _ _
  norm_map' q := by
    change ‖(g : Quaternion ℝ) * q‖ = ‖q‖
    rw [norm_mul, CStarRing.norm_of_mem_unitary g.property, one_mul]

/-- The cone used by `toSphere` commutes with an actual linear isometry. -/
theorem cone_preimage (e : Quaternion ℝ ≃ₗᵢ[ℝ] Quaternion ℝ)
    (s : Set QuaternionSphere) :
    Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereRotation e ⁻¹' s)) =
      e ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, _, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨r, hr, e q, ⟨sphereRotation e q, hq, rfl⟩, (e.map_smul r q).symm⟩
  · rintro ⟨r, hr, _, ⟨q, hq, rfl⟩, hx⟩
    refine ⟨r, hr, e.symm q, ⟨(sphereRotation e).symm q, ?_, rfl⟩, ?_⟩
    · simpa using hq
    · apply e.injective
      simpa only [map_smul, e.apply_symm_apply] using hx

/-- Surface measure induced from Euclidean volume is invariant under rotations. -/
theorem sphereRotation_preserving (e : Quaternion ℝ ≃ₗᵢ[ℝ] Quaternion ℝ) :
    MeasurePreserving (sphereRotation e) (volume : Measure (Quaternion ℝ)).toSphere
      (volume : Measure (Quaternion ℝ)).toSphere := by
  refine ⟨(sphereRotation e).measurable, Measure.ext (fun s hs => ?_)⟩
  rw [Measure.map_apply (sphereRotation e).measurable hs,
    Measure.toSphere_apply' _ ((sphereRotation e).measurable hs),
    Measure.toSphere_apply' _ hs, cone_preimage]
  congr 1
  exact e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding _

/-- Surface measure normalized by its actual finite nonzero total mass. -/
def normalizedSphere : Measure QuaternionSphere :=
  ((volume : Measure (Quaternion ℝ)).toSphere Set.univ)⁻¹ •
    (volume : Measure (Quaternion ℝ)).toSphere

instance normalizedSphere_probability : IsProbabilityMeasure normalizedSphere where
  measure_univ := by
    rw [normalizedSphere, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel
      (by simpa only [ne_eq, Measure.measure_univ_eq_zero] using
        (Measure.toSphere_ne_zero (volume : Measure (Quaternion ℝ))))
      (measure_ne_top _ _)

theorem normalizedSphere_rotation (e : Quaternion ℝ ≃ₗᵢ[ℝ] Quaternion ℝ) :
    MeasurePreserving (sphereRotation e) normalizedSphere normalizedSphere :=
  (sphereRotation_preserving e).smul_measure _

/-- The constructed sphere law viewed as a measure on the actual quaternion group. -/
def sphereGroupMeasure : Measure UnitQuaternion :=
  normalizedSphere.map sphereEquivalence.symm

instance sphereGroupMeasure_probability : IsProbabilityMeasure sphereGroupMeasure :=
  Measure.isProbabilityMeasure_map sphereEquivalence.symm.measurable.aemeasurable

instance sphereGroupMeasure_left : sphereGroupMeasure.IsMulLeftInvariant where
  map_mul_left_eq_self g := by
    unfold sphereGroupMeasure
    have he := (normalizedSphere_rotation (leftIsometry g)).map_eq
    rw [Measure.map_map (measurable_const_mul g) sphereEquivalence.symm.measurable]
    rw [← he, Measure.map_map sphereEquivalence.symm.measurable
      (sphereRotation (leftIsometry g)).measurable]
    congr 1

/-- Haar uniqueness identifies the normalized surface law without a density assumption. -/
theorem sphereGroupMeasure_eq_compactHaar :
    sphereGroupMeasure = compactHaar UnitQuaternion := by
  exact ((Measure.haarMeasure_eq_iff (⊤ : TopologicalSpace.PositiveCompacts UnitQuaternion)
    sphereGroupMeasure).2 (by simp)).symm

/-- The explicit quaternion-to-sphere map transports actual normalized Haar measure. -/
theorem sphereEquivalence_preserving :
    MeasurePreserving sphereEquivalence (compactHaar UnitQuaternion) normalizedSphere := by
  have h : MeasurePreserving sphereEquivalence.symm.toMeasurableEquiv normalizedSphere
      (compactHaar UnitQuaternion) := by
    refine ⟨sphereEquivalence.symm.measurable, ?_⟩
    exact sphereGroupMeasure_eq_compactHaar
  exact h.symm

/-- All Haar integrals are genuine normalized sphere integrals. -/
theorem compactHaar_integral_sphere (f : QuaternionSphere → ℝ) :
    (∫ q, f (sphereEquivalence q) ∂compactHaar UnitQuaternion) =
      ∫ q, f q ∂normalizedSphere :=
  sphereEquivalence_preserving.integral_comp sphereEquivalence.measurableEmbedding f


/-- Every real orthogonal transformation acts on unit quaternions. -/
def quaternionRotation (e : Quaternion ℝ ≃ₗᵢ[ℝ] Quaternion ℝ) :
    UnitQuaternion ≃ₜ UnitQuaternion :=
  sphereEquivalence.trans ((sphereRotation e).trans sphereEquivalence.symm)

theorem quaternionRotation_coe (e : Quaternion ℝ ≃ₗᵢ[ℝ] Quaternion ℝ)
    (q : UnitQuaternion) : (quaternionRotation e q : Quaternion ℝ) = e q := rfl

/-- Actual quaternion Haar measure is invariant under the full orthogonal group. -/
theorem quaternionRotation_preserving (e : Quaternion ℝ ≃ₗᵢ[ℝ] Quaternion ℝ) :
    MeasurePreserving (quaternionRotation e) (compactHaar UnitQuaternion)
      (compactHaar UnitQuaternion) := by
  have hi : MeasurePreserving sphereEquivalence.toMeasurableEquiv
      (compactHaar UnitQuaternion) normalizedSphere := sphereEquivalence_preserving
  exact hi.symm.comp ((normalizedSphere_rotation e).comp sphereEquivalence_preserving)

theorem compactHaar_integral_rotation (e : Quaternion ℝ ≃ₗᵢ[ℝ] Quaternion ℝ)
    (f : UnitQuaternion → ℝ) :
    (∫ q, f (quaternionRotation e q) ∂compactHaar UnitQuaternion) =
      ∫ q, f q ∂compactHaar UnitQuaternion :=
  (quaternionRotation_preserving e).integral_comp (quaternionRotation e).measurableEmbedding f


/-- Normalized sphere mass is the volume fraction of the corresponding open cone. -/
theorem normalizedSphere_apply (s : Set QuaternionSphere) (hs : MeasurableSet s) :
    normalizedSphere s =
      volume (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) /
        volume (Metric.ball (0 : Quaternion ℝ) 1) := by
  rw [normalizedSphere, Measure.smul_apply, smul_eq_mul,
    Measure.toSphere_apply' _ hs, Measure.toSphere_apply_univ, Quaternion.finrank_eq_four]
  rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by simp))]
  calc
    (4 : ℝ≥0∞)⁻¹ * (volume (Metric.ball (0 : Quaternion ℝ) 1))⁻¹ *
        (4 * volume (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s))) =
      ((4 : ℝ≥0∞)⁻¹ * 4) *
        (volume (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) *
          (volume (Metric.ball (0 : Quaternion ℝ) 1))⁻¹) := by ac_rfl
    _ = _ := by
      rw [ENNReal.inv_mul_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by simp)]
      simp only [one_mul, div_eq_mul_inv]

/-- A first-coordinate spherical slice is an explicit Euclidean solid cone. -/
theorem coordinate_cone (s : Set ℝ) :
    Set.Ioo (0 : ℝ) 1 •
        (Subtype.val '' {q : QuaternionSphere | (q : Quaternion ℝ).re ∈ s}) =
      {x : Quaternion ℝ | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ x.re / ‖x‖ ∈ s} := by
  ext x
  constructor
  · rintro ⟨r, hr, _, ⟨q, hq, rfl⟩, rfl⟩
    have hn : ‖(q : Quaternion ℝ)‖ = 1 := by simp
    simp only [Set.mem_setOf_eq, norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hn, mul_one]
    refine ⟨hr.1, hr.2, ?_⟩
    simpa only [Quaternion.re_smul, smul_eq_mul, mul_div_cancel_left₀ _ hr.1.ne'] using hq
  · rintro ⟨hpos, hlt, hs⟩
    let q : QuaternionSphere := ⟨‖x‖⁻¹ • x, by
      simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']⟩
    refine ⟨‖x‖, ⟨hpos, hlt⟩, (q : Quaternion ℝ), ⟨q, ?_, rfl⟩, ?_⟩
    · change (‖x‖⁻¹ • x).re ∈ s
      simpa only [Quaternion.re_smul, smul_eq_mul, div_eq_mul_inv, mul_comm] using hs
    · simp only [q, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

/-- Exact actual Haar marginal, reduced to a concrete four-dimensional cone-volume formula. -/
theorem compactHaar_coordinate_cone (s : Set ℝ) (hs : MeasurableSet s) :
    compactHaar UnitQuaternion {q | (q : Quaternion ℝ).re ∈ s} =
      volume {x : Quaternion ℝ | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ x.re / ‖x‖ ∈ s} /
        volume (Metric.ball (0 : Quaternion ℝ) 1) := by
  have hslice : MeasurableSet {q : QuaternionSphere | (q : Quaternion ℝ).re ∈ s} :=
    (Quaternion.continuous_re.comp continuous_subtype_val).measurable hs
  have h := sphereEquivalence_preserving.measure_preimage hslice.nullMeasurableSet
  change compactHaar UnitQuaternion {q | (q : Quaternion ℝ).re ∈ s} =
    normalizedSphere {q : QuaternionSphere | (q : Quaternion ℝ).re ∈ s} at h
  rw [h, normalizedSphere_apply _ hslice, coordinate_cone]


/-- The ambient four-dimensional unit ball has its exact Euclidean volume. -/
theorem quaternion_unitBall_volume :
    volume (Metric.ball (0 : Quaternion ℝ) 1) = ENNReal.ofReal (Real.pi ^ 2 / 2) := by
  simpa using InnerProductSpace.volume_ball_of_dim_even (k := 2)
    (by norm_num [Quaternion.finrank_eq_four] : Module.finrank ℝ (Quaternion ℝ) = 2 * 2)
    (0 : Quaternion ℝ) 1

/-- The surface measure used above has total mass `2 π²`, derived from volume. -/
theorem quaternion_sphere_area :
    (volume : Measure (Quaternion ℝ)).toSphere Set.univ =
      ENNReal.ofReal (2 * Real.pi ^ 2) := by
  rw [Measure.toSphere_apply_univ, Quaternion.finrank_eq_four, quaternion_unitBall_volume]
  norm_num only [Nat.cast_ofNat]
  rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

/-- The Haar integral is a surface integral with its explicitly computed normalization. -/
theorem compactHaar_integral_surface (f : QuaternionSphere → ℝ) :
    (∫ q, f (sphereEquivalence q) ∂compactHaar UnitQuaternion) =
      (2 * Real.pi ^ 2)⁻¹ * ∫ q, f q ∂(volume : Measure (Quaternion ℝ)).toSphere := by
  rw [compactHaar_integral_sphere, normalizedSphere, integral_smul_measure,
    quaternion_sphere_area, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity)]
  rfl


end
end UnifiedTheory.Clay.YangMills.SU2HaarSphere
