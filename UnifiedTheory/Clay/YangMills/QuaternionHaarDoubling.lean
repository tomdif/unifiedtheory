/- Actual quaternion Haar image bounds for the inverse midpoint map.
The factor 81 comes from a three-Lipschitz homogeneous map in four ambient
dimensions, so no unproved surface Jacobian is used. -/
import UnifiedTheory.Clay.YangMills.QuaternionRadialDoubling

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.QuaternionHaarDoubling
noncomputable section
open MeasureTheory WilsonSlabOperator SU2HaarSphere QuaternionRadialDoubling
open QuaternionSymmetricChange
open scoped Quaternion ENNReal Pointwise

abbrev haar : Measure Q := RegulatedGauge.compactHaar Q

def cone (s : Set Q) : Set ℍ := Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)

theorem haar_cone (s : Set Q) (hs : MeasurableSet s) :
    haar s = volume (cone s) / volume (Metric.ball (0 : ℍ) 1) := by
  let t : Set QuaternionSphere := sphereEquivalence.symm ⁻¹' s
  have ht : MeasurableSet t := sphereEquivalence.symm.measurable hs
  have hp := sphereEquivalence_preserving.measure_preimage ht.nullMeasurableSet
  have he : sphereEquivalence ⁻¹' t = s := by ext q; simp [t]
  rw [he, normalizedSphere_apply t ht] at hp
  have hv : (Subtype.val '' t : Set ℍ) = Subtype.val '' s := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨sphereEquivalence.symm q, hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨sphereEquivalence q, by simpa only [t, Set.mem_preimage,
        Homeomorph.symm_apply_apply] using hq, rfl⟩
  rw [hv] at hp
  exact hp

theorem cone_image (F : ℍ → ℍ) (f : Q → Q)
    (hscale : ∀ r : ℝ, 0 ≤ r → ∀ x : ℍ, F (r • x) = r • F x)
    (hunit : ∀ q : Q, F (q : ℍ) = (f q : ℍ)) (s : Set Q) :
    cone (f '' s) = F '' cone s := by
  ext x
  constructor
  · rintro ⟨r, hr, _, ⟨_, ⟨q, hq, rfl⟩, rfl⟩, rfl⟩
    refine ⟨r • (q : ℍ), ⟨r, hr, q, ⟨q, hq, rfl⟩, rfl⟩, ?_⟩
    rw [hscale r hr.1.le, hunit]
  · rintro ⟨_, ⟨r, hr, _, ⟨q, hq, rfl⟩, rfl⟩, rfl⟩
    rw [hscale r hr.1.le, hunit]
    exact ⟨r, hr, f q, ⟨f q, ⟨q, hq, rfl⟩, rfl⟩, rfl⟩

theorem haar_image_bound (F : ℍ → ℍ) (f : Q → Q) (hF : LipschitzWith 3 F)
    (hscale : ∀ r : ℝ, 0 ≤ r → ∀ x : ℍ, F (r • x) = r • F x)
    (hunit : ∀ q : Q, F (q : ℍ) = (f q : ℍ))
    (s : Set Q) (hs : MeasurableSet s) (hfs : MeasurableSet (f '' s)) :
    haar (f '' s) ≤ 81 * haar s := by
  rw [haar_cone _ hfs, haar_cone _ hs, cone_image F f hscale hunit]
  have hh := volume_image_bound F hF (cone s)
  simp only [div_eq_mul_inv]
  calc
    _ ≤ _ := mul_le_mul_left hh _
    _ = _ := by ac_rfl

def fold (z q : Q) : Q := q * z⁻¹ * q

def radialFold (z : Q) (x : ℍ) : ℍ :=
  radialDouble (x * ((z⁻¹ : Q) : ℍ)) * (z : ℍ)

theorem right_lipschitz (z : Q) : LipschitzWith 1 (fun x : ℍ => x * (z : ℍ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, ← sub_mul, norm_mul, unit_norm, mul_one, NNReal.coe_one, one_mul]
  exact le_rfl

theorem radialFold_lipschitz (z : Q) : LipschitzWith 3 (radialFold z) := by
  have hh := (right_lipschitz z).comp (radialDouble_lipschitz.comp (right_lipschitz z⁻¹))
  simpa only [one_mul, mul_one] using hh

theorem radialFold_smul (z : Q) (r : ℝ) (hr : 0 ≤ r) (x : ℍ) :
    radialFold z (r • x) = r • radialFold z x := by
  simp only [radialFold, smul_mul_assoc, radialDouble_smul r hr]

theorem radialFold_unit (z q : Q) : radialFold z (q : ℍ) = (fold z q : ℍ) := by
  have hh := radialDouble_unit (q * z⁻¹)
  change radialDouble ((q : ℍ) * ((z⁻¹ : Q) : ℍ)) = _ at hh
  rw [radialFold, hh]
  change (((q * z⁻¹) * (q * z⁻¹) * z : Q) : ℍ) = _
  congr 1
  dsimp [fold]
  group

theorem fold_continuous (z : Q) : Continuous (fold z) :=
  (continuous_id.mul continuous_const).mul continuous_id

/-- This is the actual Haar estimate, retaining both measurable sets. -/
theorem fold_image_bound (z : Q) (s : Set Q) (hs : MeasurableSet s)
    (hfs : MeasurableSet (fold z '' s)) : haar (fold z '' s) ≤ 81 * haar s :=
  haar_image_bound (radialFold z) (fold z) (radialFold_lipschitz z)
    (radialFold_smul z) (radialFold_unit z) s hs hfs

theorem fold_compact_bound (z : Q) (s : Set Q) (hs : IsCompact s) :
    haar (fold z '' s) ≤ 81 * haar s :=
  fold_image_bound z s hs.measurableSet ((hs.image (fold_continuous z)).measurableSet)

/-- The fold is exactly the inverse of midpoint contraction toward z. -/
theorem fold_midpoint (z q : Q) (h : (z : ℍ) + (q : ℍ) ≠ 0) :
    fold z (QuaternionChordMidpoint.midpoint z q h) = q := by
  have hh := QuaternionChordMidpoint.midpoint_symmetric z q h
  simpa only [fold, mul_inv_rev, inv_inv, mul_assoc] using hh

end
end UnifiedTheory.Clay.YangMills.QuaternionHaarDoubling
