/- Quantitative small-field action curvature for the actual middle Wilson
law. The spatial negative part is proportional to plaquette defects; two
nearby temporal endpoints give a positive second-difference lower bound.
No global variance comparison or control of the excluded region is claimed. -/
import UnifiedTheory.Clay.YangMills.QuaternionDefectCurvature
import UnifiedTheory.Clay.YangMills.WilsonMiddleEntropy

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonSmallFieldCurvature
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonJointRotation QuaternionDefectCurvature
open WilsonSingleLinkStaples (character)
open scoped Quaternion

variable (n : ℕ) [NeZero n]

/-- The local remainder retains the actual defect of each plaquette. -/
theorem potential_second_local (q u : Slice n) :
    -8*(∑ x : SpatialVertex n, ∑ p : SpatialPlane,
      ‖((spatialHolonomy u x p.1.1 p.1.2 : Q) : ℍ) - 1‖ *
        ((displacement n q (x,p.1.1))^2+
          (displacement n q (spatialStep n x p.1.1,p.1.2))^2+
          (displacement n q (spatialStep n x p.1.2,p.1.1))^2+
          (displacement n q (x,p.1.2))^2)) ≤
      potential character 2 (q*u)+potential character 2 (q⁻¹*u)-2*potential character 2 u := by
  have h (x : SpatialVertex n) (p : SpatialPlane) :
      (-8)* (‖((spatialHolonomy u x p.1.1 p.1.2 : Q) : ℍ) - 1‖ *
        ((displacement n q (x,p.1.1))^2+
          (displacement n q (spatialStep n x p.1.1,p.1.2))^2+
          (displacement n q (spatialStep n x p.1.2,p.1.1))^2+
          (displacement n q (x,p.1.2))^2)) ≤
        (2-(character (spatialHolonomy (q*u) x p.1.1 p.1.2)).re)+
          (2-(character (spatialHolonomy (q⁻¹*u) x p.1.1 p.1.2)).re)-
          2*(2-(character (spatialHolonomy u x p.1.1 p.1.2)).re) := by
    have hh := defect_second_lower _ _ _ _ _ _
      (holonomy_variation n q u x p.1.1 p.1.2) le_rfl
    have hs := square_four_bound (displacement n q (x,p.1.1))
      (displacement n q (spatialStep n x p.1.1,p.1.2))
      (displacement n q (spatialStep n x p.1.2,p.1.1)) (displacement n q (x,p.1.2))
    have hm := mul_le_mul_of_nonneg_left hs
      (show 0 ≤ 2*‖((spatialHolonomy u x p.1.1 p.1.2 : Q) : ℍ) - 1‖ by positivity)
    simp only [one_pow, mul_one] at hh
    nlinarith
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) =>
    Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) => h x p))
  simpa only [potential, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum] using hs

/-- Fourfold spatial incidence turns the defect-sensitive local estimate
into a bound with no factor for the number of links. -/
theorem potential_second_lower (q u : Slice n) (δ : ℝ) (hδ : 0 ≤ δ)
    (hflat : ∀ (x : SpatialVertex n) (p : SpatialPlane),
      ‖((spatialHolonomy u x p.1.1 p.1.2 : Q) : ℍ) - 1‖ ≤ δ) :
    -32*δ*cost n q ≤ potential character 2 (q*u)+potential character 2 (q⁻¹*u)-
      2*potential character 2 u := by
  let D := fun (x : SpatialVertex n) (p : SpatialPlane) =>
    (displacement n q (x,p.1.1))^2+
      (displacement n q (spatialStep n x p.1.1,p.1.2))^2+
      (displacement n q (spatialStep n x p.1.2,p.1.1))^2+
      (displacement n q (x,p.1.2))^2
  have h (x : SpatialVertex n) (p : SpatialPlane) :
      (-8*δ)*D x p ≤
        (2-(character (spatialHolonomy (q*u) x p.1.1 p.1.2)).re)+
        (2-(character (spatialHolonomy (q⁻¹*u) x p.1.1 p.1.2)).re)-
        2*(2-(character (spatialHolonomy u x p.1.1 p.1.2)).re) := by
    have hh := defect_second_lower _ _ _ _ _ δ
      (holonomy_variation n q u x p.1.1 p.1.2) (hflat x p)
    have hs := square_four_bound (displacement n q (x,p.1.1))
      (displacement n q (spatialStep n x p.1.1,p.1.2))
      (displacement n q (spatialStep n x p.1.2,p.1.1)) (displacement n q (x,p.1.2))
    have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2*δ by positivity)
    simp only [one_pow, mul_one] at hh
    dsimp only [D]
    nlinarith
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) =>
    Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) => h x p))
  have hi : (∑ x, ∑ p, D x p) = 4*cost n q := incidence_sum n q
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  rw [hi] at hs
  simp only [potential, Finset.sum_sub_distrib]
  nlinarith

/-- The temporal second difference has an exact local coefficient. -/
theorem kinetic_second_eq (q u v : Slice n) :
    kineticAction character 2 (q*u) v+kineticAction character 2 (q⁻¹*u) v-
      2*kineticAction character 2 u v =
        ∑ e, (displacement n q e)^2*(2-‖(u e : ℍ) - (v e : ℍ)‖ ^ 2) := by
  have he (e : SpatialVertex n × Fin 3) := kinetic_second_exact (q e) (u e) (v e)
  have h := Finset.sum_congr (s₁ := Finset.univ) rfl (fun e _ => he e)
  simpa only [kineticAction, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Pi.mul_apply, Pi.inv_apply, displacement] using h

theorem kinetic_second_lower (q u v : Slice n) (η : ℝ)
    (hclose : ∀ e, ‖(u e : ℍ) - (v e : ℍ)‖ ^ 2 ≤ η) :
    (2-η)*cost n q ≤ kineticAction character 2 (q*u) v+
      kineticAction character 2 (q⁻¹*u) v-2*kineticAction character 2 u v := by
  rw [kinetic_second_eq, cost, Finset.mul_sum]
  exact Finset.sum_le_sum (fun e _ => by
    have h := mul_le_mul_of_nonneg_left (hclose e) (sq_nonneg (displacement n q e))
    nlinarith)

/-- This is the actual source-weighted middle bridge action, whose ground
amplitude was cancelled in the previously proved disintegration. -/
theorem middle_second_lower (β : ℝ) (hβ : 0 ≤ β) (q v w u : Slice n)
    (δ ηv ηw : ℝ) (hδ : 0 ≤ δ)
    (hflat : ∀ (x : SpatialVertex n) (p : SpatialPlane),
      ‖((spatialHolonomy u x p.1.1 p.1.2 : Q) : ℍ) - 1‖ ≤ δ)
    (hv : ∀ e, ‖(u e : ℍ) - (v e : ℍ)‖ ^ 2 ≤ ηv)
    (hw : ∀ e, ‖(u e : ℍ) - (w e : ℍ)‖ ^ 2 ≤ ηw) :
    β*(4-ηv-ηw-32*δ)*cost n q ≤
      WilsonMiddleBridge.action n β v w (q*u)+WilsonMiddleBridge.action n β v w (q⁻¹*u)-
        2*WilsonMiddleBridge.action n β v w u := by
  have hp := mul_le_mul_of_nonneg_left (potential_second_lower n q u δ hδ hflat) hβ
  have h1 := mul_le_mul_of_nonneg_left (kinetic_second_lower n q u v ηv hv) hβ
  have h2 := mul_le_mul_of_nonneg_left (kinetic_second_lower n q u w ηw hw) hβ
  unfold WilsonMiddleBridge.action
  nlinarith

/-- An explicit positive bound in the stated small-field sector. The
comparison holds for arbitrary simultaneous rotations q. -/
theorem middle_second_small (β : ℝ) (hβ : 0 ≤ β) (q v w u : Slice n)
    (hflat : ∀ (x : SpatialVertex n) (p : SpatialPlane),
      ‖((spatialHolonomy u x p.1.1 p.1.2 : Q) : ℍ) - 1‖ ≤ 1 / 32)
    (hv : ∀ e, ‖(u e : ℍ) - (v e : ℍ)‖ ^ 2 ≤ 1 / 2)
    (hw : ∀ e, ‖(u e : ℍ) - (w e : ℍ)‖ ^ 2 ≤ 1 / 2) :
    2*β*cost n q ≤
      WilsonMiddleBridge.action n β v w (q*u)+WilsonMiddleBridge.action n β v w (q⁻¹*u)-
        2*WilsonMiddleBridge.action n β v w u := by
  have h := middle_second_lower n β hβ q v w u (1 / 32) (1 / 2) (1 / 2)
    (by norm_num) hflat hv hw
  convert h using 1
  ring

/-- The true conditional normalizer cancels from this log-density estimate.
It is pointwise small-field curvature, not global variance coercivity. -/
theorem middle_log_density_small (β : ℝ) (hβ : 0 ≤ β) (q v w u : Slice n)
    (hflat : ∀ (x : SpatialVertex n) (p : SpatialPlane),
      ‖((spatialHolonomy u x p.1.1 p.1.2 : Q) : ℍ) - 1‖ ≤ 1 / 32)
    (hv : ∀ e, ‖(u e : ℍ) - (v e : ℍ)‖ ^ 2 ≤ 1 / 2)
    (hw : ∀ e, ‖(u e : ℍ) - (w e : ℍ)‖ ^ 2 ≤ 1 / 2) :
    Real.log (WilsonMiddleEntropy.density n β v w (q*u))+
      Real.log (WilsonMiddleEntropy.density n β v w (q⁻¹*u))-
      2*Real.log (WilsonMiddleEntropy.density n β v w u) ≤ -2*β*cost n q := by
  have h := middle_second_small n β hβ q v w u hflat hv hw
  simp only [WilsonMiddleEntropy.log_density]
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonSmallFieldCurvature
