/- Rotations inside actual ground-law block coordinates. The normalization
and signed ground-log correction are proved separately for every exterior. -/
import UnifiedTheory.Clay.YangMills.WilsonJointResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonBlockRotation
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonGroundHeatBath CompactDensityEntropy
open scoped Quaternion

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _
local instance inside_left (S : Finset (SpatialVertex n × Fin 3)) :
    (insideHaar n S).IsMulLeftInvariant := by
  unfold insideHaar WilsonBlockMarginal.insideMeasure
  infer_instance

def extend (S : Finset (SpatialVertex n × Fin 3)) (q : Inside n S) : Slice n :=
  WilsonBlockMarginal.assemble S (1,q)

omit [NeZero n] in
theorem extend_continuous (S : Finset (SpatialVertex n × Fin 3)) :
    Continuous (extend n S) :=
  (WilsonBlockMarginal.assemble_continuous S).comp (continuous_const.prodMk continuous_id)

omit [NeZero n] in
theorem extend_assemble (S : Finset (SpatialVertex n × Fin 3))
    (q a : Inside n S) (r : Outside n S) :
    extend n S q * WilsonBlockMarginal.assemble S (r,a) =
      WilsonBlockMarginal.assemble S (r,q*a) := by
  funext e
  by_cases he : e ∈ S
  · simp only [extend, Pi.mul_apply, WilsonBlockMarginal.assemble_inside S _ e he]
  · simp only [extend, Pi.mul_apply, WilsonBlockMarginal.assemble_outside S _ e he,
      Pi.one_apply, one_mul]

omit [NeZero n] in
theorem extend_inv (S : Finset (SpatialVertex n × Fin 3)) (q : Inside n S) :
    (extend n S q)⁻¹ = extend n S q⁻¹ := by
  funext e
  by_cases he : e ∈ S
  · simp only [extend, Pi.inv_apply, WilsonBlockMarginal.assemble_inside S _ e he]
  · simp only [extend, Pi.inv_apply, WilsonBlockMarginal.assemble_outside S _ e he,
      Pi.one_apply, inv_one]

def cost (S : Finset (SpatialVertex n × Fin 3)) (q : Inside n S) : ℝ :=
  ∑ e, ‖(q e : ℍ)-1‖^2

omit [NeZero n] in
theorem cost_nonneg (S : Finset (SpatialVertex n × Fin 3)) (q : Inside n S) :
    0 ≤ cost n S q := Finset.sum_nonneg (fun _e _ => sq_nonneg _)

omit [NeZero n] in
theorem cost_continuous (S : Finset (SpatialVertex n × Fin 3)) : Continuous (cost n S) := by
  unfold cost
  fun_prop

theorem extend_cost (S : Finset (SpatialVertex n × Fin 3)) (q : Inside n S) :
    WilsonJointRotation.cost n (extend n S q) = cost n S q := by
  let F := fun e : SpatialVertex n × Fin 3 => ‖(extend n S q e : ℍ)-1‖^2
  have hz (e : SpatialVertex n × Fin 3) (he : e ∉ S) : F e = 0 := by
    simp only [F, extend, WilsonBlockMarginal.assemble_outside S _ e he,
      Pi.one_apply, OneMemClass.coe_one, sub_self, norm_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  have hs : (∑ e ∈ S, F e) = ∑ e, F e :=
    Finset.sum_subset (Finset.subset_univ S) (fun e _ he => hz e he)
  change (∑ e, F e) = cost n S q
  rw [← hs, Finset.sum_subtype S (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro e _
  simp only [F, extend, WilsonBlockMarginal.assemble_inside S _ e.1 e.2]

theorem density_continuous (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (r : Outside n S) :
    Continuous (conditionalDensity n β hβ S r) :=
  ((weight_continuous n β hβ S).comp
    (continuous_const.prodMk continuous_id)).div_const _

theorem rotated_density_mass (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (r : Outside n S) (q : Inside n S) :
    (∫ a, conditionalDensity n β hβ S r (q*a) ∂insideHaar n S) = 1 :=
  (integral_mul_left_eq_self (conditionalDensity n β hβ S r) q).trans
    (conditionalDensity_mass n β hβ S r)

def logGain (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (r : Outside n S) (q a : Inside n S) : ℝ :=
  Real.log (ground n β hβ (WilsonBlockMarginal.assemble S (r,q*a))) -
    Real.log (ground n β hβ (WilsonBlockMarginal.assemble S (r,a)))

theorem logGain_continuous (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (r : Outside n S) (q : Inside n S) :
    Continuous (logGain n β hβ S r q) := by
  have hg : Continuous (fun a : Inside n S =>
      Real.log (ground n β hβ (WilsonBlockMarginal.assemble S (r,a)))) :=
    ((ground n β hβ).continuous.log (fun u => (ground_pos n β hβ u).ne')).comp
      ((WilsonBlockMarginal.assemble_continuous S).comp (continuous_const.prodMk continuous_id))
  exact (hg.comp (continuous_const.mul continuous_id)).sub hg

def gain (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (r : Outside n S) (q : Inside n S) : ℝ :=
  ∫ a, logGain n β hβ S r q a ∂conditionalLaw n β hβ S r

/-- The actual conditional normalizer cancels in this logarithmic density ratio. -/
theorem entropy_eq_gain (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (r : Outside n S) (q : Inside n S) :
    entropy (insideHaar n S) (conditionalDensity n β hβ S r)
      (fun a => conditionalDensity n β hβ S r (q*a)) = -2*gain n β hβ S r q := by
  unfold gain entropy
  rw [conditionalLaw_integral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with a
  have he : Real.log (conditionalDensity n β hβ S r a /
      conditionalDensity n β hβ S r (q*a)) = -2*logGain n β hβ S r q a := by
    unfold conditionalDensity weight
    rw [div_div_div_cancel_right₀ (fiberMass_positive n β hβ S r).ne',
      Real.log_div (sq_pos_of_pos (ground_pos n β hβ _)).ne'
        (sq_pos_of_pos (ground_pos n β hβ _)).ne', Real.log_pow, Real.log_pow]
    unfold logGain
    norm_num
    ring
  rw [he]
  ring

/-- Conditional sign, for each true exterior rather than only after averaging exteriors. -/
theorem gain_nonpos (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (r : Outside n S) (q : Inside n S) :
    gain n β hβ S r q ≤ 0 := by
  have h := entropy_nonneg (insideHaar n S) (conditionalDensity n β hβ S r)
    (fun a => conditionalDensity n β hβ S r (q*a)) (density_continuous n β hβ S r)
    ((density_continuous n β hβ S r).comp (continuous_const.mul continuous_id))
    (conditionalDensity_positive n β hβ S r)
    (fun a => conditionalDensity_positive n β hβ S r (q*a))
    (conditionalDensity_mass n β hβ S r) (rotated_density_mass n β hβ S r q)
  rw [entropy_eq_gain] at h
  linarith

end
end UnifiedTheory.Clay.YangMills.WilsonBlockRotation
