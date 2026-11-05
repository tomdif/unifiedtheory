/- The actual middle-action curvature is positive along retained links even
when arbitrary plaquette defects remain elsewhere. This is pointwise only. -/
import UnifiedTheory.Clay.YangMills.WilsonDefectMask
import UnifiedTheory.Clay.YangMills.WilsonSmallFieldCurvature

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonMaskedCurvature
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonSpatialCutEnergy WilsonJointRotation
open WilsonSmallFieldCurvature WilsonDefectMask
open WilsonSingleLinkStaples (character)
open scoped Quaternion

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

def plaquetteCost (q : Slice n) (p : Plaquette n) : ℝ :=
  (displacement n q (p.1,p.2.1.1))^2+
    (displacement n q (spatialStep n p.1 p.2.1.1,p.2.1.2))^2+
    (displacement n q (spatialStep n p.1 p.2.1.2,p.2.1.1))^2+
    (displacement n q (p.1,p.2.1.2))^2

omit [NeZero n] in
theorem plaquetteCost_nonneg (q : Slice n) (p : Plaquette n) : 0 ≤ plaquetteCost n q p := by
  unfold plaquetteCost
  positivity

omit [NeZero n] in
theorem displacement_zero (q : Slice n) (e : SpatialVertex n × Fin 3) (h : q e = 1) :
    displacement n q e = 0 := by simp [displacement, h]

omit [NeZero n] in
theorem plaquetteCost_zero (q : Slice n) (p : Plaquette n)
    (h : ∀ e ∈ support n p, q e = 1) : plaquetteCost n q p = 0 := by
  have h1 := displacement_zero n q (p.1,p.2.1.1) (h _ (by simp [support]))
  have h2 := displacement_zero n q (spatialStep n p.1 p.2.1.1,p.2.1.2)
    (h _ (by simp [support]))
  have h3 := displacement_zero n q (spatialStep n p.1 p.2.1.2,p.2.1.1)
    (h _ (by simp [support]))
  have h4 := displacement_zero n q (p.1,p.2.1.2) (h _ (by simp [support]))
  simp only [plaquetteCost, h1, h2, h3, h4, zero_pow (by decide : 2 ≠ 0), add_zero]

theorem plaquetteCost_sum (q : Slice n) :
    (∑ p : Plaquette n, plaquetteCost n q p) = 4*cost n q := by
  simpa only [Fintype.sum_prod_type, plaquetteCost] using incidence_sum n q

/-- Only plaquettes touching an active direction need the small-field bound. -/
theorem potential_second_active (A : Finset (SpatialVertex n × Fin 3)) (q u : Slice n)
    (δ : ℝ) (hq : ∀ e, e ∉ A → q e = 1)
    (hflat : ∀ p e, e ∈ A → e ∈ support n p →
      ‖((spatialHolonomy u p.1 p.2.1.1 p.2.1.2 : Q) : ℍ) - 1‖ ≤ δ) :
    -32*δ*cost n q ≤ potential character 2 (q*u)+potential character 2 (q⁻¹*u)-
      2*potential character 2 u := by
  have hd (p : Plaquette n) :
      ‖((spatialHolonomy u p.1 p.2.1.1 p.2.1.2 : Q) : ℍ) - 1‖*plaquetteCost n q p ≤
        δ*plaquetteCost n q p := by
    by_cases h : ∃ e, e ∈ A ∧ e ∈ support n p
    · obtain ⟨e,he,hp⟩ := h
      exact mul_le_mul_of_nonneg_right (hflat p e he hp) (plaquetteCost_nonneg n q p)
    · have hz : plaquetteCost n q p = 0 := plaquetteCost_zero n q p (fun e he =>
        hq e (fun hA => h ⟨e,hA,he⟩))
      rw [hz, mul_zero, mul_zero]
  have hs := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) => hd p)
  rw [← Finset.mul_sum, plaquetteCost_sum] at hs
  have hl := potential_second_local n q u
  have he : -8*(∑ p : Plaquette n,
      ‖((spatialHolonomy u p.1 p.2.1.1 p.2.1.2 : Q) : ℍ) - 1‖*plaquetteCost n q p) ≤
      potential character 2 (q*u)+potential character 2 (q⁻¹*u)-2*potential character 2 u := by
    simpa only [Fintype.sum_prod_type, plaquetteCost] using hl
  nlinarith

theorem kinetic_second_active (A : Finset (SpatialVertex n × Fin 3)) (q u v : Slice n)
    (η : ℝ) (hq : ∀ e, e ∉ A → q e = 1)
    (hv : ∀ e ∈ A, ‖(u e : ℍ) - (v e : ℍ)‖ ^ 2 ≤ η) :
    (2-η)*cost n q ≤ kineticAction character 2 (q*u) v+
      kineticAction character 2 (q⁻¹*u) v-2*kineticAction character 2 u v := by
  rw [kinetic_second_eq, cost, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  by_cases he : e ∈ A
  · have hh := mul_le_mul_of_nonneg_left (hv e he) (sq_nonneg (displacement n q e))
    nlinarith
  · rw [displacement_zero n q e (hq e he)]
    norm_num

theorem middle_second_active (β : ℝ) (hβ : 0 ≤ β)
    (A : Finset (SpatialVertex n × Fin 3)) (q v w u : Slice n) (δ ηv ηw : ℝ)
    (hq : ∀ e, e ∉ A → q e = 1)
    (hflat : ∀ p e, e ∈ A → e ∈ support n p →
      ‖((spatialHolonomy u p.1 p.2.1.1 p.2.1.2 : Q) : ℍ) - 1‖ ≤ δ)
    (hv : ∀ e ∈ A, ‖(u e : ℍ) - (v e : ℍ)‖ ^ 2 ≤ ηv)
    (hw : ∀ e ∈ A, ‖(u e : ℍ) - (w e : ℍ)‖ ^ 2 ≤ ηw) :
    β*(4-ηv-ηw-32*δ)*cost n q ≤
      WilsonMiddleBridge.action n β v w (q*u)+WilsonMiddleBridge.action n β v w (q⁻¹*u)-
        2*WilsonMiddleBridge.action n β v w u := by
  have hp := mul_le_mul_of_nonneg_left (potential_second_active n A q u δ hq hflat) hβ
  have h1 := mul_le_mul_of_nonneg_left (kinetic_second_active n A q u v ηv hq hv) hβ
  have h2 := mul_le_mul_of_nonneg_left (kinetic_second_active n A q u w ηw hq hw) hβ
  unfold WilsonMiddleBridge.action
  nlinarith

/-- The active set is constructed from the actual field and block. -/
theorem good_middle_second (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (q v w u : Slice n) (δ ηv ηw : ℝ) (hδ : 0 ≤ δ)
    (hq : ∀ e, e ∉ good n S δ u → q e = 1)
    (hv : ∀ e ∈ good n S δ u, ‖(u e : ℍ) - (v e : ℍ)‖ ^ 2 ≤ ηv)
    (hw : ∀ e ∈ good n S δ u, ‖(u e : ℍ) - (w e : ℍ)‖ ^ 2 ≤ ηw) :
    β*(4-ηv-ηw-32*δ)*cost n q ≤
      WilsonMiddleBridge.action n β v w (q*u)+WilsonMiddleBridge.action n β v w (q⁻¹*u)-
        2*WilsonMiddleBridge.action n β v w u :=
  middle_second_active n β hβ _ q v w u δ ηv ηw hq
    (fun p e he hp => good_chord n S δ hδ u e he p hp) hv hw

theorem good_middle_small (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (q v w u : Slice n)
    (hq : ∀ e, e ∉ good n S (1 / 32) u → q e = 1)
    (hv : ∀ e ∈ good n S (1 / 32) u, ‖(u e : ℍ) - (v e : ℍ)‖ ^ 2 ≤ 1 / 2)
    (hw : ∀ e ∈ good n S (1 / 32) u, ‖(u e : ℍ) - (w e : ℍ)‖ ^ 2 ≤ 1 / 2) :
    2*β*cost n q ≤
      WilsonMiddleBridge.action n β v w (q*u)+WilsonMiddleBridge.action n β v w (q⁻¹*u)-
        2*WilsonMiddleBridge.action n β v w u := by
  have hh := good_middle_second n β hβ S q v w u (1 / 32) (1 / 2) (1 / 2)
    (by norm_num) hq hv hw
  convert hh using 1
  ring

theorem good_log_density (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (q v w u : Slice n)
    (hq : ∀ e, e ∉ good n S (1 / 32) u → q e = 1)
    (hv : ∀ e ∈ good n S (1 / 32) u, ‖(u e : ℍ) - (v e : ℍ)‖ ^ 2 ≤ 1 / 2)
    (hw : ∀ e ∈ good n S (1 / 32) u, ‖(u e : ℍ) - (w e : ℍ)‖ ^ 2 ≤ 1 / 2) :
    Real.log (WilsonMiddleEntropy.density n β v w (q*u))+
      Real.log (WilsonMiddleEntropy.density n β v w (q⁻¹*u))-
      2*Real.log (WilsonMiddleEntropy.density n β v w u) ≤ -2*β*cost n q := by
  have hh := good_middle_small n β hβ S q v w u hq hv hw
  simp only [WilsonMiddleEntropy.log_density]
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonMaskedCurvature
