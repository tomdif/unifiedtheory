/- Determinant-one transport of the actual explicit Minkowski double-cone
coordinate integral. Integrability is derived from a bounded rest diamond. -/
import UnifiedTheory.Audit.KFCausalConformal4DDiamondAffine
import UnifiedTheory.Audit.KFCausalConformal4DTemporalVariation
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalConformal4DDiamondMeasure
noncomputable section
open MeasureTheory Real Set Metric
open KFCausalConformal4DDiamondBenchmark (Point metric)
open KFCausalConformal4DBoostedMoments KFCausalConformal4DDiamondAffine
open KFCausalConformal4DTemporalVariation

def spatialRadius (v : Point) : ℝ := sqrt (v 1^2+v 2^2+v 3^2)

theorem future_iff_radius (v : Point) : future v ↔ spatialRadius v<v 0 := by
  have hs : 0 ≤ v 1^2+v 2^2+v 3^2 := by positivity
  constructor
  · intro hv
    apply (sqrt_lt hs hv.1.le).2
    have h := hv.2
    dsimp [lorentzSquare] at h
    linarith
  · intro hv
    have h0 : 0<v 0 := (sqrt_nonneg _).trans_lt hv
    have hsq := (sqrt_lt hs h0.le).1 hv
    refine ⟨h0,?_⟩
    dsimp [lorentzSquare]
    linarith

theorem rest_diamond_iff (T : ℝ) (v : Point) :
    v ∈ restDiamond T ↔ |v 0|+spatialRadius v<T := by
  have h1 : spatialRadius (v- -tip T)=spatialRadius v := by simp [spatialRadius,tip]
  have h2 : spatialRadius (tip T-v)=spatialRadius v := by simp [spatialRadius,tip]
  change (future (v- -tip T) ∧ future (tip T-v)) ↔ _
  rw [future_iff_radius,future_iff_radius,h1,h2]
  simp only [Pi.sub_apply,Pi.neg_apply,tip,Matrix.cons_val_zero,sub_neg_eq_add]
  by_cases hv : 0≤v 0
  · rw [abs_of_nonneg hv]
    constructor <;> intro h
    · linarith [h.2]
    · constructor <;> linarith
  · rw [abs_of_neg (lt_of_not_ge hv)]
    constructor <;> intro h
    · linarith [h.1]
    · constructor <;> linarith

theorem diamond_coordinate_iff (t r : ℝ) (x : Point) :
    x ∈ diamond (endpoint t r) 0 ↔
      t<x 0 ∧ x 0<0 ∧ (x 1-r)^2+x 2^2+x 3^2<(x 0-t)^2 ∧
        x 1^2+x 2^2+x 3^2<x 0^2 := by
  change ((0<x 0-t ∧ -(x 0-t)^2+(x 1-r)^2+(x 2-0)^2+(x 3-0)^2<0) ∧
    (0<0-x 0 ∧ -(0-x 0)^2+(0-x 1)^2+(0-x 2)^2+(0-x 3)^2<0)) ↔ _
  simp only [sub_zero,zero_sub,neg_sq]
  constructor
  · rintro ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  · rintro ⟨h0,h1,h2,h3⟩
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

theorem rest_subset_closedBall (T : ℝ) (hT : 0≤T) :
    restDiamond T ⊆ closedBall (0:Point) T := by
  intro v hv
  have hr := (rest_diamond_iff T v).1 hv
  have hR : 0≤spatialRadius v := sqrt_nonneg _
  have hs : (spatialRadius v)^2=v 1^2+v 2^2+v 3^2 := sq_sqrt (by positivity)
  have hRT : spatialRadius v ≤ T := by linarith [abs_nonneg (v 0)]
  have hRT2 : (spatialRadius v)^2 ≤ T^2 := (sq_le_sq₀ hR hT).2 hRT
  have hb : ∀ z : ℝ, z^2 ≤ T^2 → |z| ≤ T := by
    intro z hz
    exact (sq_le_sq₀ (abs_nonneg z) hT).1 (by simpa only [sq_abs] using hz)
  rw [mem_closedBall_zero_iff,pi_norm_le_iff_of_nonneg hT]
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · change |v 0|≤T
    linarith
  · change |v 1|≤T
    exact hb _ (by nlinarith [sq_nonneg (v 2),sq_nonneg (v 3)])
  · change |v 2|≤T
    exact hb _ (by nlinarith [sq_nonneg (v 1),sq_nonneg (v 3)])
  · change |v 3|≤T
    exact hb _ (by nlinarith [sq_nonneg (v 1),sq_nonneg (v 2)])

theorem rest_integrable (T : ℝ) (hT : 0≤T) (f : Point → ℝ) (hf : Continuous f) :
    IntegrableOn f (restDiamond T) :=
  (hf.continuousOn.integrableOn_compact (isCompact_closedBall (0:Point) T)).mono_set
    (rest_subset_closedBall T hT)

private theorem matrix_action (A B : ℝ) :
    ((boostMatrix A B).toLin' : Point → Point)=boost A B := by
  ext v i
  fin_cases i <;> simp [boostMatrix,boost,Matrix.toLin'_apply,Matrix.mulVec,
    dotProduct,Fin.sum_univ_succ]

theorem boost_measurePreserving (A B : ℝ) (h : A^2-B^2=1) :
    MeasurePreserving (boost A B) volume volume := by
  refine ⟨(boostEquiv A B h).continuous.measurable,?_⟩
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi
    (M := boostMatrix A B) (by rw [boost_determinant A B h]; norm_num)
  simpa only [matrix_action,boost_determinant A B h,inv_one,abs_one,
    ENNReal.ofReal_one,one_smul] using hm

theorem affine_measurePreserving (o : Point) (A B : ℝ) (h : A^2-B^2=1) :
    MeasurePreserving (affine o A B) volume volume :=
  (measurePreserving_add_left volume o).comp (boost_measurePreserving A B h)

theorem retarded_integral_transport (t r : ℝ) (ht : t<0) (hq : 0<t^2-r^2)
    (f : Point → ℝ) :
    (∫ x in diamond (endpoint t r) 0, f x) =
      ∫ z in restDiamond (sqrt (t^2-r^2)/2),
        f (affine (center t r) (t/sqrt (t^2-r^2)) (r/sqrt (t^2-r^2)) z) := by
  obtain ⟨h,_,_⟩ := retarded_parameters t r ht hq
  rw [← retarded_diamond_image t r ht hq]
  exact (affine_measurePreserving _ _ _ h).setIntegral_image_emb
    (affineEquiv _ _ _ h).measurableEmbedding f _

theorem retarded_integrable (t r : ℝ) (ht : t<0) (hq : 0<t^2-r^2)
    (f : Point → ℝ) (hf : Continuous f) :
    IntegrableOn f (diamond (endpoint t r) 0) := by
  obtain ⟨h,_,hT⟩ := retarded_parameters t r ht hq
  rw [← retarded_diamond_image t r ht hq]
  apply ((affine_measurePreserving _ _ _ h).integrableOn_image
    (affineEquiv _ _ _ h).measurableEmbedding).2
  exact rest_integrable _ hT.le _ (hf.comp (affineEquiv _ _ _ h).continuous)

theorem density_integral_transport (c t r : ℝ) (ht : t<0) (hq : 0<t^2-r^2) :
    (∫ x in diamond (endpoint t r) 0, sqrt |Matrix.det (metric (2*c) 0 x)|) =
      ∫ z in restDiamond (sqrt (t^2-r^2)/2),
        density c (t/2+(t/sqrt (t^2-r^2))*z 0+(r/sqrt (t^2-r^2))*z 1) := by
  rw [retarded_integral_transport t r ht hq]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [density_at_point]
  congr 1
  change t/2+((t/sqrt (t^2-r^2))*z 0+(r/sqrt (t^2-r^2))*z 1)=_
  ring

#print axioms future_iff_radius
#print axioms rest_diamond_iff
#print axioms diamond_coordinate_iff
#print axioms rest_subset_closedBall
#print axioms rest_integrable
#print axioms boost_measurePreserving
#print axioms affine_measurePreserving
#print axioms retarded_integral_transport
#print axioms retarded_integrable
#print axioms density_integral_transport
end
end UnifiedTheory.Audit.KFCausalConformal4DDiamondMeasure
