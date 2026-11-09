/- Fubini on a time triangle turns cumulative spacetime force into a
time-dependent test integral. All integrability is derived from finite mass. -/
import UnifiedTheory.Audit.KFCausalGlobalSpacetimeForce
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalSpacetimeTriangularIntegral
noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction

def triangle (η' : ℝ →ᵇ ℂ) (q : (ℝ × ℝ) →ᵇ ℂ) (w : ℝ × (ℝ × ℝ)) : ℂ :=
  if w.2.1 ≤ w.1 then η' w.1*q w.2 else 0

def cumulative (μ : Measure (ℝ × ℝ)) (a t : ℝ) (q : (ℝ × ℝ) →ᵇ ℂ) : ℂ :=
  ∫ z in Icc a t ×ˢ univ, q z ∂μ

theorem triangle_integrable (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (a b : ℝ) (η' : ℝ →ᵇ ℂ) (q : (ℝ × ℝ) →ᵇ ℂ) :
    Integrable (triangle η' q) ((volume.restrict (Icc a b)).prod μ) := by
  have hm : MeasurableSet {w : ℝ × (ℝ × ℝ) | w.2.1 ≤ w.1} :=
    (isClosed_le (continuous_fst.comp continuous_snd) continuous_fst).measurableSet
  simpa only [triangle,Set.indicator_apply,mem_setOf_eq] using
    ((η'.integrable (volume.restrict (Icc a b))).mul_prod (q.integrable μ)).indicator hm

theorem triangle_inner (μ : Measure (ℝ × ℝ)) (a b : ℝ)
    (hμ : ∀ᵐ z ∂μ, z.1 ∈ Icc a b)
    (η' : ℝ →ᵇ ℂ) (q : (ℝ × ℝ) →ᵇ ℂ) (t : ℝ) :
    (∫ z, triangle η' q (t,z) ∂μ) = η' t*cumulative μ a t q := by
  unfold cumulative
  rw [← integral_const_mul,← integral_indicator (measurableSet_Icc.prod MeasurableSet.univ)]
  apply integral_congr_ae
  filter_upwards [hμ] with z hz
  simp only [triangle,Set.indicator_apply,mem_prod,mem_Icc,mem_univ,and_true,hz.1,true_and]

theorem weighted_cumulative_integrable (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (a b : ℝ) (hμ : ∀ᵐ z ∂μ, z.1 ∈ Icc a b)
    (η' : ℝ →ᵇ ℂ) (q : (ℝ × ℝ) →ᵇ ℂ) :
    Integrable (fun t => η' t*cumulative μ a t q) (volume.restrict (Icc a b)) := by
  apply (triangle_integrable μ a b η' q).integral_prod_left.congr
  exact ae_of_all _ (triangle_inner μ a b hμ η' q)

theorem triangle_outer (a b : ℝ) (η η' : ℝ →ᵇ ℂ)
    (hη : ∀ t : ℝ, HasDerivAt η (η' t) t) (q : (ℝ × ℝ) →ᵇ ℂ)
    (z : ℝ × ℝ) (hz : z.1 ∈ Icc a b) :
    (∫ t in Icc a b, triangle η' q (t,z)) = (η b-η z.1)*q z := by
  have he : Ici z.1 ∩ Icc a b = Icc z.1 b := by
    ext t
    simp only [mem_inter_iff,mem_Ici,mem_Icc]
    constructor
    · exact fun ht => ⟨ht.1,ht.2.2⟩
    · exact fun ht => ⟨ht.1,le_trans hz.1 ht.1,ht.2⟩
  calc
    _ = ∫ t in Icc a b, (Ici z.1).indicator (fun t => η' t*q z) t := by
      apply integral_congr_ae
      exact ae_of_all _ (fun t => by simp only [triangle,Set.indicator_apply,mem_Ici])
    _ = (∫ t in Icc z.1 b, η' t)*q z := by
      rw [integral_indicator measurableSet_Ici,Measure.restrict_restrict measurableSet_Ici,
        he,integral_mul_const]
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hz.2,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hη t)
          (η'.continuous.intervalIntegrable z.1 b)]

theorem triangular_identity (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (a b : ℝ) (hμ : ∀ᵐ z ∂μ, z.1 ∈ Icc a b)
    (η η' : ℝ →ᵇ ℂ) (hη : ∀ t : ℝ, HasDerivAt η (η' t) t)
    (q : (ℝ × ℝ) →ᵇ ℂ) :
    (∫ t in Icc a b, η' t*cumulative μ a t q) =
      ∫ z, (η b-η z.1)*q z ∂μ := by
  calc
    _ = ∫ t in Icc a b, ∫ z, triangle η' q (t,z) ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun t => (triangle_inner μ a b hμ η' q t).symm)
    _ = ∫ z, (∫ t in Icc a b, triangle η' q (t,z)) ∂μ :=
      integral_integral_swap (triangle_integrable μ a b η' q)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hμ] with z hz
      exact triangle_outer a b η η' hη q z hz

def timeWeight (η : ℝ →ᵇ ℂ) (q : (ℝ × ℝ) →ᵇ ℂ) : (ℝ × ℝ) →ᵇ ℂ :=
  (η.compContinuous ⟨Prod.fst,continuous_fst⟩)*q

theorem triangular_linear_identity (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (a b : ℝ) (hμ : ∀ᵐ z ∂μ, z.1 ∈ Icc a b)
    (η η' : ℝ →ᵇ ℂ) (hη : ∀ t : ℝ, HasDerivAt η (η' t) t)
    (q : (ℝ × ℝ) →ᵇ ℂ) :
    (∫ t in Icc a b, η' t*cumulative μ a t q) =
      η b*(∫ z, q z ∂μ)-(∫ z, timeWeight η q z ∂μ) := by
  rw [triangular_identity μ a b hμ η η' hη q]
  have he : (fun z => (η b-η z.1)*q z) = (fun z => η b*q z-timeWeight η q z) := by
    funext z
    exact sub_mul (η b) (η z.1) (q z)
  rw [he,integral_sub ((q.integrable μ).const_mul (η b)) ((timeWeight η q).integrable μ),
    integral_const_mul]

#print axioms triangle_integrable
#print axioms triangle_inner
#print axioms weighted_cumulative_integrable
#print axioms triangle_outer
#print axioms triangular_identity
#print axioms triangular_linear_identity
end
end UnifiedTheory.Audit.KFCausalSpacetimeTriangularIntegral
