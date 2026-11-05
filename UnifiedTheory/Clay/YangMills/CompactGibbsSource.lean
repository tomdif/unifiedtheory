/- Source derivatives under an actual compact Gibbs law. Domination for
passing derivatives through the integral is proved from compactness. These
finite-cutoff identities do not give uniform ultraviolet source bounds. -/
import UnifiedTheory.Clay.YangMills.CompactGibbsContinuity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.CompactGibbsSource
noncomputable section
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- Compactness supplies a common integrable derivative bound on a time
neighborhood. No domination bound is supplied as a premise. -/
theorem integral_hasDerivAt (H H' : ℝ → X → ℝ)
    (hH : Continuous H.uncurry) (hH' : Continuous H'.uncurry)
    (hder : ∀ t x, HasDerivAt (fun s => H s x) (H' t x) t) (t : ℝ) :
    HasDerivAt (fun s => ∫ x, H s x ∂μ) (∫ x, H' t x ∂μ) t := by
  have hc : IsCompact (Set.Icc (t-1) (t+1) ×ˢ (Set.univ : Set X)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuousOn hH'.continuousOn
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := H) (F' := H') (bound := fun _ => C)
    (Ioo_mem_nhds (by linarith : t-1<t) (by linarith : t<t+1))
    (Eventually.of_forall (fun s =>
      (hH.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable))
    ((hH.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (hH'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (Eventually.of_forall (fun x s hs => hC (s,x)
      ⟨⟨hs.1.le,hs.2.le⟩,Set.mem_univ x⟩))
    (integrable_const C)
    (Eventually.of_forall (fun x s _ => hder s x))).2

def action (A F : X → ℝ) (t : ℝ) (x : X) : ℝ := A x - t*F x

def weight (A F : X → ℝ) (t : ℝ) (x : X) : ℝ := Real.exp (-action A F t x)

def partition (A F : X → ℝ) (t : ℝ) : ℝ := ∫ x, weight A F t x ∂μ

def moment (A F G : X → ℝ) (t : ℝ) : ℝ := ∫ x, weight A F t x * G x ∂μ

def expectation (A F G : X → ℝ) (t : ℝ) : ℝ :=
  ∫ x, G x ∂CompactGibbsContinuity.law μ (action A F t)

def covariance (A F G H : X → ℝ) (t : ℝ) : ℝ :=
  expectation μ A F (fun x => G x*H x) t -
    expectation μ A F G t * expectation μ A F H t

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem action_continuous (A F : X → ℝ) (hA : Continuous A) (hF : Continuous F) (t : ℝ) :
    Continuous (action A F t) := hA.sub (continuous_const.mul hF)

theorem partition_positive (A F : X → ℝ) (hA : Continuous A) (hF : Continuous F) (t : ℝ) :
    0 < partition μ A F t :=
  CompactGibbsContinuity.partition_positive μ (action A F t) (action_continuous A F hA hF t)

theorem expectation_eq_quotient (A F G : X → ℝ)
    (hA : Continuous A) (hF : Continuous F) (t : ℝ) :
    expectation μ A F G t = moment μ A F G t / partition μ A F t := by
  unfold expectation CompactGibbsContinuity.law
  exact LocalGibbsComparison.weighted_integral μ (weight A F t)
    (Real.continuous_exp.comp (action_continuous A F hA hF t).neg).measurable
    (fun _ => (Real.exp_pos _).le) (partition_positive μ A F hA hF t) G

/-- The numerator derivative is proved by differentiation under the integral. -/
theorem moment_hasDerivAt (A F G : X → ℝ)
    (hA : Continuous A) (hF : Continuous F) (hG : Continuous G) (t : ℝ) :
    HasDerivAt (moment μ A F G) (moment μ A F (fun x => F x*G x) t) t := by
  apply integral_hasDerivAt μ
    (fun s x => weight A F s x*G x)
    (fun s x => weight A F s x*(F x*G x))
  · unfold Function.uncurry weight action
    fun_prop
  · unfold Function.uncurry weight action
    fun_prop
  · intro s x
    have hlin : HasDerivAt (fun u : ℝ => -action A F u x) (F x) s := by
      convert ((hasDerivAt_const s (A x)).sub ((hasDerivAt_id s).mul_const (F x))).neg using 1
      simp
    convert hlin.exp.mul_const (G x) using 1
    unfold weight
    ring

/-- The true partition derivative, with its unnormalized numerator. -/
theorem partition_hasDerivAt (A F : X → ℝ)
    (hA : Continuous A) (hF : Continuous F) (t : ℝ) :
    HasDerivAt (partition μ A F) (moment μ A F F t) t := by
  have he : moment μ A F (fun _ => 1) = partition μ A F := by
    funext s
    simp only [moment, mul_one, partition]
  simpa only [he, moment, mul_one] using
    moment_hasDerivAt μ A F (fun _ => 1) hA hF continuous_const t

/-- The real source derivative of log Z is the actual sourced expectation. -/
theorem log_partition_hasDerivAt (A F : X → ℝ)
    (hA : Continuous A) (hF : Continuous F) (t : ℝ) :
    HasDerivAt (fun s => Real.log (partition μ A F s)) (expectation μ A F F t) t := by
  rw [expectation_eq_quotient μ A F F hA hF t]
  exact (partition_hasDerivAt μ A F hA hF t).log (partition_positive μ A F hA hF t).ne'

/-- Differentiating an actual Gibbs expectation gives its connected covariance. -/
theorem expectation_hasDerivAt (A F G : X → ℝ)
    (hA : Continuous A) (hF : Continuous F) (hG : Continuous G) (t : ℝ) :
    HasDerivAt (expectation μ A F G) (covariance μ A F G F t) t := by
  have hd := (moment_hasDerivAt μ A F G hA hF hG t).div
    (partition_hasDerivAt μ A F hA hF t) (partition_positive μ A F hA hF t).ne'
  have hf : expectation μ A F G = fun s => moment μ A F G s / partition μ A F s := by
    funext s
    exact expectation_eq_quotient μ A F G hA hF s
  rw [hf]
  convert hd using 1
  unfold covariance
  rw [expectation_eq_quotient μ A F (fun x => G x*F x) hA hF t,
    expectation_eq_quotient μ A F G hA hF t, expectation_eq_quotient μ A F F hA hF t]
  have he : moment μ A F (fun x => G x*F x) t = moment μ A F (fun x => F x*G x) t := by
    congr 1
    funext x
    exact mul_comm _ _
  rw [he]
  field_simp

/-- The first source derivative itself has the variance as its derivative. -/
theorem mean_hasDerivAt (A F : X → ℝ)
    (hA : Continuous A) (hF : Continuous F) (t : ℝ) :
    HasDerivAt (expectation μ A F F) (covariance μ A F F F t) t :=
  expectation_hasDerivAt μ A F F hA hF hF t

/-- The covariance diagonal is the integral of the centered square under
the same sourced Gibbs law. -/
theorem covariance_self_eq (A F G : X → ℝ)
    (hA : Continuous A) (hF : Continuous F) (hG : Continuous G) (t : ℝ) :
    covariance μ A F G G t =
      ∫ x, (G x - expectation μ A F G t)^2
        ∂CompactGibbsContinuity.law μ (action A F t) := by
  let ν := CompactGibbsContinuity.law μ (action A F t)
  letI : IsProbabilityMeasure ν := CompactGibbsContinuity.law_probability μ
    (action A F t) (action_continuous A F hA hF t)
  let m := expectation μ A F G t
  have hGint : Integrable G ν :=
    hG.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hG2 : Integrable (fun x => G x*G x) ν :=
    (hG.mul hG).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlin : Integrable (fun x => (2*m)*G x) ν := hGint.const_mul (2*m)
  symm
  calc
    (∫ x, (G x-m)^2 ∂ν) = ∫ x, (G x*G x-(2*m)*G x)+m^2 ∂ν := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by ring)
    _ = (∫ x, G x*G x ∂ν) - (2*m)*(∫ x, G x ∂ν) + m^2 := by
      have hadd := integral_add (hG2.sub hlin) (integrable_const (m^2))
      have hsub := integral_sub hG2 hlin
      simp only [Pi.sub_apply] at hadd hsub
      rw [hadd, hsub, integral_const_mul, integral_const, probReal_univ, smul_eq_mul, one_mul]
    _ = covariance μ A F G G t := by
      change (∫ x, G x*G x ∂ν) - (2*m)*m+m^2 = (∫ x, G x*G x ∂ν)-m*m
      ring

theorem covariance_self_nonneg (A F G : X → ℝ)
    (hA : Continuous A) (hF : Continuous F) (hG : Continuous G) (t : ℝ) :
    0 ≤ covariance μ A F G G t := by
  rw [covariance_self_eq μ A F G hA hF hG t]
  exact integral_nonneg (fun x => sq_nonneg _)

/-- This is a genuine second source derivative, expressed using Lean's deriv. -/
theorem log_partition_second_hasDerivAt (A F : X → ℝ)
    (hA : Continuous A) (hF : Continuous F) (t : ℝ) :
    HasDerivAt (fun s => deriv (fun u => Real.log (partition μ A F u)) s)
      (covariance μ A F F F t) t := by
  have he : (fun s => deriv (fun u => Real.log (partition μ A F u)) s) = expectation μ A F F := by
    funext s
    exact (log_partition_hasDerivAt μ A F hA hF s).deriv
  rw [he]
  exact mean_hasDerivAt μ A F hA hF t

end
end UnifiedTheory.Clay.YangMills.CompactGibbsSource
