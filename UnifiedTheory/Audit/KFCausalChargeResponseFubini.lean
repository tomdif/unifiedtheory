/- Whole-configuration Fubini for two independent charge angles.
Explicit continuous representatives inherit joint L2 integrability from
continuous Hilbert-space orbits. The complex pair integral is the pairing
of their means; the two angles are never identified. -/
import UnifiedTheory.Audit.KFCausalDisplacedResponseDensities
import UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalChargeResponseFubini
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)

def angles : Measure (ℝ × ℝ) := angleMeasure.prod angleMeasure
instance : IsProbabilityMeasure angles := by unfold angles; infer_instance

def measure : Measure ((ℝ × ℝ) × Configuration) := angles.prod volume

def pair (F G : ℝ → Configuration → ℂ) (z : (ℝ × ℝ) × Configuration) : ℂ :=
  star (F z.1.1 z.2)*G z.1.2 z.2

private theorem square_integral (f : Hilbert) (F : Configuration → ℂ)
    (hf : f =ᵐ[volume] F) : (∫ x, ‖F x‖^2) = ‖f‖^2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ) f,L2.inner_def,← integral_re (L2.integrable_inner (𝕜 := ℂ) f f)]
  apply integral_congr_ae
  filter_upwards [hf] with x hx
  rw [hx]
  exact norm_sq_eq_re_inner (𝕜 := ℂ) (F x)

private theorem joint_memLp (U : ℝ × ℝ → Hilbert) (F : ℝ × ℝ → Configuration → ℂ)
    (hU : MemLp U 2 angles) (hF : Continuous (fun z : (ℝ × ℝ) × Configuration => F z.1 z.2))
    (hr : ∀ t, U t =ᵐ[volume] F t) :
    MemLp (fun z : (ℝ × ℝ) × Configuration => F z.1 z.2) 2 measure := by
  have hm := hF.aestronglyMeasurable (μ := measure)
  have hs (t : ℝ × ℝ) : MemLp (F t) 2 volume := (Lp.memLp (U t)).ae_eq (hr t)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply (integrable_prod_iff (hm.norm.pow 2)).mpr
  refine ⟨Filter.Eventually.of_forall (fun t =>
    (memLp_two_iff_integrable_sq_norm (hs t).aestronglyMeasurable).mp (hs t)),?_⟩
  have he : (fun t => ∫ x : Configuration, ‖‖F t x‖^2‖) = (fun t => ‖U t‖^2) := by
    funext t
    simp only [norm_pow,norm_norm]
    exact square_integral (U t) (F t) (hr t)
  change Integrable (fun t => ∫ x : Configuration, ‖‖F t x‖^2‖) angles
  rw [he]
  exact (memLp_two_iff_integrable_sq_norm hU.aestronglyMeasurable).mp hU

variable (U V : ℝ → Hilbert) (F G : ℝ → Configuration → ℂ)
  (hU : Continuous U) (hV : Continuous V)
  (hF : Continuous (fun z : ℝ × Configuration => F z.1 z.2))
  (hG : Continuous (fun z : ℝ × Configuration => G z.1 z.2))
  (hrU : ∀ θ, U θ =ᵐ[volume] F θ) (hrV : ∀ θ, V θ =ᵐ[volume] G θ)

include hU hV hF hG hrU hrV in
theorem pair_integrable : Integrable (pair F G) measure := by
  have h1 := joint_memLp (fun t => U t.1) (fun t => F t.1)
    ((continuous_angle_memLp U hU).comp_fst angleMeasure)
    (hF.comp (continuous_fst.fst.prodMk continuous_snd)) (fun t => hrU t.1)
  have h2 := joint_memLp (fun t => V t.2) (fun t => G t.2)
    ((continuous_angle_memLp V hV).comp_snd angleMeasure)
    (hG.comp (continuous_fst.snd.prodMk continuous_snd)) (fun t => hrV t.2)
  exact h1.star.integrable_mul h2

private theorem inner_density (f g : Hilbert) (F G : Configuration → ℂ)
    (hf : f =ᵐ[volume] F) (hg : g =ᵐ[volume] G) :
    (∫ x : Configuration, star (F x)*G x) = inner ℂ f g := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf,hg] with x hx hy
  simp only [hx,hy,RCLike.inner_apply,Complex.star_def]
  ring

include hU hV hF hG hrU hrV in
theorem pair_integral : (∫ z, pair F G z ∂measure) =
    inner ℂ (∫ θ, U θ ∂angleMeasure) (∫ φ, V φ ∂angleMeasure) := by
  have hi := pair_integrable U V F G hU hV hF hG hrU hrV
  have he : (fun t : ℝ × ℝ => ∫ x : Configuration, pair F G (t,x)) =
      (fun t => inner ℂ (U t.1) (V t.2)) := by
    funext t
    exact inner_density _ _ _ _ (hrU t.1) (hrV t.2)
  have hinner : Integrable (fun t : ℝ × ℝ => inner ℂ (U t.1) (V t.2)) angles := by
    rw [← he]
    exact hi.integral_prod_left
  have hu := (continuous_angle_memLp U hU).integrable (by norm_num)
  have hv := (continuous_angle_memLp V hV).integrable (by norm_num)
  calc
    (∫ z, pair F G z ∂measure) = ∫ t, ∫ x : Configuration, pair F G (t,x) ∂volume ∂angles :=
      integral_prod _ hi
    _ = ∫ t, inner ℂ (U t.1) (V t.2) ∂angles := congrArg (fun f => ∫ t, f t ∂angles) he
    _ = ∫ θ, ∫ φ, inner ℂ (U θ) (V φ) ∂angleMeasure ∂angleMeasure := integral_prod _ hinner
    _ = ∫ θ, inner ℂ (U θ) (∫ φ, V φ ∂angleMeasure) ∂angleMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun θ => integral_inner hv (U θ))
    _ = inner ℂ (∫ θ, U θ ∂angleMeasure) (∫ φ, V φ ∂angleMeasure) := by
      calc
        _ = ∫ θ, star (inner ℂ (∫ φ, V φ ∂angleMeasure) (U θ)) ∂angleMeasure := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun θ => (inner_conj_symm _ _).symm)
        _ = _ := by
          change (∫ θ, (starRingEnd ℂ) (inner ℂ (∫ φ, V φ ∂angleMeasure) (U θ)) ∂angleMeasure) = _
          rw [integral_conj,integral_inner hu,inner_conj_symm]

#print axioms pair_integrable
#print axioms pair_integral
end
end UnifiedTheory.Audit.KFCausalChargeResponseFubini
