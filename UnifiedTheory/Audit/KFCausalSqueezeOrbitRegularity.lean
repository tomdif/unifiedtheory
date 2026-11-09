/- Integrated small-squeeze regularity with its precise exponent range.
The singular integral is controlled directly; no identification with an
unbounded spectral domain is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorSqueezeOrbitEstimate
import UnifiedTheory.Audit.KFCausalPairedSqueezeTimeDerivative
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalSqueezeOrbitRegularity
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalPairedSqueezeTransport (transport transport_initial)
open UnifiedTheory.Audit.KFCausalPairedSqueezeContinuity (transport_strong_continuous)
open UnifiedTheory.Audit.KFCausalPairedSqueezeGenerator (squeezeMomentum)
open UnifiedTheory.Audit.KFCausalPairedSqueezeTimeDerivative (affine_time_derivative)
open UnifiedTheory.Audit.KFCausalNeutralReferencePairing (coefficient coefficient_norm)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeOrbitEstimate (orbitGap)

def density (p : ℝ) (f : Hilbert) (a : ℝ) : ℝ := a^(-1-p)*orbitGap a f
def regularity (p : ℝ) (f : Hilbert) : ℝ := ∫ a in Ioo (0:ℝ) 1, density p f a

theorem orbitGap_continuous (f : Hilbert) : Continuous (fun a => orbitGap a f) :=
  ((transport_strong_continuous f).sub continuous_const).norm.pow 2

theorem generator_orbit_bound (h : ℝ) (hne : h ≠ 0) (f z : Hilbert)
    (hfz : (f,z) ∈ (squeezeMomentum h).graph) (a : ℝ) :
    ‖transport a f-f‖ ≤ (‖z‖/|h|)*|a| := by
  have hd (b : ℝ) : HasDerivAt (fun t => transport t f) (coefficient h • transport b z) b := by
    simpa only [one_mul,Complex.ofReal_one,mul_one] using affine_time_derivative h hne 1 b f z hfz
  have hb (b : ℝ) (_ : b ∈ (univ : Set ℝ)) : ‖coefficient h • transport b z‖ ≤ ‖z‖/|h| := by
    rw [norm_smul,coefficient_norm,LinearIsometryEquiv.norm_map]
    exact le_of_eq (by ring)
  have he := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun b (_ : b ∈ (univ : Set ℝ)) => (hd b).hasDerivWithinAt) hb (mem_univ 0) (mem_univ a)
  simpa only [transport_initial,sub_zero,Real.norm_eq_abs] using he

theorem generator_gap_bound (h : ℝ) (hne : h ≠ 0) (f z : Hilbert)
    (hfz : (f,z) ∈ (squeezeMomentum h).graph) (a : ℝ) :
    orbitGap a f ≤ (‖z‖/|h|)^2*a^2 := by
  simpa only [orbitGap,mul_pow,sq_abs] using
    pow_le_pow_left₀ (norm_nonneg _) (generator_orbit_bound h hne f z hfz a) 2

theorem generator_small_gap (h : ℝ) (hne : h ≠ 0) (f z : Hilbert)
    (hfz : (f,z) ∈ (squeezeMomentum h).graph) (a : ℝ) (ha : |a| ≤ 1) :
    orbitGap a f ≤ (‖z‖/|h|)^2*|a| := by
  apply (generator_gap_bound h hne f z hfz a).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  nlinarith [sq_abs a,abs_nonneg a]

theorem density_continuousOn (p : ℝ) (f : Hilbert) : ContinuousOn (density p f) (Ioo (0:ℝ) 1) :=
  (continuousOn_id.rpow_const (fun _ ha => Or.inl ha.1.ne')).mul (orbitGap_continuous f).continuousOn

private theorem weight_linear (p a : ℝ) (ha : 0 < a) : a^(-1-p)*a = a^(-p) := by
  calc
    _ = a^(-1-p)*a^(1:ℝ) := by rw [Real.rpow_one]
    _ = a^(-1-p+1) := (Real.rpow_add ha _ _).symm
    _ = _ := by congr 1; ring

theorem density_bound (p M : ℝ) (f : Hilbert)
    (hb : ∀ a ∈ Ioo (0:ℝ) 1, orbitGap a f ≤ M*a) (a : ℝ) (ha : a ∈ Ioo (0:ℝ) 1) :
    density p f a ≤ M*a^(-p) := by
  calc
    density p f a ≤ a^(-1-p)*(M*a) := mul_le_mul_of_nonneg_left (hb a ha) (Real.rpow_nonneg ha.1.le _)
    _ = M*(a^(-1-p)*a) := by ring
    _ = _ := by rw [weight_linear p a ha.1]

private theorem power_integral (p : ℝ) (hp : p < 1) :
    (∫ a in Ioo (0:ℝ) 1, a^(-p)) = 1/(1-p) := by
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    integral_rpow (Or.inl (by linarith : -1 < -p)),Real.one_rpow,
    Real.zero_rpow (by linarith : -p+1 ≠ 0),sub_zero]
  congr 1
  ring

theorem density_integrable (p : ℝ) (hp : p < 1) (M : ℝ) (f : Hilbert)
    (hb : ∀ a ∈ Ioo (0:ℝ) 1, orbitGap a f ≤ M*a) :
    IntegrableOn (density p f) (Ioo (0:ℝ) 1) := by
  have hi : IntegrableOn (fun a : ℝ => a^(-p)) (Ioo (0:ℝ) 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0:ℝ)<1)).mpr (by linarith)
  apply (hi.const_mul M).mono' ((density_continuousOn p f).aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
  have hn : 0 ≤ density p f a := mul_nonneg (Real.rpow_nonneg ha.1.le _) (sq_nonneg _)
  rw [Real.norm_eq_abs,abs_of_nonneg hn]
  exact density_bound p M f hb a ha

theorem regularity_bound (p : ℝ) (hp : p < 1) (M : ℝ) (f : Hilbert)
    (hb : ∀ a ∈ Ioo (0:ℝ) 1, orbitGap a f ≤ M*a) : regularity p f ≤ M/(1-p) := by
  have hi : IntegrableOn (fun a : ℝ => a^(-p)) (Ioo (0:ℝ) 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0:ℝ)<1)).mpr (by linarith)
  calc
    regularity p f ≤ ∫ a in Ioo (0:ℝ) 1, M*a^(-p) := by
      apply integral_mono_ae (density_integrable p hp M f hb) (hi.const_mul M)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
      exact density_bound p M f hb a ha
    _ = M/(1-p) := by rw [integral_const_mul,power_integral p hp]; ring

theorem density_comparison (p B : ℝ) (f g : Hilbert)
    (hb : ∀ a ∈ Ioo (0:ℝ) 1, orbitGap a g ≤ orbitGap a f+B*a)
    (a : ℝ) (ha : a ∈ Ioo (0:ℝ) 1) : density p g a ≤ density p f a+B*a^(-p) := by
  calc
    density p g a ≤ a^(-1-p)*(orbitGap a f+B*a) :=
      mul_le_mul_of_nonneg_left (hb a ha) (Real.rpow_nonneg ha.1.le _)
    _ = density p f a+B*(a^(-1-p)*a) := by unfold density; ring
    _ = _ := by rw [weight_linear p a ha.1]

theorem integrable_of_gap_comparison (p : ℝ) (hp : p < 1) (B : ℝ) (f g : Hilbert)
    (hf : IntegrableOn (density p f) (Ioo (0:ℝ) 1))
    (hb : ∀ a ∈ Ioo (0:ℝ) 1, orbitGap a g ≤ orbitGap a f+B*a) :
    IntegrableOn (density p g) (Ioo (0:ℝ) 1) := by
  have hi : IntegrableOn (fun a : ℝ => a^(-p)) (Ioo (0:ℝ) 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0:ℝ)<1)).mpr (by linarith)
  apply (hf.add (hi.const_mul B)).mono' ((density_continuousOn p g).aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
  have hn : 0 ≤ density p g a := mul_nonneg (Real.rpow_nonneg ha.1.le _) (sq_nonneg _)
  rw [Real.norm_eq_abs,abs_of_nonneg hn]
  exact density_comparison p B f g hb a ha

theorem regularity_comparison (p : ℝ) (hp : p < 1) (B : ℝ) (f g : Hilbert)
    (hf : IntegrableOn (density p f) (Ioo (0:ℝ) 1))
    (hb : ∀ a ∈ Ioo (0:ℝ) 1, orbitGap a g ≤ orbitGap a f+B*a) :
    regularity p g ≤ regularity p f+B/(1-p) := by
  have hi : IntegrableOn (fun a : ℝ => a^(-p)) (Ioo (0:ℝ) 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0:ℝ)<1)).mpr (by linarith)
  calc
    regularity p g ≤ ∫ a in Ioo (0:ℝ) 1, density p f a+B*a^(-p) := by
      apply integral_mono_ae (integrable_of_gap_comparison p hp B f g hf hb) (hf.add (hi.const_mul B))
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
      exact density_comparison p B f g hb a ha
    _ = regularity p f+B/(1-p) := by
      rw [integral_add hf (hi.const_mul B),integral_const_mul,power_integral p hp]
      unfold regularity
      ring

open UnifiedTheory.Audit.KFCausalClockFloorCombinedUnitary (combined)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeOrbitEstimate (orbitGap_combined)

theorem density_combined (p ε h v t : ℝ) (f : Hilbert) :
    density p (combined ε h v t f) = density p f := by
  funext a
  exact congrArg (fun x : ℝ => a^(-1-p)*x) (orbitGap_combined ε h v t a f)

theorem regularity_combined (p ε h v t : ℝ) (f : Hilbert) :
    regularity p (combined ε h v t f) = regularity p f := by
  unfold regularity
  rw [density_combined]

#print axioms orbitGap_continuous
#print axioms generator_orbit_bound
#print axioms generator_gap_bound
#print axioms generator_small_gap
#print axioms density_continuousOn
#print axioms density_bound
#print axioms density_integrable
#print axioms regularity_bound
#print axioms density_comparison
#print axioms integrable_of_gap_comparison
#print axioms regularity_comparison
#print axioms density_combined
#print axioms regularity_combined
end
end UnifiedTheory.Audit.KFCausalSqueezeOrbitRegularity
