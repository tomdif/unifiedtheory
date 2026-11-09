/-
  Finite scalar support for ENTANGLED_ACOUSTIC_BOUNDS.md.
  Gaussian conditioning, operator comparison, existence/uniqueness of the
  ground state, and the infinite-dimensional spectral representation are
  analytical suppliers, not assertions formalized by this module.
-/
import UnifiedTheory.Audit.KFCausalGeometryStability

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalEntangledAcoustic
noncomputable section
open scoped BigOperators

theorem averaged_covariance_bounds {ι : Type*} (s : Finset ι)
    (w v : ι → ℝ) (lo hi : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hn : ∑ i ∈ s, w i = 1)
    (hv : ∀ i ∈ s, lo ≤ v i ∧ v i ≤ hi) :
    lo ≤ ∑ i ∈ s, w i * v i ∧ ∑ i ∈ s, w i * v i ≤ hi := by
  constructor
  · calc
      lo = ∑ i ∈ s, w i * lo := by rw [← Finset.sum_mul, hn, one_mul]
      _ ≤ ∑ i ∈ s, w i * v i := Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left (hv i hi).1 (hw i hi)
  · calc
      (∑ i ∈ s, w i * v i) ≤ ∑ i ∈ s, w i * hi := Finset.sum_le_sum fun i hi' =>
        mul_le_mul_of_nonneg_left (hv i hi').2 (hw i hi')
      _ = hi := by rw [← Finset.sum_mul, hn, one_mul]

theorem weighted_variance_identity {ι : Type*} (s : Finset ι)
    (w v : ι → ℝ) (m : ℝ)
    (hn : ∑ i ∈ s, w i = 1) (hm : ∑ i ∈ s, w i * v i = m) :
    (∑ i ∈ s, w i * (v i - m) ^ 2) = (∑ i ∈ s, w i * v i ^ 2) - m ^ 2 := by
  calc
    (∑ i ∈ s, w i * (v i - m) ^ 2) =
        ∑ i ∈ s, (w i * v i ^ 2 - 2 * m * (w i * v i) + m ^ 2 * w i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i ∈ s, w i * v i ^ 2) - m ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, hm, hn]
      ring

theorem gaussian_mixture_cumulant {ι : Type*} (s : Finset ι)
    (w v : ι → ℝ) (m : ℝ)
    (hn : ∑ i ∈ s, w i = 1) (hm : ∑ i ∈ s, w i * v i = m) :
    3 * (∑ i ∈ s, w i * v i ^ 2) - 3 * m ^ 2 =
      3 * (∑ i ∈ s, w i * (v i - m) ^ 2) := by
  rw [weighted_variance_identity s w v m hn hm]
  ring

theorem gaussian_mixture_cumulant_nonnegative {ι : Type*} (s : Finset ι)
    (w v : ι → ℝ) (m : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hn : ∑ i ∈ s, w i = 1) (hm : ∑ i ∈ s, w i * v i = m) :
    0 ≤ 3 * (∑ i ∈ s, w i * v i ^ 2) - 3 * m ^ 2 := by
  rw [gaussian_mixture_cumulant s w v m hn hm]
  exact mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))

theorem spectral_probability_normalization {ι : Type*} (s : Finset ι)
    (energy weight : ι → ℝ) (chi : ℝ) (hc : chi ≠ 0)
    (hs : ∑ i ∈ s, 2 * energy i * weight i = 1 / chi) :
    ∑ i ∈ s, 2 * chi * energy i * weight i = 1 := by
  calc
    (∑ i ∈ s, 2 * chi * energy i * weight i) =
        chi * ∑ i ∈ s, 2 * energy i * weight i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 1 := by rw [hs]; field_simp

theorem resolvent_second_moment_bound (t response b : ℝ)
    (hb : 0 < t + b) (hr : 1 / (t + b) ≤ response) :
    t * (1 - t * response) ≤ b * t / (t + b) := by
  have h := mul_le_mul_of_nonneg_left hr (sq_nonneg t)
  simp only [mul_one_div] at h
  have hid : t - t ^ 2 / (t + b) = b * t / (t + b) := by
    field_simp
    ring
  calc
    t * (1 - t * response) ≤ t - t ^ 2 / (t + b) := by nlinarith
    _ = b * t / (t + b) := hid

theorem spectral_low_tail (mass alpha inverseMoment omega : ℝ)
    (hm : mass ≤ (alpha * omega) ^ 2 * inverseMoment)
    (hbound : omega ^ 2 * inverseMoment ≤ 4) : mass ≤ 4 * alpha ^ 2 := by
  have h := mul_le_mul_of_nonneg_left hbound (sq_nonneg alpha)
  nlinarith [sq_nonneg alpha]

theorem spectral_high_tail (mass radius moment omega : ℝ)
    (hr : 0 < radius) (ho : 0 < omega)
    (hm : (radius * omega) ^ 2 * mass ≤ moment)
    (hbound : moment ≤ 4 * omega ^ 2) : mass ≤ 4 / radius ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
  nlinarith [sq_pos_of_pos ho]

theorem spectral_annulus_bound (low band high alpha radius : ℝ)
    (hn : low + band + high = 1)
    (hl : low ≤ 4 * alpha ^ 2) (hh : high ≤ 4 / radius ^ 2) :
    1 - 4 * alpha ^ 2 - 4 / radius ^ 2 ≤ band := by linarith

theorem half_weight_in_acoustic_band (low band high : ℝ)
    (hn : low + band + high = 1) (hl : low ≤ 1 / 4) (hh : high ≤ 1 / 4) :
    1 / 2 ≤ band := by linarith

theorem unweighted_band_fraction (band total chi omega : ℝ)
    (hb : 1 / (16 * chi * omega) ≤ band)
    (ht : total ≤ 1 / (chi * omega)) : total / 16 ≤ band := by
  have h := (div_le_div_of_nonneg_right ht (by norm_num : (0 : ℝ) ≤ 16))
  have hid : (1 / (chi * omega)) / 16 = 1 / (16 * chi * omega) := by ring
  rw [hid] at h
  exact h.trans hb

theorem variational_excitation_upper (variance chi omega : ℝ)
    (hc : 0 < chi) (ho : 0 < omega)
    (hv : 1 / (4 * chi * omega) ≤ variance) :
    1 / (2 * chi * variance) ≤ 2 * omega := by
  have hd : 0 < 4 * chi * omega := by positivity
  have hpos : 0 < variance := lt_of_lt_of_le (by positivity) hv
  apply (div_le_iff₀ (by positivity : 0 < 2 * chi * variance)).mpr
  have h := (div_le_iff₀ hd).mp hv
  nlinarith

theorem protected_eigenvector {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    (s : Finset ι) (A : E →ₗ[ℝ] E) (V : ι → E →ₗ[ℝ] E)
    (n : ι → ℝ) (f : E) (lam : ℝ)
    (he : A f = lam • f) (hz : ∀ i ∈ s, V i f = 0) :
    A f + ∑ i ∈ s, n i • V i f = lam • f := by
  have hsum : (∑ i ∈ s, n i • V i f) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hz i hi, smul_zero]
  rw [hsum, add_zero, he]

theorem closed_wave_equation {E : Type*} [AddCommGroup E] [Module ℝ E]
    (D : E →ₗ[ℝ] E) (q p : E) (chi stiffness : ℝ)
    (hq : D q = (1 / chi) • p) (hp : D p = (-stiffness) • q) :
    D (D q) = (-(stiffness / chi)) • q := by
  rw [hq, map_smul, hp, smul_smul]
  congr 1
  ring

#print axioms averaged_covariance_bounds
#print axioms weighted_variance_identity
#print axioms gaussian_mixture_cumulant
#print axioms gaussian_mixture_cumulant_nonnegative
#print axioms spectral_probability_normalization
#print axioms resolvent_second_moment_bound
#print axioms spectral_low_tail
#print axioms spectral_high_tail
#print axioms spectral_annulus_bound
#print axioms half_weight_in_acoustic_band
#print axioms unweighted_band_fraction
#print axioms variational_excitation_upper
#print axioms protected_eigenvector
#print axioms closed_wave_equation

end
end UnifiedTheory.Audit.KFCausalEntangledAcoustic
