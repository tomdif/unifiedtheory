/- A finite-difference ground-amplitude identity and a bound on weighted
logarithmic gains. Interior-dependent square weights are charged to their
own source energies; no invariance of the weighted ground law is assumed. -/
import UnifiedTheory.Clay.YangMills.CompactDensityEntropy
import Mathlib.MeasureTheory.Group.Integral

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.CompactRotationIdentity
noncomputable section
open MeasureTheory CompactDensityEntropy

variable {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]

def sourceEnergy (g f : C(X, ℝ)) (q : X) : ℝ :=
  ∫ u, (g u)^2*(f (q*u)-f u)^2 ∂μ

def mixedEnergy (g f : C(X, ℝ)) (q : X) : ℝ :=
  ∫ u, g u*g (q*u)*(f (q*u)-f u)^2 ∂μ

def amplitudeEnergy (g f : C(X, ℝ)) (q : X) : ℝ :=
  ∫ u, (g (q*u)*f (q*u)-g u*f u)^2 ∂μ

omit [IsTopologicalGroup X] [CompactSpace X] [BorelSpace X]
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] in
theorem sourceEnergy_nonneg (g f : C(X, ℝ)) (q : X) : 0 ≤ sourceEnergy μ g f q :=
  integral_nonneg (fun _u => mul_nonneg (sq_nonneg _) (sq_nonneg _))

omit [IsTopologicalGroup X] [CompactSpace X] [BorelSpace X]
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] in
theorem amplitudeEnergy_nonneg (g f : C(X, ℝ)) (q : X) : 0 ≤ amplitudeEnergy μ g f q :=
  integral_nonneg (fun _u => sq_nonneg _)

/-- Exact identity before dropping the nonnegative ground-amplitude energy. -/
theorem identity (g f : C(X, ℝ)) (q : X) :
    (∫ u, (f u)^2*g u*(g (q*u)+g (q⁻¹*u)-2*g u) ∂μ) +
      amplitudeEnergy μ g f q = mixedEnergy μ g f q := by
  let C := fun u : X => g u*g (q*u)*(f (q*u)-f u)^2
  let A := fun u : X => (g (q*u)*f (q*u)-g u*f u)^2
  let V := fun u : X => (f u)^2*g u*(g (q*u)+g (q⁻¹*u)-2*g u)
  let H := fun u : X => (g u*f u)^2
  let K := fun u : X => g u*g (q⁻¹*u)*(f u)^2
  have hC : Integrable C μ := continuous_integrable μ _ (by dsimp [C]; fun_prop)
  have hA : Integrable A μ := continuous_integrable μ _ (by dsimp [A]; fun_prop)
  have hV : Integrable V μ := continuous_integrable μ _ (by dsimp [V]; fun_prop)
  have hH : Integrable H μ := continuous_integrable μ _ (by dsimp [H]; fun_prop)
  have hHq : Integrable (fun u => H (q*u)) μ :=
    continuous_integrable μ _ (by dsimp [H]; fun_prop)
  have hK : Integrable K μ := continuous_integrable μ _ (by dsimp [K]; fun_prop)
  have hKq : Integrable (fun u => K (q*u)) μ :=
    continuous_integrable μ _ (by dsimp [K]; fun_prop)
  have hzero : (∫ u, C u-A u-V u ∂μ) = 0 := by
    have he (u : X) : C u-A u-V u = (K (q*u)-K u)-(H (q*u)-H u) := by
      dsimp [C, A, V, H, K]
      rw [inv_mul_cancel_left]
      ring
    simp_rw [he]
    have hsub := integral_sub (hKq.sub hK) (hHq.sub hH)
    have hk := integral_sub hKq hK
    have hh := integral_sub hHq hH
    simp only [Pi.sub_apply] at hsub hk hh
    rw [hsub, hk, hh, integral_mul_left_eq_self K q, integral_mul_left_eq_self H q]
    ring
  have hsub := integral_sub (hC.sub hA) hV
  have hca := integral_sub hC hA
  simp only [Pi.sub_apply] at hsub hca
  rw [hsub, hca] at hzero
  change mixedEnergy μ g f q-amplitudeEnergy μ g f q-
    (∫ u, (f u)^2*g u*(g (q*u)+g (q⁻¹*u)-2*g u) ∂μ) = 0 at hzero
  linarith

/-- Haar change of variables turns the shifted density into the inverse source energy. -/
theorem mixed_le_symmetric (g f : C(X, ℝ)) (q : X) :
    mixedEnergy μ g f q ≤ (sourceEnergy μ g f q+sourceEnergy μ g f q⁻¹)/2 := by
  have hp : Integrable (fun u => (g u)^2*(f (q*u)-f u)^2) μ :=
    continuous_integrable μ _ (by fun_prop)
  have hm : Integrable (fun u => (g (q*u))^2*(f (q*u)-f u)^2) μ :=
    continuous_integrable μ _ (by fun_prop)
  have h := integral_mono
    (continuous_integrable μ (fun u => 2*(g u*g (q*u)*(f (q*u)-f u)^2)) (by fun_prop))
    (hp.add hm) (fun u => by
      simp only [Pi.add_apply]
      have ht := mul_nonneg (sq_nonneg (g u-g (q*u))) (sq_nonneg (f (q*u)-f u))
      nlinarith)
  have hs := integral_add hp hm
  simp only [Pi.add_apply] at h hs
  rw [integral_const_mul, hs] at h
  have he : (∫ u, (g (q*u))^2*(f (q*u)-f u)^2 ∂μ) = sourceEnergy μ g f q⁻¹ := by
    have hh := integral_mul_left_eq_self (μ := μ)
      (fun u : X => (g u)^2*(f (q⁻¹*u)-f u)^2) q
    calc
      _ = ∫ u, (g (q*u))^2*(f u-f (q*u))^2 ∂μ := by
        apply integral_congr_ae
        filter_upwards with u
        rw [sub_sq_comm]
      _ = _ := by simpa only [inv_mul_cancel_left, sourceEnergy] using hh
  rw [he] at h
  change 2*mixedEnergy μ g f q ≤ sourceEnergy μ g f q+sourceEnergy μ g f q⁻¹ at h
  linarith

omit μ [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] in
theorem scalar_log_gain (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a^2*(Real.log b-Real.log a) ≤ a*(b-a) := by
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hb ha))
    (sq_nonneg a)
  rw [Real.log_div hb.ne' ha.ne'] at h
  have he : a^2*(b/a-1) = a*(b-a) := by field_simp
  rwa [he] at h

/-- Arbitrary continuous square weights, with their own finite-difference energy cost. -/
theorem weighted_log_le_energy (g f : C(X, ℝ)) (hg : ∀ u, 0 < g u) (q : X) :
    (∫ u, (g u)^2*(f u)^2*
      (Real.log (g (q*u))+Real.log (g (q⁻¹*u))-2*Real.log (g u)) ∂μ) +
      amplitudeEnergy μ g f q ≤
        (sourceEnergy μ g f q+sourceEnergy μ g f q⁻¹)/2 := by
  have hlog : Continuous (fun u : X => Real.log (g u)) :=
    g.continuous.log (fun u => (hg u).ne')
  have hl : Continuous (fun u : X => (g u)^2*(f u)^2*
      (Real.log (g (q*u))+Real.log (g (q⁻¹*u))-2*Real.log (g u))) := by
    exact ((g.continuous.pow 2).mul (f.continuous.pow 2)).mul
      (((hlog.comp (f := fun u : X => q*u) (continuous_const.mul continuous_id)).add
        (hlog.comp (f := fun u : X => q⁻¹*u) (continuous_const.mul continuous_id))).sub
          (continuous_const.mul hlog))
  have h := integral_mono (continuous_integrable μ _ hl)
    (continuous_integrable μ (fun u => (f u)^2*g u*(g (q*u)+g (q⁻¹*u)-2*g u))
      (by fun_prop)) (fun u => by
        have hp := mul_le_mul_of_nonneg_left (scalar_log_gain (g u) (g (q*u)) (hg u) (hg _))
          (sq_nonneg (f u))
        have hm := mul_le_mul_of_nonneg_left (scalar_log_gain (g u) (g (q⁻¹*u)) (hg u) (hg _))
          (sq_nonneg (f u))
        nlinarith)
  have hi := identity μ g f q
  have hm := mixed_le_symmetric μ g f q
  linarith

end
end UnifiedTheory.Clay.YangMills.CompactRotationIdentity
