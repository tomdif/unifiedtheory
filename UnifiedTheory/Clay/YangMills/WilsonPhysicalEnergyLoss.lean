/- Positivity of the constructed full Wilson operator turns its Dirichlet
energy into a lower bound on actual physical variance loss. -/
import UnifiedTheory.Clay.YangMills.WilsonLocalBlockCoercivity
import UnifiedTheory.Clay.YangMills.WilsonHighFieldReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPhysicalEnergyLoss
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonPhysicalVariance WilsonGroundHeatBath WilsonHighFieldDecay WilsonHighFieldReduction
open WilsonDissipationIteration WilsonSlabContraction ContinuousBoundaryMoments
open scoped InnerProductSpace

/-- Positivity is essential here; symmetry and norm contraction alone do
not imply this estimate. -/
theorem positive_contraction_square {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (A : H →L[ℂ] H) (hA : A.IsPositive)
    (hn : ∀ x, ‖A x‖ ≤ ‖x‖) (x : H) :
    ‖A x‖^2 ≤ (inner ℂ x (A x)).re := by
  have hp := hA.re_inner_nonneg_right (x-A x)
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right,
    ← hA.inner_left_eq_inner_right x (A x)] at hp
  simp only [map_sub, inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow] at hp
  change 0 ≤ (inner ℂ x (A x)).re-‖A x‖^2-
    (‖A x‖^2-(inner ℂ (A x) (A (A x))).re) at hp
  have hb : (inner ℂ (A x) (A (A x))).re ≤ ‖A x‖^2 := by
    calc
      _ ≤ ‖inner ℂ (A x) (A (A x))‖ := Complex.re_le_norm _
      _ ≤ ‖A x‖*‖A (A x)‖ := norm_inner_le_norm _ _
      _ ≤ ‖A x‖*‖A x‖ := mul_le_mul_of_nonneg_left (hn (A x)) (norm_nonneg _)
      _ = _ := by ring
  linarith

variable (n : ℕ) [NeZero n]

theorem normalized_positive (β : ℝ) (hβ : 0 ≤ β) : (normalized n β).IsPositive := by
  refine ⟨normalized_symmetric n β, ?_⟩
  intro x
  change 0 ≤ (inner ℂ ((‖transfer n β‖⁻¹ : ℝ) • transfer n β x) x).re
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_real_left, Complex.smul_re]
  exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
    ((WilsonSlabPositiveOperator.transfer_positive n β hβ).re_inner_nonneg_left x)

theorem normalized_norm_le (β : ℝ) (hβ : 0 ≤ β) (x : Hilbert n) :
    ‖normalized n β x‖ ≤ ‖x‖ := by
  have hp := (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1
  simp only [normalized, ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hp.le)]
  calc
    _ ≤ ‖transfer n β‖⁻¹*(‖transfer n β‖*‖x‖) :=
      mul_le_mul_of_nonneg_left ((transfer n β).le_opNorm x) (inv_nonneg.mpr hp.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]

theorem weighted_embedding_pairing (β : ℝ) (hβ : 0 ≤ β) (f g : C(Slice n, ℝ)) :
    (inner ℂ (embed (measure n) (f*ground n β hβ))
      (embed (measure n) (g*ground n β hβ))).re = pairing n β hβ f g := by
  rw [ContinuousBoundaryMoments.embed, ContinuousBoundaryMoments.embed, ContinuousMap.inner_toLp]
  change (∫ u, ((g u*ground n β hβ u : ℝ) : ℂ)*
    starRingEnd ℂ ((f u*ground n β hβ u : ℝ) : ℂ) ∂measure n).re = _
  simp only [Complex.conj_ofReal, ← Complex.ofReal_mul,
    integral_complex_ofReal, Complex.ofReal_re]
  rw [pairing, groundLaw, GroundStateDirichlet.stationary_integral _ _
    (ground n β hβ).continuous]
  apply integral_congr_ae
  filter_upwards with u
  ring

theorem weighted_embedding_mass (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    ‖embed (measure n) (f*ground n β hβ)‖^2 = mass n β hβ f := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  change (inner ℂ (embed (measure n) (f*ground n β hβ))
    (embed (measure n) (f*ground n β hβ))).re = _
  rw [weighted_embedding_pairing, pairing_self]

/-- The positivity used here is proved for the full operator and transported
only on physical observables, where raw and full steps agree. -/
theorem mass_step_le_pairing (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hf : ∀ h u, f (gaugeSlice h u) = f u) :
    mass n β hβ (step n β hβ f) ≤ pairing n β hβ f (step n β hβ f) := by
  have hh := positive_contraction_square (normalized n β) (normalized_positive n β hβ)
    (normalized_norm_le n β hβ) (embed (measure n) (f*ground n β hβ))
  rw [← step_embedding n β hβ f hf, weighted_embedding_mass, weighted_embedding_pairing] at hh
  exact hh

theorem transferEnergy_identity (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hf : ∀ h u, f (gaugeSlice h u) = f u) :
    WilsonHeatBathComparison.transferEnergy n β hβ f =
      mass n β hβ f-pairing n β hβ f (step n β hβ f) := by
  rw [WilsonHeatBathComparison.transferEnergy_eq_dirichlet, GroundStateDirichlet.dirichlet]
  have hm : GroundStateDirichlet.normSquared (measure n) (ground n β hβ) f =
      mass n β hβ f := by
    rw [mass, groundLaw, GroundStateDirichlet.stationary_integral _ _ (ground n β hβ).continuous]
    rfl
  rw [hm]
  congr 1
  have hi : Integrable (fun z : Slice n × Slice n =>
      GroundStateDirichlet.edgeDensity (kernelMap n β) (ground n β hβ) ‖transfer n β‖ z *
        f z.1*f z.2) ((WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n)) :=
    CompactDensityEntropy.continuous_integrable _ _
      (((GroundStateDirichlet.edgeDensity_continuous (kernelMap n β) (kernelMap n β).continuous
        (ground n β hβ) (ground n β hβ).continuous ‖transfer n β‖).mul
          (f.continuous.comp continuous_fst)).mul (f.continuous.comp continuous_snd))
  rw [GroundStateDirichlet.pairing, integral_prod _ hi]
  rw [pairing, groundLaw, GroundStateDirichlet.stationary_integral _ _ (ground n β hβ).continuous]
  simp_rw [step_full n β hβ f hf, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  apply integral_congr_ae
  filter_upwards with v
  have hh := GroundStateDirichlet.detailed_balance (kernelMap n β) (ground n β hβ)
    ‖transfer n β‖ (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1 u v
  change (ground n β hβ u)^2*transition n β hβ u v = _ at hh
  rw [← hh]
  ring

theorem transferEnergy_le_loss (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hf : ∀ h u, f (gaugeSlice h u) = f u) :
    WilsonHeatBathComparison.transferEnergy n β hβ f ≤ loss n β hβ f := by
  rw [transferEnergy_identity n β hβ f hf, loss_mass]
  exact sub_le_sub_left (mass_step_le_pairing n β hβ f hf) _

end
end UnifiedTheory.Clay.YangMills.WilsonPhysicalEnergyLoss
