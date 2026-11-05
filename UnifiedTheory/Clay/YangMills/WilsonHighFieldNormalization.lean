/- Quantitative normalization for high-spatial-energy dynamics, using the
actual Wilson top eigenvalue and the existing polynomial cap estimate. -/
import UnifiedTheory.Clay.YangMills.WilsonGroundSlabEnergy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonHighFieldNormalization
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonGroundSlabEnergy WilsonEnergyDensity
open UnitaryHaarNeighborhood Filter
open scoped Topology

variable (n : ℕ) [NeZero n]

def links : ℝ := Fintype.card (SpatialVertex n × Fin 3)

theorem links_pos : 0 < links n := by unfold links; positivity

theorem links_ge_one : 1 ≤ links n := by
  unfold links
  exact_mod_cast (show 1 ≤ Fintype.card (SpatialVertex n × Fin 3) from Fintype.card_pos)

theorem log_top_lower (β : ℝ) (hβ : 0 < β) :
    -2*β*links n*envelope β ≤ Real.log ‖transfer n β‖ := by
  let K := grid β
  have hK : 0 < K := grid_pos β
  have hl := top_cap_lower n β hβ.le K hK
  have hp := pow_pos (massLower_pos (Fin 2) K) (7*Fintype.card (SpatialVertex n))
  have hh := Real.log_le_log (mul_pos hp (Real.exp_pos _)) hl
  rw [Real.log_mul hp.ne' (Real.exp_ne_zero _), Real.log_pow, Real.log_exp] at hh
  have hm : Real.log (massLower (Fin 2) K) = -8*Real.log ((2*K+1 : ℕ) : ℝ) := by
    simp only [massLower, Fintype.card_fin, one_div, Real.log_inv, Real.log_pow]
    norm_num
  have ht : squaredTolerance (Fin 2) K = 1568/(K : ℝ)^2 := by
    rw [squaredTolerance_formula]
    norm_num
  rw [hm, ht] at hh
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hh
  have hg : 1568/(K : ℝ)^2+(28/(3*β))*Real.log ((2*K+1 : ℕ) : ℝ) ≤ envelope β := by
    unfold envelope
    apply add_le_add
    · exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (pow_le_pow_left₀ hβ.le (beta_le_grid β) 2)
    · exact mul_le_mul_of_nonneg_left (grid_log_le β hβ) (by positivity)
  have hgm := mul_le_mul_of_nonneg_left hg
    (show 0 ≤ 6*(Fintype.card (SpatialVertex n) : ℝ)*β by positivity)
  have he : (6*(Fintype.card (SpatialVertex n) : ℝ)*β)*
      (1568/(K : ℝ)^2+(28/(3*β))*Real.log ((2*K+1 : ℕ) : ℝ)) =
      β*(6*(Fintype.card (SpatialVertex n) : ℝ)*(1568/(K : ℝ)^2))+
        56*(Fintype.card (SpatialVertex n) : ℝ)*Real.log ((2*K+1 : ℕ) : ℝ) := by
    field_simp [hβ.ne', (Nat.cast_ne_zero.mpr hK.ne' : (K : ℝ) ≠ 0)]
    ring
  rw [he] at hgm
  unfold links
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
  nlinarith [hh, hgm]

theorem top_lower (β : ℝ) (hβ : 0 < β) :
    Real.exp (-2*β*links n*envelope β) ≤ ‖transfer n β‖ := by
  have h := Real.exp_le_exp.mpr (log_top_lower n β hβ)
  rwa [Real.exp_log (PositiveKernelGroundState.transfer_top_eigenvector n β hβ.le).1] at h

def rate (β r : ℝ) : ℝ := Real.exp (-β*links n*(r-4 * envelope β))

theorem normalized_factor (β r : ℝ) (hβ : 0 < β) :
    Real.exp (-β*(r*links n))/‖transfer n β‖^2 ≤ rate n β r := by
  have hl := pow_le_pow_left₀ (Real.exp_pos _).le (top_lower n β hβ) 2
  have he : (Real.exp (-2*β*links n*envelope β))^2 =
      Real.exp (-4*β*links n*envelope β) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he] at hl
  apply (div_le_iff₀ (sq_pos_of_pos
    (PositiveKernelGroundState.transfer_top_eigenvector n β hβ.le).1)).mpr
  have h := mul_le_mul_of_nonneg_left hl (Real.exp_pos (-β*links n*(r-4 * envelope β))).le
  unfold rate
  apply le_trans _ h
  rw [← Real.exp_add]
  apply le_of_eq
  congr 1
  ring

theorem rate_uniform (β r : ℝ) (hβ : 0 ≤ β) (hr : 0 ≤ r)
    (he : 4 * envelope β ≤ r / 2) : rate n β r ≤ Real.exp (-β*r / 2) := by
  unfold rate
  apply Real.exp_le_exp.mpr
  have h1 := mul_le_mul_of_nonneg_left (show r / 2 ≤ r-4 * envelope β by linarith)
    (mul_nonneg hβ (links_pos n).le)
  have h2 := mul_le_mul_of_nonneg_left (links_ge_one n) (mul_nonneg hβ hr)
  nlinarith

omit n [NeZero n] in
theorem eventually_small_price (r : ℝ) (hr : 0 < r) :
    ∀ᶠ β : ℝ in atTop, 0 < β ∧ 4 * envelope β ≤ r / 2 := by
  have h := (WilsonGroundSlabEnergy.envelope_tendsto.const_mul 4).eventually
    (eventually_lt_nhds (show 4*(0 : ℝ) < r / 2 by linarith))
  filter_upwards [eventually_gt_atTop (0 : ℝ), h] with β hβ he
  exact ⟨hβ,he.le⟩

omit n [NeZero n] in
theorem uniform_rate_tendsto (r : ℝ) (hr : 0 < r) :
    Tendsto (fun β : ℝ => Real.exp (-β*r / 2)) atTop (𝓝 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0 : ℝ) (r / 2) (half_pos hr)
  simpa only [Real.rpow_zero, one_mul, show (fun β : ℝ => -(r / 2)*β) =
    (fun β : ℝ => -β*r / 2) by funext β; ring] using h

end
end UnifiedTheory.Clay.YangMills.WilsonHighFieldNormalization
