import UnifiedTheory.Audit.KFCausalConformal4DConnection

/-!
The explicit metric density integrated on the conformal coordinate diamond,
and its controlled proper-time expansion with curvature computed from the
connection. The region-to-geodesic-diamond identification is not asserted.
The curved BDG kernel also needs a separate measure correction and a uniform
remainder/localization argument; none is replaced by this benchmark.
-/

namespace UnifiedTheory.Audit.KFCausalConformal4DCurvatureExpansion

noncomputable section
open Real
open KFCausalConformal4DDiamondBenchmark
open KFCausalCSpecRSSConformal

theorem omega_positive (att spatial : ℝ) (p : Point) (ht : 0 ≤ att) (hs : 0 ≤ spatial) :
    0 < omega att spatial p := by
  unfold omega
  positivity

theorem omega_patch_positive (att spatial T lam : ℝ) (p : Point)
    (hT : 0 ≤ T) (hlam : 0 < lam) (hTlam : T ≤ lam / 2)
    (hatt : |att| ≤ 1 / lam^2) (hs : |spatial| ≤ 1 / lam^2)
    (htime : p 0 ^ 2 ≤ T^2) (hspace : p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 ≤ T^2) :
    (3 : ℝ) / 4 ≤ omega att spatial p := by
  have hq : T^2 / lam^2 ≤ (1 : ℝ) / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [pow_le_pow_left₀ hT hTlam 2]
  have ht1 := mul_le_mul_of_nonneg_right (abs_le.mp hatt).1 (sq_nonneg (p 0))
  have hs1 := mul_le_mul_of_nonneg_right (abs_le.mp hs).1
    (show 0 ≤ p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 by positivity)
  have ht2 := mul_le_mul_of_nonneg_left htime (show 0 ≤ 1 / lam^2 by positivity)
  have hs2 := mul_le_mul_of_nonneg_left hspace (show 0 ≤ 1 / lam^2 by positivity)
  have he : (1 / lam^2) * T^2 = T^2 / lam^2 := by ring
  rw [he] at ht2 hs2
  unfold omega
  nlinarith

theorem spherical_patch_positive (att spatial T lam t b : ℝ)
    (hT : 0 ≤ T) (hlam : 0 < lam) (hTlam : T ≤ lam / 2)
    (hatt : |att| ≤ 1 / lam^2) (hs : |spatial| ≤ 1 / lam^2)
    (ht : 0 ≤ t) (htT : t ≤ T) (hb : 0 ≤ b) (hbt : b ≤ T-t) :
    (3 : ℝ) / 4 ≤ omega att spatial ![t,b,0,0] := by
  apply omega_patch_positive att spatial T lam ![t,b,0,0] hT hlam hTlam hatt hs
  · simp only [Matrix.cons_val_zero]
    nlinarith
  · change b^2 + (0 : ℝ)^2 + 0^2 ≤ T^2
    norm_num
    nlinarith

theorem metric_spherical_volume (att spatial T : ℝ) :
    2 * (∫ t in (0 : ℝ)..T, ∫ b in (0 : ℝ)..T-t,
      4 * π * b^2 * Real.sqrt |Matrix.det (metric att spatial ![t,b,0,0])|) =
      Vg att spatial T := by
  simp_rw [metric_volume_density]
  unfold Vg
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  apply intervalIntegral.integral_congr
  intro b hb
  simp [omega]

theorem central_proper_time (att spatial T : ℝ) (ht : 0 ≤ att) :
    (∫ t in -T..T, Real.sqrt (-metric att spatial ![t,0,0,0] 0 0)) = taug att T := by
  unfold taug
  apply intervalIntegral.integral_congr
  intro t ht'
  have ho : 0 ≤ 1 + att * t^2 / 2 := by positivity
  simpa [metric, omega, eta, KFCausalConformal4DDiamondBenchmark.sign] using Real.sqrt_sq ho

theorem central_proper_time_patch (att spatial T lam : ℝ)
    (hT : 0 ≤ T) (hlam : 0 < lam) (hTlam : T ≤ lam / 2)
    (hatt : |att| ≤ 1 / lam^2) (hs : |spatial| ≤ 1 / lam^2) :
    (∫ t in -T..T, Real.sqrt (-metric att spatial ![t,0,0,0] 0 0)) = taug att T := by
  unfold taug
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : -T ≤ t ∧ t ≤ T := by
    simpa only [Set.uIcc_of_le (by linarith : -T ≤ T), Set.mem_Icc] using ht
  have ht2 : t^2 ≤ T^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht'.2) (show 0 ≤ T+t by linarith)]
  have ho := omega_patch_positive att spatial T lam ![t,0,0,0] hT hlam hTlam hatt hs
    (by simpa using ht2) (by simp; positivity)
  simp [omega] at ho
  simpa [metric, omega, eta, KFCausalConformal4DDiamondBenchmark.sign] using Real.sqrt_sq (show 0 ≤ 1+att*t^2/2 by linarith)

theorem proper_time_lower (att T lam : ℝ) (hT : 0 < T) (hlam : 0 < lam)
    (hatt : |att| ≤ 1 / lam^2) (hTlam : T ≤ lam / 2) : T ≤ taug att T := by
  have hq : T^2 / lam^2 ≤ (1 : ℝ) / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [pow_le_pow_left₀ hT.le hTlam 2]
  have ha := (abs_le.mp hatt).1
  have hb := mul_le_mul_of_nonneg_right ha (sq_nonneg T)
  have hc : -(1 / lam^2) * T^2 = -(T^2 / lam^2) := by ring
  rw [hc] at hb
  have hd : -(1 : ℝ)/4 ≤ att * T^2 := by linarith
  have he := mul_le_mul_of_nonneg_right hd hT.le
  rw [taug_eval]
  nlinarith

theorem geometric_remainder_bound (att spatial T lam : ℝ)
    (hT : 0 < T) (hlam : 0 < lam)
    (hatt : |att| ≤ 1 / lam^2) (hs : |spatial| ≤ 1 / lam^2) (hTlam : T ≤ lam / 2) :
    |Vg att spatial T / ((π/24) * taug att T ^ 4) - 1 -
      (-scalar att spatial / 180 + ricci att spatial 0 0 / 30) * taug att T ^ 2| ≤
        1557 * taug att T ^ 4 / lam^4 := by
  rw [← geometric_volume_coefficient]
  have htau := proper_time_lower att T lam hT hlam hatt hTlam
  have htaup : 0 < taug att T := lt_of_lt_of_le hT htau
  have hN := Nlin_poly_bound att spatial T lam hT hlam hatt hs hTlam
  have hQ := Qrem_bound att spatial T lam hT hlam hatt hs hTlam
  have hQ' : |24/π * Qrem att spatial T| ≤ 1536*T^4*(T^2/lam^2)^2 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 24/π)]
    calc (24/π) * |Qrem att spatial T|
        ≤ (24/π) * (64*π*(T^2/lam^2)^2*T^4) :=
          mul_le_mul_of_nonneg_left hQ (by positivity)
      _ = _ := by field_simp; ring
  have hnum : |(24/π * Vlin att spatial T - taug att T ^ 4 -
      (3*spatial-2*att)/15 * taug att T ^ 6) + 24/π * Qrem att spatial T| ≤
      1557*T^4*(T^2/lam^2)^2 := by
    exact (abs_add_le _ _).trans (by linarith)
  have heq : Vg att spatial T / ((π/24) * taug att T ^ 4) - 1 -
      (3*spatial-2*att)/15 * taug att T ^ 2 =
      ((24/π * Vlin att spatial T - taug att T ^ 4 -
        (3*spatial-2*att)/15 * taug att T ^ 6) + 24/π * Qrem att spatial T) /
        taug att T ^ 4 := by
    rw [Vg_split]
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos (pow_pos htaup 4)]
  calc _ ≤ (1557*T^4*(T^2/lam^2)^2) / taug att T ^ 4 :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = 1557*T^8 / (lam^4 * taug att T ^ 4) := by field_simp
    _ ≤ 1557*taug att T ^ 8 / (lam^4 * taug att T ^ 4) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT.le htau 8) (by positivity)
    _ = 1557*taug att T ^ 4 / lam^4 := by field_simp

theorem temporal_curvature_benchmark (c : ℝ) :
    ricci (2*c) 0 0 0 = -6*c ∧ scalar (2*c) 0 = 12*c ∧
      (-scalar (2*c) 0 / 180 + ricci (2*c) 0 0 0 / 30) = -4*c/15 := by
  rw [ricci_time, scalar_curvature]
  constructor
  · ring
  constructor <;> ring

#print axioms omega_positive
#print axioms omega_patch_positive
#print axioms spherical_patch_positive
#print axioms metric_spherical_volume
#print axioms central_proper_time
#print axioms central_proper_time_patch
#print axioms proper_time_lower
#print axioms geometric_remainder_bound
#print axioms temporal_curvature_benchmark

end

end UnifiedTheory.Audit.KFCausalConformal4DCurvatureExpansion
