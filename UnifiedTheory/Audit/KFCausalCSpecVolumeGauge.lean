/-
  Audit/KFCausalCSpecVolumeGauge.lean   (Volume sector — density gauge and relative scale)

  `scale_recovered` recovers `tau` only after FIXING the density `rho`.  Without a
  calibrated density the absolute scale is unidentifiable:

        rho * C * tau^d  =  (a^d rho) * C * (tau/a)^d ,

  so order + cardinality fix `tau` only in units of `rho^{-1/d}`.  This unit
  formalizes that gauge and the density-FREE quantity that survives it — the ratio
  of proper times — together with explicit multiplicative stability under a
  bounded relative count error `(1+delta)`.

  This cleanly decomposes the remaining wall:

        Poisson fluctuation  +  curvature bias  +  density calibration
              ==>  quantitative scale recovery.

  The gauge and the count-error stability (this file) are tractable; the count
  error `delta` itself (Poisson) and the curvature/mesoscopic certification remain
  the Hauptvermutung-facing obstruction, NOT closed here.

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalCSpecVolumeSector

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecVolumeGauge

open UnifiedTheory.Audit.KFCausalCSpecVolumeSector

/-! ## The absolute-scale gauge -/

/-- **Absolute scale is a gauge.**  The count `rho*C*tau^d` is invariant under the
rescaling `(rho, tau) → (a^d*rho, tau/a)`.  So count data alone cannot distinguish
`(rho, tau)` from `(a^d rho, tau/a)`: absolute proper time is only defined in units
of `rho^{-1/d}`. -/
theorem absolute_scale_gauge (d : ℕ) (rho C tau a : ℝ) (ha : a ≠ 0) :
    (a ^ d * rho) * C * (tau / a) ^ d = rho * C * tau ^ d := by
  have ha' : (a : ℝ) ^ d ≠ 0 := pow_ne_zero d ha
  rw [div_pow]; field_simp

/-! ## Density-free relative scale -/

/-- **Relative scale is recovered without the density.**  For two diamonds sharing
`rho, C, d`, the ratio of proper times is read off the ratio of counts, the density
cancelling: `(n1/n2)^(1/d) = tau1/tau2`. -/
theorem relative_scale_recovered (I : LocalInterval) (tau1 tau2 : ℝ)
    (ht1 : 0 ≤ tau1) (ht2 : 0 < tau2) :
    (volumeLaw I tau1 / volumeLaw I tau2) ^ ((I.d : ℝ)⁻¹) = tau1 / tau2 := by
  have hstep : volumeLaw I tau1 / volumeLaw I tau2 = (tau1 / tau2) ^ I.d := by
    simp only [volumeLaw, div_pow]
    field_simp [I.hrho.ne', I.hC.ne', ht2.ne']
  rw [hstep, ← Real.rpow_natCast (tau1 / tau2) I.d, ← Real.rpow_mul (div_nonneg ht1 ht2.le),
    mul_inv_cancel₀ (by exact_mod_cast I.hd.ne'), Real.rpow_one]

/-! ## Count-error stability of the estimator -/

/-- **Estimator under a relative count error.**  If `n = rho*C*tau^d*(1+delta)`,
the proper-time estimator returns `tau * (1+delta)^(1/d)`. -/
theorem count_estimator_recovers (I : LocalInterval) (tau delta n : ℝ)
    (htau : 0 ≤ tau) (hδ : 0 ≤ 1 + delta)
    (hn : n = I.rho * I.C * tau ^ I.d * (1 + delta)) :
    (n / (I.rho * I.C)) ^ ((I.d : ℝ)⁻¹) = tau * (1 + delta) ^ ((I.d : ℝ)⁻¹) := by
  have hrc : (0:ℝ) < I.rho * I.C := mul_pos I.hrho I.hC
  have hnorm : n / (I.rho * I.C) = tau ^ I.d * (1 + delta) := by
    rw [hn]; field_simp [I.hrho.ne', I.hC.ne']
  rw [hnorm, Real.mul_rpow (pow_nonneg htau I.d) hδ, ← Real.rpow_natCast tau I.d,
    ← Real.rpow_mul htau, mul_inv_cancel₀ (by exact_mod_cast I.hd.ne'), Real.rpow_one]

/-- **Multiplicative stability.**  A relative count error `|delta| ≤ ε < 1` gives an
explicit multiplicative band on the recovered scale:
`(1-ε)^(1/d) ≤ tau_hat/tau ≤ (1+ε)^(1/d)`. -/
theorem count_estimator_stable (d : ℕ) (delta ε : ℝ) (hε : ε < 1) (hδ : |delta| ≤ ε) :
    (1 - ε) ^ ((d : ℝ)⁻¹) ≤ (1 + delta) ^ ((d : ℝ)⁻¹)
    ∧ (1 + delta) ^ ((d : ℝ)⁻¹) ≤ (1 + ε) ^ ((d : ℝ)⁻¹) := by
  have hz : (0:ℝ) ≤ (d : ℝ)⁻¹ := by positivity
  have h1 : -ε ≤ delta := (abs_le.mp hδ).1
  have h2 : delta ≤ ε := (abs_le.mp hδ).2
  exact ⟨Real.rpow_le_rpow (by linarith) (by linarith) hz,
    Real.rpow_le_rpow (by linarith) (by linarith) hz⟩

/-! ## Relative scale is density-free even with errors -/

/-- **Density cancels even under count errors.**  With counts `n_i = rho*C*tau_i^d*
(1+delta_i)`, the recovered ratio is the true ratio times the error factor
`((1+delta1)/(1+delta2))^(1/d)` — the density is gone regardless of the errors. -/
theorem relative_scale_with_error (I : LocalInterval) (tau1 tau2 delta1 delta2 n1 n2 : ℝ)
    (ht1 : 0 ≤ tau1) (ht2 : 0 < tau2) (hd1 : 0 ≤ 1 + delta1) (hd2 : 0 < 1 + delta2)
    (hn1 : n1 = I.rho * I.C * tau1 ^ I.d * (1 + delta1))
    (hn2 : n2 = I.rho * I.C * tau2 ^ I.d * (1 + delta2)) :
    (n1 / n2) ^ ((I.d : ℝ)⁻¹)
      = (tau1 / tau2) * ((1 + delta1) / (1 + delta2)) ^ ((I.d : ℝ)⁻¹) := by
  have hrc : (0:ℝ) < I.rho * I.C := mul_pos I.hrho I.hC
  have hstep : n1 / n2 = (tau1 / tau2) ^ I.d * ((1 + delta1) / (1 + delta2)) := by
    rw [hn1, hn2, div_pow]; field_simp [I.hrho.ne', I.hC.ne', ht2.ne', hd2.ne']
  rw [hstep, Real.mul_rpow (pow_nonneg (div_nonneg ht1 ht2.le) I.d) (div_nonneg hd1 hd2.le),
    ← Real.rpow_natCast (tau1 / tau2) I.d, ← Real.rpow_mul (div_nonneg ht1 ht2.le),
    mul_inv_cancel₀ (by exact_mod_cast I.hd.ne'), Real.rpow_one]

#print axioms absolute_scale_gauge
#print axioms relative_scale_recovered
#print axioms count_estimator_recovers
#print axioms count_estimator_stable
#print axioms relative_scale_with_error

end UnifiedTheory.Audit.KFCausalCSpecVolumeGauge
