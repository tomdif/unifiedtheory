/-
  Audit/KFCausalCSpecRelativeScaleCocycle.lean   (Volume sector — relative-scale cocycle)

  Relative interval volumes define positive-real transition factors

        r_ij = (n_i / n_j)^(1/d)  =  tau_i / tau_j   (under the common-density law).

  These form an `R_{>0}`-torsor (the volume-sector analogue of the order sector's
  `S3`-torsor): reflexive, inverse, cocyclic, gauge-invariant under a common
  density change, with trivial exact loops and a common-factor reference change.

  LOOP DIAGNOSTIC.  Because `r` derived from a global count field is manifestly a
  coboundary (`r_ij = f_i/f_j`, `f_i = n_i^(1/d)`), every loop product
  `H_gamma = prod r_ij` is EXACTLY 1 (`relativeScale_loop_trivial`).  So a MEASURED
  `H_gamma != 1` (from independent edge-wise scale comparisons) is a falsifiable
  volume-consistency defect: it certifies that the edge scales do NOT come from one
  global scale field, i.e. some combination of sampling noise, curvature bias,
  density variation, or mesoscopic failure is present.  That is a concrete
  diagnostic, not another conditional inversion.

  SCOPE / grading.  Density calibration is eliminated only for RELATIVE geometry;
  absolute scale still needs a calibrated rho.  Poisson fluctuation itself is NOT
  handled here — only its deterministic propagation (`relativeScale_noisy_transition`).
  Angles are deliberately deferred: interval counts recover timelike lengths but not
  a Lorentzian polarization identity.

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalCSpecVolumeGauge

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecRelativeScaleCocycle

open UnifiedTheory.Audit.KFCausalCSpecVolumeSector
open UnifiedTheory.Audit.KFCausalCSpecVolumeGauge

/-- The relative-scale transition factor between two interval counts. -/
noncomputable def relScale (d : ℕ) (ni nj : ℝ) : ℝ := (ni / nj) ^ ((d : ℝ)⁻¹)

/-- **Reflexivity**: `r_ii = 1`. -/
theorem relativeScale_refl (d : ℕ) (ni : ℝ) (hi : 0 < ni) : relScale d ni ni = 1 := by
  unfold relScale; rw [div_self hi.ne', Real.one_rpow]

/-- **Inverse law**: `r_ij * r_ji = 1`. -/
theorem relativeScale_inv (d : ℕ) (ni nj : ℝ) (hi : 0 < ni) (hj : 0 < nj) :
    relScale d ni nj * relScale d nj ni = 1 := by
  have hi' : ni ≠ 0 := hi.ne'
  have hj' : nj ≠ 0 := hj.ne'
  unfold relScale
  rw [← Real.mul_rpow (div_nonneg hi.le hj.le) (div_nonneg hj.le hi.le),
    show ni / nj * (nj / ni) = 1 by field_simp, Real.one_rpow]

/-- **Cocycle**: `r_ij * r_jk = r_ik`. -/
theorem relativeScale_cocycle (d : ℕ) (ni nj nk : ℝ)
    (hi : 0 < ni) (hj : 0 < nj) (hk : 0 < nk) :
    relScale d ni nj * relScale d nj nk = relScale d ni nk := by
  have hj' : nj ≠ 0 := hj.ne'
  have hk' : nk ≠ 0 := hk.ne'
  unfold relScale
  rw [← Real.mul_rpow (div_nonneg hi.le hj.le) (div_nonneg hj.le hk.le),
    show ni / nj * (nj / nk) = ni / nk by field_simp]

/-- **Gauge invariance**: a common density change (common factor `c`) cancels. -/
theorem relativeScale_gaugeInvariant (d : ℕ) (c ni nj : ℝ) (hc : c ≠ 0) :
    relScale d (c * ni) (c * nj) = relScale d ni nj := by
  unfold relScale
  congr 1
  exact mul_div_mul_left ni nj hc

/-- **Trivial loop**: the exact triangle product is `1` (the cocycle is a coboundary,
so `H_gamma = 1` always for count-derived scales). -/
theorem relativeScale_loop_trivial (d : ℕ) (n0 n1 n2 : ℝ)
    (h0 : 0 < n0) (h1 : 0 < n1) (h2 : 0 < n2) :
    relScale d n0 n1 * relScale d n1 n2 * relScale d n2 n0 = 1 := by
  rw [relativeScale_cocycle d n0 n1 n2 h0 h1 h2, relativeScale_inv d n0 n2 h0 h2]

/-- **Reference change**: switching the reference diamond from `nref` to `nref'`
multiplies every reconstructed time by the SINGLE common factor `r_{ref,ref'}`,
independent of `i`. -/
theorem relativeScale_referenceChange (d : ℕ) (ni nref nref' : ℝ)
    (hi : 0 < ni) (hr : 0 < nref) (hr' : 0 < nref') :
    relScale d ni nref' = relScale d ni nref * relScale d nref nref' :=
  (relativeScale_cocycle d ni nref nref' hi hr hr').symm

/-- **Noisy transition**: with relative count errors, the transition factor is the
true ratio times an explicit error factor — the density still cancels. -/
theorem relativeScale_noisy_transition (I : LocalInterval)
    (τi τj δi δj ni nj : ℝ)
    (hti : 0 ≤ τi) (htj : 0 < τj) (hdi : 0 ≤ 1 + δi) (hdj : 0 < 1 + δj)
    (hni : ni = I.rho * I.C * τi ^ I.d * (1 + δi))
    (hnj : nj = I.rho * I.C * τj ^ I.d * (1 + δj)) :
    relScale I.d ni nj = (τi / τj) * ((1 + δi) / (1 + δj)) ^ ((I.d : ℝ)⁻¹) := by
  unfold relScale
  exact relative_scale_with_error I τi τj δi δj ni nj hti htj hdi hdj hni hnj

#print axioms relativeScale_refl
#print axioms relativeScale_inv
#print axioms relativeScale_cocycle
#print axioms relativeScale_gaugeInvariant
#print axioms relativeScale_loop_trivial
#print axioms relativeScale_referenceChange
#print axioms relativeScale_noisy_transition

end UnifiedTheory.Audit.KFCausalCSpecRelativeScaleCocycle
