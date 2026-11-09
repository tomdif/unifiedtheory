/- A quantitative Gaussian approximation for an actual aligned SU(2) star integral.
Four staples equal one and two rotate in one fixed quaternion plane. This module
concerns the literal Haar integral; it makes no full-lattice exterior-realization
or subsequent interacting renormalization claim. -/
import UnifiedTheory.Clay.YangMills.SU2ConditionalInfluence
import UnifiedTheory.Clay.YangMills.SU2WilsonLocalEquipartition
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SU2AlignedGaussianApproximation
noncomputable section
open MeasureTheory Set SU2QuaternionEquivalence SU2HaarTilt SU2HaarCovariance SU2InducedAction
open SU2ConditionalInfluence
open scoped Quaternion RealInnerProductSpace

/-- The exact radial free energy of six Wilson star plaquettes. -/
def radialPotential (β r : ℝ) : ℝ := 12 * β + potential β (r • (1 : ℍ))

theorem radialPotential_hasDerivAt (β r : ℝ) (hr : 0 ≤ r) :
    HasDerivAt (radialPotential β) (-(2 * β * axisMean (2 * β * r))) r := by
  have h := (potential_direction_hasDerivAt β 0 1 r).const_add (12 * β)
  simpa only [radialPotential, zero_add, radial_mean β r hr] using h

/-- The exact Haar correction to the classical minimum is controlled
without an asymptotic premise. -/
theorem radial_correction_bound (β r : ℝ) (hβ : 0 < β) (hr : 0 < r) (hr₆ : r ≤ 6) :
    |radialPotential β r - radialPotential β 6 - 2 * β * (6 - r)| ≤
      3 * (6 - r) / (2 * r) := by
  have hd (s : ℝ) (hs : s ∈ Icc r 6) :
      HasDerivWithinAt (fun t => radialPotential β t + 2 * β * t)
        (2 * β * (1 - axisMean (2 * β * s))) (Icc r 6) s := by
    have h := (radialPotential_hasDerivAt β s (hr.le.trans hs.1)).add
      ((hasDerivAt_id s).const_mul (2 * β))
    convert h.hasDerivWithinAt using 1
    ring
  have hb (s : ℝ) (hs : s ∈ Ico r 6) :
      ‖2 * β * (1 - axisMean (2 * β * s))‖ ≤ 3 / (2 * r) := by
    have hsp : 0 < s := hr.trans_le hs.1
    have hk : 0 < 2 * β * s := by positivity
    have he := SU2WilsonLocalEquipartition.axisExcess_bounds (2 * β * s) hk.le
    rw [axisExcess_identity] at he
    have hp : 0 ≤ 1 - axisMean (2 * β * s) :=
      nonneg_of_mul_nonneg_right he.1 hk
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hp)]
    have hc := axis_concentration hk
    have hc' := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 2 * β)
    have hdiv : 2 * β * (3 / (2 * (2 * β * s))) = 3 / (2 * s) := by
      field_simp
    rw [hdiv] at hc'
    exact hc'.trans (div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith [hs.1]))
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb 6 ⟨hr₆, le_rfl⟩
  rw [Real.norm_eq_abs] at h
  have he : radialPotential β r - radialPotential β 6 - 2 * β * (6 - r) =
      -((radialPotential β 6 + 2 * β * 6) - (radialPotential β r + 2 * β * r)) := by ring
  rw [he, abs_neg]
  convert h using 1
  ring

/-- Global fourth-order cosine error, derived from Taylor's theorem. -/
theorem cosine_remainder (t : ℝ) : |Real.cos t - (1 - t ^ 2 / 2)| ≤ t ^ 4 / 24 := by
  have hpos (x : ℝ) (hx : 0 < x) : |Real.cos x - (1 - x ^ 2 / 2)| ≤ x ^ 4 / 24 := by
    obtain ⟨y, hy, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
      (f := Real.cos) (n := 3) hx Real.contDiff_cos.contDiffOn
    have hw (k : ℕ) : iteratedDerivWithin k Real.cos (Icc 0 x) 0 =
        iteratedDeriv k Real.cos 0 :=
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hx)
        Real.contDiff_cos.contDiffAt ⟨le_rfl, hx.le⟩
    have ht : taylorWithinEval Real.cos 3 (Icc 0 x) 0 x = 1 - x ^ 2 / 2 := by
      rw [taylorWithinEval_succ Real.cos 2, taylorWithinEval_succ Real.cos 1,
        taylorWithinEval_succ Real.cos 0]
      simp only [taylor_within_zero_eval, hw]
      norm_num [iteratedDeriv_succ, Real.deriv_cos, Real.deriv_sin]
      ring
    rw [ht] at he
    have hfour : iteratedDeriv 4 Real.cos y = Real.cos y := by
      simp
    rw [hfour] at he
    norm_num only [sub_zero, Nat.factorial, Nat.cast_ofNat] at he
    rw [he, abs_div, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 24)]
    have hc := mul_le_mul_of_nonneg_right (Real.abs_cos_le_one y) (pow_nonneg (abs_nonneg x) 4)
    rw [one_mul] at hc
    simpa only [← abs_pow, abs_of_nonneg (pow_nonneg hx.le 4)] using
      div_le_div_of_nonneg_right hc (by norm_num : (0 : ℝ) ≤ 24)
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have h := hpos (-t) (neg_pos.mpr ht)
    simpa only [Real.cos_neg, even_two.neg_pow, Even.neg_pow (by decide : Even 4)] using h
  · norm_num
  · exact hpos t ht

/-- An actual unit staple in a fixed quaternion plane. -/
def rotor (t : ℝ) : ℍ := Real.cos t • (1 : ℍ) + Real.sin t • imaginaryUnit

theorem rotor_norm (t : ℝ) : ‖rotor t‖ = 1 := rotating_staple_norm t

/-- Four identity staples and two rotating unit staples. -/
def alignedSum (t s : ℝ) : ℍ := (4 : ℝ) • (1 : ℍ) + rotor t + rotor s

def alignedRadius (t s : ℝ) : ℝ := ‖alignedSum t s‖

def starPotential (β t s : ℝ) : ℝ := 12 * β + potential β (alignedSum t s)

/-- The defined potential is the literal six-staple Wilson Haar integral. -/
theorem starPotential_integral (β t s : ℝ) :
    starPotential β t s = -Real.log (∫ q : UnitQuaternion,
      Real.exp (-β * (12 - 2 * ⟪(q : ℍ), alignedSum t s⟫)) ∂haar) := by
  have he (q : UnitQuaternion) :
      Real.exp (-β * (12 - 2 * ⟪(q : ℍ), alignedSum t s⟫)) =
        Real.exp (-(12 * β)) * tiltWeight β (alignedSum t s) q := by
    unfold tiltWeight
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [integral_const_mul]
  change starPotential β t s = -Real.log (Real.exp (-(12 * β)) *
    tiltPartition β (alignedSum t s))
  rw [Real.log_mul (Real.exp_ne_zero _) (tiltPartition_pos β (alignedSum t s)).ne',
    Real.log_exp]
  unfold starPotential potential tiltPartition
  ring

theorem starPotential_radial (β t s : ℝ) :
    starPotential β t s = radialPotential β (alignedRadius t s) := by
  simp only [starPotential, radialPotential, potential, tiltPartition_radial, norm_smul,
    Real.norm_eq_abs, norm_one, mul_one, alignedRadius, abs_of_nonneg (norm_nonneg _)]

theorem radius_le_six (t s : ℝ) : alignedRadius t s ≤ 6 := by
  have h := (norm_add_le ((4 : ℝ) • (1 : ℍ) + rotor t) (rotor s)).trans
    (add_le_add (norm_add_le ((4 : ℝ) • (1 : ℍ)) (rotor t)) le_rfl)
  norm_num only [norm_smul, Real.norm_eq_abs, norm_one, mul_one,
    rotor_norm] at h
  exact h

theorem radius_defect_bound (t s : ℝ) :
    0 ≤ 6 - alignedRadius t s ∧ 6 - alignedRadius t s ≤ (t ^ 2 + s ^ 2) / 2 := by
  have hre := real_inner_le_norm (alignedSum t s) (1 : ℍ)
  have ht := Real.one_sub_sq_div_two_le_cos (x := t)
  have hs := Real.one_sub_sq_div_two_le_cos (x := s)
  simp only [Quaternion.inner_def, star_one, mul_one, norm_one] at hre
  have he : (alignedSum t s).re = 4 + Real.cos t + Real.cos s := by
    simp [alignedSum, rotor, imaginaryUnit]
  rw [he] at hre
  exact ⟨sub_nonneg.mpr (radius_le_six t s), by dsimp [alignedRadius]; linarith⟩

theorem radius_square (t s : ℝ) :
    alignedRadius t s ^ 2 = 18 + 8 * Real.cos t + 8 * Real.cos s + 2 * Real.cos (t - s) := by
  change ‖alignedSum t s‖ ^ 2 = _
  rw [pow_two, ← Quaternion.normSq_eq_norm_mul_self]
  simp [alignedSum, rotor, imaginaryUnit, Quaternion.normSq_def, Real.cos_sub]
  nlinarith [Real.cos_sq_add_sin_sq t, Real.cos_sq_add_sin_sq s]

/-- Elementary geometric error before the Haar fluctuation correction. -/
theorem radius_quadratic_error (t s : ℝ) :
    |(36 - alignedRadius t s ^ 2) - (5 * t ^ 2 + 5 * s ^ 2 - 2 * t * s)| ≤
      (t ^ 4 + s ^ 4) / 3 + (t - s) ^ 4 / 12 := by
  have ht := abs_le.mp (cosine_remainder t)
  have hs := abs_le.mp (cosine_remainder s)
  have hts := abs_le.mp (cosine_remainder (t - s))
  rw [radius_square]
  apply abs_le.mpr
  constructor <;> nlinarith [ht.1, ht.2, hs.1, hs.2, hts.1, hts.2]

/-- The aligned vacuum has radius six exactly. -/
theorem radius_zero : alignedRadius 0 0 = 6 := by
  norm_num [alignedRadius, alignedSum, rotor, imaginaryUnit]
  rw [show (4 : ℝ) • (1 : ℍ) + 1 + 1 = (6 : ℝ) • (1 : ℍ) by module]
  norm_num

/-- An explicit actual one-fiber Gaussian remainder on bounded fluctuation coordinates.
The coupling rescaling removes the raw curvature growth; it does not suppress the quadratic term. -/
theorem scaled_star_error (β R x y : ℝ) (hβ : max 1 (R ^ 2) ≤ β)
    (hx : |x| ≤ R) (hy : |y| ≤ R) :
    |starPotential β (x / Real.sqrt β) (y / Real.sqrt β) - starPotential β 0 0 -
      (5 * x ^ 2 + 5 * y ^ 2 - 2 * x * y) / 6| ≤
      (R ^ 4 / 2 + 3 * R ^ 2 / 10) / β := by
  have hb₁ : 1 ≤ β := (le_max_left _ _).trans hβ
  have hb : 0 < β := by linarith
  have hbR : R ^ 2 ≤ β := (le_max_right _ _).trans hβ
  have hR : 0 ≤ R := (abs_nonneg x).trans hx
  have hroot : 0 < Real.sqrt β := Real.sqrt_pos.mpr hb
  have hroot2 : Real.sqrt β ^ 2 = β := Real.sq_sqrt hb.le
  let t := x / Real.sqrt β
  let s := y / Real.sqrt β
  let z := R ^ 2 / β
  let r := alignedRadius t s
  have hz : 0 ≤ z := div_nonneg (sq_nonneg _) hb.le
  have hz₁ : z ≤ 1 := (div_le_one hb).mpr hbR
  have hx2 : x ^ 2 ≤ R ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg x) hx 2
    simpa only [sq_abs] using h
  have hy2 : y ^ 2 ≤ R ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg y) hy 2
    simpa only [sq_abs] using h
  have ht2 : t ^ 2 ≤ z := by
    dsimp only [t, z]
    rw [div_pow, hroot2]
    exact div_le_div_of_nonneg_right hx2 hb.le
  have hs2 : s ^ 2 ≤ z := by
    dsimp only [s, z]
    rw [div_pow, hroot2]
    exact div_le_div_of_nonneg_right hy2 hb.le
  have hts2 : (t - s) ^ 2 ≤ 4 * z := by nlinarith [sq_nonneg (t + s)]
  have ht4 : t ^ 4 ≤ z ^ 2 := by
    have h := pow_le_pow_left₀ (sq_nonneg t) ht2 2
    nlinarith
  have hs4 : s ^ 4 ≤ z ^ 2 := by
    have h := pow_le_pow_left₀ (sq_nonneg s) hs2 2
    nlinarith
  have hts4 : (t - s) ^ 4 ≤ 16 * z ^ 2 := by
    have h := pow_le_pow_left₀ (sq_nonneg (t - s)) hts2 2
    nlinarith
  have hd := radius_defect_bound t s
  have hδ : 0 ≤ 6 - r ∧ 6 - r ≤ z := ⟨hd.1, by dsimp [r]; linarith [hd.2]⟩
  have hr : 5 ≤ r := by linarith
  have hr₆ : r ≤ 6 := by linarith [hδ.1]
  have hδ2 : (6 - r) ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ hδ.1 hδ.2 2
  have hgeom := radius_quadratic_error t s
  have hgeom' : |(36 - r ^ 2) - (5 * t ^ 2 + 5 * s ^ 2 - 2 * t * s)| ≤ 2 * z ^ 2 := by
    apply hgeom.trans
    nlinarith
  have hclass : |2 * β * (6 - r) - β * (5 * t ^ 2 + 5 * s ^ 2 - 2 * t * s) / 6| ≤
      β * z ^ 2 / 2 := by
    have he : 2 * β * (6 - r) - β * (5 * t ^ 2 + 5 * s ^ 2 - 2 * t * s) / 6 =
        β / 6 * (((36 - r ^ 2) - (5 * t ^ 2 + 5 * s ^ 2 - 2 * t * s)) + (6 - r) ^ 2) := by
      ring
    rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ β / 6)]
    calc
      _ ≤ β / 6 * (|(36 - r ^ 2) - (5 * t ^ 2 + 5 * s ^ 2 - 2 * t * s)| +
          |(6 - r) ^ 2|) := mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)
      _ ≤ β / 6 * (2 * z ^ 2 + z ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add hgeom' (by simpa only [abs_of_nonneg (sq_nonneg (6 - r))] using hδ2)
      _ = _ := by ring
  have hhaar := radial_correction_bound β r hb (by linarith) hr₆
  have hhaar' : |radialPotential β r - radialPotential β 6 - 2 * β * (6 - r)| ≤
      3 * z / 10 := by
    apply hhaar.trans
    apply (div_le_iff₀ (by linarith : 0 < 2 * r)).mpr
    have hmul := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 3 * z / 5)
    nlinarith [hδ.2]
  have htotal : |radialPotential β r - radialPotential β 6 -
      β * (5 * t ^ 2 + 5 * s ^ 2 - 2 * t * s) / 6| ≤ β * z ^ 2 / 2 + 3 * z / 10 := by
    have he : radialPotential β r - radialPotential β 6 -
        β * (5 * t ^ 2 + 5 * s ^ 2 - 2 * t * s) / 6 =
        (radialPotential β r - radialPotential β 6 - 2 * β * (6 - r)) +
        (2 * β * (6 - r) - β * (5 * t ^ 2 + 5 * s ^ 2 - 2 * t * s) / 6) := by ring
    rw [he]
    exact (abs_add_le _ _).trans (by linarith [add_le_add hhaar' hclass])
  have hquad : β * (5 * t ^ 2 + 5 * s ^ 2 - 2 * t * s) / 6 =
      (5 * x ^ 2 + 5 * y ^ 2 - 2 * x * y) / 6 := by
    dsimp only [t, s]
    nth_rw 1 [← hroot2]
    field_simp [hroot.ne']
  have hconst : β * z ^ 2 / 2 + 3 * z / 10 =
      (R ^ 4 / 2 + 3 * R ^ 2 / 10) / β := by
    dsimp only [z]
    field_simp [hb.ne']
  rw [hquad, hconst] at htotal
  simpa only [starPotential_radial, radius_zero] using htotal

/-- At each fixed bounded fluctuation coordinate, the actual vacuum-subtracted
star free energy converges to its nonzero quadratic profile. -/
theorem scaled_star_tendsto (x y : ℝ) :
    Filter.Tendsto (fun β : ℝ =>
      starPotential β (x / Real.sqrt β) (y / Real.sqrt β) - starPotential β 0 0)
      Filter.atTop (nhds ((5 * x ^ 2 + 5 * y ^ 2 - 2 * x * y) / 6)) := by
  let R := max |x| |y|
  have hbound : ∀ᶠ β : ℝ in Filter.atTop,
      |starPotential β (x / Real.sqrt β) (y / Real.sqrt β) - starPotential β 0 0 -
        (5 * x ^ 2 + 5 * y ^ 2 - 2 * x * y) / 6| ≤
        (R ^ 4 / 2 + 3 * R ^ 2 / 10) / β := by
    filter_upwards [Filter.eventually_ge_atTop (max 1 (R ^ 2))] with β hβ
    exact scaled_star_error β R x y hβ (le_max_left _ _) (le_max_right _ _)
  have hlim : Filter.Tendsto (fun β : ℝ => (R ^ 4 / 2 + 3 * R ^ 2 / 10) / β)
      Filter.atTop (nhds 0) := by
    exact Filter.tendsto_id.const_div_atTop _
  have h := squeeze_zero' (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) hbound hlim
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using h)

end
end UnifiedTheory.Clay.YangMills.SU2AlignedGaussianApproximation
