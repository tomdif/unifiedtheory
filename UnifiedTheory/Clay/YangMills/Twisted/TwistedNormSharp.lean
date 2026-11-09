/- The top of the twisted transfer operator scales like one free Gaussian per link, at fixed `n`.

`norm_le_mass` gives `‖T‖ ≤ mass(β)^links`, and `norm_lower'` gives `mass(24β)^(2·links + sites) ≤ ‖T‖`. The exponents
differ, `7n³` against `3n³`. Here the lower exponent is `links · (1 + η)` with `η` as small as wanted:
* `potential_shift`: `V(v) ≤ (1 + θ) V(u) + 16 (1 + θ⁻¹) |u - v|²`, the twisted potential is quadratically stable.
* `jensen_partition`: `Z(s) ≤ Z(s')^(s/s')` for the partition function `Z(s) = ∫ exp(-s V)`, by Hölder.
* `norm_lower_sharp`: the gauge-invariant trial function `exp(-a β V)` gives
  `mass(c β)^links · (mass(16 s')^links)^η ≤ ‖T‖`, with `η = (1 + θ(a + 1/2))/(2a + 1 + θ(a + 1/2))`. Taking `θ = 1/a` and
  `a` large makes `η` small at the cost of the constant `c`, so `log ‖T‖ = -(1 + o(1)) · links · |log mass(β)|` as
  `β → ∞` at fixed `n`, up to the `η` that can be taken arbitrarily small.

This is a fixed-`n` statement about the top level only. It says nothing about the neutral level, and nothing uniform
in `n`. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedSemiclassical

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedNormSharp
noncomputable section
open MeasureTheory PeriodicLattice4 TwistedFlat TwistedStability TwistedSeams TwistedSliceLift
open WilsonTimeSlab WilsonSlabOperator TwistedTransfer TwistedLocalization TwistedFluxSector
open TwistedSemiclassical TwistedNormLower
open WilsonSingleLinkStaples (character)

variable (n : ℕ) [NeZero n]

local notation "μ'" => WilsonSlabOperator.measure n

/-- Squared link distance between two slices. -/
def sqDist (u v : Slice n) : ℝ := ∑ e, d (u e) (v e) ^ 2

theorem sqDist_continuous (u : Slice n) : Continuous (sqDist n u) := by
  unfold sqDist d
  fun_prop

theorem kinetic_eq (u v : Slice n) : kineticAction character 2 u v = sqDist n u v := by
  unfold kineticAction sqDist
  exact Finset.sum_congr rfl fun e _ => kinetic_term _ _

/-! ### Quadratic stability of the potential -/

theorem sq_shift (Dv Du S a b c e θ : ℝ) (hθ : 0 < θ) (hDv : 0 ≤ Dv) (hS0 : 0 ≤ S)
    (htri : Dv ≤ S + Du) (hS : S ≤ a + b + c + e) :
    Dv ^ 2 ≤ (1 + θ) * Du ^ 2 + 4 * (1 + θ⁻¹) * (a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2) := by
  have hι : 0 < θ⁻¹ := inv_pos.mpr hθ
  have hθι : θ * θ⁻¹ = 1 := mul_inv_cancel₀ hθ.ne'
  have h1 : Dv ^ 2 ≤ (S + Du) ^ 2 := pow_le_pow_left₀ hDv htri 2
  have h2 : 2 * Du * S ≤ θ * Du ^ 2 + θ⁻¹ * S ^ 2 := by
    have e : θ⁻¹ * (θ * Du - S) ^ 2 = θ * Du ^ 2 - 2 * Du * S + θ⁻¹ * S ^ 2 := by
      field_simp
      ring
    linarith only [mul_nonneg hι.le (sq_nonneg (θ * Du - S)), e]
  have h3 : S ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2) := by
    have := pow_le_pow_left₀ hS0 hS 2
    nlinarith only [this, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - e), sq_nonneg (b - c),
      sq_nonneg (b - e), sq_nonneg (c - e)]
  have h4 : (1 + θ⁻¹) * S ^ 2 ≤ (1 + θ⁻¹) * (4 * (a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2)) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  nlinarith only [h1, h2, h4]

theorem term_shift (θ : ℝ) (hθ : 0 < θ) (u v : Slice n) (x : SpatialVertex n) (p : SpatialPlane) :
    2 - spatialSign n x p * (character (spatialHolonomy v x p.1.1 p.1.2)).re ≤
      (1 + θ) * (2 - spatialSign n x p * (character (spatialHolonomy u x p.1.1 p.1.2)).re) +
        4 * (1 + θ⁻¹) * (d (u (x, p.1.1)) (v (x, p.1.1)) ^ 2 +
          d (u (spatialStep n x p.1.1, p.1.2)) (v (spatialStep n x p.1.1, p.1.2)) ^ 2 +
          d (u (spatialStep n x p.1.2, p.1.1)) (v (spatialStep n x p.1.2, p.1.1)) ^ 2 +
          d (u (x, p.1.2)) (v (x, p.1.2)) ^ 2) := by
  set t : Vertex n := Fin.cases 0 x with ht
  have hsp : sp n t = x := rfl
  have hv := potential_term_eq n v t p
  have hu := potential_term_eq n u t p
  rw [hsp] at hv hu
  rw [hv, hu]
  rcases p with ⟨⟨i, j⟩, hij⟩
  simp only
  unfold TwistedStability.defect
  have hf := four (lift n u t i.succ) (lift n u (step n t i.succ) j.succ)
    (lift n u (step n t j.succ) i.succ) (lift n u t j.succ)
    (lift n v t i.succ) (lift n v (step n t i.succ) j.succ)
    (lift n v (step n t j.succ) i.succ) (lift n v t j.succ)
  set Pu := lift n u t i.succ * lift n u (step n t i.succ) j.succ * (lift n u (step n t j.succ) i.succ)⁻¹ *
    (lift n u t j.succ)⁻¹ with hPu
  set Pv := lift n v t i.succ * lift n v (step n t i.succ) j.succ * (lift n v (step n t j.succ) i.succ)⁻¹ *
    (lift n v t j.succ)⁻¹ with hPv
  have htri := d_triangle Pv Pu (ω ^ twistExp i.succ j.succ t)
  rw [TwistedStability.d_comm Pv Pu] at htri
  simp only [lift_succ, sp_step_succ, hsp] at hf
  exact sq_shift _ _ _ _ _ _ _ θ hθ (d_nonneg _ _) (d_nonneg _ _) htri hf

/-- **The twisted potential is quadratically stable.** -/
theorem potential_shift (θ : ℝ) (hθ : 0 < θ) (u v : Slice n) :
    twistedPotential n v ≤ (1 + θ) * twistedPotential n u + 16 * (1 + θ⁻¹) * sqDist n u v := by
  let M : Fin 3 → ℝ := fun i => ∑ x, d (u (x, i)) (v (x, i)) ^ 2
  have hM (i j : Fin 3) : ∑ x, (d (u (x, i)) (v (x, i)) ^ 2 +
      d (u (spatialStep n x i, j)) (v (spatialStep n x i, j)) ^ 2 +
      d (u (spatialStep n x j, i)) (v (spatialStep n x j, i)) ^ 2 +
      d (u (x, j)) (v (x, j)) ^ 2) = 2 * M i + 2 * M j := by
    simp only [Finset.sum_add_distrib]
    rw [sum_spatialStep n (fun y => d (u (y, j)) (v (y, j)) ^ 2) i,
      sum_spatialStep n (fun y => d (u (y, i)) (v (y, i)) ^ 2) j]
    change M i + M j + M i + M j = _
    ring
  have hdist : sqDist n u v = M 0 + M 1 + M 2 := by
    unfold sqDist
    rw [Fintype.sum_prod_type, Finset.sum_comm, Fin.sum_univ_three]
  have hA : ∑ x : SpatialVertex n, ∑ p : SpatialPlane,
      (1 + θ) * (2 - spatialSign n x p * (character (spatialHolonomy u x p.1.1 p.1.2)).re) =
      (1 + θ) * twistedPotential n u := by
    unfold twistedPotential
    simp only [Finset.mul_sum]
  have hB : ∑ x : SpatialVertex n, ∑ p : SpatialPlane, 4 * (1 + θ⁻¹) *
      (d (u (x, p.1.1)) (v (x, p.1.1)) ^ 2 +
          d (u (spatialStep n x p.1.1, p.1.2)) (v (spatialStep n x p.1.1, p.1.2)) ^ 2 +
          d (u (spatialStep n x p.1.2, p.1.1)) (v (spatialStep n x p.1.2, p.1.1)) ^ 2 +
          d (u (x, p.1.2)) (v (x, p.1.2)) ^ 2) = 16 * (1 + θ⁻¹) * sqDist n u v := by
    rw [Finset.sum_comm]
    have hp : ∀ p : SpatialPlane, ∑ x : SpatialVertex n, 4 * (1 + θ⁻¹) *
        (d (u (x, p.1.1)) (v (x, p.1.1)) ^ 2 +
          d (u (spatialStep n x p.1.1, p.1.2)) (v (spatialStep n x p.1.1, p.1.2)) ^ 2 +
          d (u (spatialStep n x p.1.2, p.1.1)) (v (spatialStep n x p.1.2, p.1.1)) ^ 2 +
          d (u (x, p.1.2)) (v (x, p.1.2)) ^ 2) = 4 * (1 + θ⁻¹) * (2 * M p.1.1 + 2 * M p.1.2) := fun p => by
      rw [← Finset.mul_sum, hM]
    simp only [hp]
    refine (plane_sum (fun i j => 4 * (1 + θ⁻¹) * (2 * M i + 2 * M j))).trans ?_
    rw [hdist]
    ring
  have hle := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) =>
    Finset.sum_le_sum fun p (_ : p ∈ Finset.univ) => term_shift n θ hθ u v x p
  simp only [Finset.sum_add_distrib] at hle
  rw [hA, hB] at hle
  exact hle

/-! ### Gaussian integrals and the partition function -/

theorem gauss_translate (s : ℝ) (u : Slice n) :
    ∫ v, Real.exp (-s * sqDist n u v) ∂μ' = SU2GaussianMass.mass s ^ links n := by
  have h := integral_fintype_prod_eq_prod (ι := SpatialVertex n × Fin 3) (E := fun _ => Q)
    (fun e q => Real.exp (-s * d q (u e) ^ 2))
    (μ := fun _ => RegulatedGauge.compactHaar Q)
  have hp (v : Slice n) : Real.exp (-s * sqDist n u v) = ∏ e, Real.exp (-s * d (v e) (u e) ^ 2) := by
    rw [← Real.exp_sum, sqDist, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun e _ => by rw [TwistedStability.d_comm]
  simp only [hp]
  refine h.trans ?_
  simp only [gaussian_translate, Finset.prod_const, Finset.card_univ, links]

/-- The partition function of the twisted potential. -/
def Z (s : ℝ) : ℝ := ∫ u, Real.exp (-s * twistedPotential n u) ∂μ'

theorem expV_continuous (s : ℝ) : Continuous fun u : Slice n => Real.exp (-s * twistedPotential n u) :=
  Real.continuous_exp.comp (continuous_const.mul (TwistedSemiclassical.twistedPotential_continuous n))

theorem Z_pos (s : ℝ) : 0 < Z n s := by
  unfold Z
  have hc := expV_continuous n s
  have hle := integral_mono (integrable_const (Real.exp (-|s| * (12 * (n : ℝ) ^ 3)))) (ci n hc)
    (μ := μ') fun u => by
      apply Real.exp_le_exp.mpr
      have h1 := potential_le_card n u
      have h0 := TwistedSliceLift.potential_nonneg n u
      have : s * twistedPotential n u ≤ |s| * (12 * (n : ℝ) ^ 3) :=
        (le_abs_self s |> fun h => by nlinarith only [h, h0, h1, abs_nonneg s])
      linarith only [this]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hle
  exact (Real.exp_pos _).trans_le hle

theorem Z_lower (s : ℝ) (hs : 0 ≤ s) : SU2GaussianMass.mass (16 * s) ^ links n ≤ Z n s := by
  rw [← gauss_slice]
  refine integral_mono (ci n (Real.continuous_exp.comp (continuous_const.mul (dist_continuous n))))
    (ci n (expV_continuous n s)) fun u => ?_
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_left (potential_le n u) hs
  linarith only [this]

/-- **Jensen for the partition function.** `Z(s) ≤ Z(s')^(s/s')` for `0 < s < s'`, by Hölder. -/
theorem jensen_partition (s s' : ℝ) (hs : 0 < s) (hss : s < s') : Z n s ≤ Z n s' ^ (s / s') := by
  have hp : 1 < s' / s := (one_lt_div hs).mpr hss
  have hH := Real.HolderConjugate.conjExponent hp
  set f : Slice n → ℝ := fun u => Real.exp (-s * twistedPotential n u) with hf
  have hfc : Continuous f := expV_continuous n s
  have hmem (r : ENNReal) (g : Slice n → ℝ) (hg : Continuous g) : MemLp g r μ' :=
    hg.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hineq := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ') hH
    (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le)
    (Filter.Eventually.of_forall fun u => zero_le_one) (hmem _ f hfc) (hmem _ (fun _ => (1 : ℝ)) continuous_const)
  have hpow (u : Slice n) : f u ^ (s' / s) = Real.exp (-s' * twistedPotential n u) := by
    rw [hf, ← Real.exp_mul]
    congr 1
    field_simp
  have hZ' : ∫ u, f u ^ (s' / s) ∂μ' = Z n s' := by
    unfold Z
    exact integral_congr_ae (Filter.Eventually.of_forall hpow)
  have hone : (∫ _u : Slice n, (1 : ℝ) ^ Real.conjExponent (s' / s) ∂μ') ^ (1 / Real.conjExponent (s' / s)) = 1 := by
    simp
  have e : 1 / (s' / s) = s / s' := by field_simp
  rw [hone, mul_one, hZ', e] at hineq
  have hL : Z n s = ∫ u, f u * 1 ∂μ' := by
    simp only [mul_one]
    rfl
  rw [hL]
  exact hineq

/-- `Z(s') ≥ Z(s) · Z(s')^(1 - s/s')`. -/
theorem partition_ratio (s s' : ℝ) (hs : 0 < s) (hss : s < s') :
    Z n s * Z n s' ^ (1 - s / s') ≤ Z n s' := by
  have hZ := Z_pos n s'
  have hJ := jensen_partition n s s' hs hss
  calc Z n s * Z n s' ^ (1 - s / s') ≤ Z n s' ^ (s / s') * Z n s' ^ (1 - s / s') :=
        mul_le_mul_of_nonneg_right hJ (Real.rpow_nonneg hZ.le _)
    _ = Z n s' := by rw [← Real.rpow_add hZ]; simp

/-! ### The trial function -/

/-- The gauge-invariant trial function `exp(-a β V)`. -/
def trial (c : ℝ) : C(Slice n, ℝ) := ⟨fun u => Real.exp (-c * twistedPotential n u), expV_continuous n c⟩

theorem trial_gauge (c : ℝ) (k : SliceGauge n Q) (v : Slice n) : trial n c (gaugeSlice k v) = trial n c v := by
  change Real.exp (-c * twistedPotential n (gaugeSlice k v)) = Real.exp (-c * twistedPotential n v)
  rw [twistedPotential_gauge]

theorem trial_apply_kernel (β a θ : ℝ) (hβ : 0 < β) (ha : 0 < a) (hθ : 0 < θ) (u : Slice n) :
    SU2GaussianMass.mass (β * (1 + (a + 1 / 2) * (16 * (1 + θ⁻¹)))) ^ links n *
        Real.exp (-((2 * a + 1 + θ * (a + 1 / 2)) * β) * twistedPotential n u) ≤
      trial n (a * β) u * ∫ v, twistedKernel n β (u, v) * trial n (a * β) v ∂μ' := by
  set B := 16 * (1 + θ⁻¹) with hB
  set V := twistedPotential n with hV
  set c := β * (1 + (a + 1 / 2) * B) with hc
  rw [integral_kernel_invariant n β hβ.le u (trial n (a * β)) (trial_gauge n (a * β))]
  have hpt (v : Slice n) : Real.exp (-((a + 1 / 2) * (1 + θ) * β) * V u) * Real.exp (-c * sqDist n u v) ≤
      kinW n β u v * (wt n β v * trial n (a * β) v) := by
    have hs := potential_shift n θ hθ u v
    change _ ≤ Real.exp (-β * kineticAction character 2 u v) *
      (Real.exp (-(β / 2) * twistedPotential n v) * Real.exp (-(a * β) * twistedPotential n v))
    rw [kinetic_eq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hk : 0 ≤ (a + 1 / 2) * β := by positivity
    have := mul_le_mul_of_nonneg_left hs hk
    rw [hc]
    nlinarith only [this]
  have hint : ∫ v, Real.exp (-((a + 1 / 2) * (1 + θ) * β) * V u) * Real.exp (-c * sqDist n u v) ∂μ' ≤
      ∫ v, kinW n β u v * (wt n β v * trial n (a * β) v) ∂μ' :=
    integral_mono (ci n (continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul (sqDist_continuous n u)))))
      (ci n ((kinW_continuous n β u).mul ((wt_continuous n β).mul (trial n (a * β)).continuous))) hpt
  rw [integral_const_mul, gauss_translate] at hint
  calc SU2GaussianMass.mass c ^ links n * Real.exp (-((2 * a + 1 + θ * (a + 1 / 2)) * β) * V u)
      = trial n (a * β) u * (wt n β u *
          (Real.exp (-((a + 1 / 2) * (1 + θ) * β) * V u) * SU2GaussianMass.mass c ^ links n)) := by
        change _ = Real.exp (-(a * β) * V u) * (Real.exp (-(β / 2) * V u) * (Real.exp _ * _))
        have e : Real.exp (-((2 * a + 1 + θ * (a + 1 / 2)) * β) * V u) =
            Real.exp (-(a * β) * V u) * Real.exp (-(β / 2) * V u) *
              Real.exp (-((a + 1 / 2) * (1 + θ) * β) * V u) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        rw [e]
        ring
    _ ≤ trial n (a * β) u * (wt n β u * ∫ v, kinW n β u v * (wt n β v * trial n (a * β) v) ∂μ') := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left hint (Real.exp_pos _).le

/-- **The top of the transfer operator, with the free exponent up to `η`.** For `a, θ > 0`,
`mass(β (1 + (a + 1/2) 16 (1 + θ⁻¹)))^links · (mass(16 s')^links)^η ≤ ‖T‖` with `s' = (2a + 1 + θ(a + 1/2)) β` and
`η = (1 + θ(a + 1/2))/(2a + 1 + θ(a + 1/2))`. With `norm_le_mass` this pins `log ‖T‖` to `links · log mass` up to the
factor `1 + η`, and `η → 0` as `a → ∞` with `θ = 1/a`. -/
theorem norm_lower_sharp (β a θ : ℝ) (hβ : 0 < β) (ha : 0 < a) (hθ : 0 < θ) :
    SU2GaussianMass.mass (β * (1 + (a + 1 / 2) * (16 * (1 + θ⁻¹)))) ^ links n *
        (SU2GaussianMass.mass (16 * ((2 * a + 1 + θ * (a + 1 / 2)) * β)) ^ links n) ^
          ((1 + θ * (a + 1 / 2)) / (2 * a + 1 + θ * (a + 1 / 2))) ≤ ‖TwistedTransfer.transfer n β‖ := by
  set s := 2 * a * β with hsd
  set s' := (2 * a + 1 + θ * (a + 1 / 2)) * β with hs'd
  set M := SU2GaussianMass.mass (β * (1 + (a + 1 / 2) * (16 * (1 + θ⁻¹)))) ^ links n with hM
  have hs : 0 < s := by positivity
  have hss : s < s' := by
    have : 0 < (1 + θ * (a + 1 / 2)) * β := by positivity
    rw [hsd, hs'd]
    nlinarith only [this]
  have hs'0 : 0 < s' := hs.trans hss
  have hη : (1 + θ * (a + 1 / 2)) / (2 * a + 1 + θ * (a + 1 / 2)) = 1 - s / s' := by
    rw [hsd, hs'd]
    have h1 : 0 < 2 * a + 1 + θ * (a + 1 / 2) := by positivity
    field_simp
    ring
  set h := trial n (a * β) with hh
  have hI : Integrable (fun u => h u * ∫ v, twistedKernel n β (u, v) * h v ∂μ') μ' := by
    refine (pairFn_integrable n β h).integral_prod_left.congr (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [pairFn]
    ring
  have hlow : M * Z n s' ≤ ∫ u, h u * (∫ v, twistedKernel n β (u, v) * h v ∂μ') ∂μ' := by
    rw [Z, ← integral_const_mul]
    exact integral_mono (ci n (continuous_const.mul (expV_continuous n s'))) hI
      fun u => trial_apply_kernel n β a θ hβ ha hθ u
  have hsq : ∫ u, h u ^ 2 ∂μ' = Z n s := by
    unfold Z
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    change Real.exp (-(a * β) * twistedPotential n u) ^ 2 = _
    rw [sq, ← Real.exp_add]
    congr 1
    rw [hsd]
    ring
  have hform := form_le_norm n β h
  rw [hsq] at hform
  have hrat := partition_ratio n s s' hs hss
  have hZl := Z_lower n s' hs'0.le
  have hZs := Z_pos n s
  have hZs' := Z_pos n s'
  have hm0 : 0 ≤ SU2GaussianMass.mass (16 * s') ^ links n := pow_nonneg (SU2GaussianMass.mass_pos _).le _
  have he : 0 ≤ 1 - s / s' := by
    have : s / s' < 1 := (div_lt_one hs'0).mpr hss
    linarith only [this]
  have hpow : (SU2GaussianMass.mass (16 * s') ^ links n) ^ (1 - s / s') ≤ Z n s' ^ (1 - s / s') :=
    Real.rpow_le_rpow hm0 hZl he
  have hM0 : 0 ≤ M := pow_nonneg (SU2GaussianMass.mass_pos _).le _
  rw [hη]
  have key : M * (SU2GaussianMass.mass (16 * s') ^ links n) ^ (1 - s / s') * Z n s ≤
      ‖TwistedTransfer.transfer n β‖ * Z n s := by
    calc M * (SU2GaussianMass.mass (16 * s') ^ links n) ^ (1 - s / s') * Z n s
        ≤ M * (Z n s * Z n s' ^ (1 - s / s')) := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hM0
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left hpow hZs.le
      _ ≤ M * Z n s' := mul_le_mul_of_nonneg_left hrat hM0
      _ ≤ _ := hlow.trans hform
  exact le_of_mul_le_mul_right key hZs

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedNormSharp
