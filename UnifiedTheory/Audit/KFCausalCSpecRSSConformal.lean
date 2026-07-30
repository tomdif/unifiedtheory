/-
  Audit/KFCausalCSpecRSSConformal.lean
  — THE RSS EXPANSION, DERIVED (conformally flat sector)

  The last cited geometric input of the quantitative-Hauptvermutung chain was
  the Roy–Sinha–Surya/Gibbons–Solodukhin small-diamond volume expansion.  This
  file DERIVES it, with explicit constants, for the conformally flat sector:
  metrics `g = Ω²η` with radial quadratic conformal factor
  `Ω = 1 + a_tt t²/2 + a_s |x|²/2`.  Conformal maps preserve light cones, so
  the causal diamond is the flat diamond, its 4-volume is `∫ Ω⁴` (spherical
  reduction), and the proper time of the axis is `∫ Ω dt` — everything is an
  explicit 1D iterated integral.

  1.  `taug_eval`, `Vlin_eval`:  exact evaluations.
  2.  `rss_expansion_conformal`:  THE EXPANSION —
        Vg/((π/24)τ⁴) − 1 = c₁τ² + rem,  c₁ = (3a_s − 2a_tt)/15,
        |c₁| ≤ (1/3)/λ²,  |rem| ≤ 9·τ⁴/λ⁴
      for |a_tt|, |a_s| ≤ 1/λ², 0 < T ≤ λ/2 — exactly the `hexp`, `hc₁`,
      `hrem` inputs of `smallDiamond_volumeFaithful`, now theorems.
  3.  `gs_coefficients`:  c₁ = −R/180 + R₀₀/30 — the Gibbons–Solodukhin 4D
      coefficients, derived from the diamond moment integrals.
  4.  `rss_certifies_smallDiamond`:  |Vg/((π/24)τ⁴) − 1| ≤ (28/3)·τ²/λ²,
      the volume sector's `β`-certificate, derivation all the way down.

  Zero sorry.  Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalCSpecCurvatureVolumeBound

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory intervalIntegral Real

namespace UnifiedTheory.Audit.KFCausalCSpecRSSConformal

/-- The diamond 4-volume of `g = Ω²η`, `Ω = 1 + a_tt t²/2 + a_s b²/2`, in
spherical reduction (conformal maps preserve the causal structure, so the
region is the flat diamond and `dV_g = Ω⁴·4πb² db dt`, t-symmetrized). -/
noncomputable def Vg (att as T : ℝ) : ℝ :=
  2 * ∫ t in (0:ℝ)..T, ∫ b in (0:ℝ)..(T-t),
    4*π*b^2 * (1 + att*t^2/2 + as*b^2/2)^4

/-- The linearized volume. -/
noncomputable def Vlin (att as T : ℝ) : ℝ :=
  2 * ∫ t in (0:ℝ)..T, ∫ b in (0:ℝ)..(T-t),
    4*π*b^2 * (1 + 4*(att*t^2/2 + as*b^2/2))

/-- The axis proper time `∫ Ω dt` between the tips. -/
noncomputable def taug (att T : ℝ) : ℝ := ∫ t in (-T)..T, (1 + att*t^2/2)

/-! ## Exact evaluations -/

theorem taug_eval (att T : ℝ) : taug att T = 2*T + att*T^3/3 := by
  unfold taug
  have hF : ∀ t ∈ Set.uIcc (-T) T,
      HasDerivAt (fun x : ℝ => x + att/6*x^3) (1 + att*t^2/2) t := by
    intro t _
    have h2 := (hasDerivAt_id t).add ((hasDerivAt_pow 3 t).const_mul (att/6))
    have h3 : (1:ℝ) + att/6*(↑3*t^(3-1)) = 1 + att*t^2/2 := by
      push_cast
      ring
    exact h3 ▸ h2
  rw [integral_eq_sub_of_hasDerivAt hF
    ((Continuous.intervalIntegrable (by fun_prop) _ _))]
  ring

theorem J3 (T : ℝ) : ∫ t in (0:ℝ)..T, (T-t)^3 = T^4/4 := by
  have hF : ∀ t ∈ Set.uIcc (0:ℝ) T,
      HasDerivAt (fun x : ℝ => -((T-x)^4/4)) ((T-t)^3) t := by
    intro t _
    have h1 : HasDerivAt (fun x : ℝ => T - x) (-1) t :=
      (hasDerivAt_id t).const_sub T
    have h2 := ((h1.pow 4).div_const 4).neg
    have h3 : -(↑4*(T-t)^(4-1)*(-1)/4) = (T-t)^3 := by
      push_cast
      ring
    exact h3 ▸ h2
  rw [integral_eq_sub_of_hasDerivAt hF
    ((Continuous.intervalIntegrable (by fun_prop) _ _))]
  ring

theorem J5 (T : ℝ) : ∫ t in (0:ℝ)..T, (T-t)^5 = T^6/6 := by
  have hF : ∀ t ∈ Set.uIcc (0:ℝ) T,
      HasDerivAt (fun x : ℝ => -((T-x)^6/6)) ((T-t)^5) t := by
    intro t _
    have h1 : HasDerivAt (fun x : ℝ => T - x) (-1) t :=
      (hasDerivAt_id t).const_sub T
    have h2 := ((h1.pow 6).div_const 6).neg
    have h3 : -(↑6*(T-t)^(6-1)*(-1)/6) = (T-t)^5 := by
      push_cast
      ring
    exact h3 ▸ h2
  rw [integral_eq_sub_of_hasDerivAt hF
    ((Continuous.intervalIntegrable (by fun_prop) _ _))]
  ring

theorem J23 (T : ℝ) : ∫ t in (0:ℝ)..T, t^2*(T-t)^3 = T^6/60 := by
  have hF : ∀ t ∈ Set.uIcc (0:ℝ) T,
      HasDerivAt
        (fun x : ℝ => T^3/3*x^3 - 3*T^2/4*x^4 + 3*T/5*x^5 - 1/6*x^6)
        (t^2*(T-t)^3) t := by
    intro t _
    have h2 := ((((hasDerivAt_pow 3 t).const_mul (T^3/3)).sub
      ((hasDerivAt_pow 4 t).const_mul (3*T^2/4))).add
      ((hasDerivAt_pow 5 t).const_mul (3*T/5))).sub
      ((hasDerivAt_pow 6 t).const_mul (1/6))
    have h3 : T^3/3*(↑3*t^(3-1)) - 3*T^2/4*(↑4*t^(4-1))
        + 3*T/5*(↑5*t^(5-1)) - 1/6*(↑6*t^(6-1)) = t^2*(T-t)^3 := by
      push_cast
      ring
    exact h3 ▸ h2
  rw [integral_eq_sub_of_hasDerivAt hF
    ((Continuous.intervalIntegrable (by fun_prop) _ _))]
  ring

/-- Inner (radial) integral of the linearized integrand, exact. -/
theorem inner_lin_eval (att as t s : ℝ) :
    (∫ b in (0:ℝ)..s, 4*π*b^2 * (1 + 4*(att*t^2/2 + as*b^2/2)))
      = 4*π/3*(1+2*att*t^2)*s^3 + 8*π/5*as*s^5 := by
  have hF : ∀ b ∈ Set.uIcc (0:ℝ) s,
      HasDerivAt
        (fun x : ℝ => 4*π*(1+2*att*t^2)/3*x^3 + 8*π*as/5*x^5)
        (4*π*b^2 * (1 + 4*(att*t^2/2 + as*b^2/2))) b := by
    intro b _
    have h2 := ((hasDerivAt_pow 3 b).const_mul (4*π*(1+2*att*t^2)/3)).add
      ((hasDerivAt_pow 5 b).const_mul (8*π*as/5))
    have h3 : 4*π*(1+2*att*t^2)/3*(↑3*b^(3-1)) + 8*π*as/5*(↑5*b^(5-1))
        = 4*π*b^2 * (1 + 4*(att*t^2/2 + as*b^2/2)) := by
      push_cast
      ring
    exact h3 ▸ h2
  rw [integral_eq_sub_of_hasDerivAt hF
    ((Continuous.intervalIntegrable (by fun_prop) _ _))]
  ring

/-- Exact linearized volume: `(2π/3)T⁴ + (4π/45)a_tt T⁶ + (8π/15)a_s T⁶`. -/
theorem Vlin_eval (att as T : ℝ) :
    Vlin att as T = 2*π/3*T^4 + 4*π/45*att*T^6 + 8*π/15*as*T^6 := by
  unfold Vlin
  rw [integral_congr (g := fun t =>
    4*π/3*(T-t)^3 + 8*π/3*att*(t^2*(T-t)^3) + 8*π/5*as*(T-t)^5)
    (fun t _ => by rw [inner_lin_eval]; ring)]
  have hi1 : IntervalIntegrable (fun t : ℝ => 4*π/3*(T-t)^3) volume 0 T :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hi2 : IntervalIntegrable (fun t : ℝ => 8*π/3*att*(t^2*(T-t)^3))
      volume 0 T := (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hi3 : IntervalIntegrable (fun t : ℝ => 8*π/5*as*(T-t)^5) volume 0 T :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [intervalIntegral.integral_add (hi1.add hi2) hi3,
    intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, J3, J23, J5]
  ring

/-! ## The split `Vg = Vlin + Q` and the quartic remainder bound -/

/-- The quartic remainder term. -/
noncomputable def Qrem (att as T : ℝ) : ℝ :=
  2 * ∫ t in (0:ℝ)..T, ∫ b in (0:ℝ)..(T-t),
    4*π*b^2 * ((1 + att*t^2/2 + as*b^2/2)^4 - (1 + 4*(att*t^2/2 + as*b^2/2)))

theorem Vg_split (att as T : ℝ) :
    Vg att as T = Vlin att as T + Qrem att as T := by
  unfold Vg Vlin Qrem
  have hc1 : Continuous (fun t : ℝ => ∫ b in (0:ℝ)..(T-t),
      4*π*b^2 * (1 + 4*(att*t^2/2 + as*b^2/2))) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    · fun_prop
    · fun_prop
  have hc2 : Continuous (fun t : ℝ => ∫ b in (0:ℝ)..(T-t),
      4*π*b^2 * ((1 + att*t^2/2 + as*b^2/2)^4
        - (1 + 4*(att*t^2/2 + as*b^2/2)))) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    · fun_prop
    · fun_prop
  rw [← mul_add, ← intervalIntegral.integral_add
    (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
  congr 1
  apply integral_congr
  intro t _
  dsimp only
  rw [← intervalIntegral.integral_add
    ((Continuous.intervalIntegrable (by fun_prop) _ _))
    ((Continuous.intervalIntegrable (by fun_prop) _ _))]
  apply integral_congr
  intro b _
  ring

/-- Pointwise: the quartic remainder integrand is `O(q²)`. -/
theorem quartic_pointwise (phi q : ℝ) (hphi : |phi| ≤ q) (hq14 : q ≤ 1/4) :
    |(1+phi)^4 - (1 + 4*phi)| ≤ 8*q^2 := by
  have hq0 : 0 ≤ q := le_trans (abs_nonneg phi) hphi
  have h1 := abs_le.mp hphi
  have hsq : phi^2 ≤ q^2 := sq_le_sq' h1.1 h1.2
  have hq2aux : 0 ≤ q^2 + q*phi + phi^2 := by
    nlinarith [sq_nonneg (q + phi), sq_nonneg q, sq_nonneg phi]
  have hcube : phi^3 ≤ q^3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h1.2) hq2aux]
  have hcube' : -(q^3) ≤ phi^3 := by
    have hq2aux' : 0 ≤ q^2 - q*phi + phi^2 := by
      nlinarith [sq_nonneg (q - phi), sq_nonneg q, sq_nonneg phi]
    nlinarith [mul_nonneg (sub_nonneg.mpr (neg_le.mp h1.1)) hq2aux']
  have hquart : phi^4 ≤ q^4 := by nlinarith [hsq, sq_nonneg phi, sq_nonneg q]
  have h4q3 : 4*q^3 ≤ q^2 := by nlinarith [sq_nonneg q, hq14, hq0]
  have hq4 : q^4 ≤ q^2 := by nlinarith [sq_nonneg q, hq14, hq0]
  have h6 : (1+phi)^4 - (1 + 4*phi) = 6*phi^2 + 4*phi^3 + phi^4 := by ring
  rw [h6, abs_le]
  constructor
  · nlinarith [hcube', h4q3, sq_nonneg phi, sq_nonneg (phi^2), hsq]
  · nlinarith [hcube, hsq, hquart, h4q3, hq4]

/-- The quartic remainder is fourth order: `|Q| ≤ 64π·(T²/λ²)²·T⁴`. -/
theorem Qrem_bound (att as T lam : ℝ) (hT : 0 < T) (hlam : 0 < lam)
    (hatt : |att| ≤ 1/lam^2) (has : |as| ≤ 1/lam^2)
    (hTlam : T ≤ lam/2) :
    |Qrem att as T| ≤ 64*π*(T^2/lam^2)^2*T^4 := by
  set q := T^2/lam^2 with hqdef
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  have hq14 : q ≤ 1/4 := by
    rw [hqdef, div_le_iff₀ (by positivity)]
    nlinarith [hTlam, hT.le, hlam.le]
  have houter : ∀ t ∈ Set.uIoc (0:ℝ) T,
      ‖∫ b in (0:ℝ)..(T-t), 4*π*b^2 * ((1 + att*t^2/2 + as*b^2/2)^4
        - (1 + 4*(att*t^2/2 + as*b^2/2)))‖ ≤ 32*π*T^2*q^2*T := by
    intro t ht
    rw [Set.uIoc_of_le hT.le] at ht
    have hinner : ∀ b ∈ Set.uIoc (0:ℝ) (T-t),
        ‖4*π*b^2 * ((1 + att*t^2/2 + as*b^2/2)^4
          - (1 + 4*(att*t^2/2 + as*b^2/2)))‖ ≤ 32*π*T^2*q^2 := by
      intro b hb
      have hTt : (0:ℝ) ≤ T - t := by linarith [ht.2]
      rw [Set.uIoc_of_le hTt] at hb
      have hbT : b ≤ T := by linarith [hb.2, ht.1]
      have hb0 : 0 < b := hb.1
      have hphi : |att*t^2/2 + as*b^2/2| ≤ q := by
        have b1 : |att*t^2/2 + as*b^2/2| ≤ |att*t^2/2| + |as*b^2/2| :=
          abs_add_le _ _
        have b2 : |att*t^2/2| = |att| * (t^2/2) := by
          rw [show att*t^2/2 = att*(t^2/2) from by ring, abs_mul,
            abs_of_nonneg (by positivity : (0:ℝ) ≤ t^2/2)]
        have b3 : |as*b^2/2| = |as| * (b^2/2) := by
          rw [show as*b^2/2 = as*(b^2/2) from by ring, abs_mul,
            abs_of_nonneg (by positivity : (0:ℝ) ≤ b^2/2)]
        have ht2 : t^2 ≤ T^2 := by nlinarith [ht.1, ht.2]
        have hb2 : b^2 ≤ T^2 := by nlinarith [hb0, hbT]
        have g1 : |att| * (t^2/2) ≤ 1/lam^2 * (T^2/2) := by
          apply mul_le_mul hatt (by linarith) (by positivity) (by positivity)
        have g2 : |as| * (b^2/2) ≤ 1/lam^2 * (T^2/2) := by
          apply mul_le_mul has (by linarith) (by positivity) (by positivity)
        have hqeq : 1/lam^2 * (T^2/2) + 1/lam^2 * (T^2/2) = q := by
          rw [hqdef]
          field_simp
          norm_num
        rw [b2, b3] at b1
        linarith [b1, g1, g2, hqeq]
      have hpoly := quartic_pointwise (att*t^2/2 + as*b^2/2) q hphi hq14
      have hshape : (1 + att*t^2/2 + as*b^2/2)^4
          - (1 + 4*(att*t^2/2 + as*b^2/2))
          = (1+(att*t^2/2 + as*b^2/2))^4
            - (1 + 4*(att*t^2/2 + as*b^2/2)) := by ring
      rw [Real.norm_eq_abs, abs_mul, hshape]
      have hcoef : |4*π*b^2| = 4*π*b^2 := abs_of_pos (by positivity)
      rw [hcoef]
      calc 4*π*b^2 * |(1+(att*t^2/2 + as*b^2/2))^4
            - (1 + 4*(att*t^2/2 + as*b^2/2))|
          ≤ 4*π*b^2 * (8*q^2) :=
            mul_le_mul_of_nonneg_left hpoly (by positivity)
        _ ≤ 4*π*T^2 * (8*q^2) := by
            have hbb : b^2 ≤ T^2 := by nlinarith [hb0, hbT]
            nlinarith [mul_nonneg (mul_nonneg (le_of_lt Real.pi_pos)
              (sq_nonneg q)) (sub_nonneg.mpr hbb)]
        _ = 32*π*T^2*q^2 := by ring
    calc ‖∫ b in (0:ℝ)..(T-t), 4*π*b^2 * ((1 + att*t^2/2 + as*b^2/2)^4
          - (1 + 4*(att*t^2/2 + as*b^2/2)))‖
        ≤ 32*π*T^2*q^2 * |T - t - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hinner
      _ ≤ 32*π*T^2*q^2 * T := by
          have habs : |T - t - 0| ≤ T := by
            rw [abs_le]
            constructor
            · linarith [ht.2]
            · linarith [ht.1]
          exact mul_le_mul_of_nonneg_left habs (by positivity)
  unfold Qrem
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), ← Real.norm_eq_abs]
  calc 2 * ‖∫ t in (0:ℝ)..T, ∫ b in (0:ℝ)..(T-t), 4*π*b^2 *
        ((1 + att*t^2/2 + as*b^2/2)^4 - (1 + 4*(att*t^2/2 + as*b^2/2)))‖
      ≤ 2 * (32*π*T^2*q^2*T * |T - 0|) :=
        mul_le_mul_of_nonneg_left
          (intervalIntegral.norm_integral_le_of_norm_le_const houter)
          (by norm_num)
    _ = 64*π*q^2*T^4 := by
        rw [show |T - (0:ℝ)| = T from by rw [sub_zero, abs_of_pos hT]]
        ring

/-! ## The polynomial numerator bound -/

/-- `|N| ≤ 21·T⁴·q²` for the recentered numerator polynomial. -/
theorem Nlin_poly_bound (att as T lam : ℝ) (hT : 0 < T) (hlam : 0 < lam)
    (hatt : |att| ≤ 1/lam^2) (has : |as| ≤ 1/lam^2) (hTlam : T ≤ lam/2) :
    |24/π*(Vlin att as T) - (taug att T)^4
      - (3*as - 2*att)/15*(taug att T)^6| ≤ 21*T^4*(T^2/lam^2)^2 := by
  set q := T^2/lam^2 with hqdef
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  have hq14 : q ≤ 1/4 := by
    rw [hqdef, div_le_iff₀ (by positivity)]
    nlinarith [hTlam, hT.le, hlam.le]
  set u := att*T^2 with hudef
  set v := as*T^2 with hvdef
  have hu : |u| ≤ q := by
    rw [hudef, abs_mul, abs_pow, abs_of_pos hT, hqdef]
    calc |att| * T^2 ≤ 1/lam^2 * T^2 :=
          mul_le_mul_of_nonneg_right hatt (sq_nonneg T)
      _ = T^2/lam^2 := by ring
  have hv : |v| ≤ q := by
    rw [hvdef, abs_mul, abs_pow, abs_of_pos hT, hqdef]
    calc |as| * T^2 ≤ 1/lam^2 * T^2 :=
          mul_le_mul_of_nonneg_right has (sq_nonneg T)
      _ = T^2/lam^2 := by ring
  have hG : 24/π*(Vlin att as T) - (taug att T)^4
      - (3*as - 2*att)/15*(taug att T)^6
      = T^4 * ((88/15 : ℝ) * u^2 + (-64/5 : ℝ) * u * v + (88/27 : ℝ) * u^3 + (-16/3 : ℝ) * u^2 * v + (7/9 : ℝ) * u^4 + (-32/27 : ℝ) * u^3 * v + (8/81 : ℝ) * u^5 + (-4/27 : ℝ) * u^4 * v + (8/1215 : ℝ) * u^6 + (-4/405 : ℝ) * u^5 * v + (2/10935 : ℝ) * u^7 + (-1/3645 : ℝ) * u^6 * v) := by
    rw [Vlin_eval, taug_eval, hudef, hvdef]
    field_simp
    ring
  have hb1 : |(88/15 : ℝ) * u^2| ≤ (88/15 : ℝ) * q^2 := by
    rw [abs_mul, abs_pow, show |(88/15 : ℝ)| = (88/15 : ℝ) from by norm_num]
    have h1 : |u|^2 ≤ q^2 := pow_le_pow_left₀ (abs_nonneg u) hu 2
    nlinarith [h1, abs_nonneg u, abs_nonneg v, sq_nonneg q]
  have hb2 : |(-64/5 : ℝ) * u * v| ≤ (64/5 : ℝ) * q^2 := by
    rw [abs_mul, abs_mul, show |(-64/5 : ℝ)| = (64/5 : ℝ) from by norm_num]
    have h1 : |u| * |v| ≤ q * q :=
      mul_le_mul hu hv (abs_nonneg v) (by positivity)
    nlinarith [h1, abs_nonneg u, abs_nonneg v, sq_nonneg q]
  have hb3 : |(88/27 : ℝ) * u^3| ≤ (22/27 : ℝ) * q^2 := by
    rw [abs_mul, abs_pow, show |(88/27 : ℝ)| = (88/27 : ℝ) from by norm_num]
    have h1 : |u|^3 ≤ q^3 := pow_le_pow_left₀ (abs_nonneg u) hu 3
    have h2 : q^3 ≤ (1/4 : ℝ)^1 * q^2 := by
      calc q^3 = q^1 * q^2 := by ring
        _ ≤ (1/4 : ℝ)^1 * q^2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hq14 1) (sq_nonneg q)
    have h3 : (1/4 : ℝ)^1 * q^2 = ((1/4 : ℝ)) * q^2 := by norm_num
    nlinarith [h1, h2, h3, abs_nonneg u, abs_nonneg v, sq_nonneg q]
  have hb4 : |(-16/3 : ℝ) * u^2 * v| ≤ (4/3 : ℝ) * q^2 := by
    rw [abs_mul, abs_mul, abs_pow, show |(-16/3 : ℝ)| = (16/3 : ℝ) from by norm_num]
    have h1 : |u|^2 * |v| ≤ q^2 * q :=
      mul_le_mul (pow_le_pow_left₀ (abs_nonneg u) hu 2) hv (abs_nonneg v) (by positivity)
    have h2 : q^2 * q ≤ (1/4 : ℝ)^1 * q^2 := by
      calc q^2 * q = q^1 * q^2 := by ring
        _ ≤ (1/4 : ℝ)^1 * q^2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hq14 1) (sq_nonneg q)
    have h3 : (1/4 : ℝ)^1 * q^2 = ((1/4 : ℝ)) * q^2 := by norm_num
    nlinarith [h1, h2, h3, abs_nonneg u, abs_nonneg v, sq_nonneg q]
  have hb5 : |(7/9 : ℝ) * u^4| ≤ (7/144 : ℝ) * q^2 := by
    rw [abs_mul, abs_pow, show |(7/9 : ℝ)| = (7/9 : ℝ) from by norm_num]
    have h1 : |u|^4 ≤ q^4 := pow_le_pow_left₀ (abs_nonneg u) hu 4
    have h2 : q^4 ≤ (1/4 : ℝ)^2 * q^2 := by
      calc q^4 = q^2 * q^2 := by ring
        _ ≤ (1/4 : ℝ)^2 * q^2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hq14 2) (sq_nonneg q)
    have h3 : (1/4 : ℝ)^2 * q^2 = ((1/16 : ℝ)) * q^2 := by norm_num
    nlinarith [h1, h2, h3, abs_nonneg u, abs_nonneg v, sq_nonneg q]
  have hb6 : |(-32/27 : ℝ) * u^3 * v| ≤ (2/27 : ℝ) * q^2 := by
    rw [abs_mul, abs_mul, abs_pow, show |(-32/27 : ℝ)| = (32/27 : ℝ) from by norm_num]
    have h1 : |u|^3 * |v| ≤ q^3 * q :=
      mul_le_mul (pow_le_pow_left₀ (abs_nonneg u) hu 3) hv (abs_nonneg v) (by positivity)
    have h2 : q^3 * q ≤ (1/4 : ℝ)^2 * q^2 := by
      calc q^3 * q = q^2 * q^2 := by ring
        _ ≤ (1/4 : ℝ)^2 * q^2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hq14 2) (sq_nonneg q)
    have h3 : (1/4 : ℝ)^2 * q^2 = ((1/16 : ℝ)) * q^2 := by norm_num
    nlinarith [h1, h2, h3, abs_nonneg u, abs_nonneg v, sq_nonneg q]
  have hb7 : |(8/81 : ℝ) * u^5| ≤ (1/648 : ℝ) * q^2 := by
    rw [abs_mul, abs_pow, show |(8/81 : ℝ)| = (8/81 : ℝ) from by norm_num]
    have h1 : |u|^5 ≤ q^5 := pow_le_pow_left₀ (abs_nonneg u) hu 5
    have h2 : q^5 ≤ (1/4 : ℝ)^3 * q^2 := by
      calc q^5 = q^3 * q^2 := by ring
        _ ≤ (1/4 : ℝ)^3 * q^2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hq14 3) (sq_nonneg q)
    have h3 : (1/4 : ℝ)^3 * q^2 = ((1/64 : ℝ)) * q^2 := by norm_num
    nlinarith [h1, h2, h3, abs_nonneg u, abs_nonneg v, sq_nonneg q]
  have hb8 : |(-4/27 : ℝ) * u^4 * v| ≤ (1/432 : ℝ) * q^2 := by
    rw [abs_mul, abs_mul, abs_pow, show |(-4/27 : ℝ)| = (4/27 : ℝ) from by norm_num]
    have h1 : |u|^4 * |v| ≤ q^4 * q :=
      mul_le_mul (pow_le_pow_left₀ (abs_nonneg u) hu 4) hv (abs_nonneg v) (by positivity)
    have h2 : q^4 * q ≤ (1/4 : ℝ)^3 * q^2 := by
      calc q^4 * q = q^3 * q^2 := by ring
        _ ≤ (1/4 : ℝ)^3 * q^2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hq14 3) (sq_nonneg q)
    have h3 : (1/4 : ℝ)^3 * q^2 = ((1/64 : ℝ)) * q^2 := by norm_num
    nlinarith [h1, h2, h3, abs_nonneg u, abs_nonneg v, sq_nonneg q]
  have hb9 : |(8/1215 : ℝ) * u^6| ≤ (1/38880 : ℝ) * q^2 := by
    rw [abs_mul, abs_pow, show |(8/1215 : ℝ)| = (8/1215 : ℝ) from by norm_num]
    have h1 : |u|^6 ≤ q^6 := pow_le_pow_left₀ (abs_nonneg u) hu 6
    have h2 : q^6 ≤ (1/4 : ℝ)^4 * q^2 := by
      calc q^6 = q^4 * q^2 := by ring
        _ ≤ (1/4 : ℝ)^4 * q^2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hq14 4) (sq_nonneg q)
    have h3 : (1/4 : ℝ)^4 * q^2 = ((1/256 : ℝ)) * q^2 := by norm_num
    nlinarith [h1, h2, h3, abs_nonneg u, abs_nonneg v, sq_nonneg q]
  have hb10 : |(-4/405 : ℝ) * u^5 * v| ≤ (1/25920 : ℝ) * q^2 := by
    rw [abs_mul, abs_mul, abs_pow, show |(-4/405 : ℝ)| = (4/405 : ℝ) from by norm_num]
    have h1 : |u|^5 * |v| ≤ q^5 * q :=
      mul_le_mul (pow_le_pow_left₀ (abs_nonneg u) hu 5) hv (abs_nonneg v) (by positivity)
    have h2 : q^5 * q ≤ (1/4 : ℝ)^4 * q^2 := by
      calc q^5 * q = q^4 * q^2 := by ring
        _ ≤ (1/4 : ℝ)^4 * q^2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hq14 4) (sq_nonneg q)
    have h3 : (1/4 : ℝ)^4 * q^2 = ((1/256 : ℝ)) * q^2 := by norm_num
    nlinarith [h1, h2, h3, abs_nonneg u, abs_nonneg v, sq_nonneg q]
  have hb11 : |(2/10935 : ℝ) * u^7| ≤ (1/5598720 : ℝ) * q^2 := by
    rw [abs_mul, abs_pow, show |(2/10935 : ℝ)| = (2/10935 : ℝ) from by norm_num]
    have h1 : |u|^7 ≤ q^7 := pow_le_pow_left₀ (abs_nonneg u) hu 7
    have h2 : q^7 ≤ (1/4 : ℝ)^5 * q^2 := by
      calc q^7 = q^5 * q^2 := by ring
        _ ≤ (1/4 : ℝ)^5 * q^2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hq14 5) (sq_nonneg q)
    have h3 : (1/4 : ℝ)^5 * q^2 = ((1/1024 : ℝ)) * q^2 := by norm_num
    nlinarith [h1, h2, h3, abs_nonneg u, abs_nonneg v, sq_nonneg q]
  have hb12 : |(-1/3645 : ℝ) * u^6 * v| ≤ (1/3732480 : ℝ) * q^2 := by
    rw [abs_mul, abs_mul, abs_pow, show |(-1/3645 : ℝ)| = (1/3645 : ℝ) from by norm_num]
    have h1 : |u|^6 * |v| ≤ q^6 * q :=
      mul_le_mul (pow_le_pow_left₀ (abs_nonneg u) hu 6) hv (abs_nonneg v) (by positivity)
    have h2 : q^6 * q ≤ (1/4 : ℝ)^5 * q^2 := by
      calc q^6 * q = q^5 * q^2 := by ring
        _ ≤ (1/4 : ℝ)^5 * q^2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hq14 5) (sq_nonneg q)
    have h3 : (1/4 : ℝ)^5 * q^2 = ((1/1024 : ℝ)) * q^2 := by norm_num
    nlinarith [h1, h2, h3, abs_nonneg u, abs_nonneg v, sq_nonneg q]
  have s1 : |(88/15 : ℝ) * u^2| ≤ (88/15 : ℝ) * q^2 := hb1
  have s2 : |(88/15 : ℝ) * u^2 + (-64/5 : ℝ) * u * v| ≤ (88/15 : ℝ) * q^2 + (64/5 : ℝ) * q^2 :=
    (abs_add_le _ _).trans (add_le_add s1 hb2)
  have s3 : |(88/15 : ℝ) * u^2 + (-64/5 : ℝ) * u * v + (88/27 : ℝ) * u^3| ≤ (88/15 : ℝ) * q^2 + (64/5 : ℝ) * q^2 + (22/27 : ℝ) * q^2 :=
    (abs_add_le _ _).trans (add_le_add s2 hb3)
  have s4 : |(88/15 : ℝ) * u^2 + (-64/5 : ℝ) * u * v + (88/27 : ℝ) * u^3 + (-16/3 : ℝ) * u^2 * v| ≤ (88/15 : ℝ) * q^2 + (64/5 : ℝ) * q^2 + (22/27 : ℝ) * q^2 + (4/3 : ℝ) * q^2 :=
    (abs_add_le _ _).trans (add_le_add s3 hb4)
  have s5 : |(88/15 : ℝ) * u^2 + (-64/5 : ℝ) * u * v + (88/27 : ℝ) * u^3 + (-16/3 : ℝ) * u^2 * v + (7/9 : ℝ) * u^4| ≤ (88/15 : ℝ) * q^2 + (64/5 : ℝ) * q^2 + (22/27 : ℝ) * q^2 + (4/3 : ℝ) * q^2 + (7/144 : ℝ) * q^2 :=
    (abs_add_le _ _).trans (add_le_add s4 hb5)
  have s6 : |(88/15 : ℝ) * u^2 + (-64/5 : ℝ) * u * v + (88/27 : ℝ) * u^3 + (-16/3 : ℝ) * u^2 * v + (7/9 : ℝ) * u^4 + (-32/27 : ℝ) * u^3 * v| ≤ (88/15 : ℝ) * q^2 + (64/5 : ℝ) * q^2 + (22/27 : ℝ) * q^2 + (4/3 : ℝ) * q^2 + (7/144 : ℝ) * q^2 + (2/27 : ℝ) * q^2 :=
    (abs_add_le _ _).trans (add_le_add s5 hb6)
  have s7 : |(88/15 : ℝ) * u^2 + (-64/5 : ℝ) * u * v + (88/27 : ℝ) * u^3 + (-16/3 : ℝ) * u^2 * v + (7/9 : ℝ) * u^4 + (-32/27 : ℝ) * u^3 * v + (8/81 : ℝ) * u^5| ≤ (88/15 : ℝ) * q^2 + (64/5 : ℝ) * q^2 + (22/27 : ℝ) * q^2 + (4/3 : ℝ) * q^2 + (7/144 : ℝ) * q^2 + (2/27 : ℝ) * q^2 + (1/648 : ℝ) * q^2 :=
    (abs_add_le _ _).trans (add_le_add s6 hb7)
  have s8 : |(88/15 : ℝ) * u^2 + (-64/5 : ℝ) * u * v + (88/27 : ℝ) * u^3 + (-16/3 : ℝ) * u^2 * v + (7/9 : ℝ) * u^4 + (-32/27 : ℝ) * u^3 * v + (8/81 : ℝ) * u^5 + (-4/27 : ℝ) * u^4 * v| ≤ (88/15 : ℝ) * q^2 + (64/5 : ℝ) * q^2 + (22/27 : ℝ) * q^2 + (4/3 : ℝ) * q^2 + (7/144 : ℝ) * q^2 + (2/27 : ℝ) * q^2 + (1/648 : ℝ) * q^2 + (1/432 : ℝ) * q^2 :=
    (abs_add_le _ _).trans (add_le_add s7 hb8)
  have s9 : |(88/15 : ℝ) * u^2 + (-64/5 : ℝ) * u * v + (88/27 : ℝ) * u^3 + (-16/3 : ℝ) * u^2 * v + (7/9 : ℝ) * u^4 + (-32/27 : ℝ) * u^3 * v + (8/81 : ℝ) * u^5 + (-4/27 : ℝ) * u^4 * v + (8/1215 : ℝ) * u^6| ≤ (88/15 : ℝ) * q^2 + (64/5 : ℝ) * q^2 + (22/27 : ℝ) * q^2 + (4/3 : ℝ) * q^2 + (7/144 : ℝ) * q^2 + (2/27 : ℝ) * q^2 + (1/648 : ℝ) * q^2 + (1/432 : ℝ) * q^2 + (1/38880 : ℝ) * q^2 :=
    (abs_add_le _ _).trans (add_le_add s8 hb9)
  have s10 : |(88/15 : ℝ) * u^2 + (-64/5 : ℝ) * u * v + (88/27 : ℝ) * u^3 + (-16/3 : ℝ) * u^2 * v + (7/9 : ℝ) * u^4 + (-32/27 : ℝ) * u^3 * v + (8/81 : ℝ) * u^5 + (-4/27 : ℝ) * u^4 * v + (8/1215 : ℝ) * u^6 + (-4/405 : ℝ) * u^5 * v| ≤ (88/15 : ℝ) * q^2 + (64/5 : ℝ) * q^2 + (22/27 : ℝ) * q^2 + (4/3 : ℝ) * q^2 + (7/144 : ℝ) * q^2 + (2/27 : ℝ) * q^2 + (1/648 : ℝ) * q^2 + (1/432 : ℝ) * q^2 + (1/38880 : ℝ) * q^2 + (1/25920 : ℝ) * q^2 :=
    (abs_add_le _ _).trans (add_le_add s9 hb10)
  have s11 : |(88/15 : ℝ) * u^2 + (-64/5 : ℝ) * u * v + (88/27 : ℝ) * u^3 + (-16/3 : ℝ) * u^2 * v + (7/9 : ℝ) * u^4 + (-32/27 : ℝ) * u^3 * v + (8/81 : ℝ) * u^5 + (-4/27 : ℝ) * u^4 * v + (8/1215 : ℝ) * u^6 + (-4/405 : ℝ) * u^5 * v + (2/10935 : ℝ) * u^7| ≤ (88/15 : ℝ) * q^2 + (64/5 : ℝ) * q^2 + (22/27 : ℝ) * q^2 + (4/3 : ℝ) * q^2 + (7/144 : ℝ) * q^2 + (2/27 : ℝ) * q^2 + (1/648 : ℝ) * q^2 + (1/432 : ℝ) * q^2 + (1/38880 : ℝ) * q^2 + (1/25920 : ℝ) * q^2 + (1/5598720 : ℝ) * q^2 :=
    (abs_add_le _ _).trans (add_le_add s10 hb11)
  have s12 : |(88/15 : ℝ) * u^2 + (-64/5 : ℝ) * u * v + (88/27 : ℝ) * u^3 + (-16/3 : ℝ) * u^2 * v + (7/9 : ℝ) * u^4 + (-32/27 : ℝ) * u^3 * v + (8/81 : ℝ) * u^5 + (-4/27 : ℝ) * u^4 * v + (8/1215 : ℝ) * u^6 + (-4/405 : ℝ) * u^5 * v + (2/10935 : ℝ) * u^7 + (-1/3645 : ℝ) * u^6 * v| ≤ (88/15 : ℝ) * q^2 + (64/5 : ℝ) * q^2 + (22/27 : ℝ) * q^2 + (4/3 : ℝ) * q^2 + (7/144 : ℝ) * q^2 + (2/27 : ℝ) * q^2 + (1/648 : ℝ) * q^2 + (1/432 : ℝ) * q^2 + (1/38880 : ℝ) * q^2 + (1/25920 : ℝ) * q^2 + (1/5598720 : ℝ) * q^2 + (1/3732480 : ℝ) * q^2 :=
    (abs_add_le _ _).trans (add_le_add s11 hb12)
  rw [hG, abs_mul, abs_of_pos (pow_pos hT 4)]
  have hfin : |(88/15 : ℝ) * u^2 + (-64/5 : ℝ) * u * v + (88/27 : ℝ) * u^3 + (-16/3 : ℝ) * u^2 * v + (7/9 : ℝ) * u^4 + (-32/27 : ℝ) * u^3 * v + (8/81 : ℝ) * u^5 + (-4/27 : ℝ) * u^4 * v + (8/1215 : ℝ) * u^6 + (-4/405 : ℝ) * u^5 * v + (2/10935 : ℝ) * u^7 + (-1/3645 : ℝ) * u^6 * v| ≤ 21*q^2 := by
    nlinarith [s12, sq_nonneg q]
  calc T^4 * |(88/15 : ℝ) * u^2 + (-64/5 : ℝ) * u * v + (88/27 : ℝ) * u^3 + (-16/3 : ℝ) * u^2 * v + (7/9 : ℝ) * u^4 + (-32/27 : ℝ) * u^3 * v + (8/81 : ℝ) * u^5 + (-4/27 : ℝ) * u^4 * v + (8/1215 : ℝ) * u^6 + (-4/405 : ℝ) * u^5 * v + (2/10935 : ℝ) * u^7 + (-1/3645 : ℝ) * u^6 * v| ≤ T^4 * (21*q^2) :=
        mul_le_mul_of_nonneg_left hfin (by positivity)
    _ = 21*T^4*q^2 := by ring

/-! ## THE RSS EXPANSION -/

/-- **THE RSS/GS EXPANSION, DERIVED** (conformally flat sector):

    Vg/((π/24)·τ⁴) − 1 = c₁·τ² + rem,
    c₁ = (3·a_s − 2·a_tt)/15,   |c₁| ≤ (1/3)/λ²,   |rem| ≤ 9·τ⁴/λ⁴

for `|a_tt|, |a_s| ≤ 1/λ²`, `0 < T ≤ λ/2` — exactly the `hexp`, `hc₁`,
`hrem` hypotheses of `smallDiamond_volumeFaithful`, now theorems. -/
theorem rss_expansion_conformal (att as T lam : ℝ)
    (hT : 0 < T) (hlam : 0 < lam)
    (hatt : |att| ≤ 1/lam^2) (has : |as| ≤ 1/lam^2) (hTlam : T ≤ lam/2) :
    ∃ c₁ rem : ℝ,
      Vg att as T / ((π/24) * (taug att T)^4) - 1
        = c₁ * (taug att T)^2 + rem
      ∧ |c₁| ≤ (1/3) / lam^2
      ∧ |rem| ≤ 9 * (taug att T)^4 / lam^4 := by
  have hπ : (0:ℝ) < π := Real.pi_pos
  set q := T^2/lam^2 with hqdef
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  have hq14 : q ≤ 1/4 := by
    rw [hqdef, div_le_iff₀ (by positivity)]
    nlinarith [hTlam, hT.le, hlam.le]
  have hattl := abs_le.mp hatt
  have hasl := abs_le.mp has
  have htau : taug att T = 2*T + att*T^3/3 := taug_eval att T
  have htau_low : 23*T/12 ≤ taug att T := by
    rw [htau]
    have h1 : -(1/lam^2)*T^3 ≤ att*T^3 := by
      nlinarith [hattl.1, pow_pos hT 3]
    have h2 : (1/lam^2)*T^3 = q*T := by
      rw [hqdef]
      field_simp
    nlinarith [h1, h2, hq14, hT.le]
  have htau_pos : 0 < taug att T := lt_of_lt_of_le (by positivity) htau_low
  refine ⟨(3*as - 2*att)/15,
    Vg att as T / ((π/24) * (taug att T)^4) - 1
      - (3*as - 2*att)/15 * (taug att T)^2, by ring, ?_, ?_⟩
  · have hw : (1:ℝ)/3/lam^2 = (1/3)*(1/lam^2) := by ring
    rw [abs_le, hw]
    constructor
    · linarith [hattl.2, hasl.1]
    · linarith [hattl.1, hasl.2]
  · have hNb := Nlin_poly_bound att as T lam hT hlam hatt has hTlam
    have hQb := Qrem_bound att as T lam hT hlam hatt has hTlam
    have hsplit := Vg_split att as T
    have hrem_eq : Vg att as T / ((π/24) * (taug att T)^4) - 1
        - (3*as - 2*att)/15 * (taug att T)^2
        = ((24/π*(Vlin att as T) - (taug att T)^4
            - (3*as - 2*att)/15*(taug att T)^6)
           + 24/π*(Qrem att as T)) / (taug att T)^4 := by
      rw [hsplit]
      field_simp
      ring
    rw [hrem_eq, abs_div, abs_of_pos (pow_pos htau_pos 4)]
    have hQ2 : |24/π*(Qrem att as T)| ≤ 1536*T^4*q^2 := by
      rw [abs_mul, show |24/π| = 24/π from abs_of_pos (by positivity)]
      calc 24/π * |Qrem att as T| ≤ 24/π * (64*π*(T^2/lam^2)^2*T^4) :=
            mul_le_mul_of_nonneg_left hQb (by positivity)
        _ = 1536*T^4*q^2 := by
            rw [hqdef]
            first
            | (field_simp; ring)
            | field_simp
    have hnum : |(24/π*(Vlin att as T) - (taug att T)^4
        - (3*as - 2*att)/15*(taug att T)^6) + 24/π*(Qrem att as T)|
        ≤ 1557*T^4*q^2 := by
      calc |(24/π*(Vlin att as T) - (taug att T)^4
            - (3*as - 2*att)/15*(taug att T)^6) + 24/π*(Qrem att as T)|
          ≤ |24/π*(Vlin att as T) - (taug att T)^4
            - (3*as - 2*att)/15*(taug att T)^6| + |24/π*(Qrem att as T)| :=
            abs_add_le _ _
        _ ≤ 21*T^4*q^2 + 1536*T^4*q^2 := by
            have hNb' := hNb
            rw [← hqdef] at hNb'
            linarith [hNb', hQ2]
        _ = 1557*T^4*q^2 := by ring
    have htau4 : (23/12)^4*T^4 ≤ (taug att T)^4 := by
      calc ((23:ℝ)/12)^4*T^4 = (23*T/12)^4 := by ring
        _ ≤ (taug att T)^4 := pow_le_pow_left₀ (by positivity) htau_low 4
    have hT4 : T^4 ≤ ((12:ℝ)/23)^4*(taug att T)^4 := by nlinarith [htau4]
    have h8 : 1557*(T^4*T^4) ≤ 9*((taug att T)^4*(taug att T)^4) := by
      have h2 := mul_le_mul hT4 hT4 (by positivity) (by positivity)
      nlinarith [h2, pow_pos htau_pos 4]
    calc |(24/π*(Vlin att as T) - (taug att T)^4
          - (3*as - 2*att)/15*(taug att T)^6) + 24/π*(Qrem att as T)|
          / (taug att T)^4
        ≤ 1557*T^4*q^2 / (taug att T)^4 := by
          gcongr
      _ = 1557*(T^4*T^4)/((taug att T)^4*lam^4) := by
          rw [hqdef]
          first
          | (field_simp; ring)
          | field_simp
      _ ≤ 9 * (taug att T)^4 / lam^4 := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < (taug att T)^4*lam^4)]
          have hlamdiv : 9 * (taug att T)^4 / lam^4 * ((taug att T)^4*lam^4)
              = 9 * ((taug att T)^4 * (taug att T)^4) * (lam^4/lam^4) := by
            ring
          rw [hlamdiv, div_self (by positivity : (lam:ℝ)^4 ≠ 0), mul_one]
          exact h8

/-! ## The Gibbons–Solodukhin coefficients -/

/-- Linearized scalar curvature of `g = Ω²η` at the center:
`R = −6□Ω = −6(−a_tt + 3a_s)`. -/
noncomputable def Rscalar (att as : ℝ) : ℝ := 6*att - 18*as

/-- Linearized `R₀₀` of `g = Ω²η`: `R₀₀ = −2∂²ₜφ − η₀₀□φ = −3a_tt + 3a_s`. -/
noncomputable def Rtt (att as : ℝ) : ℝ := -3*att + 3*as

/-- **The Gibbons–Solodukhin 4D coefficients, derived**:
`c₁ = −R/180 + R₀₀/30`. -/
theorem gs_coefficients (att as : ℝ) :
    (3*as - 2*att)/15 = -(Rscalar att as)/180 + (Rtt att as)/30 := by
  unfold Rscalar Rtt
  ring

/-! ## The volume-faithfulness certificate -/

/-- **The certificate**: the conformal family satisfies the small-diamond
volume-faithfulness bound with `A = 1/3`, `D = 9` derived:
`|Vg/((π/24)τ⁴) − 1| ≤ (1/3 + 9)·τ²/λ²`. -/
theorem rss_certifies_smallDiamond (att as T lam : ℝ)
    (hT : 0 < T) (hlam : 0 < lam)
    (hatt : |att| ≤ 1/lam^2) (has : |as| ≤ 1/lam^2) (hTlam : T ≤ lam/2)
    (htaulam : taug att T ≤ lam) :
    |Vg att as T / ((π/24) * (taug att T)^4) - 1|
      ≤ (1/3 + 9) * (taug att T)^2 / lam^2 := by
  obtain ⟨c₁, rem, heq, hc₁, hrem⟩ :=
    rss_expansion_conformal att as T lam hT hlam hatt has hTlam
  have hattl := abs_le.mp hatt
  have htau : taug att T = 2*T + att*T^3/3 := taug_eval att T
  have htau_low : 23*T/12 ≤ taug att T := by
    rw [htau]
    have h1 : -(1/lam^2)*T^3 ≤ att*T^3 := by
      nlinarith [hattl.1, pow_pos hT 3]
    have hq14 : T^2/lam^2 ≤ 1/4 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hTlam, hT.le, hlam.le]
    have h2 : (1/lam^2)*T^3 = (T^2/lam^2)*T := by
      field_simp
    nlinarith [h1, h2, hq14, hT.le]
  have htau_pos : 0 < taug att T := lt_of_lt_of_le (by positivity) htau_low
  have hexp4 : Vg att as T / ((π/24) * (taug att T)^(4:ℕ)) - 1
      = c₁ * (taug att T)^2 + rem := heq
  exact UnifiedTheory.Audit.KFCausalCSpecCurvatureVolumeBound.smallDiamond_volumeFaithful
    (π/24) (1/3) 9 (taug att T) lam (Vg att as T) 4
    htau_pos hlam (by norm_num) htaulam c₁ rem hexp4 hc₁ hrem

#print axioms taug_eval
#print axioms Vlin_eval
#print axioms Vg_split
#print axioms Qrem_bound
#print axioms Nlin_poly_bound
#print axioms rss_expansion_conformal
#print axioms gs_coefficients
#print axioms rss_certifies_smallDiamond

end UnifiedTheory.Audit.KFCausalCSpecRSSConformal
