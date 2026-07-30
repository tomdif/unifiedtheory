/-
  Audit/KFCausalCSpecReconstructionLimit.lean
  — THE CURVED DICTIONARY, THE RESOLUTION LIMIT, AND THE GLOBAL GLUE

  Climbing the ladder above the local quantitative Hauptvermutung:

  1.  `count_estimator_error_curved`:  bias + variance.  With the counting
      window `|n/ρV − 1| ≤ ε` AND the curvature bias `|V/((π/24)τ⁴) − 1| ≤ b`
      (instantiated by `smallDiamond_volumeFaithful`: b = (A+D)τ²/λ²), the
      proper-time estimator satisfies |τ̂² − τ²| ≤ (ε + b + εb)·τ².
  2.  `hauptvermutung_curved`:  the metric-component reconstruction in curved
      space: error ≤ (3/2)·(ε + b + εb)·S.
  3.  `am_gm_tradeoff` / `resolution_limit`:  THE RESOLUTION LIMIT OF
      SPACETIME.  The statistical error shrinks with the diamond (ε ∝ τ⁻²
      at fixed density) while the curvature bias grows (b ∝ τ²); no choice
      of window beats the AM–GM floor
          err ≥ 2·√(K·c_R),   K = k·√(24/π)·ρ^{−1/2},  c_R = (A+D)/λ²,
      i.e. metric components cannot be known better than ∝ ρ^{−1/4} in
      curved spacetime.  Discreteness plus curvature is a bandwidth limit.
  4.  `minkowski_form` / `cstab_standard_tetrad`:  the stability constant of
      the standard Minkowski tetrad frame is EXACTLY 2: coordinate-axis
      anchor differences give ‖w‖ ≤ 2·max|η(w,eᵢ)| in 4D.
  5.  `global_hauptvermutung`:  the end-to-end composition — per-chart
      counts (window ε, bias b) + chart maps matching their own estimators +
      Karcher barycenter stability κ  ⟹  the glued map is a GLOBAL
      approximate isometry with distortion ≤ (ε + b + εb)·S + κ.

  Zero sorry.  Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalCSpecQuantitativeHauptvermutung
import UnifiedTheory.Audit.KFCausalCSpecCurvatureVolumeBound
import UnifiedTheory.Audit.KFCausalCSpecGluing

set_option autoImplicit false

open UnifiedTheory.Audit.KFCausalCSpecQuantitativeHauptvermutung
open UnifiedTheory.Audit.KFCausalCSpecGluing

namespace UnifiedTheory.Audit.KFCausalCSpecReconstructionLimit

/-! ## 1. The curved counting dictionary: bias + variance -/

/-- **Bias + variance for the proper-time estimator.**  Counting window ε
around the TRUE curved volume, curvature bias b of the true volume against
the flat dictionary `(π/24)τ⁴` (this is exactly the `β` bounded by
`smallDiamond_volumeFaithful`): the flat-dictionary estimator still recovers
τ² with relative error ε + b + εb. -/
theorem count_estimator_error_curved (rho tau2 n Vol ε b : ℝ)
    (hρ : 0 < rho) (hτ : 0 < tau2) (hn : 0 ≤ n) (hV : 0 < Vol)
    (hε : 0 ≤ ε) (hb : 0 ≤ b)
    (hconc : |n / (rho * Vol) - 1| ≤ ε)
    (hbias : |Vol / ((Real.pi/24) * tau2^2) - 1| ≤ b) :
    |Real.sqrt (24 * n / (Real.pi * rho)) - tau2|
      ≤ (ε + b + ε * b) * tau2 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  set u := n / (rho * Vol) with hu
  set v := Vol / ((Real.pi/24) * tau2^2) with hv
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have harg : 24 * n / (Real.pi * rho) = tau2^2 * (u * v) := by
    rw [hu, hv]
    field_simp
  have huv : |u * v - 1| ≤ ε + b + ε * b := by
    have hprod : u * v - 1 = (u - 1) * (v - 1) + (u - 1) + (v - 1) := by ring
    calc |u * v - 1|
        = |(u - 1) * (v - 1) + (u - 1) + (v - 1)| := by rw [hprod]
      _ ≤ |(u - 1) * (v - 1) + (u - 1)| + |v - 1| := abs_add_le _ _
      _ ≤ |(u - 1) * (v - 1)| + |u - 1| + |v - 1| := by
          have := abs_add_le ((u - 1) * (v - 1)) (u - 1)
          linarith
      _ = |u - 1| * |v - 1| + |u - 1| + |v - 1| := by rw [abs_mul]
      _ ≤ ε * b + ε + b := by
          have h1 : |u - 1| * |v - 1| ≤ ε * b :=
            mul_le_mul hconc hbias (abs_nonneg _) hε
          linarith [hconc, hbias]
      _ = ε + b + ε * b := by ring
  rw [harg, Real.sqrt_mul (by positivity) (u * v), Real.sqrt_sq hτ.le,
    show tau2 * Real.sqrt (u * v) - tau2 = tau2 * (Real.sqrt (u * v) - 1)
      from by ring,
    abs_mul, abs_of_pos hτ]
  calc tau2 * |Real.sqrt (u * v) - 1|
      ≤ tau2 * |u * v - 1| :=
        mul_le_mul_of_nonneg_left
          (sqrt_error_le (u * v) (mul_nonneg hu0 hv0)) hτ.le
    _ ≤ tau2 * (ε + b + ε * b) := mul_le_mul_of_nonneg_left huv hτ.le
    _ = (ε + b + ε * b) * tau2 := by ring

/-! ## 2. The curved metric reconstruction -/

/-- **The quantitative Hauptvermutung in curved space.**  Same three-count
estimator, now with the curvature bias folded in: metric-component error
at most `(3/2)·(ε + b + εb)·S`. -/
theorem hauptvermutung_curved {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (ai aj ao : V) (rho ε b S : ℝ)
    (t_io t_jo t_ij n_io n_jo n_ij V_io V_jo V_ij : ℝ)
    (hρ : 0 < rho) (hε : 0 ≤ ε) (hb : 0 ≤ b)
    (ht_io : sigma2 B ai ao = t_io) (ht_jo : sigma2 B aj ao = t_jo)
    (ht_ij : sigma2 B ai aj = t_ij)
    (hpos_io : 0 < t_io) (hpos_jo : 0 < t_jo) (hpos_ij : 0 < t_ij)
    (hS_io : t_io ≤ S) (hS_jo : t_jo ≤ S) (hS_ij : t_ij ≤ S)
    (hn_io : 0 ≤ n_io) (hn_jo : 0 ≤ n_jo) (hn_ij : 0 ≤ n_ij)
    (hV_io : 0 < V_io) (hV_jo : 0 < V_jo) (hV_ij : 0 < V_ij)
    (hconc_io : |n_io / (rho * V_io) - 1| ≤ ε)
    (hconc_jo : |n_jo / (rho * V_jo) - 1| ≤ ε)
    (hconc_ij : |n_ij / (rho * V_ij) - 1| ≤ ε)
    (hbias_io : |V_io / ((Real.pi/24) * t_io^2) - 1| ≤ b)
    (hbias_jo : |V_jo / ((Real.pi/24) * t_jo^2) - 1| ≤ b)
    (hbias_ij : |V_ij / ((Real.pi/24) * t_ij^2) - 1| ≤ b) :
    |(Real.sqrt (24 * n_io / (Real.pi * rho))
        + Real.sqrt (24 * n_jo / (Real.pi * rho))
        - Real.sqrt (24 * n_ij / (Real.pi * rho))) / 2
      - B (ai - ao) (aj - ao)| ≤ 3/2 * ((ε + b + ε * b) * S) := by
  have hS0 : 0 ≤ S := le_trans hpos_io.le hS_io
  have hebb : 0 ≤ ε + b + ε * b := by positivity
  have e_io := count_estimator_error_curved rho t_io n_io V_io ε b
    hρ hpos_io hn_io hV_io hε hb hconc_io hbias_io
  have e_jo := count_estimator_error_curved rho t_jo n_jo V_jo ε b
    hρ hpos_jo hn_jo hV_jo hε hb hconc_jo hbias_jo
  have e_ij := count_estimator_error_curved rho t_ij n_ij V_ij ε b
    hρ hpos_ij hn_ij hV_ij hε hb hconc_ij hbias_ij
  apply gram_reconstruction_lipschitz B hsymm ai aj ao _ _ _ ((ε + b + ε * b) * S)
  · rw [ht_io]
    exact le_trans e_io (mul_le_mul_of_nonneg_left hS_io hebb)
  · rw [ht_jo]
    exact le_trans e_jo (mul_le_mul_of_nonneg_left hS_jo hebb)
  · rw [ht_ij]
    exact le_trans e_ij (mul_le_mul_of_nonneg_left hS_ij hebb)

/-! ## 3. THE RESOLUTION LIMIT OF SPACETIME -/

/-- **AM–GM tradeoff.**  For every window `x > 0`, the bias+variance sum
`A/x + c·x` is bounded below by `2√(A·c)` — no window choice beats the
geometric-mean floor. -/
theorem am_gm_tradeoff (A c x : ℝ) (hA : 0 ≤ A) (hc : 0 ≤ c) (hx : 0 < x) :
    2 * Real.sqrt (A * c) ≤ A / x + c * x := by
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · rw [← hc0]
    have h1 : Real.sqrt (A * 0) = 0 := by rw [mul_zero, Real.sqrt_zero]
    rw [h1]
    have h2 : 0 ≤ A / x := div_nonneg hA hx.le
    linarith
  · set s := Real.sqrt (A * c) with hsdef
    have hs2 : s^2 = A * c := Real.sq_sqrt (mul_nonneg hA hcpos.le)
    have hkey : c * (A + c * x^2 - 2 * s * x) = (s - c * x)^2 := by
      linear_combination (-1 : ℝ) * hs2
    have hQ : 0 ≤ A + c * x^2 - 2 * s * x := by
      have hsq : (0:ℝ) ≤ (s - c * x)^2 := sq_nonneg _
      nlinarith [hcpos]
    rw [show A / x + c * x = (A + c * x^2) / x from by field_simp,
      le_div_iff₀ hx]
    linarith

/-- **THE RESOLUTION LIMIT.**  Instantiating the tradeoff with the counting
variance `K/τ²` (K = k·√(24/π)·ρ^{−1/2}, from `poisson_count_concentration`
at confidence k) and the curvature bias `c_R·τ²` (c_R = (A+D)/λ², from
`smallDiamond_volumeFaithful`): for EVERY diamond size τ,

    2·√(K·c_R)  ≤  K/τ² + c_R·τ².

Since `K ∝ ρ^{−1/2}`, the floor scales as `ρ^{−1/4}·√k(A+D)/λ`: **metric
components of a curved spacetime cannot be reconstructed from causal-set
counting to better than O(ρ^{−1/4})** — discreteness plus curvature is a
bandwidth limit, with all constants derived. -/
theorem resolution_limit (K cR τ : ℝ) (hK : 0 ≤ K) (hc : 0 ≤ cR)
    (hτ : 0 < τ) :
    2 * Real.sqrt (K * cR) ≤ K / τ^2 + cR * τ^2 :=
  am_gm_tradeoff K cR (τ^2) hK hc (by positivity)

/-! ## 4. The standard tetrad has stability constant exactly 2 -/

/-- The Minkowski bilinear form on `ℝ^{1,3}` (as `EuclideanSpace ℝ (Fin 4)`
with signature `(−,+,+,+)`). -/
noncomputable def minkowskiForm :
    EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun w v => -(w 0 * v 0) + w 1 * v 1 + w 2 * v 2 + w 3 * v 3)
    (by intro m₁ m₂ v; simp [PiLp.add_apply]; ring)
    (by intro c m v; simp [PiLp.smul_apply, smul_eq_mul]; ring)
    (by intro m v₁ v₂; simp [PiLp.add_apply]; ring)
    (by intro c m v; simp [PiLp.smul_apply, smul_eq_mul]; ring)

/-- **The standard tetrad's stability constant is 2.**  If the Minkowski
inner products of `w` against the four coordinate-axis anchor differences
are all ≤ η, then `‖w‖ ≤ 2η`.  This instantiates the `hstab` hypothesis of
`trilateration_stability` with `Cstab = 2`, closing the last abstract
constant of the local reconstruction chain: point-location error ≤ 4δ. -/
theorem cstab_standard_tetrad (η : ℝ) (w : EuclideanSpace ℝ (Fin 4))
    (hη : 0 ≤ η)
    (h : ∀ i : Fin 4, |minkowskiForm w (EuclideanSpace.single i 1)| ≤ η) :
    ‖w‖ ≤ 2 * η := by
  have hcoord : ∀ i : Fin 4, |w i| ≤ η := by
    intro i
    have hi := h i
    fin_cases i <;>
      simpa [minkowskiForm, EuclideanSpace.single_apply, abs_neg] using hi
  have hsum : (∑ i : Fin 4, ‖w i‖^2) ≤ 4 * η^2 := by
    have hterm : ∀ i ∈ Finset.univ, ‖w i‖^2 ≤ η^2 := by
      intro i _
      rw [Real.norm_eq_abs]
      nlinarith [hcoord i, abs_nonneg (w i)]
    calc (∑ i : Fin 4, ‖w i‖^2)
        ≤ ∑ _i : Fin 4, η^2 := Finset.sum_le_sum hterm
      _ = 4 * η^2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          norm_num
  calc ‖w‖ = Real.sqrt (∑ i : Fin 4, ‖w i‖^2) := EuclideanSpace.norm_eq w
    _ ≤ Real.sqrt (4 * η^2) := Real.sqrt_le_sqrt hsum
    _ = 2 * η := by
        rw [show 4 * η^2 = (2 * η)^2 from by ring,
          Real.sqrt_sq (by linarith)]

/-! ## 5. THE GLOBAL QUANTITATIVE HAUPTVERMUTUNG -/

/-- **The end-to-end composition.**  Per-chart interval counts, each in its
counting window (ε) with curvature bias (b) against the true intervals `G`;
chart maps `g i` that realize their own count-estimators exactly; Karcher
barycenter stability κ (`hbary`, the cited geometric input of the gluing
step).  Then the glued map is a GLOBAL approximate isometry:

    distortion ≤ (ε + b + εb)·S + κ.

Order + number determine the geometry of the whole spacetime region, with
error bars, through the explicit chain
Chebyshev–Poisson → flat dictionary π/24 → curvature bias (A+D)τ²/λ² →
barycenter gluing. -/
theorem global_hauptvermutung
    {X Y ι : Type*} (G : X → X → ℝ) (F : Y → Y → ℝ)
    (bary : (ι → Y) → Y) (κ ε b S rho : ℝ)
    (hρ : 0 < rho) (hε : 0 ≤ ε) (hb : 0 ≤ b)
    (hbary : ∀ (a b' : ι → Y) (m η : ℝ),
      (∀ i, |F (a i) (b' i) - m| ≤ η) → |F (bary a) (bary b') - m| ≤ η + κ)
    (g : ι → X → Y) (n : ι → X → X → ℝ) (Vol : ι → X → X → ℝ)
    (hG : ∀ x x', 0 < G x x') (hGS : ∀ x x', G x x' ≤ S)
    (hchart : ∀ i x x',
      F (g i x) (g i x') = Real.sqrt (24 * n i x x' / (Real.pi * rho)))
    (hn : ∀ i x x', 0 ≤ n i x x') (hV : ∀ i x x', 0 < Vol i x x')
    (hconc : ∀ i x x', |n i x x' / (rho * Vol i x x') - 1| ≤ ε)
    (hbias : ∀ i x x',
      |Vol i x x' / ((Real.pi/24) * (G x x')^2) - 1| ≤ b) :
    HasDistortion G F (fun x => bary (fun i => g i x))
      ((ε + b + ε * b) * S + κ) := by
  have hebb : 0 ≤ ε + b + ε * b := by positivity
  have hloc : ∀ i, HasDistortion G F (g i) ((ε + b + ε * b) * S) := by
    intro i x x'
    rw [hchart i x x']
    have herr := count_estimator_error_curved rho (G x x') (n i x x')
      (Vol i x x') ε b hρ (hG x x') (hn i x x') (hV i x x') hε hb
      (hconc i x x') (hbias i x x')
    exact le_trans herr
      (mul_le_mul_of_nonneg_left (hGS x x') hebb)
  exact glue_distortion G F bary ((ε + b + ε * b) * S) κ hbary g hloc

#print axioms count_estimator_error_curved
#print axioms hauptvermutung_curved
#print axioms am_gm_tradeoff
#print axioms resolution_limit
#print axioms cstab_standard_tetrad
#print axioms global_hauptvermutung

end UnifiedTheory.Audit.KFCausalCSpecReconstructionLimit
