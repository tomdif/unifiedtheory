/-
  Audit/KFCausalCSpecKarcherClosure.lean
  — DISCHARGING THE KARCHER HYPOTHESIS

  The global quantitative Hauptvermutung (`global_hauptvermutung`) carried
  one cited geometric input: the barycenter stability `hbary` with defect κ.
  This file DERIVES it for the arithmetic-mean barycenter:

  1.  `karcher_mean_stability`:  if the diagonal interval values of the
      chart differences sit in an η-window around m, and the PAIRWISE chart
      discrepancies (in interval terms) are ≤ d, then the mean's interval
      value is within η + d/2 of m.  Mechanism: polarization bounds every
      cross term, |B wᵢ wⱼ − m| ≤ η + d/2, and the mean's quadratic form is
      the average of the N² cross terms.  The Karcher defect is NOT an
      axiom: κ = d/2, with d the chart-overlap consistency datum.
  2.  `global_hauptvermutung_mean`:  the closed end-to-end theorem — per-
      chart counts (window ε, curvature bias b) + pairwise chart consistency
      d  ⟹  the arithmetic-mean glue is a global approximate isometry with
      distortion ≤ (ε + b + εb)·S + d/2.  No cited stability input remains;
      the only geometric hypothesis left in the whole chain is the
      Roy–Sinha–Surya expansion behind the bias bound.

  Zero sorry.  Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalCSpecReconstructionLimit

set_option autoImplicit false

open UnifiedTheory.Audit.KFCausalCSpecReconstructionLimit
open UnifiedTheory.Audit.KFCausalCSpecGluing

namespace UnifiedTheory.Audit.KFCausalCSpecKarcherClosure

/-- **Karcher stability of the arithmetic mean, derived.**  Diagonal windows
η around m plus pairwise discrepancies ≤ d give the mean's quadratic value
within η + d/2 of m: the barycenter defect is κ = d/2, not a postulate. -/
theorem karcher_mean_stability {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (B : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (w : ι → Y) (m η d : ℝ)
    (hdiag : ∀ i, |B (w i) (w i) - m| ≤ η)
    (hpair : ∀ i j, |B (w i - w j) (w i - w j)| ≤ d) :
    |B ((Fintype.card ι : ℝ)⁻¹ • ∑ i, w i)
       ((Fintype.card ι : ℝ)⁻¹ • ∑ i, w i) - m| ≤ η + d / 2 := by
  have hcard : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  set N := (Fintype.card ι : ℝ) with hNdef
  have hN0 : N ≠ 0 := hcard.ne'
  -- every cross term is controlled through polarization
  have hcross : ∀ i j, |B (w i) (w j) - m| ≤ η + d / 2 := by
    intro i j
    have hpol : B (w i) (w j)
        = (B (w i) (w i) + B (w j) (w j)
            - B (w i - w j) (w i - w j)) / 2 := by
      simp only [map_sub, LinearMap.sub_apply]
      have s1 := hsymm (w i) (w j)
      linarith
    rw [hpol]
    have h1 := hdiag i
    have h2 := hdiag j
    have h3 := hpair i j
    rw [abs_le] at h1 h2 h3 ⊢
    constructor
    · linarith [h1.1, h2.1, h3.2]
    · linarith [h1.2, h2.2, h3.1]
  -- the mean's quadratic form is the average of the N² cross terms
  have hexp : B (N⁻¹ • ∑ i, w i) (N⁻¹ • ∑ i, w i)
      = N⁻¹ * (N⁻¹ * ∑ i, ∑ j, B (w i) (w j)) := by
    simp only [map_smul, LinearMap.smul_apply, map_sum,
      LinearMap.sum_apply, smul_eq_mul]
    rw [← Finset.mul_sum, Finset.sum_comm]
  -- recentering: pull m inside the double sum
  have hinner : ∀ i, (∑ j, (B (w i) (w j) - m))
      = (∑ j, B (w i) (w j)) - N * m := by
    intro i
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hNdef]
  have hsum2 : (∑ i, ∑ j, (B (w i) (w j) - m))
      = (∑ i, ∑ j, B (w i) (w j)) - N * (N * m) := by
    rw [Finset.sum_congr rfl (fun i _ => hinner i), Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hNdef]
  have hshift : N⁻¹ * (N⁻¹ * ∑ i, ∑ j, B (w i) (w j)) - m
      = N⁻¹ * (N⁻¹ * ∑ i, ∑ j, (B (w i) (w j) - m)) := by
    rw [hsum2]
    field_simp
  rw [hexp, hshift, abs_mul, abs_mul,
    abs_of_pos (by positivity : (0:ℝ) < N⁻¹)]
  calc N⁻¹ * (N⁻¹ * |∑ i, ∑ j, (B (w i) (w j) - m)|)
      ≤ N⁻¹ * (N⁻¹ * ∑ i, ∑ j, |B (w i) (w j) - m|) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc |∑ i, ∑ j, (B (w i) (w j) - m)|
            ≤ ∑ i, |∑ j, (B (w i) (w j) - m)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, ∑ j, |B (w i) (w j) - m| :=
              Finset.sum_le_sum
                (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ N⁻¹ * (N⁻¹ * ∑ _i : ι, ∑ _j : ι, (η + d / 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum
          (fun i _ => Finset.sum_le_sum (fun j _ => hcross i j))
    _ = η + d / 2 := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, nsmul_eq_mul, ← hNdef]
        field_simp

/-- **THE CLOSED GLOBAL QUANTITATIVE HAUPTVERMUTUNG.**  Per-chart interval
counts (Poisson window ε, curvature bias b) + pairwise chart consistency d
⟹ the arithmetic-mean glue is a GLOBAL approximate isometry:

    distortion ≤ (ε + b + εb)·S + d/2.

The Karcher stability is no longer a cited input — it is
`karcher_mean_stability`.  The full chain Chebyshev–Poisson → π/24 →
curvature bias → polarization → mean gluing is now derivation all the way
through; the sole remaining geometric hypothesis in the program is the
Roy–Sinha–Surya expansion behind `smallDiamond_volumeFaithful`. -/
theorem global_hauptvermutung_mean
    {X Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (B : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (G : X → X → ℝ) (κd ε b S rho : ℝ)
    (hρ : 0 < rho) (hε : 0 ≤ ε) (hb : 0 ≤ b)
    (g : ι → X → Y) (n : ι → X → X → ℝ) (Vol : ι → X → X → ℝ)
    (hG : ∀ x x', 0 < G x x') (hGS : ∀ x x', G x x' ≤ S)
    (hchart : ∀ i x x', B (g i x - g i x') (g i x - g i x')
      = Real.sqrt (24 * n i x x' / (Real.pi * rho)))
    (hn : ∀ i x x', 0 ≤ n i x x') (hV : ∀ i x x', 0 < Vol i x x')
    (hconc : ∀ i x x', |n i x x' / (rho * Vol i x x') - 1| ≤ ε)
    (hbias : ∀ i x x',
      |Vol i x x' / ((Real.pi/24) * (G x x')^2) - 1| ≤ b)
    (hpair : ∀ i j x x',
      |B ((g i x - g i x') - (g j x - g j x'))
         ((g i x - g i x') - (g j x - g j x'))| ≤ κd) :
    HasDistortion G (fun y y' => B (y - y') (y - y'))
      (fun x => (Fintype.card ι : ℝ)⁻¹ • ∑ i, g i x)
      ((ε + b + ε * b) * S + κd / 2) := by
  intro x x'
  have hebb : 0 ≤ ε + b + ε * b := by positivity
  have hmean : ((Fintype.card ι : ℝ)⁻¹ • ∑ i, g i x)
      - ((Fintype.card ι : ℝ)⁻¹ • ∑ i, g i x')
      = (Fintype.card ι : ℝ)⁻¹ • ∑ i, (g i x - g i x') := by
    rw [Finset.sum_sub_distrib, smul_sub]
  have hdiag : ∀ i, |B (g i x - g i x') (g i x - g i x') - G x x'|
      ≤ (ε + b + ε * b) * S := by
    intro i
    rw [hchart i x x']
    exact le_trans
      (count_estimator_error_curved rho (G x x') (n i x x') (Vol i x x')
        ε b hρ (hG x x') (hn i x x') (hV i x x') hε hb
        (hconc i x x') (hbias i x x'))
      (mul_le_mul_of_nonneg_left (hGS x x') hebb)
  have hstab := karcher_mean_stability B hsymm
    (fun i => g i x - g i x') (G x x') ((ε + b + ε * b) * S) κd
    hdiag (fun i j => hpair i j x x')
  show |B (_ - _) (_ - _) - G x x'| ≤ _
  rw [hmean]
  exact hstab

/-- Relation-restricted form of the quantitative Hauptvermutung.  Every
interval-specific hypothesis is consumed only on a pair satisfying `R`, and
the conclusion records exactly that restricted scope. -/
theorem global_hauptvermutung_mean_on
    {X Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (R : X → X → Prop)
    (B : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (G : X → X → ℝ) (κd ε b S rho : ℝ)
    (hρ : 0 < rho) (hε : 0 ≤ ε) (hb : 0 ≤ b)
    (g : ι → X → Y) (n : ι → X → X → ℝ) (Vol : ι → X → X → ℝ)
    (hG : ∀ x x', R x x' → 0 < G x x')
    (hGS : ∀ x x', R x x' → G x x' ≤ S)
    (hchart : ∀ i x x', R x x' →
      B (g i x - g i x') (g i x - g i x') =
        Real.sqrt (24 * n i x x' / (Real.pi * rho)))
    (hn : ∀ i x x', 0 ≤ n i x x')
    (hV : ∀ i x x', R x x' → 0 < Vol i x x')
    (hconc : ∀ i x x', R x x' →
      |n i x x' / (rho * Vol i x x') - 1| ≤ ε)
    (hbias : ∀ i x x', R x x' →
      |Vol i x x' / ((Real.pi/24) * (G x x')^2) - 1| ≤ b)
    (hpair : ∀ i j x x', R x x' →
      |B ((g i x - g i x') - (g j x - g j x'))
         ((g i x - g i x') - (g j x - g j x'))| ≤ κd) :
    HasDistortionOn R G (fun y y' => B (y - y') (y - y'))
      (fun x => (Fintype.card ι : ℝ)⁻¹ • ∑ i, g i x)
      ((ε + b + ε * b) * S + κd / 2) := by
  intro x x' hx
  have hebb : 0 ≤ ε + b + ε * b := by positivity
  have hmean : ((Fintype.card ι : ℝ)⁻¹ • ∑ i, g i x)
      - ((Fintype.card ι : ℝ)⁻¹ • ∑ i, g i x')
      = (Fintype.card ι : ℝ)⁻¹ • ∑ i, (g i x - g i x') := by
    rw [Finset.sum_sub_distrib, smul_sub]
  have hdiag : ∀ i, |B (g i x - g i x') (g i x - g i x') - G x x'|
      ≤ (ε + b + ε * b) * S := by
    intro i
    rw [hchart i x x' hx]
    exact le_trans
      (count_estimator_error_curved rho (G x x') (n i x x') (Vol i x x')
        ε b hρ (hG x x' hx) (hn i x x') (hV i x x' hx) hε hb
        (hconc i x x' hx) (hbias i x x' hx))
      (mul_le_mul_of_nonneg_left (hGS x x' hx) hebb)
  have hstab := karcher_mean_stability B hsymm
    (fun i => g i x - g i x') (G x x') ((ε + b + ε * b) * S) κd
    hdiag (fun i j => hpair i j x x' hx)
  show |B (_ - _) (_ - _) - G x x'| ≤ _
  rw [hmean]
  exact hstab

/-- Distinct-pair interval laws, together with a zero source diagonal, give the
same total distortion statement as the legacy all-pairs theorem.  The upgrade
uses `hasDistortion_of_distinct`; no diagonal count or volume law is invented. -/
theorem global_hauptvermutung_mean_distinct
    {X Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (B : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (G : X → X → ℝ) (κd ε b S rho : ℝ)
    (hρ : 0 < rho) (hε : 0 ≤ ε) (hb : 0 ≤ b)
    (hS : 0 ≤ S) (hκd : 0 ≤ κd) (hGself : ∀ x, G x x = 0)
    (g : ι → X → Y) (n : ι → X → X → ℝ) (Vol : ι → X → X → ℝ)
    (hG : ∀ x x', x ≠ x' → 0 < G x x')
    (hGS : ∀ x x', G x x' ≤ S)
    (hchart : ∀ i x x', x ≠ x' →
      B (g i x - g i x') (g i x - g i x') =
        Real.sqrt (24 * n i x x' / (Real.pi * rho)))
    (hn : ∀ i x x', 0 ≤ n i x x')
    (hV : ∀ i x x', x ≠ x' → 0 < Vol i x x')
    (hconc : ∀ i x x', x ≠ x' →
      |n i x x' / (rho * Vol i x x') - 1| ≤ ε)
    (hbias : ∀ i x x', x ≠ x' →
      |Vol i x x' / ((Real.pi/24) * (G x x')^2) - 1| ≤ b)
    (hpair : ∀ i j x x', x ≠ x' →
      |B ((g i x - g i x') - (g j x - g j x'))
         ((g i x - g i x') - (g j x - g j x'))| ≤ κd) :
    HasDistortion G (fun y y' => B (y - y') (y - y'))
      (fun x => (Fintype.card ι : ℝ)⁻¹ • ∑ i, g i x)
      ((ε + b + ε * b) * S + κd / 2) := by
  apply hasDistortion_of_distinct G
    (fun y y' => B (y - y') (y - y'))
    (fun x => (Fintype.card ι : ℝ)⁻¹ • ∑ i, g i x)
    ((ε + b + ε * b) * S + κd / 2)
  · exact global_hauptvermutung_mean_on
      (fun x x' => x ≠ x') B hsymm G κd ε b S rho hρ hε hb g n Vol
      hG (fun x x' _ => hGS x x') hchart hn hV hconc hbias hpair
  · intro x
    simp [hGself x]
  · positivity

#print axioms karcher_mean_stability
#print axioms global_hauptvermutung_mean
#print axioms global_hauptvermutung_mean_on
#print axioms global_hauptvermutung_mean_distinct

end UnifiedTheory.Audit.KFCausalCSpecKarcherClosure
