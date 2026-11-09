/-
  Quantitative and calculus ingredients for reference-phase locality.
  The overlap/resolvent and marked cubical-kernel suppliers are proved
  analytically in UNIFORM_REFERENCE_LOCALITY.md, not fully formalized here.
  The final action example proves underdetermination, not a physical TOE.
-/
import UnifiedTheory.Audit.KFCausalReferencePhaseDescent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalUniformReferenceLocality
noncomputable section
open scoped BigOperators
open MeasureTheory

/-- Integration by parts needed for a pure-gradient change of reference. -/
theorem weighted_ward_integral (ρ ρ' : ℝ → ℝ)
    (hd : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt ρ (ρ' t) t)
    (hi : IntervalIntegrable ρ volume 0 1)
    (hw : IntervalIntegrable (fun t => (1 - t) * ρ' t) volume 0 1) :
    (∫ t in (0 : ℝ)..1, (1 - t) * ρ' t) = (∫ t in (0 : ℝ)..1, ρ t) - ρ 0 := by
  have hdF : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s => (1 - s) * ρ s) (-ρ t + (1 - t) * ρ' t) t := by
    intro t ht
    convert ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul (hd t ht) using 1
    dsimp
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hdF (hi.neg.add hw)
  have hineg : IntervalIntegrable (fun t => -ρ t) volume 0 1 := hi.neg
  rw [intervalIntegral.integral_add hineg hw, intervalIntegral.integral_neg] at he
  simp only [sub_self, zero_mul, sub_zero, one_mul, zero_sub] at he
  linarith

/-- The curvature flux and scalar Ward correction cancel as real numbers. -/
theorem gradient_reference_cancellation (ρ ρ' : ℝ → ℝ) (I c₀ c₁ : ℝ)
    (hd : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt ρ (ρ' t) t)
    (hi : IntervalIntegrable ρ volume 0 1)
    (hw : IntervalIntegrable (fun t => (1 - t) * ρ' t) volume 0 1)
    (hflat : ρ 0 = 0)
    (hI : I = -(∫ t in (0 : ℝ)..1, (1 - t) * ρ' t))
    (hC : c₁ - c₀ = ∫ t in (0 : ℝ)..1, ρ t) : I + c₁ - c₀ = 0 := by
  rw [weighted_ward_integral ρ ρ' hd hi hw, hflat, sub_zero] at hI
  linarith

section Fibre
variable {V : Type*} [AddCommGroup V]

/-- An additive comparison can replace a shift by a gauge-equivalent seam.
The cocycle and the actual pure-gradient cancellation are explicit suppliers. -/
theorem seam_replacement (K : V → V → V → ℝ) (b a r S g : V)
    (hr : r = S + g)
    (hc : K b a (S + g) = K b a S + K (b + S) (a - S) g)
    (hg : K (b + S) (a - S) g = 0) : K b a r = K b a S := by
  rw [hr, hc, hg, add_zero]

end Fibre

/-- Preserve an extra marked site through a centered, non-enlarging homotopy. -/
theorem marked_radius_transfer (u v R D : ℝ) (hv : v ≤ u) (hD : D ≤ v + R) :
    u + D ≤ 3 * max u R := by
  have hu := le_max_left u R
  have hR := le_max_right u R
  linarith

/-- A new anchor is at most twice the old marked diameter from the mark. -/
theorem marked_diameter_transfer (u v R D : ℝ) (hv : v ≤ u) (hD : D ≤ v + R) :
    D ≤ 2 * max u R := by
  have hu := le_max_left u R
  have hR := le_max_right u R
  linarith

theorem marked_exponential_transfer (μ u v R D : ℝ) (hμ : 0 ≤ μ)
    (hv : v ≤ u) (hD : D ≤ v + R) :
    Real.exp (-μ * max u R) ≤ Real.exp (-μ * u / 3) * Real.exp (-μ * D / 3) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := marked_radius_transfer u v R D hv hD
  nlinarith

section FiniteSums
variable {E : Type*} [Fintype E]

/-- Exposes the seam-supported term and the difference of local primitives. -/
theorem scalar_correction_split (a S hi hj : E → ℝ) :
    -(∑ e, (a e - S e) * hj e) + (∑ e, a e * hi e) =
      (∑ e, S e * hj e) - (∑ e, a e * (hj e - hi e)) := by
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Each of the 2^m terms from differentiating a linear mean is controlled. -/
theorem bounded_chain_rule_sum (c k : E → ℝ) (δ : ℝ)
    (hc : ∀ e, |c e| ≤ 1) (hk : ∀ e, |k e| ≤ δ) :
    |∑ e, c e * k e| ≤ Fintype.card E * δ := by
  calc
    _ ≤ ∑ e, |c e * k e| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : E, δ := by
      apply Finset.sum_le_sum
      intro e _
      rw [abs_mul]
      calc
        _ ≤ 1 * δ := mul_le_mul (hc e) (hk e) (abs_nonneg _) (by norm_num)
        _ = δ := one_mul δ
    _ = _ := by simp

end FiniteSums

/-- Extends a derivative estimate from the exactly flat zero-fluctuation base. -/
theorem integrate_small_derivative (g g' : ℝ → ℝ) (δ : ℝ)
    (hd : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt g (g' t) t)
    (hi : IntervalIntegrable g' volume 0 1)
    (hb : ∀ t ∈ Set.uIoc (0 : ℝ) 1, |g' t| ≤ δ) (hzero : g 0 = 0) :
    |g 1| ≤ δ := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun t ht => (show ‖g' t‖ ≤ δ by simpa only [Real.norm_eq_abs] using hb t ht))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi, hzero, sub_zero] at hbound
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hbound

/-- Add a volume-small correction to an exponentially local response. -/
theorem local_response_preserved (j correction C D α β d L : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hβ : 0 ≤ β) (hd : 0 ≤ d) (hdiam : d ≤ 2 * L)
    (hj : |j| ≤ C * Real.exp (-α * d))
    (hc : |correction| ≤ D * Real.exp (-β * L)) :
    |j - correction| ≤ (C + D) * Real.exp (-(min α (β / 2)) * d) := by
  have hv := KFCausalSecondCohomology.volume_to_distance_bound d L β D hβ hD hdiam
  have hα : C * Real.exp (-α * d) ≤ C * Real.exp (-(min α (β / 2)) * d) := by
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.exp_le_exp.mpr
    have h := min_le_left α (β / 2)
    nlinarith
  have hβ' : D * Real.exp (-β * d / 2) ≤ D * Real.exp (-(min α (β / 2)) * d) := by
    apply mul_le_mul_of_nonneg_left _ hD
    apply Real.exp_le_exp.mpr
    have h := min_le_right α (β / 2)
    nlinarith
  calc
    _ ≤ |j| + |correction| := by simpa using (abs_sub_le j 0 correction)
    _ ≤ C * Real.exp (-α * d) + D * Real.exp (-β * L) := add_le_add hj hc
    _ ≤ C * Real.exp (-(min α (β / 2)) * d) + D * Real.exp (-(min α (β / 2)) * d) :=
      add_le_add hα (hv.trans hβ')
    _ = _ := by ring

section ActionFreedom
variable {V P : Type*} [AddCommGroup V] [AddCommGroup P]

/-- Any plaquette action remains gauge invariant when curl annihilates gradients. -/
theorem plaquette_action_gauge_invariant (curl : V →+ P) (cost : P → ℝ)
    (a gradient : V) (hg : curl gradient = 0) : cost (curl (a + gradient)) = cost (curl a) := by
  rw [map_add, hg, add_zero]

end ActionFreedom

/-- Two positive local couplings give different weights on a nonflat field.
Thus the measure conditions alone do not select even this dynamical parameter. -/
theorem positive_action_couplings_distinct (s : ℝ) (hs : 0 < s) :
    Real.exp (-2 * s) < Real.exp (-s) := by
  apply Real.exp_lt_exp.mpr
  linarith

#print axioms weighted_ward_integral
#print axioms gradient_reference_cancellation
#print axioms seam_replacement
#print axioms marked_radius_transfer
#print axioms marked_diameter_transfer
#print axioms marked_exponential_transfer
#print axioms scalar_correction_split
#print axioms bounded_chain_rule_sum
#print axioms integrate_small_derivative
#print axioms local_response_preserved
#print axioms plaquette_action_gauge_invariant
#print axioms positive_action_couplings_distinct

end
end UnifiedTheory.Audit.KFCausalUniformReferenceLocality
