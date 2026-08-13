/-
  Audit/KFCausalReplicaOverlap.lean

  THE REPLICA-OVERLAP STRUCTURE OF THE COHERENT MEASURE:
  OVERLAP = PARTICIPATION RATIO, AND
  COHERENT = BORN x EFFECTIVE HISTORY MULTIPLICITY

  Context.  Phase telescoping (KFCausalCoherentRecordAccretion) makes
  the class-identified coherent measure Q(C) = R(C)^2 with R a
  positive path sum.  The replica-doubling test (2026-08-13) refuted
  the naive independent-replica law and exposed the true structure,
  verified exactly in replica_overlap_deep.py and formalized here:

  1. `overlap_eq_participation_ratio` — the event-level replica
     overlap c(A) = f_Q(A)/f_R(A)^2 equals EXACTLY the ratio of
     participation numbers N(Omega)/N(A), N(X) = (sum_X R)^2 /
     sum_X R^2 = the effective number of geometry classes carrying
     the measure in X.  "Two worlds agree on a rare event more often
     than chance" = "rare events are carried by fewer effective
     geometries than the world at large."
  2. `participation_ge_one` / `participation_le_card` — the
     participation number is pinched: 1 <= N(X) <= |X| (left:
     square-superadditivity of nonnegative aggregation, reused from
     the accretion file; right: Cauchy-Schwarz).
  3. `overlap_bounds` — hence N(Omega)/|A| <= c(A) <= N(Omega):
     overlap growth is bounded by effective-geometry growth.
  4. `coherent_eq_born_mul_multiplicity` — per class, Q(C) =
     P(C) * Neff(C) with Neff(C) = R(C)^2/W(C); summed:
     Q(Omega) = sum_C P(C) * Neff(C), i.e. THE ANTI-DECOHERENCE RATE
     IS THE MEAN EFFECTIVE HISTORY COUNT, Q(Omega)/P(Omega) =
     E_P[Neff].  With R(C), W(C) the SAME nonnegative path family
     summed linearly resp. quadratically, Neff is that family's
     participation number, so `participation` bounds give
     1 <= Neff(C) <= #paths(C): the coherent measure is the Born
     measure reweighted by a dynamically computed history
     multiplicity — the history-counting axiom made dynamical.

  Measured companions (replica_overlap_deep.log): identities exact;
  overlap exponents obey gamma_A ~ -0.7 a_R with corr = -0.974 over
  12 events (the empirical scaling law f_Q ~ f_R^{1.3} replacing the
  refuted doubling); E_P[Neff] grows x3.3 per element;
  corr(ln Neff, ln P) -> +0.70.

  Zero sorry.  Zero custom axioms.
-/
import UnifiedTheory.Audit.KFCausalCoherentRecordAccretion
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalReplicaOverlap

open UnifiedTheory.Audit.KFCausalCoherentRecordAccretion
open Finset

variable {ι : Type}

/-- Participation number of a nonnegative weight family on a finite
set: the effective number of carriers of the measure. -/
noncomputable def participation (s : Finset ι) (R : ι → ℝ) : ℝ :=
  (∑ i ∈ s, R i) ^ 2 / ∑ i ∈ s, R i ^ 2

/-- `N(X) >= 1`: aggregation of nonnegative weights is
square-superadditive (reused accretion lemma). -/
theorem participation_ge_one (s : Finset ι) (R : ι → ℝ)
    (hR : ∀ i ∈ s, 0 ≤ R i) (hpos : 0 < ∑ i ∈ s, R i ^ 2) :
    1 ≤ participation s R := by
  rw [participation, le_div_iff₀ hpos, one_mul]
  exact sq_sum_ge_sum_sq s R hR

/-- `N(X) <= |X|`: Cauchy–Schwarz with the constant family. -/
theorem participation_le_card (s : Finset ι) (R : ι → ℝ)
    (hpos : 0 < ∑ i ∈ s, R i ^ 2) :
    participation s R ≤ s.card := by
  rw [participation, div_le_iff₀ hpos]
  have h : (∑ i ∈ s, R i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, R i ^ 2 := by
    exact_mod_cast sq_sum_le_card_mul_sum_sq (s := s) (f := R)
  exact h

/-- THE OVERLAP IDENTITY.  The event-level replica overlap
`c(A) = (Q-fraction of A) / (R-fraction of A)^2` equals the ratio of
participation numbers `N(Omega) / N(A)`: replica correlation IS
effective-geometry counting. -/
theorem overlap_eq_participation_ratio
    (Ω A : Finset ι) (R : ι → ℝ)
    (hA1 : 0 < ∑ i ∈ A, R i) (hΩ1 : 0 < ∑ i ∈ Ω, R i)
    (hA2 : 0 < ∑ i ∈ A, R i ^ 2) (hΩ2 : 0 < ∑ i ∈ Ω, R i ^ 2) :
    ((∑ i ∈ A, R i ^ 2) / ∑ i ∈ Ω, R i ^ 2) /
      ((∑ i ∈ A, R i) / ∑ i ∈ Ω, R i) ^ 2 =
    participation Ω R / participation A R := by
  rw [participation, participation]
  field_simp

/-- Overlap is pinched by effective-geometry counts:
`N(Omega)/|A| <= c(A) <= N(Omega)`. -/
theorem overlap_bounds
    (Ω A : Finset ι) (R : ι → ℝ) (hR : ∀ i ∈ A, 0 ≤ R i)
    (hA1 : 0 < ∑ i ∈ A, R i) (hΩ1 : 0 < ∑ i ∈ Ω, R i)
    (hA2 : 0 < ∑ i ∈ A, R i ^ 2) (hΩ2 : 0 < ∑ i ∈ Ω, R i ^ 2)
    (hcard : 0 < (A.card : ℝ)) :
    participation Ω R / A.card ≤
      ((∑ i ∈ A, R i ^ 2) / ∑ i ∈ Ω, R i ^ 2) /
        ((∑ i ∈ A, R i) / ∑ i ∈ Ω, R i) ^ 2 ∧
    ((∑ i ∈ A, R i ^ 2) / ∑ i ∈ Ω, R i ^ 2) /
        ((∑ i ∈ A, R i) / ∑ i ∈ Ω, R i) ^ 2 ≤
      participation Ω R := by
  rw [overlap_eq_participation_ratio Ω A R hA1 hΩ1 hA2 hΩ2]
  have hNA1 : 1 ≤ participation A R := participation_ge_one A R hR hA2
  have hNAc : participation A R ≤ A.card := participation_le_card A R hA2
  have hNApos : 0 < participation A R := lt_of_lt_of_le one_pos hNA1
  have hNΩpos : 0 < participation Ω R := by
    rw [participation]
    exact div_pos (pow_pos hΩ1 2) hΩ2
  constructor
  · exact div_le_div_of_nonneg_left hNΩpos.le hNApos hNAc
  · calc participation Ω R / participation A R ≤
        participation Ω R / 1 :=
          div_le_div_of_nonneg_left hNΩpos.le one_pos hNA1
      _ = participation Ω R := div_one _

/-- COHERENT = BORN x MULTIPLICITY, per class: with `W C > 0`,
`R C ^ 2 = W C * (R C ^ 2 / W C)`; summed over classes,
`Q(Omega) = sum_C P(C) * Neff(C)` — the anti-decoherence rate is the
mean effective history count. -/
theorem coherent_eq_born_mul_multiplicity
    (s : Finset ι) (R W : ι → ℝ) (hW : ∀ i ∈ s, 0 < W i) :
    ∑ i ∈ s, R i ^ 2 = ∑ i ∈ s, W i * (R i ^ 2 / W i) := by
  refine Finset.sum_congr rfl fun i hi => ?_
  field_simp [ne_of_gt (hW i hi)]

/-- The multiplicity is a genuine effective count: if `R` and `W` are
the linear and quadratic sums of one nonnegative path family `x`,
then `1 <= R^2/W <= #paths` (participation bounds applied to the
paths within a class). -/
theorem multiplicity_bounds {κ : Type} (paths : Finset κ) (x : κ → ℝ)
    (hx : ∀ j ∈ paths, 0 ≤ x j)
    (hpos : 0 < ∑ j ∈ paths, x j ^ 2) :
    1 ≤ (∑ j ∈ paths, x j) ^ 2 / ∑ j ∈ paths, x j ^ 2 ∧
    (∑ j ∈ paths, x j) ^ 2 / ∑ j ∈ paths, x j ^ 2 ≤ paths.card :=
  ⟨participation_ge_one paths x hx hpos,
   participation_le_card paths x hpos⟩

#print axioms participation_ge_one
#print axioms participation_le_card
#print axioms overlap_eq_participation_ratio
#print axioms overlap_bounds
#print axioms coherent_eq_born_mul_multiplicity
#print axioms multiplicity_bounds

end UnifiedTheory.Audit.KFCausalReplicaOverlap
