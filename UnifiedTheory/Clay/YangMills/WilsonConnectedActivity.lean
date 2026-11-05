/- Explicit rooted connected-plaquette activity sums. The geometric entropy
constant is 256 and the final bound is independent of the spatial period. -/
import UnifiedTheory.Clay.YangMills.WilsonPlaquetteGraph
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonConnectedActivity
noncomputable section
open WilsonTimeSlab WilsonPlaquetteGraph

def budget (ρ : ℝ) (m : ℕ) : ℝ := ρ * (256 * ρ)^(m - 1) / (1 - 256 * ρ)

variable (N : ℕ) [NeZero N]

abbrev Index (p : Plaquettes N) (m L : ℕ) :=
  Σ j : Fin L, rooted N p (m + j.val)

def marked (p : Plaquettes N) (m L : ℕ) (i : Index N p m L) : Finset (Plaquettes N) := i.2.val

theorem marked_spec (p : Plaquettes N) (m L : ℕ) (i : Index N p m L) :
    p ∈ marked N p m L i ∧ (marked N p m L i).card = m + i.1.val ∧
      ((graph N).induce (marked N p m L i : Set (Plaquettes N))).Preconnected :=
  (FiniteConnectedCount.rooted_mem (graph N) p _ _).mp i.2.property

theorem marked_card (p : Plaquettes N) (m L : ℕ) (i : Index N p m L) :
    (marked N p m L i).card = m + i.1.val := (marked_spec N p m L i).2.1

/-- The finite index at the full lattice cardinality includes every rooted
connected set of size at least m, and no other set. -/
theorem exists_index (p : Plaquettes N) (m : ℕ) (S : Finset (Plaquettes N)) :
    (∃ i : Index N p m (Fintype.card (Plaquettes N) + 1),
      marked N p m _ i = S) ↔
      p ∈ S ∧ m ≤ S.card ∧ ((graph N).induce (S : Set (Plaquettes N))).Preconnected := by
  classical
  constructor
  · rintro ⟨i,rfl⟩
    obtain ⟨hp,hcard,hconn⟩ := marked_spec N p m _ i
    exact ⟨hp,by omega,hconn⟩
  · rintro ⟨hp,hm,hconn⟩
    have hc := Finset.card_le_univ S
    let j : Fin (Fintype.card (Plaquettes N) + 1) := ⟨S.card - m,by omega⟩
    have hk : m + j.val = S.card := by dsimp [j]; omega
    refine ⟨⟨j,⟨S,?_⟩⟩,rfl⟩
    exact (FiniteConnectedCount.rooted_mem (graph N) p _ S).mpr ⟨hp,hk.symm,hconn⟩

theorem activity_sum (p : Plaquettes N) (m L : ℕ) (ρ : ℝ) :
    (∑ i : Index N p m L, ρ ^ (marked N p m L i).card) =
      ∑ j : Fin L, ((rooted N p (m + j.val)).card : ℝ) * ρ^(m + j.val) := by
  simp only [marked_card, Index, Fintype.sum_sigma, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Fintype.card_coe]

omit N [NeZero N] in
theorem activity_term (ρ : ℝ) (m j : ℕ) (hm : 0 < m) :
    (256 : ℝ)^(m + j - 1) * ρ^(m + j) =
      ρ * (256 * ρ)^(m - 1) * (256 * ρ)^j := by
  have he : m + j - 1 = (m - 1) + j := by omega
  have hf : m + j = 1 + ((m - 1) + j) := by omega
  rw [he, hf]
  simp only [pow_add, pow_one, mul_pow]
  ring

/-- The sum over all rooted sizes m through m+L-1 obeys a uniform geometric bound. -/
theorem activity_bound (p : Plaquettes N) (m L : ℕ) (hm : 0 < m)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hsmall : 256 * ρ < 1) :
    (∑ i : Index N p m L, ρ^(marked N p m L i).card) ≤
      budget ρ m := by
  unfold budget
  rw [activity_sum]
  have hc (j : Fin L) : ((rooted N p (m + j.val)).card : ℝ) ≤
      (256 : ℝ)^(m + j.val - 1) := by exact_mod_cast rooted_card N p (m + j.val)
  have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_right (hc j) (pow_nonneg hρ (m + j.val)))
  simp_rw [activity_term ρ m _ hm] at h
  rw [← Finset.mul_sum] at h
  apply h.trans
  have hg : (∑ j : Fin L, (256 * ρ)^j.val) ≤ 1 / (1 - 256 * ρ) := by
    simpa only [Fin.sum_univ_eq_sum_range, Nat.Ico_zero_eq_range, pow_zero] using
      (geom_sum_Ico_le_of_lt_one (m := 0) (n := L)
        (show 0 ≤ 256 * ρ by positivity) hsmall)
  simpa only [one_div, div_eq_mul_inv, mul_assoc, one_mul] using
    mul_le_mul_of_nonneg_left hg
      (mul_nonneg hρ (pow_nonneg (show 0 ≤ 256 * ρ by positivity) (m - 1)))

end
end UnifiedTheory.Clay.YangMills.WilsonConnectedActivity
