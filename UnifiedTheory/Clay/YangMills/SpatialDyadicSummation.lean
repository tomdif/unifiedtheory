/- Polynomial counting on the actual three-dimensional periodic spatial slice.
Dyadic fourth-power decay is summable with constants independent of the period.
This is geometry and summation, not a Wilson covariance decay assertion. -/
import UnifiedTheory.Clay.YangMills.WilsonGramNearFar
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SpatialDyadicSummation
noncomputable section
open WilsonTimeSlab

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _

def Close (r : ℕ) (e d : SpatialVertex n × Fin 3) : Prop :=
  ∀ i : Fin 3, ∃ t : ℤ, |t| ≤ (r : ℤ) ∧ d.1 i - e.1 i = (t : ZMod n)

def ball (r : ℕ) (e : SpatialVertex n × Fin 3) : Finset (SpatialVertex n × Fin 3) :=
  by classical exact Finset.univ.filter (Close n r e)

theorem mem_ball (r : ℕ) (e d : SpatialVertex n × Fin 3) :
    d ∈ ball n r e ↔ Close n r e d := by
  classical
  simp [ball]

theorem ball_mono (r s : ℕ) (hrs : r ≤ s) (e : SpatialVertex n × Fin 3) :
    ball n r e ⊆ ball n s e := by
  intro d hd
  rw [mem_ball] at hd ⊢
  intro i
  obtain ⟨t, ht, he⟩ := hd i
  exact ⟨t, ht.trans (by exact_mod_cast hrs), he⟩

theorem self_mem_ball (r : ℕ) (e : SpatialVertex n × Fin 3) : e ∈ ball n r e := by
  rw [mem_ball]
  exact fun _ => ⟨0, by simp, by simp⟩

theorem ball_period (e : SpatialVertex n × Fin 3) : ball n n e = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro d
  rw [mem_ball]
  intro i
  let z := d.1 i - e.1 i
  refine ⟨(z.val : ℤ), ?_, ?_⟩
  · rw [abs_of_nonneg (Int.natCast_nonneg _)]
    exact_mod_cast (ZMod.val_lt z).le
  · simpa only [Int.cast_natCast] using (ZMod.natCast_zmod_val z).symm

def offset (r : ℕ) (e : SpatialVertex n × Fin 3)
    (z : (Fin 3 → Fin (2 * r + 1)) × Fin 3) : SpatialVertex n × Fin 3 :=
  (fun i => e.1 i + ((z.1 i).val : ZMod n) - (r : ZMod n), z.2)

theorem ball_subset_offsets (r : ℕ) (e : SpatialVertex n × Fin 3) :
    ball n r e ⊆ Finset.univ.image (offset n r e) := by
  intro d hd
  rw [mem_ball] at hd
  choose t ht he using hd
  have ht0 (i : Fin 3) : 0 ≤ t i + (r : ℤ) := by
    have h := (abs_le.mp (ht i)).1
    omega
  let z : Fin 3 → Fin (2 * r + 1) := fun i =>
    ⟨(t i + (r : ℤ)).toNat, by
      have h := (abs_le.mp (ht i)).2
      omega⟩
  refine Finset.mem_image.mpr ⟨(z, d.2), Finset.mem_univ _, ?_⟩
  apply Prod.ext
  · funext i
    have hc : ((z i).val : ZMod n) = (t i : ZMod n) + (r : ZMod n) := by
      change (((t i + (r : ℤ)).toNat : ℕ) : ZMod n) = _
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (ht0 i), Int.cast_add, Int.cast_natCast]
    change e.1 i + ((z i).val : ZMod n) - (r : ZMod n) = d.1 i
    rw [hc, ← he i]
    ring
  · rfl

/-- Periodic collisions only decrease this count; no no-wrapping assumption is used. -/
theorem ball_card (r : ℕ) (e : SpatialVertex n × Fin 3) :
    (ball n r e).card ≤ 3 * (2 * r + 1) ^ 3 := by
  have h := (Finset.card_le_card (ball_subset_offsets n r e)).trans
    (Finset.card_image_le (f := offset n r e))
  simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, mul_comm] using h

theorem ball_one_card (e : SpatialVertex n × Fin 3) : (ball n 1 e).card ≤ 81 := by
  simpa using ball_card n 1 e

def shell (k : ℕ) (e : SpatialVertex n × Fin 3) : Finset (SpatialVertex n × Fin 3) :=
  ball n (2 ^ (k + 1)) e \ ball n (2 ^ k) e

theorem shell_card (k : ℕ) (e : SpatialVertex n × Fin 3) :
    (shell n k e).card ≤ 375 * 8 ^ k := by
  have hp : 1 ≤ (2 : ℕ) ^ k := Nat.one_le_pow k 2 (by norm_num)
  have hb : 2 * 2 ^ (k + 1) + 1 ≤ 5 * 2 ^ k := by
    rw [pow_succ]
    omega
  calc
    _ ≤ (ball n (2 ^ (k + 1)) e).card := Finset.card_le_card Finset.sdiff_subset
    _ ≤ 3 * (2 * 2 ^ (k + 1) + 1) ^ 3 := ball_card n _ e
    _ ≤ 3 * (5 * 2 ^ k) ^ 3 := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hb 3)
    _ = 375 * 8 ^ k := by rw [mul_pow, ← pow_mul, Nat.mul_comm k 3, pow_mul]; ring

theorem dyadic_covers (e : SpatialVertex n × Fin 3) :
    ball n (2 ^ n) e = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro d
  exact ball_mono n n (2 ^ n) (Nat.le_of_lt (Nat.lt_two_pow_self (n := n))) e
    (by rw [ball_period]; exact Finset.mem_univ d)

/-- The numerical shell ratio is one half: cubic volume times fourth-power decay. -/
theorem shell_sum (F : (SpatialVertex n × Fin 3) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (e : SpatialVertex n × Fin 3) (k : ℕ)
    (hF : ∀ d ∈ shell n k e, F d ≤ C * (1 / 16 : ℝ) ^ k) :
    (∑ d ∈ shell n k e, F d) ≤ 375 * C * (1 / 2 : ℝ) ^ k := by
  calc
    _ ≤ ∑ _d ∈ shell n k e, C * (1 / 16 : ℝ) ^ k := Finset.sum_le_sum hF
    _ = ((shell n k e).card : ℝ) * (C * (1 / 16 : ℝ) ^ k) := by simp
    _ ≤ (375 * (8 : ℝ) ^ k) * (C * (1 / 16 : ℝ) ^ k) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast shell_card n k e
    _ = 375 * C * (1 / 2 : ℝ) ^ k := by
      rw [show (375 * (8 : ℝ) ^ k) * (C * (1 / 16 : ℝ) ^ k) =
        375 * C * ((8 : ℝ) ^ k * (1 / 16 : ℝ) ^ k) by ring, ← mul_pow]
      norm_num

theorem ball_sum (F : (SpatialVertex n × Fin 3) → ℝ) (M C : ℝ)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (e : SpatialVertex n × Fin 3)
    (hlocal : ∀ d ∈ ball n 1 e, F d ≤ M)
    (hdecay : ∀ k d, d ∉ ball n (2 ^ k) e → F d ≤ C * (1 / 16 : ℝ) ^ k) (m : ℕ) :
    (∑ d ∈ ball n (2 ^ m) e, F d) ≤
      81 * M + 375 * C * ∑ k ∈ Finset.range m, (1 / 2 : ℝ) ^ k := by
  induction m with
  | zero =>
    simp only [pow_zero, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
    calc
      _ ≤ ∑ _d ∈ ball n 1 e, M := Finset.sum_le_sum hlocal
      _ = ((ball n 1 e).card : ℝ) * M := by simp
      _ ≤ 81 * M := mul_le_mul_of_nonneg_right (by exact_mod_cast ball_one_card n e) hM
  | succ m ih =>
    have hs := shell_sum n F C hC e m (fun d hd =>
      hdecay m d (Finset.mem_sdiff.mp hd).2)
    have hb : ball n (2 ^ m) e ⊆ ball n (2 ^ (m + 1)) e :=
      ball_mono n _ _ (Nat.pow_le_pow_right (by norm_num) (by omega)) e
    have he := Finset.sum_sdiff hb (f := F)
    change (∑ d ∈ shell n m e, F d) + _ = _ at he
    rw [Finset.sum_range_succ]
    linarith

/-- An actual finite torus of any size has this same bound. The decay premise
is deliberately polynomial and does not include a physical mass gap. -/
theorem sum_bound (F : (SpatialVertex n × Fin 3) → ℝ) (M C : ℝ)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (e : SpatialVertex n × Fin 3)
    (hlocal : ∀ d ∈ ball n 1 e, F d ≤ M)
    (hdecay : ∀ k d, d ∉ ball n (2 ^ k) e → F d ≤ C * (1 / 16 : ℝ) ^ k) :
    (∑ d, F d) ≤ 81 * M + 750 * C := by
  have h := ball_sum n F M C hM hC e hlocal hdecay n
  rw [dyadic_covers] at h
  have hg := mul_le_mul_of_nonneg_left (sum_geometric_two_le n)
    (show 0 ≤ 375 * C by positivity)
  linarith

end
end UnifiedTheory.Clay.YangMills.SpatialDyadicSummation
