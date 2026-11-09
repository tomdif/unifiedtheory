/- All translations and coordinate orientations of a reference patch share
one source-loss charge. The remaining volume price is explicit and multiplies
the kth-power pattern activity, rather than a one-defect activity. -/
import UnifiedTheory.Clay.YangMills.WilsonAffinePatchCover

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonAllPatchCounts
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundHeatBath
open WilsonPhysicalVariance WilsonHighFieldDecay
open SpatialPlaquetteCutGeometry SpatialWilsonPatchWeights
open WilsonPlaquetteColumnTail (rate rate_nonneg)

variable (n : ℕ) [NeZero n]

abbrev Index (A : Finset (Plaquette n)) (k : ℕ) :=
  Equiv.Perm (Fin 3) × (SpatialVertex (2 * n) × A.powersetCard k)

def frame (A : Finset (Plaquette n)) (k : ℕ) (i : Index n A k) :
    WilsonRawSymmetry.Symmetry (2 * n) :=
  WilsonPatchSymmetry.affine n i.1 i.2.1

def marked (A : Finset (Plaquette n)) (k : ℕ) (i : Index n A k) : Finset (Plaquette n) := i.2.2.val

theorem index_card (A : Finset (Plaquette n)) (k : ℕ) :
    Fintype.card (Index n A k) = 6 * (2 * n) ^ 3 * A.card.choose k := by
  simp only [Index, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin,
    Fintype.card_coe, Finset.card_powersetCard, SpatialVertex, Fintype.card_fun, ZMod.card]
  norm_num
  ring

omit [NeZero n] in
theorem marked_aligned (A : Finset (Plaquette n)) (hA : Aligned n A) (k : ℕ) (i : Index n A k) :
    Aligned n (marked n A k i) := fun p hp =>
  hA p ((Finset.mem_powersetCard.mp i.2.2.property).1 hp)

omit [NeZero n] in
theorem marked_card (A : Finset (Plaquette n)) (k : ℕ) (i : Index n A k) :
    (marked n A k i).card = k := (Finset.mem_powersetCard.mp i.2.2.property).2

def allBad (A : Finset (Plaquette n)) (R : ℝ) (k : ℕ) : Set (Slice (2 * n)) :=
  WilsonAffinePatchCover.bad n (frame n A k) (marked n A k) (fun _ => R)

/-- The common-cover event is exactly existence of a translated/oriented
patch with at least k hard defects. Repeated geometric frames cause no problem. -/
theorem mem_allBad (A : Finset (Plaquette n)) (R : ℝ) (k : ℕ) (u : Slice (2 * n)) :
    u ∈ allBad n A R k ↔ ∃ σ : Equiv.Perm (Fin 3), ∃ s : SpatialVertex (2 * n),
      (WilsonPatchSymmetry.affine n σ s).map u ∈ WilsonPatchCountTail.event n A R k := by
  simp only [allBad, WilsonAffinePatchCover.bad, Set.mem_setOf_eq, Index, Prod.exists,
    frame, marked, WilsonPatchCountTail.event_eq_union, WilsonPatchCover.bad]

theorem all_tail (A : Finset (Plaquette n)) (hA : Aligned n A)
    (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (hR : 0 < R) (k : ℕ) (f : C(Slice (2 * n), ℝ)) :
    (∫ u, (allBad n A R k).indicator (fun v => (f v) ^ 2) u ∂groundLaw (2 * n) β (by linarith)) ≤
      2 * loss (2 * n) β (by linarith) f +
        2 * (6 * (2 * n : ℝ) ^ 3) * (A.card.choose k : ℝ) * (rate β R) ^ k *
          mass (2 * n) β (by linarith) f := by
  have h := WilsonAffinePatchCover.weighted_union n β hβ (frame n A k) (marked n A k)
    (marked_aligned n A hA k) (fun _ => R) (fun _ => hR) f
  simpa only [marked_card, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, index_card,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using h

theorem all_decay (A : Finset (Plaquette n)) (hA : Aligned n A)
    (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (hR : 0 < R) (k : ℕ) (f : C(Slice (2 * n), ℝ))
    (hs : ∀ u, u ∉ allBad n A R k → f u = 0) :
    mass (2 * n) β (by linarith) (step (2 * n) β (by linarith) f) ≤
      (6 * (2 * n : ℝ) ^ 3) * (A.card.choose k : ℝ) * (rate β R) ^ k *
        mass (2 * n) β (by linarith) f := by
  have h := WilsonAffinePatchCover.union_decay n β hβ (frame n A k) (marked n A k)
    (marked_aligned n A hA k) (fun _ => R) (fun _ => hR) f hs
  simpa only [marked_card, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, index_card,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using h

theorem density_tail (A : Finset (Plaquette n)) (hA : Aligned n A)
    (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (hR : 0 < R) (b k : ℕ) (hk : A.card ≤ b * k)
    (f : C(Slice (2 * n), ℝ)) :
    (∫ u, (allBad n A R k).indicator (fun v => (f v) ^ 2) u ∂groundLaw (2 * n) β (by linarith)) ≤
      2 * loss (2 * n) β (by linarith) f +
        2 * (6 * (2 * n : ℝ) ^ 3) * ((2 : ℝ) ^ b * rate β R) ^ k *
          mass (2 * n) β (by linarith) f := by
  have ht := all_tail n A hA β hβ R hR k f
  have hb := mul_le_mul_of_nonneg_left
    (WilsonPatchCountTail.binomial_entropy A.card b k (rate β R) (rate_nonneg β R) hk)
    (show 0 ≤ 6 * (2 * n : ℝ) ^ 3 by positivity)
  have hc := mul_le_mul_of_nonneg_right hb (mass_nonneg (2 * n) β (by linarith) f)
  linarith

/-- All geometric frames retain a vanishing plaquette threshold and kth-power error. -/
theorem weak_coupling_tail (A : Finset (Plaquette n)) (hA : Aligned n A)
    (β : ℝ) (hβ : 1 < β) (b k : ℕ) (hk : A.card ≤ b * k) (f : C(Slice (2 * n), ℝ)) :
    (∫ u, (allBad n A (WilsonPlaquetteLocalLimit.threshold β) k).indicator
      (fun v => (f v) ^ 2) u ∂groundLaw (2 * n) β (by linarith)) ≤
      2 * loss (2 * n) β (by linarith) f +
        2 * (6 * (2 * n : ℝ) ^ 3) *
          (((2 : ℝ) ^ b * WilsonPlaquetteLocalLimit.coefficient) / β) ^ k *
            mass (2 * n) β (by linarith) f := by
  have h := density_tail n A hA β (by linarith) (WilsonPlaquetteLocalLimit.threshold β)
    (WilsonPlaquetteLocalLimit.threshold_pos β hβ) b k hk f
  simpa only [WilsonPlaquetteLocalLimit.rate_threshold β (by linarith), mul_div_assoc] using h

theorem density_decay (A : Finset (Plaquette n)) (hA : Aligned n A)
    (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (hR : 0 < R) (b k : ℕ) (hk : A.card ≤ b * k)
    (f : C(Slice (2 * n), ℝ)) (hs : ∀ u, u ∉ allBad n A R k → f u = 0) :
    mass (2 * n) β (by linarith) (step (2 * n) β (by linarith) f) ≤
      (6 * (2 * n : ℝ) ^ 3) * ((2 : ℝ) ^ b * rate β R) ^ k *
        mass (2 * n) β (by linarith) f := by
  have ht := all_decay n A hA β hβ R hR k f hs
  have hb := mul_le_mul_of_nonneg_left
    (WilsonPatchCountTail.binomial_entropy A.card b k (rate β R) (rate_nonneg β R) hk)
    (show 0 ≤ 6 * (2 * n : ℝ) ^ 3 by positivity)
  have hc := mul_le_mul_of_nonneg_right hb (mass_nonneg (2 * n) β (by linarith) f)
  linarith

/-- A kth-power activity can pay the whole translation/orientation volume price. -/
theorem volume_price (q c t : ℝ) (k : ℕ) (hq : 0 ≤ q) (hact : q ≤ Real.exp (-c))
    (hvol : Real.log (6 * (2 * n : ℝ) ^ 3) + t ≤ c * k) :
    (6 * (2 * n : ℝ) ^ 3) * q ^ k ≤ Real.exp (-t) := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
  have hp : 0 < 6 * (2 * n : ℝ) ^ 3 := by positivity
  calc
    _ ≤ (6 * (2 * n : ℝ) ^ 3) * (Real.exp (-c)) ^ k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hact k) hp.le
    _ = Real.exp (Real.log (6 * (2 * n : ℝ) ^ 3) + (k : ℝ) * (-c)) := by
      rw [Real.exp_add, Real.exp_log hp, Real.exp_nat_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem entropy_tail (A : Finset (Plaquette n)) (hA : Aligned n A)
    (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (hR : 0 < R) (b k : ℕ) (hk : A.card ≤ b * k)
    (c t : ℝ) (hact : (2 : ℝ) ^ b * rate β R ≤ Real.exp (-c))
    (hvol : Real.log (6 * (2 * n : ℝ) ^ 3) + t ≤ c * k) (f : C(Slice (2 * n), ℝ)) :
    (∫ u, (allBad n A R k).indicator (fun v => (f v) ^ 2) u ∂groundLaw (2 * n) β (by linarith)) ≤
      2 * loss (2 * n) β (by linarith) f +
        2 * Real.exp (-t) * mass (2 * n) β (by linarith) f := by
  have ht := density_tail n A hA β hβ R hR b k hk f
  have hp := volume_price n _ c t k (mul_nonneg (by positivity) (rate_nonneg β R)) hact hvol
  have hh := mul_le_mul_of_nonneg_right hp (mass_nonneg (2 * n) β (by linarith) f)
  linarith

theorem entropy_loss (A : Finset (Plaquette n)) (hA : Aligned n A)
    (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (hR : 0 < R) (b k : ℕ) (hk : A.card ≤ b * k)
    (c t : ℝ) (hact : (2 : ℝ) ^ b * rate β R ≤ Real.exp (-c))
    (hvol : Real.log (6 * (2 * n : ℝ) ^ 3) + t ≤ c * k) (f : C(Slice (2 * n), ℝ))
    (hs : ∀ u, u ∉ allBad n A R k → f u = 0) :
    (1 - Real.exp (-t)) * mass (2 * n) β (by linarith) f ≤ loss (2 * n) β (by linarith) f := by
  rw [loss_mass]
  have ht := density_decay n A hA β hβ R hR b k hk f hs
  have hp := volume_price n _ c t k (mul_nonneg (by positivity) (rate_nonneg β R)) hact hvol
  have hh := mul_le_mul_of_nonneg_right hp (mass_nonneg (2 * n) β (by linarith) f)
  linarith

end
end UnifiedTheory.Clay.YangMills.WilsonAllPatchCounts
