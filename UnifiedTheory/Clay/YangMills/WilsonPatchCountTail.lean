/- Actual defect counts on a common reflection plane. The simultaneous
pattern bound pays the binomial entropy while charging source loss once.
The resulting exponent is proportional to the number of marked defects. -/
import UnifiedTheory.Clay.YangMills.WilsonPatchCover
import UnifiedTheory.Clay.YangMills.WilsonPlaquetteLocalLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPatchCountTail
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonGroundHeatBath
open WilsonPhysicalVariance WilsonHighFieldDecay
open SpatialPlaquetteCutGeometry SpatialWilsonPatchWeights
open SpatialWilsonPlaquetteKernels (defect)
open WilsonPlaquetteColumnTail (rate rate_nonneg)

variable (n : ℕ) [NeZero n]

def large (A : Finset (Plaquette n)) (R : ℝ) (u : Slice (2 * n)) : Finset (Plaquette n) := by
  classical
  exact A.filter (fun p => 2 * R ≤ defect n p u)

def event (A : Finset (Plaquette n)) (R : ℝ) (k : ℕ) : Set (Slice (2 * n)) :=
  {u | k ≤ (large n A R u).card}

omit [NeZero n] in
theorem event_eq_union (A : Finset (Plaquette n)) (R : ℝ) (k : ℕ) :
    event n A R k = WilsonPatchCover.bad n (fun S : A.powersetCard k => S.val) (fun _ => R) := by
  classical
  ext u
  constructor
  · intro hu
    obtain ⟨S,hS,hk⟩ := Finset.exists_subset_card_eq hu
    have hA : S ⊆ A := hS.trans (Finset.filter_subset _ A)
    refine ⟨⟨S,Finset.mem_powersetCard.mpr ⟨hA,hk⟩⟩,?_⟩
    intro p
    exact (Finset.mem_filter.mp (hS p.property)).2
  · rintro ⟨S,hS⟩
    have hsub : S.val ⊆ large n A R u := by
      intro p hp
      exact Finset.mem_filter.mpr ⟨(Finset.mem_powersetCard.mp S.property).1 hp,hS ⟨p,hp⟩⟩
    have hc := Finset.card_le_card hsub
    rwa [(Finset.mem_powersetCard.mp S.property).2] at hc

theorem event_measurable (A : Finset (Plaquette n)) (R : ℝ) (k : ℕ) :
    MeasurableSet (event n A R k) := by
  rw [event_eq_union]
  exact WilsonPatchCover.bad_measurable n _ _

/-- The source-sensitive bound uses the actual binomial number of candidates. -/
theorem binomial_tail (A : Finset (Plaquette n)) (hA : Aligned n A)
    (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (hR : 0 < R) (k : ℕ) (f : C(Slice (2 * n), ℝ)) :
    (∫ u, (event n A R k).indicator (fun v => (f v) ^ 2) u ∂groundLaw (2 * n) β (by linarith)) ≤
      2 * loss (2 * n) β (by linarith) f +
        2 * (A.card.choose k : ℝ) * (rate β R) ^ k * mass (2 * n) β (by linarith) f := by
  have h := WilsonPatchCover.same_size_tail n β hβ (fun S : A.powersetCard k => S.val)
    (fun S p hp => hA p ((Finset.mem_powersetCard.mp S.property).1 hp)) k
    (fun S => (Finset.mem_powersetCard.mp S.property).2) R hR f
  rw [event_eq_union]
  simpa only [Fintype.card_coe, Finset.card_powersetCard] using h

theorem binomial_decay (A : Finset (Plaquette n)) (hA : Aligned n A)
    (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (f : C(Slice (2 * n), ℝ)) (hs : ∀ u, u ∉ event n A R k → f u = 0) :
    mass (2 * n) β (by linarith) (step (2 * n) β (by linarith) f) ≤
      (A.card.choose k : ℝ) * (rate β R) ^ k * mass (2 * n) β (by linarith) f := by
  have h := WilsonPatchCover.union_decay n β hβ (fun S : A.powersetCard k => S.val)
    (fun S p hp => hA p ((Finset.mem_powersetCard.mp S.property).1 hp))
    (fun _ => R) (fun _ => hR) f (by simpa only [← event_eq_union] using hs)
  have he (S : A.powersetCard k) : S.val.card = k := (Finset.mem_powersetCard.mp S.property).2
  simpa only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_coe, Finset.card_powersetCard] using h

omit n [NeZero n] in
/-- An explicit entropy budget for a fraction 1/b of marked defects. -/
theorem binomial_entropy (M b k : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) (hM : M ≤ b * k) :
    (M.choose k : ℝ) * ρ ^ k ≤ ((2 : ℝ) ^ b * ρ) ^ k := by
  have hc : (M.choose k : ℝ) ≤ (2 : ℝ) ^ M := by exact_mod_cast Nat.choose_le_two_pow M k
  have hp : (2 : ℝ) ^ M ≤ ((2 : ℝ) ^ b) ^ k := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) hM
  have hh := mul_le_mul_of_nonneg_right (hc.trans hp) (pow_nonneg hρ k)
  simpa only [mul_pow] using hh

/-- At least k defects among at most b*k candidates have exponential mass error. -/
theorem density_tail (A : Finset (Plaquette n)) (hA : Aligned n A)
    (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (hR : 0 < R) (b k : ℕ) (hk : A.card ≤ b * k)
    (f : C(Slice (2 * n), ℝ)) :
    (∫ u, (event n A R k).indicator (fun v => (f v) ^ 2) u ∂groundLaw (2 * n) β (by linarith)) ≤
      2 * loss (2 * n) β (by linarith) f +
        2 * ((2 : ℝ) ^ b * rate β R) ^ k * mass (2 * n) β (by linarith) f := by
  have ht := binomial_tail n A hA β hβ R hR k f
  have hb := mul_le_mul_of_nonneg_right (binomial_entropy A.card b k (rate β R)
    (rate_nonneg β R) hk) (mass_nonneg (2 * n) β (by linarith) f)
  linarith

theorem density_loss (A : Finset (Plaquette n)) (hA : Aligned n A)
    (β : ℝ) (hβ : 3 / 4 ≤ β) (R : ℝ) (hR : 0 < R) (b k : ℕ) (hk : A.card ≤ b * k)
    (f : C(Slice (2 * n), ℝ)) (hs : ∀ u, u ∉ event n A R k → f u = 0) :
    (1 - ((2 : ℝ) ^ b * rate β R) ^ k) * mass (2 * n) β (by linarith) f ≤
      loss (2 * n) β (by linarith) f := by
  rw [loss_mass]
  have ht := binomial_decay n A hA β hβ R hR k f hs
  have hb := mul_le_mul_of_nonneg_right (binomial_entropy A.card b k (rate β R)
    (rate_nonneg β R) hk) (mass_nonneg (2 * n) β (by linarith) f)
  linarith

/-- The hard defect threshold tends to zero while the count error retains
its kth power. The area/volume is not substituted into the one-defect rate. -/
theorem weak_coupling_tail (A : Finset (Plaquette n)) (hA : Aligned n A)
    (β : ℝ) (hβ : 1 < β) (b k : ℕ) (hk : A.card ≤ b * k) (f : C(Slice (2 * n), ℝ)) :
    (∫ u, (event n A (WilsonPlaquetteLocalLimit.threshold β) k).indicator
      (fun v => (f v) ^ 2) u ∂groundLaw (2 * n) β (by linarith)) ≤
      2 * loss (2 * n) β (by linarith) f +
        2 * (((2 : ℝ) ^ b * WilsonPlaquetteLocalLimit.coefficient) / β) ^ k *
          mass (2 * n) β (by linarith) f := by
  have h := density_tail n A hA β (by linarith) (WilsonPlaquetteLocalLimit.threshold β)
    (WilsonPlaquetteLocalLimit.threshold_pos β hβ) b k hk f
  simpa only [WilsonPlaquetteLocalLimit.rate_threshold β (by linarith), mul_div_assoc] using h

end
end UnifiedTheory.Clay.YangMills.WilsonPatchCountTail
