/- Actual normalized Gibbs fluctuation control on the fixed chord patch.
The product Haar distortion contributes log(81) per active link. The cap
complement and retained endpoint covariance remain separate obligations. -/
import UnifiedTheory.Clay.YangMills.WilsonChordPatchLaw
import UnifiedTheory.Clay.YangMills.CompactGibbsContractionMoment

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPatchFluctuation
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonJointRotation
open WilsonSpatialCutEnergy WilsonPatchNeighborhood WilsonChordPatchLaw
open WilsonBoundaryConnected
open QuaternionChordMidpoint
open scoped Quaternion NNReal ENNReal

variable (n : ℕ) [NeZero n]

theorem distance_continuous (z : Slice n) : Continuous (distanceSq n z) := by
  unfold distanceSq
  fun_prop

/-- The deterministic midpoint decrease is for the same map whose Haar
pushforward was bounded; it is not merely an existential midpoint. -/
theorem action_gain (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε ^ 2 < 2) (κ : ℝ) (hκ : 0 ≤ κ)
    (A : Slice n → ℝ) (z x : Coordinates n S v₀ ε)
    (hmin : IsMinOn A (region n S v₀ ε) (assemble n S v₀ ε z))
    (hsecond : ∀ m ∈ region n S v₀ ε, ∀ a : Slice n, (∀ e, e ∉ S → a e = 1) →
      κ * cost n a ≤ A (a * m) + A (a⁻¹ * m) - 2 * A m) :
    (κ / 4) * distanceSq n (assemble n S v₀ ε z) (assemble n S v₀ ε x) ≤
      A (assemble n S v₀ ε x) - A (assemble n S v₀ ε (contract n S v₀ ε hε z x)) := by
  let Z := assemble n S v₀ ε z
  let V := assemble n S v₀ ε x
  let M := assemble n S v₀ ε (contract n S v₀ ε hε z x)
  let a : Slice n := Z * M⁻¹
  have ha : ∀ e, e ∉ S → a e = 1 := by
    intro e he
    simp only [a, Z, M, Pi.mul_apply, Pi.inv_apply, assemble_outside n S v₀ ε _ e he,
      mul_inv_cancel]
  have hp : a * M = Z := by dsimp [a]; group
  have hm : a⁻¹ * M = V := by
    funext e
    by_cases he : e ∈ S
    · simpa only [a, Z, V, M, Pi.mul_apply, Pi.inv_apply, assemble_inside n S v₀ ε _ e he,
        contract, QuaternionCapContraction.contract] using
        midpoint_symmetric (z ⟨e, he⟩).1 (x ⟨e, he⟩).1
          (sum_ne_zero (z ⟨e, he⟩).1 (x ⟨e, he⟩).1 (v₀ e) ε hε
            (z ⟨e, he⟩).2 (x ⟨e, he⟩).2)
    · simp only [Pi.mul_apply, Pi.inv_apply, ha e he, inv_one, one_mul, M, V,
        assemble_outside n S v₀ ε _ e he]
  have hd : distanceSq n Z V ≤ 4 * cost n a := by
    unfold distanceSq cost
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    by_cases he : e ∈ S
    · simpa only [a, Z, V, M, displacement, Pi.mul_apply, Pi.inv_apply, rotation_chord,
        assemble_inside n S v₀ ε _ e he, contract, QuaternionCapContraction.contract] using
        midpoint_chord (z ⟨e, he⟩).1 (x ⟨e, he⟩).1
          (sum_ne_zero (z ⟨e, he⟩).1 (x ⟨e, he⟩).1 (v₀ e) ε hε
            (z ⟨e, he⟩).2 (x ⟨e, he⟩).2)
    · simp only [Z, V, assemble_outside n S v₀ ε _ e he, sub_self, norm_zero,
        zero_pow (by decide : 2 ≠ 0)]
      positivity
  have hM : M ∈ region n S v₀ ε := assemble_mem n S v₀ ε hε0 _
  have hh := hsecond M hM a ha
  rw [hp, hm] at hh
  have hminM : A Z ≤ A M := hmin hM
  have hmul := mul_le_mul_of_nonneg_left hd hκ
  change κ / 4 * distanceSq n Z V ≤ A V - A M
  nlinarith only [hh, hminM, hmul]

theorem exponential_moment (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε ^ 2 < 2) (κ : ℝ) (hκ : 0 ≤ κ)
    (A : Slice n → ℝ) (hA : Continuous A) (z : Coordinates n S v₀ ε)
    (hmin : IsMinOn A (region n S v₀ ε) (assemble n S v₀ ε z))
    (hsecond : ∀ m ∈ region n S v₀ ε, ∀ a : Slice n, (∀ e, e ∉ S → a e = 1) →
      κ * cost n a ≤ A (a * m) + A (a⁻¹ * m) - 2 * A m) :
    (∫ x, Real.exp ((κ / 4) * distanceSq n (assemble n S v₀ ε z) (assemble n S v₀ ε x))
      ∂law n S v₀ ε A) ≤ (81 : ℝ) ^ S.card := by
  letI := base_probability n S v₀ ε hε0
  have hh := CompactGibbsContractionMoment.exponential_moment (baseMeasure n S v₀ ε)
    (A ∘ assemble n S v₀ ε)
    (fun x => distanceSq n (assemble n S v₀ ε z) (assemble n S v₀ ε x))
    (hA.comp (assemble_continuous n S v₀ ε))
    ((distance_continuous n _).comp (assemble_continuous n S v₀ ε))
    (contract n S v₀ ε hε z) (contract_continuous n S v₀ ε hε z)
    ((81 : ℝ≥0) ^ S.card)
    (by simpa only [ENNReal.coe_pow, ENNReal.coe_ofNat] using
      contract_map_bound n S v₀ ε hε0 hε z)
    (κ / 4) (action_gain n S v₀ ε hε0.le hε κ hκ A z · hmin hsecond)
  simpa only [NNReal.coe_pow, NNReal.coe_ofNat] using hh

/-- A normalized expectation bound, linear in the number of active links
and inverse in the actual sourced curvature coefficient. -/
theorem mean_bound (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε ^ 2 < 2) (κ : ℝ) (hκ : 0 < κ)
    (A : Slice n → ℝ) (hA : Continuous A) (z : Coordinates n S v₀ ε)
    (hmin : IsMinOn A (region n S v₀ ε) (assemble n S v₀ ε z))
    (hsecond : ∀ m ∈ region n S v₀ ε, ∀ a : Slice n, (∀ e, e ∉ S → a e = 1) →
      κ * cost n a ≤ A (a * m) + A (a⁻¹ * m) - 2 * A m) :
    (∫ x, distanceSq n (assemble n S v₀ ε z) (assemble n S v₀ ε x) ∂law n S v₀ ε A) ≤
      4 * (S.card : ℝ) * Real.log 81 / κ := by
  letI := base_probability n S v₀ ε hε0
  have hh := CompactGibbsContractionMoment.mean_bound (baseMeasure n S v₀ ε)
    (A ∘ assemble n S v₀ ε)
    (fun x => distanceSq n (assemble n S v₀ ε z) (assemble n S v₀ ε x))
    (hA.comp (assemble_continuous n S v₀ ε))
    ((distance_continuous n _).comp (assemble_continuous n S v₀ ε))
    (contract n S v₀ ε hε z) (contract_continuous n S v₀ ε hε z)
    ((81 : ℝ≥0) ^ S.card) (by positivity)
    (by simpa only [ENNReal.coe_pow, ENNReal.coe_ofNat] using
      contract_map_bound n S v₀ ε hε0 hε z)
    (κ / 4) (by positivity) (action_gain n S v₀ ε hε0.le hε κ hκ.le A z · hmin hsecond)
  simp only [NNReal.coe_pow, NNReal.coe_ofNat, Real.log_pow] at hh
  convert hh using 1
  ring

/-- The previously constructed minimizer controls actual fluctuations of
the two-source Wilson law on the patch, not only minimizing configurations. -/
theorem action_fluctuation (β : ℝ) (hβ : 1 < β) (u w : Slice n)
    (e d : SpatialVertex n × Fin 3) (hed : e ≠ d) (q r : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (hflat : ∀ p b, b ∈ S → b ∈ support n p →
      ‖((spatialHolonomy v₀ p.1 p.2.1.1 p.2.1.2 : Q) : ℍ) - 1‖ ≤ 1 / 64)
    (hu : ∀ b ∈ S, ‖(v₀ b : ℍ) - (u b : ℍ)‖ ≤ 1 / 2)
    (hw : ∀ b ∈ S, ‖(v₀ b : ℍ) - (w b : ℍ)‖ ≤ 1 / 2) :
    ∃ v ∈ region n S v₀ (1 / 256),
      IsMinOn (WilsonTiltedMiddleAction.action n β u w e d q r s t)
        (region n S v₀ (1 / 256)) v ∧
      (∫ x, distanceSq n v (assemble n S v₀ (1 / 256) x)
        ∂law n S v₀ (1 / 256) (WilsonTiltedMiddleAction.action n β u w e d q r s t)) ≤
        2 * (S.card : ℝ) * Real.log 81 / (β - 1) := by
  obtain ⟨v, ⟨hv, hmin⟩, _⟩ := WilsonPatchMinimum.action_unique_minimum n β hβ u w e d hed
    q r hq hr s t hs ht S v₀ hflat hu hw
  refine ⟨v, hv, hmin, ?_⟩
  have hh := mean_bound n S v₀ (1 / 256) (by norm_num) (by norm_num)
    (2 * β - 2) (by linarith) _ (WilsonTiltedMiddleAction.action_continuous n β u w e d q r s t)
    (lift n S v₀ (1 / 256) v hv) (by rwa [assemble_lift])
    (fun m hm a ha => WilsonPatchSourceCurvature.action_second_patch n β (by linarith)
      u w e d hed q r hq hr s t hs ht S v₀ m a hm ha hflat hu hw)
  rw [assemble_lift] at hh
  convert hh using 1
  have h1 : β - 1 ≠ 0 := by linarith
  have h2 : 2 * β - 2 ≠ 0 := by linarith
  field_simp
  ring

/-- The full transported source interval has the same normalized
fluctuation bound with beta-2 in place of beta-1. -/
theorem transport_fluctuation (β : ℝ) (hβ : 2 < β) (u w : Slice n)
    (e d b : SpatialVertex n × Fin 3) (hed : e ≠ d) (q r p : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (hp : β * ‖(p : ℍ) - 1‖ ≤ 1)
    (s t h : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hh : h ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (hflat : ∀ z c, c ∈ S → c ∈ support n z →
      ‖((spatialHolonomy v₀ z.1 z.2.1.1 z.2.1.2 : Q) : ℍ) - 1‖ ≤ 1 / 64)
    (hu : ∀ c ∈ S, ‖(v₀ c : ℍ) - (u c : ℍ)‖ ≤ 1 / 2)
    (hw : ∀ c ∈ S, ‖(v₀ c : ℍ) - (w c : ℍ)‖ ≤ 1 / 2) :
    ∃ v ∈ region n S v₀ (1 / 256),
      IsMinOn (CompactGibbsSource.action
        (WilsonTiltedMiddleAction.action n β u w e d q r s t) (source n β b p w) h)
        (region n S v₀ (1 / 256)) v ∧
      (∫ x, distanceSq n v (assemble n S v₀ (1 / 256) x)
        ∂law n S v₀ (1 / 256) (CompactGibbsSource.action
          (WilsonTiltedMiddleAction.action n β u w e d q r s t) (source n β b p w) h)) ≤
        2 * (S.card : ℝ) * Real.log 81 / (β - 2) := by
  obtain ⟨v, ⟨hv, hmin⟩, _⟩ := WilsonPatchMinimum.transport_unique_minimum n β hβ u w
    e d b hed q r p hq hr hp s t h hs ht hh S v₀ hflat hu hw
  refine ⟨v, hv, hmin, ?_⟩
  have hA := CompactGibbsSource.action_continuous _ _
    (WilsonTiltedMiddleAction.action_continuous n β u w e d q r s t)
    (source_continuous n β b p w) h
  have hg := mean_bound n S v₀ (1 / 256) (by norm_num) (by norm_num)
    (2 * β - 4) (by linarith) _ hA (lift n S v₀ (1 / 256) v hv)
    (by rwa [assemble_lift])
    (fun m hm a ha => WilsonPatchSourceCurvature.transport_second_patch n β (by linarith)
      u w e d b hed q r p hq hr hp s t h hs ht hh S v₀ m a hm ha hflat hu hw)
  rw [assemble_lift] at hg
  convert hg using 1
  have h1 : β - 2 ≠ 0 := by linarith
  have h2 : 2 * β - 4 ≠ 0 := by linarith
  field_simp
  ring

end
end UnifiedTheory.Clay.YangMills.WilsonPatchFluctuation
