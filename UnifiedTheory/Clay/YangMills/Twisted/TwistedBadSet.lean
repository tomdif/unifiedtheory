/- The covariant block bound with its hypothesis localized. Plaquettes with defect above `δ` are bad.
On fluctuations that vanish on the links of bad plaquettes, the block-scale bound holds with no condition
on the bad plaquettes at all. The action tail bounds the number of bad plaquettes per link, with no
dependence on the volume, except on an event of probability exponentially small in the volume. So the
bound holds on a subspace whose codimension is a small fraction, uniform in `N`, of all directions. The
remaining directions may be negative, and nothing here controls them. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedCovariant

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedBadSet
noncomputable section
open PeriodicLattice4 TwistedFlat CommutingShifts TwistedHessian TwistedActionJet TwistedSmallField
open TwistedStability TwistedLandau TwistedLocalization TwistedReflection TwistedHessianField BlockShifts
open TwistedCovariant
open PeriodicPlaquetteReflection PeriodicTimeReflection RegulatedGauge
open WilsonSingleLinkStaples (Q character character_re)
open scoped Quaternion RealInnerProductSpace
open Classical

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

/-- Plaquettes with defect above `δ`. -/
def badPlaq (U : V' → Fin 4 → Q) (δ : ℝ) : Finset (PlaquetteIndex (2 * n)) :=
  Finset.univ.filter fun p => δ < defect U p.2.1.1 p.2.1.2 p.1

/-- The links of a plaquette. -/
def plaqLinks (p : PlaquetteIndex (2 * n)) : Finset (V' × Fin 4) :=
  {(p.1, p.2.1.1), (step (2 * n) p.1 p.2.1.1, p.2.1.2), (step (2 * n) p.1 p.2.1.2, p.2.1.1),
    (p.1, p.2.1.2)}

/-- The links touching a bad plaquette. -/
def badLinks (U : V' → Fin 4 → Q) (δ : ℝ) : Finset (V' × Fin 4) :=
  (badPlaq n U δ).biUnion (plaqLinks n)

theorem card_badLinks_le (U : V' → Fin 4 → Q) (δ : ℝ) :
    (badLinks n U δ).card ≤ 4 * (badPlaq n U δ).card := by
  have h := Finset.card_biUnion_le_card_mul (badPlaq n U δ) (plaqLinks n) 4
    fun p _ => Finset.card_le_four
  exact h.trans_eq (Nat.mul_comm _ _)

theorem card_badPlaq_le (U : V' → Fin 4 → Q) (δ : ℝ) (hδ0 : 0 ≤ δ) :
    ((badPlaq n U δ).card : ℝ) * δ ^ 2 ≤ actionL U := by
  have h1 : ∑ p ∈ badPlaq n U δ, δ ^ 2 ≤ ∑ p ∈ badPlaq n U δ, defect U p.2.1.1 p.2.1.2 p.1 ^ 2 := by
    refine Finset.sum_le_sum fun p hp => ?_
    have := (Finset.mem_filter.1 hp).2
    exact pow_le_pow_left₀ hδ0 this.le 2
  have h2 : ∑ p ∈ badPlaq n U δ, defect U p.2.1.1 p.2.1.2 p.1 ^ 2 ≤ actionL U :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  exact h1.trans h2

/-- The direction vanishes on the links of bad plaquettes. -/
def Avoids (U : V' → Fin 4 → Q) (δ : ℝ) (X : Fin 3 → Fin 4 → Section (2 * n)) : Prop :=
  ∀ l ∈ badLinks n U δ, imag X l.2 l.1 = 0

/-- The four vanishing statements for one bad plaquette. -/
theorem avoids_plaq (U : V' → Fin 4 → Q) (δ : ℝ) (X : Fin 3 → Fin 4 → Section (2 * n))
    (hX : Avoids n U δ X) (x : V') (μ ν : Fin 4) (h : μ < ν) (hb : δ < defect U μ ν x) :
    imag X μ x = 0 ∧ imag X ν (step (2 * n) x μ) = 0 ∧ imag X μ (step (2 * n) x ν) = 0 ∧
      imag X ν x = 0 := by
  have hp : ((x, ⟨(μ, ν), h⟩) : PlaquetteIndex (2 * n)) ∈ badPlaq n U δ :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩
  have hl (l : V' × Fin 4) (hm : l ∈ plaqLinks n ((x, ⟨(μ, ν), h⟩) : PlaquetteIndex (2 * n))) :
      imag X l.2 l.1 = 0 := hX l (Finset.mem_biUnion.2 ⟨_, hp, hm⟩)
  refine ⟨hl (x, μ) ?_, hl (step (2 * n) x μ, ν) ?_, hl (step (2 * n) x ν, μ) ?_, hl (x, ν) ?_⟩ <;>
    simp [plaqLinks]

theorem Ad_zero (u : Q) : Ad u 0 = 0 := by
  simp [Ad]

/-! ### The local commutator bound -/

/-- The defect of the plaquette in the plane of `μ, ν`, in either order. -/
def pd (U : V' → Fin 4 → Q) (μ ν : Fin 4) (z : V') : ℝ :=
  if μ < ν then defect U μ ν z else if ν < μ then defect U ν μ z else 0

theorem pd_nonneg (U : V' → Fin 4 → Q) (μ ν : Fin 4) (z : V') : 0 ≤ pd n U μ ν z := by
  unfold pd
  split_ifs
  · exact defect_nonneg _ _ _ _
  · exact defect_nonneg _ _ _ _
  · exact le_rfl

theorem comm_lt (U : V' → Fin 4 → Q) (μ ν : Fin 4) (u : QField (2 * n)) (z : V') :
    ‖Ad (U z μ) (Ad (U (step (2 * n) z μ) ν) (u (step (2 * n) (step (2 * n) z ν) μ))) -
        Ad (U z ν) (Ad (U (step (2 * n) z ν) μ) (u (step (2 * n) (step (2 * n) z ν) μ)))‖ ≤
      2 * defect U μ ν z * ‖u (step (2 * n) (step (2 * n) z ν) μ)‖ := by
  rw [← Ad_mul, ← Ad_mul]
  set a := U z μ
  set b := U (step (2 * n) z μ) ν
  set c := U (step (2 * n) z ν) μ
  set e := U z ν
  set v := u (step (2 * n) (step (2 * n) z ν) μ)
  have hP : a * b = (a * b * c⁻¹ * e⁻¹) * (e * c) := by group
  rw [hP, Ad_mul]
  have hc := Ad_close (a * b * c⁻¹ * e⁻¹) (twistExp μ ν z) (Ad (e * c) v)
  rw [norm_Ad] at hc
  exact hc

theorem comm_pointwise (U : V' → Fin 4 → Q) (μ ν : Fin 4) (u : QField (2 * n)) (z : V') :
    ‖(covT U μ (covT U ν u) - covT U ν (covT U μ u)) z‖ ≤
      2 * pd n U μ ν z * ‖u (step (2 * n) (step (2 * n) z ν) μ)‖ := by
  have e : (covT U μ (covT U ν u) - covT U ν (covT U μ u)) z =
      Ad (U z μ) (Ad (U (step (2 * n) z μ) ν) (u (step (2 * n) (step (2 * n) z μ) ν))) -
        Ad (U z ν) (Ad (U (step (2 * n) z ν) μ) (u (step (2 * n) (step (2 * n) z ν) μ))) := rfl
  rw [e]
  rcases lt_trichotomy μ ν with h | h | h
  · rw [step_step_comm z μ ν]
    have := comm_lt n U μ ν u z
    simpa only [pd, h, if_true] using this
  · subst h
    simp only [sub_self, norm_zero]
    have := pd_nonneg n U μ μ z
    positivity
  · rw [norm_sub_rev, step_step_comm z μ ν]
    have := comm_lt n U ν μ u z
    rw [step_step_comm z μ ν] at this
    have hnl : ¬ μ < ν := not_lt.2 h.le
    simpa only [pd, hnl, h, if_true, if_false] using this

/-- If `y` vanishes where the plaquette is bad, the commutator acts as if all defects were at most `δ`. -/
theorem cross_local (U : V' → Fin 4 → Q) (δ : ℝ) (hδ0 : 0 ≤ δ) (μ ν : Fin 4) (u y : QField (2 * n))
    (hy : ∀ z, δ < pd n U μ ν z → y (step (2 * n) z μ) = 0) :
    |⟪covT U μ (covT U ν u) - covT U ν (covT U μ u), covT U μ y⟫| ≤ 2 * δ * ‖u‖ * ‖y‖ := by
  set W := covT U μ (covT U ν u) - covT U ν (covT U μ u) with hW
  let Wt : QField (2 * n) := WithLp.toLp 2 fun z => if pd n U μ ν z ≤ δ then W z else 0
  have hin : ⟪W, covT U μ y⟫ = ⟪Wt, covT U μ y⟫ := by
    rw [PiLp.inner_apply, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun z _ => ?_
    change _ = ⟪if pd n U μ ν z ≤ δ then W z else 0, covT U μ y z⟫
    split_ifs with hz
    · rfl
    · rw [covT_apply, hy z (not_le.1 hz), Ad_zero, inner_zero_right, inner_zero_right]
  have hn : ‖Wt‖ ≤ 2 * δ * ‖u‖ := by
    refine norm_le_of_pointwise Wt u ((stepEquiv (N := 2 * n) ν).trans (stepEquiv μ)) _
      (by positivity) fun z => ?_
    change ‖if pd n U μ ν z ≤ δ then W z else 0‖ ≤ 2 * δ * ‖u (step (2 * n) (step (2 * n) z ν) μ)‖
    split_ifs with hz
    · refine (comm_pointwise n U μ ν u z).trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith only [hz]) (norm_nonneg _)
    · rw [norm_zero]
      positivity
  rw [hin]
  refine (abs_real_inner_le_norm _ _).trans ?_
  have hT : ‖covT U μ y‖ = ‖y‖ := (covShift U μ).norm_T y
  rw [hT]
  exact mul_le_mul_of_nonneg_right hn (norm_nonneg y)

/-- The form of `block_coercive_of_cross` that bad plaquettes do not enter. -/
theorem cross_avoids (U : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hX : Avoids n U δ X) (μ ν : Fin 4) :
    |⟪(covShift U μ).Dstar (Xh n X μ), (covShift U ν).Dstar (Xh n X ν)⟫ -
        ⟪(covShift U ν).D (Xh n X μ), (covShift U μ).D (Xh n X ν)⟫| ≤
      2 * δ * ‖Xh n X μ‖ * ‖Xh n X ν‖ := by
  rw [cross_eq]
  have hu : ‖(covShift U μ).S (Xh n X μ)‖ = ‖Xh n X μ‖ := (covShift U μ).norm_S _
  have key := cross_local n U δ hδ0 μ ν ((covShift U μ).S (Xh n X μ)) (Xh n X ν) ?_
  · rw [hu] at key
    exact key
  · intro z hz
    change imag X ν (step (2 * n) z μ) = 0
    unfold pd at hz
    split_ifs at hz with h1 h2
    · exact (avoids_plaq n U δ X hX z μ ν h1 hz).2.1
    · exact (avoids_plaq n U δ X hX z ν μ h2 hz).2.2.1
    · exact absurd hz (not_lt.2 hδ0)

/-! ### The Hessian -/

theorem plaq_avoids (U : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hX : Avoids n U δ X) (x : V') (μ ν : Fin 4) (h : μ < ν) :
    ‖covCurl n U X μ ν x‖ ^ 2 - (32 * δ ^ 2 + 8 * δ) * linkSq n X x μ ν ≤
      -(2 * (secondCoeff (plaqOf n U X x μ ν).Y₁ (plaqOf n U X x μ ν).Y₂ (plaqOf n U X x μ ν).Y₃
        (plaqOf n U X x μ ν).Y₄ * plaqC n U X x μ ν).re) := by
  by_cases hb : δ < defect U μ ν x
  · obtain ⟨h1, h2, h3, h4⟩ := avoids_plaq n U δ X hX x μ ν h hb
    have y1 : (plaqOf n U X x μ ν).Y₁ = imag X μ x := rfl
    have y2 : (plaqOf n U X x μ ν).Y₂ = Ad (U x μ) (imag X ν (step (2 * n) x μ)) := rfl
    have y3 : (plaqOf n U X x μ ν).Y₃ = -Ad (U x μ * U (step (2 * n) x μ) ν *
      (U (step (2 * n) x ν) μ)⁻¹) (imag X μ (step (2 * n) x ν)) := rfl
    have y4 : (plaqOf n U X x μ ν).Y₄ = -Ad (U x μ * U (step (2 * n) x μ) ν *
      (U (step (2 * n) x ν) μ)⁻¹ * (U x ν)⁻¹) (imag X ν x) := rfl
    rw [y1, y2, y3, y4, covCurl_eq]
    unfold linkSq
    rw [h1, h2, h3, h4]
    simp [Ad_zero, secondCoeff]
  · exact plaq_cov_bound n U X δ hδ0 x μ ν (not_lt.1 hb)

theorem hessian_avoids (β : ℝ) (hβ : 0 ≤ β) (U : V' → Fin 4 → Q)
    (X : Fin 3 → Fin 4 → Section (2 * n)) (δ : ℝ) (hδ0 : 0 ≤ δ) (hX : Avoids n U δ X) :
    β * (curlEnergy (covShift U) (Xh n X) - (192 * δ ^ 2 + 48 * δ) * ∑ a, ∑ μ, ‖X a μ‖ ^ 2) ≤
      deriv (deriv fun t => action n Q (spatialTwist n) character β 2 (cfg n U X t)) 0 := by
  rw [second_derivative_field]
  refine mul_le_mul_of_nonneg_left ?_ hβ
  have hsum := Finset.sum_le_sum fun (p : PlaquetteIndex (2 * n)) (_ : p ∈ Finset.univ) =>
    plaq_avoids n U X δ hδ0 hX p.1 p.2.1.1 p.2.1.2 p.2.2
  refine le_trans (le_of_eq ?_) hsum
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hl : ∑ p : PlaquetteIndex (2 * n), linkSq n X p.1 p.2.1.1 p.2.1.2 =
      6 * ∑ a, ∑ μ, ‖X a μ‖ ^ 2 := link_count n X
  have hc : ∑ p : PlaquetteIndex (2 * n), ‖covCurl n U X p.2.1.1 p.2.1.2 p.1‖ ^ 2 =
      curlEnergy (covShift U) (Xh n X) := by
    unfold curlEnergy
    simp only [curl_field_norm]
    rw [← plane_sum (fun μ ν => ∑ x, ‖covCurl n U X μ ν x‖ ^ 2), Fintype.sum_prod_type,
      Finset.sum_comm]
  rw [hl, hc]
  ring

/-- **The block-scale bound away from bad plaquettes.** On directions vanishing on the links of
plaquettes with defect above `1/(1000 L²)`, the form is at least `β/(16 L²)` times the norm. Nothing is
assumed about the bad plaquettes themselves, and neither the constant nor the threshold involves `N`. -/
theorem block_coercive_avoids (β : ℝ) (hβ : 0 ≤ β) (U : V' → Fin 4 → Q)
    (X : Fin 3 → Fin 4 → Section (2 * n)) (L : ℕ) (hL : 1 ≤ L)
    (hX : Avoids n U (1 / (1000 * (L : ℝ) ^ 2)) X) :
    β * (1 / (16 * (L : ℝ) ^ 2) * ∑ a, ∑ μ, ‖X a μ‖ ^ 2) ≤
      deriv (deriv fun t => action n Q (spatialTwist n) character β 2 (cfg n U X t)) 0 +
        β * (‖div (covShift U) (Xh n X)‖ ^ 2 +
          1 / (4 * (L : ℝ) ^ 2) * ∑ μ, ‖blockAvg (covShift U) L (Xh n X μ)‖ ^ 2) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  set y : ℝ := 1 / (L : ℝ) ^ 2 with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 1 := by
    rw [hy]
    exact (div_le_one (by positivity)).2 (one_le_pow₀ hL1)
  have e1 : 1 / (1000 * (L : ℝ) ^ 2) = y / 1000 := by
    rw [hy]
    field_simp
  have e2 : 1 / (8 * (L : ℝ) ^ 2) = y / 8 := by
    rw [hy]
    field_simp
  have e3 : 1 / (16 * (L : ℝ) ^ 2) = y / 16 := by
    rw [hy]
    field_simp
  rw [e1] at hX
  have hδ0 : 0 ≤ y / 1000 := by positivity
  have h1 := hessian_avoids n β hβ U X (y / 1000) hδ0 hX
  have h2 := block_coercive_of_cross (covShift U) L hL (2 * (y / 1000)) (by positivity) (Xh n X)
    (cross_avoids n U X (y / 1000) hδ0 hX)
  rw [Xh_norm] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 hβ
  have hW : 0 ≤ ∑ a : Fin 3, ∑ μ : Fin 4, ‖X a μ‖ ^ 2 := by positivity
  rw [e2] at h3
  rw [e3]
  have hc : y / 16 ≤ y / 8 - 4 * (2 * (y / 1000)) - (192 * (y / 1000) ^ 2 + 48 * (y / 1000)) := by
    nlinarith only [hy0, hy1, mul_nonneg hy0.le (sub_nonneg.2 hy1)]
  have hm := mul_le_mul_of_nonneg_right hc hW
  have hm2 := mul_le_mul_of_nonneg_left hm hβ
  nlinarith only [h1, h3, hm2]

/-! ### The density of bad plaquettes -/

/-- **The density of bad plaquettes, uniform in the volume.** Except on an event of probability
`exp(-t · links)`, the number of bad plaquettes per link is below `(log cap(24β) + t)/(β δ²)`. -/
theorem measure_bad_density (β δ t : ℝ) (hβ : 1 / 32 ≤ β) (hδ0 : 0 ≤ δ) :
    TwistedLocalization.twistedLaw n β {U | (linkCount n : ℝ) *
        (Real.log (SU2GaussianMass.cap (24 * β)) + t) / β ≤
        ((badPlaq n (linkValue (2 * n) Q U) δ).card : ℝ) * δ ^ 2} ≤
      ENNReal.ofReal (Real.exp (-(t * linkCount n))) := by
  have hβ0 : 0 < β := by linarith only [hβ]
  set C := SU2GaussianMass.cap (24 * β) with hC
  have hC0 : 0 < C := by
    have h1 := SU2GaussianMass.mass_cap_lower (24 * β) (by linarith only [hβ])
    have h2 := SU2GaussianMass.cap_nonneg (24 * β) (by positivity)
    rcases h2.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at h1
      norm_num at h1
  set s := (linkCount n : ℝ) * (Real.log C + t) / β with hs
  have hsub : {U : Configuration V' Q | s ≤ ((badPlaq n (linkValue (2 * n) Q U) δ).card : ℝ) * δ ^ 2} ⊆
      {U | s ≤ actionOne n U} := by
    intro U hU
    change s ≤ actionOne n U
    rw [TwistedNearFlat.actionOne_eq]
    exact le_trans hU (card_badPlaq_le n _ δ hδ0)
  have ht := action_tail n β s hβ
  rw [← hC] at ht
  have he : Real.exp (-β * s) * C ^ linkCount n = Real.exp (-(t * linkCount n)) := by
    have e1 : -β * s = -((linkCount n : ℝ) * Real.log C) + -(t * linkCount n) := by
      rw [hs]
      field_simp
      ring
    have e2 : C ^ linkCount n = Real.exp ((linkCount n : ℝ) * Real.log C) := by
      rw [Real.exp_nat_mul, Real.exp_log hC0]
    rw [e1, Real.exp_add, e2, mul_right_comm, ← Real.exp_add]
    simp
  rw [he] at ht
  exact (MeasureTheory.measure_mono hsub).trans ht

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedBadSet
