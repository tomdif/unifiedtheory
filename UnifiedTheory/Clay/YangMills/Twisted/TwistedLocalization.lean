/- The first statement here about the twisted quantum measure. The action is bounded above
by the squared distance to the flat field, which bounds the partition function from below by
an exact product of Haar Gaussian masses. That gives a tail bound on the action under the law,
and `action_stability` turns it into localization of the winding holonomies. The coupling must
grow faster than the lattice volume, so this is not the physical trajectory. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedStability
import UnifiedTheory.Clay.YangMills.Twisted.TwistedSmallField
import UnifiedTheory.Clay.YangMills.Twisted.TwistedTransfer
import UnifiedTheory.Clay.YangMills.SU2GaussianMass

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedLocalization
noncomputable section
open MeasureTheory PeriodicLattice4 TwistedFlat TwistedStability TwistedReflection
open PeriodicPlaquetteReflection PeriodicTimeReflection RegulatedGauge
open WilsonSingleLinkStaples (Q character)
open scoped Quaternion ENNReal

variable (n : ℕ) [NeZero n]

theorem d_inv (g h : Q) : d g⁻¹ h⁻¹ = d g h := by
  have h1 := d_mul_left g g⁻¹ h⁻¹
  have h2 := d_mul_right h (g * g⁻¹) (g * h⁻¹)
  rw [mul_inv_cancel, one_mul, mul_assoc, inv_mul_cancel, mul_one] at h2
  rw [← h1]
  rw [mul_inv_cancel]
  rw [← h2]
  exact d_comm _ _

/-- A plaquette defect is at most the sum of the four link distances to the flat field. -/
theorem defect_le (L : Vertex (2 * n) → Fin 4 → Q) (x : Vertex (2 * n)) (μ ν : Fin 4)
    (h : μ < ν) :
    defect L μ ν x ≤ d (L x μ) (flatLink x μ) + d (L (step (2 * n) x μ) ν) (flatLink (step (2 * n) x μ) ν) +
      d (L (step (2 * n) x ν) μ) (flatLink (step (2 * n) x ν) μ) + d (L x ν) (flatLink x ν) := by
  unfold defect
  rw [← flatLink_flat (N := 2 * n) x μ ν h]
  set A := L x μ
  set B := L (step (2 * n) x μ) ν
  set C := L (step (2 * n) x ν) μ
  set D := L x ν
  set a := flatLink x μ
  set b := flatLink (step (2 * n) x μ) ν
  set c := flatLink (step (2 * n) x ν) μ
  set e := flatLink x ν
  have s1 : d (A * B * C⁻¹ * D⁻¹) (a * B * C⁻¹ * D⁻¹) = d A a := by
    simp only [mul_assoc]
    rw [d_mul_right]
  have s2 : d (a * B * C⁻¹ * D⁻¹) (a * b * C⁻¹ * D⁻¹) = d B b := by
    simp only [mul_assoc]
    rw [d_mul_left, d_mul_right]
  have s3 : d (a * b * C⁻¹ * D⁻¹) (a * b * c⁻¹ * D⁻¹) = d C c := by
    simp only [mul_assoc]
    rw [d_mul_left, d_mul_left, d_mul_right, d_inv]
  have s4 : d (a * b * c⁻¹ * D⁻¹) (a * b * c⁻¹ * e⁻¹) = d D e := by
    rw [d_mul_left, d_inv]
  have t1 := d_triangle (A * B * C⁻¹ * D⁻¹) (a * B * C⁻¹ * D⁻¹) (a * b * c⁻¹ * e⁻¹)
  have t2 := d_triangle (a * B * C⁻¹ * D⁻¹) (a * b * C⁻¹ * D⁻¹) (a * b * c⁻¹ * e⁻¹)
  have t3 := d_triangle (a * b * C⁻¹ * D⁻¹) (a * b * c⁻¹ * D⁻¹) (a * b * c⁻¹ * e⁻¹)
  linarith only [t1, t2, t3, s1, s2, s3, s4]

/-- Sum of squared link distances to the flat field. -/
def distSq (L : Vertex (2 * n) → Fin 4 → Q) : ℝ :=
  ∑ μ, ∑ x, d (L x μ) (flatLink x μ) ^ 2

/-- Six plaquettes meet each link, written for an arbitrary link density. -/
theorem six_count (m : Vertex (2 * n) → Fin 4 → ℝ) :
    ∑ p : PlaquetteIndex (2 * n), (m p.1 p.2.1.1 + m (step (2 * n) p.1 p.2.1.1) p.2.1.2 +
        m (step (2 * n) p.1 p.2.1.2) p.2.1.1 + m p.1 p.2.1.2) =
      6 * ∑ μ, ∑ x, m x μ := by
  let M : Fin 4 → ℝ := fun μ => ∑ x, m x μ
  have hstep (μ ν : Fin 4) : ∑ x, m (step (2 * n) x μ) ν = M ν :=
    Equiv.sum_comp (TwistedHessian.stepEquiv (N := 2 * n) μ) (fun y => m y ν)
  have hpl (μ ν : Fin 4) : ∑ x, (m x μ + m (step (2 * n) x μ) ν + m (step (2 * n) x ν) μ + m x ν) =
      2 * M μ + 2 * M ν := by
    simp only [Finset.sum_add_distrib]
    rw [hstep μ ν, hstep ν μ]
    change M μ + M ν + M μ + M ν = _
    ring
  have hL : ∑ p : PlaquetteIndex (2 * n), (m p.1 p.2.1.1 + m (step (2 * n) p.1 p.2.1.1) p.2.1.2 +
        m (step (2 * n) p.1 p.2.1.2) p.2.1.1 + m p.1 p.2.1.2) =
      ∑ d : Plane, (2 * M d.1.1 + 2 * M d.1.2) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    exact hpl d.1.1 d.1.2
  have hP : ∑ d : Plane, (2 * M d.1.1 + 2 * M d.1.2) =
      ∑ μ, ∑ ν, if μ < ν then 2 * M μ + 2 * M ν else 0 :=
    TwistedActionJet.plane_sum (fun μ ν => 2 * M μ + 2 * M ν)
  rw [hL, hP]
  simp (decide := true) only [Fin.sum_univ_four, if_true, if_false]
  ring

/-- The unit-coupling twisted action. -/
def actionOne (U : Configuration (Vertex (2 * n)) Q) : ℝ :=
  action n Q (spatialTwist n) character 1 2 U

theorem action_eq_mul (β : ℝ) (U : Configuration (Vertex (2 * n)) Q) :
    action n Q (spatialTwist n) character β 2 U = β * actionOne n U := by
  unfold actionOne action
  rw [one_mul]

/-- The twisted action is at most `24` times the squared distance to the flat field. -/
theorem actionOne_le (U : Configuration (Vertex (2 * n)) Q) :
    actionOne n U ≤ 24 * distSq n (linkValue (2 * n) Q U) := by
  set L := linkValue (2 * n) Q U with hL
  have hp (p : PlaquetteIndex (2 * n)) :
      term n Q (spatialTwist n) character 2 U p ≤
        4 * (d (L p.1 p.2.1.1) (flatLink p.1 p.2.1.1) ^ 2 +
          d (L (step (2 * n) p.1 p.2.1.1) p.2.1.2) (flatLink (step (2 * n) p.1 p.2.1.1) p.2.1.2) ^ 2 +
          d (L (step (2 * n) p.1 p.2.1.2) p.2.1.1) (flatLink (step (2 * n) p.1 p.2.1.2) p.2.1.1) ^ 2 +
          d (L p.1 p.2.1.2) (flatLink p.1 p.2.1.2) ^ 2) := by
    rcases p with ⟨x, ⟨⟨μ, ν⟩, h⟩⟩
    simp only
    rw [term_eq_defect_sq]
    have hle := defect_le n L x μ ν h
    have hn := defect_nonneg L μ ν x
    set a := d (L x μ) (flatLink x μ)
    set b := d (L (step (2 * n) x μ) ν) (flatLink (step (2 * n) x μ) ν)
    set c := d (L (step (2 * n) x ν) μ) (flatLink (step (2 * n) x ν) μ)
    set e := d (L x ν) (flatLink x ν)
    have hsq : defect L μ ν x ^ 2 ≤ (a + b + c + e) ^ 2 := pow_le_pow_left₀ hn hle 2
    nlinarith only [hsq, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - e), sq_nonneg (b - c),
      sq_nonneg (b - e), sq_nonneg (c - e)]
  unfold actionOne action
  rw [one_mul]
  refine (Finset.sum_le_sum fun p _ => hp p).trans ?_
  rw [← Finset.mul_sum, six_count n (fun x μ => d (L x μ) (flatLink x μ) ^ 2)]
  unfold distSq
  linarith only [le_refl (24 * ∑ μ, ∑ x, d (L x μ) (flatLink x μ) ^ 2)]

/-! ### The partition function -/

theorem continuous_actionOne : Continuous (actionOne n) :=
  continuous_action n Q (spatialTwist n) character WilsonSingleLinkStaples.character_continuous 1 2

/-- A Haar Gaussian centered anywhere has the mass of the one centered at the identity. -/
theorem gaussian_translate (b : Q) (s : ℝ) :
    ∫ q : Q, Real.exp (-s * d q b ^ 2) ∂compactHaar Q = SU2GaussianMass.mass s := by
  unfold SU2GaussianMass.mass SU2GaussianMass.weight
  rw [← integral_mul_left_eq_self (fun q : Q => Real.exp (-s * d q b ^ 2)) b]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  have h : d (b * q) b = ‖(q : ℍ[ℝ]) - 1‖ := by
    have e := d_mul_left b q 1
    rw [mul_one] at e
    rw [e]
    rfl
  simp only [h]

/-- Number of independent links. -/
def linkCount : ℕ := Fintype.card (Edge (Vertex (2 * n)))

theorem linkCount_eq : linkCount n = 4 * (2 * n) ^ 4 := by
  unfold linkCount
  rw [Fintype.card_congr (edgeCoordinates (2 * n))]
  simp [ZMod.card]
  ring

theorem distSq_eq (U : Configuration (Vertex (2 * n)) Q) :
    distSq n (linkValue (2 * n) Q U) = ∑ e, d (U e) (flatConfiguration n e) ^ 2 := by
  rw [← Equiv.sum_comp (edgeCoordinates (2 * n)).symm, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- The partition function is at least an exact product of Gaussian masses, for `β ≥ 0`. -/
theorem partition_lower (β : ℝ) (hβ : 0 ≤ β) :
    ENNReal.ofReal (SU2GaussianMass.mass (24 * β) ^ linkCount n) ≤
      gibbsPartition (Vertex (2 * n)) Q (action n Q (spatialTwist n) character β 2) := by
  have hprod : (∫ U : Configuration (Vertex (2 * n)) Q,
      ∏ e, Real.exp (-(24 * β) * d (U e) (flatConfiguration n e) ^ 2)
        ∂referenceMeasure Q (Vertex (2 * n))) =
      SU2GaussianMass.mass (24 * β) ^ linkCount n := by
    unfold referenceMeasure
    have h := integral_fintype_prod_eq_prod (ι := Edge (Vertex (2 * n))) (E := fun _ => Q)
      (fun e q => Real.exp (-(24 * β) * d q (flatConfiguration n e) ^ 2))
      (μ := fun _ => compactHaar Q)
    refine h.trans ?_
    simp only [gaussian_translate, Finset.prod_const, Finset.card_univ, linkCount]
  have hcontP : Continuous fun U : Configuration (Vertex (2 * n)) Q =>
      ∏ e, Real.exp (-(24 * β) * d (U e) (flatConfiguration n e) ^ 2) := by
    refine continuous_finset_prod _ fun e _ => ?_
    unfold d
    fun_prop
  rw [← hprod, ofReal_integral_eq_lintegral_ofReal
    (hcontP.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (Filter.Eventually.of_forall fun U => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)]
  unfold gibbsPartition gibbsDensity
  refine lintegral_mono fun U => ENNReal.ofReal_le_ofReal ?_
  rw [← Real.exp_sum, action_eq_mul]
  apply Real.exp_le_exp.mpr
  have h := actionOne_le n U
  rw [distSq_eq] at h
  rw [← Finset.mul_sum]
  nlinarith only [h, hβ]

/-- The twisted law. -/
abbrev twistedLaw (β : ℝ) : Measure (Configuration (Vertex (2 * n)) Q) :=
  law n Q (spatialTwist n) character β 2

/-- **Action tail bound under the twisted quantum measure**, for `β ≥ 1/32`. -/
theorem action_tail (β s : ℝ) (hβ : 1 / 32 ≤ β) :
    twistedLaw n β {U | s ≤ actionOne n U} ≤
      ENNReal.ofReal (Real.exp (-β * s) * SU2GaussianMass.cap (24 * β) ^ linkCount n) := by
  have hβ0 : 0 ≤ β := by linarith only [hβ]
  have hM := SU2GaussianMass.mass_pos (24 * β)
  have hcap := SU2GaussianMass.mass_cap_lower (24 * β) (by linarith only [hβ])
  set M := SU2GaussianMass.mass (24 * β)
  set K := SU2GaussianMass.cap (24 * β)
  have hA : MeasurableSet {U | s ≤ actionOne n U} :=
    (isClosed_le continuous_const (continuous_actionOne n)).measurableSet
  set S := action n Q (spatialTwist n) character β 2 with hS
  have hSc : Continuous S := continuous_action n Q (spatialTwist n) character
    WilsonSingleLinkStaples.character_continuous β 2
  have hdens : Measurable (gibbsDensity (Vertex (2 * n)) Q S) :=
    (Real.continuous_exp.comp hSc.neg).measurable.ennreal_ofReal
  have hset : (referenceMeasure Q (Vertex (2 * n))).withDensity (gibbsDensity (Vertex (2 * n)) Q S)
      {U | s ≤ actionOne n U} ≤ ENNReal.ofReal (Real.exp (-β * s)) := by
    rw [withDensity_apply _ hA]
    calc
      _ ≤ ∫⁻ _ in {U | s ≤ actionOne n U}, ENNReal.ofReal (Real.exp (-β * s))
            ∂referenceMeasure Q (Vertex (2 * n)) := by
        refine setLIntegral_mono measurable_const fun U hU => ENNReal.ofReal_le_ofReal ?_
        rw [hS, action_eq_mul]
        apply Real.exp_le_exp.mpr
        have : s ≤ actionOne n U := hU
        nlinarith only [this, hβ0]
      _ = ENNReal.ofReal (Real.exp (-β * s)) * referenceMeasure Q (Vertex (2 * n))
            {U | s ≤ actionOne n U} := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (Real.exp (-β * s)) * 1 := by
        gcongr
        exact prob_le_one
      _ = _ := mul_one _
  have hZ : (gibbsPartition (Vertex (2 * n)) Q S)⁻¹ ≤ ENNReal.ofReal (K ^ linkCount n) := by
    have hl := partition_lower n β hβ0
    have hMp : 0 < M ^ linkCount n := pow_pos hM _
    refine (ENNReal.inv_le_inv.mpr hl).trans ?_
    rw [← ENNReal.ofReal_inv_of_pos hMp]
    apply ENNReal.ofReal_le_ofReal
    rw [inv_eq_one_div, div_le_iff₀ hMp, ← mul_pow, mul_comm K M]
    exact one_le_pow₀ hcap
  change (gibbsPartition (Vertex (2 * n)) Q S)⁻¹ *
    (referenceMeasure Q (Vertex (2 * n))).withDensity (gibbsDensity (Vertex (2 * n)) Q S)
      {U | s ≤ actionOne n U} ≤ _
  rw [mul_comm (Real.exp _), ENNReal.ofReal_mul (pow_nonneg (SU2GaussianMass.cap_nonneg _
    (by positivity)) _)]
  exact mul_le_mul' hZ hset

/-- The event that the winding relations hold at some base point, within `ε`. -/
def Localized (ε : ℝ) (U : Configuration (Vertex (2 * n)) Q) : Prop :=
  ∃ x, d (wind (linkValue (2 * n) Q U) 1 x * wind (linkValue (2 * n) Q U) 2 x)
        (ω * (wind (linkValue (2 * n) Q U) 2 x * wind (linkValue (2 * n) Q U) 1 x)) ≤ ε ∧
    (d (wind (linkValue (2 * n) Q U) 3 x) 1 ≤ 8 / 3 * ε ∨
      d (wind (linkValue (2 * n) Q U) 3 x) ω ≤ 8 / 3 * ε) ∧
    (d (wind (linkValue (2 * n) Q U) 0 x) 1 ≤ 8 / 3 * ε ∨
      d (wind (linkValue (2 * n) Q U) 0 x) ω ≤ 8 / 3 * ε)

/-- **Localization of the twisted quantum measure.** The law gives the failure of the flat
winding relations at scale `ε` probability at most `exp (-β ε²) · cap(24β)^links`. -/
theorem localization (β ε : ℝ) (hβ : 1 / 32 ≤ β) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    twistedLaw n β {U | ¬ Localized n ε U} ≤
      ENNReal.ofReal (Real.exp (-β * ε ^ 2) * SU2GaussianMass.cap (24 * β) ^ linkCount n) := by
  refine (measure_mono fun U hU => ?_).trans (action_tail n β (ε ^ 2) hβ)
  change ε ^ 2 ≤ actionOne n U
  by_contra hlt
  push_neg at hlt
  apply hU
  have hS1 : actionOne n U ≤ 1 := by nlinarith only [hlt, hε0, hε1]
  have hsq : Real.sqrt (actionOne n U) ≤ ε := by
    rw [Real.sqrt_le_left hε0]
    exact hlt.le
  obtain ⟨x, h1, h2, h3⟩ := action_stability n U hS1
  have hK : 8 / 3 * Real.sqrt (actionOne n U) ≤ 8 / 3 * ε := by linarith only [hsq]
  refine ⟨x, h1.trans hsq, ?_, ?_⟩
  · exact h2.imp (fun h => h.trans hK) (fun h => h.trans hK)
  · exact h3.imp (fun h => h.trans hK) (fun h => h.trans hK)

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedLocalization
