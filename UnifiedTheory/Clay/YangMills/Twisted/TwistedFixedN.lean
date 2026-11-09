/- Two inputs to the fixed-`n` semiclassical limit (Attack 1 of the swarm synthesis). Both hold for every `β` and `n`.

* `frameWeight_lower`: a field whose off-tree links lie within `ε` of a rotated reference has frame weight at least
  `ballMass ε₁`, for `ε + 2 ε₁ < √2`. This is the open hypothesis of `integral_tree_chart`, on fields near the rotated reference.
  The bound depends on neither `β` nor `n`. Connecting `near_flat` to this hypothesis is not done here.
* `energy_no_log`: `E[S] ≤ 48 N⁶/β + 24 N⁴ exp(-β·flatThreshold) cap(24β)^links`, with no `log β`. It beats `energy_le` only for
  `log β` above about `64 n³`, and its tail is small only near `β ~ N¹⁴ log N`, so it is a fixed-`n` statement and gives nothing on the
  trajectory `β ~ log n`.

Neither gives a limit for `neutralLevel`, and neither touches the kernel. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedSemiclassical
import UnifiedTheory.Clay.YangMills.Twisted.TwistedBlockStep
import UnifiedTheory.Clay.YangMills.Twisted.TwistedFlow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedFixedN
noncomputable section
open MeasureTheory
open scoped Quaternion
open SU2QuaternionEquivalence TwistedSemiclassical TwistedBlockStep TwistedBlockMap
open WilsonSingleLinkStaples (Q)

section Frame
open TwistedStability TwistedLandau RegulatedGauge
open WilsonTimeSlab TwistedTreeGauge
variable {E : Type*} [Fintype E]

/-- Distance below `√2` puts a unit quaternion in the half around the reference. -/
theorem mem_nearRef_of_d_lt (r y : Q) (h : d y r < Real.sqrt 2) : y ∈ nearRef r := by
  have hs : d y r ^ 2 < 2 := by
    calc _ < Real.sqrt 2 ^ 2 := pow_lt_pow_left₀ h (d_nonneg _ _) (by norm_num)
      _ = 2 := Real.sq_sqrt (by norm_num)
  have hd : d (r⁻¹ * y) 1 = d y r := by
    have := d_mul_left r⁻¹ y r
    rwa [inv_mul_cancel] at this
  rw [← hd] at hs
  have hre : d (r⁻¹ * y) 1 ^ 2 = 2 - 2 * ((r⁻¹ * y : Q) : Quaternion ℝ).re := by
    have := d_sq_eq (r⁻¹ * y) 1
    simpa [rePart] using this
  change 0 < ((r⁻¹ * y : Q) : Quaternion ℝ).re
  linarith only [hs, hre]

/-- Conjugation by `k` within `ε₁` of the identity moves `r` by at most `2 ε₁`. -/
theorem d_conj_le (k r : Q) (ε₁ : ℝ) (hk : d k 1 ≤ ε₁) : d (k * r * k⁻¹) r ≤ 2 * ε₁ := by
  have e : d (k * r * k⁻¹) r = d (k * r) (r * k) := by
    have := d_mul_right k (k * r * k⁻¹) r
    rw [inv_mul_cancel_right] at this
    exact this.symm
  have h1 : d (k * r) r ≤ ε₁ := by
    have := d_mul_right r k 1
    rw [one_mul] at this
    rwa [this]
  have h2 : d r (r * k) ≤ ε₁ := by
    have := d_mul_left r 1 k
    rw [mul_one] at this
    rw [this, TwistedStability.d_comm]
    exact hk
  rw [e]
  linarith only [d_triangle (k * r) r (r * k), h1, h2]

/-- **The frame weight is bounded below near a rotated reference.** If every link of `x` is within `ε` of `h r_e h⁻¹`, and
`ε + 2 ε₁ < √2`, then the rotations `k h⁻¹` with `k` within `ε₁` of the identity all bring `x` into the near set. The bound has
no dependence on `β`, on the lattice, or on the number of links. -/
theorem frameWeight_lower (r x : E → Q) (h : Q) (ε ε₁ : ℝ) (hclose : ∀ e, d (x e) (h * r e * h⁻¹) ≤ ε)
    (hsum : ε + 2 * ε₁ < Real.sqrt 2) : ballMass ε₁ ≤ frameWeight r x := by
  classical
  set H := compactHaar Q with hH
  have hgood (g : Q) (hg : d (g * h) 1 ≤ ε₁) : conjF g x ∈ nearSet r := by
    refine Set.mem_pi.mpr fun e _ => mem_nearRef_of_d_lt _ _ ?_
    set k := g * h with hk
    have hgk : g = k * h⁻¹ := by rw [hk, mul_inv_cancel_right]
    have ey : d (h⁻¹ * x e * h) (r e) ≤ ε := by
      have h1 := d_mul_left h⁻¹ (x e) (h * r e * h⁻¹)
      have h2 := d_mul_right h (h⁻¹ * x e) (h⁻¹ * (h * r e * h⁻¹))
      have h3 : h⁻¹ * (h * r e * h⁻¹) * h = r e := by group
      rw [h3] at h2
      calc _ = d (x e) (h * r e * h⁻¹) := by rw [h2, h1]
        _ ≤ ε := hclose e
    have eg : conjF g x e = k * (h⁻¹ * x e * h) * k⁻¹ := by
      simp only [conjF, hgk]
      group
    have e1 : d (k * (h⁻¹ * x e * h) * k⁻¹) (k * r e * k⁻¹) ≤ ε := by
      rw [d_mul_right, d_mul_left]
      exact ey
    have e2 := d_conj_le k (r e) ε₁ hg
    rw [eg]
    linarith only [d_triangle (k * (h⁻¹ * x e * h) * k⁻¹) (k * r e * k⁻¹) (r e), e1, e2, hsum]
  have hAm : MeasurableSet {g : Q | d (g * h) 1 ≤ ε₁} :=
    (isClosed_le (by unfold d; fun_prop) continuous_const).measurableSet
  have hmass : H.real {g : Q | d (g * h) 1 ≤ ε₁} = ballMass ε₁ := by
    unfold ballMass
    have : {g : Q | d (g * h) 1 ≤ ε₁} = (fun g => g * h) ⁻¹' {q : Q | d q 1 ≤ ε₁} := rfl
    rw [this]
    simp only [measureReal_def]
    rw [measure_preimage_mul_right]
  have hc : Measurable fun g : Q => conjF g x := by
    refine measurable_pi_iff.mpr fun e => ?_
    change Measurable fun g : Q => g * x e * g⁻¹
    exact (measurable_id.mul_const _).mul measurable_id.inv
  have hi : Integrable (fun g => (nearSet r).indicator (fun _ => (1 : ℝ)) (conjF g x)) H := by
    refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun g => ?_)
    · exact ((measurable_const.indicator (nearSet_measurable r)).comp hc).aestronglyMeasurable
    · by_cases hm : conjF g x ∈ nearSet r <;> simp [hm]
  have hle : ∫ g, Set.indicator {g : Q | d (g * h) 1 ≤ ε₁} (1 : Q → ℝ) g ∂H ≤
      ∫ g, (nearSet r).indicator (fun _ => (1 : ℝ)) (conjF g x) ∂H := by
    refine integral_mono ((integrable_const (1 : ℝ)).indicator hAm) hi fun g => ?_
    by_cases hg : d (g * h) 1 ≤ ε₁
    · simp [Set.indicator_of_mem (show g ∈ {g : Q | d (g * h) 1 ≤ ε₁} from hg), Set.indicator_of_mem (hgood g hg)]
    · rw [Set.indicator_of_notMem (show g ∉ {g : Q | d (g * h) 1 ≤ ε₁} from hg)]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  rw [integral_indicator_one hAm, hmass] at hle
  exact hle

/-- The chart identity `integral_tree_chart` with its frame-weight hypothesis replaced by closeness to a rotated reference on the
support of `F`. Showing that a slice in the valley has this closeness in tree gauge is not done here. -/
theorem integral_tree_chart_of_close (n : ℕ) [NeZero n] (F : C(WilsonSlabOperator.Slice n, ℝ))
    (hF : ∀ (h : SliceGauge n Q) u, F (gaugeSlice h u) = F u)
    (r : {e : SpatialVertex n × Fin 3 // ¬ isTree n e} → Q) (ε ε₁ : ℝ) (hε₁ : 0 < ε₁)
    (hsum : ε + 2 * ε₁ < Real.sqrt 2)
    (hclose : ∀ x : {e : SpatialVertex n × Fin 3 // ¬ isTree n e} → Q, F (treeGlue n x) ≠ 0 → ∃ h : Q, ∀ e, d (x e) (h * r e * h⁻¹) ≤ ε) :
    ∫ u, F u ∂WilsonSlabOperator.measure n =
      ∫ t : {e : SpatialVertex n × Fin 3 // ¬ isTree n e} → EuclideanSpace ℝ (Fin 3),
        F (treeGlue n fun e => r e * gnomQ (t e)) / frameWeight r (fun e => r e * gnomQ (t e))
          ∂(Measure.pi fun _ => gnomMeasure) :=
  integral_tree_chart n F hF r (ballMass ε₁) (ballMass_pos ε₁ hε₁) fun x hx => by
    obtain ⟨h, hh⟩ := hclose x hx
    exact frameWeight_lower r x h ε ε₁ hh hsum

end Frame

section Energy
open TwistedFlow
open PeriodicLattice4 TwistedFlat CommutingShifts TwistedHessian TwistedActionJet TwistedSmallField
open TwistedStability TwistedLandau TwistedLocalization TwistedReflection TwistedHessianField TwistedIBP
open TwistedCovariant
open PeriodicPlaquetteReflection PeriodicTimeReflection RegulatedGauge

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

/-- **The energy with no logarithm.** Near the flat fields `grad_dom` bounds the action by the force, the force has a bare bound
under the law (`law_force_bare`), and the far set is small by `action_tail`. -/
theorem energy_no_log (β : ℝ) (hβ : 1 / 32 ≤ β) :
    ∫ U, actionOne n U ∂twistedLaw n β ≤
      48 * ((2 * n : ℕ) : ℝ) ^ 6 / β +
        24 * ((2 * n : ℕ) : ℝ) ^ 4 *
          (Real.exp (-β * flatThreshold n) * SU2GaussianMass.cap (24 * β) ^ linkCount n) := by
  classical
  have hβ0 : 0 < β := by linarith only [hβ]
  set N : ℝ := ((2 * n : ℕ) : ℝ) with hN
  have hNp : 0 < N := by
    have := NeZero.pos n
    rw [hN]
    exact_mod_cast (by omega : 0 < 2 * n)
  set A : Set (Configuration V' Q) := {U | flatThreshold n ≤ actionOne n U} with hA
  have hAm : MeasurableSet A := (isClosed_le continuous_const (continuous_actionOne n)).measurableSet
  have hpt (U : Configuration V' Q) : actionOne n U ≤
      N ^ 2 / 3 * forceSq n U + 24 * N ^ 4 * A.indicator 1 U := by
    have hF : 0 ≤ forceSq n U := by unfold forceSq; positivity
    by_cases hU : U ∈ A
    · rw [Set.indicator_of_mem hU, Pi.one_apply, mul_one]
      have h1 := action_le_total n U
      have h2 : 0 ≤ N ^ 2 / 3 * forceSq n U := by positivity
      linarith only [h1, h2]
    · rw [Set.indicator_of_notMem hU, mul_zero, add_zero]
      have := grad_dom n U (le_of_lt (not_le.1 hU))
      linarith only [this]
  have hi1 : Integrable (fun U => N ^ 2 / 3 * forceSq n U) (twistedLaw n β) :=
    (integrable_law n β (continuous_forceSq n)).const_mul _
  have hi2 : Integrable (fun U => 24 * N ^ 4 * A.indicator (1 : Configuration V' Q → ℝ) U) (twistedLaw n β) :=
    ((integrable_const (1 : ℝ)).indicator hAm).const_mul _
  have hint := integral_mono (integrable_law n β (continuous_actionOne n)) (hi1.add hi2) hpt
  simp only [Pi.add_apply] at hint
  rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul, integral_indicator_one hAm] at hint
  refine hint.trans (add_le_add ?_ ?_)
  · have h := law_force_bare n β hβ0
    calc N ^ 2 / 3 * ∫ U, forceSq n U ∂twistedLaw n β ≤ N ^ 2 / 3 * (144 * N ^ 4 / β) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 48 * N ^ 6 / β := by ring
  · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine ENNReal.toReal_le_of_le_ofReal ?_ (action_tail n β (flatThreshold n) hβ)
    have hcap : 0 < SU2GaussianMass.cap (24 * β) := by
      have hM := SU2GaussianMass.mass_pos (24 * β)
      have hcap := SU2GaussianMass.mass_cap_lower (24 * β) (by linarith only [hβ])
      by_contra hcn
      push_neg at hcn
      nlinarith only [hM, hcn, hcap]
    positivity

end Energy

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedFixedN
