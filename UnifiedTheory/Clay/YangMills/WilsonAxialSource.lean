/- Source-weighted control of actual temporal mismatch on a small-curvature
spatial box. The source remains the correlated physical variance-pair source. -/
import UnifiedTheory.Clay.YangMills.WilsonAxialAlignment
import UnifiedTheory.Clay.YangMills.WilsonGaugeBlockSource

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonAxialSource
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonAxialRegularity WilsonAxialBox
open WilsonAxialAlignment WilsonPhysicalVariance WilsonGroundHeatBath CompactDensityEntropy
open WilsonGaugeSourceTail (source source_continuous source_nonneg)
open scoped Quaternion

variable (n : ℕ) [NeZero n]

omit [NeZero n] in
theorem flat_closed (L : ℕ) (δ : ℝ) : IsClosed {u : Slice n | FlatBox n u L δ} := by
  unfold FlatBox
  simp only [Set.setOf_forall]
  refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun c =>
    isClosed_iInter fun _ha => isClosed_iInter fun _hb => isClosed_iInter fun _hc =>
      isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _hij => ?_
  exact isClosed_le
    (show Continuous (fun u : Slice n =>
      ‖((spatialHolonomy u (WilsonAxialGauge.vertex n a b c) i j : Q) : ℍ)-1‖) by
        unfold spatialHolonomy
        fun_prop) continuous_const

theorem energy_continuous (L : ℕ) :
    Continuous (fun z : Slice n × Slice n => energy n L z.1 z.2) := by
  unfold energy
  fun_prop

def event (L : ℕ) (δ a : ℝ) : Set (Slice n × Slice n) :=
  {z | FlatBox n z.1 (L + 1) δ ∧ FlatBox n z.2 (L + 1) δ ∧ a < energy n L z.1 z.2}

theorem event_measurable (L : ℕ) (δ a : ℝ) : MeasurableSet (event n L δ a) := by
  exact ((flat_closed n (L + 1) δ).preimage continuous_fst).measurableSet.inter
    (((flat_closed n (L + 1) δ).preimage continuous_snd).measurableSet.inter
      (isOpen_lt continuous_const (energy_continuous n L)).measurableSet)

def rowMass (L : ℕ) (δ a β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) (u : Slice n) : ℝ :=
  (∫ v, (event n L δ a).indicator (source n β hβ f) (u, v) ∂WilsonSlabOperator.measure n)/2

theorem rowMass_integrable (L : ℕ) (δ a β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    Integrable (rowMass n L δ a β hβ f) (groundLaw n β hβ) := by
  letI := groundLaw_probability n β hβ
  exact (((continuous_integrable ((groundLaw n β hβ).prod (WilsonSlabOperator.measure n)) _
    (source_continuous n β hβ f)).indicator
      (event_measurable n L δ a)).integral_prod_left).div_const 2

variable [Fact (1 < n)]

theorem event_subset (L : ℕ) (hpos : 0 < L) (hL : L + 1 ≤ n)
    (δ a t : ℝ) (hδ : 0 ≤ δ) (ha : budget L δ + t ≤ a) :
    event n L δ a ⊆ WilsonGaugeBlockTail.bad n (block n L) t := by
  rintro ⟨u,v⟩ ⟨hu,hv,he⟩
  exact bad_of_energy n L hpos hL u v δ t hδ hu hv (ha.trans_lt he)

theorem rowMass_upper (L : ℕ) (hpos : 0 < L) (hL : L + 1 ≤ n)
    (δ a t β : ℝ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (ha : budget L δ + t ≤ a)
    (f : C(Slice n, ℝ)) (u : Slice n) :
    rowMass n L δ a β hβ f u ≤ WilsonGaugeBlockSource.rowTail n β hβ (block n L) t f u := by
  let E := {v : Slice n | (u,v) ∈ event n L δ a}
  let B := {v : Slice n | (u,v) ∈ WilsonGaugeBlockTail.bad n (block n L) t}
  have hE : MeasurableSet E := (event_measurable n L δ a).preimage
    (measurable_const.prodMk measurable_id)
  have hB : MeasurableSet B :=
    (WilsonGaugeBlockTail.bad_open n (block n L) t).measurableSet.preimage
    (measurable_const.prodMk measurable_id)
  have hi := continuous_integrable (WilsonSlabOperator.measure n) _
    ((source_continuous n β hβ f).comp
      (f := fun v : Slice n => (u,v)) (continuous_const.prodMk continuous_id))
  have h := integral_mono (hi.indicator hE) (hi.indicator hB) (fun v => by
    by_cases hv : v ∈ E
    · have hb : v ∈ B := event_subset n L hpos hL δ a t hδ ha hv
      rw [Set.indicator_of_mem hv, Set.indicator_of_mem hb]
    · rw [Set.indicator_of_notMem hv]
      exact Set.indicator_nonneg (fun _ _ => source_nonneg n β hβ f _) _)
  exact div_le_div_of_nonneg_right h (by norm_num)

/-- The actual source error is paid by original-transfer variance loss. -/
theorem meanMass_upper (L : ℕ) (hpos : 0 < L) (hL : L + 1 ≤ n)
    (δ a t β : ℝ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (ha : budget L δ + t ≤ a)
    (f : C(Slice n, ℝ)) (hF : ∀ h v, f (gaugeSlice h v) = f v) :
    (∫ u, rowMass n L δ a β hβ f u ∂groundLaw n β hβ) ≤
      WilsonGaugeBlockSource.tailCap n β t (block n L)*loss n β hβ f := by
  exact (integral_mono (rowMass_integrable n L δ a β hβ f)
    (WilsonGaugeBlockSource.rowTail_integrable n β hβ (block n L) t f)
    (rowMass_upper n L hpos hL δ a t β hβ hδ ha f)).trans
      (WilsonGaugeBlockSource.meanTail_upper n β hβ (block n L) t f hF)

/-- A concrete scale choice yields exponential suppression in the box volume.
The event still requires small spatial plaquette defects in both fields. -/
theorem extensive_source_tail (L : ℕ) (hlarge : 4096 ≤ L) (hL : L + 1 ≤ n)
    (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hF : ∀ h v, f (gaugeSlice h v) = f v) :
    (∫ u, rowMass n L (1 / (100 * ((L : ℝ) + 1))) ((L : ℝ)^3/8) β hβ f u
      ∂groundLaw n β hβ) ≤ (WilsonGaugeSourceTail.tailCap β (1/16))^(L^3)*loss n β hβ f := by
  have hd : 0 ≤ 1 / (100 * ((L : ℝ) + 1)) := by positivity
  have hb := budget_small L hlarge (1 / (100 * ((L : ℝ) + 1))) hd le_rfl
  have h := meanMass_upper n L (by omega) hL (1 / (100 * ((L : ℝ) + 1))) ((L : ℝ)^3/8)
    ((1/16)*((block n L).card : ℝ)) β hβ hd (by rw [block_card n L hL]; push_cast; linarith) f hF
  rw [WilsonGaugeBlockSource.tailCap_extensive, block_card n L hL] at h
  exact h

end
end UnifiedTheory.Clay.YangMills.WilsonAxialSource
