/- The canonical Weyl estimates apply to the actual all-time quantum
propagator. Any pointwise small-hbar limit of its normalized-state phase
characteristics has a positive classical kernel. No limit existence,
tightness, measure representation or classical transport is assumed proved. -/
import UnifiedTheory.Audit.KFCausalCanonicalWeylLimit
import UnifiedTheory.Audit.KFCausalCanonicalWeylDirac
import UnifiedTheory.Audit.KFCausalClockFloorInitialCharacteristic
import UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianConcentration (dot dot_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra
open UnifiedTheory.Audit.KFCausalCanonicalWeylLimit

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

abbrev Frequencies := Frequency (X := Configuration)

def positionFrequency (r : ℝ) (ξ : Transverse) : Configuration →L[ℝ] ℝ where
  toFun x := r*x.1+dot ξ x.2
  map_add' x y := by simp [dot,mul_add,Finset.sum_add_distrib]; ring
  map_smul' a x := by simp [dot,Finset.mul_sum,mul_left_comm,mul_add]
  cont := (continuous_const.mul continuous_fst).add ((dot_continuous ξ).comp continuous_snd)

theorem operator_eq_observable (h r u : ℝ) (ξ η : Transverse) :
    operator volume h (positionFrequency r ξ,(u,η)) =
      KFCausalClockFloorInitialCharacteristic.observable h r u ξ η := rfl

def evolvedCharacteristic (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s t : ℝ) (f : Hilbert) (z : Frequencies) : ℂ :=
  characteristic volume h (evolution ε hε h hh hb m g κ s t f) z

theorem evolvedCharacteristic_initial (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s : ℝ) (f : Hilbert) (z : Frequencies) :
    evolvedCharacteristic ε hε h hh hb m g κ s s f z = characteristic volume h f z := by
  have he := congrArg (fun A : Hilbert →L[ℂ] Hilbert => A f)
    (evolution_initial ε hε h hh hb m g κ s)
  change evolution ε hε h hh hb m g κ s s f = f at he
  simp only [evolvedCharacteristic,he]

theorem evolvedCharacteristic_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s t : ℝ) (f : Hilbert) (hn : ‖f‖ = 1) (z : Frequencies) :
    ‖evolvedCharacteristic ε hε h hh hb m g κ s t f z‖ ≤ 1 := by
  simpa only [evolvedCharacteristic,evolution_norm,hn,one_pow] using
    characteristic_bound volume h (evolution ε hε h hh hb m g κ s t f) z

theorem evolvedCharacteristic_continuous_time (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s : ℝ) (f : Hilbert) (z : Frequencies) :
    Continuous (fun t => evolvedCharacteristic ε hε h hh hb m g κ s t f z) := by
  have hc := evolution_strong_continuous ε hε h hh hb m g κ s f
  exact hc.inner ((operator volume h z).continuous.comp hc)

theorem evolved_commutator_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s t : ℝ) (f : Hilbert) (hn : ‖f‖ = 1)
    (z w : Frequencies) :
    let v := evolution ε hε h hh hb m g κ s t f
    ‖operator volume h z (operator volume h w v)-operator volume h w (operator volume h z v)‖ ≤
      |h| * (|w.1 z.2|+|z.1 w.2|) := by
  simpa only [evolution_norm,hn,mul_one] using
    commutator_bound volume h z w (evolution ε hε h hh hb m g κ s t f)

theorem evolved_commutator_uniform_limit (ε : ℝ) (hε : 0 < ε)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (m g κ s : ℝ) (f : ℕ → Hilbert) (hn : ∀ n, ‖f n‖ = 1)
    (z w : Frequencies) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ,
      let v := evolution ε hε (h n) (hh n) (hb n) m g κ s t (f n)
      ‖operator volume (h n) z (operator volume (h n) w v)-
        operator volume (h n) w (operator volume (h n) z v)‖ < δ := by
  have ht : Tendsto (fun n => |h n| * (|w.1 z.2|+|z.1 w.2|)) atTop (𝓝 0) := by
    simpa only [abs_zero,zero_mul] using hz.abs.mul_const (|w.1 z.2|+|z.1 w.2|)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
  refine ⟨N,?_⟩
  intro n hNn t
  exact (evolved_commutator_bound ε hε (h n) (hh n) (hb n) m g κ s t (f n) (hn n) z w).trans_lt
    (hN n hNn)

theorem evolved_limit_properties (ε : ℝ) (hε : 0 < ε)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (m g κ s : ℝ) (t : ℕ → ℝ)
    (f : ℕ → Hilbert) (hn : ∀ n, ‖f n‖ = 1) (χ : Frequencies → ℂ)
    (hc : ∀ z, Tendsto (fun n => evolvedCharacteristic ε hε (h n) (hh n) (hb n)
      m g κ s (t n) (f n) z) atTop (𝓝 (χ z))) :
    χ 0 = 1 ∧ (∀ z, ‖χ z‖ ≤ 1 ∧ χ (-z) = starRingEnd ℂ (χ z)) ∧
      ∀ (N : ℕ) (z : Fin N → Frequencies) (c : Fin N → ℂ),
        0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i)*c j*χ (z j-z i)).re ∧
          (∑ i, ∑ j, starRingEnd ℂ (c i)*c j*χ (z j-z i)).im = 0 := by
  let v : ℕ → Hilbert := fun n => evolution ε hε (h n) (hh n) (hb n) m g κ s (t n) (f n)
  have hv (n : ℕ) : ‖v n‖ = 1 := by simp only [v,evolution_norm,hn]
  exact ⟨limit_zero volume h v hv χ hc,
    fun z => ⟨limit_bound volume h v hv χ hc z,limit_conjugate volume h hz v hv χ hc z⟩,
    limit_positive_kernel volume h hz v hv χ hc⟩

theorem evolved_dirac_uniform_limit (ε : ℝ) (hε : 0 < ε)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (m g κ s : ℝ) (f : ℕ → Hilbert) (hn : ∀ n, ‖f n‖ = 1)
    (z w : Frequencies) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ,
      ‖KFCausalCanonicalWeylDirac.residual volume (h n) z w
        (evolution ε hε (h n) (hh n) (hb n) m g κ s t (f n))‖ < δ := by
  obtain ⟨N,hN⟩ := KFCausalCanonicalWeylDirac.residual_uniform_limit volume h hh hz z w δ hδ
  exact ⟨N,fun n hn' t => hN n hn' _ (by simp only [evolution_norm,hn])⟩

#print axioms operator_eq_observable
#print axioms evolvedCharacteristic_initial
#print axioms evolvedCharacteristic_bound
#print axioms evolvedCharacteristic_continuous_time
#print axioms evolved_commutator_bound
#print axioms evolved_commutator_uniform_limit
#print axioms evolved_limit_properties
#print axioms evolved_dirac_uniform_limit

end
end UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics
