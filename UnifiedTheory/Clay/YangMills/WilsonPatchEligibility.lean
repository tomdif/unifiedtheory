/- One local energetic eligibility condition supplies all previously
required patch geometry and the exponential cap-complement margin. -/
import UnifiedTheory.Clay.YangMills.WilsonPatchExponentialCovariance

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonPatchEligibility
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonSpatialCutEnergy WilsonPatchLocalEnergy
open WilsonPatchComplementTail WilsonPatchConditioning WilsonPatchGaussianPartition
open WilsonBoundaryConnected GibbsCrossCovariance
open scoped Quaternion

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _
local instance plaquetteDecidableEq : DecidableEq (Plaquette n) := Classical.decEq _

omit n [NeZero n] in
def threshold : ℝ := (1 / 256) ^ 2 / 2

omit n [NeZero n] in
theorem threshold_pos : 0 < threshold := by norm_num [threshold]

theorem background_nonneg (S : Finset (SpatialVertex n × Fin 3)) (v u w : Slice n) :
    0 ≤ backgroundCost n S v u w := by
  unfold backgroundCost
  positivity [incident_nonneg n S v, endpoint_nonneg n S v u w]

theorem incident_point_bound (S : Finset (SpatialVertex n × Fin 3)) (v : Slice n)
    (p : Plaquette n) (b : SpatialVertex n × Fin 3) (hb : b ∈ S) (hp : b ∈ support n p) :
    defect n v p ≤ incidentEnergy n S v := by
  have hnon (q : Plaquette n) : 0 ≤ defect n v q :=
    (WilsonSlabBounds.characterDefect_bounds _).1
  by_cases hbulk : p ∈ bulk n S
  · have hh := Finset.single_le_sum (f := defect n v) (fun q _ => hnon q) hbulk
    have h0 := (part_bounds n (boundary n S) v).1
    change defect n v p ≤ bulkPotential n S v at hh
    change 0 ≤ boundaryPotential n S v at h0
    unfold incidentEnergy
    linarith
  · have hout : p ∉ bulk n Sᶜ := by
      intro h
      have hh := (Finset.mem_filter.mp h).2 hp
      exact (Finset.mem_compl.mp hh) hb
    have hbd : p ∈ boundary n S := by
      simp only [boundary, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union]
      exact ⟨trivial, fun h => h.elim hbulk hout⟩
    have hh := Finset.single_le_sum (f := defect n v) (fun q _ => hnon q) hbd
    have h0 := (part_bounds n (bulk n S) v).1
    change defect n v p ≤ boundaryPotential n S v at hh
    change 0 ≤ bulkPotential n S v at h0
    unfold incidentEnergy
    linarith

omit [NeZero n] in
theorem defect_chord (v : Slice n) (p : Plaquette n) :
    defect n v p = ‖((spatialHolonomy v p.1 p.2.1.1 p.2.1.2 : Q) : ℍ) - 1‖ ^ 2 := by
  rw [SU2GaussianMass.chord_square]
  unfold defect
  rw [WilsonSingleLinkStaples.character_re]
  ring

omit [NeZero n] in
theorem link_kinetic_bound (S : Finset (SpatialVertex n × Fin 3)) (v u : Slice n)
    (b : SpatialVertex n × Fin 3) (hb : b ∈ S) :
    ‖(v b : ℍ) - (u b : ℍ)‖ ^ 2 ≤ kineticPart n S v u := by
  rw [kinetic_distance]
  exact Finset.single_le_sum (f := fun e => ‖(v e : ℍ) - (u e : ℍ)‖ ^ 2)
    (fun _ _ => sq_nonneg _) hb

/-- The single energy condition implies the incident-plaquette and both
endpoint chord hypotheses throughout the established patch argument. -/
theorem geometry (S : Finset (SpatialVertex n × Fin 3)) (v₀ u w : Slice n)
    (hgood : backgroundCost n S v₀ u w ≤ threshold) :
    (∀ p b, b ∈ S → b ∈ support n p →
      ‖((spatialHolonomy v₀ p.1 p.2.1.1 p.2.1.2 : Q) : ℍ) - 1‖ ≤ 1 / 64) ∧
    (∀ b ∈ S, ‖(v₀ b : ℍ) - (u b : ℍ)‖ ≤ 1 / 2) ∧
    (∀ b ∈ S, ‖(v₀ b : ℍ) - (w b : ℍ)‖ ≤ 1 / 2) := by
  have hi := incident_nonneg n S v₀
  have hu := kinetic_nonneg n S v₀ u
  have hw := kinetic_nonneg n S v₀ w
  unfold backgroundCost endpointEnergy threshold at hgood
  refine ⟨?_, ?_, ?_⟩
  · intro p b hb hp
    have hh := incident_point_bound n S v₀ p b hb hp
    rw [defect_chord] at hh
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 64)).mp
    linarith
  · intro b hb
    have hh := link_kinetic_bound n S v₀ u b hb
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp
    linarith
  · intro b hb
    have hh := link_kinetic_bound n S v₀ w b hb
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp
    linarith

def budget (β : ℝ) (S : Finset (SpatialVertex n × Fin 3)) (a M : ℝ) : ℝ :=
  8 * (S.card : ℝ) * Real.log 81 / (β - a) +
    20 * Real.exp ((S.card : ℝ) * Real.log (gaussianCap β) + 2 * M - β * threshold)

omit [NeZero n] in
theorem budget_nonneg (β : ℝ) (S : Finset (SpatialVertex n × Fin 3))
    (a M : ℝ) (hβ : a < β) : 0 ≤ budget n β S a M := by
  unfold budget
  have hl : 0 ≤ Real.log 81 := Real.log_nonneg (by norm_num)
  have hd : 0 < β - a := sub_pos.mpr hβ
  positivity

theorem connected_good (β : ℝ) (hβ : 1 < β) (u w : Slice n)
    (e d : SpatialVertex n × Fin 3) (hed : e ≠ d) (q r : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (hgood : backgroundCost n S v₀ u w ≤ threshold) :
    |covariance (interiorLaw n S v₀ (WilsonTiltedMiddleAction.action n β u w e d q r s t))
      (source n β e q u ∘ insert n S v₀) (source n β d r u ∘ insert n S v₀)| ≤
      budget n β S 1 4 := by
  obtain ⟨hflat, hu, hw⟩ := geometry n S v₀ u w hgood
  have hc := WilsonPatchExponentialCovariance.connected_bound n β hβ u w e d hed
    q r hq hr s t hs ht S v₀ hflat hu hw
  have hb := tailBound_suppressed n β (by linarith) S v₀ u w (1 / 256) 4 hgood
  unfold budget threshold
  rw [← mul_div_assoc β ((1 / 256) ^ 2) 2]
  linarith only [hc, hb]

theorem transport_good (β : ℝ) (hβ : 2 < β) (u w : Slice n)
    (e d b : SpatialVertex n × Fin 3) (hed : e ≠ d) (q r p : Q)
    (hq : β * ‖(q : ℍ) - 1‖ ≤ 1) (hr : β * ‖(r : ℍ) - 1‖ ≤ 1)
    (hp : β * ‖(p : ℍ) - 1‖ ≤ 1)
    (s t h : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hh : h ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (SpatialVertex n × Fin 3)) (v₀ : Slice n)
    (hgood : backgroundCost n S v₀ u w ≤ threshold) :
    |covariance (interiorLaw n S v₀ (CompactGibbsSource.action
        (WilsonTiltedMiddleAction.action n β u w e d q r s t) (source n β b p w) h))
      (source n β e q u ∘ insert n S v₀) (source n β b p w ∘ insert n S v₀)| ≤
      budget n β S 2 6 := by
  obtain ⟨hflat, hu, hw⟩ := geometry n S v₀ u w hgood
  have hc := WilsonPatchExponentialCovariance.transport_connected_bound n β hβ u w e d b hed
    q r p hq hr hp s t h hs ht hh S v₀ hflat hu hw
  have hb := tailBound_suppressed n β (by linarith) S v₀ u w (1 / 256) 6 hgood
  unfold budget threshold
  rw [← mul_div_assoc β ((1 / 256) ^ 2) 2]
  linarith only [hc, hb]

end
end UnifiedTheory.Clay.YangMills.WilsonPatchEligibility
