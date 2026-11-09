/- Source-weighted exponential suppression of a connected high-defect
plaquette cluster joining two prescribed plaquettes. This controls bad
connectivity, not the mixed logarithmic response of the ground state. -/
import UnifiedTheory.Clay.YangMills.WilsonConnectedWeakCoupling
import UnifiedTheory.Clay.YangMills.FiniteConnectedDistance

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonBadClusterBridge
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonTimeSlab WilsonGroundHeatBath
open WilsonPhysicalVariance WilsonHighFieldDecay WilsonTemporalGauge WilsonGroundLocalComparison
open SpatialPlaquetteCutGeometry SpatialWilsonPlaquetteKernels WilsonGroundSlabEnergy
open WilsonClusterSourceDecay WilsonConnectedActivity

variable (n : ℕ) [NeZero n]

open Classical in
def sets (p q : Plaquette (2 * n)) : Finset (Finset (Plaquette (2 * n))) :=
  Finset.univ.filter (fun S => p ∈ S ∧ q ∈ S ∧
    ((WilsonPlaquetteGraph.graph (2 * (2 * n))).induce
      (S : Set (Plaquette (2 * n)))).Preconnected)

theorem sets_mem (p q : Plaquette (2 * n)) (S : Finset (Plaquette (2 * n))) :
    S ∈ sets n p q ↔ p ∈ S ∧ q ∈ S ∧
      ((WilsonPlaquetteGraph.graph (2 * (2 * n))).induce
        (S : Set (Plaquette (2 * n)))).Preconnected := by
  classical
  simp only [sets, Finset.mem_filter, Finset.mem_univ, true_and]

def event (p q : Plaquette (2 * n)) (R : ℝ) : Set (Slice (2 * (2 * n))) :=
  WilsonPatchCover.bad (2 * n) (fun S : sets n p q => S.val) (fun _ => R)

def distance (p q : Plaquette (2 * n)) : ℕ :=
  (WilsonPlaquetteGraph.graph (2 * (2 * n))).dist p q

theorem event_measurable (p q : Plaquette (2 * n)) (R : ℝ) :
    MeasurableSet (event n p q R) := WilsonPatchCover.bad_measurable (2 * n) _ _

theorem event_subset (p q : Plaquette (2 * n)) (R : ℝ) :
    event n p q R ⊆ WilsonConnectedSource.event n p (distance n p q + 1) R := by
  rintro u ⟨S,hS⟩
  obtain ⟨hp,hq,hconn⟩ := (sets_mem n p q S.val).mp S.property
  have hd := FiniteConnectedDistance.distance_lt_card
    (WilsonPlaquetteGraph.graph (2 * (2 * n))) S.val p q hp hq hconn
  apply (WilsonConnectedSource.mem_event n p _ R u).mpr
  exact ⟨S.val,hp,hd,hconn,fun r hr => hS ⟨r,hr⟩⟩

theorem mass_le (p q : Plaquette (2 * n)) (R β : ℝ) (hβ : 0 ≤ β)
    (f : C(Slice (2 * (2 * n)), ℝ)) :
    (∫ u, (event n p q R).indicator (fun v => (f v)^2) u
      ∂groundLaw (2 * (2 * n)) β hβ) ≤
    (∫ u, (WilsonConnectedSource.event n p (distance n p q + 1) R).indicator
      (fun v => (f v)^2) u ∂groundLaw (2 * (2 * n)) β hβ) := by
  letI := groundLaw_probability (2 * (2 * n)) β hβ
  have hi := CompactDensityEntropy.continuous_integrable (groundLaw (2 * (2 * n)) β hβ)
    _ (f.continuous.pow 2)
  apply integral_mono (hi.indicator (event_measurable n p q R))
    (hi.indicator (WilsonConnectedSource.event_measurable n p _ R))
  intro u
  by_cases hu : u ∈ event n p q R
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (event_subset n p q R hu)]
  · rw [Set.indicator_of_notMem hu]
    exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) u

theorem source_tail (p q : Plaquette (2 * n))
    (β : ℝ) (hβ : 0 < β) (R : ℝ) (hmargin : 96 * envelope β ≤ R) (hR : 0 < R)
    (hsmall : 256 * rate β R < 1) (f : C(Slice (2 * (2 * n)), ℝ)) :
    (∫ u, (event n p q R).indicator (fun v => (f v)^2) u
      ∂groundLaw (2 * (2 * n)) β hβ.le) ≤
      2 * loss (2 * (2 * n)) β hβ.le f +
        2 * (rate β R * (256 * rate β R)^(distance n p q) / (1 - 256 * rate β R)) *
          mass (2 * (2 * n)) β hβ.le f := by
  have h := (mass_le n p q R β hβ.le f).trans
    (WilsonConnectedSource.source_tail n p (distance n p q + 1) (by omega)
      β hβ R hmargin hR hsmall f)
  simpa only [budget, Nat.add_sub_cancel] using h

theorem weak_coupling_tail (p q : Plaquette (2 * n))
    (β : ℝ) (hβ : 256 ≤ β) (f : C(Slice (2 * (2 * n)), ℝ)) :
    (∫ u, (event n p q (WilsonClusterActivity.threshold β)).indicator (fun v => (f v)^2) u
      ∂groundLaw (2 * (2 * n)) β (by linarith)) ≤
      2 * loss (2 * (2 * n)) β (by linarith) f +
        (4 / (2 * β + 5)) * (1 / 2 : ℝ)^(distance n p q) *
          mass (2 * (2 * n)) β (by linarith) f := by
  have h := (mass_le n p q (WilsonClusterActivity.threshold β) β (by linarith) f).trans
    (WilsonConnectedWeakCoupling.source_tail n p (distance n p q + 1) (by omega) β hβ f)
  simpa only [Nat.add_sub_cancel] using h

theorem physical_tail (p q : Plaquette (2 * n))
    (β : ℝ) (hβ : 256 ≤ β) (f : C(Slice (2 * (2 * n)), ℝ))
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) :
    (∫ u, (event n p q (WilsonClusterActivity.threshold β)).indicator (fun v => (f v)^2) u
      ∂groundLaw (2 * (2 * n)) β (by linarith)) ≤
      2 * (mass (2 * (2 * n)) β (by linarith) f -
        ∫ u, (∫ v, transition (2 * (2 * n)) β (by linarith) u v * f v
          ∂WilsonSlabOperator.measure (2 * (2 * n)))^2
          ∂groundLaw (2 * (2 * n)) β (by linarith)) +
        (4 / (2 * β + 5)) * (1 / 2 : ℝ)^(distance n p q) *
          mass (2 * (2 * n)) β (by linarith) f := by
  rw [WilsonClusterPhysicalSource.full_mass n β (by linarith) f hinv, ← loss_mass]
  exact weak_coupling_tail n p q β hβ f

end
end UnifiedTheory.Clay.YangMills.WilsonBadClusterBridge
