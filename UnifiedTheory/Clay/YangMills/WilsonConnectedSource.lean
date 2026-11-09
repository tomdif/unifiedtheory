/- Summation of every rooted connected high-defect plaquette cluster.
The source loss is charged once, the root is fixed, and all cluster sizes
are included. The resulting coefficient is independent of spatial volume. -/
import UnifiedTheory.Clay.YangMills.WilsonConnectedActivity
import UnifiedTheory.Clay.YangMills.WilsonClusterPhysicalSource

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonConnectedSource
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonTimeSlab WilsonGroundHeatBath
open WilsonPhysicalVariance WilsonHighFieldDecay WilsonTemporalGauge WilsonGroundLocalComparison
open SpatialPlaquetteCutGeometry SpatialWilsonPlaquetteKernels WilsonGroundSlabEnergy
open WilsonClusterSourceDecay WilsonConnectedActivity

variable (n : ℕ) [NeZero n]

abbrev PatternIndex (p : Plaquette (2 * n)) (m : ℕ) :=
  Index (2 * (2 * n)) p m (Fintype.card (Plaquette (2 * n)) + 1)

def patterns (p : Plaquette (2 * n)) (m : ℕ) (i : PatternIndex n p m) :
    Finset (Plaquette (2 * n)) := marked (2 * (2 * n)) p m _ i

def event (p : Plaquette (2 * n)) (m : ℕ) (R : ℝ) : Set (Slice (2 * (2 * n))) :=
  WilsonPatchCover.bad (2 * n) (patterns n p m) (fun _ => R)

/-- This is exactly existence of a connected all-high-defect cluster of
size at least m containing the prescribed root plaquette. -/
theorem mem_event (p : Plaquette (2 * n)) (m : ℕ) (R : ℝ) (u : Slice (2 * (2 * n))) :
    u ∈ event n p m R ↔ ∃ S : Finset (Plaquette (2 * n)), p ∈ S ∧ m ≤ S.card ∧
      ((WilsonPlaquetteGraph.graph (2 * (2 * n))).induce
        (S : Set (Plaquette (2 * n)))).Preconnected ∧
      ∀ q ∈ S, 2 * R ≤ defect (2 * n) q u := by
  constructor
  · rintro ⟨i,hi⟩
    obtain ⟨hp,hcard,hconn⟩ := marked_spec (2 * (2 * n)) p m _ i
    exact ⟨patterns n p m i,hp,by change m ≤ (marked _ _ _ _ i).card; rw [hcard]; omega,hconn,
      fun q hq => hi ⟨q,hq⟩⟩
  · rintro ⟨S,hp,hm,hconn,hbad⟩
    obtain ⟨i,hi⟩ := (exists_index (2 * (2 * n)) p m S).mpr ⟨hp,hm,hconn⟩
    refine ⟨i,?_⟩
    intro q
    apply hbad q.val
    rw [← hi]
    exact q.property

theorem event_measurable (p : Plaquette (2 * n)) (m : ℕ) (R : ℝ) :
    MeasurableSet (event n p m R) := WilsonPatchCover.bad_measurable (2 * n) _ _

theorem activity_bound (p : Plaquette (2 * n)) (m : ℕ) (hm : 0 < m)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hsmall : 256 * ρ < 1) :
    (∑ i : PatternIndex n p m, ρ^(patterns n p m i).card) ≤ budget ρ m :=
  WilsonConnectedActivity.activity_bound (2 * (2 * n)) p m _ hm ρ hρ hsmall

/-- All connected sizes are summed with one variance-loss charge. -/
theorem source_tail (p : Plaquette (2 * n)) (m : ℕ) (hm : 0 < m)
    (β : ℝ) (hβ : 0 < β) (R : ℝ) (hmargin : 96 * envelope β ≤ R) (hR : 0 < R)
    (hsmall : 256 * rate β R < 1) (f : C(Slice (2 * (2 * n)), ℝ)) :
    (∫ u, (event n p m R).indicator (fun v => (f v)^2) u
      ∂groundLaw (2 * (2 * n)) β hβ.le) ≤
      2 * loss (2 * (2 * n)) β hβ.le f +
        2 * budget (rate β R) m * mass (2 * (2 * n)) β hβ.le f := by
  have h := WilsonClusterCover.weighted_union n β hβ (patterns n p m) (fun _ => R)
    (fun _ => hmargin) (fun _ => hR) f
  have hc := mul_le_mul_of_nonneg_right
    (activity_bound n p m hm (rate β R) (rate_pos β R).le hsmall)
    (mass_nonneg (2 * (2 * n)) β hβ.le f)
  change (∫ u, (event n p m R).indicator (fun v => (f v)^2) u
    ∂groundLaw (2 * (2 * n)) β hβ.le) ≤ _ at h
  nlinarith

theorem supported_decay (p : Plaquette (2 * n)) (m : ℕ) (hm : 0 < m)
    (β : ℝ) (hβ : 0 < β) (R : ℝ) (hmargin : 96 * envelope β ≤ R) (hR : 0 < R)
    (hsmall : 256 * rate β R < 1) (f : C(Slice (2 * (2 * n)), ℝ))
    (hs : ∀ u, u ∉ event n p m R → f u = 0) :
    mass (2 * (2 * n)) β hβ.le (step (2 * (2 * n)) β hβ.le f) ≤
      budget (rate β R) m * mass (2 * (2 * n)) β hβ.le f := by
  exact (WilsonClusterCover.union_decay n β hβ (patterns n p m) (fun _ => R)
    (fun _ => hmargin) (fun _ => hR) f hs).trans
    (mul_le_mul_of_nonneg_right
      (activity_bound n p m hm (rate β R) (rate_pos β R).le hsmall)
      (mass_nonneg (2 * (2 * n)) β hβ.le f))

theorem supported_loss (p : Plaquette (2 * n)) (m : ℕ) (hm : 0 < m)
    (β : ℝ) (hβ : 0 < β) (R : ℝ) (hmargin : 96 * envelope β ≤ R) (hR : 0 < R)
    (hsmall : 256 * rate β R < 1) (f : C(Slice (2 * (2 * n)), ℝ))
    (hs : ∀ u, u ∉ event n p m R → f u = 0) :
    (1 - budget (rate β R) m) * mass (2 * (2 * n)) β hβ.le f ≤
      loss (2 * (2 * n)) β hβ.le f := by
  rw [loss_mass]
  have h := supported_decay n p m hm β hβ R hmargin hR hsmall f hs
  linarith

theorem physical_tail (p : Plaquette (2 * n)) (m : ℕ) (hm : 0 < m)
    (β : ℝ) (hβ : 0 < β) (R : ℝ) (hmargin : 96 * envelope β ≤ R) (hR : 0 < R)
    (hsmall : 256 * rate β R < 1) (f : C(Slice (2 * (2 * n)), ℝ))
    (hinv : ∀ h u, f (gaugeSlice h u) = f u) :
    (∫ u, (event n p m R).indicator (fun v => (f v)^2) u
      ∂groundLaw (2 * (2 * n)) β hβ.le) ≤
      2 * (mass (2 * (2 * n)) β hβ.le f -
        ∫ u, (∫ v, transition (2 * (2 * n)) β hβ.le u v * f v
          ∂WilsonSlabOperator.measure (2 * (2 * n)))^2 ∂groundLaw (2 * (2 * n)) β hβ.le) +
        2 * budget (rate β R) m * mass (2 * (2 * n)) β hβ.le f := by
  rw [WilsonClusterPhysicalSource.full_mass n β hβ.le f hinv, ← loss_mass]
  exact source_tail n p m hm β hβ R hmargin hR hsmall f

end
end UnifiedTheory.Clay.YangMills.WilsonConnectedSource
