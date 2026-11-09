/- Extensive iterated maximal-packing schedule on the four-dimensional periodic
Wilson lattice, with complete finite-volume covariance exhaustion. The initial
packed block eliminates at least 1/25 of all lattice links, every stage is
automatically admissible for the evolved supports, and after at most
|Edge (Vertex n)| steps the retained covariance vanishes identically, reducing
the nonlocal remainder after ultraviolet contact subtraction to a pure finite
sum of coarse stage noise kernels. -/
import UnifiedTheory.Clay.YangMills.FiniteFactorPackingTower
import UnifiedTheory.Clay.YangMills.WilsonCoarseCovariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonExtensiveSchedule
noncomputable section
open MeasureTheory Filter RegulatedGauge PeriodicLattice4 LocalFields
open WilsonIndependentBlocks SingleLinkWilsonOscillation WilsonSingleLinkStaples
open WilsonInducedSupport WilsonFactorTower WilsonIteratedNoiseKernel
open WilsonGrowingContact GrowingStageContactPath WilsonCoarseCovariance
open FiniteFactorConditional FiniteFactorElimination FiniteFactorIteration
open FiniteFactorResponseIteration FiniteFactorPackingTower GibbsExhaustedTower
open scoped Topology

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _
local instance plaquetteDecidableEq : DecidableEq (PlaquetteIndex n) := Classical.decEq _

/-- Every function on a finite product space depends on the full coordinate Finset. -/
theorem dependsOn_univ {I X : Type*} [Fintype I] (F : (I → X) → ℝ) :
    DependsOn F ((Finset.univ : Finset I) : Set I) := by
  intro U V hUV
  congr 1
  funext i
  exact hUV i (Finset.mem_univ i)

/-- Plaquette factors touching a lattice edge coincide with its six affected plaquettes. -/
theorem plaquette_touching_eq_affected (e : Edge (Vertex n)) :
    touching (plaquetteEdges n) e = affected n (edgeCoord n e).1 (edgeCoord n e).2 := by
  ext p
  simp only [touching, Finset.mem_filter, Finset.mem_univ, true_and, mem_plaquetteEdges]

/-- Every lattice edge touches at most six original plaquette supports. -/
theorem plaquette_touching_card_le (e : Edge (Vertex n)) :
    (touching (plaquetteEdges n) e).card ≤ 6 := by
  rw [plaquette_touching_eq_affected]
  exact affected_card n (edgeCoord n e).1 (edgeCoord n e).2

/-- On a nondegenerate periodic lattice (n > 1), every edge touches exactly six plaquettes. -/
theorem plaquette_touching_card_eq_six [Fact (1 < n)] (e : Edge (Vertex n)) :
    (touching (plaquetteEdges n) e).card = 6 := by
  rw [plaquette_touching_eq_affected]
  exact affected_card_eq_six n (edgeCoord n e).1 (edgeCoord n e).2

/-- Total number of oriented links on the four-dimensional periodic lattice of period n. -/
def edgeCount : ℕ := Fintype.card (Edge (Vertex n))

/-- Canonical iterated maximal-packing schedule for the periodic four-dimensional Wilson lattice. -/
def wilsonSchedule : ℕ → Finset (Edge (Vertex n)) :=
  packedSchedule (plaquetteEdges n) Finset.univ

/-- The canonical packed Wilson schedule is admissible at every elimination depth. -/
theorem wilsonSchedule_admissible : Admissible n (wilsonSchedule n) :=
  packedSchedule_admissible (plaquetteEdges n) Finset.univ

/-- Distinct stages of the canonical Wilson schedule eliminate disjoint link blocks. -/
theorem wilsonSchedule_disjoint {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (wilsonSchedule n j) (wilsonSchedule n k) :=
  packedSchedule_disjoint (plaquetteEdges n) Finset.univ hjk

/-- Extensive initial block: the first maximal-packing step eliminates ≥ 1/25 of all links. -/
theorem wilsonSchedule_zero_card_bound :
    edgeCount n ≤ 25 * (wilsonSchedule n 0).card := by
  have h := packedSchedule_zero_card_bound (plaquetteEdges n)
    (Finset.univ : Finset (Edge (Vertex n))) 4 6
    (plaquetteEdges_card n) (plaquette_touching_card_le n)
  simpa only [Finset.card_univ, edgeCount, wilsonSchedule] using h

/-- The initial packed Wilson block is nonempty on every periodic lattice. -/
theorem wilsonSchedule_zero_nonempty : (wilsonSchedule n 0).Nonempty := by
  apply packedSchedule_nonempty (plaquetteEdges n) Finset.univ 0
  exact ⟨WilsonUniformVariance.selectedLink n 0 0, Finset.mem_univ _⟩

/-- Stagewise quantitative packing density bound for the canonical Wilson schedule. -/
theorem wilsonSchedule_stage_card_bound (k : ℕ) :
    (active Finset.univ (wilsonSchedule n) k).card ≤
      (2 ^ k * 6 * sizeEnvelope 4 6 k + 1) * (wilsonSchedule n k).card :=
  packedSchedule_stage_card_bound (plaquetteEdges n) Finset.univ 4 6
    (plaquetteEdges_card n) (plaquette_touching_card_le n) k

/-- All lattice links are eliminated from the active inventory by depth edgeCount n. -/
theorem wilson_active_eq_empty {N : ℕ} (hN : edgeCount n ≤ N) :
    active Finset.univ (wilsonSchedule n) N = ∅ :=
  active_eq_empty_of_card_le (plaquetteEdges n) Finset.univ
    (by simpa only [Finset.card_univ, edgeCount] using hN)

/-- At any exhaustion depth N ≥ edgeCount n, the conditional Wilson source response is constant. -/
theorem wilson_response_const (β : ℝ) (f : PlaquetteIndex n → ℝ) {N : ℕ}
    (hN : edgeCount n ≤ N) (U V : Configuration (Vertex n) Q) :
    response n β (wilsonSchedule n) f N U = response n β (wilsonSchedule n) f N V := by
  have hact : (⟨FiniteFactorConditional.action (initialFactor n β),
      FiniteFactorConditional.action_continuous _ (initialFactor_continuous n β)⟩ :
        C(Configuration (Vertex n) Q, ℝ)) = initialAction n β := by
    ext W
    exact congrFun (initial_sum n β) W
  unfold response
  rw [← hact]
  exact observable_const_of_exhausted (compactHaar Q) (plaquetteEdges n)
    (initialFactor n β) (initialFactor_continuous n β) (initialFactor_dependsOn n β)
    (wilsonSchedule n) (wilsonSchedule_admissible n) (sourceMap n f)
    Finset.univ Finset.univ (dependsOn_univ _)
    (fun _ => Finset.subset_univ _) Finset.Subset.rfl N (wilson_active_eq_empty n hN) U V

/-- At any exhaustion depth N ≥ edgeCount n, the retained Wilson source covariance vanishes. -/
theorem wilson_covarianceAt_eq_zero (β : ℝ) (f g : PlaquetteIndex n → ℝ) {N : ℕ}
    (hN : edgeCount n ≤ N) :
    GibbsCrossCovariance.covariance (law n β (wilsonSchedule n) N)
      (response n β (wilsonSchedule n) f N) (response n β (wilsonSchedule n) g N) = 0 := by
  have hact : (⟨FiniteFactorConditional.action (initialFactor n β),
      FiniteFactorConditional.action_continuous _ (initialFactor_continuous n β)⟩ :
        C(Configuration (Vertex n) Q, ℝ)) = initialAction n β := by
    ext W
    exact congrFun (initial_sum n β) W
  change GibbsCoordinateTower.covarianceAt (compactHaar Q) (wilsonSchedule n)
    (initialAction n β) (sourceMap n f) (sourceMap n g) N = 0
  rw [← hact]
  exact packedSchedule_covarianceAt_eq_zero (compactHaar Q) (plaquetteEdges n)
    (initialFactor n β) (initialFactor_continuous n β) (initialFactor_dependsOn n β)
    (sourceMap n f) (sourceMap n g) Finset.univ Finset.univ (dependsOn_univ _)
    (fun _ => Finset.subset_univ _) Finset.Subset.rfl N
    (by simpa only [Finset.card_univ, edgeCount] using hN)

/-- Complete finite-volume Wilson covariance decomposition into stage noise bilinear forms. -/
theorem wilson_covariance_eq_sum (β : ℝ) (f g : PlaquetteIndex n → ℝ) {N : ℕ}
    (hN : edgeCount n ≤ N) :
    GibbsCrossCovariance.covariance (wilsonLaw n Q character β 2)
      (WilsonBlockNoiseKernel.source n f) (WilsonBlockNoiseKernel.source n g) =
      ∑ j ∈ Finset.range N, bilinear n β (wilsonSchedule n) j f g := by
  rw [WilsonIteratedSourcePairing.covariance_telescope n β (wilsonSchedule n) N f g,
    wilson_covarianceAt_eq_zero n β f g hN, add_zero]

/-- Physical retained covariance vanishes identically at any exhaustion depth N ≥ edgeCount n. -/
theorem retainedCovariance_eq_zero_of_exhausted (β a : ℝ) {N : ℕ} (hN : edgeCount n ≤ N)
    (plane plane' : Plane) (f g : TestFunction) :
    retainedCovariance n β a (wilsonSchedule n) N plane plane' f g = 0 := by
  unfold retainedCovariance
  rw [wilson_covarianceAt_eq_zero n β _ _ hN, mul_zero]

/-- Explicit finite sum of coarse stage noise kernels from UV depth J to exhaustion edgeCount n. -/
def exhaustedCoarseSum (β a : ℝ) (J : ℕ) (plane plane' : Plane) (f g : TestFunction) : ℝ :=
  (a ^ 8)⁻¹ * ∑ j ∈ Finset.range (edgeCount n - J),
    bilinear n β (wilsonSchedule n) (J + j)
      (WilsonPhysicalCellWeights.weight n a plane f)
      (WilsonPhysicalCellWeights.weight n a plane' g)

/-- Under the canonical packed schedule, the coarse covariance through exhaustion equals the
pure finite sum of coarse stage noise kernels with no unintegrated remainder. -/
theorem coarseCovariance_eq_exhaustedCoarseSum (β a : ℝ) (J : ℕ)
    (plane plane' : Plane) (f g : TestFunction) :
    coarseCovariance n β a (wilsonSchedule n) J (edgeCount n - J) plane plane' f g =
      exhaustedCoarseSum n β a J plane plane' f g := by
  have hle : edgeCount n ≤ J + (edgeCount n - J) := by omega
  unfold coarseCovariance exhaustedCoarseSum
  rw [retainedCovariance_eq_zero_of_exhausted n β a hle plane plane' f g, add_zero]

/-- The retained covariance at any UV depth J equals the finite coarse noise sum to exhaustion. -/
theorem retainedCovariance_eq_exhaustedCoarseSum (β a : ℝ) (J : ℕ)
    (plane plane' : Plane) (f g : TestFunction) :
    retainedCovariance n β a (wilsonSchedule n) J plane plane' f g =
      exhaustedCoarseSum n β a J plane plane' f g := by
  rw [← coarseCovariance_eq_retained n β a (wilsonSchedule n) J (edgeCount n - J),
    coarseCovariance_eq_exhaustedCoarseSum]

/-- Each diagonal exhausted coarse sum is nonnegative. -/
theorem exhaustedCoarseSum_self_nonneg (β a : ℝ) (J : ℕ) (plane : Plane) (f : TestFunction) :
    0 ≤ exhaustedCoarseSum n β a J plane plane f f := by
  rw [← retainedCovariance_eq_exhaustedCoarseSum]
  exact retained_self_nonneg n β a (wilsonSchedule n) J plane f

omit [NeZero n] in
/-- Along the growing path, the contact-repaired physical covariance minus the pure finite sum of
coarse stage noise kernels converges to zero on every real Schwartz product test. -/
theorem growing_exhausted_coarse_repair_tendsto (β : ℕ → ℝ)
    (plane plane' : Plane) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0) :
    Tendsto (fun k =>
      WilsonSchwartzCovariance.fullCovariance (period k) (β k) (spacing k) plane plane' f g -
      (contactSum (period k) (β k) (spacing k) (radius k)
        (wilsonSchedule (period k)) k plane plane'
        (SchwartzProductTensor.tensor f g)).re -
      exhaustedCoarseSum (period k) (β k) (spacing k) k plane plane' f g)
      atTop (𝓝 0) := by
  have h := growing_real_coarse_repair_tendsto β
    (fun k => wilsonSchedule (period k))
    (fun k => wilsonSchedule_admissible (period k))
    (fun k => edgeCount (period k) - k) plane plane' f g hf hg
  simpa only [coarseCovariance_eq_exhaustedCoarseSum] using h

omit [NeZero n] in
/-- Continuum convergence of the contact-repaired Wilson covariance is equivalent to convergence
of the pure finite sum of coarse stage noise kernels from k to edgeCount (period k). -/
theorem repaired_limit_iff_exhaustedCoarseSum_limit (β : ℕ → ℝ)
    (plane plane' : Plane) (f g : TestFunction)
    (hf : ∀ x, (f x).im = 0) (hg : ∀ x, (g x).im = 0) (c : ℝ) :
    Tendsto (fun k => repairedCovariance (period k) (β k) (spacing k) (radius k)
      (wilsonSchedule (period k)) k plane plane' f g) atTop (𝓝 c) ↔
    Tendsto (fun k => exhaustedCoarseSum (period k) (β k) (spacing k) k
      plane plane' f g) atTop (𝓝 c) := by
  have h := repaired_limit_iff_coarse_limit β
    (fun k => wilsonSchedule (period k))
    (fun k => wilsonSchedule_admissible (period k))
    (fun k => edgeCount (period k) - k) plane plane' f g hf hg c
  simpa only [coarseCovariance_eq_exhaustedCoarseSum] using h

end
end UnifiedTheory.Clay.YangMills.WilsonExtensiveSchedule
