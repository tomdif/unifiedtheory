/- Derived finite range for every actual Wilson elimination stage.
The support radius follows the computed factor/source recursion. Vanishing of
the removed covariance is proved under each actual induced conditional law. -/
import UnifiedTheory.Clay.YangMills.WilsonIteratedNoiseKernel
import UnifiedTheory.Clay.YangMills.FiniteFactorResponseIteration
import UnifiedTheory.Clay.YangMills.FiniteFactorNoiseLocality
import UnifiedTheory.Clay.YangMills.PeriodicSupportRelation

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonIteratedNoiseLocality
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonSingleLinkStaples LocalFields
open WilsonFactorTower WilsonIteratedNoiseKernel WilsonInducedSupport
open FiniteFactorResponseIteration PeriodicSupportRelation

variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

/-- The response support is computed from every preceding actual support family. -/
def sourceSupport (T : ℕ → Finset (Edge (Vertex n))) (p : PlaquetteIndex n) (j : ℕ) :
    Finset (Edge (Vertex n)) := sourceSupports (plaquetteEdges n) T (plaquetteEdges n p) j

theorem response_dependsOn (β : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (hT : Admissible n T) (p : PlaquetteIndex n) (j : ℕ) :
    DependsOn (response n β T (WilsonBlockNoiseKernel.basis n p) j)
      (sourceSupport n T p j : Set _) := by
  have hF : DependsOn (sourceMap n (WilsonBlockNoiseKernel.basis n p))
      (plaquetteEdges n p : Set _) := by
    intro U V hUV
    change WilsonBlockNoiseKernel.source n (WilsonBlockNoiseKernel.basis n p) U =
      WilsonBlockNoiseKernel.source n (WilsonBlockNoiseKernel.basis n p) V
    rw [WilsonBlockNoiseKernel.source_basis, WilsonBlockNoiseKernel.source_basis]
    exact plaquetteTerm_dependsOn n Q character 2 p hUV
  have h := observable_dependsOn (compactHaar Q) (plaquetteEdges n) (initialFactor n β)
    (initialFactor_continuous n β) (initialFactor_dependsOn n β) T hT
    (sourceMap n (WilsonBlockNoiseKernel.basis n p)) (plaquetteEdges n p) hF j
  have hi : (⟨FiniteFactorConditional.action (initialFactor n β),
      FiniteFactorConditional.action_continuous _ (initialFactor_continuous n β)⟩ :
        C(Configuration (Vertex n) Q, ℝ)) = initialAction n β := by
    ext U
    exact congrFun (initial_sum n β) U
  rw [hi] at h
  exact h

/-- The actual response neighborhood has dyadic radius in periodic integer coordinates. -/
theorem sourceSupport_radius (T : ℕ → Finset (Edge (Vertex n))) (p : PlaquetteIndex n)
    (j : ℕ) (d : Edge (Vertex n)) (hd : d ∈ sourceSupport n T p j) :
    Close n (2 ^ j) (center n p) d :=
  sourceSupports_dyadic (Close n) (close_symm n) (close_mono n) (close_add n)
    (plaquetteEdges n) T (fun p e he d hd => plaquette_diameter n p e d he hd)
    (plaquetteEdges n p) (center n p)
    (plaquette_centered n p) j d hd

/-- Pure coordinate separation suffices to make the entire actual factor tower admissible. -/
theorem admissible_of_separation (T : ℕ → Finset (Edge (Vertex n)))
    (hT : ∀ j, ∀ e ∈ T j, ∀ d ∈ T j, e ≠ d → ¬Close n (2 ^ j) e d) : Admissible n T := by
  intro j
  exact stage_independent_of_separation (Close n) (close_symm n) (close_mono n) (close_add n)
    (plaquetteEdges n) T (fun p e he d hd => plaquette_diameter n p e d he hd) j (hT j)

/-- Disjoint computed response neighborhoods give zero actual stage covariance. -/
theorem coefficient_zero (β : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (hT : Admissible n T) (j : ℕ) (p q : PlaquetteIndex n)
    (hpq : Disjoint (sourceSupport n T p j) (sourceSupport n T q j)) :
    coefficient n β T j p q = 0 := by
  change GibbsCoordinateElimination.removedGram (compactHaar Q) (T j)
    (GibbsCoordinateTower.action (compactHaar Q) T (initialAction n β) j)
    (response n β T (WilsonBlockNoiseKernel.basis n p) j)
    (response n β T (WilsonBlockNoiseKernel.basis n q) j) = 0
  rw [← stageAction_eq_tower n β T hT j]
  exact FiniteFactorNoiseLocality.removedGram_zero (compactHaar Q) (supports n T j)
    (factors n β T j) (factors_continuous n β T j) (factors_dependsOn n β T j)
    (T j) (hT j) 1 _ _ (sourceSupport n T p j) (sourceSupport n T q j)
    (response_dependsOn n β T hT p j) (response_dependsOn n β T hT q j) hpq

/-- Literal physical range at every depth, with the exact periodic no-wrap requirement. -/
theorem kernel_zero_far (β a R : ℝ) (T : ℕ → Finset (Edge (Vertex n)))
    (hT : Admissible n T) (j : ℕ) (ha : 0 < a)
    (hperiod : 2 * R + (2 * (2 : ℝ) ^ j + 1) * a < (n : ℝ) * a)
    (plane plane' : Plane) (x y : Spacetime) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R)
    (hfar : (4 * (2 : ℝ) ^ j + 2) * a < ‖x - y‖) :
    kernel n β a T j plane plane' x y = 0 := by
  have hp : 2 * R + (2 * ((2 ^ j : ℕ) : ℝ) + 1) * a < (n : ℝ) * a := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hperiod
  have hf : (4 * ((2 ^ j : ℕ) : ℝ) + 2) * a < ‖x - y‖ := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hfar
  have hd := sample_supports_disjoint n (fun p => sourceSupport n T p j) (2 ^ j)
    (fun p d hd => sourceSupport_radius n T p j d hd) a R ha hp plane plane' x y hx hy hf
  unfold kernel
  rw [coefficient_zero n β T hT j _ _ hd, mul_zero]

end
end UnifiedTheory.Clay.YangMills.WilsonIteratedNoiseLocality
