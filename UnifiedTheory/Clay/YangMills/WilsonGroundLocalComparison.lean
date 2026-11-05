/- Actual finite-block comparison for the constructed Wilson ground state and
its normalized transition density. Constants depend on the changed links,
not on the full spatial volume. No mixing estimate is asserted. -/
import UnifiedTheory.Clay.YangMills.WilsonPositiveGroundState
import UnifiedTheory.Clay.YangMills.WilsonSlabLocalComparison
import UnifiedTheory.Clay.YangMills.WilsonSlabTransitionComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonGroundLocalComparison
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonTimeSlab

/-- A single-coordinate comparison telescopes over exactly the finite set of changed coordinates. -/
theorem finite_change_comparison {I G : Type*} (F : (I → G) → ℝ) (c : ℝ)
    (hF : ∀ e u v, (∀ q, q ≠ e → u q = v q) → F u ≤ Real.exp c * F v)
    (S : Finset I) (u v : I → G) (huv : ∀ q, q ∉ S → u q = v q) :
    F u ≤ Real.exp (c * (S.card : ℝ)) * F v := by
  classical
  induction S using Finset.induction_on generalizing u v with
  | empty =>
    have he : u = v := funext (fun q => huv q (by simp))
    simp [he]
  | @insert e S he ih =>
    let w := Function.update u e (v e)
    have h1 : ∀ q, q ≠ e → u q = w q := by
      intro q hq
      simp [w, Function.update_of_ne hq]
    have h2 : ∀ q, q ∉ S → w q = v q := by
      intro q hq
      by_cases hqe : q = e
      · simp [w, hqe]
      · simpa [w, Function.update_of_ne hqe] using huv q (by simp [hq, hqe])
    calc
      F u ≤ Real.exp c * F w := hF e u w h1
      _ ≤ Real.exp c * (Real.exp (c * (S.card : ℝ)) * F v) :=
        mul_le_mul_of_nonneg_left (ih w v h2) (Real.exp_pos _).le
      _ = _ := by
        rw [← mul_assoc, ← Real.exp_add, Finset.card_insert_of_notMem he, Nat.cast_add,
          Nat.cast_one]
        congr 2
        ring

variable (n : ℕ) [NeZero n]

/-- A chosen actual positive unit ground state, using the proved existence theorem. -/
def ground (β : ℝ) (hβ : 0 ≤ β) : C(Slice n, ℝ) :=
  (WilsonPositiveGroundState.exists_positive_top_eigenfunction n β hβ).choose

theorem ground_pos (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) : 0 < ground n β hβ u :=
  (WilsonPositiveGroundState.exists_positive_top_eigenfunction n β hβ).choose_spec.1 u

theorem ground_square_integral (β : ℝ) (hβ : 0 ≤ β) :
    (∫ u, (ground n β hβ u) ^ 2 ∂measure n) = 1 :=
  (WilsonPositiveGroundState.exists_positive_top_eigenfunction n β hβ).choose_spec.2.1

theorem ground_equation (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    (∫ v, kernel WilsonSingleLinkStaples.character β 2 u v * ground n β hβ v ∂measure n) =
      ‖transfer n β‖ * ground n β hβ u :=
  (WilsonPositiveGroundState.exists_positive_top_eigenfunction n β hβ).choose_spec.2.2.2.2 u

/-- The fundamental SU(2) trace has the actual dimension-two bound. -/
theorem character_bound (q : Q) : ‖WilsonSingleLinkStaples.character q‖ ≤ 2 := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    UnitaryCharacterObservables.unitary_trace_bound (WilsonEnergyDensity.representation q)

/-- Changing one true spatial link changes the full kernel by at most exp(12 beta). -/
theorem kernel_single_link (β : ℝ) (hβ : 0 ≤ β) (e : SpatialVertex n × Fin 3)
    (u u' v : Slice n) (hu : ∀ q, q ≠ e → u q = u' q) :
    kernel WilsonSingleLinkStaples.character β 2 u v ≤
      Real.exp (12 * β) * kernel WilsonSingleLinkStaples.character β 2 u' v := by
  have h := WilsonSlabLocalComparison.kernel_comparison n Q
    WilsonSingleLinkStaples.character WilsonSingleLinkStaples.character_continuous
    2 (by norm_num) character_bound β 2 e.1 e.2 u u' v hu
  simpa only [abs_of_nonneg hβ, show 6 * β * 2 = 12 * β by ring] using h

/-- Kernel comparison for an arbitrary finite set of changed spatial links. -/
theorem kernel_block (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (u u' v : Slice n) (hu : ∀ q, q ∉ S → u q = u' q) :
    kernel WilsonSingleLinkStaples.character β 2 u v ≤
      Real.exp (12 * β * (S.card : ℝ)) * kernel WilsonSingleLinkStaples.character β 2 u' v :=
  finite_change_comparison (fun w => kernel WilsonSingleLinkStaples.character β 2 w v)
    (12 * β) (fun e w w' hw => kernel_single_link n β hβ e w w' v hw) S u u' hu

/-- The constructed positive top ground state inherits the actual single-link constant. -/
theorem ground_single_link (β : ℝ) (hβ : 0 ≤ β) (e : SpatialVertex n × Fin 3)
    (u u' : Slice n) (hu : ∀ q, q ≠ e → u q = u' q) :
    ground n β hβ u ≤ Real.exp (12 * β) * ground n β hβ u' := by
  have h := WilsonSlabLocalComparison.eigenfunction_comparison n Q
    WilsonSingleLinkStaples.character WilsonSingleLinkStaples.character_continuous
    2 (by norm_num) character_bound β 2 (measure n) (ground n β hβ)
    (ground n β hβ).continuous (fun v => (ground_pos n β hβ v).le)
    ‖transfer n β‖ (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1
    (ground_equation n β hβ) e.1 e.2 u u' hu
  simpa only [abs_of_nonneg hβ, show 6 * β * 2 = 12 * β by ring] using h

/-- The ground-state comparison depends only on the number of changed links. -/
theorem ground_block (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (u u' : Slice n) (hu : ∀ q, q ∉ S → u q = u' q) :
    ground n β hβ u ≤ Real.exp (12 * β * (S.card : ℝ)) * ground n β hβ u' :=
  finite_change_comparison (ground n β hβ) (12 * β)
    (ground_single_link n β hβ) S u u' hu

/-- The actual Doob transition density relative to spatial Haar. -/
def transition (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n) : ℝ :=
  GroundStateDirichlet.transition (kernelMap n β) (ground n β hβ) ‖transfer n β‖ u v

theorem transition_pos (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n) :
    0 < transition n β hβ u v := by
  exact div_pos (mul_pos (kernel_positive WilsonSingleLinkStaples.character
    WilsonSingleLinkStaples.character_continuous β 2 u v) (ground_pos n β hβ v))
    (mul_pos (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1
      (ground_pos n β hβ u))

theorem transition_mass (β : ℝ) (hβ : 0 ≤ β) (u : Slice n) :
    (∫ v, transition n β hβ u v ∂measure n) = 1 :=
  GroundStateDirichlet.transition_normalized (measure n) (kernelMap n β) (ground n β hβ)
    (ground_pos n β hβ) ‖transfer n β‖
    (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1 (ground_equation n β hβ) u

/-- The actual positive ground construction discharges the one-link transition premises. -/
theorem transition_single_link (β : ℝ) (hβ : 0 ≤ β) (e : SpatialVertex n × Fin 3)
    (u u' v : Slice n) (hu : ∀ q, q ≠ e → u q = u' q) :
    transition n β hβ u v ≤ Real.exp (24 * β) * transition n β hβ u' v := by
  have h := WilsonSlabTransitionComparison.transition_local_comparison n Q
    WilsonSingleLinkStaples.character WilsonSingleLinkStaples.character_continuous
    2 (by norm_num) character_bound β 2 (ground n β hβ)
    (ground n β hβ).continuous (ground_pos n β hβ)
    ‖transfer n β‖ (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1
    (ground_equation n β hβ) e.1 e.2 u u' v hu
  simpa only [abs_of_nonneg hβ, show 12 * β * 2 = 24 * β by ring] using h

/-- The normalized transition density has finite-block row ratio exp(24 beta card S).
Its constant is independent of the total number of lattice links. -/
theorem transition_block (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (u u' v : Slice n) (hu : ∀ q, q ∉ S → u q = u' q) :
    transition n β hβ u v ≤
      Real.exp (24 * β * (S.card : ℝ)) * transition n β hβ u' v :=
  finite_change_comparison (fun w => transition n β hβ w v) (24 * β)
    (fun e w w' hw => transition_single_link n β hβ e w w' v hw) S u u' hu

/-- Literal row-density ratios are well defined because the actual transition
is strictly positive. -/
theorem transition_ratio_bound (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset (SpatialVertex n × Fin 3)) (u u' v : Slice n)
    (hu : ∀ q, q ∉ S → u q = u' q) :
    transition n β hβ u v / transition n β hβ u' v ≤
      Real.exp (24 * β * (S.card : ℝ)) :=
  (div_le_iff₀ (transition_pos n β hβ u' v)).mpr (transition_block n β hβ S u u' v hu)

end
end UnifiedTheory.Clay.YangMills.WilsonGroundLocalComparison
