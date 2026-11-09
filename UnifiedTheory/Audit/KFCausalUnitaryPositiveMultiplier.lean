/- Positive self-adjoint multipliers transported through a unitary map.
The bounded resolvent is conjugated first; its inverse supplies the actual
unbounded operator, whose maximal graph and energy are proved below. -/
import UnifiedTheory.Audit.KFCausalPositiveMultiplierEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalUnitaryPositiveMultiplier
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalPositiveMultiplierResolvent
open UnifiedTheory.Audit.KFCausalPositiveMultiplierEnergy
open UnifiedTheory.Audit.KFCausalResolventHamiltonian
open UnifiedTheory.Audit.KFCausalInverseResolventGraph

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [MeasurableSpace X] {μ : Measure X}

def conjugateResolvent (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x) : H →L[ℂ] H :=
  (Ω.symm : Lp ℂ 2 μ →L[ℂ] H).comp ((resolvent w hm hw).comp (Ω : H →L[ℂ] Lp ℂ 2 μ))

theorem coordinate_resolvent (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x) (f : H) :
    Ω (conjugateResolvent Ω w hm hw f) = resolvent w hm hw (Ω f) := by
  change Ω (Ω.symm (resolvent w hm hw (Ω f))) = _
  exact Ω.apply_symm_apply _

theorem conjugate_injective (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x) :
    Function.Injective (conjugateResolvent Ω w hm hw) :=
  Ω.symm.injective.comp ((resolvent_injective w hm hw).comp Ω.injective)

theorem conjugate_symmetric (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x) (f g : H) :
    inner ℂ (conjugateResolvent Ω w hm hw f) g =
      inner ℂ f (conjugateResolvent Ω w hm hw g) := by
  calc
    _ = inner ℂ (Ω (conjugateResolvent Ω w hm hw f)) (Ω g) :=
      (Ω.inner_map_map _ _).symm
    _ = inner ℂ (Ω f) (Ω (conjugateResolvent Ω w hm hw g)) := by
      rw [coordinate_resolvent,coordinate_resolvent]
      exact resolvent_symmetric w hm hw _ _
    _ = _ := Ω.inner_map_map _ _

theorem conjugate_dense [CompleteSpace H] (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x) :
    DenseRange (conjugateResolvent Ω w hm hw) :=
  symmetric_injective_dense _ (conjugate_injective Ω w hm hw) (conjugate_symmetric Ω w hm hw)

def positivePullback (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x) : H →ₗ.[ℂ] H :=
  inverseShift (conjugateResolvent Ω w hm hw) (conjugate_injective Ω w hm hw)

theorem pullback_selfAdjoint [CompleteSpace H] (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x) :
    IsSelfAdjoint (positivePullback Ω w hm hw) :=
  inverseShift_selfAdjoint _ _ (conjugate_dense Ω w hm hw) (conjugate_symmetric Ω w hm hw)

theorem pullback_graph_iff (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x) (f g : H) :
    (f,g) ∈ (positivePullback Ω w hm hw).graph ↔
      Ω g =ᵐ[μ] fun x => (w x:ℂ)*(Ω f) x := by
  rw [← multiplier_graph_iff w hm hw (Ω f) (Ω g)]
  rw [positivePullback,positiveMultiplier,inverseShift_graph_iff,inverseShift_graph_iff]
  constructor
  · intro he
    have hΩ := congrArg Ω he
    simpa only [coordinate_resolvent,map_add] using hΩ
  · intro he
    apply Ω.injective
    rw [coordinate_resolvent,map_add]
    exact he

theorem pullback_domain_iff (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x) (f : H) :
    f ∈ (positivePullback Ω w hm hw).domain ↔ MemLp (fun x => (w x:ℂ)*(Ω f) x) 2 μ := by
  constructor
  · intro hf
    exact (Lp.memLp (Ω (positivePullback Ω w hm hw ⟨f,hf⟩))).ae_eq
      ((pullback_graph_iff Ω w hm hw f _).mp ((positivePullback Ω w hm hw).mem_graph ⟨f,hf⟩))
  · intro hp
    apply LinearPMap.mem_domain_of_mem_graph (y := Ω.symm (hp.toLp _))
    apply (pullback_graph_iff Ω w hm hw f _).mpr
    rw [Ω.apply_symm_apply]
    exact hp.coeFn_toLp

def spectralState (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x)
    (f : (positivePullback Ω w hm hw).domain) : (positiveMultiplier (μ := μ) w hm hw).domain :=
  ⟨Ω f,(multiplier_domain_iff w hm hw _).mpr ((pullback_domain_iff Ω w hm hw f).mp f.property)⟩

theorem pullback_coordinates (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x)
    (f : (positivePullback Ω w hm hw).domain) :
    Ω (positivePullback Ω w hm hw f) = positiveMultiplier w hm hw (spectralState Ω w hm hw f) := by
  apply Lp.ext
  exact ((pullback_graph_iff Ω w hm hw f _).mp ((positivePullback Ω w hm hw).mem_graph f)).trans
    (multiplier_coe w hm hw (spectralState Ω w hm hw f)).symm

theorem pullback_domain_integrable_iff (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x) (f : H) :
    f ∈ (positivePullback Ω w hm hw).domain ↔
      Integrable (fun x => (w x)^2*‖(Ω f) x‖^2) μ := by
  rw [pullback_domain_iff,← multiplier_domain_iff w hm hw, multiplier_domain_integrable_iff]

theorem pullback_norm_square (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x)
    (f : (positivePullback Ω w hm hw).domain) :
    ‖positivePullback Ω w hm hw f‖^2 = ∫ x, (w x)^2*‖(Ω f) x‖^2 ∂μ := by
  rw [← Ω.norm_map (positivePullback Ω w hm hw f),pullback_coordinates]
  exact multiplier_norm_square w hm hw (spectralState Ω w hm hw f)

theorem pullback_positive (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x)
    (f : (positivePullback Ω w hm hw).domain) :
    0 ≤ (inner ℂ (positivePullback Ω w hm hw f) (f:H)).re := by
  rw [← Ω.inner_map_map (positivePullback Ω w hm hw f) (f:H),pullback_coordinates]
  exact multiplier_positive w hm hw (spectralState Ω w hm hw f)

theorem pullback_dense [CompleteSpace H] (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x) :
    Dense ((positivePullback Ω w hm hw).domain : Set H) :=
  (pullback_selfAdjoint Ω w hm hw).dense_domain

theorem pullback_closed [CompleteSpace H] (Ω : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x) :
    (positivePullback Ω w hm hw).IsClosed := (pullback_selfAdjoint Ω w hm hw).isClosed

#print axioms coordinate_resolvent
#print axioms conjugate_injective
#print axioms conjugate_symmetric
#print axioms conjugate_dense
#print axioms pullback_selfAdjoint
#print axioms pullback_graph_iff
#print axioms pullback_domain_iff
#print axioms pullback_coordinates
#print axioms pullback_domain_integrable_iff
#print axioms pullback_norm_square
#print axioms pullback_positive
#print axioms pullback_dense
#print axioms pullback_closed

end
end UnifiedTheory.Audit.KFCausalUnitaryPositiveMultiplier
