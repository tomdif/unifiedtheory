/- Actual site-time reflection of the periodic four-dimensional lattice.
Temporal links reverse orientation and are inverted; spatial links retain their
orientation. For even period the fixed vertices lie on the two boundary planes.
No product-half identification or reflection positivity is assumed. -/
import UnifiedTheory.Clay.YangMills.PeriodicLattice4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.PeriodicTimeReflection
noncomputable section
open PeriodicLattice4 RegulatedGauge MeasureTheory

def reflectVertex (N : ℕ) (x : Vertex N) : Vertex N :=
  fun j => if j = 0 then -x j else x j

theorem reflectVertex_involutive (N : ℕ) : Function.Involutive (reflectVertex N) := by
  intro x
  funext j
  by_cases hj : j = 0 <;> simp [reflectVertex, hj]

def vertexEquiv (N : ℕ) : Vertex N ≃ Vertex N :=
  (reflectVertex_involutive N).toPerm

@[simp] theorem reflectVertex_twice (N : ℕ) (x : Vertex N) :
    reflectVertex N (reflectVertex N x) = x := reflectVertex_involutive N x

theorem reflectVertex_step_spatial (N : ℕ) (x : Vertex N) (μ : Fin 4) (hμ : μ ≠ 0) :
    reflectVertex N (step N x μ) = step N (reflectVertex N x) μ := by
  funext j
  by_cases hj : j = 0
  · subst j
    simp [reflectVertex, step, hμ]
  · simp [reflectVertex, step, hj]

theorem reflectVertex_step_time (N : ℕ) (x : Vertex N) :
    step N (reflectVertex N (step N x 0)) 0 = reflectVertex N x := by
  funext j
  by_cases hj : j = 0
  · subst j
    simp [reflectVertex, step]
  · simp [reflectVertex, step, hj]

theorem reflectVertex_fixed_iff (n : ℕ) (x : Vertex (2 * n)) :
    reflectVertex (2 * n) x = x ↔ (x 0).val = 0 ∨ (x 0).val = n := by
  have hfix : reflectVertex (2 * n) x = x ↔ -(x 0) = x 0 := by
    constructor
    · intro he
      simpa [reflectVertex] using congrFun he 0
    · intro he
      funext j
      by_cases hj : j = 0
      · subst j; simpa [reflectVertex] using he
      · simp [reflectVertex, hj]
  rw [hfix, ZMod.neg_eq_self_iff, ← ZMod.val_eq_zero]
  omega

/-- Positive lattice edges are canonically a starting vertex and a direction. -/
def edgeCoordinates (N : ℕ) : Edge (Vertex N) ≃ Vertex N × Fin 4 where
  toFun e := (e.1, e.2.2.val)
  invFun p := ⟨p.1, step N p.1 p.2, forward N p.1 p.2⟩
  left_inv e := by
    rcases e with ⟨x, y, μ, hμ⟩
    cases hμ
    rfl
  right_inv _ := rfl

def reflectIndex (N : ℕ) (p : Vertex N × Fin 4) : Vertex N × Fin 4 :=
  (if p.2 = 0 then reflectVertex N (step N p.1 0) else reflectVertex N p.1, p.2)

theorem reflectIndex_direction (N : ℕ) (p : Vertex N × Fin 4) :
    (reflectIndex N p).2 = p.2 := rfl

theorem reflectIndex_involutive (N : ℕ) : Function.Involutive (reflectIndex N) := by
  rintro ⟨x, μ⟩
  by_cases hμ : μ = 0
  · subst μ
    simp [reflectIndex, reflectVertex_step_time]
  · simp [reflectIndex, hμ]

def indexEquiv (N : ℕ) : (Vertex N × Fin 4) ≃ (Vertex N × Fin 4) :=
  (reflectIndex_involutive N).toPerm

def edgeEquiv (N : ℕ) : Edge (Vertex N) ≃ Edge (Vertex N) :=
  (edgeCoordinates N).trans ((indexEquiv N).trans (edgeCoordinates N).symm)

theorem edgeEquiv_involutive (N : ℕ) : Function.Involutive (edgeEquiv N) := by
  intro e
  change (edgeCoordinates N).symm (reflectIndex N
    ((edgeCoordinates N) ((edgeCoordinates N).symm (reflectIndex N ((edgeCoordinates N) e))))) = e
  rw [Equiv.apply_symm_apply, reflectIndex_involutive, Equiv.symm_apply_apply]

theorem edgeEquiv_direction (N : ℕ) (e : Edge (Vertex N)) :
    ((edgeEquiv N) e).2.2.val = e.2.2.val := rfl

variable (N : ℕ) (G : Type*) [Group G]

def reflectConfiguration (U : Configuration (Vertex N) G) : Configuration (Vertex N) G :=
  fun e => if e.2.2.val = 0 then (U (edgeEquiv N e))⁻¹ else U (edgeEquiv N e)

theorem reflectConfiguration_involutive : Function.Involutive (reflectConfiguration N G) := by
  intro U
  funext e
  by_cases he : e.2.2.val = 0 <;>
    simp [reflectConfiguration, edgeEquiv_direction, he, edgeEquiv_involutive N e]

def linkValue (U : Configuration (Vertex N) G) (x : Vertex N) (μ : Fin 4) : G :=
  link (Vertex N) G U (forward N x μ)

theorem reflect_link_time (U : Configuration (Vertex N) G) (x : Vertex N) :
    linkValue N G (reflectConfiguration N G U) x 0 =
      (linkValue N G U (reflectVertex N (step N x 0)) 0)⁻¹ := rfl

theorem reflect_link_spatial (U : Configuration (Vertex N) G) (x : Vertex N)
    (μ : Fin 4) (hμ : μ ≠ 0) :
    linkValue N G (reflectConfiguration N G U) x μ =
      linkValue N G U (reflectVertex N x) μ := by
  simp [linkValue, link, forward, reflectConfiguration, edgeEquiv, edgeCoordinates,
    indexEquiv, reflectIndex, hμ, Function.Involutive.toPerm]

theorem reflectConfiguration_gauge (g : GaugeTransformation (Vertex N) G)
    (U : Configuration (Vertex N) G) :
    reflectConfiguration N G (gauge (Vertex N) G g U) =
      gauge (Vertex N) G (fun x => g (reflectVertex N x)) (reflectConfiguration N G U) := by
  funext e
  rcases e with ⟨x, y, μ, hμ⟩
  cases hμ
  by_cases hm : μ = 0
  · subst μ
    simp [reflectConfiguration, RegulatedGauge.gauge, edgeEquiv, edgeCoordinates, indexEquiv,
      reflectIndex, Function.Involutive.toPerm, reflectVertex_step_time, mul_assoc]
  · simp [reflectConfiguration, RegulatedGauge.gauge, edgeEquiv, edgeCoordinates, indexEquiv,
      reflectIndex, Function.Involutive.toPerm, hm, reflectVertex_step_spatial N x μ hm]

variable [NeZero N] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem compactHaar_preserves_inv : MeasurePreserving Inv.inv (compactHaar G) (compactHaar G) := by
  have hm : IsProbabilityMeasure (compactHaar G).inv :=
    Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
  have he : (compactHaar G).inv = compactHaar G :=
    ((Measure.haarMeasure_eq_iff (⊤ : TopologicalSpace.PositiveCompacts G)
      (compactHaar G).inv).2 (by simp)).symm
  exact ⟨measurable_inv, he⟩

theorem reference_preserves_edgePermutation :
    MeasurePreserving (fun U : Configuration (Vertex N) G => U ∘ edgeEquiv N)
      (referenceMeasure G (Vertex N)) (referenceMeasure G (Vertex N)) := by
  have h := measurePreserving_piCongrLeft
    (fun _ : Edge (Vertex N) => compactHaar G) (edgeEquiv N).symm
  convert h using 1
  funext U e
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

theorem reference_preserves_orientationInv :
    MeasurePreserving (fun U : Configuration (Vertex N) G =>
      fun e => if e.2.2.val = 0 then (U e)⁻¹ else U e)
      (referenceMeasure G (Vertex N)) (referenceMeasure G (Vertex N)) := by
  refine measurePreserving_pi (fun _ : Edge (Vertex N) => compactHaar G)
    (fun _ : Edge (Vertex N) => compactHaar G)
    (f := fun e u => if e.2.2.val = 0 then u⁻¹ else u) ?_
  intro e
  by_cases he : e.2.2.val = 0
  · simpa only [he, if_true] using compactHaar_preserves_inv G
  · simpa only [he, if_false] using MeasurePreserving.id (compactHaar G)

/-- Actual reflected forward-link configurations preserve the product Haar law. -/
theorem reference_preserves_reflection :
    MeasurePreserving (reflectConfiguration N G)
      (referenceMeasure G (Vertex N)) (referenceMeasure G (Vertex N)) :=
  (reference_preserves_orientationInv N G).comp (reference_preserves_edgePermutation N G)

end
end UnifiedTheory.Clay.YangMills.PeriodicTimeReflection
