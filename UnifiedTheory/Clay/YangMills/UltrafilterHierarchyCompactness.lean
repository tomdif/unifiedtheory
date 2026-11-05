/- Common all-order weak extraction from continuous seminorm bounds without
a dense test family. The convergence is along one ultrafilter refining atTop,
not a claimed sequential subsequence. The regulator-uniform renormalized
seminorm bounds themselves remain analytic inputs. -/
import UnifiedTheory.Clay.YangMills.HierarchyCompactness
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Filter.Ultrafilter.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.UltrafilterHierarchyCompactness
noncomputable section
open Filter ContinuumControl
open scoped Topology

def regulatorUltrafilter : Ultrafilter ℕ := Ultrafilter.of atTop

theorem regulatorUltrafilter_le : (regulatorUltrafilter : Filter ℕ) ≤ atTop :=
  Ultrafilter.of_le atTop

theorem bounded_scalar_limit (U : Ultrafilter ℕ) (c : ℕ → ℂ) (B : ℝ)
    (hb : ∀ k, ‖c k‖ ≤ B) :
    ∃ z : ℂ, Tendsto c (U : Filter ℕ) (𝓝 z) ∧ ‖z‖ ≤ B := by
  have hball : (Ultrafilter.map c U : Filter ℂ) ≤ 𝓟 (Metric.closedBall 0 B) := by
    rw [Ultrafilter.coe_map, le_principal_iff]
    change ∀ᶠ k in (U : Filter ℕ), c k ∈ Metric.closedBall 0 B
    exact Eventually.of_forall (fun k => by simpa using hb k)
  obtain ⟨z, hz, hc⟩ := (isCompact_closedBall (0 : ℂ) B).ultrafilter_le_nhds
    (Ultrafilter.map c U) hball
  exact ⟨z, hc, by simpa using hz⟩

section Linear
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module ℂ E] [ContinuousSMul ℂ E]

theorem exists_linear_limit (U : Ultrafilter ℕ) (F : ℕ → E →L[ℂ] ℂ)
    (p : Seminorm ℂ E) (hp : Continuous p) (hb : ∀ k x, ‖F k x‖ ≤ p x) :
    ∃ W : E →L[ℂ] ℂ, (∀ x, Tendsto (fun k => F k x) (U : Filter ℕ) (𝓝 (W x))) ∧
      ∀ x, ‖W x‖ ≤ p x := by
  have he (x : E) := bounded_scalar_limit U (fun k => F k x) (p x) (fun k => hb k x)
  choose z hz hzb using he
  let L : E →ₗ[ℂ] ℂ :=
    { toFun := z
      map_add' := by
        intro x y
        exact tendsto_nhds_unique (by simpa only [map_add] using hz (x + y))
          ((hz x).add (hz y))
      map_smul' := by
        intro a x
        exact tendsto_nhds_unique (by simpa only [map_smul] using hz (a • x))
          (tendsto_const_nhds.smul (hz x)) }
  exact ⟨⟨L, SeminormWeakCompactness.continuous_of_seminorm_bound L p hp hzb⟩, hz, hzb⟩

theorem moving_test_limit (l : Filter ℕ) (F : ℕ → E →L[ℂ] ℂ)
    (p : Seminorm ℂ E) (hp : Continuous p) (hb : ∀ k x, ‖F k x‖ ≤ p x)
    (x : E) (xk : ℕ → E) (hxk : Tendsto xk l (𝓝 x)) (z : ℂ)
    (hx : Tendsto (fun k => F k x) l (𝓝 z)) :
    Tendsto (fun k => F k (xk k)) l (𝓝 z) := by
  have he : Tendsto (fun k => F k (xk k) - F k x) l (𝓝 0) := by
    apply squeeze_zero_norm (a := fun k => p (xk k - x))
    · intro k
      rw [← map_sub]
      exact hb k _
    · have hd : Tendsto (fun k => xk k - x) l (𝓝 (x - x)) :=
        hxk.sub tendsto_const_nhds
      simpa using (hp.tendsto (x - x)).comp hd
  simpa only [sub_add_cancel, zero_add] using he.add hx
end Linear

def WeakAlong (l : Filter ℕ) (S : ℕ → Hierarchy) (W : Hierarchy) : Prop :=
  ∀ n f, Tendsto (fun k => (S k).correlation n f) l (𝓝 (W.correlation n f))

/-- All orders and all Schwartz tests converge along the same ultrafilter;
no separability premise, replacement observable, or independently chosen
coordinate subsequence is used. -/
theorem exists_hierarchy_limit (U : Ultrafilter ℕ) (S : ℕ → Hierarchy)
    (p : ∀ n, Seminorm ℂ (CorrelationTest n)) (hp : ∀ n, Continuous (p n))
    (hb : HierarchyCompactness.UniformSeminormBound S p) :
    ∃ W : Hierarchy, WeakAlong (U : Filter ℕ) S W ∧
      ∀ n f, ‖W.correlation n f‖ ≤ p n f := by
  have he (n : ℕ) := exists_linear_limit U (fun k => (S k).correlation n)
    (p n) (hp n) (fun k f => hb k n f)
  choose W hW hbound using he
  exact ⟨⟨W⟩, hW, hbound⟩

theorem exists_regulator_limit (S : ℕ → Hierarchy)
    (p : ∀ n, Seminorm ℂ (CorrelationTest n)) (hp : ∀ n, Continuous (p n))
    (hb : HierarchyCompactness.UniformSeminormBound S p) :
    ∃ W : Hierarchy, WeakAlong (regulatorUltrafilter : Filter ℕ) S W ∧
      ∀ n f, ‖W.correlation n f‖ ≤ p n f :=
  exists_hierarchy_limit regulatorUltrafilter S p hp hb

theorem atTop_tendsto {X : Type*} [TopologicalSpace X] (f : ℕ → X) (x : X)
    (h : Tendsto f atTop (𝓝 x)) :
    Tendsto f (regulatorUltrafilter : Filter ℕ) (𝓝 x) :=
  h.mono_left regulatorUltrafilter_le

theorem atTop_eventually (P : ℕ → Prop) (h : ∀ᶠ k in atTop, P k) :
    ∀ᶠ k in (regulatorUltrafilter : Filter ℕ), P k :=
  regulatorUltrafilter_le h

end
end UnifiedTheory.Clay.YangMills.UltrafilterHierarchyCompactness
