/- Weak subsequential compactness in a separable complex Hilbert space,
obtained from sequential Banach-Alaoglu and the Riesz representation.
Small norm errors preserve the resulting weak limit. -/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalHilbertWeakSubsequence
noncomputable section
open Filter TopologicalSpace
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def weakRiesz (x : H) : WeakDual ℂ H := StrongDual.toWeakDual (InnerProductSpace.toDual ℂ H x)

theorem weakRiesz_apply (x y : H) : weakRiesz x y = inner ℂ x y := rfl

theorem bounded_weak_subsequence [SeparableSpace H] (u : ℕ → H) (C : ℝ)
    (hb : ∀ n, ‖u n‖ ≤ C) :
    ∃ x : H, ‖x‖ ≤ C ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ y : H, Tendsto (fun n => inner ℂ (u (φ n)) y) atTop (𝓝 (inner ℂ x y)) := by
  have hm : ∀ n, weakRiesz (u n) ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ H) C := by
    intro n
    change dist (InnerProductSpace.toDual ℂ H (u n)) 0 ≤ C
    simpa only [dist_zero_right,LinearIsometryEquiv.norm_map] using hb n
  obtain ⟨v,hv,φ,hφ,hlim⟩ := (WeakDual.isSeqCompact_closedBall ℂ H (0 : StrongDual ℂ H) C) hm
  let x : H := (InnerProductSpace.toDual ℂ H).symm (WeakDual.toStrongDual v)
  refine ⟨x,?_,φ,hφ,?_⟩
  · change dist (WeakDual.toStrongDual v) 0 ≤ C at hv
    simpa only [x,LinearIsometryEquiv.norm_map,dist_zero_right] using hv
  · intro y
    have he := ((WeakDual.eval_continuous y).tendsto v).comp hlim
    have hx : inner ℂ x y = v y := by
      change (InnerProductSpace.toDual ℂ H x) y = v y
      dsimp only [x]
      rw [LinearIsometryEquiv.apply_symm_apply]
      rfl
    simpa only [Function.comp_apply,weakRiesz_apply,hx] using he

omit [CompleteSpace H] in
theorem weak_limit_of_norm_error {u v : ℕ → H} {x : H}
    (he : Tendsto (fun n => ‖u n-v n‖) atTop (𝓝 0))
    (hv : ∀ y, Tendsto (fun n => inner ℂ (v n) y) atTop (𝓝 (inner ℂ x y))) :
    ∀ y, Tendsto (fun n => inner ℂ (u n) y) atTop (𝓝 (inner ℂ x y)) := by
  have hd : Tendsto (fun n => u n-v n) atTop (𝓝 (0:H)) := tendsto_zero_iff_norm_tendsto_zero.mpr he
  intro y
  have hi := (hd.inner (𝕜 := ℂ) (tendsto_const_nhds (x := y))).add (hv y)
  simpa only [inner_zero_left,zero_add,inner_sub_left,sub_add_cancel] using hi

/-- A single subsequence works for every member of a countable family.
The bounds may depend on the family index. -/
theorem countable_weak_subsequence [SeparableSpace H] {I : Type*} [Countable I]
    (u : ℕ → I → H) (C : I → ℝ) (hb : ∀ n i, ‖u n i‖ ≤ C i) :
    ∃ x : I → H, (∀ i, ‖x i‖ ≤ C i) ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i y, Tendsto (fun n => inner ℂ (u (φ n) i) y) atTop (𝓝 (inner ℂ (x i) y)) := by
  let K (i : I) : Set (WeakDual ℂ H) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ H) (C i)
  have hK (i : I) : IsCompact (K i) := WeakDual.isCompact_closedBall ℂ _ _
  letI (i : I) : CompactSpace (K i) := isCompact_iff_compactSpace.mp (hK i)
  letI (i : I) : MetrizableSpace (K i) := WeakDual.metrizable_of_isCompact ℂ H (K i) (hK i)
  have hm (n : ℕ) (i : I) : weakRiesz (u n i) ∈ K i := by
    change dist (InnerProductSpace.toDual ℂ H (u n i)) 0 ≤ C i
    simpa only [dist_zero_right,LinearIsometryEquiv.norm_map] using hb n i
  let z : ℕ → ∀ i, K i := fun n i => ⟨weakRiesz (u n i),hm n i⟩
  obtain ⟨v,φ,hφ,hlim⟩ := CompactSpace.tendsto_subseq z
  let x : I → H := fun i => (InnerProductSpace.toDual ℂ H).symm (WeakDual.toStrongDual (v i).val)
  refine ⟨x,?_,φ,hφ,?_⟩
  · intro i
    have hi := (v i).property
    change dist (WeakDual.toStrongDual (v i).val) 0 ≤ C i at hi
    simpa only [x,LinearIsometryEquiv.norm_map,dist_zero_right] using hi
  · intro i y
    have hc : Continuous (fun v : ∀ i, K i => (v i).val y) :=
      (WeakDual.eval_continuous y).comp (continuous_subtype_val.comp (continuous_apply i))
    have he := (hc.tendsto v).comp hlim
    have hx : inner ℂ (x i) y = (v i).val y := by
      change (InnerProductSpace.toDual ℂ H (x i)) y = (v i).val y
      dsimp only [x]
      rw [LinearIsometryEquiv.apply_symm_apply]
      rfl
    simpa only [Function.comp_apply,z,weakRiesz_apply,hx] using he

#print axioms bounded_weak_subsequence
#print axioms weak_limit_of_norm_error
#print axioms countable_weak_subsequence

end
end UnifiedTheory.Audit.KFCausalHilbertWeakSubsequence
