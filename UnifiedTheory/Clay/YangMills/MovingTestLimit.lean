/- Uniform seminorm estimates permit moving Schwartz tests in a weak limit.
This is needed when the lattice reflection plane moves with the spacing. -/
import UnifiedTheory.Clay.YangMills.HierarchyCompactness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.MovingTestLimit
noncomputable section
open Filter ContinuumControl
open scoped Topology

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E]

theorem moving_limit (F : ℕ → E →L[ℂ] ℂ) (p : Seminorm ℂ E) (hp : Continuous p)
    (hb : ∀ k x, ‖F k x‖ ≤ p x) (x : E) (z : ℂ)
    (hc : Tendsto (fun k => F k x) atTop (𝓝 z))
    (test : ℕ → E) (ht : Tendsto test atTop (𝓝 x)) :
    Tendsto (fun k => F k (test k)) atTop (𝓝 z) := by
  have hdiff : Tendsto (fun k => test k - x) atTop (𝓝 0) := by
    simpa only [sub_self] using ht.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))
  have hpzero : Tendsto (fun k => p (test k - x)) atTop (𝓝 0) := by
    simpa only [map_zero] using (hp.tendsto 0).comp hdiff
  have hsmall : Tendsto (fun k => F k (test k - x)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun k => hb k (test k - x)) hpzero
  have h := hsmall.add hc
  simpa only [map_sub, sub_add_cancel, zero_add] using h

theorem hierarchy_moving_limit (S : ℕ → Hierarchy) (W : Hierarchy)
    (hc : WeakConvergence S W) (p : (m : ℕ) → Seminorm ℂ (CorrelationTest m))
    (hp : ∀ m, Continuous (p m)) (hb : ∀ k m f, ‖(S k).correlation m f‖ ≤ p m f)
    (m : ℕ) (f : CorrelationTest m) (test : ℕ → CorrelationTest m)
    (ht : Tendsto test atTop (𝓝 f)) :
    Tendsto (fun k => (S k).correlation m (test k)) atTop (𝓝 (W.correlation m f)) :=
  moving_limit (fun k => (S k).correlation m) (p m) (hp m) (fun k f => hb k m f)
    f (W.correlation m f) (hc m f) test ht

/-- The fixed reflected limiting form inherits positivity when finite-cutoff
forms are evaluations on converging reflected/tensor tests. -/
theorem reflected_positive_limit (F : ℕ → E →L[ℂ] ℂ) (p : Seminorm ℂ E)
    (hp : Continuous p) (hb : ∀ k x, ‖F k x‖ ≤ p x) (x : E) (z : ℂ)
    (hc : Tendsto (fun k => F k x) atTop (𝓝 z))
    (test : ℕ → E) (ht : Tendsto test atTop (𝓝 x))
    (hpos : ∀ᶠ k in atTop, 0 ≤ (F k (test k)).re ∧ (F k (test k)).im = 0) :
    0 ≤ z.re ∧ z.im = 0 := by
  have h := moving_limit F p hp hb x z hc test ht
  constructor
  · exact ge_of_tendsto (Complex.continuous_re.tendsto z |>.comp h)
      (hpos.mono (fun _ h => h.1))
  · exact tendsto_nhds_unique (Complex.continuous_im.tendsto z |>.comp h)
      (tendsto_const_nhds.congr' (hpos.mono (fun _ h => h.2.symm)))

end
end UnifiedTheory.Clay.YangMills.MovingTestLimit
