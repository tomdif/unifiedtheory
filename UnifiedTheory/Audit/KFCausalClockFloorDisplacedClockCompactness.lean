/- Finite-window compactness of the actual quantum clock expectations.
Every admissible small-hbar sequence has a uniformly convergent clock
subsequence with values in [0,1] and the proved Lipschitz bound. This is
compactness of one observable, not a phase-space measure or transport law. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockIntegral
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Sequences

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockCompactness
noncomputable section
open Filter
open scoped Topology BoundedContinuousFunction
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRates
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockWindow

def boundedPaths {X : Type*} [PseudoMetricSpace X] (L : ℝ) : Set (X →ᵇ ℝ) :=
  {f | (∀ x, f x ∈ Set.Icc (0:ℝ) 1) ∧ ∀ x y, dist (f x) (f y) ≤ L*dist x y}

theorem boundedPaths_compact {X : Type*} [PseudoMetricSpace X] [CompactSpace X] (L : ℝ) :
    IsCompact (boundedPaths (X := X) L) := by
  have hc : IsClosed (boundedPaths (X := X) L) := by
    unfold boundedPaths
    simp only [Set.setOf_and,Set.setOf_forall]
    exact (isClosed_iInter (fun x => isClosed_Icc.preimage (BoundedContinuousFunction.lipschitz_eval_const x).continuous)).inter
      (isClosed_iInter (fun x => isClosed_iInter (fun y => isClosed_le
        ((BoundedContinuousFunction.lipschitz_eval_const x).continuous.dist
          (BoundedContinuousFunction.lipschitz_eval_const y).continuous) continuous_const)))
  apply BoundedContinuousFunction.arzela_ascoli₂ (Set.Icc (0:ℝ) 1) isCompact_Icc _ hc
    (fun f x hf => hf.1 x)
  exact Metric.equicontinuous_of_continuity_modulus (fun d : ℝ => L*d)
    (by simpa only [Pi.mul_apply,id_eq,mul_zero] using ((continuous_const (y := L)).mul continuous_id).tendsto (0:ℝ))
    _ (fun x y f => f.property.2 x y)

abbrev Window (s T : ℝ) := Set.Icc (s-T) (s+T)

def windowPath (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s T : ℝ) (p : Configuration) : Window s T →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun t => clockExpectation ε a h hε ha hh hb m g κ s p t,
      (clockExpectation_continuous ε a h hε ha hh hb m g κ s p).comp continuous_subtype_val⟩

theorem windowPath_bounds (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (m g κ s T : ℝ) (p : Configuration) (t : Window s T) :
    windowPath ε a h hε ha hh hb m g κ s T p t ∈ Set.Icc (0:ℝ) 1 :=
  clockExpectation_bounds ε a h hε ha hh hb m g κ s p t

theorem clock_paths_subsequence (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g κ s T : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) :
    ∃ f : Window s T →ᵇ ℝ, (∀ t, f t ∈ Set.Icc (0:ℝ) 1) ∧
      (∀ r t, dist (f r) (f t) ≤ speedConstant ε a m g κ s T p*dist r t) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ TendstoUniformly
        (fun n => windowPath ε a (h (φ n)) hε ha (hh (φ n)) (hb (φ n)) m g κ s T p) f atTop := by
  let F : ℕ → Window s T →ᵇ ℝ := fun n => windowPath ε a (h n) hε ha (hh n) (hb n) m g κ s T p
  have he : ∀ᶠ n in atTop, F n ∈ boundedPaths (speedConstant ε a m g κ s T p) := by
    filter_upwards [clockExpectation_window_lipschitz ε a hε ha m g κ s p hm hg hκ h hh hb hz T] with n hn
    refine ⟨windowPath_bounds ε a (h n) hε ha (hh n) (hb n) m g κ s T p,?_⟩
    intro r t
    have hw (u : Window s T) : |(u:ℝ)-s| ≤ T :=
      abs_le.mpr ⟨by linarith [u.property.1],by linarith [u.property.2]⟩
    simpa only [F,windowPath,BoundedContinuousFunction.mkOfCompact_apply,ContinuousMap.coe_mk,
      Subtype.dist_eq,Real.dist_eq] using hn t r (hw t) (hw r)
  obtain ⟨f,hf,φ,hφ,hlim⟩ := (boundedPaths_compact (X := Window s T) (speedConstant ε a m g κ s T p)).tendsto_subseq' he.frequently
  exact ⟨f,hf.1,hf.2,φ,hφ,BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim⟩

#print axioms boundedPaths_compact
#print axioms windowPath_bounds
#print axioms clock_paths_subsequence

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockCompactness
