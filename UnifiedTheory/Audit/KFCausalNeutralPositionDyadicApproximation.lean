/- Finite dyadic expectations approximate the actual bare position
characteristic uniformly on evolved states. The largest dyadic width
controls the approximation, independently of the number of scales. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionDyadicWindow
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialCharacteristic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralPositionDyadicApproximation
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalFiniteMultiplierAverage
open UnifiedTheory.Audit.KFCausalDyadicHeatCancellation (width width_pos)
open UnifiedTheory.Audit.KFCausalDyadicResponseChoice (width_mono)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState (referenceState)
open UnifiedTheory.Audit.KFCausalNeutralPositionDyadicEhrenfest (characteristic)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCharacteristic

theorem mean_reference (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hne : h ≠ 0)
    (hh : |h| ≤ 2*Real.pi*ε/3) (m g k s : ℝ) (p : Configuration)
    (δ v : ℝ) (N : ℕ) (hδ : 0 < δ) (t : ℝ) :
    characteristic ε hε h δ v N hδ hh hne m g k s t
      (referenceState ε a h hε ha hne hh m g k s p) =
    mean N (fun j => radial ε a h hε ha hne hh m g k s p (width δ j) (width_pos δ hδ j) v t) :=
  congrArg (mean N) (funext (fun j =>
    (radial_reference ε a h hε ha hne hh m g k s p (width δ j) (width_pos δ hδ j) v t).symm))

theorem uniform_mean_approximation (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (m g k s : ℝ) (p : Configuration) (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
    (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T η : ℝ) (hη : 0 < η) :
    ∃ D : ℝ, 0 < D ∧ ∃ M : ℕ, ∀ n ≥ M, ∀ N : ℕ, 0 < N →
      ∀ δ : ℝ, ∀ hδ : 0 < δ, width δ N < D → ∀ v t : ℝ, |t-s| ≤ T →
      ‖characteristic ε hε (h n) δ v N hδ (hh n) (hne n) m g k s t
          (referenceState ε a (h n) hε ha (hne n) (hh n) m g k s p)-
        bare ε a (h n) hε ha (hne n) (hh n) m g k s p v t‖ < η := by
  obtain ⟨D,hD,M,hM⟩ := uniform_approximation ε a hε ha m g k s p hm hg hk h hne hh hz
    T (η/2) (by positivity)
  refine ⟨D,hD,M,?_⟩
  intro n hn N hN δ hδ hd v t ht
  let f := fun j => radial ε a (h n) hε ha (hne n) (hh n) m g k s p (width δ j) (width_pos δ hδ j) v t
  let b := bare ε a (h n) hε ha (hne n) (hh n) m g k s p v t
  have hs : ‖mean N (fun j => f j-b)‖ ≤ η/2 := by
    apply mean_norm_le N hN
    intro j hj
    exact (hM n hn (width δ j) (width_pos δ hδ j)
      ((width_mono δ hδ.le j N (Nat.le_of_lt (Finset.mem_range.mp hj))).trans_lt hd) v t ht).le
  have he : mean N (fun j => f j-b) = mean N f-b :=
    (mean_sub N f (fun _ => b)).trans (congrArg (fun z => mean N f-z) (mean_const N hN b))
  have href := mean_reference ε a (h n) hε ha (hne n) (hh n) m g k s p δ v N hδ t
  exact ((congrArg norm ((congrArg (fun z => z-b) href).trans he.symm)).le.trans hs).trans_lt (by linarith)

#print axioms mean_reference
#print axioms uniform_mean_approximation

end
end UnifiedTheory.Audit.KFCausalNeutralPositionDyadicApproximation
