/- Construction of one all-time weak limit trajectory for the actual
eight-factor regulated Yosida dynamics. Both the smoothed form states and
physical states converge along the same cutoff subsequence. The limit
equation, strong convergence, uniqueness and norm conservation are not
asserted here. -/
import UnifiedTheory.Audit.KFCausalPhysicalFormGeometry
import UnifiedTheory.Audit.KFCausalPhysicalCountableLimit
import UnifiedTheory.Audit.KFCausalPhysicalWeakPairing
import UnifiedTheory.Audit.KFCausalWeakLimitFromTests
import UnifiedTheory.Audit.KFCausalRationalCauchyExtension
import UnifiedTheory.Audit.KFCausalPairingCauchyTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalPhysicalWeakTrajectory
noncomputable section
open Filter TopologicalSpace
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalPhysicalFormTransport
open UnifiedTheory.Audit.KFCausalPhysicalFormGeometry
open UnifiedTheory.Audit.KFCausalPhysicalYosidaDynamics
open UnifiedTheory.Audit.KFCausalPhysicalSmoothedTrajectory
open UnifiedTheory.Audit.KFCausalPhysicalFormWindowBound
open UnifiedTheory.Audit.KFCausalPhysicalWeakPairing
open UnifiedTheory.Audit.KFCausalPhysicalCountableLimit
open UnifiedTheory.Audit.KFCausalHilbertWeakSubsequence
open UnifiedTheory.Audit.KFCausalWeakLimitTransport
open UnifiedTheory.Audit.KFCausalWeakLimitFromTests
open UnifiedTheory.Audit.KFCausalRationalCauchyExtension
open UnifiedTheory.Audit.KFCausalPairingCauchyTransfer

structure WeakTrajectory (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) where
  subsequence : ℕ → ℕ
  strictMono : StrictMono subsequence
  formState : ℝ → FormSpace ε hε hbar hh mass2 quartic vacuum 0
  formBound : ∀ t, ‖formState t‖ ≤ windowRadius ε hε hbar hh mass2 quartic vacuum s |t| w
  formConvergence : ∀ t y, Tendsto (fun n => inner ℂ
    (smoothedLift ε hε hbar hh mass2 quartic vacuum (cutoff (subsequence n)) (cutoff_pos (subsequence n)) s t
      (embedding ε hε hbar hh mass2 quartic vacuum 0 w)) y) atTop (𝓝 (inner ℂ (formState t) y))
  physicalConvergence : ∀ t y, Tendsto (fun n => inner ℂ
    (dynamics ε hε hbar hh mass2 quartic vacuum (cutoff (subsequence n)) (cutoff_pos (subsequence n)) s t
      (embedding ε hε hbar hh mass2 quartic vacuum 0 w)) y) atTop
    (𝓝 (inner ℂ (embedding ε hε hbar hh mass2 quartic vacuum 0 (formState t)) y))

/-- The certificate is constructed from the concrete cutoff trajectories. -/
theorem exists_weak_trajectory (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) : Nonempty (WeakTrajectory ε hε hbar hh mass2 quartic vacuum s w) := by
  obtain ⟨v,_,φ,hφ,_,hphys,_⟩ := exists_countable_limit ε hε hbar hh mass2 quartic vacuum s w
    (fun q : ℚ => (q:ℝ))
  have hc (t : ℝ) (y : FormSpace ε hε hbar hh mass2 quartic vacuum 0) : CauchySeq (fun n => inner ℂ
      (dynamics ε hε hbar hh mass2 quartic vacuum (cutoff (φ n)) (cutoff_pos (φ n)) s t
        (embedding ε hε hbar hh mass2 quartic vacuum 0 w)) (embedding ε hε hbar hh mass2 quartic vacuum 0 y)) := by
    apply rational_cauchy_extension (fun n z => inner ℂ
      (dynamics ε hε hbar hh mass2 quartic vacuum (cutoff (φ n)) (cutoff_pos (φ n)) s z
        (embedding ε hε hbar hh mass2 quartic vacuum 0 w)) (embedding ε hε hbar hh mass2 quartic vacuum 0 y))
    · intro T hT
      refine ⟨pairingBound ε hε hbar hh mass2 quartic vacuum s T w y,pairingBound_nonneg ε hε hbar hh mass2 quartic vacuum s T w y,?_⟩
      intro n x z hx hz
      rw [dist_eq_norm]
      exact weak_pairing_lipschitz ε hε hbar hh mass2 quartic vacuum (cutoff (φ n)) (cutoff_pos (φ n))
        s T z x hT hz hx w y
    · intro q
      exact (hphys q (embedding ε hε hbar hh mass2 quartic vacuum 0 y)).cauchySeq
  have hex (t : ℝ) : ∃ x : FormSpace ε hε hbar hh mass2 quartic vacuum 0,
      ‖x‖ ≤ windowRadius ε hε hbar hh mass2 quartic vacuum s |t| w ∧
      ∀ y, Tendsto (fun n => inner ℂ
        (smoothedLift ε hε hbar hh mass2 quartic vacuum (cutoff (φ n)) (cutoff_pos (φ n)) s t
          (embedding ε hε hbar hh mass2 quartic vacuum 0 w)) y) atTop (𝓝 (inner ℂ x y)) := by
    apply exists_weak_limit_of_test_cauchy (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0) (H := Hilbert)
      (embedding ε hε hbar hh mass2 quartic vacuum 0) (embedding_injective ε hε hbar hh mass2 quartic vacuum 0)
    · intro n
      exact smoothed_window_norm ε hε hbar hh mass2 quartic vacuum (cutoff (φ n)) (cutoff_pos (φ n))
        s |t| t (abs_nonneg _) le_rfl w
    · intro y
      have he := (smoothed_defect_tendsto ε hε hbar hh mass2 quartic vacuum s t w).comp hφ.tendsto_atTop
      exact pairing_cauchy_of_norm_error he (embedding ε hε hbar hh mass2 quartic vacuum 0 y) (hc t y)
  choose x hx hlim using hex
  refine ⟨⟨φ,hφ,x,hx,hlim,?_⟩⟩
  intro t
  have he := (smoothed_defect_tendsto ε hε hbar hh mass2 quartic vacuum s t w).comp hφ.tendsto_atTop
  have hm := weak_map (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0) (H := Hilbert)
    (embedding ε hε hbar hh mass2 quartic vacuum 0)
    (u := fun n => smoothedLift ε hε hbar hh mass2 quartic vacuum (cutoff (φ n)) (cutoff_pos (φ n)) s t
      (embedding ε hε hbar hh mass2 quartic vacuum 0 w)) (x := x t) (hlim t)
  exact weak_limit_of_norm_error (H := Hilbert) he hm

def weakTrajectory (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) : WeakTrajectory ε hε hbar hh mass2 quartic vacuum s w :=
  Classical.choice (exists_weak_trajectory ε hε hbar hh mass2 quartic vacuum s w)

theorem weak_trajectory_norm_bound (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh mass2 quartic vacuum s w) (t : ℝ) :
    ‖embedding ε hε hbar hh mass2 quartic vacuum 0 (V.formState t)‖ ≤ ‖embedding ε hε hbar hh mass2 quartic vacuum 0 w‖ :=
  weak_norm_le
    (fun n => (dynamics_norm ε hε hbar hh mass2 quartic vacuum (cutoff (V.subsequence n))
      (cutoff_pos (V.subsequence n)) s t _).le) (V.physicalConvergence t)

theorem weak_trajectory_initial (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh mass2 quartic vacuum s w) :
    V.formState s = w := by
  apply embedded_tests_separate (embedding ε hε hbar hh mass2 quartic vacuum 0) (embedding_injective ε hε hbar hh mass2 quartic vacuum 0)
  intro y
  have hpair := V.physicalConvergence s (embedding ε hε hbar hh mass2 quartic vacuum 0 y)
  simp only [dynamics_initial,ContinuousLinearMap.one_apply] at hpair
  exact tendsto_nhds_unique hpair tendsto_const_nhds

theorem weak_trajectory_pairing_lipschitz (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) (V : WeakTrajectory ε hε hbar hh mass2 quartic vacuum s w)
    (T x y : ℝ) (hT : 0 ≤ T) (hx : |x| ≤ T) (hy : |y| ≤ T)
    (v : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    ‖inner ℂ (embedding ε hε hbar hh mass2 quartic vacuum 0 (V.formState y)) (embedding ε hε hbar hh mass2 quartic vacuum 0 v)-
      inner ℂ (embedding ε hε hbar hh mass2 quartic vacuum 0 (V.formState x)) (embedding ε hε hbar hh mass2 quartic vacuum 0 v)‖ ≤
      pairingBound ε hε hbar hh mass2 quartic vacuum s T w v * |y-x| := by
  have hl := ((V.physicalConvergence y (embedding ε hε hbar hh mass2 quartic vacuum 0 v)).sub
    (V.physicalConvergence x (embedding ε hε hbar hh mass2 quartic vacuum 0 v))).norm
  exact le_of_tendsto hl (Filter.Eventually.of_forall (fun n => weak_pairing_lipschitz
    ε hε hbar hh mass2 quartic vacuum (cutoff (V.subsequence n)) (cutoff_pos (V.subsequence n)) s T x y hT hx hy w v))

#print axioms exists_weak_trajectory
#print axioms weakTrajectory
#print axioms weak_trajectory_norm_bound
#print axioms weak_trajectory_initial
#print axioms weak_trajectory_pairing_lipschitz

end
end UnifiedTheory.Audit.KFCausalPhysicalWeakTrajectory
