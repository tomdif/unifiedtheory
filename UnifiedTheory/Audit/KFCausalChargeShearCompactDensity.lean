/- The common shear test family is dense in the physical Hilbert space
and supplies normalized nonzero states with every charge rotation in the
actual shear domain. Density here is Hilbert density, not graph-core or
vacuum-exponential density. -/
import UnifiedTheory.Audit.KFCausalChargeShearCompactDomain
import UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
import Mathlib.Analysis.Normed.Lp.SmoothApprox

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 300000

namespace UnifiedTheory.Audit.KFCausalChargeShearCompactDensity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalChargeShearJointFlow (Space)
open UnifiedTheory.Audit.KFCausalChargeShearCompactDomain
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (JointHilbert)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates action)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)

theorem jointState_dense : DenseRange jointState := by
  apply (Lp.dense_hasCompactSupport_contDiff (E := Space) (F := ℂ) (μ := volume)
    (p := 2) (by norm_num)).mono
  rintro g ⟨f,hf,hc,hs⟩
  let φ : Test := ⟨f,hs.of_le (by norm_num),hc⟩
  exact ⟨φ,Lp.ext ((test_memLp φ).coeFn_toLp.trans hf.symm)⟩

theorem state_dense : DenseRange state :=
  chargeCoordinates.symm.surjective.denseRange.comp jointState_dense chargeCoordinates.symm.continuous

theorem common_domain_dense (h : ℝ) (hh : h ≠ 0) :
    Dense {f : Hilbert | ∀ θ : ℝ, action h hh θ f ∈ (shearMomentum h).domain} := by
  apply state_dense.mono
  rintro f ⟨φ,rfl⟩ θ
  exact LinearPMap.mem_domain_of_mem_graph (orbit_graph h hh θ φ)

theorem exists_nonzero_test : ∃ f : Test, state f ≠ 0 := by
  by_contra hn
  have hz : ∀ f : Test, state f = 0 := by simpa only [not_exists,not_not] using hn
  have he : (fun f : Hilbert => f) = (fun _ => (0:Hilbert)) :=
    state_dense.equalizer continuous_id continuous_const (funext hz)
  exact KFCausalClockFloorInvariantTrial.trialState_ne_zero 1 1 1
    (by norm_num) (by norm_num) (by norm_num)
    (congrFun he (KFCausalClockFloorInvariantTrial.trialState 1 1 1
      (by norm_num) (by norm_num) (by norm_num)))

theorem exists_normalized_common_domain (h : ℝ) (hh : h ≠ 0) :
    ∃ f : Hilbert, ‖f‖ = 1 ∧ ∀ θ : ℝ, action h hh θ f ∈ (shearMomentum h).domain := by
  obtain ⟨φ,hφ⟩ := exists_nonzero_test
  refine ⟨((‖state φ‖⁻¹:ℝ):ℂ) • state φ,?_,?_⟩
  · simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hφ)]
  · intro θ
    rw [map_smul]
    exact (shearMomentum h).domain.smul_mem _
      (LinearPMap.mem_domain_of_mem_graph (orbit_graph h hh θ φ))

#print axioms jointState_dense
#print axioms state_dense
#print axioms common_domain_dense
#print axioms exists_nonzero_test
#print axioms exists_normalized_common_domain
end
end UnifiedTheory.Audit.KFCausalChargeShearCompactDensity
