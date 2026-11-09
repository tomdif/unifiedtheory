/- Actual shear graphs for the existing coherent Gaussian energy family,
including every charge rotation. The common energy/shear domain is dense
in Hilbert norm. No graph for the exponential output is asserted here. -/
import UnifiedTheory.Audit.KFCausalCoherentShearDifferential
import UnifiedTheory.Audit.KFCausalClockFloorCoherentFormOrbit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalCoherentShearDomain
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state state_zero action_state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSources (state_configuration_coe)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentUnitary (amplitudeConstant clockFrequency sourceCoefficients)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentDerivative (physicalProfile physicalProfile_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentClockMomentum (sourceProfile_eq)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
  (clockFunction clockFunction_memLp neutralWidth neutralWidth_positive neutralWidth_bound trialState_ne_zero)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalCoherentShearDifferential (profileOutput physicalProfile_graph)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (commonEnergyDomain)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)

theorem state_eq_toLp (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (k : Joint 2 4) :
    state ε a h hε ha hh k =
      (physicalProfile_memLp (amplitudeConstant h k) (clockFrequency k) (groundWidth h) (neutralWidth h)
        (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
        (sourceCoefficients h k) (clockFunction ε a) (clockFunction_memLp ε a hε ha)).toLp
        (physicalProfile (amplitudeConstant h k) (clockFrequency k) (groundWidth h) (neutralWidth h)
          (sourceCoefficients h k) (clockFunction ε a)) := by
  apply Lp.ext
  filter_upwards [state_configuration_coe ε a h hε ha hh k,
    (physicalProfile_memLp (amplitudeConstant h k) (clockFrequency k) (groundWidth h) (neutralWidth h)
      (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
      (sourceCoefficients h k) (clockFunction ε a) (clockFunction_memLp ε a hε ha)).coeFn_toLp] with x hx hy
  rw [hy]
  rw [sourceProfile_eq] at hx
  exact hx

def shearOutput (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (k : Joint 2 4) : Hilbert :=
  profileOutput h (amplitudeConstant h k) (clockFrequency k) (groundWidth h) (neutralWidth h)
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h)
    (sourceCoefficients h k) (clockFunction ε a) (clockFunction_memLp ε a hε ha)

theorem state_shear_graph (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (k : Joint 2 4) :
    (state ε a h hε ha hh k,shearOutput ε a h hε ha hh k) ∈ (shearMomentum h).graph := by
  rw [state_eq_toLp]
  exact physicalProfile_graph h hh _ _ _ _ _ _ _ _ _ _

theorem state_shear_domain (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (k : Joint 2 4) :
    state ε a h hε ha hh k ∈ (shearMomentum h).domain :=
  LinearPMap.mem_domain_of_mem_graph (state_shear_graph ε a h hε ha hh k)

theorem action_state_shear_graph (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (θ : ℝ) (k : Joint 2 4) :
    (action h hh θ (state ε a h hε ha hh k),shearOutput ε a h hε ha hh (parameter θ k)) ∈
      (shearMomentum h).graph := by
  rw [action_state]
  exact state_shear_graph ε a h hε ha hh _

theorem coherentSpan_le_shearDomain (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) :
    coherentSpan ε a h hε ha hh ≤ (shearMomentum h).domain := by
  apply Submodule.span_le.mpr
  rintro f ⟨k,rfl⟩
  exact state_shear_domain ε a h hε ha hh k

theorem all_angle_energy_shear_dense (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hbound : |h| ≤ 2*Real.pi*ε/3) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    Dense {f : Hilbert | ∀ θ : ℝ, action h hh θ f ∈ commonEnergyDomain ε hε h v l ∧
      action h hh θ f ∈ (shearMomentum h).domain} := by
  have hd := Submodule.dense_iff_topologicalClosure_eq_top.mpr (coherentSpan_dense ε a h hε ha hh)
  apply hd.mono
  intro f hf θ
  have hr := action_coherentSpan ε a h hε ha hh θ f hf
  exact ⟨coherentSpan_le_commonEnergyDomain ε a h hε ha hh hbound v l hr,
    coherentSpan_le_shearDomain ε a h hε ha hh hr⟩

theorem exists_normalized_energy_shear (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hbound : |h| ≤ 2*Real.pi*ε/3) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    ∃ f : Hilbert, ‖f‖ = 1 ∧ ∀ θ : ℝ, action h hh θ f ∈ commonEnergyDomain ε hε h v l ∧
      action h hh θ f ∈ (shearMomentum h).domain := by
  let ψ := state ε a h hε ha hh 0
  have hn : ψ ≠ 0 := by
    dsimp only [ψ]
    rw [state_zero]
    exact trialState_ne_zero ε a h hε ha hh
  refine ⟨((‖ψ‖⁻¹:ℝ):ℂ) • ψ,?_,?_⟩
  · simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hn)]
  · intro θ
    rw [map_smul]
    exact ⟨(commonEnergyDomain ε hε h v l).smul_mem _
      (action_state_commonEnergyDomain ε a h hε ha hh hbound θ 0 v l),
      (shearMomentum h).domain.smul_mem _
        (LinearPMap.mem_domain_of_mem_graph (action_state_shear_graph ε a h hε ha hh θ 0))⟩

#print axioms state_eq_toLp
#print axioms state_shear_graph
#print axioms state_shear_domain
#print axioms action_state_shear_graph
#print axioms coherentSpan_le_shearDomain
#print axioms all_angle_energy_shear_dense
#print axioms exists_normalized_energy_shear
end
end UnifiedTheory.Audit.KFCausalCoherentShearDomain
