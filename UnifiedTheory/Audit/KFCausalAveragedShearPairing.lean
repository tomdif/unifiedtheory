/- The signed shear pairing is genuinely integrable on the constructed
continuous orbit domain, including finite coherent superpositions. Its
integrated response identity retains a shear-moment requirement; no bound
by the physical Hamiltonian energy is asserted. -/
import UnifiedTheory.Audit.KFCausalContinuousShearOrbitDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000

namespace UnifiedTheory.Audit.KFCausalAveragedShearPairing
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorShearWeight (root)
open UnifiedTheory.Audit.KFCausalClockFloorSignedShearResponse (root_shear_graph response_weighted_shear)
open UnifiedTheory.Audit.KFCausalContinuousShearOrbitDomain

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hbound : |h| ≤ 2*Real.pi*ε/3)
local notation "W" => root ε hε h hbound hh
local notation "J" => shearMomentum h
local notation "T" => orderedExponential ε hε h
local notation "responseL" => KFCausalClockFloorVacuumMomentumResponse.response ε hε h hbound
local notation "response" => KFCausalClockFloorPureClockVacuumResponse.response ε hε h hbound

def pairing (g j : ℝ → Hilbert) (θ : ℝ) : ℝ := (inner ℂ (W (g θ)) (W (j θ))).re
def meanShear (g j : ℝ → Hilbert) : ℝ := ∫ θ, pairing ε h hε hh hbound g j θ ∂angleMeasure

theorem pairing_continuous (g j : ℝ → Hilbert) (hg : Continuous g) (hj : Continuous j) :
    Continuous (pairing ε h hε hh hbound g j) :=
  Complex.continuous_re.comp (((W).continuous.comp hg).inner ((W).continuous.comp hj))

theorem pairing_integrable (g j : ℝ → Hilbert) (hg : Continuous g) (hj : Continuous j) :
    Integrable (pairing ε h hε hh hbound g j) angleMeasure :=
  (continuous_angle_memLp _ (pairing_continuous ε h hε hh hbound g j hg hj)).integrable (by norm_num)

theorem weighted_square_integrable (g : ℝ → Hilbert) (hg : Continuous g) :
    Integrable (fun θ => ‖W (g θ)‖^2) angleMeasure :=
  (continuous_angle_memLp _ (((W).continuous.comp hg).norm.pow 2)).integrable (by norm_num)

theorem meanShear_bound (g j : ℝ → Hilbert) (hg : Continuous g) (hj : Continuous j) :
    |meanShear ε h hε hh hbound g j| ≤
      (1/2)*((∫ θ, ‖W (g θ)‖^2 ∂angleMeasure)+(∫ θ, ‖W (j θ)‖^2 ∂angleMeasure)) := by
  have hg2 := weighted_square_integrable ε h hε hh hbound g hg
  have hj2 := weighted_square_integrable ε h hε hh hbound j hj
  have hp := pairing_integrable ε h hε hh hbound g j hg hj
  have hb (θ : ℝ) : ‖pairing ε h hε hh hbound g j θ‖ ≤
      (1/2)*(‖W (g θ)‖^2+‖W (j θ)‖^2) := by
    have hi := (Complex.abs_re_le_norm (inner ℂ (W (g θ)) (W (j θ)))).trans
      (norm_inner_le_norm (𝕜 := ℂ) _ _)
    change |(inner ℂ (W (g θ)) (W (j θ))).re| ≤ _
    nlinarith [sq_nonneg (‖W (g θ)‖-‖W (j θ)‖)]
  calc
    _ ≤ ∫ θ, ‖pairing ε h hε hh hbound g j θ‖ ∂angleMeasure := by
      simpa only [meanShear,Real.norm_eq_abs] using
        norm_integral_le_integral_norm (f := pairing ε h hε hh hbound g j)
    _ ≤ ∫ θ, (1/2)*(‖W (g θ)‖^2+‖W (j θ)‖^2) ∂angleMeasure :=
      integral_mono hp.norm ((hg2.add hj2).const_mul (1/2)) hb
    _ = _ := by rw [integral_const_mul,integral_add hg2 hj2]

include hh in
theorem response_integrable (g j : ℝ → Hilbert) (hg : Continuous g) (hj : Continuous j)
    (hgraph : ∀ θ, (g θ,j θ) ∈ (J).graph) :
    Integrable (fun θ => response (g θ) (j θ)) angleMeasure := by
  have he : (fun θ => response (g θ) (j θ)) =
      fun θ => responseL (g θ)+(4/ε^2)*pairing ε h hε hh hbound g j θ :=
    funext (fun θ => response_weighted_shear ε hε h hbound hh (g θ) (j θ) (hgraph θ))
  rw [he]
  exact ((continuous_angle_memLp _
    ((KFCausalClockFloorVacuumMomentumResponse.response_continuous ε hε h hbound).comp hg)).integrable
      (by norm_num)).add ((pairing_integrable ε h hε hh hbound g j hg hj).const_mul _)

theorem response_integral_split (g j : ℝ → Hilbert) (hg : Continuous g) (hj : Continuous j)
    (hgraph : ∀ θ, (g θ,j θ) ∈ (J).graph) :
    (∫ θ, response (g θ) (j θ) ∂angleMeasure) =
      (∫ θ, responseL (g θ) ∂angleMeasure)+(4/ε^2)*meanShear ε h hε hh hbound g j := by
  simp_rw [response_weighted_shear ε hε h hbound hh _ _ (hgraph _)]
  rw [integral_add]
  · rw [integral_const_mul]
    rfl
  · exact (continuous_angle_memLp _
      ((KFCausalClockFloorVacuumMomentumResponse.response_continuous ε hε h hbound).comp hg)).integrable
        (by norm_num)
  · exact (pairing_integrable ε h hε hh hbound g j hg hj).const_mul _

theorem meanShear_unique (f : Hilbert) (g j u v : ℝ → Hilbert)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (T).graph ∧ (g θ,j θ) ∈ (J).graph)
    (hu : ∀ θ, (action h hh (2*Real.pi*θ) f,u θ) ∈ (T).graph ∧ (u θ,v θ) ∈ (J).graph) :
    meanShear ε h hε hh hbound g j = meanShear ε h hε hh hbound u v := by
  obtain ⟨rfl,rfl⟩ := orbit_outputs_unique ε h hε hh f g j u v hg hu
  rfl

theorem orbitDomain_force (f : Hilbert) (hf : f ∈ orbitDomain ε h hε hh) :
    ∃ g j : ℝ → Hilbert, Continuous g ∧ Continuous j ∧
      (∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (T).graph ∧
        (g θ,j θ) ∈ (J).graph ∧ (W (g θ),W (j θ)) ∈ (J).graph) ∧
      Integrable (pairing ε h hε hh hbound g j) angleMeasure ∧
      Integrable (fun θ => response (g θ) (j θ)) angleMeasure := by
  obtain ⟨g,j,hg,hj,hgraph⟩ := hf
  exact ⟨g,j,hg,hj,fun θ => ⟨(hgraph θ).1,(hgraph θ).2,
    root_shear_graph ε hε h hbound hh (g θ) (j θ) (hgraph θ).2⟩,
    pairing_integrable ε h hε hh hbound g j hg hj,
    response_integrable ε h hε hh hbound g j hg hj (fun θ => (hgraph θ).2)⟩

#print axioms pairing_continuous
#print axioms pairing_integrable
#print axioms weighted_square_integrable
#print axioms meanShear_bound
#print axioms response_integrable
#print axioms response_integral_split
#print axioms meanShear_unique
#print axioms orbitDomain_force
end
end UnifiedTheory.Audit.KFCausalAveragedShearPairing
