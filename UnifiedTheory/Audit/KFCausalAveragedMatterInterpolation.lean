/- Charge averaging of the constructed field-weighted interpolation.
The initial expectation and the integrated path cost are separately
integrable. Actual endpoint graphs identify the same finite coherent
representation at every charge angle. No energy estimate is assumed. -/
import UnifiedTheory.Audit.KFCausalCoherentMatterInterpolationOrbit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalAveragedMatterInterpolation
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state action_state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorShearWeight (root rootValue root_coe)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalCoherentMatterInterpolationOrbit

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (l : Transverse →L[ℝ] ℝ) (i : Fin 2) {n : ℕ} (k : Fin n → Joint 2 4) (z : Fin n → ℂ)

local notation "U" => field ε a h hε ha hh hb l i k z
local notation "J" => shear ε a h hε ha hh hb l i k z
local notation "Q" => expectation ε a h hε ha hh hb l i k z
local notation "C" => pathCost ε a h hε ha hh hb l i k z
local notation "f" => ∑ r, z r • state ε a h hε ha hh (k r)

theorem endpoint_average_lower (W : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℂ)
    (hW : ∀ v : Hilbert, W v =ᵐ[volume] fun x => w x.1*v x) :
    (∫ θ, Q W θ 0 ∂angleMeasure)-(h^2/(4*ε))*(∫ θ, C W θ ∂angleMeasure) ≤
      ∫ θ, Q W θ 1 ∂angleMeasure := by
  have h0 := expectation_angle_integrable ε a h hε ha hh hb l i k z W 0
  have h1 := expectation_angle_integrable ε a h hε ha hh hb l i k z W 1
  have hC := pathCost_angle_integrable ε a h hε ha hh hb l i k z W
  have hp (θ : ℝ) : Q W θ 0-(h^2/(4*ε))*C W θ ≤ Q W θ 1 :=
    KFCausalFieldShearInterpolationEstimate.endpoint_comparison ε h hε hb l i
      (fun r => KFCausalImaginaryShearCoherentBridge.coherentSeed a h ha hh (parameter (2*Real.pi*θ) (k r)))
      (fun r => z r*KFCausalClockFloorCoherentUnitary.amplitudeConstant h (parameter (2*Real.pi*θ) (k r)))
      hh W w hW
  have hi := integral_mono (h0.sub (hC.const_mul (h^2/(4*ε)))) h1 hp
  simp only [Pi.sub_apply] at hi
  rwa [integral_sub h0 (hC.const_mul (h^2/(4*ε))),integral_const_mul] at hi

theorem endpoints_actual (g u j : ℝ → Hilbert)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (orderedExponential ε hε h).graph)
    (hu : ∀ θ, (g θ,u θ) ∈ (fieldPower l i).graph)
    (hj : ∀ θ, (u θ,j θ) ∈ (shearMomentum h).graph) :
    ∀ θ, U θ 1 = u θ ∧ J θ 1 = j θ := by
  intro θ
  apply KFCausalCoherentMatterInterpolation.endpoints_actual ε a h hε ha hh hb l i
    (fun r => parameter (2*Real.pi*θ) (k r)) z (g θ) (u θ) (j θ) _ (hu θ) (hj θ)
  simpa only [map_sum,map_smul,action_state] using hg θ

theorem actual_average_lower (W : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℂ)
    (hW : ∀ v : Hilbert, W v =ᵐ[volume] fun x => w x.1*v x)
    (g u j : ℝ → Hilbert)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (orderedExponential ε hε h).graph)
    (hu : ∀ θ, (g θ,u θ) ∈ (fieldPower l i).graph)
    (hj : ∀ θ, (u θ,j θ) ∈ (shearMomentum h).graph) :
    Continuous u ∧ Continuous j ∧
    Integrable (fun θ => (inner ℂ (W (u θ)) (W (j θ))).re) angleMeasure ∧
    (∫ θ, Q W θ 0 ∂angleMeasure)-(h^2/(4*ε))*(∫ θ, C W θ ∂angleMeasure) ≤
      ∫ θ, (inner ℂ (W (u θ)) (W (j θ))).re ∂angleMeasure := by
  have he := endpoints_actual ε a h hε ha hh hb l i k z g u j hg hu hj
  have hc := curves_joint_continuous ε a h hε ha hh hb l i k z
  have hU : Continuous u := (hc.1.comp (continuous_id.prodMk continuous_const)).congr (fun θ => (he θ).1)
  have hJ : Continuous j := (hc.2.1.comp (continuous_id.prodMk continuous_const)).congr (fun θ => (he θ).2)
  have hQ : Continuous (fun θ => (inner ℂ (W (u θ)) (W (j θ))).re) :=
    Complex.continuous_re.comp ((W.continuous.comp hU).inner (W.continuous.comp hJ))
  refine ⟨hU,hJ,(continuous_angle_memLp _ hQ).integrable (by norm_num),?_⟩
  have hav := endpoint_average_lower ε a h hε ha hh hb l i k z W w hW
  have hterm : (∫ θ, Q W θ 1 ∂angleMeasure) =
      ∫ θ, (inner ℂ (W (u θ)) (W (j θ))).re ∂angleMeasure := by
    apply integral_congr_ae
    filter_upwards [] with θ
    unfold expectation
    rw [(he θ).1,(he θ).2]
  exact hav.trans_eq hterm

theorem physical_average_lower (g u j : ℝ → Hilbert)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) f,g θ) ∈ (orderedExponential ε hε h).graph)
    (hu : ∀ θ, (g θ,u θ) ∈ (fieldPower l i).graph)
    (hj : ∀ θ, (u θ,j θ) ∈ (shearMomentum h).graph) :
    let W := root ε hε h hb hh
    (4/ε^2)*(∫ θ, Q W θ 0 ∂angleMeasure)-(h^2/ε^3)*(∫ θ, C W θ ∂angleMeasure) ≤
      (4/ε^2)*(∫ θ, (inner ℂ (W (u θ)) (W (j θ))).re ∂angleMeasure) := by
  dsimp only
  have he := (actual_average_lower ε a h hε ha hh hb l i k z
    (root ε hε h hb hh) (fun s => (rootValue ε h s:ℂ)) (root_coe ε hε h hb hh) g u j hg hu hj).2.2.2
  convert mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 4/ε^2) using 1
  ring

theorem coherent_actual_average (v : Hilbert) (hv : v ∈ coherentSpan ε a h hε ha hh)
    (g u j : ℝ → Hilbert)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) v,g θ) ∈ (orderedExponential ε hε h).graph)
    (hu : ∀ θ, (g θ,u θ) ∈ (fieldPower l i).graph)
    (hj : ∀ θ, (u θ,j θ) ∈ (shearMomentum h).graph) :
    ∃ (m : ℕ) (p : Fin m → Joint 2 4) (c : Fin m → ℂ),
      v = ∑ r, c r • state ε a h hε ha hh (p r) ∧
      Continuous u ∧ Continuous j ∧
      Integrable (fun θ => expectation ε a h hε ha hh hb l i p c (root ε hε h hb hh) θ 0) angleMeasure ∧
      Integrable (pathCost ε a h hε ha hh hb l i p c (root ε hε h hb hh)) angleMeasure ∧
      (4/ε^2)*(∫ θ, expectation ε a h hε ha hh hb l i p c (root ε hε h hb hh) θ 0 ∂angleMeasure)-
        (h^2/ε^3)*(∫ θ, pathCost ε a h hε ha hh hb l i p c (root ε hε h hb hh) θ ∂angleMeasure) ≤
      (4/ε^2)*(∫ θ, (inner ℂ (root ε hε h hb hh (u θ)) (root ε hε h hb hh (j θ))).re ∂angleMeasure) := by
  obtain ⟨m,p,c,he⟩ := KFCausalCoherentSpanVacuumSign.finite_representation ε a h hε ha hh v hv
  have hg' : ∀ θ, (action h hh (2*Real.pi*θ) (∑ r, c r • state ε a h hε ha hh (p r)),g θ) ∈
      (orderedExponential ε hε h).graph := by
    rw [← he]
    exact hg
  have hc := actual_average_lower ε a h hε ha hh hb l i p c (root ε hε h hb hh)
    (fun s => (rootValue ε h s:ℂ)) (root_coe ε hε h hb hh) g u j hg' hu hj
  exact ⟨m,p,c,he,hc.1,hc.2.1,
    expectation_angle_integrable ε a h hε ha hh hb l i p c (root ε hε h hb hh) 0,
    pathCost_angle_integrable ε a h hε ha hh hb l i p c (root ε hε h hb hh),
    physical_average_lower ε a h hε ha hh hb l i p c g u j hg' hu hj⟩

#print axioms endpoint_average_lower
#print axioms endpoints_actual
#print axioms actual_average_lower
#print axioms physical_average_lower
#print axioms coherent_actual_average
end
end UnifiedTheory.Audit.KFCausalAveragedMatterInterpolation
