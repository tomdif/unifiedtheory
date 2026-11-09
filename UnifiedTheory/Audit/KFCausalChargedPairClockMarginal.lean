/- Actual paired-state energy and response reduce to a single clock
integral with the exact positive transverse potential kernel. Fubini and
absolute integrability follow from the already constructed L2 outputs. -/
import UnifiedTheory.Audit.KFCausalChargedPairPotentialResponse
import UnifiedTheory.Audit.KFCausalChargedPairPotentialKernel
import UnifiedTheory.Audit.KFCausalPositiveKernelClockResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalChargedPairClockMarginal
noncomputable section
open MeasureTheory
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalChargedPairOrderedOutputs (pairedShifted pairedShifted_memLp output_coe)
open KFCausalChargedPairPotentialKernel (kernel physicalDensity)
open KFCausalPositiveKernelClockResponse (clockWeight energy weakResponse)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalClockFloorInvariantTrial (neutralWidth)
open KFCausalChargedPairPotentialResponse (potentialDensity responseDensity potentialDensity_integrable)
open KFCausalChargedPairFactorResponse (factorEnergy)
open KFCausalChargedPairHamiltonianResponse (potentialEnergy potentialResponse)
open KFCausalSourcedResponseFactorBridge (index)

def energyDensity (ε a h : ℝ) (x : Configuration) : ℝ :=
  ‖pairedShifted ε a h pointField 0 x‖^2+
    ‖pairedShifted ε a h pointField 1 x‖^2/2+
      ‖pairedShifted ε a h pointField 2 x‖^2/4

def physicalKernel (ε h s : ℝ) : ℝ :=
  kernel (groundWidth h) (neutralWidth h) (scale ε (-h/2) s)

theorem energy_density_factorization (ε a h : ℝ) (x : Configuration) :
    energyDensity ε a h x =
      clockWeight ε a 0 (-h/2) x.1 *
        physicalDensity (groundWidth h) (neutralWidth h) (scale ε (-h/2) x.1) x.2 := by
  simp only [energyDensity, pairedShifted, KFCausalGaussianResponseDensities.amplitude,
    KFCausalRelativeGaussianDifferential.profile, physicalDensity, clockWeight,
    KFCausalQuarticPlaneDomination.potential, Fin.val_zero, Fin.val_one,
    show (2:Fin 3).val=2 by rfl, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    one_mul, pow_zero, pow_one, mul_pow, sq_abs]
  ring

theorem response_density_factorization (ε a h : ℝ) (x : Configuration) :
    potentialDensity ε a h x =
      2*(KFCausalClockResponseTransport.weakSlope ε a 0 (-h/2) x.1).re *
        (clockWeight ε a 0 (-h/2) x.1 *
          physicalDensity (groundWidth h) (neutralWidth h) (scale ε (-h/2) x.1) x.2) := by
  rw [← energy_density_factorization]
  unfold potentialDensity responseDensity energyDensity
  ring

theorem energy_slice (ε a h s : ℝ) :
    (∫ q : Transverse, energyDensity ε a h (s,q)) =
      energy ε a 0 (-h/2) (physicalKernel ε h) s := by
  simp_rw [energy_density_factorization]
  rw [integral_const_mul]
  rfl

theorem response_slice (ε a h s : ℝ) :
    (∫ q : Transverse, potentialDensity ε a h (s,q)) =
      weakResponse ε a 0 (-h/2) (physicalKernel ε h) s := by
  simp_rw [response_density_factorization]
  rw [integral_const_mul, integral_const_mul]
  rfl

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3)

include hε ha hh hb in
theorem factor_density_integrable (n : Fin 3) :
    Integrable (fun x => ‖pairedShifted ε a h pointField n x‖^2) volume :=
  (pairedShifted_memLp ε a h hε ha hh hb modelDirections pointField n).integrable_norm_pow
    (by norm_num : (2:ℕ) ≠ 0)

include hε ha hh hb in
theorem energyDensity_integrable : Integrable (energyDensity ε a h) volume :=
  ((factor_density_integrable ε a h hε ha hh hb 0).add
    ((factor_density_integrable ε a h hε ha hh hb 1).div_const 2)).add
      ((factor_density_integrable ε a h hε ha hh hb 2).div_const 4)

include hε ha hh hb in
theorem clock_energy_integrable :
    Integrable (energy ε a 0 (-h/2) (physicalKernel ε h)) volume :=
  (energyDensity_integrable ε a h hε ha hh hb).integral_prod_left.congr
    (Filter.Eventually.of_forall (energy_slice ε a h))

include hε ha hh hb in
theorem clock_response_integrable :
    Integrable (weakResponse ε a 0 (-h/2) (physicalKernel ε h)) volume :=
  (potentialDensity_integrable ε a h hε ha hh hb).integral_prod_left.congr
    (Filter.Eventually.of_forall (response_slice ε a h))

theorem factorEnergy_integral (n : Fin 3) :
    factorEnergy ε a h hε ha hh hb (index n) =
      ∫ x, ‖pairedShifted ε a h pointField n x‖^2 := by
  rw [factorEnergy, KFCausalAveragedEnergyGraph.l2_norm_square volume]
  apply integral_congr_ae
  filter_upwards [output_coe ε a h hε ha hh hb modelDirections pointField n] with x hx
  rw [hx]

theorem potentialEnergy_integral :
    potentialEnergy ε a h hε ha hh hb = ∫ x, energyDensity ε a h x := by
  have h0 := factorEnergy_integral ε a h hε ha hh hb 0
  have h1 := factorEnergy_integral ε a h hε ha hh hb 1
  have h2 := factorEnergy_integral ε a h hε ha hh hb 2
  change factorEnergy ε a h hε ha hh hb 7 = _ at h0
  change factorEnergy ε a h hε ha hh hb 5 = _ at h1
  change factorEnergy ε a h hε ha hh hb 6 = _ at h2
  have hi : Integrable (fun x => ‖pairedShifted ε a h pointField 0 x‖^2+
      ‖pairedShifted ε a h pointField 1 x‖^2/2) volume :=
    (factor_density_integrable ε a h hε ha hh hb 0).add
      ((factor_density_integrable ε a h hε ha hh hb 1).div_const 2)
  unfold potentialEnergy energyDensity
  rw [integral_add hi ((factor_density_integrable ε a h hε ha hh hb 2).div_const 4),
    integral_add (factor_density_integrable ε a h hε ha hh hb 0)
      ((factor_density_integrable ε a h hε ha hh hb 1).div_const 2),
    integral_div, integral_div, ← h0, ← h1, ← h2]

theorem potentialEnergy_clock_integral :
    potentialEnergy ε a h hε ha hh hb =
      ∫ s, energy ε a 0 (-h/2) (physicalKernel ε h) s := by
  rw [potentialEnergy_integral]
  change (∫ x : ℝ × Transverse, energyDensity ε a h x ∂volume.prod volume) = _
  rw [integral_prod _ (energyDensity_integrable ε a h hε ha hh hb)]
  exact integral_congr_ae (Filter.Eventually.of_forall (energy_slice ε a h))

theorem potentialResponse_clock_integral :
    potentialResponse ε a h hε ha hh hb =
      ∫ s, weakResponse ε a 0 (-h/2) (physicalKernel ε h) s := by
  rw [KFCausalChargedPairPotentialResponse.potentialResponse_integral]
  change (∫ x : ℝ × Transverse, potentialDensity ε a h x ∂volume.prod volume) = _
  rw [integral_prod _ (potentialDensity_integrable ε a h hε ha hh hb)]
  exact integral_congr_ae (Filter.Eventually.of_forall (response_slice ε a h))

#print axioms energy_density_factorization
#print axioms response_density_factorization
#print axioms energy_slice
#print axioms response_slice
#print axioms factor_density_integrable
#print axioms energyDensity_integrable
#print axioms clock_energy_integrable
#print axioms clock_response_integrable
#print axioms factorEnergy_integral
#print axioms potentialEnergy_integral
#print axioms potentialEnergy_clock_integral
#print axioms potentialResponse_clock_integral
end
end UnifiedTheory.Audit.KFCausalChargedPairClockMarginal
