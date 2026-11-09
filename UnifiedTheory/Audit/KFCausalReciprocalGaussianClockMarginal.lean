/- Actual reciprocal-state energy and response reduce to a single clock
integral with the exact positive transverse potential kernel. Fubini and
absolute integrability follow from the already constructed L2 outputs. -/
import UnifiedTheory.Audit.KFCausalReciprocalGaussianPotentialResponse
import UnifiedTheory.Audit.KFCausalReciprocalGaussianKernel
import UnifiedTheory.Audit.KFCausalPositiveKernelClockResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalGaussianClockMarginal
noncomputable section
open MeasureTheory
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalReciprocalGaussianOutputs (shifted output_coe)
open KFCausalReciprocalGaussianKernel (kernel physicalDensity)
open KFCausalPositiveKernelClockResponse (clockWeight energy weakResponse)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalClockFloorInvariantTrial (neutralWidth)
open KFCausalReciprocalGaussianPotentialResponse (potentialDensity responseDensity potentialDensity_integrable)
open KFCausalReciprocalGaussianResponse (factorEnergy)
open KFCausalReciprocalGaussianResponse (potentialEnergy potentialResponse)
open KFCausalSourcedResponseFactorBridge (index)

def energyDensity (ε a h w : ℝ) (x : Configuration) : ℝ :=
  ‖shifted ε a h w 0 x‖^2+
    ‖shifted ε a h w 1 x‖^2/2+
      ‖shifted ε a h w 2 x‖^2/4

def physicalKernel (ε h w s : ℝ) : ℝ :=
  kernel (groundWidth h) (neutralWidth h) w (scale ε (-h/2) s)

theorem energy_density_factorization (ε a h w : ℝ) (x : Configuration) :
    energyDensity ε a h w x =
      clockWeight ε a 0 (-h/2) x.1 *
        physicalDensity (groundWidth h) (neutralWidth h) w (scale ε (-h/2) x.1) x.2 := by
  simp only [energyDensity, shifted, physicalDensity, clockWeight,
    KFCausalQuarticPlaneDomination.potential, Fin.val_zero, Fin.val_one,
    show (2:Fin 3).val=2 by rfl, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    pow_zero, pow_one, mul_pow, sq_abs,norm_one]
  ring

theorem response_density_factorization (ε a h w : ℝ) (x : Configuration) :
    potentialDensity ε a h w x =
      2*(KFCausalClockResponseTransport.weakSlope ε a 0 (-h/2) x.1).re *
        (clockWeight ε a 0 (-h/2) x.1 *
          physicalDensity (groundWidth h) (neutralWidth h) w (scale ε (-h/2) x.1) x.2) := by
  rw [← energy_density_factorization]
  unfold potentialDensity responseDensity energyDensity
  ring

theorem energy_slice (ε a h w s : ℝ) :
    (∫ q : Transverse, energyDensity ε a h w (s,q)) =
      energy ε a 0 (-h/2) (physicalKernel ε h w) s := by
  simp_rw [energy_density_factorization]
  rw [integral_const_mul]
  rfl

theorem response_slice (ε a h w s : ℝ) :
    (∫ q : Transverse, potentialDensity ε a h w (s,q)) =
      weakResponse ε a 0 (-h/2) (physicalKernel ε h w) s := by
  simp_rw [response_density_factorization]
  rw [integral_const_mul, integral_const_mul]
  rfl

variable (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hw : 1 ≤ w)
  (hb : |h| ≤ 2*Real.pi*ε/3)

include hε ha hh hw hb in
theorem factor_density_integrable (n : Fin 3) :
    Integrable (fun x => ‖shifted ε a h w n x‖^2) volume :=
  ((Lp.memLp (KFCausalReciprocalGaussianMomentum.output ε a h w hε ha hh hw hb (index n))).ae_eq
    (output_coe ε a h w hε ha hh hw hb n)).integrable_norm_pow
    (by norm_num : (2:ℕ) ≠ 0)

include hε ha hh hw hb in
theorem energyDensity_integrable : Integrable (energyDensity ε a h w) volume :=
  ((factor_density_integrable ε a h w hε ha hh hw hb 0).add
    ((factor_density_integrable ε a h w hε ha hh hw hb 1).div_const 2)).add
      ((factor_density_integrable ε a h w hε ha hh hw hb 2).div_const 4)

include hε ha hh hw hb in
theorem clock_energy_integrable :
    Integrable (energy ε a 0 (-h/2) (physicalKernel ε h w)) volume :=
  (energyDensity_integrable ε a h w hε ha hh hw hb).integral_prod_left.congr
    (Filter.Eventually.of_forall (energy_slice ε a h w))

include hε ha hh hw hb in
theorem clock_response_integrable :
    Integrable (weakResponse ε a 0 (-h/2) (physicalKernel ε h w)) volume :=
  (potentialDensity_integrable ε a h w hε ha hh hw hb).integral_prod_left.congr
    (Filter.Eventually.of_forall (response_slice ε a h w))

theorem factorEnergy_integral (n : Fin 3) :
    factorEnergy ε a h w hε ha hh hw hb (index n) =
      ∫ x, ‖shifted ε a h w n x‖^2 := by
  rw [factorEnergy, KFCausalAveragedEnergyGraph.l2_norm_square volume]
  apply integral_congr_ae
  filter_upwards [output_coe ε a h w hε ha hh hw hb n] with x hx
  rw [hx]

theorem potentialEnergy_integral :
    potentialEnergy ε a h w hε ha hh hw hb = ∫ x, energyDensity ε a h w x := by
  have h0 := factorEnergy_integral ε a h w hε ha hh hw hb 0
  have h1 := factorEnergy_integral ε a h w hε ha hh hw hb 1
  have h2 := factorEnergy_integral ε a h w hε ha hh hw hb 2
  change factorEnergy ε a h w hε ha hh hw hb 7 = _ at h0
  change factorEnergy ε a h w hε ha hh hw hb 5 = _ at h1
  change factorEnergy ε a h w hε ha hh hw hb 6 = _ at h2
  have hi : Integrable (fun x => ‖shifted ε a h w 0 x‖^2+
      ‖shifted ε a h w 1 x‖^2/2) volume :=
    (factor_density_integrable ε a h w hε ha hh hw hb 0).add
      ((factor_density_integrable ε a h w hε ha hh hw hb 1).div_const 2)
  unfold potentialEnergy energyDensity
  rw [integral_add hi ((factor_density_integrable ε a h w hε ha hh hw hb 2).div_const 4),
    integral_add (factor_density_integrable ε a h w hε ha hh hw hb 0)
      ((factor_density_integrable ε a h w hε ha hh hw hb 1).div_const 2),
    integral_div, integral_div, ← h0, ← h1, ← h2]

theorem potentialEnergy_clock_integral :
    potentialEnergy ε a h w hε ha hh hw hb =
      ∫ s, energy ε a 0 (-h/2) (physicalKernel ε h w) s := by
  rw [potentialEnergy_integral]
  change (∫ x : ℝ × Transverse, energyDensity ε a h w x ∂volume.prod volume) = _
  rw [integral_prod _ (energyDensity_integrable ε a h w hε ha hh hw hb)]
  exact integral_congr_ae (Filter.Eventually.of_forall (energy_slice ε a h w))

theorem potentialResponse_clock_integral :
    potentialResponse ε a h w hε ha hh hw hb =
      ∫ s, weakResponse ε a 0 (-h/2) (physicalKernel ε h w) s := by
  rw [KFCausalReciprocalGaussianPotentialResponse.potentialResponse_integral]
  change (∫ x : ℝ × Transverse, potentialDensity ε a h w x ∂volume.prod volume) = _
  rw [integral_prod _ (potentialDensity_integrable ε a h w hε ha hh hw hb)]
  exact integral_congr_ae (Filter.Eventually.of_forall (response_slice ε a h w))

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
end UnifiedTheory.Audit.KFCausalReciprocalGaussianClockMarginal
