/- Full clock marginals of the actual centered/paired/corrected-quartic superposition.
The transverse kernel is the full absolute square of the sum; no cross
term is discarded when identifying the physical energy and response. -/
import UnifiedTheory.Audit.KFCausalQuarticTripleOrderedOutputs
import UnifiedTheory.Audit.KFCausalQuarticTripleHamiltonian
import UnifiedTheory.Audit.KFCausalQuarticSpanKernel
import UnifiedTheory.Audit.KFCausalPositiveKernelClockResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalQuarticTripleClockMarginal
noncomputable section
open MeasureTheory
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalQuarticTripleDomain (Coefficients)
open KFCausalQuarticTripleOrderedOutputs
  (shifted shifted_memLp embedCoefficients embedded_profile responseDensity responseDensity_integrable factorEnergy_integral factorRate_integral)
open KFCausalQuarticSpanKernel (kernel physicalDensity)
open KFCausalPositiveKernelClockResponse (clockWeight energy weakResponse)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalClockFloorInvariantTrial (neutralWidth)
open KFCausalQuarticTripleDomain (factorEnergy factorRate)
open KFCausalQuarticTripleHamiltonian (potentialEnergy potentialResponse)

def energyDensity (ε a h : ℝ) (c : Coefficients) (x : Configuration) : ℝ :=
  ‖shifted ε a h c 0 x‖^2+‖shifted ε a h c 1 x‖^2/2+‖shifted ε a h c 2 x‖^2/4
def potentialDensity (ε a h : ℝ) (c : Coefficients) (x : Configuration) : ℝ :=
  responseDensity ε a h c 0 x+responseDensity ε a h c 1 x/2+responseDensity ε a h c 2 x/4
def physicalKernel (ε h : ℝ) (c : Coefficients) (s : ℝ) : ℝ :=
  kernel (groundWidth h) (neutralWidth h) (scale ε (-h/2) s) (embedCoefficients (groundWidth h) c)

theorem energy_density_factorization (ε a h : ℝ) (c : Coefficients) (x : Configuration) :
    energyDensity ε a h c x = clockWeight ε a 0 (-h/2) x.1 *
      physicalDensity (groundWidth h) (neutralWidth h) (scale ε (-h/2) x.1) (embedCoefficients (groundWidth h) c) x.2 := by
  simp only [energyDensity, shifted, KFCausalGaussianResponseDensities.amplitude,
    KFCausalRelativeGaussianDifferential.profile, physicalDensity, embedded_profile, clockWeight,
    KFCausalQuarticPlaneDomination.potential, Fin.val_zero, Fin.val_one,
    show (2:Fin 3).val=2 by rfl, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    one_mul, pow_zero, pow_one, mul_pow, sq_abs]
  ring

theorem response_density_factorization (ε a h : ℝ) (c : Coefficients) (x : Configuration) :
    potentialDensity ε a h c x =
      2*(KFCausalClockResponseTransport.weakSlope ε a 0 (-h/2) x.1).re *
        (clockWeight ε a 0 (-h/2) x.1 *
          physicalDensity (groundWidth h) (neutralWidth h) (scale ε (-h/2) x.1) (embedCoefficients (groundWidth h) c) x.2) := by
  rw [← energy_density_factorization]
  unfold potentialDensity responseDensity energyDensity
  ring

theorem energy_slice (ε a h : ℝ) (c : Coefficients) (s : ℝ) :
    (∫ q : Transverse, energyDensity ε a h c (s,q)) =
      energy ε a 0 (-h/2) (physicalKernel ε h c) s := by
  simp_rw [energy_density_factorization]
  rw [integral_const_mul]
  rfl

theorem response_slice (ε a h : ℝ) (c : Coefficients) (s : ℝ) :
    (∫ q : Transverse, potentialDensity ε a h c (s,q)) =
      weakResponse ε a 0 (-h/2) (physicalKernel ε h c) s := by
  simp_rw [response_density_factorization]
  rw [integral_const_mul,integral_const_mul]
  rfl

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (c : Coefficients)

include hε ha hh hb in
theorem factor_density_integrable (n : Fin 3) :
    Integrable (fun x => ‖shifted ε a h c n x‖^2) volume :=
  (shifted_memLp ε a h hε ha hh hb c n).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)

include hε ha hh hb in
theorem energyDensity_integrable : Integrable (energyDensity ε a h c) volume :=
  ((factor_density_integrable ε a h hε ha hh hb c 0).add
    ((factor_density_integrable ε a h hε ha hh hb c 1).div_const 2)).add
      ((factor_density_integrable ε a h hε ha hh hb c 2).div_const 4)

include hε ha hh hb in
theorem potentialDensity_integrable : Integrable (potentialDensity ε a h c) volume :=
  ((responseDensity_integrable ε a h hε ha hh hb c 0).add
    ((responseDensity_integrable ε a h hε ha hh hb c 1).div_const 2)).add
      ((responseDensity_integrable ε a h hε ha hh hb c 2).div_const 4)

include hε ha hh hb in
theorem clock_energy_integrable :
    Integrable (energy ε a 0 (-h/2) (physicalKernel ε h c)) volume :=
  (energyDensity_integrable ε a h hε ha hh hb c).integral_prod_left.congr
    (Filter.Eventually.of_forall (energy_slice ε a h c))

include hε ha hh hb in
theorem clock_response_integrable :
    Integrable (weakResponse ε a 0 (-h/2) (physicalKernel ε h c)) volume :=
  (potentialDensity_integrable ε a h hε ha hh hb c).integral_prod_left.congr
    (Filter.Eventually.of_forall (response_slice ε a h c))

theorem potentialEnergy_integral :
    potentialEnergy ε a h hε ha hh hb c = ∫ x, energyDensity ε a h c x := by
  have h0 := factorEnergy_integral ε a h hε ha hh hb c 0
  have h1 := factorEnergy_integral ε a h hε ha hh hb c 1
  have h2 := factorEnergy_integral ε a h hε ha hh hb c 2
  change factorEnergy ε a h hε ha hh hb c 7 = _ at h0
  change factorEnergy ε a h hε ha hh hb c 5 = _ at h1
  change factorEnergy ε a h hε ha hh hb c 6 = _ at h2
  have hi : Integrable (fun x => ‖shifted ε a h c 0 x‖^2+‖shifted ε a h c 1 x‖^2/2) volume :=
    (factor_density_integrable ε a h hε ha hh hb c 0).add
      ((factor_density_integrable ε a h hε ha hh hb c 1).div_const 2)
  unfold potentialEnergy energyDensity
  rw [integral_add hi ((factor_density_integrable ε a h hε ha hh hb c 2).div_const 4),
    integral_add (factor_density_integrable ε a h hε ha hh hb c 0)
      ((factor_density_integrable ε a h hε ha hh hb c 1).div_const 2),
    integral_div,integral_div,← h0,← h1,← h2]

theorem potentialResponse_integral :
    potentialResponse ε a h hε ha hh hb c = ∫ x, potentialDensity ε a h c x := by
  have h0 := factorRate_integral ε a h hε ha hh hb c 0
  have h1 := factorRate_integral ε a h hε ha hh hb c 1
  have h2 := factorRate_integral ε a h hε ha hh hb c 2
  change factorRate ε a h hε ha hh hb c 7 = _ at h0
  change factorRate ε a h hε ha hh hb c 5 = _ at h1
  change factorRate ε a h hε ha hh hb c 6 = _ at h2
  have hi : Integrable (fun x => responseDensity ε a h c 0 x+responseDensity ε a h c 1 x/2) volume :=
    (responseDensity_integrable ε a h hε ha hh hb c 0).add
      ((responseDensity_integrable ε a h hε ha hh hb c 1).div_const 2)
  unfold potentialResponse potentialDensity
  rw [integral_add hi ((responseDensity_integrable ε a h hε ha hh hb c 2).div_const 4),
    integral_add (responseDensity_integrable ε a h hε ha hh hb c 0)
      ((responseDensity_integrable ε a h hε ha hh hb c 1).div_const 2),
    integral_div,integral_div,← h0,← h1,← h2]

theorem potentialEnergy_clock_integral :
    potentialEnergy ε a h hε ha hh hb c =
      ∫ s, energy ε a 0 (-h/2) (physicalKernel ε h c) s := by
  rw [potentialEnergy_integral]
  change (∫ x : ℝ × Transverse, energyDensity ε a h c x ∂volume.prod volume) = _
  rw [integral_prod _ (energyDensity_integrable ε a h hε ha hh hb c)]
  exact integral_congr_ae (Filter.Eventually.of_forall (energy_slice ε a h c))

theorem potentialResponse_clock_integral :
    potentialResponse ε a h hε ha hh hb c =
      ∫ s, weakResponse ε a 0 (-h/2) (physicalKernel ε h c) s := by
  rw [potentialResponse_integral]
  change (∫ x : ℝ × Transverse, potentialDensity ε a h c x ∂volume.prod volume) = _
  rw [integral_prod _ (potentialDensity_integrable ε a h hε ha hh hb c)]
  exact integral_congr_ae (Filter.Eventually.of_forall (response_slice ε a h c))

#print axioms energy_density_factorization
#print axioms response_density_factorization
#print axioms energy_slice
#print axioms response_slice
#print axioms factor_density_integrable
#print axioms energyDensity_integrable
#print axioms potentialDensity_integrable
#print axioms clock_energy_integrable
#print axioms clock_response_integrable
#print axioms potentialEnergy_integral
#print axioms potentialResponse_integral
#print axioms potentialEnergy_clock_integral
#print axioms potentialResponse_clock_integral
end
end UnifiedTheory.Audit.KFCausalQuarticTripleClockMarginal
