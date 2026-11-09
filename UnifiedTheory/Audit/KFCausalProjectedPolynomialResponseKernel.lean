/- Exact integrable configuration-space kernels for projected polynomial
ordered energy and momentum pairings. Arbitrary complex polynomials
retain all interference. These are whole-configuration weak response
kernels; no clock integration by parts or uniform estimate is assumed. -/
import UnifiedTheory.Audit.KFCausalProjectedPolynomialOrderedProfile
import UnifiedTheory.Audit.KFCausalProjectedPolynomialMomentumDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalProjectedPolynomialResponseKernel
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalProjectedPolynomialOrderedProfile (shiftedWeight)
open UnifiedTheory.Audit.KFCausalPolynomialOrderedMomentumDensity (clockSlope)
open UnifiedTheory.Audit.KFCausalSourcedResponseFactorBridge (index)
open UnifiedTheory.Audit.KFCausalDisplacedPolynomialProjectedResponse
  (meanInput meanMomentum factorEnergy factorRate)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources (clockFrequency)
open UnifiedTheory.Audit.KFCausalClockResponseTransport (weakSlope)

theorem response_scalar (h : ℝ) (hh : h ≠ 0) (z : ℂ) (d : ℝ) :
    (-2/h)*(((-Complex.I*(h:ℂ))*z)*(d:ℂ)).im = 2*z.re*d := by
  simp only [Complex.mul_im,Complex.mul_re,Complex.neg_re,Complex.neg_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im]
  field_simp [hh]
  ring

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (q k : Joint 2 4)

def kernel (P Q : Polynomial ℂ) (n : Fin 3) (x : Configuration) : ℂ :=
  star (shiftedWeight ε h P x)*shiftedWeight ε h Q x*
    ((‖meanInput ε a h hε ha hh hb q k 1 (index n) x‖^2:ℝ):ℂ)

def momentumKernel (P Q : Polynomial ℂ) (n : Fin 3) (x : Configuration) : ℂ :=
  clockSlope ε a h (clockFrequency h k) x*kernel ε a h hε ha hh hb q k P Q n x

def responseDensity (P : Polynomial ℂ) (n : Fin 3) (x : Configuration) : ℝ :=
  2*(weakSlope ε a (clockFrequency h k) (-h/2) x.1).re*
    ‖shiftedWeight ε h P x‖^2*‖meanInput ε a h hε ha hh hb q k 1 (index n) x‖^2

theorem energy_density (P Q : Polynomial ℂ) (n : Fin 3) :
    (fun x : Configuration => inner ℂ (meanInput ε a h hε ha hh hb q k P (index n) x)
      (meanInput ε a h hε ha hh hb q k Q (index n) x)) =ᵐ[volume]
        kernel ε a h hε ha hh hb q k P Q n := by
  filter_upwards [KFCausalProjectedPolynomialOrderedProfile.mean_relation ε a h hε ha hh hb q k P n,
    KFCausalProjectedPolynomialOrderedProfile.mean_relation ε a h hε ha hh hb q k Q n] with x hp hQ
  rw [hp,hQ]
  simp only [RCLike.inner_apply,map_mul,Complex.star_def,kernel,Complex.ofReal_pow]
  calc
    _ = starRingEnd ℂ (shiftedWeight ε h P x)*shiftedWeight ε h Q x*
        (starRingEnd ℂ (meanInput ε a h hε ha hh hb q k 1 (index n) x)*
          meanInput ε a h hε ha hh hb q k 1 (index n) x) := by ring
    _ = _ := by rw [Complex.conj_mul']

theorem energy_kernel_integrable (P Q : Polynomial ℂ) (n : Fin 3) :
    Integrable (kernel ε a h hε ha hh hb q k P Q n) volume :=
  (L2.integrable_inner (𝕜 := ℂ) (meanInput ε a h hε ha hh hb q k P (index n))
    (meanInput ε a h hε ha hh hb q k Q (index n))).congr
      (energy_density ε a h hε ha hh hb q k P Q n)

theorem energy_pairing (P Q : Polynomial ℂ) (n : Fin 3) :
    inner ℂ (meanInput ε a h hε ha hh hb q k P (index n))
      (meanInput ε a h hε ha hh hb q k Q (index n)) =
        ∫ x : Configuration, kernel ε a h hε ha hh hb q k P Q n x := by
  rw [L2.inner_def]
  exact integral_congr_ae (energy_density ε a h hε ha hh hb q k P Q n)

theorem momentum_density (P Q : Polynomial ℂ) (n : Fin 3) :
    (fun x : Configuration => inner ℂ (meanInput ε a h hε ha hh hb q k P (index n) x)
      (meanMomentum ε a h hε ha hh hb q k Q (index n) x)) =ᵐ[volume]
        momentumKernel ε a h hε ha hh hb q k P Q n := by
  filter_upwards [KFCausalProjectedPolynomialMomentumDensity.mean_relation ε a h hε ha hh hb q k Q n,
    energy_density ε a h hε ha hh hb q k P Q n] with x hm he
  rw [hm]
  change inner ℂ (meanInput ε a h hε ha hh hb q k P (index n) x)
    (clockSlope ε a h (clockFrequency h k) x • meanInput ε a h hε ha hh hb q k Q (index n) x) = _
  rw [inner_smul_right,he]
  rfl

theorem momentum_kernel_integrable (P Q : Polynomial ℂ) (n : Fin 3) :
    Integrable (momentumKernel ε a h hε ha hh hb q k P Q n) volume :=
  (L2.integrable_inner (𝕜 := ℂ) (meanInput ε a h hε ha hh hb q k P (index n))
    (meanMomentum ε a h hε ha hh hb q k Q (index n))).congr
      (momentum_density ε a h hε ha hh hb q k P Q n)

theorem momentum_pairing (P Q : Polynomial ℂ) (n : Fin 3) :
    inner ℂ (meanInput ε a h hε ha hh hb q k P (index n))
      (meanMomentum ε a h hε ha hh hb q k Q (index n)) =
        ∫ x : Configuration, momentumKernel ε a h hε ha hh hb q k P Q n x := by
  rw [L2.inner_def]
  exact integral_congr_ae (momentum_density ε a h hε ha hh hb q k P Q n)

theorem kernel_self (P : Polynomial ℂ) (n : Fin 3) (x : Configuration) :
    kernel ε a h hε ha hh hb q k P P n x =
      ((‖shiftedWeight ε h P x‖^2*‖meanInput ε a h hε ha hh hb q k 1 (index n) x‖^2:ℝ):ℂ) := by
  simp only [kernel,Complex.star_def,Complex.conj_mul',Complex.ofReal_mul,Complex.ofReal_pow]

theorem diagonal_density (P : Polynomial ℂ) (n : Fin 3) (x : Configuration) :
    (-2/h)*(momentumKernel ε a h hε ha hh hb q k P P n x).im =
      responseDensity ε a h hε ha hh hb q k P n x := by
  rw [momentumKernel,kernel_self]
  unfold clockSlope responseDensity
  rw [response_scalar h hh]
  ring

theorem response_density_integrable (P : Polynomial ℂ) (n : Fin 3) :
    Integrable (responseDensity ε a h hε ha hh hb q k P n) volume :=
  ((momentum_kernel_integrable ε a h hε ha hh hb q k P P n).im.const_mul (-2/h)).congr
    (Filter.Eventually.of_forall (diagonal_density ε a h hε ha hh hb q k P n))

theorem factorRate_integral (P : Polynomial ℂ) (n : Fin 3) :
    factorRate ε a h hε ha hh hb q k P (index n) =
      ∫ x : Configuration, responseDensity ε a h hε ha hh hb q k P n x := by
  have him : (∫ x : Configuration,
      (momentumKernel ε a h hε ha hh hb q k P P n x).im) =
      (∫ x : Configuration, momentumKernel ε a h hε ha hh hb q k P P n x).im :=
    integral_im (momentum_kernel_integrable ε a h hε ha hh hb q k P P n)
  rw [factorRate,momentum_pairing,← him,← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall (diagonal_density ε a h hε ha hh hb q k P n))

theorem factorEnergy_integral (P : Polynomial ℂ) (n : Fin 3) :
    factorEnergy ε a h hε ha hh hb q k P (index n) =
      ∫ x : Configuration, ‖shiftedWeight ε h P x‖^2*
        ‖meanInput ε a h hε ha hh hb q k 1 (index n) x‖^2 := by
  rw [factorEnergy,KFCausalAveragedEnergyGraph.l2_norm_square]
  apply integral_congr_ae
  filter_upwards [KFCausalProjectedPolynomialOrderedProfile.mean_relation ε a h hε ha hh hb q k P n]
    with x hx
  rw [hx,norm_mul,mul_pow]

#print axioms response_scalar
#print axioms energy_density
#print axioms energy_kernel_integrable
#print axioms energy_pairing
#print axioms momentum_density
#print axioms momentum_kernel_integrable
#print axioms momentum_pairing
#print axioms kernel_self
#print axioms diagonal_density
#print axioms response_density_integrable
#print axioms factorRate_integral
#print axioms factorEnergy_integral
end
end UnifiedTheory.Audit.KFCausalProjectedPolynomialResponseKernel
