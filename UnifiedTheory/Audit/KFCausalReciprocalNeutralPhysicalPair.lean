/- The two-dimensional cross kernel represents actual ordered energy
and momentum pairings. Absolute integrability follows from the proved
operator outputs before the clock integral is separated. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralOrderedProfile
import UnifiedTheory.Audit.KFCausalReciprocalNeutralKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralPhysicalPair
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalQuarticPlaneDomination (potential)
open KFCausalReciprocalNeutralOrderedProfile (shiftedProfile output_coe momentumOutput_coe)
open KFCausalReciprocalNeutralPackets (output momentumOutput)
open KFCausalReciprocalNeutralKernel (kernel)
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalClockFloorInvariantTrial (neutralWidth)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalPolynomialOrderedMomentumDensity (clockSlope)
open KFCausalSourcedResponseFactorBridge (index)

variable (ε h a₁ a₂ w₁ w₂ p₁ p₂ : ℝ) (C₁ C₂ b₁ b₂ : ℂ)
  (P₁ P₂ : Polynomial ℂ)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "S₁" => shiftedProfile ε a₁ α β h w₁ C₁ p₁ b₁ P₁
local notation "S₂" => shiftedProfile ε a₂ α β h w₂ C₂ p₂ b₂ P₂

def neutralProfile (b : ℂ) (P : Polynomial ℂ) (z : ℂ) : ℂ := Complex.exp (b*z)*P.eval z

def coefficient (s : ℝ) : ℂ :=
  conj (C₁*clockAmplitude ε a₁ p₁ (-h/2) s)*(C₂*clockAmplitude ε a₂ p₂ (-h/2) s)

def density (x : Configuration) : ℂ := (potential (pointField x.2):ℂ)*(conj (S₁ x)*S₂ x)

def momentumDensity (x : Configuration) : ℂ :=
  clockSlope ε a₂ h p₂ x*density ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ x

def clockKernel (s : ℝ) : ℂ :=
  coefficient ε h a₁ a₂ p₁ p₂ C₁ C₂ s*
    kernel α β w₁ w₂ (scale ε (-h/2) s) (neutralProfile b₁ P₁) (neutralProfile b₂ P₂)

theorem density_slice (s : ℝ) :
    (∫ q : Transverse, density ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ (s,q)) =
      clockKernel ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ s := by
  unfold clockKernel kernel
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  simp only [density,coefficient,shiftedProfile,KFCausalReciprocalNeutralKernel.density,
    KFCausalReciprocalCrossKernel.density,neutralProfile,map_mul]
  ring

theorem momentumDensity_slice (s : ℝ) :
    (∫ q : Transverse, momentumDensity ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ (s,q)) =
      clockSlope ε a₂ h p₂ (s,0)*clockKernel ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ s := by
  unfold momentumDensity
  change (∫ q : Transverse, clockSlope ε a₂ h p₂ (s,0)*
    density ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ (s,q)) = _
  rw [integral_const_mul,density_slice]

theorem density_expansion (x : Configuration) :
    density ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ x =
      conj (S₁ x)*S₂ x+
        conj ((pointField x.2:ℂ)*S₁ x)*((pointField x.2:ℂ)*S₂ x)/2+
        conj ((pointField x.2:ℂ)^2*S₁ x)*((pointField x.2:ℂ)^2*S₂ x)/4 := by
  simp only [density,potential,map_mul,map_pow,Complex.conj_ofReal]
  push_cast
  ring

variable (hε : 0 < ε) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hh : h ≠ 0)
  (hw₁ : 1 ≤ w₁) (hw₂ : 1 ≤ w₂) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "U₁" => output ε a₁ h w₁ hε ha₁ hh hw₁ C₁ p₁ b₁ P₁ hb
local notation "U₂" => output ε a₂ h w₂ hε ha₂ hh hw₂ C₂ p₂ b₂ P₂ hb
local notation "V₂" => momentumOutput ε a₂ h w₂ hε ha₂ hh hw₂ C₂ p₂ b₂ P₂ hb

include hε ha₁ ha₂ hh hw₁ hw₂ hb in
theorem factor_product_integrable (n : Fin 3) :
    Integrable (fun x : Configuration =>
      conj ((pointField x.2:ℂ)^n.val*S₁ x)*((pointField x.2:ℂ)^n.val*S₂ x)) := by
  have h1 := (Lp.memLp (U₁ (index n))).ae_eq
    (output_coe ε a₁ h w₁ hε ha₁ hh hw₁ C₁ p₁ b₁ P₁ hb n)
  have h2 := (Lp.memLp (U₂ (index n))).ae_eq
    (output_coe ε a₂ h w₂ hε ha₂ hh hw₂ C₂ p₂ b₂ P₂ hb n)
  simpa only [Complex.star_def] using h1.star.integrable_mul h2

include hε ha₁ ha₂ hh hw₁ hw₂ hb in
theorem momentum_product_integrable (n : Fin 3) :
    Integrable (fun x : Configuration =>
      conj ((pointField x.2:ℂ)^n.val*S₁ x)*
        (clockSlope ε a₂ h p₂ x*((pointField x.2:ℂ)^n.val*S₂ x))) := by
  have h1 := (Lp.memLp (U₁ (index n))).ae_eq
    (output_coe ε a₁ h w₁ hε ha₁ hh hw₁ C₁ p₁ b₁ P₁ hb n)
  have h2 := (Lp.memLp (V₂ (index n))).ae_eq
    (momentumOutput_coe ε a₂ h w₂ hε ha₂ hh hw₂ C₂ p₂ b₂ P₂ hb n)
  simpa only [Complex.star_def] using h1.star.integrable_mul h2

include hε ha₁ ha₂ hh hw₁ hw₂ hb in
theorem density_integrable : Integrable (density ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂) := by
  have hi := factor_product_integrable ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂
    hε ha₁ ha₂ hh hw₁ hw₂ hb
  apply (((hi 0).add ((hi 1).div_const 2)).add ((hi 2).div_const 4)).congr
  filter_upwards [] with x
  convert (density_expansion ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ x).symm using 1
  simp

include hε ha₁ ha₂ hh hw₁ hw₂ hb in
theorem momentumDensity_integrable :
    Integrable (momentumDensity ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂) := by
  have hi := momentum_product_integrable ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂
    hε ha₁ ha₂ hh hw₁ hw₂ hb
  apply (((hi 0).add ((hi 1).div_const 2)).add ((hi 2).div_const 4)).congr
  filter_upwards [] with x
  simp only [Pi.add_apply,momentumDensity,density_expansion,Fin.val_zero,Fin.val_one,
    show (2:Fin 3).val=2 from rfl,pow_zero,pow_one,one_mul]
  ring

theorem factor_pair_integral (n : Fin 3) :
    inner ℂ (U₁ (index n)) (U₂ (index n)) =
      ∫ x : Configuration, conj ((pointField x.2:ℂ)^n.val*S₁ x)*((pointField x.2:ℂ)^n.val*S₂ x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [output_coe ε a₁ h w₁ hε ha₁ hh hw₁ C₁ p₁ b₁ P₁ hb n,
    output_coe ε a₂ h w₂ hε ha₂ hh hw₂ C₂ p₂ b₂ P₂ hb n] with x hx hy
  simp only [hx,hy,RCLike.inner_apply]
  ring

theorem momentum_pair_integral (n : Fin 3) :
    inner ℂ (U₁ (index n)) (V₂ (index n)) =
      ∫ x : Configuration, conj ((pointField x.2:ℂ)^n.val*S₁ x)*
        (clockSlope ε a₂ h p₂ x*((pointField x.2:ℂ)^n.val*S₂ x)) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [output_coe ε a₁ h w₁ hε ha₁ hh hw₁ C₁ p₁ b₁ P₁ hb n,
    momentumOutput_coe ε a₂ h w₂ hε ha₂ hh hw₂ C₂ p₂ b₂ P₂ hb n] with x hx hy
  simp only [hx,hy,RCLike.inner_apply]
  ring

include hε ha₁ ha₂ hh hw₁ hw₂ hb in
theorem density_clock_integral :
    (∫ x, density ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ x) =
      ∫ s, clockKernel ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ s := by
  change (∫ x : Configuration, density ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ x
    ∂volume.prod volume) = _
  rw [integral_prod _ (density_integrable ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂
    hε ha₁ ha₂ hh hw₁ hw₂ hb)]
  simp_rw [density_slice]

include hε ha₁ ha₂ hh hw₁ hw₂ hb in
theorem momentumDensity_clock_integral :
    (∫ x, momentumDensity ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ x) =
      ∫ s, clockSlope ε a₂ h p₂ (s,0)*clockKernel ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ s := by
  change (∫ x : Configuration, momentumDensity ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ x
    ∂volume.prod volume) = _
  rw [integral_prod _ (momentumDensity_integrable ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂
    hε ha₁ ha₂ hh hw₁ hw₂ hb)]
  simp_rw [momentumDensity_slice]

#print axioms density_slice
#print axioms momentumDensity_slice
#print axioms density_expansion
#print axioms factor_product_integrable
#print axioms momentum_product_integrable
#print axioms density_integrable
#print axioms momentumDensity_integrable
#print axioms factor_pair_integral
#print axioms momentum_pair_integral
#print axioms density_clock_integral
#print axioms momentumDensity_clock_integral
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralPhysicalPair
