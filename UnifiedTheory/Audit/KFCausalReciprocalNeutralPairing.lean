/- Actual cross-packet ordered pairings reduce to a clock integral of
the joint two-dimensional neutral kernel. Independent clock frequencies,
sources, widths and polynomial degrees are retained. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralPhysicalPair

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralPairing
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalReciprocalNeutralPhysicalPair
open KFCausalReciprocalNeutralPackets (output momentumOutput)
open KFCausalReciprocalNeutralOrderedProfile (shiftedProfile)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalPolynomialOrderedMomentumDensity (clockSlope)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalReciprocalCrossGeometry (A B C)
open KFCausalComplexGaussianMoments (gaussianValue)

variable (ε h a₁ a₂ w₁ w₂ p₁ p₂ : ℝ) (C₁ C₂ b₁ b₂ : ℂ)
  (P₁ P₂ : Polynomial ℂ)
  (hε : 0 < ε) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hh : h ≠ 0)
  (hw₁ : 1 ≤ w₁) (hw₂ : 1 ≤ w₂) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "U₁" => output ε a₁ h w₁ hε ha₁ hh hw₁ C₁ p₁ b₁ P₁ hb
local notation "U₂" => output ε a₂ h w₂ hε ha₂ hh hw₂ C₂ p₂ b₂ P₂ hb
local notation "V₂" => momentumOutput ε a₂ h w₂ hε ha₂ hh hw₂ C₂ p₂ b₂ P₂ hb
local notation "S₁" => shiftedProfile ε a₁ (groundWidth h) (neutralWidth h) h w₁ C₁ p₁ b₁ P₁
local notation "S₂" => shiftedProfile ε a₂ (groundWidth h) (neutralWidth h) h w₂ C₂ p₂ b₂ P₂
local notation "D" => density ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂
local notation "MD" => momentumDensity ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂
local notation "K" => clockKernel ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂

theorem ordered_pair_clock_kernel :
    inner ℂ (U₁ 7) (U₂ 7)+inner ℂ (U₁ 5) (U₂ 5)/2+inner ℂ (U₁ 6) (U₂ 6)/4 = ∫ s, K s := by
  rw [← density_clock_integral ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂
    hε ha₁ ha₂ hh hw₁ hw₂ hb]
  have hi := factor_product_integrable ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂
    hε ha₁ ha₂ hh hw₁ hw₂ hb
  have h0 := factor_pair_integral ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂
    hε ha₁ ha₂ hh hw₁ hw₂ hb 0
  have h1 := factor_pair_integral ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂
    hε ha₁ ha₂ hh hw₁ hw₂ hb 1
  have h2 := factor_pair_integral ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂
    hε ha₁ ha₂ hh hw₁ hw₂ hb 2
  change inner ℂ (U₁ 7) (U₂ 7) = _ at h0
  change inner ℂ (U₁ 5) (U₂ 5) = _ at h1
  change inner ℂ (U₁ 6) (U₂ 6) = _ at h2
  let f (n : Fin 3) (x : Configuration) :=
    conj ((pointField x.2:ℂ)^n.val*S₁ x)*((pointField x.2:ℂ)^n.val*S₂ x)
  have he : D = fun x => f 0 x+f 1 x/2+f 2 x/4 := by
    funext x
    simp only [f,Fin.val_zero,Fin.val_one,show (2:Fin 3).val=2 from rfl,pow_zero,pow_one,one_mul]
    exact density_expansion ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ x
  have h01 : Integrable (fun x => f 0 x+f 1 x/2) := (hi 0).add ((hi 1).div_const 2)
  rw [he]
  change _ = ∫ x, f 0 x+f 1 x/2+f 2 x/4
  rw [integral_add h01 ((hi 2).div_const 4),integral_add (hi 0) ((hi 1).div_const 2),
    integral_div,integral_div]
  exact congrArg₂ (·+·) (congrArg₂ (·+·) h0 (congrArg (fun z : ℂ => z/2) h1))
    (congrArg (fun z : ℂ => z/4) h2)

theorem momentum_pair_clock_kernel :
    inner ℂ (U₁ 7) (V₂ 7)+inner ℂ (U₁ 5) (V₂ 5)/2+inner ℂ (U₁ 6) (V₂ 6)/4 =
      ∫ s, clockSlope ε a₂ h p₂ (s,0)*K s := by
  rw [← momentumDensity_clock_integral ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂
    hε ha₁ ha₂ hh hw₁ hw₂ hb]
  have hi := momentum_product_integrable ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂
    hε ha₁ ha₂ hh hw₁ hw₂ hb
  have h0 := momentum_pair_integral ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂
    hε ha₁ ha₂ hh hw₁ hw₂ hb 0
  have h1 := momentum_pair_integral ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂
    hε ha₁ ha₂ hh hw₁ hw₂ hb 1
  have h2 := momentum_pair_integral ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂
    hε ha₁ ha₂ hh hw₁ hw₂ hb 2
  change inner ℂ (U₁ 7) (V₂ 7) = _ at h0
  change inner ℂ (U₁ 5) (V₂ 5) = _ at h1
  change inner ℂ (U₁ 6) (V₂ 6) = _ at h2
  let f (n : Fin 3) (x : Configuration) :=
    conj ((pointField x.2:ℂ)^n.val*S₁ x)*
      (clockSlope ε a₂ h p₂ x*((pointField x.2:ℂ)^n.val*S₂ x))
  have he : MD = fun x => f 0 x+f 1 x/2+f 2 x/4 := by
    funext x
    simp only [momentumDensity,density_expansion,f,Fin.val_zero,Fin.val_one,
      show (2:Fin 3).val=2 from rfl,pow_zero,pow_one,one_mul]
    ring
  have h01 : Integrable (fun x => f 0 x+f 1 x/2) := (hi 0).add ((hi 1).div_const 2)
  rw [he]
  change _ = ∫ x, f 0 x+f 1 x/2+f 2 x/4
  rw [integral_add h01 ((hi 2).div_const 4),integral_add (hi 0) ((hi 1).div_const 2),
    integral_div,integral_div]
  exact congrArg₂ (·+·) (congrArg₂ (·+·) h0 (congrArg (fun z : ℂ => z/2) h1))
    (congrArg (fun z : ℂ => z/4) h2)

include hε ha₁ ha₂ hh hw₁ hw₂ hb in
theorem clockKernel_integrable : Integrable K :=
  (density_integrable ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂
    hε ha₁ ha₂ hh hw₁ hw₂ hb).integral_prod_left.congr
      (Filter.Eventually.of_forall (density_slice ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂))

include hε ha₁ ha₂ hh hw₁ hw₂ hb in
theorem momentumClockKernel_integrable : Integrable (fun s => clockSlope ε a₂ h p₂ (s,0)*K s) :=
  (momentumDensity_integrable ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂
    hε ha₁ ha₂ hh hw₁ hw₂ hb).integral_prod_left.congr
      (Filter.Eventually.of_forall (momentumDensity_slice ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂))

include hε hh hw₁ hw₂ hb in
theorem actual_widths (s : ℝ) :
    0 < (A (groundWidth h) w₁ w₂ (scale ε (-h/2) s)).re ∧
      0 < (B (groundWidth h) w₁ w₂ (scale ε (-h/2) s)).re := by
  have hy : |-h/2| ≤ Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  obtain ⟨hc,ha⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive _ _
    (groundWidth_positive h hh) _
    (KFCausalChargedPairCompactGeometry.actual_mem_region _ _ ε (-h/2) s
      (groundWidth_positive h hh) (neutralWidth_positive h hh).le (neutralWidth_bound h) hε hy)
  obtain ⟨hA,hB,_,_⟩ := KFCausalReciprocalCrossGeometry.widths_positive _ _ w₁ w₂ _
    hw₁ hw₂ ha hc (neutralWidth_positive h hh)
  exact ⟨hA,hB⟩

include hε hh hw₁ hw₂ hb in
theorem clockKernel_plane (s : ℝ) :
    K s = coefficient ε h a₁ a₂ p₁ p₂ C₁ C₂ s*
      ((1/4:ℂ)*gaussianValue (A (groundWidth h) w₁ w₂ (scale ε (-h/2) s))^2*
        gaussianValue (B (groundWidth h) w₁ w₂ (scale ε (-h/2) s))*
        ∫ u : Fin 2 → ℝ, KFCausalReciprocalNeutralKernel.planeDensity (neutralWidth h)
          (C (groundWidth h) (neutralWidth h) w₁ w₂ (scale ε (-h/2) s))
          (scale ε (-h/2) s) (neutralProfile b₁ P₁) (neutralProfile b₂ P₂) u) := by
  obtain ⟨hA,hB⟩ := actual_widths ε h w₁ w₂ hε hh hw₁ hw₂ hb s
  rw [clockKernel,KFCausalReciprocalNeutralKernel.kernel_gaussian_marginal _ _ w₁ w₂
    (by linarith) (by linarith) _ _ _ hA hB]

#print axioms ordered_pair_clock_kernel
#print axioms momentum_pair_clock_kernel
#print axioms clockKernel_integrable
#print axioms momentumClockKernel_integrable
#print axioms actual_widths
#print axioms clockKernel_plane
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralPairing
