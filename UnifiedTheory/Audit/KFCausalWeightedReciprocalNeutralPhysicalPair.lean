/- Actual weighted energy and momentum pairings, with per-channel L1
derived from the original operator outputs before separating the clock.
The identities allow arbitrary real weights and arbitrary neutral sources. -/
import UnifiedTheory.Audit.KFCausalWeightedReciprocalNeutralCross
import UnifiedTheory.Audit.KFCausalReciprocalNeutralPhysicalPair

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalWeightedReciprocalNeutralPhysicalPair
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalReciprocalNeutralOrderedProfile (shiftedProfile)
open KFCausalReciprocalNeutralPhysicalPair (coefficient)
open KFCausalReciprocalNeutralPackets (output momentumOutput)
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalClockFloorInvariantTrial (neutralWidth)
open KFCausalPolynomialOrderedMomentumDensity (clockSlope)
open KFCausalSourcedResponseFactorBridge (index)
open KFCausalReciprocalNeutralCrossBounds (pairIntegral)

variable (ε h a₁ a₂ w₁ w₂ p₁ p₂ : ℝ) (C₁ C₂ b₁ b₂ : ℂ)
  (P₁ P₂ : Polynomial ℂ)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "S₁" => shiftedProfile ε a₁ α β h w₁ C₁ p₁ b₁ P₁
local notation "S₂" => shiftedProfile ε a₂ α β h w₂ C₂ p₂ b₂ P₂

def channelClockKernel (k : ℕ) (s : ℝ) : ℂ :=
  coefficient ε h a₁ a₂ p₁ p₂ C₁ C₂ s*
    pairIntegral ε (-h/2) α β w₁ w₂ b₁ b₂ P₁ P₂ k s

private theorem channel_slice (k : ℕ) (s : ℝ) :
    (∫ q : Transverse, conj ((pointField q:ℂ)^k*S₁ (s,q))*
      ((pointField q:ℂ)^k*S₂ (s,q))) =
      channelClockKernel ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ k s := by
  unfold channelClockKernel pairIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  simp only [coefficient,shiftedProfile,KFCausalReciprocalNeutralCrossBounds.density,
    KFCausalReciprocalNeutralClockEnvelope.curve,KFCausalReciprocalNeutralSliceIntegrability.factor,
    KFCausalNeutralExponentialProfiles.exponentialProfile,one_mul,map_mul]
  ring

private theorem momentum_channel_slice (k : ℕ) (s : ℝ) :
    (∫ q : Transverse, conj ((pointField q:ℂ)^k*S₁ (s,q))*
      (clockSlope ε a₂ h p₂ (s,q)*((pointField q:ℂ)^k*S₂ (s,q)))) =
      clockSlope ε a₂ h p₂ (s,0)*
        channelClockKernel ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ k s := by
  rw [← channel_slice ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ k s,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  change _ = clockSlope ε a₂ h p₂ (s,q)*_
  ring

variable (hε : 0 < ε) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hh : h ≠ 0)
  (hw₁ : 1 ≤ w₁) (hw₂ : 1 ≤ w₂) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "U₁" => output ε a₁ h w₁ hε ha₁ hh hw₁ C₁ p₁ b₁ P₁ hb
local notation "U₂" => output ε a₂ h w₂ hε ha₂ hh hw₂ C₂ p₂ b₂ P₂ hb
local notation "V₂" => momentumOutput ε a₂ h w₂ hε ha₂ hh hw₂ C₂ p₂ b₂ P₂ hb
local notation "K" => channelClockKernel ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂

include hε ha₁ ha₂ hh hw₁ hw₂ hb in
theorem channel_integrable (k : Fin 3) : Integrable (K k.val) :=
  (KFCausalReciprocalNeutralPhysicalPair.factor_product_integrable
    ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ hε ha₁ ha₂ hh hw₁ hw₂ hb k).integral_prod_left.congr
      (Filter.Eventually.of_forall (channel_slice ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ k.val))

include hε ha₁ ha₂ hh hw₁ hw₂ hb in
theorem momentum_channel_integrable (k : Fin 3) :
    Integrable (fun s => clockSlope ε a₂ h p₂ (s,0)*K k.val s) :=
  (KFCausalReciprocalNeutralPhysicalPair.momentum_product_integrable
    ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ hε ha₁ ha₂ hh hw₁ hw₂ hb k).integral_prod_left.congr
      (Filter.Eventually.of_forall (momentum_channel_slice ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ k.val))

theorem channel_pair (k : Fin 3) :
    inner ℂ (U₁ (index k)) (U₂ (index k)) = ∫ s, K k.val s := by
  rw [KFCausalReciprocalNeutralPhysicalPair.factor_pair_integral]
  have hi := KFCausalReciprocalNeutralPhysicalPair.factor_product_integrable
    ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ hε ha₁ ha₂ hh hw₁ hw₂ hb k
  rw [show (volume : Measure Configuration)=volume.prod volume from rfl,integral_prod _ hi]
  simp_rw [channel_slice]

theorem momentum_channel_pair (k : Fin 3) :
    inner ℂ (U₁ (index k)) (V₂ (index k)) = ∫ s, clockSlope ε a₂ h p₂ (s,0)*K k.val s := by
  rw [KFCausalReciprocalNeutralPhysicalPair.momentum_pair_integral]
  have hi := KFCausalReciprocalNeutralPhysicalPair.momentum_product_integrable
    ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ hε ha₁ ha₂ hh hw₁ hw₂ hb k
  rw [show (volume : Measure Configuration)=volume.prod volume from rfl,integral_prod _ hi]
  simp_rw [momentum_channel_slice]

variable (mass2 quartic vacuum : ℝ)

def clockKernel (s : ℝ) : ℂ :=
  coefficient ε h a₁ a₂ p₁ p₂ C₁ C₂ s*
    KFCausalWeightedReciprocalNeutralCross.actual mass2 quartic vacuum ε (-h/2) α β
      w₁ w₂ b₁ b₂ P₁ P₂ s

private theorem clockKernel_channels (s : ℝ) :
    clockKernel ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ mass2 quartic vacuum s =
      (vacuum:ℂ)*K 0 s+(mass2:ℂ)*K 1 s/2+(quartic:ℂ)*K 2 s/4 := by
  unfold clockKernel KFCausalWeightedReciprocalNeutralCross.actual channelClockKernel
  ring

local notation "WK" => clockKernel ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ mass2 quartic vacuum

include hε ha₁ ha₂ hh hw₁ hw₂ hb in
theorem clockKernel_integrable : Integrable WK := by
  have hi := channel_integrable ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ hε ha₁ ha₂ hh hw₁ hw₂ hb
  exact (((hi 0).const_mul (vacuum:ℂ)).add (((hi 1).const_mul (mass2:ℂ)).div_const 2)).add
    (((hi 2).const_mul (quartic:ℂ)).div_const 4) |>.congr
      (Filter.Eventually.of_forall (fun s => (clockKernel_channels ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ mass2 quartic vacuum s).symm))

include hε ha₁ ha₂ hh hw₁ hw₂ hb in
theorem momentumClockKernel_integrable : Integrable (fun s => clockSlope ε a₂ h p₂ (s,0)*WK s) := by
  have hi := momentum_channel_integrable ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ hε ha₁ ha₂ hh hw₁ hw₂ hb
  apply ((((hi 0).const_mul (vacuum:ℂ)).add (((hi 1).const_mul (mass2:ℂ)).div_const 2)).add
    (((hi 2).const_mul (quartic:ℂ)).div_const 4)).congr
  filter_upwards [] with s
  simp only [Pi.add_apply,clockKernel_channels,Fin.val_zero,Fin.val_one,show (2:Fin 3).val=2 from rfl]
  ring

theorem ordered_pair_clock_kernel :
    (vacuum:ℂ)*inner ℂ (U₁ 7) (U₂ 7)+(mass2:ℂ)*inner ℂ (U₁ 5) (U₂ 5)/2+
      (quartic:ℂ)*inner ℂ (U₁ 6) (U₂ 6)/4 = ∫ s, WK s := by
  have hi := channel_integrable ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ hε ha₁ ha₂ hh hw₁ hw₂ hb
  have h0 : Integrable (K 0) := hi 0
  have h1 : Integrable (K 1) := hi 1
  have h2 : Integrable (K 2) := hi 2
  have h01 : Integrable (fun s => (vacuum:ℂ)*K 0 s+(mass2:ℂ)*K 1 s/2) :=
    (h0.const_mul (vacuum:ℂ)).add ((h1.const_mul (mass2:ℂ)).div_const 2)
  simp_rw [clockKernel_channels]
  rw [integral_add h01
    ((h2.const_mul (quartic:ℂ)).div_const 4),
    integral_add (h0.const_mul (vacuum:ℂ)) ((h1.const_mul (mass2:ℂ)).div_const 2)]
  simp only [integral_div,integral_const_mul]
  have e0 := channel_pair ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ hε ha₁ ha₂ hh hw₁ hw₂ hb 0
  change inner ℂ (U₁ 7) (U₂ 7)=(∫ s, K 0 s) at e0
  have e1 := channel_pair ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ hε ha₁ ha₂ hh hw₁ hw₂ hb 1
  change inner ℂ (U₁ 5) (U₂ 5)=(∫ s, K 1 s) at e1
  have e2 := channel_pair ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ hε ha₁ ha₂ hh hw₁ hw₂ hb 2
  change inner ℂ (U₁ 6) (U₂ 6)=(∫ s, K 2 s) at e2
  rw [← e0,← e1,← e2]

theorem momentum_pair_clock_kernel :
    (vacuum:ℂ)*inner ℂ (U₁ 7) (V₂ 7)+(mass2:ℂ)*inner ℂ (U₁ 5) (V₂ 5)/2+
      (quartic:ℂ)*inner ℂ (U₁ 6) (V₂ 6)/4 = ∫ s, clockSlope ε a₂ h p₂ (s,0)*WK s := by
  have hi := momentum_channel_integrable ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ hε ha₁ ha₂ hh hw₁ hw₂ hb
  have he : (fun s => clockSlope ε a₂ h p₂ (s,0)*WK s)=fun s =>
      (vacuum:ℂ)*(clockSlope ε a₂ h p₂ (s,0)*K 0 s)+
      (mass2:ℂ)*(clockSlope ε a₂ h p₂ (s,0)*K 1 s)/2+
      (quartic:ℂ)*(clockSlope ε a₂ h p₂ (s,0)*K 2 s)/4 := by
    funext s
    rw [clockKernel_channels]
    ring
  have h0 : Integrable (fun s => clockSlope ε a₂ h p₂ (s,0)*K 0 s) := hi 0
  have h1 : Integrable (fun s => clockSlope ε a₂ h p₂ (s,0)*K 1 s) := hi 1
  have h2 : Integrable (fun s => clockSlope ε a₂ h p₂ (s,0)*K 2 s) := hi 2
  have h01 : Integrable (fun s => (vacuum:ℂ)*(clockSlope ε a₂ h p₂ (s,0)*K 0 s)+
      (mass2:ℂ)*(clockSlope ε a₂ h p₂ (s,0)*K 1 s)/2) :=
    (h0.const_mul (vacuum:ℂ)).add ((h1.const_mul (mass2:ℂ)).div_const 2)
  rw [he,integral_add h01
    ((h2.const_mul (quartic:ℂ)).div_const 4),
    integral_add (h0.const_mul (vacuum:ℂ)) ((h1.const_mul (mass2:ℂ)).div_const 2)]
  simp only [integral_div,integral_const_mul]
  have e0 := momentum_channel_pair ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ hε ha₁ ha₂ hh hw₁ hw₂ hb 0
  change inner ℂ (U₁ 7) (V₂ 7)=(∫ s, clockSlope ε a₂ h p₂ (s,0)*K 0 s) at e0
  have e1 := momentum_channel_pair ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ hε ha₁ ha₂ hh hw₁ hw₂ hb 1
  change inner ℂ (U₁ 5) (V₂ 5)=(∫ s, clockSlope ε a₂ h p₂ (s,0)*K 1 s) at e1
  have e2 := momentum_channel_pair ε h a₁ a₂ w₁ w₂ p₁ p₂ C₁ C₂ b₁ b₂ P₁ P₂ hε ha₁ ha₂ hh hw₁ hw₂ hb 2
  change inner ℂ (U₁ 6) (V₂ 6)=(∫ s, clockSlope ε a₂ h p₂ (s,0)*K 2 s) at e2
  rw [← e0,← e1,← e2]

#print axioms channel_integrable
#print axioms momentum_channel_integrable
#print axioms channel_pair
#print axioms momentum_channel_pair
#print axioms clockKernel_integrable
#print axioms momentumClockKernel_integrable
#print axioms ordered_pair_clock_kernel
#print axioms momentum_pair_clock_kernel
end
end UnifiedTheory.Audit.KFCausalWeightedReciprocalNeutralPhysicalPair
