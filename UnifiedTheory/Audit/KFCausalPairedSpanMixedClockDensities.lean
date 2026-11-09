/- L2 and L1 estimates for actual independently clocked shifted packets.
Directional source outputs supply all three potential factors and their
pure-clock momentum densities, for arbitrary real frequencies. -/
import UnifiedTheory.Audit.KFCausalChargedPairOrderedMomentumDensity
import UnifiedTheory.Audit.KFCausalPairedSpanMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalPairedSpanMixedClockDensities
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalPairedSpanMoments (Coefficients)
open KFCausalDirectionalShiftedCoefficients (shiftedProfile)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalSourcedResponseFactorBridge (index)
open KFCausalChargedPairDomain (directions combine)
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalClockFloorInvariantTrial (neutralWidth)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalChargedPairCoordinates (pairPolynomial)
open KFCausalGaussianResponseDensities (amplitude)
open KFCausalClockResponseTransport (weakSlope)
open KFCausalPolynomialOrderedMomentumDensity (clockSlope)

def centered (ε a h p : ℝ) (n : Fin 3) : Configuration → ℂ :=
  amplitude ε a (groundWidth h) (neutralWidth h) p (-h/2) 0 1 pointField n
def paired (ε a h p : ℝ) (n : Fin 3) (x : Configuration) : ℂ :=
  (scale ε (-h/2) x.1)^2*(pairPolynomial x.2:ℂ)*centered ε a h p n x
def shifted (ε a b h p q : ℝ) (c : Coefficients) (n : Fin 3) (x : Configuration) : ℂ :=
  c.1*centered ε a h p n x+c.2*paired ε b h q n x
def weakShifted (ε a b h p q : ℝ) (c : Coefficients) (n : Fin 3) (x : Configuration) : ℂ :=
  c.1*(weakSlope ε a p (-h/2) x.1*centered ε a h p n x)+
    c.2*(weakSlope ε b q (-h/2) x.1*paired ε b h q n x)
def energyDensity (ε a b h p q : ℝ) (c : Coefficients) (x : Configuration) : ℝ :=
  ‖shifted ε a b h p q c 0 x‖^2+‖shifted ε a b h p q c 1 x‖^2/2+
    ‖shifted ε a b h p q c 2 x‖^2/4
def responseDensity (ε a b h p q : ℝ) (c : Coefficients) (n : Fin 3)
    (x : Configuration) : ℝ :=
  2*(conj (shifted ε a b h p q c n x)*weakShifted ε a b h p q c n x).re
def potentialDensity (ε a b h p q : ℝ) (c : Coefficients) (x : Configuration) : ℝ :=
  responseDensity ε a b h p q c 0 x+responseDensity ε a b h p q c 1 x/2+
    responseDensity ε a b h p q c 2 x/4

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3)

include hε ha hh hb in
theorem directional_memLp (p : ℝ) (d : Transverse) (k : ℕ) (n : Fin 3) :
    MemLp (shiftedProfile ε a (groundWidth h) (neutralWidth h) p (-h/2) 1 d k pointField n)
      2 volume :=
  (Lp.memLp (KFCausalDirectionalGaussianDomain.output ε a h hε ha hh 1 p d k hb
    modelDirections pointField (index n))).ae_eq
      (KFCausalDirectionalShiftedCoefficients.output_coe ε a h hε ha hh 1 p d k hb
        modelDirections pointField n)

include hε ha hh hb in
theorem directional_weak_memLp (p : ℝ) (d : Transverse) (k : ℕ) (n : Fin 3) :
    MemLp (fun x => weakSlope ε a p (-h/2) x.1*
      shiftedProfile ε a (groundWidth h) (neutralWidth h) p (-h/2) 1 d k pointField n x)
      2 volume := by
  have hm : MemLp (fun x => clockSlope ε a h p x*
      shiftedProfile ε a (groundWidth h) (neutralWidth h) p (-h/2) 1 d k pointField n x)
      2 volume := by
    apply (Lp.memLp (KFCausalDirectionalClockMomentum.factor ε a h hε ha hh p d 1 hb k
      modelDirections pointField (index n))).ae_eq
    filter_upwards [KFCausalChargedPairOrderedMomentumDensity.directional_relation
      ε a h hε ha hh hb 1 p d k modelDirections pointField n,
      KFCausalDirectionalShiftedCoefficients.output_coe ε a h hε ha hh 1 p d k hb
        modelDirections pointField n] with x hx hu
    rw [hx,hu]
  have hz : -Complex.I*(h:ℂ) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr hh)
  convert hm.const_smul (-Complex.I*(h:ℂ))⁻¹ using 1
  funext x
  simp only [Pi.smul_apply,smul_eq_mul,clockSlope,← mul_assoc,inv_mul_cancel₀ hz,one_mul]

theorem paired_polarization (p : ℝ) (n : Fin 3) (x : Configuration) :
    paired ε a h p n x = combine (fun i =>
      shiftedProfile ε a (groundWidth h) (neutralWidth h) p (-h/2) 1 (directions i) 2
        pointField n x) := by
  have hp := KFCausalChargedPairOrderedOutputs.shifted_polarization (scale ε (-h/2) x.1) x.2
  simp only [combine,smul_eq_mul] at hp
  unfold paired centered
  rw [← hp]
  simp only [combine,shiftedProfile,smul_eq_mul]
  ring

include hε ha hh hb in
theorem centered_memLp (p : ℝ) (n : Fin 3) : MemLp (centered ε a h p n) 2 volume := by
  convert directional_memLp ε a h hε ha hh hb p 0 0 n using 1
  funext x
  simp only [shiftedProfile,pow_zero,one_mul,centered]

include hε ha hh hb in
theorem centered_weak_memLp (p : ℝ) (n : Fin 3) :
    MemLp (fun x => weakSlope ε a p (-h/2) x.1*centered ε a h p n x) 2 volume := by
  simpa only [shiftedProfile,pow_zero,one_mul,centered] using
    directional_weak_memLp ε a h hε ha hh hb p 0 0 n

include hε ha hh hb in
theorem paired_memLp (p : ℝ) (n : Fin 3) : MemLp (paired ε a h p n) 2 volume := by
  have hi (i : Fin 4) := directional_memLp ε a h hε ha hh hb p (directions i) 2 n
  convert (((hi 0).sub (hi 1)).sub (hi 2)).add (hi 3) |>.const_smul (1/4:ℂ) using 1
  funext x
  exact paired_polarization ε a h p n x

include hε ha hh hb in
theorem paired_weak_memLp (p : ℝ) (n : Fin 3) :
    MemLp (fun x => weakSlope ε a p (-h/2) x.1*paired ε a h p n x) 2 volume := by
  have hi (i : Fin 4) := directional_weak_memLp ε a h hε ha hh hb p (directions i) 2 n
  convert (((hi 0).sub (hi 1)).sub (hi 2)).add (hi 3) |>.const_smul (1/4:ℂ) using 1
  funext x
  rw [paired_polarization ε a h p n x]
  simp only [combine,Pi.smul_apply,Pi.add_apply,Pi.sub_apply,smul_eq_mul]
  ring

include hε ha hh hb in
theorem shifted_memLp (b p q : ℝ) (hbw : 0 < b) (c : Coefficients) (n : Fin 3) :
    MemLp (shifted ε a b h p q c n) 2 volume :=
  ((centered_memLp ε a h hε ha hh hb p n).const_smul c.1).add
    ((paired_memLp ε b h hε hbw hh hb q n).const_smul c.2)

include hε ha hh hb in
theorem weakShifted_memLp (b p q : ℝ) (hbw : 0 < b) (c : Coefficients) (n : Fin 3) :
    MemLp (weakShifted ε a b h p q c n) 2 volume :=
  ((centered_weak_memLp ε a h hε ha hh hb p n).const_smul c.1).add
    ((paired_weak_memLp ε b h hε hbw hh hb q n).const_smul c.2)

include hε ha hh hb in
theorem responseDensity_integrable (b p q : ℝ) (hbw : 0 < b) (c : Coefficients) (n : Fin 3) :
    Integrable (responseDensity ε a b h p q c n) volume := by
  have hi := (shifted_memLp ε a h hε ha hh hb b p q hbw c n).star.integrable_mul
    (weakShifted_memLp ε a h hε ha hh hb b p q hbw c n)
  simpa only [responseDensity,Complex.star_def] using hi.re.const_mul 2

include hε ha hh hb in
theorem energyDensity_integrable (b p q : ℝ) (hbw : 0 < b) (c : Coefficients) :
    Integrable (energyDensity ε a b h p q c) volume := by
  have hi (n : Fin 3) := (shifted_memLp ε a h hε ha hh hb b p q hbw c n).integrable_norm_pow
    (by norm_num : (2:ℕ) ≠ 0)
  exact ((hi 0).add ((hi 1).div_const 2)).add ((hi 2).div_const 4)

include hε ha hh hb in
theorem potentialDensity_integrable (b p q : ℝ) (hbw : 0 < b) (c : Coefficients) :
    Integrable (potentialDensity ε a b h p q c) volume :=
  ((responseDensity_integrable ε a h hε ha hh hb b p q hbw c 0).add
    ((responseDensity_integrable ε a h hε ha hh hb b p q hbw c 1).div_const 2)).add
      ((responseDensity_integrable ε a h hε ha hh hb b p q hbw c 2).div_const 4)

#print axioms directional_memLp
#print axioms directional_weak_memLp
#print axioms paired_polarization
#print axioms centered_memLp
#print axioms centered_weak_memLp
#print axioms paired_memLp
#print axioms paired_weak_memLp
#print axioms shifted_memLp
#print axioms weakShifted_memLp
#print axioms responseDensity_integrable
#print axioms energyDensity_integrable
#print axioms potentialDensity_integrable
end
end UnifiedTheory.Audit.KFCausalPairedSpanMixedClockDensities
