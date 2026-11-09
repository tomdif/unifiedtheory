/- The three potential factors of the centered/paired superposition and
its actual momentum. Every coefficient cross term remains inside the
absolute square or inner product; integrability follows from actual L2 outputs. -/
import UnifiedTheory.Audit.KFCausalPairedSpanDomain
import UnifiedTheory.Audit.KFCausalChargedPairPotentialResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalPairedSpanOrderedOutputs
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalPairedSpanMoments (Coefficients)
open KFCausalPairedSpanDomain (combine combine_coe output momentumOutput factorEnergy factorRate)
open KFCausalSourcedResponseFactorBridge (index)
open KFCausalGaussianResponseDensities (amplitude)
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalClockFloorInvariantTrial (neutralWidth)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalChargedPairCoordinates (pairPolynomial)
open KFCausalPolynomialOrderedMomentumDensity (clockSlope clockSlope_continuous)
open KFCausalUnboundedMultiplierIntegral (relation relation_iff_bounded)
open KFCausalClockResponseTransport (weakSlope)

def shifted (ε a h : ℝ) (c : Coefficients) (n : Fin 3) (x : Configuration) : ℂ :=
  (c.1+c.2*(scale ε (-h/2) x.1)^2*(pairPolynomial x.2:ℂ))*
    amplitude ε a (groundWidth h) (neutralWidth h) 0 (-h/2) 0 1 pointField n x

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3)

theorem output_coe (c : Coefficients) (n : Fin 3) :
    output ε a h hε ha hh hb c (index n) =ᵐ[volume] shifted ε a h c n := by
  have h0 : KFCausalDirectionalGaussianDomain.output ε a h hε ha hh 1 0 0 0 hb
      modelDirections pointField (index n) =ᵐ[volume]
        amplitude ε a (groundWidth h) (neutralWidth h) 0 (-h/2) 0 1 pointField n := by
    filter_upwards [KFCausalDirectionalShiftedCoefficients.output_coe ε a h hε ha hh
      1 0 0 0 hb modelDirections pointField n] with x hx
    simpa only [KFCausalDirectionalShiftedCoefficients.shiftedProfile, pow_zero, one_mul] using hx
  have hs := combine_coe c _ _ _ _ h0
    (KFCausalChargedPairOrderedOutputs.output_coe ε a h hε ha hh hb modelDirections pointField n)
  filter_upwards [hs] with x hx
  change (combine c _ _) x = _
  rw [hx]
  unfold shifted KFCausalChargedPairOrderedOutputs.pairedShifted
  ring

theorem momentum_relation (c : Coefficients) (n : Fin 3) :
    relation (clockSlope ε a h 0)
      (output ε a h hε ha hh hb c (index n)) (momentumOutput ε a h hε ha hh hb c (index n)) := by
  have hm := (clockSlope_continuous ε a h hε hb 0).measurable
  have h0 := (relation_iff_bounded _ hm _ _).mp
    (KFCausalChargedPairOrderedMomentumDensity.directional_relation ε a h hε ha hh hb
      1 0 0 0 modelDirections pointField n)
  have h1 := (relation_iff_bounded _ hm _ _).mp
    (KFCausalChargedPairOrderedMomentumDensity.paired_relation ε a h hε ha hh hb
      modelDirections pointField n)
  apply (relation_iff_bounded _ hm _ _).mpr
  simp only [output, momentumOutput, combine, map_add, map_smul, h0, h1]

theorem momentum_coe (c : Coefficients) (n : Fin 3) :
    momentumOutput ε a h hε ha hh hb c (index n) =ᵐ[volume]
      fun x => clockSlope ε a h 0 x*shifted ε a h c n x := by
  filter_upwards [momentum_relation ε a h hε ha hh hb c n,
    output_coe ε a h hε ha hh hb c n] with x hm hu
  rw [hm,hu]

include hε ha hh hb in
theorem shifted_memLp (c : Coefficients) (n : Fin 3) : MemLp (shifted ε a h c n) 2 volume :=
  (Lp.memLp (output ε a h hε ha hh hb c (index n))).ae_eq (output_coe ε a h hε ha hh hb c n)

include hε ha hh hb in
theorem momentum_density_memLp (c : Coefficients) (n : Fin 3) :
    MemLp (fun x => clockSlope ε a h 0 x*shifted ε a h c n x) 2 volume :=
  (Lp.memLp (momentumOutput ε a h hε ha hh hb c (index n))).ae_eq
    (momentum_coe ε a h hε ha hh hb c n)

def pairDensity (c : Coefficients) (n : Fin 3) (x : Configuration) : ℂ :=
  conj (shifted ε a h c n x)*(clockSlope ε a h 0 x*shifted ε a h c n x)
def responseDensity (c : Coefficients) (n : Fin 3) (x : Configuration) : ℝ :=
  2*(weakSlope ε a 0 (-h/2) x.1).re*‖shifted ε a h c n x‖^2

include hε ha hh hb in
theorem pairDensity_integrable (c : Coefficients) (n : Fin 3) :
    Integrable (pairDensity ε a h c n) volume := by
  have hi := (shifted_memLp ε a h hε ha hh hb c n).star.integrable_mul
    (momentum_density_memLp ε a h hε ha hh hb c n)
  simpa only [pairDensity, Complex.star_def] using hi

include hε ha hh hb in
theorem responseDensity_integrable (c : Coefficients) (n : Fin 3) :
    Integrable (responseDensity ε a h c n) volume :=
  ((pairDensity_integrable ε a h hε ha hh hb c n).im.const_mul (-2/h)).congr
    (Filter.Eventually.of_forall (fun x =>
      KFCausalChargedPairPotentialResponse.scalar_response_identity h hh
        (shifted ε a h c n x) (weakSlope ε a 0 (-h/2) x.1)))

theorem factorEnergy_integral (c : Coefficients) (n : Fin 3) :
    factorEnergy ε a h hε ha hh hb c (index n) = ∫ x, ‖shifted ε a h c n x‖^2 := by
  rw [factorEnergy, KFCausalAveragedEnergyGraph.l2_norm_square volume]
  apply integral_congr_ae
  filter_upwards [output_coe ε a h hε ha hh hb c n] with x hx
  rw [hx]

theorem factorRate_integral (c : Coefficients) (n : Fin 3) :
    factorRate ε a h hε ha hh hb c (index n) = ∫ x, responseDensity ε a h c n x := by
  have hi : inner ℂ (output ε a h hε ha hh hb c (index n))
      (momentumOutput ε a h hε ha hh hb c (index n)) = ∫ x, pairDensity ε a h c n x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [output_coe ε a h hε ha hh hb c n,
      momentum_coe ε a h hε ha hh hb c n] with x hu hm
    simp only [hu,hm,RCLike.inner_apply,pairDensity]
    ring
  have him : (∫ x, pairDensity ε a h c n x).im = ∫ x, (pairDensity ε a h c n x).im := by
    simpa only [RCLike.im_eq_complex_im] using
      (integral_im (pairDensity_integrable ε a h hε ha hh hb c n)).symm
  rw [factorRate,hi,him,← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x =>
    KFCausalChargedPairPotentialResponse.scalar_response_identity h hh
      (shifted ε a h c n x) (weakSlope ε a 0 (-h/2) x.1)))

#print axioms output_coe
#print axioms momentum_relation
#print axioms momentum_coe
#print axioms shifted_memLp
#print axioms momentum_density_memLp
#print axioms pairDensity_integrable
#print axioms responseDensity_integrable
#print axioms factorEnergy_integral
#print axioms factorRate_integral
end
end UnifiedTheory.Audit.KFCausalPairedSpanOrderedOutputs
