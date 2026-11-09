/- Identify the mixed state's three ordered outputs and actual momentum
outputs with the independently clocked densities already estimated.
Each component keeps its own weak slope before summation. -/
import UnifiedTheory.Audit.KFCausalPairedSpanMixedClockHamiltonian
import UnifiedTheory.Audit.KFCausalPairedSpanMixedClockDensities

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalPairedSpanMixedClockOrderedBridge
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalPairedSpanMoments (Coefficients)
open KFCausalPairedSpanMixedClockDomain
  (output momentumOutput factorEnergy factorRate)
open KFCausalPairedSpanMixedClockHamiltonian (potentialEnergy potentialResponse)
open KFCausalPairedSpanMixedClockDensities
open KFCausalDirectionalShiftedCoefficients (shiftedProfile)
open KFCausalSourcedResponseFactorBridge (index)
open KFCausalChargedPairDomain (directions)
open KFCausalPolynomialOrderedMomentumDensity (clockSlope)
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalClockFloorInvariantTrial (neutralWidth)

theorem centered_output_coe (ε a h p : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (n : Fin 3) :
    KFCausalDirectionalGaussianDomain.output ε a h hε ha hh 1 p 0 0 hb
      modelDirections pointField (index n) =ᵐ[volume] centered ε a h p n := by
  filter_upwards [KFCausalDirectionalShiftedCoefficients.output_coe ε a h hε ha hh
    1 p 0 0 hb modelDirections pointField n] with x hx
  simpa only [shiftedProfile,pow_zero,one_mul,centered] using hx

theorem paired_output_coe (ε a h p : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (n : Fin 3) :
    KFCausalChargedPairFrequencyDomain.output ε a h hε ha hh p hb
      modelDirections pointField (index n) =ᵐ[volume] paired ε a h p n := by
  have he := KFCausalChargedPairDomain.combine_coe
    (fun i => KFCausalDirectionalGaussianDomain.output ε a h hε ha hh 1 p (directions i) 2 hb
      modelDirections pointField (index n))
    (fun i => shiftedProfile ε a (groundWidth h) (neutralWidth h) p (-h/2) 1 (directions i) 2 pointField n)
    (fun i => KFCausalDirectionalShiftedCoefficients.output_coe ε a h hε ha hh 1 p (directions i) 2 hb
      modelDirections pointField n)
  filter_upwards [he] with x hx
  change (KFCausalChargedPairDomain.combine _ : Hilbert) x = _
  rw [hx]
  exact (paired_polarization ε a h p n x).symm

theorem paired_momentum_coe (ε a h p : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (n : Fin 3) :
    KFCausalChargedPairFrequencyDomain.momentumOutput ε a h hε ha hh p hb
      modelDirections pointField (index n) =ᵐ[volume]
        fun x => clockSlope ε a h p x*paired ε a h p n x := by
  have hr := KFCausalChargedPairOrderedMomentumDensity.relation_combine
    (clockSlope ε a h p) (KFCausalPolynomialOrderedMomentumDensity.clockSlope_continuous
      ε a h hε hb p).measurable _ _
    (fun i => KFCausalChargedPairOrderedMomentumDensity.directional_relation
      ε a h hε ha hh hb 1 p (directions i) 2 modelDirections pointField n)
  filter_upwards [hr,paired_output_coe ε a h p hε ha hh hb n] with x hm hu
  change (KFCausalChargedPairDomain.combine _ : Hilbert) x = _
  rw [hm]
  change clockSlope ε a h p x*
    (KFCausalChargedPairFrequencyDomain.output ε a h hε ha hh p hb
      modelDirections pointField (index n)) x = _
  rw [hu]

theorem scalar_response (h : ℝ) (hh : h ≠ 0) (z w : ℂ) :
    (-2/h)*(conj z*((-Complex.I*(h:ℂ))*w)).im = 2*(conj z*w).re := by
  have he : conj z*((-Complex.I*(h:ℂ))*w) = (-Complex.I*(h:ℂ))*(conj z*w) := by ring
  rw [he]
  simp only [Complex.mul_im,Complex.mul_re,Complex.neg_re,Complex.neg_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
    neg_zero,zero_mul,zero_add,sub_zero,mul_zero]
  field_simp [hh]

variable (ε a b h p q : ℝ) (hε : 0 < ε) (ha : 0 < a) (hbw : 0 < b) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (c : Coefficients)

theorem output_coe (n : Fin 3) :
    output ε a b h p q hε ha hbw hh hb c (index n) =ᵐ[volume] shifted ε a b h p q c n :=
  KFCausalPairedSpanDomain.combine_coe c _ _ _ _
    (centered_output_coe ε a h p hε ha hh hb n)
    (paired_output_coe ε b h q hε hbw hh hb n)

theorem momentum_coe (n : Fin 3) :
    momentumOutput ε a b h p q hε ha hbw hh hb c (index n) =ᵐ[volume]
      fun x => (-Complex.I*(h:ℂ))*weakShifted ε a b h p q c n x := by
  have h0 : KFCausalDirectionalClockMomentum.factor ε a h hε ha hh p 0 1 hb 0
      modelDirections pointField (index n) =ᵐ[volume]
        fun x => clockSlope ε a h p x*centered ε a h p n x := by
    filter_upwards [KFCausalChargedPairOrderedMomentumDensity.directional_relation
      ε a h hε ha hh hb 1 p 0 0 modelDirections pointField n,
      centered_output_coe ε a h p hε ha hh hb n] with x hm hu
    rw [hm,hu]
  have he := KFCausalPairedSpanDomain.combine_coe c _ _ _ _ h0
    (paired_momentum_coe ε b h q hε hbw hh hb n)
  filter_upwards [he] with x hx
  change (KFCausalPairedSpanDomain.combine c _ _) x = _
  rw [hx]
  unfold clockSlope weakShifted
  ring

def pairDensity (n : Fin 3) (x : Configuration) : ℂ :=
  conj (shifted ε a b h p q c n x)*((-Complex.I*(h:ℂ))*weakShifted ε a b h p q c n x)

include hε ha hbw hh hb in
theorem pairDensity_integrable (n : Fin 3) : Integrable (pairDensity ε a b h p q c n) volume := by
  have hi := (shifted_memLp ε a h hε ha hh hb b p q hbw c n).star.integrable_mul
    ((weakShifted_memLp ε a h hε ha hh hb b p q hbw c n).const_smul (-Complex.I*(h:ℂ)))
  simpa only [pairDensity,Complex.star_def,Pi.smul_apply,smul_eq_mul] using hi

theorem factorEnergy_integral (n : Fin 3) :
    factorEnergy ε a b h p q hε ha hbw hh hb c (index n) =
      ∫ x, ‖shifted ε a b h p q c n x‖^2 := by
  rw [factorEnergy,KFCausalAveragedEnergyGraph.l2_norm_square volume]
  apply integral_congr_ae
  filter_upwards [output_coe ε a b h p q hε ha hbw hh hb c n] with x hx
  rw [hx]

theorem factorRate_integral (n : Fin 3) :
    factorRate ε a b h p q hε ha hbw hh hb c (index n) =
      ∫ x, responseDensity ε a b h p q c n x := by
  have hi : inner ℂ (output ε a b h p q hε ha hbw hh hb c (index n))
      (momentumOutput ε a b h p q hε ha hbw hh hb c (index n)) =
        ∫ x, pairDensity ε a b h p q c n x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [output_coe ε a b h p q hε ha hbw hh hb c n,
      momentum_coe ε a b h p q hε ha hbw hh hb c n] with x hu hm
    simp only [hu,hm,RCLike.inner_apply,pairDensity]
    ring
  have him : (∫ x, pairDensity ε a b h p q c n x).im =
      ∫ x, (pairDensity ε a b h p q c n x).im := by
    simpa only [RCLike.im_eq_complex_im] using
      (integral_im (pairDensity_integrable ε a b h p q hε ha hbw hh hb c n)).symm
  rw [factorRate,hi,him,← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x =>
    scalar_response h hh (shifted ε a b h p q c n x) (weakShifted ε a b h p q c n x)))

theorem potentialEnergy_integral :
    potentialEnergy ε a b h p q hε ha hbw hh hb c =
      ∫ x, energyDensity ε a b h p q c x := by
  have h0 := factorEnergy_integral ε a b h p q hε ha hbw hh hb c 0
  have h1 := factorEnergy_integral ε a b h p q hε ha hbw hh hb c 1
  have h2 := factorEnergy_integral ε a b h p q hε ha hbw hh hb c 2
  change factorEnergy ε a b h p q hε ha hbw hh hb c 7 = _ at h0
  change factorEnergy ε a b h p q hε ha hbw hh hb c 5 = _ at h1
  change factorEnergy ε a b h p q hε ha hbw hh hb c 6 = _ at h2
  have hi (n : Fin 3) := (shifted_memLp ε a h hε ha hh hb b p q hbw c n).integrable_norm_pow
    (by norm_num : (2:ℕ) ≠ 0)
  have h01 : Integrable (fun x => ‖shifted ε a b h p q c 0 x‖^2+
      ‖shifted ε a b h p q c 1 x‖^2/2) volume := (hi 0).add ((hi 1).div_const 2)
  unfold potentialEnergy energyDensity
  rw [integral_add h01 ((hi 2).div_const 4),integral_add (hi 0) ((hi 1).div_const 2),
    integral_div,integral_div,← h0,← h1,← h2]

theorem potentialResponse_integral :
    potentialResponse ε a b h p q hε ha hbw hh hb c =
      ∫ x, potentialDensity ε a b h p q c x := by
  have h0 := factorRate_integral ε a b h p q hε ha hbw hh hb c 0
  have h1 := factorRate_integral ε a b h p q hε ha hbw hh hb c 1
  have h2 := factorRate_integral ε a b h p q hε ha hbw hh hb c 2
  change factorRate ε a b h p q hε ha hbw hh hb c 7 = _ at h0
  change factorRate ε a b h p q hε ha hbw hh hb c 5 = _ at h1
  change factorRate ε a b h p q hε ha hbw hh hb c 6 = _ at h2
  have hi (n : Fin 3) := responseDensity_integrable ε a h hε ha hh hb b p q hbw c n
  have h01 : Integrable (fun x => responseDensity ε a b h p q c 0 x+
      responseDensity ε a b h p q c 1 x/2) volume := (hi 0).add ((hi 1).div_const 2)
  unfold potentialResponse potentialDensity
  rw [integral_add h01 ((hi 2).div_const 4),integral_add (hi 0) ((hi 1).div_const 2),
    integral_div,integral_div,← h0,← h1,← h2]

#print axioms centered_output_coe
#print axioms paired_output_coe
#print axioms paired_momentum_coe
#print axioms scalar_response
#print axioms output_coe
#print axioms momentum_coe
#print axioms pairDensity_integrable
#print axioms factorEnergy_integral
#print axioms factorRate_integral
#print axioms potentialEnergy_integral
#print axioms potentialResponse_integral
end
end UnifiedTheory.Audit.KFCausalPairedSpanMixedClockOrderedBridge
