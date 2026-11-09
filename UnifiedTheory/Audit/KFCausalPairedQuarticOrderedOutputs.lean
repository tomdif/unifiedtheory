/- The corrected quartic's ordered outputs use its actual complex shift.
Their clock-momentum representatives follow from the established
unbounded multiplier relation on directional source outputs. -/
import UnifiedTheory.Audit.KFCausalPairedQuarticDomain
import UnifiedTheory.Audit.KFCausalChargedPairOrderedMomentumDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace UnifiedTheory.Audit.KFCausalPairedQuarticOrderedOutputs
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalPairedQuarticPolarization (directions degrees coefficients)
open KFCausalQuarticChargeProfiles (chargedRadius)
open KFCausalChargedPairCoordinates (pairPolynomial)
open KFCausalDirectionalShiftedCoefficients (shiftedLinear shiftedProfile)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalGaussianResponseDensities (amplitude)
open KFCausalSourcedResponseFactorBridge (index)
open KFCausalClockFloorInvariantTrial (neutralWidth)
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalPairedQuarticDomain (output momentumOutput)
open KFCausalFiniteLpRepresentatives (sum_coe)
open KFCausalUnboundedMultiplierIntegral (relation relation_iff_bounded)
open KFCausalPolynomialOrderedMomentumDensity (clockSlope clockSlope_continuous)

def shiftedPolynomial (α : ℝ) (r : ℂ) (q : Transverse) : ℂ :=
  r^4*(pairPolynomial q:ℂ)^2-r^2*(chargedRadius q:ℂ)/(4*(α:ℂ))+1/(8*(α:ℂ)^2)

theorem complex_polarization (α : ℝ) (z : Fin 5 → ℂ) :
    (∑ i, coefficients α i*(∑ j : Fin 5, (directions i j:ℂ)*z j)^(degrees i)) =
      (z 0*z 1-z 2*z 3)^2-(z 0^2+z 1^2+z 2^2+z 3^2)/(4*(α:ℂ))+1/(8*(α:ℂ)^2) := by
  simp [coefficients,directions,degrees,Fin.sum_univ_succ]
  ring

theorem shifted_polarization (α : ℝ) (r : ℂ) (q : Transverse) :
    (∑ i, coefficients α i*(shiftedLinear (directions i) r q)^(degrees i)) =
      shiftedPolynomial α r q := by
  unfold shiftedLinear
  rw [complex_polarization]
  simp only [KFCausalRelativeGaussianDifferential.position,shiftedPolynomial,pairPolynomial,chargedRadius]
  push_cast
  ring

def shifted (ε a h : ℝ) (l : Transverse →L[ℝ] ℝ) (n : Fin 3) (x : Configuration) : ℂ :=
  shiftedPolynomial (groundWidth h) (scale ε (-h/2) x.1) x.2*
    amplitude ε a (groundWidth h) (neutralWidth h) 0 (-h/2) 0 1 l n x

theorem shiftedProfile_factorization (ε a α β y : ℝ) (C : ℂ) (d : Transverse)
    (k : ℕ) (l : Transverse →L[ℝ] ℝ) (n : Fin 3) (x : Configuration) :
    shiftedProfile ε a α β 0 y C d k l n x =
      (C*(shiftedLinear d (scale ε y x.1) x.2)^k)*amplitude ε a α β 0 y 0 1 l n x := by
  simp only [shiftedProfile,amplitude,KFCausalRelativeGaussianDifferential.profile,one_mul]
  ring

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (n : Fin 3)

theorem output_coe :
    output ε a h hε ha hh hb v l (index n) =ᵐ[volume] shifted ε a h l n := by
  have hs := sum_coe volume Finset.univ (fun i : Fin 21 =>
    KFCausalDirectionalGaussianDomain.output ε a h hε ha hh
      (coefficients (groundWidth h) i) 0 (directions i) (degrees i) hb v l (index n))
  have hi := ae_all_iff.mpr (fun i : Fin 21 =>
    KFCausalDirectionalShiftedCoefficients.output_coe ε a h hε ha hh
      (coefficients (groundWidth h) i) 0 (directions i) (degrees i) hb v l n)
  filter_upwards [hs,hi] with x hx hy
  change (∑ i : Fin 21, KFCausalDirectionalGaussianDomain.output ε a h hε ha hh
    (coefficients (groundWidth h) i) 0 (directions i) (degrees i) hb v l (index n) : Hilbert) x = _
  rw [hx]
  simp_rw [hy,shiftedProfile_factorization]
  rw [← Finset.sum_mul,shifted_polarization]
  rfl

theorem momentum_relation :
    relation (clockSlope ε a h 0)
      (output ε a h hε ha hh hb v l (index n))
      (momentumOutput ε a h hε ha hh hb v l (index n)) := by
  have hm := (clockSlope_continuous ε a h hε hb 0).measurable
  have hi (i : Fin 21) := (relation_iff_bounded _ hm _ _).mp
    (KFCausalChargedPairOrderedMomentumDensity.directional_relation ε a h hε ha hh hb
      (coefficients (groundWidth h) i) 0 (directions i) (degrees i) v l n)
  apply (relation_iff_bounded _ hm _ _).mpr
  simp only [output,momentumOutput,map_sum,hi]

theorem momentum_coe :
    momentumOutput ε a h hε ha hh hb v l (index n) =ᵐ[volume]
      fun x => clockSlope ε a h 0 x*shifted ε a h l n x := by
  filter_upwards [momentum_relation ε a h hε ha hh hb v l n,
    output_coe ε a h hε ha hh hb v l n] with x hm hu
  rw [hm,hu]

include hε ha hh hb v in
theorem shifted_memLp : MemLp (shifted ε a h l n) 2 volume :=
  (Lp.memLp (output ε a h hε ha hh hb v l (index n))).ae_eq
    (output_coe ε a h hε ha hh hb v l n)

include hε ha hh hb v in
theorem momentum_density_memLp :
    MemLp (fun x => clockSlope ε a h 0 x*shifted ε a h l n x) 2 volume :=
  (Lp.memLp (momentumOutput ε a h hε ha hh hb v l (index n))).ae_eq
    (momentum_coe ε a h hε ha hh hb v l n)

#print axioms complex_polarization
#print axioms shifted_polarization
#print axioms shiftedProfile_factorization
#print axioms output_coe
#print axioms momentum_relation
#print axioms momentum_coe
#print axioms shifted_memLp
#print axioms momentum_density_memLp
end
end UnifiedTheory.Audit.KFCausalPairedQuarticOrderedOutputs
