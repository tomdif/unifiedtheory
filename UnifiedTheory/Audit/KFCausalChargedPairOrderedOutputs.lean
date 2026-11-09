/- Actual ordered outputs of the nonzero paired state. The three
potential-factor representatives agree with the transported quadratic
used in the previous exact transverse sign certificate. -/
import UnifiedTheory.Audit.KFCausalChargedPairDomain
import UnifiedTheory.Audit.KFCausalDirectionalShiftedCoefficients

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalChargedPairOrderedOutputs
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalChargedPairDomain (directions combine combine_coe)
open KFCausalChargedPairCoordinates (pairPolynomial)
open KFCausalDirectionalShiftedCoefficients (shiftedLinear shiftedProfile)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalGaussianResponseDensities (amplitude)
open KFCausalSourcedResponseFactorBridge (index)
open KFCausalClockFloorInvariantTrial (neutralWidth)
open KFCausalChargeGaussianGeometry (groundWidth)

theorem complex_polarization (z : Fin 5 → ℂ) :
    combine (fun i => (∑ j : Fin 5, (directions i j:ℂ)*z j)^2) =
      z 0*z 1-z 2*z 3 := by
  have h0 : (∑ j : Fin 5, (directions 0 j:ℂ)*z j) = z 0+z 1 := by
    simp [directions,Fin.sum_univ_succ]
  have h1 : (∑ j : Fin 5, (directions 1 j:ℂ)*z j) = z 0-z 1 := by
    simp [directions,Fin.sum_univ_succ,sub_eq_add_neg]
  have h2 : (∑ j : Fin 5, (directions 2 j:ℂ)*z j) = z 2+z 3 := by
    simp [directions,Fin.sum_univ_succ]
  have h3 : (∑ j : Fin 5, (directions 3 j:ℂ)*z j) = z 2-z 3 := by
    simp [directions,Fin.sum_univ_succ,sub_eq_add_neg]
  simp only [combine,smul_eq_mul,h0,h1,h2,h3]
  ring

theorem shifted_polarization (r : ℂ) (q : Transverse) :
    combine (fun i => (shiftedLinear (directions i) r q)^2) = r^2*(pairPolynomial q:ℂ) :=
  (complex_polarization (KFCausalRelativeGaussianDifferential.position r q)).trans
    (KFCausalChargedPairCoordinates.shifted_pair r q)

def pairedShifted (ε a h : ℝ) (l : Transverse →L[ℝ] ℝ) (n : Fin 3)
    (x : Configuration) : ℂ :=
  (scale ε (-h/2) x.1)^2*(pairPolynomial x.2:ℂ)*
    amplitude ε a (groundWidth h) (neutralWidth h) 0 (-h/2) 0 1 l n x

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (n : Fin 3)

theorem output_coe :
    KFCausalChargedPairDomain.output ε a h hε ha hh hb v l (index n) =ᵐ[volume]
      pairedShifted ε a h l n := by
  have he := combine_coe
    (fun i => KFCausalDirectionalGaussianDomain.output ε a h hε ha hh 1 0 (directions i) 2 hb v l (index n))
    (fun i => shiftedProfile ε a (groundWidth h) (neutralWidth h) 0 (-h/2) 1 (directions i) 2 l n)
    (fun i => KFCausalDirectionalShiftedCoefficients.output_coe
      ε a h hε ha hh 1 0 (directions i) 2 hb v l n)
  filter_upwards [he] with x hx
  change (combine _ : Hilbert) x = _
  rw [hx]
  have hp := shifted_polarization (scale ε (-h/2) x.1) x.2
  simp only [shiftedProfile,combine,smul_eq_mul] at hp ⊢
  unfold pairedShifted
  rw [← hp]
  ring

include hε ha hh hb v in
theorem pairedShifted_memLp : MemLp (pairedShifted ε a h l n) 2 volume :=
  (Lp.memLp (KFCausalChargedPairDomain.output ε a h hε ha hh hb v l (index n))).ae_eq
    (output_coe ε a h hε ha hh hb v l n)

include hε hb in
theorem pairedShifted_continuous : Continuous (pairedShifted ε a h l n) := by
  have hr := (KFCausalClockFloorRelativeShift.scale_smooth ε (-h/2) hε
    (KFCausalClockFloorShiftedOutput.shift_bound ε h hb)).continuous.comp
      (continuous_fst : Continuous (fun x : Configuration => x.1))
  have hA := KFCausalDirectionalShiftedCoefficients.amplitude_continuous
    ε a (groundWidth h) (neutralWidth h) 0 (-h/2) hε
      (KFCausalClockFloorShiftedOutput.shift_bound ε h hb) 1 l n
  unfold pairedShifted pairPolynomial
  fun_prop

#print axioms complex_polarization
#print axioms shifted_polarization
#print axioms output_coe
#print axioms pairedShifted_memLp
#print axioms pairedShifted_continuous
end
end UnifiedTheory.Audit.KFCausalChargedPairOrderedOutputs
