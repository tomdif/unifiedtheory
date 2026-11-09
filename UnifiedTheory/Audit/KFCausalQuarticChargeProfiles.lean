/- The corrected quartic profile is invariant in actual charge coordinates.
The uncorrected square has a nonzero quarter-turn defect. -/
import UnifiedTheory.Audit.KFCausalQuarticTensorStates
import UnifiedTheory.Audit.KFCausalChargeZeroSwapWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace UnifiedTheory.Audit.KFCausalQuarticChargeProfiles
noncomputable section
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalEuclideanProductCoordinates (Joint split split_fst split_snd)
open KFCausalQuarticChargeAlgebra
open KFCausalQuarticTensorStates (configurationDensity configurationMonomial mixedDensity)
open KFCausalChargeGaussianIdentities (configurationProfile mixed_profile_identity)
open KFCausalChargeGaussianGeometry (radius radius_coordinates radius_flow profile dilate_flow)
open KFCausalChargeZeroSwapWitness (imbalance imbalanceRaw imbalance_flow)
open KFCausalNormalizedChargeFlow (dilate flowEquiv)
open KFCausalPairedModeCoordinates (scale scale_square)
open KFCausalChargedPairCoordinates (pairPolynomial)

def chargedRadius (q : Transverse) : ℝ := (q 0)^2+(q 1)^2+(q 2)^2+(q 3)^2
def quarticPolynomial (α : ℝ) (q : Transverse) : ℝ :=
  (pairPolynomial q)^2-chargedRadius q/(4*α)+1/(8*α^2)
def frequencyRadius (c : ℝ) (x : Joint 2 4) : ℝ :=
  c^2*((x (.inl 0))^2+(x (.inl 1))^2)
def correctedWeight (α c : ℝ) (x : Joint 2 4) : ℝ :=
  (imbalance c x)^2/4-radius c x/(4*α)+1/(8*α^2)
def squareWeight (α c : ℝ) (x : Joint 2 4) : ℝ :=
  (imbalance c x)^2/4-frequencyRadius c x/(2*α)+1/(4*α^2)

theorem configuration_corrected (α β : ℝ) (g : ℝ → ℂ) (x : Configuration) :
    configurationDensity α β g (correctedCoefficients α) x =
      (quarticPolynomial α x.2:ℂ)*configurationProfile α β g x := by
  unfold configurationDensity configurationMonomial correctedCoefficients
  rw [polynomial_identity]
  have hs : (scale:ℂ)^2 = (1/2:ℂ) := by
    rw [← Complex.ofReal_pow,scale_square]
    norm_num
  have hs4 : (scale:ℂ)^4 = (1/4:ℂ) := by
    calc
      _ = ((scale:ℂ)^2)^2 := by ring
      _ = _ := by rw [hs]; norm_num
  unfold quarticPolynomial chargedRadius pairPolynomial
  push_cast
  ring_nf
  simp only [hs,hs4]
  ring

theorem configuration_square (α β : ℝ) (g : ℝ → ℂ) (x : Configuration) :
    configurationDensity α β g squareCoefficients x =
      ((pairPolynomial x.2)^2:ℝ)*configurationProfile α β g x := by
  unfold configurationDensity configurationMonomial squareCoefficients
  rw [polynomial_identity]
  have hs : (scale:ℂ)^2 = (1/2:ℂ) := by
    rw [← Complex.ofReal_pow,scale_square]
    norm_num
  have hs4 : (scale:ℂ)^4 = (1/4:ℂ) := by
    calc
      _ = ((scale:ℂ)^2)^2 := by ring
      _ = _ := by rw [hs]; norm_num
  unfold pairPolynomial
  push_cast
  ring_nf
  rw [hs4]
  ring

theorem ratio_matching (α c : ℝ) (hα : 0 < α) (hmatch : Real.pi^2/α = α*c^2) :
    ratio α = (c:ℂ)^2 := by
  have he := (div_eq_iff hα.ne').mp hmatch
  have hr : Real.pi^2/α^2 = c^2 := by
    apply (div_eq_iff (pow_ne_zero 2 hα.ne')).mpr
    nlinarith only [he]
  unfold ratio
  exact_mod_cast hr

theorem mixed_corrected (α β c : ℝ) (hα : 0 < α) (hmatch : Real.pi^2/α = α*c^2)
    (g : ℝ → ℂ) (x : Joint 2 4) :
    mixedDensity α β g (correctedCoefficients α) x =
      (correctedWeight α c x:ℂ)*(((Real.pi/α:ℝ):ℂ)*profile α β c g x) := by
  unfold mixedDensity
  rw [corrected_identity α hα,mixed_profile_identity α β c hα hmatch g x,
    ratio_matching α c hα hmatch]
  unfold correctedWeight imbalance imbalanceRaw dilate
  rw [radius_coordinates]
  simp only [split_fst,split_snd]
  push_cast
  ring

theorem mixed_square (α β c : ℝ) (hα : 0 < α) (hmatch : Real.pi^2/α = α*c^2)
    (g : ℝ → ℂ) (x : Joint 2 4) :
    mixedDensity α β g squareCoefficients x =
      (squareWeight α c x:ℂ)*(((Real.pi/α:ℝ):ℂ)*profile α β c g x) := by
  unfold mixedDensity
  rw [square_identity α hα,mixed_profile_identity α β c hα hmatch g x,
    ratio_matching α c hα hmatch]
  unfold squareWeight frequencyRadius imbalance imbalanceRaw dilate
  simp only [split_fst,split_snd]
  push_cast
  ring

theorem correctedWeight_flow (α c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Joint 2 4) :
    correctedWeight α c (flowEquiv c hc θ x) = correctedWeight α c x := by
  simp only [correctedWeight,imbalance_flow,radius_flow]

theorem correctedWeight_continuous (α c : ℝ) : Continuous (correctedWeight α c) := by
  unfold correctedWeight
  simp only [radius_coordinates]
  unfold imbalance imbalanceRaw dilate
  fun_prop

theorem squareWeight_continuous (α c : ℝ) : Continuous (squareWeight α c) := by
  unfold squareWeight frequencyRadius imbalance imbalanceRaw dilate
  fun_prop

theorem frequencyRadius_quarter_turn (c : ℝ) (hc : c ≠ 0) (x : Joint 2 4) :
    frequencyRadius c (flowEquiv c hc (Real.pi/2) x) =
      (x (.inr 1))^2+(x (.inr 2))^2 := by
  calc
    _ = (dilate c (flowEquiv c hc (Real.pi/2) x) (.inl 0))^2+
        (dilate c (flowEquiv c hc (Real.pi/2) x) (.inl 1))^2 := by
      simp only [frequencyRadius,dilate]
      ring
    _ = (KFCausalPairedRotation.rotate (Real.pi/2) (dilate c x) (.inl 0))^2+
        (KFCausalPairedRotation.rotate (Real.pi/2) (dilate c x) (.inl 1))^2 := by
      rw [dilate_flow]
    _ = _ := by simp [KFCausalPairedRotation.rotate,dilate]

theorem squareWeight_quarter_defect (α c : ℝ) (hc : c ≠ 0) (x : Joint 2 4) :
    squareWeight α c (flowEquiv c hc (Real.pi/2) x)-squareWeight α c x =
      (frequencyRadius c x-((x (.inr 1))^2+(x (.inr 2))^2))/(2*α) := by
  simp only [squareWeight,imbalance_flow,frequencyRadius_quarter_turn]
  ring

#print axioms configuration_corrected
#print axioms configuration_square
#print axioms ratio_matching
#print axioms mixed_corrected
#print axioms mixed_square
#print axioms correctedWeight_flow
#print axioms correctedWeight_continuous
#print axioms squareWeight_continuous
#print axioms frequencyRadius_quarter_turn
#print axioms squareWeight_quarter_defect
end
end UnifiedTheory.Audit.KFCausalQuarticChargeProfiles
