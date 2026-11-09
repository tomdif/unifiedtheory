/- The two actual symmetric kinetic seconds after each original
vacuum or matter output, with charge projection through closed momenta. -/
import UnifiedTheory.Audit.KFCausalSymmetricJetAction
import UnifiedTheory.Audit.KFCausalSymmetricKineticGraphAssembly
import UnifiedTheory.Audit.KFCausalOuterMatterExponential
import UnifiedTheory.Audit.KFCausalMatterPrimitiveAverage

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalOuterSymmetricVacuumMatter
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalPhysicalCircleAction (action action_strong_continuous)
open KFCausalStandingChargeOperator (zeroProjection)
open KFCausalVacuumMatterInput (innerDegree innerOutput)
open KFCausalSourcedWidthMatterSquare (baseline)
open KFCausalMatterPrimitiveAverage (average average_graph average_inverseL average_action)
open KFCausalPhysicalTransverseMomentum (transverseMomentum transverseMomentum_selfAdjoint)
open KFCausalSymmetricMomentumCoordinates (symmetricDirection)
open KFCausalClockFloorSymmetricOrbitGraph (symmetricEnergyIndex)
open KFCausalSymmetricKineticGraphAssembly (kineticSecond)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalEuclideanProductCoordinates (Block Joint split)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalNormalizedChargeFlow (momentumScale)
open KFCausalSymmetricMixedTranslation (velocity clock_translate)
open KFCausalSymmetricPhysicalJets (numerator)
open MeasureTheory

variable (ε h a W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a) (hw : 1 ≤ w)
  (hW : w ≤ W) (hb : |h| ≤ ε/10) (i : Option (Fin 2)) (j : Fin 2)
local notation "u" => innerOutput ε h a w C p b P hε hh ha hw hb i

def rawOutput (order : Fin 3) (θ : ℝ) : Hilbert :=
  KFCausalSymmetricJetAction.output ε h a W w C p b P (innerDegree i) j order
    hε hh ha hw hW hb θ

def forwardOutput (θ : ℝ) : Hilbert :=
  (-Complex.I*(h:ℂ)) • rawOutput ε h a W w C p b P hε hh ha hw hW hb i j 1 θ

def momentumOutput (θ : ℝ) : Hilbert :=
  (-(h:ℂ)^2) • rawOutput ε h a W w C p b P hε hh ha hw hW hb i j 2 θ

def secondOutput (θ : ℝ) : Hilbert :=
  inverseL ε hε (momentumOutput ε h a W w C p b P hε hh ha hw hW hb i j θ)

def projectedForward : Hilbert := average (forwardOutput ε h a W w C p b P hε hh ha hw hW hb i j)
def projectedOutput : Hilbert :=
  inverseL ε hε (average (momentumOutput ε h a W w C p b P hε hh ha hw hW hb i j))

theorem zero_output (θ : ℝ) :
    rawOutput ε h a W w C p b P hε hh ha hw hW hb i j 0 θ=inverseL ε hε (action h hh θ u) := by
  rw [rawOutput,KFCausalSymmetricJetAction.output,KFCausalSymmetricJetAction.action_zero_order,
    KFCausalOuterMatterExponential.actual_input ε h a W w C p b P hε hh ha hw hW hb i θ]

private def profile (order : Fin 3) (θ : ℝ) (x : Block 2 × Block 4) : ℂ :=
  numerator ε h a (groundWidth h) w (momentumScale h) θ C p b (Polynomial.X^innerDegree i) P j order
    (x.2 0:ℂ) ((split 2 4).symm x)

include hh hw in
private theorem profile_derivatives (θ : ℝ) (x : Joint 2 4) :
    HasDerivAt (fun t : ℝ => profile ε h a w C p b P i j 0 θ
      (split 2 4 (x+t • velocity ε hε j (x (.inr 0)))))
      (profile ε h a w C p b P i j 1 θ (split 2 4 x)) 0 ∧
    HasDerivAt (fun t : ℝ => profile ε h a w C p b P i j 1 θ
      (split 2 4 (x+t • velocity ε hε j (x (.inr 0)))))
      (profile ε h a w C p b P i j 2 θ (split 2 4 x)) 0 := by
  have he (t : ℝ) : (split 2 4 (x+t • velocity ε hε j (x (.inr 0)))).2 0=x (.inr 0) :=
    clock_translate ε hε j (x (.inr 0)) t x
  have h₁ := KFCausalSymmetricPhysicalJets.numerator_zero_derivative ε hε h a
    (groundWidth h) w (momentumScale h) θ C p b (Polynomial.X^innerDegree i) P j
    (x (.inr 0)) x (groundWidth_positive h hh) (zero_lt_one.trans_le hw)
  have h₂ := KFCausalSymmetricPhysicalJets.numerator_first_derivative ε hε h a
    (groundWidth h) w (momentumScale h) θ C p b (Polynomial.X^innerDegree i) P j
    (x (.inr 0)) x (groundWidth_positive h hh) (zero_lt_one.trans_le hw)
  simpa only [profile,MeasurableEquiv.symm_apply_apply,he] using And.intro h₁ h₂

private theorem primitive_graphs (θ : ℝ) :
    (inverseL ε hε (action h hh θ u),forwardOutput ε h a W w C p b P hε hh ha hw hW hb i j θ) ∈
      (transverseMomentum h (symmetricDirection j)).graph ∧
    (forwardOutput ε h a W w C p b P hε hh ha hw hW hb i j θ,
      momentumOutput ε h a W w C p b P hε hh ha hw hW hb i j θ) ∈
        (transverseMomentum h (symmetricDirection j)).graph := by
  have hrep (order : Fin 3) :
      KFCausalClockFloorMixedRadial.clockMixed ε hε
        (rawOutput ε h a W w C p b P hε hh ha hw hW hb i j order θ) =ᵐ[volume]
          profile ε h a w C p b P i j order θ :=
    KFCausalSymmetricJetAction.output_clockMixed ε h a W w C p b P (innerDegree i) j order
      hε hh ha hw hW hb θ
  have hzero := hrep 0
  rw [zero_output ε h a W w C p b P hε hh ha hw hW hb i j θ] at hzero
  exact KFCausalSymmetricMixedDerivativeGraph.second_derivative_graph ε hε j h hh
    (inverseL ε hε (action h hh θ u))
    (rawOutput ε h a W w C p b P hε hh ha hw hW hb i j 1 θ)
    (rawOutput ε h a W w C p b P hε hh ha hw hW hb i j 2 θ)
    _ _ _ hzero (hrep 1) (hrep 2)
    (fun x => (profile_derivatives ε h a w C p b P hε hh hw i j θ x).1)
    (fun x => (profile_derivatives ε h a w C p b P hε hh hw i j θ x).2)

theorem first_momentum_graph (θ : ℝ) :
    (inverseL ε hε (action h hh θ u),forwardOutput ε h a W w C p b P hε hh ha hw hW hb i j θ) ∈
      (transverseMomentum h (symmetricDirection j)).graph :=
  (primitive_graphs ε h a W w C p b P hε hh ha hw hW hb i j θ).1

theorem second_momentum_graph (θ : ℝ) :
    (forwardOutput ε h a W w C p b P hε hh ha hw hW hb i j θ,
      momentumOutput ε h a W w C p b P hε hh ha hw hW hb i j θ) ∈
        (transverseMomentum h (symmetricDirection j)).graph :=
  (primitive_graphs ε h a W w C p b P hε hh ha hw hW hb i j θ).2

theorem forward_graph (θ : ℝ) :
    (action h hh θ u,forwardOutput ε h a W w C p b P hε hh ha hw hW hb i j θ) ∈
      (energyFactor ε hε h modelDirections pointField (symmetricEnergyIndex j)).graph :=
  KFCausalSymmetricKineticGraphAssembly.actual_forward_graph ε hε h j _ _
    (first_momentum_graph ε h a W w C p b P hε hh ha hw hW hb i j θ)

theorem reverse_graph (θ : ℝ) :
    (forwardOutput ε h a W w C p b P hε hh ha hw hW hb i j θ,
      secondOutput ε h a W w C p b P hε hh ha hw hW hb i j θ) ∈
        (reverseFactor ε hε h modelDirections pointField (symmetricEnergyIndex j)).graph :=
  KFCausalSymmetricKineticGraphAssembly.actual_reverse_graph ε hε h j _ _
    (second_momentum_graph ε h a W w C p b P hε hh ha hw hW hb i j θ)

theorem mixed_graph (θ : ℝ) :
    (action h hh θ u,secondOutput ε h a W w C p b P hε hh ha hw hW hb i j θ) ∈
      (kineticSecond ε hε h j).graph :=
  KFCausalSymmetricKineticGraphAssembly.actual_second_graph ε hε h j _ _ _
    (first_momentum_graph ε h a W w C p b P hε hh ha hw hW hb i j θ)
    (second_momentum_graph ε h a W w C p b P hε hh ha hw hW hb i j θ)

include hW in
theorem mixed_domain (θ : ℝ) : action h hh θ u ∈ (kineticSecond ε hε h j).domain :=
  LinearPMap.mem_domain_of_mem_graph (mixed_graph ε h a W w C p b P hε hh ha hw hW hb i j θ)

theorem rawOutput_continuous (order : Fin 3) :
    Continuous (rawOutput ε h a W w C p b P hε hh ha hw hW hb i j order) :=
  KFCausalSymmetricJetAction.output_continuous ε h a W w C p b P (innerDegree i) j order
    hε hh ha hw hW hb

theorem forwardOutput_continuous :
    Continuous (forwardOutput ε h a W w C p b P hε hh ha hw hW hb i j) :=
  (rawOutput_continuous ε h a W w C p b P hε hh ha hw hW hb i j 1).const_smul _

theorem momentumOutput_continuous :
    Continuous (momentumOutput ε h a W w C p b P hε hh ha hw hW hb i j) :=
  (rawOutput_continuous ε h a W w C p b P hε hh ha hw hW hb i j 2).const_smul _

theorem secondOutput_continuous : Continuous (secondOutput ε h a W w C p b P hε hh ha hw hW hb i j) :=
  (inverseL ε hε).continuous.comp (momentumOutput_continuous ε h a W w C p b P hε hh ha hw hW hb i j)

private theorem projected_first_momentum :
    (inverseL ε hε (zeroProjection h hh u),projectedForward ε h a W w C p b P hε hh ha hw hW hb i j) ∈
      (transverseMomentum h (symmetricDirection j)).graph := by
  have hg := average_graph _ (transverseMomentum_selfAdjoint h (symmetricDirection j)).isClosed
    (fun θ => inverseL ε hε (action h hh θ u)) _
    ((inverseL ε hε).continuous.comp (action_strong_continuous h hh u))
    (forwardOutput_continuous ε h a W w C p b P hε hh ha hw hW hb i j)
    (first_momentum_graph ε h a W w C p b P hε hh ha hw hW hb i j)
  rwa [average_inverseL ε hε _ (action_strong_continuous h hh u),average_action h hh u] at hg

private theorem projected_second_momentum :
    (projectedForward ε h a W w C p b P hε hh ha hw hW hb i j,
      average (momentumOutput ε h a W w C p b P hε hh ha hw hW hb i j)) ∈
        (transverseMomentum h (symmetricDirection j)).graph :=
  average_graph _ (transverseMomentum_selfAdjoint h (symmetricDirection j)).isClosed _ _
    (forwardOutput_continuous ε h a W w C p b P hε hh ha hw hW hb i j)
    (momentumOutput_continuous ε h a W w C p b P hε hh ha hw hW hb i j)
    (second_momentum_graph ε h a W w C p b P hε hh ha hw hW hb i j)

theorem projected_forward_graph :
    (zeroProjection h hh u,projectedForward ε h a W w C p b P hε hh ha hw hW hb i j) ∈
      (energyFactor ε hε h modelDirections pointField (symmetricEnergyIndex j)).graph :=
  KFCausalSymmetricKineticGraphAssembly.actual_forward_graph ε hε h j _ _
    (projected_first_momentum ε h a W w C p b P hε hh ha hw hW hb i j)

theorem projected_reverse_graph :
    (projectedForward ε h a W w C p b P hε hh ha hw hW hb i j,
      projectedOutput ε h a W w C p b P hε hh ha hw hW hb i j) ∈
        (reverseFactor ε hε h modelDirections pointField (symmetricEnergyIndex j)).graph :=
  KFCausalSymmetricKineticGraphAssembly.actual_reverse_graph ε hε h j _ _
    (projected_second_momentum ε h a W w C p b P hε hh ha hw hW hb i j)

theorem projected_graph :
    (zeroProjection h hh u,projectedOutput ε h a W w C p b P hε hh ha hw hW hb i j) ∈
      (kineticSecond ε hε h j).graph :=
  KFCausalSymmetricKineticGraphAssembly.actual_second_graph ε hε h j _ _ _
    (projected_first_momentum ε h a W w C p b P hε hh ha hw hW hb i j)
    (projected_second_momentum ε h a W w C p b P hε hh ha hw hW hb i j)

include hW in
theorem projected_domain : zeroProjection h hh u ∈ (kineticSecond ε hε h j).domain :=
  LinearPMap.mem_domain_of_mem_graph (projected_graph ε h a W w C p b P hε hh ha hw hW hb i j)

#print axioms zero_output
#print axioms first_momentum_graph
#print axioms second_momentum_graph
#print axioms forward_graph
#print axioms reverse_graph
#print axioms mixed_graph
#print axioms mixed_domain
#print axioms rawOutput_continuous
#print axioms forwardOutput_continuous
#print axioms momentumOutput_continuous
#print axioms secondOutput_continuous
#print axioms projected_forward_graph
#print axioms projected_reverse_graph
#print axioms projected_graph
#print axioms projected_domain
end
end UnifiedTheory.Audit.KFCausalOuterSymmetricVacuumMatter
