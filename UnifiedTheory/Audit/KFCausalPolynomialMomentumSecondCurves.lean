/- All eight reverse graphs on the source-circle representation of the
actual clock momentum. Bounded clock maps preserve the second kinetic
graphs; the doubled spectral action controls the vacuum contribution. -/
import UnifiedTheory.Audit.KFCausalPolynomialMomentumMatterCurve
import UnifiedTheory.Audit.KFCausalCoherentSecondCurves
import UnifiedTheory.Audit.KFCausalKineticSquareClockOutput
import UnifiedTheory.Audit.KFCausalGaussianMomentumVacuumSquare

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalPolynomialMomentumSecondCurves
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalPolynomialGaussianStates
  (circleSource sourceBound circleSource_continuous circleSource_bound)
open KFCausalSourceCircleCoefficients
open KFCausalVariableWidthPolynomialMomentum (pureCurve factorCurve pureCurve_continuous factorCurve_continuous)
open KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open KFCausalClockFloorTrialClockEnergy (dampedClockFunction dampedClockFunction_memLp)
open KFCausalClockFloorClockHalf (clockHalf clockHalf_selfAdjoint)
open KFCausalClockFloorBoundedInverse (inverseL inverseL_graph orderedExponential_closed)
open KFCausalClockFloorExponential (longitudinalExponential longitudinal_exponential_closed)
open KFCausalClockFloorTrialSpectralDomain (orderedExponential reversedExponential)
open KFCausalPhysicalTransverseMomentum (transverseMomentum transverseMomentum_selfAdjoint)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalCoherentFactorResponseBounds (kineticIndex)
open KFCausalGaussianVacuumSquare (original_strip double_strip)
open KFCausalPureClockOutputMultipliers (outputMap outputMap_continuous)
open KFCausalOrderedOperatorComposition (composition_graph)
open KFCausalProjectedKineticResponse (integral_closed_graph)

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi*ε/3)
  (p : ℝ) (b : Fin 5 → ℂ) (i : Fin 5) (n : ℕ)
local notation "hb₀" => original_strip ε h hε hb
local notation "hb₂" => double_strip ε h hb

def clockCurve (θ : ℝ) : Hilbert :=
  KFCausalGaussianClockSquare.momentumOutput ε a α β hε ha hα hβ hw (weight n θ) p (circleSource b i θ) h
def kineticCurve (j : Fin 4) (θ : ℝ) : Hilbert := outputMap ε a h hε ha p
  (KFCausalCoherentSecondCurves.kineticCurve ε a α β hε ha hα hβ hw h (weight n) (fun _ => p) (circleSource b i) j θ)
  (KFCausalCoherentSecondCurves.kineticCurve ε (a/2) α β hε (half_pos ha) hα hβ hw h (weight n) (fun _ => p) (circleSource b i) j θ)
def vacuumCurve (θ : ℝ) : Hilbert :=
  KFCausalGaussianMomentumVacuumSquare.doubleOutput ε a α β hε ha hα hβ hw (weight n θ) p (circleSource b i θ) h hb

theorem clock_continuous : Continuous (clockCurve ε a α β hε ha hα hβ hw h p b i n) := by
  have hc (a' : ℝ) (ha' : 0 < a') := KFCausalCoherentSecondCurves.clock_continuous ε a' α β
    hε ha' hα hβ hw (sourceBound b) (weight n) (fun _ => p) (circleSource b i)
    (weight_continuous n) continuous_const (circleSource_continuous b i)
    (fun θ => (weight_norm n θ).le) (circleSource_bound b i)
  exact outputMap_continuous ε a h hε ha p _ _ (hc a ha) (hc (a/2) (half_pos ha))

theorem kinetic_continuous (j : Fin 4) :
    Continuous (kineticCurve ε a α β hε ha hα hβ hw h p b i n j) := by
  have hc (a' : ℝ) (ha' : 0 < a') := KFCausalCoherentSecondCurves.kinetic_continuous ε a' α β
    hε ha' hα hβ hw h (sourceBound b) (weight n) (fun _ => p) (circleSource b i)
    (weight_continuous n) continuous_const (circleSource_continuous b i)
    (fun θ => (weight_norm n θ).le) (circleSource_bound b i) j
  exact outputMap_continuous ε a h hε ha p _ _ (hc a ha) (hc (a/2) (half_pos ha))

theorem vacuum_continuous : Continuous (vacuumCurve ε a α β hε ha hα hβ hw h hb p b i n) :=
  continuous_const.smul (factorCurve_continuous ε a α β hε ha hα hβ hw (2*h) p b i hb₂ n 0 0 7)

def meanClock : Hilbert := ∫ θ, clockCurve ε a α β hε ha hα hβ hw h p b i n θ ∂angleMeasure
def meanKinetic (j : Fin 4) : Hilbert := inverseL ε hε
  (∫ θ, kineticCurve ε a α β hε ha hα hβ hw h p b i n j θ ∂angleMeasure)
def meanVacuum : Hilbert := inverseL ε hε
  (∫ θ, vacuumCurve ε a α β hε ha hα hβ hw h hb p b i n θ ∂angleMeasure)

theorem mean_clock_graph :
    (∫ θ, factorCurve ε a α β hε ha hα hβ hw h p b i hb₀ n modelDirections pointField 0 θ ∂angleMeasure,
      meanClock ε a α β hε ha hα hβ hw h p b i n) ∈ (clockHalf ε).graph :=
  integral_closed_graph _ (clockHalf_selfAdjoint ε).isClosed _ _
    (factorCurve_continuous ε a α β hε ha hα hβ hw h p b i hb₀ n modelDirections pointField 0)
    (clock_continuous ε a α β hε ha hα hβ hw h p b i n)
    (fun θ => KFCausalGaussianClockSquare.momentum_second_graph ε a α β hε ha hα hβ hw
      (weight n θ) p (circleSource b i θ) h hb₀ modelDirections pointField)

include hh in
theorem mean_kinetic_graph (j : Fin 4) :
    (∫ θ, factorCurve ε a α β hε ha hα hβ hw h p b i hb₀ n modelDirections pointField (kineticIndex j) θ ∂angleMeasure,
      meanKinetic ε a α β hε ha hα hβ hw h p b i n j) ∈
        (KFCausalClockFloorKineticSquare.reverse ε h (modelDirections j)).graph := by
  have hpoint (θ : ℝ) :
      (factorCurve ε a α β hε ha hα hβ hw h p b i hb₀ n modelDirections pointField (kineticIndex j) θ,
        kineticCurve ε a α β hε ha hα hβ hw h p b i n j θ) ∈ (transverseMomentum h (modelDirections j)).graph := by
    fin_cases j <;> exact KFCausalKineticSquareClockOutput.outputMap_transverse_graph ε a h hε ha hh _ p _ _ _ _
      (KFCausalSourcedSecondMomentum.second_graph α β hα hβ hw (weight n θ) p (circleSource b i θ)
        (dampedClockFunction ε a) (dampedClockFunction_memLp ε a hε ha) h _)
      (KFCausalSourcedSecondMomentum.second_graph α β hα hβ hw (weight n θ) p (circleSource b i θ)
        (dampedClockFunction ε (a/2)) (dampedClockFunction_memLp ε (a/2) hε (half_pos ha)) h _)
  have hG := integral_closed_graph _ (transverseMomentum_selfAdjoint h (modelDirections j)).isClosed _ _
    (factorCurve_continuous ε a α β hε ha hα hβ hw h p b i hb₀ n modelDirections pointField (kineticIndex j))
    (kinetic_continuous ε a α β hε ha hα hβ hw h p b i n j) hpoint
  exact (composition_graph _ _ _ _).mpr ⟨_,hG,(inverseL_graph ε hε _ _).mpr rfl⟩

include hh in
theorem mean_vacuum_square_graph :
    (∫ θ, pureCurve ε a α β hε ha hα hβ hw h p b i n θ ∂angleMeasure,
      meanVacuum ε a α β hε ha hα hβ hw h hb p b i n) ∈
        (KFCausalClockFloorVacuumSquare.square ε hε h).graph := by
  have hc := pureCurve_continuous ε a α β hε ha hα hβ hw h p b i n
  have hi := (continuous_angle_memLp _ hc).integrable (by norm_num)
  have he := (inverseL ε hε).integral_comp_comm hi
  have hG := integral_closed_graph _ (longitudinal_exponential_closed ε hε h 1)
    (fun θ => inverseL ε hε (pureCurve ε a α β hε ha hα hβ hw h p b i n θ))
    (vacuumCurve ε a α β hε ha hα hβ hw h hb p b i n)
    ((inverseL ε hε).continuous.comp hc)
    (vacuum_continuous ε a α β hε ha hα hβ hw h hb p b i n)
    (fun θ => KFCausalGaussianMomentumVacuumSquare.doubleOutput_graph ε a α β hε ha hα hβ hw
      (weight n θ) p (circleSource b i θ) h hh hb)
  rw [he] at hG
  exact (KFCausalClockFloorVacuumSquare.square_graph ε hε h _ _).mpr ⟨_,hG,rfl⟩

include hh in
theorem mean_vacuum_reverse_graph :
    (∫ θ, factorCurve ε a α β hε ha hα hβ hw h p b i hb₀ n modelDirections pointField 7 θ ∂angleMeasure,
      meanVacuum ε a α β hε ha hα hβ hw h hb p b i n) ∈ (reversedExponential ε hε h).graph := by
  have hfirst := integral_closed_graph _ (orderedExponential_closed ε hε h)
    (pureCurve ε a α β hε ha hα hβ hw h p b i n)
    (factorCurve ε a α β hε ha hα hβ hw h p b i hb₀ n modelDirections pointField 7)
    (pureCurve_continuous ε a α β hε ha hα hβ hw h p b i n)
    (factorCurve_continuous ε a α β hε ha hα hβ hw h p b i hb₀ n modelDirections pointField 7)
    (fun θ => KFCausalSourcedMomentumFactors.factorOutput_graph ε a α β hε ha hα hβ hw
      (weight n θ) p (circleSource b i θ) h hh hb₀ modelDirections pointField 7)
  obtain ⟨u,hu,hz⟩ := (composition_graph _ _ _ _).mp
    (mean_vacuum_square_graph ε a α β hε ha hα hβ hw h hh hb p b i n)
  have he := (orderedExponential ε hε h).mem_graph_snd_inj' hu hfirst rfl
  dsimp only at he
  rwa [he] at hz

def meanSecond : Fin 8 → Hilbert :=
  ![meanClock ε a α β hε ha hα hβ hw h p b i n,
    meanKinetic ε a α β hε ha hα hβ hw h p b i n 0,
    meanKinetic ε a α β hε ha hα hβ hw h p b i n 1,
    meanKinetic ε a α β hε ha hα hβ hw h p b i n 2,
    meanKinetic ε a α β hε ha hα hβ hw h p b i n 3,
    KFCausalPolynomialMomentumMatterCurve.meanOutput ε a α β hε ha hα hβ hw h hb p b i n 0,
    KFCausalPolynomialMomentumMatterCurve.meanOutput ε a α β hε ha hα hβ hw h hb p b i n 1,
    meanVacuum ε a α β hε ha hα hβ hw h hb p b i n]

include hh in
theorem mean_reverse_graph (j : Fin 8) :
    (∫ θ, factorCurve ε a α β hε ha hα hβ hw h p b i hb₀ n modelDirections pointField j θ ∂angleMeasure,
      meanSecond ε a α β hε ha hα hβ hw h hb p b i n j) ∈
        (reverseFactor ε hε h modelDirections pointField j).graph := by
  fin_cases j
  · exact mean_clock_graph ε a α β hε ha hα hβ hw h hb p b i n
  · exact mean_kinetic_graph ε a α β hε ha hα hβ hw h hh hb p b i n 0
  · exact mean_kinetic_graph ε a α β hε ha hα hβ hw h hh hb p b i n 1
  · exact mean_kinetic_graph ε a α β hε ha hα hβ hw h hh hb p b i n 2
  · exact mean_kinetic_graph ε a α β hε ha hα hβ hw h hh hb p b i n 3
  · exact KFCausalPolynomialMomentumMatterCurve.linear_reverse_graph ε a α β hε ha hα hβ hw h hb p b i n
  · exact KFCausalPolynomialMomentumMatterCurve.quadratic_reverse_graph ε a α β hε ha hα hβ hw h hb p b i n
  · exact mean_vacuum_reverse_graph ε a α β hε ha hα hβ hw h hh hb p b i n

#print axioms clock_continuous
#print axioms kinetic_continuous
#print axioms vacuum_continuous
#print axioms mean_clock_graph
#print axioms mean_kinetic_graph
#print axioms mean_vacuum_square_graph
#print axioms mean_vacuum_reverse_graph
#print axioms mean_reverse_graph
end
end UnifiedTheory.Audit.KFCausalPolynomialMomentumSecondCurves
