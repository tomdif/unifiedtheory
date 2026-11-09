/- All eight reverse energy graphs along bounded source curves. The
remaining clock, kinetic and vacuum graphs are integrated through their
closed intermediate operators, then combined with the proved matter graphs. -/
import UnifiedTheory.Audit.KFCausalSourcedSecondMomentum
import UnifiedTheory.Audit.KFCausalCoherentMatterCurve
import UnifiedTheory.Audit.KFCausalGaussianClockSquare
import UnifiedTheory.Audit.KFCausalEnergyReverseFactors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCoherentSecondCurves
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalClockFloorCoherentBounds (sourceSize)
open KFCausalClockFloorCoherentOrbitContinuity (physicalProfile_curve_continuous continuous_angle_memLp)
open KFCausalClockFloorSourcedClockMomentum (state)
open KFCausalClockFloorSourcedCommonDomain (factorOutput)
open KFCausalClockFloorTrialClockEnergy (dampedClockFunction dampedClockFunction_memLp)
open KFCausalClockFloorClockHalf (clockHalf clockHalf_selfAdjoint)
open KFCausalClockFloorBoundedInverse (inverseL inverseL_graph)
open KFCausalClockFloorExponential (longitudinalExponential longitudinal_exponential_closed)
open KFCausalClockFloorTrialSpectralDomain (orderedExponential reversedExponential)
open KFCausalPhysicalTransverseMomentum (transverseMomentum transverseMomentum_selfAdjoint)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalCoherentFactorResponseBounds (kineticIndex)
open KFCausalGaussianVacuumSquare (original_strip double_strip)
open KFCausalOrderedOperatorComposition (composition_graph)
open KFCausalProjectedKineticResponse (integral_closed_graph)
open KFCausalVariableWidthSourceCurves (meanState meanFactor factor_continuous state_continuous meanFactor_graph)

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (h : ℝ) (hb : |h| ≤ Real.pi*ε/3)
  (P B : ℝ) (C : ℝ → ℂ) (p : ℝ → ℝ) (b : ℝ → Fin 5 → ℂ)
  (hCc : Continuous C) (hpc : Continuous p) (hbc : Continuous b)
  (hC : ∀ θ, ‖C θ‖ ≤ 1) (hp : ∀ θ, |p θ| ≤ P) (hB : ∀ θ, sourceSize (b θ) ≤ B)
local notation "hb₀" => original_strip ε h hε hb
local notation "g" => dampedClockFunction ε a
local notation "hg" => dampedClockFunction_memLp ε a hε ha

def clockCurve (θ : ℝ) : Hilbert :=
  KFCausalGaussianClockSquare.output ε a α β hε ha hα hβ hw (C θ) (p θ) (b θ)
def kineticCurve (i : Fin 4) (θ : ℝ) : Hilbert :=
  KFCausalSourcedSecondMomentum.secondOutput α β hα hβ hw (C θ) (p θ) (b θ) g hg h (modelDirections i)
def vacuumCurve (θ : ℝ) : Hilbert :=
  KFCausalGaussianVacuumSquare.doubleOutput ε a α β hε ha hα hβ hw (C θ) (p θ) (b θ) h hb

include hCc hpc hbc hC hB in
theorem clock_continuous : Continuous (clockCurve ε a α β hε ha hα hβ hw C p b) :=
  physicalProfile_curve_continuous α β B hα hβ hw C p b
    (KFCausalGaussianClockSquare.fullClockFunction ε a)
    (KFCausalGaussianClockSquare.fullClockFunction_memLp ε a hε ha) hCc hpc hbc hC hB

include hCc hpc hbc hC hB in
theorem kinetic_continuous (i : Fin 4) :
    Continuous (kineticCurve ε a α β hε ha hα hβ hw h C p b i) :=
  KFCausalSourcedSecondMomentum.secondOutput_curve_continuous α β hα hβ hw g hg
    B C p b hCc hpc hbc hC hB h (modelDirections i)

include hCc hpc hbc hC hp hB in
theorem vacuum_continuous : Continuous (vacuumCurve ε a α β hε ha hα hβ hw h hb C p b) :=
  (KFCausalVariableWidthFieldContinuity.outputs_curve_continuous ε a α β (2*h) hε ha hα hβ hw
    (double_strip ε h hb) P B C p b hCc hpc hbc hC hp hB).1

def meanClock : Hilbert := ∫ θ, clockCurve ε a α β hε ha hα hβ hw C p b θ ∂angleMeasure
def meanKinetic (i : Fin 4) : Hilbert := inverseL ε hε
  (∫ θ, kineticCurve ε a α β hε ha hα hβ hw h C p b i θ ∂angleMeasure)
def meanVacuum : Hilbert := inverseL ε hε
  (∫ θ, vacuumCurve ε a α β hε ha hα hβ hw h hb C p b θ ∂angleMeasure)

include hCc hpc hbc hC hp hB in
theorem mean_clock_graph :
    (meanFactor ε a α β hε ha hα hβ hw h hb₀ C p b modelDirections pointField 0,
      meanClock ε a α β hε ha hα hβ hw C p b) ∈ (clockHalf ε).graph :=
  integral_closed_graph _ (clockHalf_selfAdjoint ε).isClosed _ _
    (factor_continuous ε a α β hε ha hα hβ hw h hb₀ P B C p b hCc hpc hbc hC hp hB modelDirections pointField 0)
    (clock_continuous ε a α β hε ha hα hβ hw B C p b hCc hpc hbc hC hB)
    (fun θ => KFCausalGaussianClockSquare.second_graph ε a α β hε ha hα hβ hw (C θ) (p θ) (b θ))

include hCc hpc hbc hC hp hB in
theorem mean_kinetic_graph (i : Fin 4) :
    (meanFactor ε a α β hε ha hα hβ hw h hb₀ C p b modelDirections pointField (kineticIndex i),
      meanKinetic ε a α β hε ha hα hβ hw h C p b i) ∈
        (KFCausalClockFloorKineticSquare.reverse ε h (modelDirections i)).graph := by
  have hpoint (θ : ℝ) :
      (factorOutput ε a α β hε ha hα hβ hw (C θ) (p θ) (b θ) h hb₀ modelDirections pointField (kineticIndex i),
        kineticCurve ε a α β hε ha hα hβ hw h C p b i θ) ∈ (transverseMomentum h (modelDirections i)).graph := by
    fin_cases i <;> exact KFCausalSourcedSecondMomentum.second_graph α β hα hβ hw (C θ) (p θ) (b θ) g hg h _
  have hG := integral_closed_graph _ (transverseMomentum_selfAdjoint h (modelDirections i)).isClosed _ _
    (factor_continuous ε a α β hε ha hα hβ hw h hb₀ P B C p b hCc hpc hbc hC hp hB modelDirections pointField (kineticIndex i))
    (kinetic_continuous ε a α β hε ha hα hβ hw h B C p b hCc hpc hbc hC hB i) hpoint
  exact (composition_graph _ _ _ _).mpr ⟨_,hG,(inverseL_graph ε hε _ _).mpr rfl⟩

include hCc hpc hbc hC hp hB in
theorem mean_vacuum_square_graph :
    (meanState ε a α β hε ha hα hβ hw C p b,
      meanVacuum ε a α β hε ha hα hβ hw h hb C p b) ∈
        (KFCausalClockFloorVacuumSquare.square ε hε h).graph := by
  have hc := state_continuous ε a α β hε ha hα hβ hw B C p b hCc hpc hbc hC hB
  have hi := (continuous_angle_memLp _ hc).integrable (by norm_num)
  have he := (inverseL ε hε).integral_comp_comm hi
  have hG := integral_closed_graph _ (longitudinal_exponential_closed ε hε h 1)
    (fun θ => inverseL ε hε (state ε a α β hε ha hα hβ hw (C θ) (p θ) (b θ)))
    (vacuumCurve ε a α β hε ha hα hβ hw h hb C p b)
    ((inverseL ε hε).continuous.comp hc)
    (vacuum_continuous ε a α β hε ha hα hβ hw h hb P B C p b hCc hpc hbc hC hp hB)
    (fun θ => KFCausalGaussianVacuumSquare.doubleOutput_graph ε a α β hε ha hα hβ hw (C θ) (p θ) (b θ) h hb)
  rw [he] at hG
  exact (KFCausalClockFloorVacuumSquare.square_graph ε hε h _ _).mpr ⟨_,hG,rfl⟩

include hCc hpc hbc hC hp hB in
theorem mean_vacuum_reverse_graph :
    (meanFactor ε a α β hε ha hα hβ hw h hb₀ C p b modelDirections pointField 7,
      meanVacuum ε a α β hε ha hα hβ hw h hb C p b) ∈ (reversedExponential ε hε h).graph := by
  obtain ⟨u,hu,hz⟩ := (composition_graph _ _ _ _).mp
    (mean_vacuum_square_graph ε a α β hε ha hα hβ hw h hb P B C p b hCc hpc hbc hC hp hB)
  have he := (orderedExponential ε hε h).mem_graph_snd_inj' hu
    (meanFactor_graph ε a α β hε ha hα hβ hw h hb₀ P B C p b hCc hpc hbc hC hp hB modelDirections pointField 7) rfl
  dsimp only at he
  rwa [he] at hz

def meanSecond : Fin 8 → Hilbert :=
  ![meanClock ε a α β hε ha hα hβ hw C p b,
    meanKinetic ε a α β hε ha hα hβ hw h C p b 0,
    meanKinetic ε a α β hε ha hα hβ hw h C p b 1,
    meanKinetic ε a α β hε ha hα hβ hw h C p b 2,
    meanKinetic ε a α β hε ha hα hβ hw h C p b 3,
    KFCausalCoherentMatterCurve.meanOutput ε a α β hε ha hα hβ hw h hb C p b 0,
    KFCausalCoherentMatterCurve.meanOutput ε a α β hε ha hα hβ hw h hb C p b 1,
    meanVacuum ε a α β hε ha hα hβ hw h hb C p b]

include hCc hpc hbc hC hp hB in
theorem mean_reverse_graph (j : Fin 8) :
    (meanFactor ε a α β hε ha hα hβ hw h hb₀ C p b modelDirections pointField j,
      meanSecond ε a α β hε ha hα hβ hw h hb C p b j) ∈
        (reverseFactor ε hε h modelDirections pointField j).graph := by
  fin_cases j
  · exact mean_clock_graph ε a α β hε ha hα hβ hw h hb P B C p b hCc hpc hbc hC hp hB
  · exact mean_kinetic_graph ε a α β hε ha hα hβ hw h hb P B C p b hCc hpc hbc hC hp hB 0
  · exact mean_kinetic_graph ε a α β hε ha hα hβ hw h hb P B C p b hCc hpc hbc hC hp hB 1
  · exact mean_kinetic_graph ε a α β hε ha hα hβ hw h hb P B C p b hCc hpc hbc hC hp hB 2
  · exact mean_kinetic_graph ε a α β hε ha hα hβ hw h hb P B C p b hCc hpc hbc hC hp hB 3
  · exact KFCausalCoherentMatterCurve.linear_reverse_graph ε a α β hε ha hα hβ hw h hb P B C p b hCc hpc hbc hC hp hB
  · exact KFCausalCoherentMatterCurve.quadratic_reverse_graph ε a α β hε ha hα hβ hw h hb P B C p b hCc hpc hbc hC hp hB
  · exact mean_vacuum_reverse_graph ε a α β hε ha hα hβ hw h hb P B C p b hCc hpc hbc hC hp hB

#print axioms clock_continuous
#print axioms kinetic_continuous
#print axioms vacuum_continuous
#print axioms mean_clock_graph
#print axioms mean_kinetic_graph
#print axioms mean_vacuum_square_graph
#print axioms mean_vacuum_reverse_graph
#print axioms mean_reverse_graph
end
end UnifiedTheory.Audit.KFCausalCoherentSecondCurves
