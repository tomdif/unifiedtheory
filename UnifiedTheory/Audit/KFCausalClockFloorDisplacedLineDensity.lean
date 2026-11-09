/- The full recentered analytic line is identified with the actual
displaced spectral representative. Its pointwise density limit retains
the clock Gaussian, transverse Gaussian and physical shear. -/
import UnifiedTheory.Audit.KFCausalClockFloorCenteredDensityLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedLineDensity
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse flow)
open UnifiedTheory.Audit.KFCausalClockFloorCenteredDensityLimit
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedPhaseLimit (rescaledPosition)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedShiftPhase (grouped shiftedPosition shear shiftedPosition_actual)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedClockPhase
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect (realClock)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip (clockPhase)
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (clockFactor)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources
open UnifiedTheory.Audit.KFCausalClassicalChargePhase (physicalTail)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)

def recenter (ε : ℝ) (hε : 0 < ε) (u h : ℝ) (Q ξ : Transverse) :=
  grouped (flow (-((KFCausalRegularizedLongitudinalChart.chartIso ε hε).symm u)) (rescaledPosition h Q ξ))

def centeredLine (ε a u h r : ℝ) (Q P ξ : Transverse) : ℂ :=
  clockPhase (r/h) (inverseShift ε u h)*clockFactor a ((u:ℂ)+((-h/2:ℝ):ℂ)*Complex.I)*
    KFCausalClockFloorCenteredGaussian.packet (groundWidth h) (neutralWidth h) Q (fun i => P i/h)
      (shiftedPosition ε u h (rescaledPosition h Q ξ))

theorem clockPhase_norm_ratio (ε u h r : ℝ) (hε : 0 < ε) :
    ‖clockPhase (r/h) (inverseShift ε u h)‖ = ‖phaseRatio ε r u h‖ := by
  rw [clockPhase_factor,norm_mul,inverseShift_zero,KFCausalComplexClockInverse.complexInverse_real ε hε]
  have hr (s : ℝ) : ‖clockPhase (r/h) (s:ℂ)‖ = 1 := by simp [clockPhase,Complex.norm_exp]
  rw [hr,one_mul]

theorem centeredLine_square (ε a u h r : ℝ) (hε : 0 < ε) (Q P ξ : Transverse) :
    ‖centeredLine ε a u h r Q P ξ‖^2 =
      ‖clockFactor a ((u:ℂ)+((-h/2:ℝ):ℂ)*Complex.I)‖^2*density ε u h r Q P ξ := by
  simp only [centeredLine,density,norm_mul,mul_pow,clockPhase_norm_ratio ε u h r hε]
  ring

theorem centeredLine_density_tendsto (ε a u r : ℝ) (hε : 0 < ε) (Q P ξ : Transverse)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => ‖centeredLine ε a u (h n) r Q P ξ‖^2) atTop
      (𝓝 (‖clockFactor a (u:ℂ)‖^2 *
        (Real.exp (-2*KFCausalClockFloorCenteredGaussian.realQuadratic (groundWidth 1) (neutralWidth 1) ξ)*
          Real.exp ((r+shear Q P)/realClock ε hε u)))) := by
  have hc : Continuous (fun h : ℝ => clockFactor a ((u:ℂ)+((-h/2:ℝ):ℂ)*Complex.I)) := by
    unfold clockFactor
    fun_prop
  have ht := (hc.continuousAt.tendsto.comp hz).norm.pow 2
  simp only [neg_zero,zero_div,Complex.ofReal_zero,zero_mul,add_zero] at ht
  simp_rw [centeredLine_square ε a u _ r hε]
  exact ht.mul (density_tendsto ε u r hε Q P ξ h hh hz)

theorem displacedLine_norm (ε a u h : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (q k : Joint 2 4) (ξ : Transverse) :
    let Q := physicalTail (KFCausalDisplacedPhysicalPhase.phase h q k).1
    let P := physicalTail (KFCausalDisplacedPhysicalPhase.phase h q k).2
    ‖amplitude h q k * KFCausalClockFloorCoherentStrip.line ε a (groundWidth h) (neutralWidth h)
      (clockFrequency h k) (source h q k) (-h/2) (u,recenter ε hε u h Q ξ)‖^2 =
      ‖centeredLine ε a u h (h*clockFrequency h k) Q P ξ‖^2 := by
  dsimp only
  have hf : h*clockFrequency h k/h = clockFrequency h k := by field_simp
  have hp := KFCausalClockFloorDisplacedCentering.displaced_packet_norm h hh q k
    (inverseShift ε u h) (recenter ε hε u h (physicalTail (KFCausalDisplacedPhysicalPhase.phase h q k).1) ξ)
  have he : KFCausalClockFloorCoherentBounds.position (inverseShift ε u h)
      (recenter ε hε u h (physicalTail (KFCausalDisplacedPhysicalPhase.phase h q k).1) ξ) =
      shiftedPosition ε u h (rescaledPosition h (physicalTail (KFCausalDisplacedPhysicalPhase.phase h q k).1) ξ) :=
    funext (shiftedPosition_actual ε u h hε _)
  rw [he] at hp
  simp only [KFCausalClockFloorCoherentStrip.line,KFCausalClockFloorCoherentStrip.trial,
    centeredLine,hf]
  change ‖amplitude h q k*(clockPhase (clockFrequency h k) (inverseShift ε u h)*
    clockFactor a ((u:ℂ)+((-h/2:ℝ):ℂ)*Complex.I)*_)‖^2 = _
  simp only [norm_mul] at hp ⊢
  have ht := congrArg (fun z : ℝ =>
    (‖clockPhase (clockFrequency h k) (inverseShift ε u h)‖*
      ‖clockFactor a ((u:ℂ)+((-h/2:ℝ):ℂ)*Complex.I)‖*z)^2) hp
  convert ht using 1
  simp only [inverseShift]
  ring

theorem boosted_clock (h : ℝ) (hh : h ≠ 0) (p : Configuration) (θ : ℝ) :
    h*clockFrequency h (KFCausalChargeModulationFlow.parameter θ
      (KFCausalDisplacedBoostParameters.boostK (h⁻¹ • p))) = p.1 := by
  change h*(2*Real.pi*(h⁻¹*p.1/(2*Real.pi))) = p.1
  field_simp

def boostedLine (ε a : ℝ) (hε : 0 < ε) (u h : ℝ) (p : Configuration) (θ : ℝ) (ξ : Transverse) : ℂ :=
  let q := KFCausalChargeModulationFlow.parameter θ (KFCausalDisplacedBoostParameters.boostQ h (h⁻¹ • p))
  let k := KFCausalChargeModulationFlow.parameter θ (KFCausalDisplacedBoostParameters.boostK (h⁻¹ • p))
  amplitude h q k * KFCausalClockFloorCoherentStrip.line ε a (groundWidth h) (neutralWidth h)
    (clockFrequency h k) (source h q k) (-h/2)
      (u,recenter ε hε u h (physicalTail (KFCausalDisplacedPhysicalPhase.phase h q k).1) ξ)

theorem boostedLine_norm (ε a : ℝ) (hε : 0 < ε) (u h : ℝ) (hh : h ≠ 0)
    (p : Configuration) (θ : ℝ) (ξ : Transverse) :
    let z := KFCausalClassicalChargePhase.rotate (-θ) (0,KFCausalClassicalPhysicalPhase.toPaired p)
    ‖boostedLine ε a hε u h p θ ξ‖^2 =
      ‖centeredLine ε a u h p.1 (physicalTail z.1) (physicalTail z.2) ξ‖^2 := by
  dsimp only [boostedLine]
  rw [displacedLine_norm ε a u h hε hh,boosted_clock h hh,
    KFCausalDisplacedPhysicalPhase.phase_boost_orbit h hh]

theorem boostedLine_density_tendsto (ε a u : ℝ) (hε : 0 < ε)
    (p : Configuration) (θ : ℝ) (ξ : Transverse)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => ‖boostedLine ε a hε u (h n) p θ ξ‖^2) atTop
      (𝓝 (‖clockFactor a (u:ℂ)‖^2 *
        (Real.exp (-2*KFCausalClockFloorCenteredGaussian.realQuadratic (groundWidth 1) (neutralWidth 1) ξ)*
          Real.exp ((p.1+KFCausalClassicalChargePhase.shear
            (KFCausalClassicalChargePhase.rotate (-θ) (0,KFCausalClassicalPhysicalPhase.toPaired p)))/
              realClock ε hε u)))) := by
  simp_rw [boostedLine_norm ε a hε u _ (hh _)]
  exact centeredLine_density_tendsto ε a u p.1 hε _ _ ξ h hh hz

#print axioms clockPhase_norm_ratio
#print axioms centeredLine_square
#print axioms centeredLine_density_tendsto
#print axioms displacedLine_norm
#print axioms boosted_clock
#print axioms boostedLine_norm
#print axioms boostedLine_density_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedLineDensity
