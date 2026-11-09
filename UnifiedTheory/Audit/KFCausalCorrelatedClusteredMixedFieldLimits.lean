/- Mixed field powers inherit actual strong limits for the independent
Gaussian clock amplitudes and their actual pure-clock momentum amplitudes.
All required clock-weight integrability is proved, rather than assumed. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredMixedFieldTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredMixedFieldLimits
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredPhysicalClockLimit (amplitudes)
open KFCausalCorrelatedClusteredNeutralPowers (fieldProfile)
open KFCausalMixedFieldClockCoefficients
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalMixedFieldClockBounds (field)

theorem field_zero_shift (ε s : ℝ) (hε : 0 < ε)
    (q : KFCausalTransverseDilationFlow.Transverse) :
    field (scale ε 0 s) q = (pointField q:ℂ) := by
  rw [KFCausalImaginaryShearInitialMultiplier.scale_zero ε s hε]
  change (q 4:ℂ)+(3*(1:ℂ)-2)*((q 2+q 3:ℝ):ℂ) = ((q 2+q 3+q 4:ℝ):ℂ)
  push_cast
  ring

variable {m : ℕ} (f : Family m) (α β ε y z : ℝ) (a p : Fin m → ℝ) (n : ℕ)
  (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hε : 0 < ε)
  (ha : ∀ i, 0 < a i) (hy : |y| ≤ Real.pi*ε/3) (hz : |z| ≤ Real.pi*ε/3) (hy0 : y ≠ 0)

def momentumAmplitudes (h s : ℝ) (i : Fin m) : ℂ :=
  KFCausalShiftedMomentumClockAmplitude.amplitude ε (a i) (p i) y h s

include hα hβ hw hε ha hy hz hy0

theorem input_exists_limit (u : ℝ → Hilbert)
    (hu : ∀ δ, 0 < δ → u δ =ᵐ[volume] fieldProfile f (amplitudes ε y a p) α β ε y z n δ) :
    ∃ v : Hilbert, Tendsto u (𝓝[>] 0) (𝓝 v) :=
  KFCausalCorrelatedClusteredMixedFieldTransfer.exists_limit f (amplitudes ε y a p) α β ε y z n
    hα hβ hw hε hy hz hy0
    (fun i => inputCoefficient_continuous ε (a i) (p i) y z n hε hy)
    (fun i => inputCoefficient_memLp ε (a i) (p i) y z n hε (ha i) hy hy0) u hu

theorem momentum_exists_limit (h : ℝ) (u : ℝ → Hilbert)
    (hu : ∀ δ, 0 < δ → u δ =ᵐ[volume] fieldProfile f (momentumAmplitudes ε y a p h) α β ε y z n δ) :
    ∃ v : Hilbert, Tendsto u (𝓝[>] 0) (𝓝 v) :=
  KFCausalCorrelatedClusteredMixedFieldTransfer.exists_limit f (momentumAmplitudes ε y a p h) α β ε y z n
    hα hβ hw hε hy hz hy0
    (fun i => momentumCoefficient_continuous ε (a i) (p i) y z h n hε hy)
    (fun i => momentumCoefficient_memLp ε (a i) (p i) y z h n hε (ha i) hy hy0) u hu

#print axioms field_zero_shift
#print axioms input_exists_limit
#print axioms momentum_exists_limit
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredMixedFieldLimits
