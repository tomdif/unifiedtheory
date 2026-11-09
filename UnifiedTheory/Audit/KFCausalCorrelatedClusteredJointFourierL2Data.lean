/- Actual correlated clock amplitudes discharge the joint L2 hypotheses.
The finite quotient, charged jet and one clock moment are assembled here;
identification with the unitary partial Fourier operator is separate. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredJointFourierDecomposition
import UnifiedTheory.Audit.KFCausalShiftedNarrowWeightedLimits
import UnifiedTheory.Audit.KFCausalFiniteLpRepresentatives

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredJointFourierL2Data
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredPhysicalClockLimit
open KFCausalCorrelatedClusteredJointFourierDecomposition
open KFCausalShiftedNarrowNormalizedCoefficients
open KFCausalShiftedNarrowWeightedProfiles
open KFCausalShiftedNarrowWeightedLimits

variable {m : ℕ} (f : Family m) (α β ε y z : ℝ) (a p : Fin m → ℝ) (k : ℕ)
  (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hε : 0 < ε)
  (hy : |y| ≤ Real.pi*ε/3) (hz : |z| ≤ Real.pi*ε/3) (ha : ∀ i, 0 < a i)
local notation "c" => amplitudes ε y a p
local notation "d" => momentAmplitude ε y a p
local notation "U" => inputPart f α ε y z k
local notation "V" => regularPart f α β ε y z p k
local notation "W" => chargedPart f α ε y z k
local notation "hc" => amplitudes_continuous ε y a p hε hy
local notation "hc2" => amplitudes_memLp ε y a p hε hy ha
local notation "hU" => fun i => inputCoefficient_controlled ε y z hε hy hz α (f.amplitude i) (f.polynomial i) k
local notation "hV" => fun i => regularCoefficient_controlled ε y z hε hy hz α β (p i) (f.amplitude i) (f.source i) (f.polynomial i) k
local notation "hW" => fun i => chargedCoefficient_controlled ε y z hε hy hz α (f.amplitude i) (f.polynomial i) k

include hε hy in
theorem momentAmplitude_continuous (i : Fin m) : Continuous (fun s => d s i) :=
  (KFCausalClockFloorRelativeShift.argument_smooth ε y).continuous.mul (hc i)

include hε hy ha in
theorem momentAmplitude_memLp (i : Fin m) : MemLp (fun s => d s i) 2 volume :=
  KFCausalShiftedGaussianRadialMoments.amplitude_moment_memLp ε (a i) (p i) y hε (ha i) hy

local notation "hd" => momentAmplitude_continuous ε y a p hε hy
local notation "hd2" => momentAmplitude_memLp ε y a p hε hy ha

include hα hβ hw hε hy hz ha

def inputVector (i : Fin m) (δ : ℝ) : Hilbert :=
  vector α β ε y (f.source i) (fun s => c s i) (U i) hα hβ hw hε hy (hc i) (hc2 i) (hU i) (f.degree i) δ

def inputLimitVector (i : Fin m) : Hilbert :=
  limitVector α β ε y (f.source i) (fun s => c s i) (U i) hα hβ hw hε hy (hc2 i) (hU i) (f.degree i)

theorem inputVector_coe (i : Fin m) (δ : ℝ) (hδ : 0 < δ) :
    inputVector f α β ε y z a p k hα hβ hw hε hy hz ha i δ =ᵐ[volume]
      weighted α β ε y (f.source i) (fun s => c s i) (U i) (f.degree i) δ :=
  vector_coe α β ε y (f.source i) (fun s => c s i) (U i) hα hβ hw hε hy (hc i) (hc2 i) (hU i) (f.degree i) δ hδ

theorem inputLimitVector_coe (i : Fin m) :
    inputLimitVector f α β ε y z a p k hα hβ hw hε hy hz ha i =ᵐ[volume]
      moment α β ε y (f.source i) (fun s => c s i) (U i) (f.degree i) :=
  limitVector_coe α β ε y (f.source i) (fun s => c s i) (U i) hα hβ hw hε hy (hc2 i) (hU i) (f.degree i)

theorem inputVector_tendsto (i : Fin m) :
    Tendsto (inputVector f α β ε y z a p k hα hβ hw hε hy hz ha i) (𝓝[>] 0)
      (𝓝 (inputLimitVector f α β ε y z a p k hα hβ hw hε hy hz ha i)) :=
  vector_tendsto α β ε y (f.source i) (fun s => c s i) (U i) hα hβ hw hε hy (hc i) (hc2 i) (hU i) (f.degree i)

def regularVector (i : Fin m) (δ : ℝ) : Hilbert :=
  vector α β ε y (f.source i) (fun s => c s i) (V i) hα hβ hw hε hy (hc i) (hc2 i) (hV i) (f.degree i) δ

def regularLimitVector (i : Fin m) : Hilbert :=
  limitVector α β ε y (f.source i) (fun s => c s i) (V i) hα hβ hw hε hy (hc2 i) (hV i) (f.degree i)

theorem regularVector_coe (i : Fin m) (δ : ℝ) (hδ : 0 < δ) :
    regularVector f α β ε y z a p k hα hβ hw hε hy hz ha i δ =ᵐ[volume]
      weighted α β ε y (f.source i) (fun s => c s i) (V i) (f.degree i) δ :=
  vector_coe α β ε y (f.source i) (fun s => c s i) (V i) hα hβ hw hε hy (hc i) (hc2 i) (hV i) (f.degree i) δ hδ

theorem regularLimitVector_coe (i : Fin m) :
    regularLimitVector f α β ε y z a p k hα hβ hw hε hy hz ha i =ᵐ[volume]
      moment α β ε y (f.source i) (fun s => c s i) (V i) (f.degree i) :=
  limitVector_coe α β ε y (f.source i) (fun s => c s i) (V i) hα hβ hw hε hy (hc2 i) (hV i) (f.degree i)

theorem regularVector_tendsto (i : Fin m) :
    Tendsto (regularVector f α β ε y z a p k hα hβ hw hε hy hz ha i) (𝓝[>] 0)
      (𝓝 (regularLimitVector f α β ε y z a p k hα hβ hw hε hy hz ha i)) :=
  vector_tendsto α β ε y (f.source i) (fun s => c s i) (V i) hα hβ hw hε hy (hc i) (hc2 i) (hV i) (f.degree i)

def chargedVector (i : Fin m) (δ : ℝ) : Hilbert :=
  jetVector α β ε y (f.source i) (fun s => c s i) (W i) hα hβ hw hε hy (hc i) (hc2 i) (hW i) (f.degree i) δ

def chargedLimitVector (i : Fin m) : Hilbert :=
  limitJetVector α β ε y (f.source i) (fun s => c s i) (W i) hα hβ hw hε hy (hc2 i) (hW i) (f.degree i)

theorem chargedVector_coe (i : Fin m) (δ : ℝ) (hδ : 0 < δ) :
    chargedVector f α β ε y z a p k hα hβ hw hε hy hz ha i δ =ᵐ[volume]
      weightedJet α β ε y (f.source i) (fun s => c s i) (W i) (f.degree i) δ :=
  jetVector_coe α β ε y (f.source i) (fun s => c s i) (W i) hα hβ hw hε hy (hc i) (hc2 i) (hW i) (f.degree i) δ hδ

theorem chargedLimitVector_coe (i : Fin m) :
    chargedLimitVector f α β ε y z a p k hα hβ hw hε hy hz ha i =ᵐ[volume]
      limitJet α β ε y (f.source i) (fun s => c s i) (W i) (f.degree i) :=
  limitJetVector_coe α β ε y (f.source i) (fun s => c s i) (W i) hα hβ hw hε hy (hc2 i) (hW i) (f.degree i)

theorem chargedVector_tendsto (i : Fin m) :
    Tendsto (chargedVector f α β ε y z a p k hα hβ hw hε hy hz ha i) (𝓝[>] 0)
      (𝓝 (chargedLimitVector f α β ε y z a p k hα hβ hw hε hy hz ha i)) :=
  jetVector_tendsto α β ε y (f.source i) (fun s => c s i) (W i) hα hβ hw hε hy (hc i) (hc2 i) (hW i) (f.degree i)

def momentVector (i : Fin m) (δ : ℝ) : Hilbert :=
  vector α β ε y (f.source i) (fun s => d s i) (U i) hα hβ hw hε hy (hd i) (hd2 i) (hU i) (f.degree i) δ

def momentLimitVector (i : Fin m) : Hilbert :=
  limitVector α β ε y (f.source i) (fun s => d s i) (U i) hα hβ hw hε hy (hd2 i) (hU i) (f.degree i)

theorem momentVector_coe (i : Fin m) (δ : ℝ) (hδ : 0 < δ) :
    momentVector f α β ε y z a p k hα hβ hw hε hy hz ha i δ =ᵐ[volume]
      weighted α β ε y (f.source i) (fun s => d s i) (U i) (f.degree i) δ :=
  vector_coe α β ε y (f.source i) (fun s => d s i) (U i) hα hβ hw hε hy (hd i) (hd2 i) (hU i) (f.degree i) δ hδ

theorem momentLimitVector_coe (i : Fin m) :
    momentLimitVector f α β ε y z a p k hα hβ hw hε hy hz ha i =ᵐ[volume]
      moment α β ε y (f.source i) (fun s => d s i) (U i) (f.degree i) :=
  limitVector_coe α β ε y (f.source i) (fun s => d s i) (U i) hα hβ hw hε hy (hd2 i) (hU i) (f.degree i)

theorem momentVector_tendsto (i : Fin m) :
    Tendsto (momentVector f α β ε y z a p k hα hβ hw hε hy hz ha i) (𝓝[>] 0)
      (𝓝 (momentLimitVector f α β ε y z a p k hα hβ hw hε hy hz ha i)) :=
  vector_tendsto α β ε y (f.source i) (fun s => d s i) (U i) hα hβ hw hε hy (hd i) (hd2 i) (hU i) (f.degree i)

#print axioms momentAmplitude_continuous
#print axioms momentAmplitude_memLp
#print axioms inputVector_coe
#print axioms inputLimitVector_coe
#print axioms inputVector_tendsto
#print axioms regularVector_coe
#print axioms regularLimitVector_coe
#print axioms regularVector_tendsto
#print axioms chargedVector_coe
#print axioms chargedLimitVector_coe
#print axioms chargedVector_tendsto
#print axioms momentVector_coe
#print axioms momentLimitVector_coe
#print axioms momentVector_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredJointFourierL2Data
