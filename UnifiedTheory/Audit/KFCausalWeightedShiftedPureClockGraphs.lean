/- Constructed pure-clock graphs for weighted shifted sourced Gaussians.
The derivative output is a finite sum of controlled Gaussian moments;
both input and output are continuous along bounded source curves. -/
import UnifiedTheory.Audit.KFCausalShiftedSourceWeightedContinuity
import UnifiedTheory.Audit.KFCausalWeightedShiftedPureClockCalculus
import UnifiedTheory.Audit.KFCausalFiniteLpRepresentatives

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalWeightedShiftedPureClockGraphs
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalRadialMultipliers
open KFCausalRelativeGaussianDifferential (profile)
open KFCausalClockFloorRelativeShift (scale argument)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude clockAmplitude_smooth)
open KFCausalShiftedGaussianPureDifferential (realInverse)
open KFCausalWeightedShiftedPureClockCalculus
open KFCausalClockFloorPureClockDerivative (differential)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalCanonicalClockDerivative (clockDerivative)
open KFCausalClockFloorCoherentBounds (sourceSize)

variable (ε a α β p y : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3)
local notation "A" => clockAmplitude ε a p y
local notation "hA" => clockAmplitude_smooth ε a p y hε hy
local notation "hAm" => KFCausalShiftedClockAmplitude.clockAmplitude_memLp ε a p y hε ha hy
local notation "A₁" => (fun s => argument ε y s*clockAmplitude ε a p y s)
local notation "hA₁" => ContDiff.mul (KFCausalClockFloorRelativeShift.argument_smooth ε y) hA
local notation "hAm₁" => KFCausalShiftedGaussianRadialMoments.amplitude_moment_memLp ε a p y hε ha hy
local notation "F" => profile A (scale ε y) α β

def vector (m : Configuration → ℂ) (hm : Controlled m) (b : Fin 5 → ℂ) : Hilbert :=
  KFCausalShiftedSourceWeightedContinuity.state ε y α β A m hε hy hα hβ hw hA hAm hm 1 b
def momentVector (m : Configuration → ℂ) (hm : Controlled m) (b : Fin 5 → ℂ) : Hilbert :=
  KFCausalShiftedSourceWeightedContinuity.state ε y α β A₁ m hε hy hα hβ hw hA₁ hAm₁ hm 1 b

theorem vector_coe (m : Configuration → ℂ) (hm : Controlled m) (b : Fin 5 → ℂ) :
    vector ε a α β p y hε ha hα hβ hw hy m hm b =ᵐ[volume] fun x => m x*F b x := by
  filter_upwards [KFCausalShiftedSourceWeightedContinuity.state_coe ε y α β A m
    hε hy hα hβ hw hA hAm hm 1 b] with x hx
  simpa only [vector,KFCausalShiftedSourceWeightedContinuity.weighted,one_mul] using hx

theorem momentVector_coe (m : Configuration → ℂ) (hm : Controlled m) (b : Fin 5 → ℂ) :
    momentVector ε a α β p y hε ha hα hβ hw hy m hm b =ᵐ[volume]
      fun x => m x*(argument ε y x.1*F b x) := by
  filter_upwards [KFCausalShiftedSourceWeightedContinuity.state_coe ε y α β A₁ m
    hε hy hα hβ hw hA₁ hAm₁ hm 1 b] with x hx
  change momentVector ε a α β p y hε ha hα hβ hw hy m hm b x = _ at hx
  rw [hx]
  unfold KFCausalShiftedSourceWeightedContinuity.weighted profile
  ring

variable (m R : Configuration → ℂ) (hm : Controlled m) (hR : Controlled R)
local notation "m₀" => (fun x => R x+m x*baseCoefficient ε α β p y x)
local notation "hm₀" => controlled_add _ _ hR (controlled_mul _ _ hm (baseCoefficient_controlled ε α β p y hε hy))
local notation "mᵢ" => (fun i x => m x*sourceCoefficient ε y i x)
local notation "hmᵢ" => (fun i => controlled_mul _ _ hm (sourceCoefficient_controlled ε y hε hy i))
local notation "V" => vector ε a α β p y hε ha hα hβ hw hy
local notation "W" => momentVector ε a α β p y hε ha hα hβ hw hy

def preOutput (b : Fin 5 → ℂ) : Hilbert :=
  V m₀ hm₀ b+∑ i, b i • V (mᵢ i) (hmᵢ i) b-(2*(a:ℂ)) • W m hm b
def input (C : ℂ) (b : Fin 5 → ℂ) : Hilbert := C • V m hm b
def output (h : ℝ) (C : ℂ) (b : Fin 5 → ℂ) : Hilbert :=
  C • ((-Complex.I*(h:ℂ)) • preOutput ε a α β p y hε ha hα hβ hw hy m R hm hR b)

theorem input_coe (C : ℂ) (b : Fin 5 → ℂ) :
    input ε a α β p y hε ha hα hβ hw hy m hm C b =ᵐ[volume] fun x => C*(m x*F b x) := by
  filter_upwards [Lp.coeFn_smul C (V m hm b),vector_coe ε a α β p y hε ha hα hβ hw hy m hm b]
    with x hc hv
  simpa only [input,Pi.smul_apply,smul_eq_mul,hv] using hc

variable (hmd : Differentiable ℝ m) (hRate : ∀ x, realInverse ε x.1*clockDerivative m x = R x)

include hmd hRate in
theorem preOutput_coe (b : Fin 5 → ℂ) :
    preOutput ε a α β p y hε ha hα hβ hw hy m R hm hR b =ᵐ[volume]
      differential ε (fun x => m x*F b x) := by
  have hs := KFCausalFiniteLpRepresentatives.weighted_sum_coe volume b
    (fun i => V (mᵢ i) (hmᵢ i) b) (fun i x => mᵢ i x*F b x)
    (fun i => vector_coe ε a α β p y hε ha hα hβ hw hy (mᵢ i) (hmᵢ i) b)
  filter_upwards [Lp.coeFn_sub (V m₀ hm₀ b+∑ i, b i • V (mᵢ i) (hmᵢ i) b) ((2*(a:ℂ)) • W m hm b),
    Lp.coeFn_add (V m₀ hm₀ b) (∑ i, b i • V (mᵢ i) (hmᵢ i) b),
    Lp.coeFn_smul (2*(a:ℂ)) (W m hm b),vector_coe ε a α β p y hε ha hα hβ hw hy m₀ hm₀ b,
    momentVector_coe ε a α β p y hε ha hα hβ hw hy m hm b,hs] with x hsub hadd hsm hbase hmoment hsum
  change preOutput ε a α β p y hε ha hα hβ hw hy m R hm hR b x = _ at hsub
  simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hsub hadd hsm
  rw [hsub,hadd,hsm,hbase,hmoment,hsum]
  exact (weighted_differential ε a α β p y b hε hy m R hmd hRate x).symm

include hmd hRate in
theorem graph (h : ℝ) (hh : h ≠ 0) (C : ℂ) (b : Fin 5 → ℂ) :
    (input ε a α β p y hε ha hα hβ hw hy m hm C b,
      output ε a α β p y hε ha hα hβ hw hy m R hm hR h C b) ∈
      (pureMomentum ε hε h).graph := by
  have hf : MemLp (fun x => m x*F b x) 2 volume :=
    (Lp.memLp (V m hm b)).ae_eq (vector_coe ε a α β p y hε ha hα hβ hw hy m hm b)
  have hd : MemLp (differential ε (fun x => m x*F b x)) 2 volume :=
    (Lp.memLp (preOutput ε a α β p y hε ha hα hβ hw hy m R hm hR b)).ae_eq
      (preOutput_coe ε a α β p y hε ha hα hβ hw hy m R hm hR hmd hRate b)
  have hi : hf.toLp (fun x => m x*F b x) = V m hm b :=
    Lp.ext (hf.coeFn_toLp.trans (vector_coe ε a α β p y hε ha hα hβ hw hy m hm b).symm)
  have ho : hd.toLp (differential ε (fun x => m x*F b x)) =
      preOutput ε a α β p y hε ha hα hβ hw hy m R hm hR b :=
    Lp.ext (hd.coeFn_toLp.trans (preOutput_coe ε a α β p y hε ha hα hβ hw hy m R hm hR hmd hRate b).symm)
  have hg := KFCausalClockFloorPureClockDifferential.differential_graph ε hε h hh _ hf hd
    (hmd.mul ((KFCausalRelativeGaussianDifferential.profile_smooth _ _ hA
      (KFCausalClockFloorRelativeShift.scale_smooth ε y hε hy) α β b).differentiable (by norm_num)))
  rw [hi,ho] at hg
  exact (pureMomentum ε hε h).graph.smul_mem C hg

omit R hR hmd hRate in
theorem input_continuous (B : ℝ) (C : ℝ → ℂ) (b : ℝ → Fin 5 → ℂ)
    (hCc : Continuous C) (hbc : Continuous b) (hbB : ∀ θ, sourceSize (b θ) ≤ B) :
    Continuous (fun θ => input ε a α β p y hε ha hα hβ hw hy m hm (C θ) (b θ)) :=
  hCc.smul (KFCausalShiftedSourceWeightedContinuity.state_curve_continuous ε y α β A m
    hε hy hα hβ hw hA hAm hm B (fun _ => 1) b continuous_const hbc (fun _ => by simp) hbB)

omit hmd hRate in
theorem output_continuous (B : ℝ) (C : ℝ → ℂ) (b : ℝ → Fin 5 → ℂ)
    (hCc : Continuous C) (hbc : Continuous b) (hbB : ∀ θ, sourceSize (b θ) ≤ B) (h : ℝ) :
    Continuous (fun θ => output ε a α β p y hε ha hα hβ hw hy m R hm hR h (C θ) (b θ)) := by
  have hV (q : Configuration → ℂ) (hq : Controlled q) : Continuous (fun θ => V q hq (b θ)) :=
    KFCausalShiftedSourceWeightedContinuity.state_curve_continuous ε y α β A q
      hε hy hα hβ hw hA hAm hq B (fun _ => 1) b continuous_const hbc (fun _ => by simp) hbB
  have hW : Continuous (fun θ => W m hm (b θ)) :=
    KFCausalShiftedSourceWeightedContinuity.state_curve_continuous ε y α β A₁ m
      hε hy hα hβ hw hA₁ hAm₁ hm B (fun _ => 1) b continuous_const hbc (fun _ => by simp) hbB
  have hs : Continuous (fun θ => ∑ i, b θ i • V (mᵢ i) (hmᵢ i) (b θ)) :=
    continuous_finset_sum _ (fun i _ => ((continuous_apply i).comp hbc).smul (hV (mᵢ i) (hmᵢ i)))
  exact hCc.smul (continuous_const.smul (((hV m₀ hm₀).add hs).sub (continuous_const.smul hW)))

#print axioms vector_coe
#print axioms momentVector_coe
#print axioms input_coe
#print axioms preOutput_coe
#print axioms graph
#print axioms input_continuous
#print axioms output_continuous
end
end UnifiedTheory.Audit.KFCausalWeightedShiftedPureClockGraphs
