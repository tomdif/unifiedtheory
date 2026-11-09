/- Actual JT outputs on the coherent span have both physical field
domains. Fourth moments are derived from the existing Gaussian envelope,
including the boundary of the closed imaginary clock strip. -/
import UnifiedTheory.Audit.KFCausalFieldWeightedShearMoments
import UnifiedTheory.Audit.KFCausalCoherentShearCompositions
import UnifiedTheory.Audit.KFCausalCoherentVacuumCommutator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoherentWeightedShearDomains
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (profile profile_smooth)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (relative scale scale_smooth scale_bound relative_bound)
open UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile
open UnifiedTheory.Audit.KFCausalImaginaryShearInterpolation (path timeAmplitude timeScale)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathBounds (envelope path_bound)
open UnifiedTheory.Audit.KFCausalGaussianFourthMoments (envelope_fourth_memLp)
open UnifiedTheory.Audit.KFCausalGaussianSecondShearDifferential (first)
open UnifiedTheory.Audit.KFCausalFieldWeightedShearMoments (weighted_first_memLp)
open UnifiedTheory.Audit.KFCausalShiftedGaussianShearDomain (shearOutput shearOutput_coe)
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare (fieldSquare fieldSquare_domain)
open UnifiedTheory.Audit.KFCausalPhysicalField (physicalField fieldSquare_domain_le_physicalField)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (shiftedOutput state_ordered_graph)
open UnifiedTheory.Audit.KFCausalCoherentShearCompositions (shiftedShearOutput shiftedOutput_shear_graph)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)

theorem profile_fourth_memLp (ε a α β p y : ℝ) (b : Fin 5 → ℂ)
    (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (i : Fin 5) :
    MemLp (fun x : Configuration => (x.2 i:ℂ)^4*
      profile (clockAmplitude ε a p y) (scale ε y) α β b x) 2 volume := by
  have hD (s : ℝ) : ‖relative ε y s‖ ≤ Real.pi/3 :=
    (relative_bound ε y s hε hy).trans ((div_le_iff₀ hε).mpr (by nlinarith))
  have he (x : Configuration) : path (clockAmplitude ε a p y) (relative ε y) α β b 1 x =
      profile (clockAmplitude ε a p y) (scale ε y) α β b x := by
    simp only [path,profile,timeAmplitude,timeScale,Complex.ofReal_one,sub_self,
      zero_mul,Complex.exp_zero,one_mul,scale,KFCausalClockFloorShearBounds.complexScale]
  have hc : Continuous (fun x : Configuration => (x.2 i:ℂ)^4*
      profile (clockAmplitude ε a p y) (scale ε y) α β b x) :=
    ((Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_snd)).pow 4).mul
      (profile_smooth _ _ (clockAmplitude_smooth ε a p y hε hy) (scale_smooth ε y hε hy) α β b).continuous
  apply (envelope_fourth_memLp _
    (KFCausalShiftedClockAmplitude.clockAmplitude_memLp ε a p y hε ha hy) α β hα hβ b i).of_le
    hc.aestronglyMeasurable
  filter_upwards [] with x
  have hp := path_bound (clockAmplitude ε a p y) (relative ε y) hD α β hα hβ hw b 1
    (by constructor <;> norm_num) x
  rw [he] at hp
  simpa only [norm_mul] using mul_le_mul_of_nonneg_left hp (norm_nonneg ((x.2 i:ℂ)^4))

theorem shearOutput_square_domain (ε a α β p y : ℝ) (b : Fin 5 → ℂ)
    (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (h : ℝ) (l : Transverse →L[ℝ] ℝ) :
    shearOutput ε a α β p y b hε ha hα hβ hw hy h ∈ (fieldSquare l).domain := by
  apply (fieldSquare_domain l _).mpr
  have hm := (weighted_first_memLp (clockAmplitude ε a p y) (scale ε y)
    (clockAmplitude_smooth ε a p y hε hy) (scale_smooth ε y hε hy)
    (Real.exp (|y|/(2*ε))) (Real.exp_pos _).le (fun s => scale_bound ε y s hε hy) α β b
    (profile_memLp ε a α β p y b hε ha hα hβ hw hy)
    (profile_fourth_memLp ε a α β p y b hε ha hα hβ hw hy) l).const_mul (-Complex.I*(h:ℂ))
  apply hm.ae_eq
  filter_upwards [shearOutput_coe ε a α β p y b hε ha hα hβ hw hy h] with x hx
  rw [hx]
  simp only [first]
  ring

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)

theorem shiftedShearOutput_square_domain (k : KFCausalEuclideanProductCoordinates.Joint 2 4)
    (l : Transverse →L[ℝ] ℝ) :
    shiftedShearOutput ε a h hε ha hh hb k ∈ (fieldSquare l).domain :=
  (fieldSquare l).domain.smul_mem _ (shearOutput_square_domain ε a _ _ _ (-h/2) _ hε ha
    (KFCausalChargeGaussianGeometry.groundWidth_positive h hh)
    (KFCausalClockFloorInvariantTrial.neutralWidth_positive h hh)
    (KFCausalClockFloorInvariantTrial.neutralWidth_bound h)
    (KFCausalClockFloorShiftedOutput.shift_bound ε h hb) h l)

include hb in
theorem actual_shear_field_domains (f : Hilbert) (hf : f ∈ coherentSpan ε a h hε ha hh)
    (g j : Hilbert) (hg : (f,g) ∈ (orderedExponential ε hε h).graph)
    (hj : (g,j) ∈ (shearMomentum h).graph) (l : Transverse →L[ℝ] ℝ) :
    j ∈ (physicalField l).domain ∧ j ∈ (fieldSquare l).domain := by
  obtain ⟨n,q,z,rfl⟩ := KFCausalCoherentSpanVacuumSign.finite_representation ε a h hε ha hh f hf
  have ht : (∑ i, z i • state ε a h hε ha hh (q i),
      ∑ i, z i • shiftedOutput ε a h hε ha hh hb (q i)) ∈ (orderedExponential ε hε h).graph := by
    have hs := (orderedExponential ε hε h).graph.sum_mem
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => (orderedExponential ε hε h).graph.smul_mem
        (z i) (state_ordered_graph ε a h hε ha hh hb (q i)))
    simpa only [Prod.smul_mk,← prod_mk_sum] using hs
  have hjs : (∑ i, z i • shiftedOutput ε a h hε ha hh hb (q i),
      ∑ i, z i • shiftedShearOutput ε a h hε ha hh hb (q i)) ∈ (shearMomentum h).graph := by
    have hs := (shearMomentum h).graph.sum_mem
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => (shearMomentum h).graph.smul_mem
        (z i) (shiftedOutput_shear_graph ε a h hε ha hh hb (q i)))
    simpa only [Prod.smul_mk,← prod_mk_sum] using hs
  have eg := (orderedExponential ε hε h).mem_graph_snd_inj' hg ht rfl
  have ej := (shearMomentum h).mem_graph_snd_inj' hj hjs eg
  dsimp only at ej
  have hd : j ∈ (fieldSquare l).domain := by
    rw [ej]
    exact (fieldSquare l).domain.sum_mem (fun i _ => (fieldSquare l).domain.smul_mem (z i)
      (shiftedShearOutput_square_domain ε a h hε ha hh hb (q i) l))
  exact ⟨fieldSquare_domain_le_physicalField l hd,hd⟩

#print axioms profile_fourth_memLp
#print axioms shearOutput_square_domain
#print axioms shiftedShearOutput_square_domain
#print axioms actual_shear_field_domains
end
end UnifiedTheory.Audit.KFCausalCoherentWeightedShearDomains
