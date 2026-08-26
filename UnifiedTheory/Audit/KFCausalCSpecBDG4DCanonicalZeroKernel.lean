/-
  Audit/KFCausalCSpecBDG4DCanonicalZeroKernel.lean

  A CONCRETE UNIT-SUPPORT 4D BDG KERNEL INPUT

  The Gate-4 operator interface previously accepted an arbitrary split kernel
  package.  This file proves one reusable kernel-only estimate: on the unit
  active lightcone rectangle, the committed 4D smearing function gives

      |(v-u)^2 f4D(a u^2 v^2)| <= 9.

  It then combines that genuine estimate with the identically-zero smooth
  compactly supported profile.  The resulting operator package is completely
  explicit and has mean and target zero.  It is a non-vacuous certificate for
  the analytic interface, but only for the zero test profile; it is not a claim
  that the microscopic harmonic history supplies a physical continuum field.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecRecoveredStageBDG4DConeBound
import UnifiedTheory.Audit.KFCausalMinkowski4DRealModes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable

open Filter Topology
open UnifiedTheory.Audit.KFCausalMinkowski4DMoments
open UnifiedTheory.Audit.KFCausalMinkowski4DRealModes

/-- Unit support and zero profile bounds. -/
def canonicalZeroBDG4DScales : BDG4DOperatorProfileScales where
  uSupport := 1
  vSupport := 1
  profileBound := 0
  profileDerivBound := 0
  mixedBound := 0
  mixedUDerivBound := 0
  mixedVDerivBound := 0
  coneBound := 0
  huSupport_pos := by norm_num
  hvSupport_pos := by norm_num

/-- The identically-zero profile and all of its displayed derivatives. -/
def canonicalZeroBDG4DFunctions : BDG4DOperatorProfileFunctions where
  mbar := fun _ _ => 0
  profile := fun _ _ => 0
  profileU := fun _ _ => 0
  profileUV := fun _ _ => 0
  profileUVU := fun _ _ => 0
  profileUVV := fun _ _ => 0
  profileUU := fun _ => 0
  profileVV := fun _ => 0
  profile_def := by simp
  even_mbar := by simp

/-- Smoothness and derivative identities of the zero profile. -/
def canonicalZeroBDG4DRegularity :
    BDG4DOperatorProfileRegularity canonicalZeroBDG4DFunctions where
  profile_cont := by fun_prop
  profileU_cont := by fun_prop
  profileUV_cont := by fun_prop
  profile_deriv_u := by
    intro v u
    simpa [canonicalZeroBDG4DFunctions] using
      (hasDerivAt_const u (0 : ℝ))
  profileU_deriv_v := by
    intro u v
    simpa [canonicalZeroBDG4DFunctions] using
      (hasDerivAt_const v (0 : ℝ))
  profileUV_deriv_u := by
    intro v u
    simpa [canonicalZeroBDG4DFunctions] using
      (hasDerivAt_const u (0 : ℝ))
  profileUV_deriv_v := by
    intro u v
    simpa [canonicalZeroBDG4DFunctions] using
      (hasDerivAt_const v (0 : ℝ))
  profileVV_deriv := by
    intro u
    simpa [canonicalZeroBDG4DFunctions] using
      (hasDerivAt_const u (0 : ℝ))
  profileUU_deriv := by
    intro v
    simpa [canonicalZeroBDG4DFunctions] using
      (hasDerivAt_const v (0 : ℝ))
  profileUVV_axis_cont := by fun_prop
  profileUVU_axis_cont := by fun_prop

/-- Every uniform profile bound is exact for the zero profile. -/
def canonicalZeroBDG4DUniformBounds :
    BDG4DOperatorProfileUniformBounds
      canonicalZeroBDG4DScales canonicalZeroBDG4DFunctions where
  profile_bound := by simp [canonicalZeroBDG4DScales, canonicalZeroBDG4DFunctions]
  profileU_bound := by simp [canonicalZeroBDG4DScales, canonicalZeroBDG4DFunctions]
  profileUV_bound := by simp [canonicalZeroBDG4DScales, canonicalZeroBDG4DFunctions]
  profileUVU_bound := by simp [canonicalZeroBDG4DScales, canonicalZeroBDG4DFunctions]
  profileUVV_bound := by simp [canonicalZeroBDG4DScales, canonicalZeroBDG4DFunctions]

/-- The zero profile obeys every upper support condition. -/
def canonicalZeroBDG4DSupport :
    BDG4DOperatorProfileSupport
      canonicalZeroBDG4DScales canonicalZeroBDG4DFunctions where
  profile_support_u := by simp [canonicalZeroBDG4DFunctions]
  profile_support_v := by simp [canonicalZeroBDG4DFunctions]
  profileU_support_u := by simp [canonicalZeroBDG4DFunctions]
  profileU_support_v := by simp [canonicalZeroBDG4DFunctions]
  profileUV_support_u := by simp [canonicalZeroBDG4DFunctions]
  profileUV_support_v := by simp [canonicalZeroBDG4DFunctions]
  profileVV_support := by simp [canonicalZeroBDG4DFunctions]
  profileUU_support := by simp [canonicalZeroBDG4DFunctions]

/-- The zero profile also obeys the lower lightcone support conditions. -/
def canonicalZeroBDG4DLightconeSupport :
    BDG4DOperatorProfileLightconeSupport canonicalZeroBDG4DFunctions where
  profile_support_u_neg := by simp [canonicalZeroBDG4DFunctions]
  profile_support_v_neg := by simp [canonicalZeroBDG4DFunctions]

/-- The committed global estimate `|f4D z| <= 9` gives an explicit weighted
kernel bound on the unit active rectangle. -/
def canonicalUnitBDG4DWeightedKernelBound :
    BDG4DWeightedKernelActiveBound canonicalZeroBDG4DScales where
  activeWeightedConeBound := 9
  activeWeightedConeBound_nonneg := by norm_num
  weighted_f4D_bound := by
    intro a ha u v hu hv hu_one hv_one
    change u < 1 at hu_one
    change v < 1 at hv_one
    have hz : 0 ≤ a * u ^ 2 * v ^ 2 := by positivity
    have hf : |f4D (a * u ^ 2 * v ^ 2)| ≤ 9 :=
      f4D_abs_le _ hz
    have hdiff_lower : -1 ≤ v - u := by linarith
    have hdiff_upper : v - u ≤ 1 := by linarith
    have hsq : (v - u) ^ 2 ≤ 1 := by nlinarith
    rw [abs_mul, abs_sq]
    calc
      (v - u) ^ 2 * |f4D (a * u ^ 2 * v ^ 2)| ≤ 1 * 9 :=
        mul_le_mul hsq hf (abs_nonneg _) (by norm_num)
      _ = 9 := by norm_num

/-- A fully explicit split Gate-4 operator input.  Its kernel bound is genuine;
its selected continuum test profile is the zero profile. -/
noncomputable def canonicalZeroBDG4DKernelData :
    BDG4DOperatorProfileKernelSplitData where
  scales := canonicalZeroBDG4DScales
  functions := canonicalZeroBDG4DFunctions
  regularity := canonicalZeroBDG4DRegularity
  uniformBounds := canonicalZeroBDG4DUniformBounds
  support := canonicalZeroBDG4DSupport
  lightconeSupport := canonicalZeroBDG4DLightconeSupport
  kernelBound := canonicalUnitBDG4DWeightedKernelBound
  coneBound_ge := by
    norm_num [canonicalUnitBDG4DWeightedKernelBound,
      canonicalZeroBDG4DScales]

/-- The explicit zero-profile target is zero. -/
theorem canonicalZeroBDG4D_target_eq_zero :
    BDG4DOperatorProfileData.target
      canonicalZeroBDG4DKernelData.toProfileData = 0 := by
  simp [BDG4DOperatorProfileData.target,
    BDG4DOperatorProfileKernelSplitData.toProfileData,
    BDG4DOperatorProfileKernelSplitData.toSplitData,
    BDG4DOperatorProfileSplitData.toProfileData,
    canonicalZeroBDG4DKernelData, canonicalZeroBDG4DFunctions]

/-- Minimal anti-vacuity diagnostic for a benchmark that is meant to recover a
nonzero continuum operator target.  This is deliberately not advertised as a
complete definition of physicality: a physical test observable can have zero
d'Alembertian.  It does, however, rule out using an identically-zero profile as
evidence for recovery of a specified nonzero target. -/
def HasNonzeroBDG4DTarget
    (data : BDG4DOperatorProfileKernelSplitData) : Prop :=
  BDG4DOperatorProfileData.target data.toProfileData ≠ 0

/-- The canonical zero-profile package is only an interface-consistency
benchmark: it fails the nonzero-target diagnostic exactly. -/
theorem canonicalZeroBDG4D_not_hasNonzeroTarget :
    ¬ HasNonzeroBDG4DTarget canonicalZeroBDG4DKernelData := by
  intro h
  exact h canonicalZeroBDG4D_target_eq_zero

/-- Its reduced operator mean is identically zero at every sampling scale. -/
theorem canonicalZeroBDG4D_mean_eq_zero (a : ℝ) :
    BDG4DOperatorProfileData.mean
      canonicalZeroBDG4DKernelData.toProfileData a = 0 := by
  simp [BDG4DOperatorProfileData.mean,
    BDG4DOperatorProfileKernelSplitData.toProfileData,
    BDG4DOperatorProfileKernelSplitData.toSplitData,
    BDG4DOperatorProfileSplitData.toProfileData,
    canonicalZeroBDG4DKernelData, canonicalZeroBDG4DFunctions]

/-- Consequently every sampling sequence has the zero operator limit, without
an extra analytic supplier. -/
theorem canonicalZeroBDG4D_sampled_tendsto (density : ℕ → ℝ) :
    Tendsto
      (fun n => BDG4DOperatorProfileData.mean
        canonicalZeroBDG4DKernelData.toProfileData (density n))
      atTop (𝓝 0) := by
  simpa [canonicalZeroBDG4D_mean_eq_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

#print axioms canonicalUnitBDG4DWeightedKernelBound
#print axioms canonicalZeroBDG4DKernelData
#print axioms canonicalZeroBDG4D_target_eq_zero
#print axioms canonicalZeroBDG4D_not_hasNonzeroTarget
#print axioms canonicalZeroBDG4D_mean_eq_zero
#print axioms canonicalZeroBDG4D_sampled_tendsto

end UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
