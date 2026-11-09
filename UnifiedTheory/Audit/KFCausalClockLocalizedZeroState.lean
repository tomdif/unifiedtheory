/- Nonzero physical charge-zero targets with compact log-clock support.
These targets need not lie in the Hamiltonian energy domain. Subsequent
approximation in that domain must be proved separately. -/
import UnifiedTheory.Audit.KFCausalPhysicalGaussianCharge
import UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
import Mathlib.MeasureTheory.Function.ContinuousMapDense

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockLocalizedZeroState
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianCharge
open UnifiedTheory.Audit.KFCausalChargeGaussianIdentities
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalStandingChargeOperator
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator

def bump (S s : ℝ) : ℂ := (max 0 (1 - |s - (S+2)|) : ℝ)

theorem bump_continuous (S : ℝ) : Continuous (bump S) := by
  unfold bump
  fun_prop

theorem bump_zero_outside (S s : ℝ) (hs : s ∉ Set.Icc (S+1) (S+3)) : bump S s = 0 := by
  have h : 1 ≤ |s-(S+2)| := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hs
    rcases hs with hs | hs
    · have h := neg_le_abs (s-(S+2))
      linarith
    · have h := le_abs_self (s-(S+2))
      linarith
  simp only [bump, max_eq_left (by linarith : 1-|s-(S+2)| ≤ 0), Complex.ofReal_zero]

theorem bump_memLp (S : ℝ) : MemLp (bump S) 2 volume :=
  (bump_continuous S).memLp_of_hasCompactSupport
    (HasCompactSupport.intro isCompact_Icc (bump_zero_outside S))

def target (hbar : ℝ) (hh : hbar ≠ 0) (S : ℝ) : Hilbert :=
  groundState hbar hh 1 zero_lt_one (bump S) (bump_continuous S) (bump_memLp S)

theorem target_coe (hbar : ℝ) (hh : hbar ≠ 0) (S : ℝ) :
    target hbar hh S =ᵐ[volume] configurationProfile (groundWidth hbar) 1 (bump S) :=
  groundState_coe _ _ _ _ _ _ _

theorem target_zero_sector (hbar : ℝ) (hh : hbar ≠ 0) (S : ℝ) :
    target hbar hh S ∈ zeroSector hbar hh :=
  groundState_mem_zeroSector _ _ _ _ _ _ _

theorem target_supported (hbar : ℝ) (hh : hbar ≠ 0) (S : ℝ) :
    ∀ᵐ x ∂volume, x.1 < S → target hbar hh S x = 0 := by
  filter_upwards [target_coe hbar hh S] with x hx hs
  rw [hx, configurationProfile, bump_zero_outside S x.1 (by
    simp only [Set.mem_Icc, not_and_or, not_le]; left; linarith), zero_mul]

theorem target_ne_zero (hbar : ℝ) (hh : hbar ≠ 0) (S : ℝ) : target hbar hh S ≠ 0 := by
  intro hz
  have hc := target_coe hbar hh S
  rw [hz] at hc
  have he : configurationProfile (groundWidth hbar) 1 (bump S) =ᵐ[volume] fun _ => (0:ℂ) := by
    filter_upwards [hc, Lp.coeFn_zero ℂ 2 (volume : Measure Configuration)] with x hx h0
    exact hx.symm.trans h0
  have h := congrFun (Measure.eq_of_ae_eq he
    (configurationProfile_continuous _ _ _ (bump_continuous S)) continuous_const) (S+2,0)
  simp [configurationProfile, bump, KFCausalClockFloorShearBounds.physicalGaussian] at h

theorem exists_unit_localized_zero (hbar : ℝ) (hh : hbar ≠ 0) (S : ℝ) :
    ∃ f : Hilbert, ‖f‖ = 1 ∧ f ∈ zeroSector hbar hh ∧
      (∀ᵐ x ∂volume, x.1 < S → f x = 0) := by
  let f := target hbar hh S
  let c : ℂ := (‖f‖⁻¹ : ℝ)
  have hn : ‖c • f‖ = 1 := by
    rw [norm_smul]
    simp only [c, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (target_ne_zero hbar hh S))
  refine ⟨c • f, hn,
    (zeroSector hbar hh).smul_mem c (target_zero_sector hbar hh S), ?_⟩
  filter_upwards [Lp.coeFn_smul c f, target_supported hbar hh S] with x hx hs hlow
  rw [hx]
  change c • f x = 0
  rw [show f x = 0 from hs hlow, smul_zero]

#print axioms bump_continuous
#print axioms bump_zero_outside
#print axioms bump_memLp
#print axioms target_coe
#print axioms target_zero_sector
#print axioms target_supported
#print axioms target_ne_zero
#print axioms exists_unit_localized_zero

end
end UnifiedTheory.Audit.KFCausalClockLocalizedZeroState
