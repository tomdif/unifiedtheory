/- The actual circular zero-charge shells have an Euler character.
Its first excitation already excludes the unmodified Watson R1 characters. -/
import UnifiedTheory.Audit.KFCausalFreeCircularSpectralDomain
import UnifiedTheory.Audit.KFCausalFreeChargedNormalForm
import UnifiedTheory.LayerA.WatsonSeriesBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalPhysicalChargedCharacter
noncomputable section
open PowerSeries
open KFCausalCircularZeroLevelCounting
open UnifiedTheory.QSeries.Watson

def character : PowerSeries ℤ := PowerSeries.mk fun p => (Fintype.card (Level p):ℤ)

theorem coefficient (p : ℕ) : coeff p character = ((p+1:ℕ)^2:ℤ) := by
  rw [character,coeff_mk,level_card]
  push_cast
  ring

theorem character_eq_euler : character = KFCausalFreeChargedNormalForm.chargedPairSeries := by
  ext p
  rw [coefficient,KFCausalFreeChargedNormalForm.coeff_chargedPairSeries,
    KFCausalFreeChargedNormalForm.balanced_charged_count]
  push_cast
  ring

theorem first_excitation : coeff 1 character = 4 := by rw [coefficient]; norm_num

private theorem inverse_FP_constant (a b n : ℕ) (ha : 0 < a) :
    coeff 0 (Ring.inverse (FP 1 a b n)) = 1 := by
  have hf : constantCoeff (FP 1 a b n) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact (coeff_of_dvd_sub (FP_sub_one_dvd 1 a b n) ha).trans (by simp)
  have he := congrArg (constantCoeff (R := ℤ))
    (Ring.mul_inverse_cancel (FP 1 a b n) (isUnit_FP 1 ha b n))
  simpa only [map_mul,map_one,hf,one_mul,coeff_zero_eq_constantCoeff_apply] using he

theorem chi_first : coeff 1 chiA = 1 := by
  rw [chiA,coeff_osum]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range 2) (by
    intro n hn
    apply Finset.mem_range.mpr
    by_contra hh
    have he : coeff 1 (X^n*Ring.inverse (FP 1 (n+1) 1 n)) = 0 := by
      rw [coeff_X_pow_mul',if_neg (by omega)]
    exact hn he)]
  norm_num [Finset.sum_range_succ,coeff_X_pow_mul',FP_zero,Ring.inverse_one,
    inverse_FP_constant]

theorem F0_first : coeff 1 F0w = 0 := by
  rw [F0w,coeff_osum]
  have hz (n : ℕ) : coeff 1 (X^(2*(n*n))*Ring.inverse (FP 1 1 2 n)) = 0 := by
    cases n with
    | zero => simp [FP_zero]
    | succ n => rw [coeff_X_pow_mul',if_neg (by nlinarith)]
  simp only [hz,finsum_zero]

theorem P0_first : coeff 1 P0w = -1 := by
  have he := UnifiedTheory.LayerA.WatsonSeriesBridge.chi0_R1_coeff 1
  rw [chi_first,F0_first] at he
  omega

theorem character_ne_chi : character ≠ chiA := by
  intro he
  have h := congrArg (coeff 1) he
  rw [first_excitation,chi_first] at h
  norm_num at h

theorem character_ne_F0 : character ≠ F0w := by
  intro he
  have h := congrArg (coeff 1) he
  rw [first_excitation,F0_first] at h
  norm_num at h

theorem character_ne_P0 : character ≠ P0w := by
  intro he
  have h := congrArg (coeff 1) he
  rw [first_excitation,P0_first] at h
  norm_num at h

theorem character_ne_R1_combination : character ≠ 2*F0w-P0w := by
  rw [← UnifiedTheory.LayerA.WatsonSeriesBridge.chi0_R1]
  exact character_ne_chi

#print axioms character_eq_euler
#print axioms chi_first
#print axioms F0_first
#print axioms P0_first
#print axioms character_ne_R1_combination
end
end UnifiedTheory.Audit.KFCausalPhysicalChargedCharacter
