/- Exact occupation counting inside the actual zero-charge index set.
This counts charged modes; the two continuous spectator variables remain. -/
import UnifiedTheory.Audit.KFCausalCircularChargeDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCircularZeroLevelCounting
noncomputable section
open KFCausalHermiteProductBasis (Index)
open KFCausalFourCircularChargeBasis (charge)

def positiveCount (i : Index) : ℕ := i.1.1+i.2.1
def negativeCount (i : Index) : ℕ := i.1.2+i.2.2
def occupation (i : Index) : ℕ := positiveCount i+negativeCount i

theorem charge_zero_iff (i : Index) : charge i = 0 ↔ positiveCount i = negativeCount i := by
  simp only [charge, positiveCount, negativeCount]
  omega

def Level (p : ℕ) := {i : Index // charge i = 0 ∧ positiveCount i = p}

def levelEquiv (p : ℕ) : Level p ≃ (Fin (p+1) × Fin (p+1)) where
  toFun i :=
    (⟨i.val.1.1, by
      have h := i.property.2
      simp only [positiveCount] at h
      omega⟩,
     ⟨i.val.1.2, by
      have h := (charge_zero_iff i.val).mp i.property.1
      have hp := i.property.2
      simp only [positiveCount, negativeCount] at h hp
      omega⟩)
  invFun j := ⟨((j.1.val, j.2.val), (p-j.1.val, p-j.2.val)), by
    rw [charge_zero_iff]
    simp only [positiveCount, negativeCount]
    have ha := j.1.isLt
    have hb := j.2.isLt
    omega⟩
  left_inv i := by
    apply Subtype.ext
    have h := (charge_zero_iff i.val).mp i.property.1
    have hp := i.property.2
    simp only [positiveCount, negativeCount] at h hp
    apply Prod.ext <;> apply Prod.ext <;> simp only <;> omega
  right_inv j := by
    apply Prod.ext <;> apply Fin.ext <;> rfl

instance (p : ℕ) : Fintype (Level p) := Fintype.ofEquiv _ (levelEquiv p).symm

theorem level_card (p : ℕ) : Fintype.card (Level p) = (p+1)^2 := by
  rw [Fintype.card_congr (levelEquiv p), Fintype.card_prod, Fintype.card_fin]
  ring

theorem level_occupation (p : ℕ) (i : Level p) : occupation i.val = 2*p := by
  have h := (charge_zero_iff i.val).mp i.property.1
  simp only [occupation, ← h, i.property.2]
  omega

#print axioms levelEquiv
#print axioms level_card
#print axioms level_occupation
end
end UnifiedTheory.Audit.KFCausalCircularZeroLevelCounting
