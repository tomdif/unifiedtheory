/- Exact coordinates for disjoint two-vertex cells on a periodic lattice.
Fine coordinates split into a coarse coordinate and a binary offset. -/
import UnifiedTheory.Clay.YangMills.PeriodicHalfGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.DyadicCellCoordinates
noncomputable section

variable (m : ℕ) [NeZero m]

def coarse (x : ZMod (2 * m)) : ZMod m := (x.val / 2 : ℕ)
def bit (x : ZMod (2 * m)) : Fin 2 := ⟨x.val % 2,Nat.mod_lt _ (by decide)⟩
def join (x : ZMod m) (b : Fin 2) : ZMod (2 * m) := (2 * x.val + b.val : ℕ)

theorem coarse_val (x : ZMod (2 * m)) : (coarse m x).val = x.val / 2 := by
  have hx := x.val_lt
  exact ZMod.val_natCast_of_lt (by omega)

theorem join_val (x : ZMod m) (b : Fin 2) : (join m x b).val = 2 * x.val + b.val := by
  have hx := x.val_lt
  have hb := b.isLt
  exact ZMod.val_natCast_of_lt (by omega)

theorem coarse_join (x : ZMod m) (b : Fin 2) : coarse m (join m x b) = x := by
  unfold coarse
  rw [join_val]
  have hb := b.isLt
  have he : (2 * x.val + b.val) / 2 = x.val := by omega
  rw [he, ZMod.natCast_zmod_val]

theorem bit_join (x : ZMod m) (b : Fin 2) : bit m (join m x b) = b := by
  apply Fin.ext
  change (join m x b).val % 2 = b.val
  rw [join_val]
  have hb := b.isLt
  omega

theorem join_split (x : ZMod (2 * m)) : join m (coarse m x) (bit m x) = x := by
  apply ZMod.val_injective
  rw [join_val, coarse_val]
  change 2 * (x.val / 2) + x.val % 2 = x.val
  omega

def equiv : ZMod m × Fin 2 ≃ ZMod (2 * m) where
  toFun xb := join m xb.1 xb.2
  invFun x := (coarse m x,bit m x)
  left_inv xb := Prod.ext (coarse_join m xb.1 xb.2) (bit_join m xb.1 xb.2)
  right_inv := join_split m

def lift (x : ZMod m) : ZMod (2 * m) := join m x 0

theorem join_add (x s : ZMod m) (b : Fin 2) :
    join m (x + s) b = join m x b + lift m s := by
  have he : ((2 * (x + s).val : ℕ) : ZMod (2 * m)) =
      ((2 * (x.val + s.val) : ℕ) : ZMod (2 * m)) := by
    rw [ZMod.val_add, ← Nat.mul_mod_mul_left, ZMod.natCast_mod]
  change ((2 * (x + s).val + b.val : ℕ) : ZMod (2 * m)) =
    ((2 * x.val + b.val : ℕ) : ZMod (2 * m)) + ((2 * s.val + 0 : ℕ) : ZMod (2 * m))
  push_cast at he ⊢
  rw [he]
  ring

theorem coarse_add_lift (x : ZMod (2 * m)) (s : ZMod m) :
    coarse m (x + lift m s) = coarse m x + s := by
  conv_lhs => rw [← join_split m x, ← join_add]
  rw [coarse_join]

theorem bit_add_lift (x : ZMod (2 * m)) (s : ZMod m) : bit m (x + lift m s) = bit m x := by
  conv_lhs => rw [← join_split m x, ← join_add]
  rw [bit_join]

theorem coarse_reflect (x : ZMod (2 * m)) :
    coarse m (-(x + 1)) = -(coarse m x + 1) := by
  apply ZMod.val_injective
  rw [coarse_val, PeriodicHalfGeometry.val_neg_add_one,
    PeriodicHalfGeometry.val_neg_add_one, coarse_val]
  have hx := x.val_lt
  omega

theorem bit_reflect_val (x : ZMod (2 * m)) : (bit m (-(x + 1))).val = 1 - (bit m x).val := by
  change (-(x + 1)).val % 2 = 1 - x.val % 2
  rw [PeriodicHalfGeometry.val_neg_add_one]
  have hx := x.val_lt
  omega

theorem succ_val (x : ZMod (2 * m)) : (x + 1).val = (x.val + 1) % (2 * m) := by
  rw [ZMod.val_add, ZMod.val_one'' (by have hm := NeZero.pos m; omega)]

theorem bit_succ_val (x : ZMod (2 * m)) : (bit m (x + 1)).val = 1 - (bit m x).val := by
  change (x + 1).val % 2 = 1 - x.val % 2
  rw [succ_val]
  have hx := x.val_lt
  by_cases h : x.val + 1 < 2 * m
  · rw [Nat.mod_eq_of_lt h]
    omega
  · have he : x.val + 1 = 2 * m := by omega
    rw [he, Nat.mod_self]
    omega

theorem succ_even_val (x : ZMod (2 * m)) (hx : bit m x = 0) : (x + 1).val = x.val + 1 := by
  have hb : x.val % 2 = 0 := congrArg Fin.val hx
  have ht := x.val_lt
  rw [succ_val, Nat.mod_eq_of_lt (by omega)]

theorem coarse_succ_even (x : ZMod (2 * m)) (hx : bit m x = 0) :
    coarse m (x + 1) = coarse m x := by
  apply ZMod.val_injective
  rw [coarse_val, coarse_val, succ_even_val m x hx]
  have hb : x.val % 2 = 0 := congrArg Fin.val hx
  omega

theorem bit_reflect_succ (x : ZMod (2 * m)) : bit m (-(x + 1 + 1)) = bit m x := by
  apply Fin.ext
  rw [bit_reflect_val, bit_succ_val]
  have hb := (bit m x).isLt
  omega

theorem coarse_reflect_succ_even (x : ZMod (2 * m)) (hx : bit m x = 0) :
    coarse m (-(x + 1 + 1)) = -(coarse m x + 1) := by
  rw [coarse_reflect, coarse_succ_even m x hx]

end
end UnifiedTheory.Clay.YangMills.DyadicCellCoordinates
