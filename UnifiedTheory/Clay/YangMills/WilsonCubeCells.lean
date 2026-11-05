/- Disjoint six-plaquette cube cells in the actual periodic spatial lattice.
Each coarse vertex labels a two-by-two-by-two set of fine vertices. -/
import UnifiedTheory.Clay.YangMills.DyadicCellCoordinates
import UnifiedTheory.Clay.YangMills.WilsonFramedDeletion

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonCubeCells
noncomputable section
open WilsonTimeSlab SpatialPlaquetteCutGeometry DyadicCellCoordinates

abbrev Offsets := Fin 3 → Fin 2
abbrev Pattern := {q : SpatialPlane × Offsets // q.2 q.1.val.1 = 0 ∧ q.2 q.1.val.2 = 0}

theorem pattern_card : Fintype.card Pattern = 6 := by decide

variable (m : ℕ) [NeZero m]

def coarseVertex (x : SpatialVertex (2 * m)) : SpatialVertex m := fun j => coarse m (x j)
def offsets (x : SpatialVertex (2 * m)) : Offsets := fun j => bit m (x j)
def joinVertex (x : SpatialVertex m) (b : Offsets) : SpatialVertex (2 * m) :=
  fun j => join m (x j) (b j)

theorem coarse_joinVertex (x : SpatialVertex m) (b : Offsets) :
    coarseVertex m (joinVertex m x b) = x := funext (fun j => coarse_join m (x j) (b j))

theorem offsets_joinVertex (x : SpatialVertex m) (b : Offsets) :
    offsets m (joinVertex m x b) = b := funext (fun j => bit_join m (x j) (b j))

theorem joinVertex_split (x : SpatialVertex (2 * m)) :
    joinVertex m (coarseVertex m x) (offsets m x) = x := funext (fun j => join_split m (x j))

def encode (q : SpatialVertex m × Pattern) : Plaquette m :=
  (joinVertex m q.1 q.2.val.2,q.2.val.1)

theorem encode_injective : Function.Injective (encode m) := by
  rintro ⟨x,z⟩ ⟨y,w⟩ h
  have hx := congrArg (fun p : Plaquette m => coarseVertex m p.1) h
  have hb := congrArg (fun p : Plaquette m => offsets m p.1) h
  have hp := congrArg Prod.snd h
  simp only [encode, coarse_joinVertex] at hx
  simp only [encode, offsets_joinVertex] at hb
  change z.val.1 = w.val.1 at hp
  exact Prod.ext hx (Subtype.ext (Prod.ext hp hb))

def embedding : SpatialVertex m × Pattern ↪ Plaquette m := ⟨encode m,encode_injective m⟩

def Internal (p : Plaquette m) : Prop := offsets m p.1 p.2.val.1 = 0 ∧ offsets m p.1 p.2.val.2 = 0

theorem encode_internal (q : SpatialVertex m × Pattern) : Internal m (encode m q) := by
  simpa only [Internal, encode, offsets_joinVertex] using q.2.property

def cellSet (S : Finset (SpatialVertex m)) : Finset (Plaquette m) :=
  (S ×ˢ Finset.univ).map (embedding m)

theorem cellSet_mem (S : Finset (SpatialVertex m)) (p : Plaquette m) :
    p ∈ cellSet m S ↔ Internal m p ∧ coarseVertex m p.1 ∈ S := by
  classical
  constructor
  · intro hp
    obtain ⟨⟨x,z⟩,hx,he⟩ := Finset.mem_map.mp hp
    change encode m (x,z) = p at he
    rw [← he]
    exact ⟨encode_internal m _,by
      simpa only [encode, coarse_joinVertex] using (Finset.mem_product.mp hx).1⟩
  · rintro ⟨hi,hx⟩
    let z : Pattern := ⟨(p.2,offsets m p.1),hi⟩
    apply Finset.mem_map.mpr
    refine ⟨(coarseVertex m p.1,z),Finset.mem_product.mpr ⟨hx,Finset.mem_univ _⟩,?_⟩
    change (joinVertex m (coarseVertex m p.1) (offsets m p.1),p.2) = p
    rw [joinVertex_split]

theorem cellSet_card (S : Finset (SpatialVertex m)) : (cellSet m S).card = 6 * S.card := by
  simp only [cellSet, Finset.card_map, Finset.card_product, Finset.card_univ,
    pattern_card, Nat.mul_comm]

def marked (f : SpatialVertex m → Bool) : Finset (SpatialVertex m) :=
  Finset.univ.filter (fun x => f x = true)

def deleted (f : SpatialVertex m → Bool) : Finset (Plaquette m) := cellSet m (marked m f)

theorem deleted_mem (f : SpatialVertex m → Bool) (p : Plaquette m) :
    p ∈ deleted m f ↔ Internal m p ∧ f (coarseVertex m p.1) = true := by
  simp only [deleted, cellSet_mem, marked, Finset.mem_filter, Finset.mem_univ, true_and]

theorem deleted_card (f : SpatialVertex m → Bool) : (deleted m f).card = 6 * (marked m f).card :=
  cellSet_card m _

theorem deleted_false : deleted m (fun _ => false) = ∅ := by
  classical
  ext p
  simp only [deleted_mem, Bool.false_eq_true, and_false, Finset.notMem_empty]

theorem deleted_true : deleted m (fun _ => true) = cellSet m Finset.univ := by
  simp only [deleted, marked, Finset.filter_true]

theorem full_card : (deleted m (fun _ => true)).card = 6 * m^3 := by
  rw [deleted_true, cellSet_card]
  simp only [Finset.card_univ, SpatialVertex, Fintype.card_fun, ZMod.card, Fintype.card_fin]

def label (S : Finset (SpatialVertex m)) (x : SpatialVertex m) : Bool := by
  classical
  exact decide (x ∈ S)

theorem marked_label (S : Finset (SpatialVertex m)) : marked m (label m S) = S := by
  classical
  ext x
  simp [marked, label]

theorem deleted_label (S : Finset (SpatialVertex m)) : deleted m (label m S) = cellSet m S := by
  rw [deleted, marked_label]

end
end UnifiedTheory.Clay.YangMills.WilsonCubeCells
