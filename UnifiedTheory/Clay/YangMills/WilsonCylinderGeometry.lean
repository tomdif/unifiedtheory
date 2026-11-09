/-
An open time cylinder with independent temporal length and fixed periodic
spatial volume. Its positive-link inventory and oriented square boundaries
match the actual Wilson slice holonomies. Shared-square dependence changes
time by at most one; finite neighborhoods therefore separate time slices
without any periodic temporal wraparound. No influence or mixing estimate
is assumed or derived merely from this geometry.
-/
import UnifiedTheory.Clay.YangMills.WilsonTimeSlab
import Mathlib.Logic.Function.DependsOn
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonCylinderGeometry
noncomputable section
open WilsonTimeSlab

abbrev SpatialLink (n L : ℕ) := Fin (L + 1) × (SpatialVertex n × Fin 3)
abbrev TemporalLink (n L : ℕ) := Fin L × SpatialVertex n
abbrev Link (n L : ℕ) := SpatialLink n L ⊕ TemporalLink n L
abbrev SpatialPlaquette (n L : ℕ) := Fin (L + 1) × (SpatialVertex n × SpatialPlane)
abbrev TemporalPlaquette (n L : ℕ) := Fin L × (SpatialVertex n × Fin 3)
abbrev Plaquette (n L : ℕ) := SpatialPlaquette n L ⊕ TemporalPlaquette n L

variable (n L : ℕ)
local instance linkDecidableEq : DecidableEq (Link n L) := Classical.decEq _

def spatialBoundary (p : SpatialPlaquette n L) : Fin 4 → Link n L :=
  ![Sum.inl (p.1, p.2.1, p.2.2.1.1),
    Sum.inl (p.1, spatialStep n p.2.1 p.2.2.1.1, p.2.2.1.2),
    Sum.inl (p.1, spatialStep n p.2.1 p.2.2.1.2, p.2.2.1.1),
    Sum.inl (p.1, p.2.1, p.2.2.1.2)]

def temporalBoundary (p : TemporalPlaquette n L) : Fin 4 → Link n L :=
  ![Sum.inr (p.1, p.2.1), Sum.inl (p.1.succ, p.2.1, p.2.2),
    Sum.inr (p.1, spatialStep n p.2.1 p.2.2),
    Sum.inl (p.1.castSucc, p.2.1, p.2.2)]

/-- The ordered four links have signs plus, plus, minus, minus. -/
def boundary (p : Plaquette n L) : Fin 4 → Link n L :=
  Sum.elim (spatialBoundary n L) (temporalBoundary n L) p

def incidentLinks (p : Plaquette n L) : Finset (Link n L) :=
  Finset.univ.image (boundary n L p)

def incident (p : Plaquette n L) (e : Link n L) : Prop := e ∈ incidentLinks n L p

theorem incident_iff (p : Plaquette n L) (e : Link n L) :
    incident n L p e ↔ ∃ k : Fin 4, boundary n L p k = e := by
  simp [incident, incidentLinks]

theorem incidentLinks_card_le (p : Plaquette n L) : (incidentLinks n L p).card ≤ 4 := by
  exact (Finset.card_image_le).trans (by simp)

def linkTime (e : Link n L) : ℕ := Sum.elim (fun a => a.1.val) (fun a => a.1.val) e

def plaquetteTime (p : Plaquette n L) : ℕ :=
  Sum.elim (fun a => a.1.val) (fun a => a.1.val) p

/-- Every boundary link lies at the lower time or one time layer above it. -/
theorem boundary_time_bounds (p : Plaquette n L) (k : Fin 4) :
    plaquetteTime n L p ≤ linkTime n L (boundary n L p k) ∧
      linkTime n L (boundary n L p k) ≤ plaquetteTime n L p + 1 := by
  rcases p with p | p <;> fin_cases k <;>
    simp [boundary, spatialBoundary, temporalBoundary, linkTime, plaquetteTime]

theorem incident_time_bounds (p : Plaquette n L) (e : Link n L) (he : incident n L p e) :
    plaquetteTime n L p ≤ linkTime n L e ∧
      linkTime n L e ≤ plaquetteTime n L p + 1 := by
  obtain ⟨k, rfl⟩ := (incident_iff n L p e).mp he
  exact boundary_time_bounds n L p k

/-- Any two positive links in one actual cylinder square differ in time by at most one. -/
theorem incident_time_diameter (p : Plaquette n L) (a b : Link n L)
    (ha : incident n L p a) (hb : incident n L p b) :
    linkTime n L a ≤ linkTime n L b + 1 ∧ linkTime n L b ≤ linkTime n L a + 1 := by
  have h₁ := incident_time_bounds n L p a ha
  have h₂ := incident_time_bounds n L p b hb
  omega

/-- A shared plaquette is the actual local-dependence adjacency. -/
def Neighbors (a b : Link n L) : Prop :=
  ∃ p : Plaquette n L, incident n L p a ∧ incident n L p b

theorem neighbors_symm (a b : Link n L) : Neighbors n L a b ↔ Neighbors n L b a := by
  constructor <;> rintro ⟨p, ha, hb⟩ <;> exact ⟨p, hb, ha⟩

theorem neighbor_time_diameter (a b : Link n L) (h : Neighbors n L a b) :
    linkTime n L a ≤ linkTime n L b + 1 ∧ linkTime n L b ≤ linkTime n L a + 1 := by
  obtain ⟨p, ha, hb⟩ := h
  exact incident_time_diameter n L p a b ha hb

section Fields
variable {G : Type*}

def spatialSlice (U : Link n L → G) (t : Fin (L + 1)) : SpatialLinks n G :=
  fun e => U (Sum.inl (t, e))

def temporalSlice (U : Link n L → G) (t : Fin L) : SliceGauge n G :=
  fun x => U (Sum.inr (t, x))

variable [Group G]

/-- The actual oriented plaquette product on the disjoint-union link inventory. -/
def plaquetteProduct (U : Link n L → G) (p : Plaquette n L) : G :=
  U (boundary n L p 0) * U (boundary n L p 1) *
    (U (boundary n L p 2))⁻¹ * (U (boundary n L p 3))⁻¹

theorem spatial_plaquette_product (U : Link n L → G) (p : SpatialPlaquette n L) :
    plaquetteProduct n L U (Sum.inl p) =
      spatialHolonomy (spatialSlice n L U p.1) p.2.1 p.2.2.1.1 p.2.2.1.2 := by
  rfl

theorem temporal_plaquette_product (U : Link n L → G) (p : TemporalPlaquette n L) :
    plaquetteProduct n L U (Sum.inr p) =
      temporalHolonomy (spatialSlice n L U p.1.castSucc) (spatialSlice n L U p.1.succ)
        (temporalSlice n L U p.1) p.2.1 p.2.2 := by
  rfl
end Fields

section Finite
variable [NeZero n]
local instance neighborsDecidable (a b : Link n L) : Decidable (Neighbors n L a b) :=
  Classical.propDecidable _

/-- One dependence layer, including the original support. -/
def layer (A : Finset (Link n L)) : Finset (Link n L) :=
  A ∪ Finset.univ.filter (fun b => ∃ a ∈ A, Neighbors n L a b)

theorem mem_layer (A : Finset (Link n L)) (b : Link n L) :
    b ∈ layer n L A ↔ b ∈ A ∨ ∃ a ∈ A, Neighbors n L a b := by
  simp [layer]

def neighborhood (A : Finset (Link n L)) : ℕ → Finset (Link n L)
  | 0 => A
  | k + 1 => layer n L (neighborhood A k)

/-- Finite propagation of the upper time edge from a genuine coordinate support. -/
theorem neighborhood_time_upper (A : Finset (Link n L)) (t : ℕ)
    (hA : ∀ e ∈ A, linkTime n L e ≤ t) (k : ℕ) :
    ∀ e ∈ neighborhood n L A k, linkTime n L e ≤ t + k := by
  induction k with
  | zero => simpa only [neighborhood, Nat.add_zero] using hA
  | succ k ih =>
    intro e he
    rcases (mem_layer n L _ e).mp he with he | ⟨a, ha, hae⟩
    · have h := ih e he
      omega
    · have h := ih a ha
      have hh := (neighbor_time_diameter n L a e hae).2
      omega

/-- Finite propagation of the lower time edge, using natural-number bounds. -/
theorem neighborhood_time_lower (A : Finset (Link n L)) (t : ℕ)
    (hA : ∀ e ∈ A, t ≤ linkTime n L e) (k : ℕ) :
    ∀ e ∈ neighborhood n L A k, t ≤ linkTime n L e + k := by
  induction k with
  | zero => simpa only [neighborhood, Nat.add_zero] using hA
  | succ k ih =>
    intro e he
    rcases (mem_layer n L _ e).mp he with he | ⟨a, ha, hae⟩
    · have h := ih e he
      omega
    · have h := ih a ha
      have hh := (neighbor_time_diameter n L a e hae).1
      omega

/-- The exact separation premise needed by the covariance telescoping argument. -/
theorem separated_by_time (A B : Finset (Link n L)) (s t k : ℕ)
    (hA : ∀ e ∈ A, linkTime n L e ≤ s) (hB : ∀ e ∈ B, t ≤ linkTime n L e)
    (hgap : s + k < t) : Disjoint (neighborhood n L A k) B := by
  apply Finset.disjoint_left.mpr
  intro e heA heB
  have ha := neighborhood_time_upper n L A s hA k e heA
  have hb := hB e heB
  omega

/-- The actual spatial links on one fixed time slice. -/
def sliceSupport (t : Fin (L + 1)) : Finset (Link n L) :=
  Finset.univ.image (fun e : SpatialVertex n × Fin 3 => Sum.inl (t, e))

theorem sliceSupport_time (t : Fin (L + 1)) (e : Link n L) (he : e ∈ sliceSupport n L t) :
    linkTime n L e = t.val := by
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
  rfl

/-- Arbitrary time separations have no wraparound correction on this open cylinder. -/
theorem sliceSupport_separation (s t : Fin (L + 1)) (d j : ℕ)
    (hgap : s.val + d ≤ t.val) (hj : j < d) :
    Disjoint (neighborhood n L (sliceSupport n L s) j) (sliceSupport n L t) := by
  apply separated_by_time n L _ _ s.val t.val j
  · intro e he
    exact (sliceSupport_time n L s e he).le
  · intro e he
    exact (sliceSupport_time n L t e he).ge
  · omega

theorem slice_observable_dependsOn {G Y : Type*} (t : Fin (L + 1))
    (F : SpatialLinks n G → Y) :
    DependsOn (fun U : Link n L → G => F (spatialSlice n L U t))
      (sliceSupport n L t : Set (Link n L)) := by
  intro U V hUV
  apply congrArg F
  funext e
  apply hUV (Sum.inl (t, e))
  exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩
end Finite

end
end UnifiedTheory.Clay.YangMills.WilsonCylinderGeometry
