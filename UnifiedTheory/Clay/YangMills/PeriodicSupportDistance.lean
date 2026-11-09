/- The least periodic coordinate radius supplies an actual distance weight
for Wilson link supports. Direction labels may have zero distance at one
base vertex; only the triangle inequality is needed here. -/
import UnifiedTheory.Clay.YangMills.PeriodicSupportRelation

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.PeriodicSupportDistance
noncomputable section
open RegulatedGauge PeriodicLattice4 WilsonIndependentBlocks WilsonInducedSupport
open PeriodicSupportRelation

variable (n : ℕ) [NeZero n]

theorem exists_close (e d : Edge (Vertex n)) : ∃ r, Close n r e d := by
  refine ⟨n, fun ν => ?_⟩
  let z := (edgeCoord n d).1 ν - (edgeCoord n e).1 ν
  refine ⟨(z.val : ℤ), ?_, ?_⟩
  · rw [abs_of_nonneg (Int.natCast_nonneg _)]
    exact_mod_cast (ZMod.val_lt z).le
  · simpa only [Int.cast_natCast] using (ZMod.natCast_zmod_val z).symm

/-- The least radius in the already proved periodic support relation. -/
def distance (e d : Edge (Vertex n)) : ℕ := by
  classical
  exact Nat.find (exists_close n e d)

theorem close_distance (e d : Edge (Vertex n)) : Close n (distance n e d) e d :=
  by classical exact Nat.find_spec (exists_close n e d)

theorem distance_le (e d : Edge (Vertex n)) (r : ℕ) (h : Close n r e d) :
    distance n e d ≤ r := by
  classical
  exact Nat.find_min' (exists_close n e d) h

theorem distance_self (e : Edge (Vertex n)) : distance n e e = 0 :=
  Nat.eq_zero_of_le_zero (distance_le n e e 0 (close_refl n 0 e))

theorem distance_triangle (e d f : Edge (Vertex n)) :
    distance n e f ≤ distance n e d + distance n d f :=
  distance_le n e f _ (close_add n _ _ e d f (close_distance n e d) (close_distance n d f))

theorem distance_symmetric (e d : Edge (Vertex n)) : distance n e d = distance n d e := by
  apply Nat.le_antisymm
  · exact distance_le n e d _ (close_symm n _ d e (close_distance n d e))
  · exact distance_le n d e _ (close_symm n _ e d (close_distance n e d))

theorem plaquette_distance (p : PlaquetteIndex n) (e d : Edge (Vertex n))
    (he : e ∈ plaquetteEdges n p) (hd : d ∈ plaquetteEdges n p) : distance n e d ≤ 1 :=
  distance_le n e d 1 (plaquette_diameter n p e d he hd)

theorem exists_close_support (S : Finset (Edge (Vertex n))) (hS : S.Nonempty)
    (e : Edge (Vertex n)) : ∃ r, ∃ d ∈ S, Close n r e d := by
  obtain ⟨d, hd⟩ := hS
  exact ⟨distance n e d, d, hd, close_distance n e d⟩

/-- Distance to a nonempty observable support, using the same periodic geometry. -/
def toSupport (S : Finset (Edge (Vertex n))) (hS : S.Nonempty) (e : Edge (Vertex n)) : ℕ :=
  by classical exact Nat.find (exists_close_support n S hS e)

theorem toSupport_attained (S : Finset (Edge (Vertex n))) (hS : S.Nonempty)
    (e : Edge (Vertex n)) : ∃ d ∈ S, Close n (toSupport n S hS e) e d :=
  by classical exact Nat.find_spec (exists_close_support n S hS e)

theorem toSupport_zero (S : Finset (Edge (Vertex n))) (hS : S.Nonempty)
    (e : Edge (Vertex n)) (he : e ∈ S) : toSupport n S hS e = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  exact Nat.find_min' (exists_close_support n S hS e) ⟨e, he, close_refl n 0 e⟩

theorem toSupport_triangle (S : Finset (Edge (Vertex n))) (hS : S.Nonempty)
    (e d : Edge (Vertex n)) : toSupport n S hS e ≤ distance n e d + toSupport n S hS d := by
  classical
  obtain ⟨f, hf, hdf⟩ := toSupport_attained n S hS d
  exact Nat.find_min' (exists_close_support n S hS e)
    ⟨f, hf, close_add n _ _ e d f (close_distance n e d) hdf⟩

/-- Separation is tested against every original link in the second support. -/
theorem toSupport_lower (S : Finset (Edge (Vertex n))) (hS : S.Nonempty)
    (e : Edge (Vertex n)) (R : ℕ) (hR : ∀ d ∈ S, R ≤ distance n e d) :
    R ≤ toSupport n S hS e := by
  obtain ⟨d, hd, hc⟩ := toSupport_attained n S hS e
  exact (hR d hd).trans (distance_le n e d _ hc)

end
end UnifiedTheory.Clay.YangMills.PeriodicSupportDistance
