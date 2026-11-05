/- A concrete nonempty schedule for an unbounded number of genuine Wilson
eliminations. Each stage removes one new coordinate along a coordinate line.
This sparse witness is not blocking to a fixed physical scale. -/
import UnifiedTheory.Clay.YangMills.WilsonFactorTower
import UnifiedTheory.Clay.YangMills.GrowingStageContactPath

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonGrowingBlockWitness
noncomputable section
open RegulatedGauge PeriodicLattice4 WilsonUniformVariance WilsonIndependentBlocks

variable (n : ℕ)
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _

/-- The coordinate-line vertex with temporal coordinate j modulo n. -/
def vertex (j : ℕ) : Vertex n := fun ν => if ν = 0 then (j : ZMod n) else 0

/-- One actual positive link in direction one, transverse to the selected coordinate line. -/
def link (j : ℕ) : Edge (Vertex n) := selectedLink n (vertex n j) 1

/-- Only indices below the period are used; later blocks are empty. -/
def block (j : ℕ) : Finset (Edge (Vertex n)) :=
  if j < n then {link n j} else ∅

theorem vertex_zero (j : ℕ) : vertex n j 0 = (j : ZMod n) := by
  simp [vertex]

theorem link_injective_below {i j : ℕ} (hi : i < n) (hj : j < n)
    (h : link n i = link n j) : i = j := by
  have he := congrArg (fun e : Edge (Vertex n) => (edgeCoord n e).1 0) h
  change vertex n i 0 = vertex n j 0 at he
  rw [vertex_zero, vertex_zero] at he
  have hv := congrArg ZMod.val he
  simpa only [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] using hv

theorem block_eq_singleton (j : ℕ) (hj : j < n) : block n j = {link n j} := by
  simp only [block, if_pos hj]

theorem block_eq_empty (j : ℕ) (hj : n ≤ j) : block n j = ∅ := by
  simp only [block, if_neg (Nat.not_lt.mpr hj)]

theorem block_nonempty (j : ℕ) (hj : j < n) : (block n j).Nonempty := by
  rw [block_eq_singleton n j hj]
  exact Finset.singleton_nonempty _

theorem block_card (j : ℕ) (hj : j < n) : (block n j).card = 1 := by
  simp only [block_eq_singleton n j hj, Finset.card_singleton]

/-- No coordinate is ever selected by two distinct stages. -/
theorem block_disjoint {i j : ℕ} (hij : i ≠ j) : Disjoint (block n i) (block n j) := by
  by_cases hi : i < n
  · by_cases hj : j < n
    · rw [block_eq_singleton n i hi, block_eq_singleton n j hj,
        Finset.disjoint_singleton_left, Finset.mem_singleton]
      exact fun h => hij (link_injective_below n hi hj h)
    · rw [block_eq_empty n j (Nat.le_of_not_gt hj)]
      exact Finset.disjoint_empty_right _
  · rw [block_eq_empty n i (Nat.le_of_not_gt hi)]
    exact Finset.disjoint_empty_left _

/-- Singleton updates are independent for every nonlinear induced factor family. -/
theorem block_independent {P : Type*} (D : P → Finset (Edge (Vertex n))) (j : ℕ) :
    FiniteFactorConditional.Independent D (block n j) := by
  intro p e he d hd _ _
  by_cases hj : j < n
  · rw [block_eq_singleton n j hj] at he hd
    exact (Finset.mem_singleton.mp he).trans (Finset.mem_singleton.mp hd).symm
  · rw [block_eq_empty n j (Nat.le_of_not_gt hj)] at he
    exact False.elim (Finset.notMem_empty _ he)

/-- Admissibility is discharged for the actual computed Wilson supports at every depth. -/
theorem admissible [NeZero n] : WilsonFactorTower.Admissible n (block n) :=
  fun j => block_independent n (WilsonFactorTower.supports n (block n) j) j

/-- The first two blocks share an original plaquette. Their union is therefore
not merely one independent block of the initial action. -/
theorem first_two_not_independent [NeZero n] (hn : 1 < n) :
    ¬FiniteFactorConditional.Independent (WilsonInducedSupport.plaquetteEdges n)
      (block n 0 ∪ block n 1) := by
  let p : PeriodicLattice4.PlaquetteIndex n :=
    (vertex n 0, (⟨(0, 1), by decide⟩ : PeriodicLattice4.Plane))
  have hv : vertex n 1 = step n (vertex n 0) 0 := by
    ext ν
    by_cases hν : ν = 0
    · subst ν
      simp [vertex, step]
    · simp [vertex, step, hν]
  have h0 : link n 0 ∈ WilsonInducedSupport.plaquetteEdges n p := by
    apply (WilsonInducedSupport.mem_plaquetteEdges n p (link n 0)).mpr
    change p ∈ SingleLinkWilsonOscillation.affected n (vertex n 0) 1
    apply incident_affected n p (vertex n 0, 1)
    exact Or.inr (Or.inr (Or.inr rfl))
  have h1 : link n 1 ∈ WilsonInducedSupport.plaquetteEdges n p := by
    apply (WilsonInducedSupport.mem_plaquetteEdges n p (link n 1)).mpr
    change p ∈ SingleLinkWilsonOscillation.affected n (vertex n 1) 1
    apply incident_affected n p (vertex n 1, 1)
    exact Or.inr (Or.inl (congrArg (fun x => (x, (1 : Fin 4))) hv))
  intro h
  have he := h p (link n 0)
    (Finset.mem_union_left _ (by simp [block, (Nat.zero_lt_one.trans hn)])) (link n 1)
    (Finset.mem_union_right _ (by simp [block, hn])) h0 h1
  have hh := link_injective_below n (Nat.zero_lt_one.trans hn) hn he
  omega

/-- A prefix below the period removes exactly its number of distinct coordinates. -/
theorem prefix_card (k : ℕ) (hk : k ≤ n) :
    ((Finset.range k).biUnion (block n)).card = k := by
  classical
  rw [Finset.card_biUnion (fun i _ j _ hij => block_disjoint n hij)]
  calc
    (∑ j ∈ Finset.range k, (block n j).card) = ∑ _j ∈ Finset.range k, 1 := by
      apply Finset.sum_congr rfl
      intro j hj
      exact block_card n j ((Finset.mem_range.mp hj).trans_le hk)
    _ = k := by simp

/-- The explicit expanding path has room for every one of its k selected stages. -/
theorem stage_count_lt_period (k : ℕ) : k < GrowingStageContactPath.period k := by
  have h1 : k < 2 ^ k := Nat.lt_two_pow_self
  have h2 : 2 ^ k ≤ (2 ^ k) ^ 17 :=
    le_self_pow₀ Nat.one_le_two_pow (by norm_num : (17 : ℕ) ≠ 0)
  unfold GrowingStageContactPath.period
  omega

instance pathPeriodNeZero (k : ℕ) : NeZero (GrowingStageContactPath.period k) :=
  ⟨Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le k) (stage_count_lt_period k))⟩

theorem path_admissible (k : ℕ) :
    WilsonFactorTower.Admissible (GrowingStageContactPath.period k)
      (block (GrowingStageContactPath.period k)) := admissible _

theorem path_block_nonempty (k j : ℕ) (hj : j < k) :
    (block (GrowingStageContactPath.period k) j).Nonempty :=
  block_nonempty _ j (hj.trans (stage_count_lt_period k))

theorem path_prefix_card (k : ℕ) :
    ((Finset.range k).biUnion (block (GrowingStageContactPath.period k))).card = k :=
  prefix_card _ k (stage_count_lt_period k).le

end
end UnifiedTheory.Clay.YangMills.WilsonGrowingBlockWitness
