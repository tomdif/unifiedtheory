/-
  Audit/OrderSensitiveObservables.lean

  ORDER-SENSITIVE FINITE BENCHMARK — REPAIRING INPUT ERASURE

  `ObservableSeparation.lean` proves that the advertised signature in
  `NoBackgroundSpace.lean` cannot distinguish a two-element chain from
  a two-element antichain.  This file supplies the first constructive
  repair: observables that inspect the order relation itself.

  The benchmark contains four non-isomorphic four-event orders:

    * an antichain;
    * two disjoint two-event chains (a sparse causal sample);
    * a causal diamond / 2 x 2 product order;
    * a total chain.

  The signature records strict comparable pairs, covering links, the
  aggregate size of open intervals, exact height, and exact width.  It
  separates all four benchmarks and is invariant under every one of the
  24 relabelings of their common carrier `Fin 4`.

  HONEST SCOPE:

  This is a finite separation benchmark, not a continuum reconstruction
  theorem.  This file deliberately remains the purely order-combinatorial
  baseline.  The generic determinant-defined `K_F` API and its normalized
  spectral augmentation are supplied by `LayerB/KFFinitePoset.lean` and
  `Audit/KFSpectralCoarseGraining.lean`.
-/

import UnifiedTheory.Audit.ObservableSeparation
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.OrderSensitiveObservables

open UnifiedTheory.LayerB.NoBackgroundSpace

/-! ## 1. Four explicit benchmark orders -/

/-- Four unrelated events. -/
def antichainFour : FinPoset where
  n := 4
  hn := by decide
  rel := fun i j => decide (i = j)
  refl := by decide
  antisymm := by decide
  trans := by decide

/-- A sparse four-event causal sample consisting of the strict pairs
`0 < 1` and `2 < 3`, with no cross-pair comparabilities. -/
def twoChainsFour : FinPoset where
  n := 4
  hn := by decide
  rel := fun i j => decide (i = j ∨ (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3))
  refl := by decide
  antisymm := by decide
  trans := by decide

/-- The four-event causal diamond, equivalently the product order
`Fin 2 x Fin 2`: `0` is bottom, `3` is top, and `1`, `2` are
incomparable middle events. -/
def diamondFour : FinPoset where
  n := 4
  hn := by decide
  rel := fun i j => decide (
    i = j
      ∨ (i = 0 ∧ (j = 1 ∨ j = 2 ∨ j = 3))
      ∨ ((i = 1 ∨ i = 2) ∧ j = 3))
  refl := by decide
  antisymm := by decide
  trans := by decide

/-- Four totally ordered events. -/
def chainFour : FinPoset where
  n := 4
  hn := by decide
  rel := fun i j => decide (i.val ≤ j.val)
  refl := by decide
  antisymm := by decide
  trans := by decide

/-! ## 2. Relation-derived observables -/

/-- Strict precedence removes the reflexive diagonal from `FinPoset.rel`. -/
def StrictPrecedes (P : FinPoset) (i j : Fin P.n) : Prop :=
  i ≠ j ∧ P.rel i j = true

instance strictPrecedesDecidable (P : FinPoset) (i j : Fin P.n) :
    Decidable (StrictPrecedes P i j) := by
  unfold StrictPrecedes
  infer_instance

/-- Number of ordered strict comparable pairs.  Antisymmetry ensures each
comparable unordered pair contributes exactly once. -/
def strictPairCount (P : FinPoset) : ℕ :=
  ∑ pair : Fin P.n × Fin P.n,
    if StrictPrecedes P pair.1 pair.2 then 1 else 0

/-- The open interval `(i,j)`: events strictly between `i` and `j`. -/
def openInterval (P : FinPoset) (i j : Fin P.n) : Finset (Fin P.n) :=
  Finset.univ.filter (fun k => StrictPrecedes P i k ∧ StrictPrecedes P k j)

/-- Cardinality of an open interval. -/
def openIntervalCard (P : FinPoset) (i j : Fin P.n) : ℕ :=
  (openInterval P i j).card

/-- A covering link is a strict precedence relation with empty open interval. -/
def IsLink (P : FinPoset) (i j : Fin P.n) : Prop :=
  StrictPrecedes P i j ∧ openIntervalCard P i j = 0

instance isLinkDecidable (P : FinPoset) (i j : Fin P.n) :
    Decidable (IsLink P i j) := by
  unfold IsLink
  infer_instance

/-- Number of covering links in the Hasse diagram. -/
def linkCount (P : FinPoset) : ℕ :=
  ∑ pair : Fin P.n × Fin P.n,
    if IsLink P pair.1 pair.2 then 1 else 0

/-- Aggregate open-interval mass.  Equivalently, the number of triples
`i < k < j`.  Unlike a constant density label, this changes with the
actual transitive structure of the order. -/
def openIntervalMass (P : FinPoset) : ℕ :=
  ∑ pair : Fin P.n × Fin P.n, openIntervalCard P pair.1 pair.2

/-! ## 3. Exact finite height and width -/

/-- A subset is a chain when every two distinct members are comparable. -/
def IsChainSubset (P : FinPoset) (subset : Finset (Fin P.n)) : Prop :=
  ∀ i ∈ subset, ∀ j ∈ subset, i ≠ j →
    P.rel i j = true ∨ P.rel j i = true

instance isChainSubsetDecidable (P : FinPoset) (subset : Finset (Fin P.n)) :
    Decidable (IsChainSubset P subset) := by
  unfold IsChainSubset
  infer_instance

/-- A subset is an antichain when distinct members are incomparable. -/
def IsAntichainSubset (P : FinPoset) (subset : Finset (Fin P.n)) : Prop :=
  ∀ i ∈ subset, ∀ j ∈ subset, i ≠ j →
    P.rel i j = false ∧ P.rel j i = false

instance isAntichainSubsetDecidable (P : FinPoset) (subset : Finset (Fin P.n)) :
    Decidable (IsAntichainSubset P subset) := by
  unfold IsAntichainSubset
  infer_instance

/-- Cardinalities of all chain subsets. -/
def chainSizes (P : FinPoset) : Finset ℕ :=
  ((Finset.univ.powerset.filter (IsChainSubset P)).image Finset.card)

/-- The empty subset ensures `chainSizes` is nonempty. -/
theorem chainSizes_nonempty (P : FinPoset) : (chainSizes P).Nonempty := by
  refine Finset.image_nonempty.mpr ?_
  refine ⟨∅, ?_⟩
  simp [IsChainSubset]

/-- Exact height: cardinality of a largest chain subset. -/
def orderHeight (P : FinPoset) : ℕ :=
  (chainSizes P).max' (chainSizes_nonempty P)

/-- Cardinalities of all antichain subsets. -/
def antichainSizes (P : FinPoset) : Finset ℕ :=
  ((Finset.univ.powerset.filter (IsAntichainSubset P)).image Finset.card)

/-- The empty subset ensures `antichainSizes` is nonempty. -/
theorem antichainSizes_nonempty (P : FinPoset) : (antichainSizes P).Nonempty := by
  refine Finset.image_nonempty.mpr ?_
  refine ⟨∅, ?_⟩
  simp [IsAntichainSubset]

/-- Exact width: cardinality of a largest antichain subset. -/
def orderWidth (P : FinPoset) : ℕ :=
  (antichainSizes P).max' (antichainSizes_nonempty P)

/-! ## 4. The separating signature -/

/-- A finite observable vector whose non-cardinality fields all inspect
`P.rel`.  Keeping `eventCount` explicit prevents comparisons across sizes
from hiding a carrier-size change. -/
structure OrderSignature where
  eventCount : ℕ
  strictPairs : ℕ
  links : ℕ
  intervalMass : ℕ
  height : ℕ
  width : ℕ
  deriving DecidableEq, Repr

def orderSignature (P : FinPoset) : OrderSignature where
  eventCount := P.n
  strictPairs := strictPairCount P
  links := linkCount P
  intervalMass := openIntervalMass P
  height := orderHeight P
  width := orderWidth P

/-! ## 5. Exact benchmark evaluations -/

theorem antichainFour_signature :
    orderSignature antichainFour =
      { eventCount := 4, strictPairs := 0, links := 0,
        intervalMass := 0, height := 1, width := 4 } := by
  decide

theorem twoChainsFour_signature :
    orderSignature twoChainsFour =
      { eventCount := 4, strictPairs := 2, links := 2,
        intervalMass := 0, height := 2, width := 2 } := by
  decide

theorem diamondFour_signature :
    orderSignature diamondFour =
      { eventCount := 4, strictPairs := 5, links := 4,
        intervalMass := 2, height := 3, width := 2 } := by
  decide

theorem chainFour_signature :
    orderSignature chainFour =
      { eventCount := 4, strictPairs := 6, links := 3,
        intervalMass := 4, height := 4, width := 1 } := by
  decide

/-- The preregistered separation gate for the four benchmark orders. -/
def BenchmarkSignaturesPairwiseDistinct : Prop :=
    orderSignature antichainFour ≠ orderSignature twoChainsFour
    ∧ orderSignature antichainFour ≠ orderSignature diamondFour
    ∧ orderSignature antichainFour ≠ orderSignature chainFour
    ∧ orderSignature twoChainsFour ≠ orderSignature diamondFour
    ∧ orderSignature twoChainsFour ≠ orderSignature chainFour
    ∧ orderSignature diamondFour ≠ orderSignature chainFour

/-- All four finite orders are separated by the observable vector. -/
theorem benchmark_signatures_pairwise_distinct :
    BenchmarkSignaturesPairwiseDistinct := by
  unfold BenchmarkSignaturesPairwiseDistinct
  rw [antichainFour_signature, twoChainsFour_signature,
    diamondFour_signature, chainFour_signature]
  decide

/-! ## 6. Relabeling invariance on the preregistered benchmark -/

/-- Relabel a finite order by a permutation of its event carrier. -/
def relabel (P : FinPoset) (σ : Equiv.Perm (Fin P.n)) : FinPoset where
  n := P.n
  hn := P.hn
  rel := fun i j => P.rel (σ.symm i) (σ.symm j)
  refl := by
    intro i
    exact P.refl (σ.symm i)
  antisymm := by
    intro i j hij hji
    exact σ.symm.injective (P.antisymm (σ.symm i) (σ.symm j) hij hji)
  trans := by
    intro i j k hij hjk
    exact P.trans (σ.symm i) (σ.symm j) (σ.symm k) hij hjk

@[simp]
theorem strictPrecedes_relabel_apply_iff (P : FinPoset)
    (σ : Equiv.Perm (Fin P.n)) (i j : Fin P.n) :
    StrictPrecedes (relabel P σ) (σ i) (σ j) ↔ StrictPrecedes P i j := by
  simp [StrictPrecedes, relabel]

theorem strictPairCount_relabel (P : FinPoset)
    (σ : Equiv.Perm (Fin P.n)) :
    strictPairCount (relabel P σ) = strictPairCount P := by
  let pairEquiv : (Fin P.n × Fin P.n) ≃ (Fin P.n × Fin P.n) :=
    Equiv.prodCongr σ σ
  unfold strictPairCount
  calc
    (∑ pair : Fin P.n × Fin P.n,
        if StrictPrecedes (relabel P σ) pair.1 pair.2 then 1 else 0) =
        ∑ pair : Fin P.n × Fin P.n,
          if StrictPrecedes (relabel P σ) (σ pair.1) (σ pair.2) then 1 else 0 := by
      have h := pairEquiv.sum_comp (fun pair =>
        if StrictPrecedes (relabel P σ) pair.1 pair.2 then 1 else 0)
      change (∑ pair : Fin P.n × Fin P.n,
          if StrictPrecedes (relabel P σ) (σ pair.1) (σ pair.2) then 1 else 0) =
        ∑ pair : Fin P.n × Fin P.n,
          if StrictPrecedes (relabel P σ) pair.1 pair.2 then 1 else 0 at h
      exact h.symm
    _ = ∑ pair : Fin P.n × Fin P.n,
        if StrictPrecedes P pair.1 pair.2 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro pair _
      simp only [strictPrecedes_relabel_apply_iff]

theorem openIntervalCard_relabel_apply (P : FinPoset)
    (σ : Equiv.Perm (Fin P.n)) (i j : Fin P.n) :
    openIntervalCard (relabel P σ) (σ i) (σ j) = openIntervalCard P i j := by
  symm
  apply Finset.card_equiv σ
  intro k
  simp [openInterval, StrictPrecedes, relabel]

@[simp]
theorem isLink_relabel_apply_iff (P : FinPoset)
    (σ : Equiv.Perm (Fin P.n)) (i j : Fin P.n) :
    IsLink (relabel P σ) (σ i) (σ j) ↔ IsLink P i j := by
  simp [IsLink, openIntervalCard_relabel_apply]

theorem linkCount_relabel (P : FinPoset)
    (σ : Equiv.Perm (Fin P.n)) :
    linkCount (relabel P σ) = linkCount P := by
  let pairEquiv : (Fin P.n × Fin P.n) ≃ (Fin P.n × Fin P.n) :=
    Equiv.prodCongr σ σ
  unfold linkCount
  calc
    (∑ pair : Fin P.n × Fin P.n,
        if IsLink (relabel P σ) pair.1 pair.2 then 1 else 0) =
        ∑ pair : Fin P.n × Fin P.n,
          if IsLink (relabel P σ) (σ pair.1) (σ pair.2) then 1 else 0 := by
      have h := pairEquiv.sum_comp (fun pair =>
        if IsLink (relabel P σ) pair.1 pair.2 then 1 else 0)
      change (∑ pair : Fin P.n × Fin P.n,
          if IsLink (relabel P σ) (σ pair.1) (σ pair.2) then 1 else 0) =
        ∑ pair : Fin P.n × Fin P.n,
          if IsLink (relabel P σ) pair.1 pair.2 then 1 else 0 at h
      exact h.symm
    _ = ∑ pair : Fin P.n × Fin P.n,
        if IsLink P pair.1 pair.2 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro pair _
      simp only [isLink_relabel_apply_iff]

theorem openIntervalMass_relabel (P : FinPoset)
    (σ : Equiv.Perm (Fin P.n)) :
    openIntervalMass (relabel P σ) = openIntervalMass P := by
  let pairEquiv : (Fin P.n × Fin P.n) ≃ (Fin P.n × Fin P.n) :=
    Equiv.prodCongr σ σ
  unfold openIntervalMass
  calc
    (∑ pair : Fin P.n × Fin P.n,
        openIntervalCard (relabel P σ) pair.1 pair.2) =
        ∑ pair : Fin P.n × Fin P.n,
          openIntervalCard (relabel P σ) (σ pair.1) (σ pair.2) := by
      simpa [pairEquiv] using
        (pairEquiv.sum_comp (fun pair =>
          openIntervalCard (relabel P σ) pair.1 pair.2)).symm
    _ = ∑ pair : Fin P.n × Fin P.n,
        openIntervalCard P pair.1 pair.2 := by
      apply Finset.sum_congr rfl
      intro pair _
      exact openIntervalCard_relabel_apply P σ pair.1 pair.2

theorem isChainSubset_relabel_iff (P : FinPoset)
    (σ : Equiv.Perm (Fin P.n)) (subset : Finset (Fin P.n)) :
    IsChainSubset (relabel P σ) subset ↔
      IsChainSubset P (subset.map σ.symm.toEmbedding) := by
  constructor
  · intro h i hi j hj hij
    rcases Finset.mem_map.mp hi with ⟨i', hi', rfl⟩
    rcases Finset.mem_map.mp hj with ⟨j', hj', rfl⟩
    have hij' : i' ≠ j' := fun hEq => hij (congrArg σ.symm hEq)
    simpa [relabel] using h i' hi' j' hj' hij'
  · intro h i hi j hj hij
    have hi' : σ.symm i ∈ subset.map σ.symm.toEmbedding :=
      Finset.mem_map.mpr ⟨i, hi, rfl⟩
    have hj' : σ.symm j ∈ subset.map σ.symm.toEmbedding :=
      Finset.mem_map.mpr ⟨j, hj, rfl⟩
    have hij' : σ.symm i ≠ σ.symm j := σ.symm.injective.ne hij
    simpa [relabel] using h (σ.symm i) hi' (σ.symm j) hj' hij'

theorem isAntichainSubset_relabel_iff (P : FinPoset)
    (σ : Equiv.Perm (Fin P.n)) (subset : Finset (Fin P.n)) :
    IsAntichainSubset (relabel P σ) subset ↔
      IsAntichainSubset P (subset.map σ.symm.toEmbedding) := by
  constructor
  · intro h i hi j hj hij
    rcases Finset.mem_map.mp hi with ⟨i', hi', rfl⟩
    rcases Finset.mem_map.mp hj with ⟨j', hj', rfl⟩
    have hij' : i' ≠ j' := fun hEq => hij (congrArg σ.symm hEq)
    simpa [relabel] using h i' hi' j' hj' hij'
  · intro h i hi j hj hij
    have hi' : σ.symm i ∈ subset.map σ.symm.toEmbedding :=
      Finset.mem_map.mpr ⟨i, hi, rfl⟩
    have hj' : σ.symm j ∈ subset.map σ.symm.toEmbedding :=
      Finset.mem_map.mpr ⟨j, hj, rfl⟩
    have hij' : σ.symm i ≠ σ.symm j := σ.symm.injective.ne hij
    simpa [relabel] using h (σ.symm i) hi' (σ.symm j) hj' hij'

theorem chainSizes_relabel (P : FinPoset) (σ : Equiv.Perm (Fin P.n)) :
    chainSizes (relabel P σ) = chainSizes P := by
  ext size
  constructor
  · intro hsize
    rcases Finset.mem_image.mp hsize with ⟨subset, hsubset, hcard⟩
    have hchain : IsChainSubset (relabel P σ) subset :=
      (Finset.mem_filter.mp hsubset).2
    refine Finset.mem_image.mpr ⟨subset.map σ.symm.toEmbedding, ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
          (isChainSubset_relabel_iff P σ subset).mp hchain⟩
    · simpa using hcard
  · intro hsize
    rcases Finset.mem_image.mp hsize with ⟨subset, hsubset, hcard⟩
    have hchain : IsChainSubset P subset := (Finset.mem_filter.mp hsubset).2
    refine Finset.mem_image.mpr ⟨subset.map σ.toEmbedding, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
      apply (isChainSubset_relabel_iff P σ _).mpr
      simpa [Finset.map_map] using hchain
    · simpa using hcard

theorem antichainSizes_relabel (P : FinPoset) (σ : Equiv.Perm (Fin P.n)) :
    antichainSizes (relabel P σ) = antichainSizes P := by
  ext size
  constructor
  · intro hsize
    rcases Finset.mem_image.mp hsize with ⟨subset, hsubset, hcard⟩
    have hanti : IsAntichainSubset (relabel P σ) subset :=
      (Finset.mem_filter.mp hsubset).2
    refine Finset.mem_image.mpr ⟨subset.map σ.symm.toEmbedding, ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
          (isAntichainSubset_relabel_iff P σ subset).mp hanti⟩
    · simpa using hcard
  · intro hsize
    rcases Finset.mem_image.mp hsize with ⟨subset, hsubset, hcard⟩
    have hanti : IsAntichainSubset P subset := (Finset.mem_filter.mp hsubset).2
    refine Finset.mem_image.mpr ⟨subset.map σ.toEmbedding, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
      apply (isAntichainSubset_relabel_iff P σ _).mpr
      simpa [Finset.map_map] using hanti
    · simpa using hcard

theorem orderHeight_relabel (P : FinPoset) (σ : Equiv.Perm (Fin P.n)) :
    orderHeight (relabel P σ) = orderHeight P := by
  simp only [orderHeight, chainSizes_relabel]

theorem orderWidth_relabel (P : FinPoset) (σ : Equiv.Perm (Fin P.n)) :
    orderWidth (relabel P σ) = orderWidth P := by
  simp only [orderWidth, antichainSizes_relabel]

/-- The repaired signature is an observable of the unlabeled finite order:
it is invariant under every event-carrier permutation, for every `FinPoset`. -/
theorem orderSignature_relabel (P : FinPoset) (σ : Equiv.Perm (Fin P.n)) :
    orderSignature (relabel P σ) = orderSignature P := by
  simp only [orderSignature]
  rw [strictPairCount_relabel P σ, linkCount_relabel P σ,
    openIntervalMass_relabel P σ, orderHeight_relabel P σ,
    orderWidth_relabel P σ]
  rfl

/-- A benchmark order passes the relabeling gate when all permutations
preserve its full observable signature. -/
def SignatureRelabelingInvariant (P : FinPoset) : Prop :=
  ∀ σ : Equiv.Perm (Fin P.n), orderSignature (relabel P σ) = orderSignature P

theorem benchmark_signatures_relabeling_invariant :
    SignatureRelabelingInvariant antichainFour
    ∧ SignatureRelabelingInvariant twoChainsFour
    ∧ SignatureRelabelingInvariant diamondFour
    ∧ SignatureRelabelingInvariant chainFour := by
  repeat' apply And.intro
  all_goals
    intro σ
    exact orderSignature_relabel _ σ

/-! ## 7. Input-use regression guards -/

/-- Each relation-derived scalar changes on at least one equal-size pair.
This prevents a future refactor from silently replacing it with a function
of cardinality alone. -/
theorem relation_observables_detect_order_change :
    strictPairCount antichainFour ≠ strictPairCount chainFour
    ∧ linkCount antichainFour ≠ linkCount diamondFour
    ∧ openIntervalMass twoChainsFour ≠ openIntervalMass diamondFour
    ∧ orderHeight antichainFour ≠ orderHeight chainFour
    ∧ orderWidth antichainFour ≠ orderWidth chainFour := by
  decide

/-- The repaired signature closes the exact counterexample from
`ObservableSeparation`: unlike the old advertised signature, it separates
the equal-cardinality chain and antichain benchmarks. -/
theorem repaired_signature_closes_order_blind_counterexample :
    orderSignature antichainFour ≠ orderSignature chainFour := by
  exact benchmark_signatures_pairwise_distinct.2.2.1

/-! ## 8. Master benchmark theorem -/

theorem order_sensitive_benchmark_v1 :
    BenchmarkSignaturesPairwiseDistinct
    ∧ SignatureRelabelingInvariant antichainFour
    ∧ SignatureRelabelingInvariant twoChainsFour
    ∧ SignatureRelabelingInvariant diamondFour
    ∧ SignatureRelabelingInvariant chainFour
    ∧ strictPairCount antichainFour ≠ strictPairCount chainFour
    ∧ linkCount antichainFour ≠ linkCount diamondFour
    ∧ openIntervalMass twoChainsFour ≠ openIntervalMass diamondFour
    ∧ orderHeight antichainFour ≠ orderHeight chainFour
    ∧ orderWidth antichainFour ≠ orderWidth chainFour := by
  refine ⟨benchmark_signatures_pairwise_distinct,
    benchmark_signatures_relabeling_invariant.1,
    benchmark_signatures_relabeling_invariant.2.1,
    benchmark_signatures_relabeling_invariant.2.2.1,
    benchmark_signatures_relabeling_invariant.2.2.2, ?_⟩
  exact relation_observables_detect_order_change

/-! ## Trust regression output -/

#print axioms benchmark_signatures_pairwise_distinct
#print axioms benchmark_signatures_relabeling_invariant
#print axioms relation_observables_detect_order_change
#print axioms order_sensitive_benchmark_v1

end UnifiedTheory.Audit.OrderSensitiveObservables
