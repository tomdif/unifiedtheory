/- Quantitative support geometry for exact finite-factor elimination.
The factor stars and evolved supports are the ones computed by the actual
elimination theorem. Metric bounds permit iteration without fixed locality. -/
import UnifiedTheory.Clay.YangMills.FiniteFactorElimination
import UnifiedTheory.Clay.YangMills.ProductResponseSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.FiniteFactorSupportGrowth
noncomputable section
open MeasureTheory FiniteFactorConditional FiniteFactorElimination

section Supports
variable {I P : Type*} [Fintype P] [DecidableEq I]

/-- Source coordinates retained after eliminating a block, together with the
stars of exactly those removed coordinates used by the source. -/
def sourceSupport (D : P → Finset I) (T Q : Finset I) : Finset I :=
  (Q ∪ (Q ∩ T).biUnion (factorStar D)) \ T

theorem mem_sourceSupport (D : P → Finset I) (T Q : Finset I) (i : I) :
    i ∈ sourceSupport D T Q ↔ i ∉ T ∧
      (i ∈ Q ∨ ∃ e ∈ Q, e ∈ T ∧ ∃ p, e ∈ D p ∧ i ∈ D p) := by
  simp only [sourceSupport, Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_inter, mem_factorStar]
  aesop

theorem sourceSupport_disjoint (D : P → Finset I) (T Q : Finset I) :
    Disjoint (sourceSupport D T Q) T := Finset.sdiff_disjoint

theorem sourceSupport_card (D : P → Finset I) (T Q : Finset I) :
    (sourceSupport D T Q).card ≤ Q.card +
      ∑ e ∈ Q ∩ T, (factorStar D e).card := by
  exact (Finset.card_le_card Finset.sdiff_subset).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left (Finset.card_biUnion_le) _))

theorem factorStar_card (D : P → Finset I) (i : I) :
    (factorStar D i).card ≤ ∑ p ∈ touching D i, (D p).card :=
  Finset.card_biUnion_le

theorem factorStar_card_bound (D : P → Finset I) (d t : ℕ)
    (hD : ∀ p, (D p).card ≤ d) (ht : ∀ i, (touching D i).card ≤ t) (i : I) :
    (factorStar D i).card ≤ t * d := by
  calc
    (factorStar D i).card ≤ ∑ p ∈ touching D i, (D p).card := factorStar_card D i
    _ ≤ ∑ _p ∈ touching D i, d := Finset.sum_le_sum (fun p _ => hD p)
    _ = (touching D i).card * d := by simp
    _ ≤ t * d := Nat.mul_le_mul_right d (ht i)

theorem nextSupport_card_bound (D : P → Finset I) (T : Finset I) (d t : ℕ)
    (hD : ∀ p, (D p).card ≤ d) (ht : ∀ i, (touching D i).card ≤ t) (j : P ⊕ T) :
    (nextSupport D T j).card ≤ max d (t * d) := by
  cases j with
  | inl p =>
    exact (Finset.card_le_card (Finset.sdiff_subset : D p \ T ⊆ D p)).trans
      ((hD p).trans (le_max_left _ _))
  | inr e =>
    exact (Finset.card_le_card (Finset.sdiff_subset :
      factorStar D e.val \ T ⊆ factorStar D e.val)).trans
      ((factorStar_card_bound D d t hD ht e).trans (le_max_right _ _))

theorem sourceSupport_card_bound (D : P → Finset I) (T Q : Finset I) (d t : ℕ)
    (hD : ∀ p, (D p).card ≤ d) (ht : ∀ i, (touching D i).card ≤ t) :
    (sourceSupport D T Q).card ≤ Q.card + (Q ∩ T).card * (t * d) := by
  calc
    _ ≤ Q.card + ∑ e ∈ Q ∩ T, (factorStar D e).card := sourceSupport_card D T Q
    _ ≤ Q.card + ∑ _e ∈ Q ∩ T, t * d :=
      Nat.add_le_add_left (Finset.sum_le_sum (fun e _ =>
        factorStar_card_bound D d t hD ht e)) _
    _ = _ := by simp
theorem selected_star_card (D : P → Finset I) (T : Finset I)
    (hT : Independent D T) (i : I) :
    (T.filter (fun e => i ∈ factorStar D e)).card ≤ (touching D i).card := by
  classical
  have hsub : T.filter (fun e => i ∈ factorStar D e) ⊆
      (touching D i).biUnion (fun p => D p ∩ T) := by
    intro e he
    obtain ⟨heT, hei⟩ := Finset.mem_filter.mp he
    obtain ⟨p, hep, hip⟩ := (mem_factorStar D e i).mp hei
    exact Finset.mem_biUnion.mpr ⟨p,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hip⟩, Finset.mem_inter.mpr ⟨hep, heT⟩⟩
  calc
    _ ≤ ((touching D i).biUnion (fun p => D p ∩ T)).card := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ touching D i, (D p ∩ T).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ touching D i, 1 := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.card_le_one.mpr
      intro e he d hd
      exact hT p e (Finset.mem_inter.mp he).2 d (Finset.mem_inter.mp hd).2
        (Finset.mem_inter.mp he).1 (Finset.mem_inter.mp hd).1
    _ = _ := by simp

theorem next_touching_card (D : P → Finset I) (T : Finset I)
    (hT : Independent D T) (i : I) :
    (touching (nextSupport D T) i).card ≤ 2 * (touching D i).card := by
  classical
  have hfirst : (∑ p, if i ∈ D p \ T then 1 else 0) ≤ (touching D i).card := by
    simp only [touching, Finset.card_filter]
    apply Finset.sum_le_sum
    intro p _
    by_cases hi : i ∈ D p
    · simp only [hi, ite_true]
      split_ifs <;> omega
    · simp [hi]
  have hsecond : (∑ e : T, if i ∈ factorStar D e.val \ T then 1 else 0) ≤
      (T.filter (fun e => i ∈ factorStar D e)).card := by
    rw [Finset.card_filter]
    rw [← Finset.sum_attach T (fun e => if i ∈ factorStar D e then 1 else 0)]
    change (∑ e : T, if i ∈ factorStar D e.val \ T then 1 else 0) ≤
      ∑ e : T, if i ∈ factorStar D e.val then 1 else 0
    apply Finset.sum_le_sum
    intro e _
    by_cases hi : i ∈ factorStar D e.val
    · simp only [hi, ite_true]
      split_ifs <;> omega
    · simp [hi]
  simp only [touching, Finset.card_filter, Fintype.sum_sum_type, nextSupport,
    Sum.elim_inl, Sum.elim_inr]
  have hh := selected_star_card D T hT i
  simp only [touching, Finset.card_filter] at hh hfirst hsecond
  omega

end Supports

section Response
variable {I P X : Type*} [Fintype P] [DecidableEq I]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- A source may depend on any number of selected coordinates. The literal
conditional response depends only on its computed retained neighborhood. -/
theorem block_response_dependsOn (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (T : Finset I) (hT : Independent D T) (F : (I → X) → ℝ)
    (hFc : Continuous F) (Q : Finset I) (hF : DependsOn F (Q : Set I)) :
    DependsOn (GibbsMarginalTower.response (Measure.pi (fun _ : T => μ))
      (fun z => action Φ (replace T z.1 z.2))
      (fun z => F (replace T z.1 z.2))) (sourceSupport D T Q : Set I) := by
  classical
  let x₀ : X := Classical.choice (nonempty_of_isProbabilityMeasure μ)
  let L : Finset T := Finset.univ.filter (fun e => e.val ∈ Q)
  let R : T → Finset I := fun e => factorStar D e.val \ T
  have hreplace : Continuous (fun z : (I → X) × (T → X) => replace T z.1 z.2) := by
    apply continuous_pi
    intro i
    by_cases hi : i ∈ T
    · simpa only [replace, dif_pos hi] using
        ((continuous_apply (⟨i, hi⟩ : T)).comp continuous_snd)
    · simpa only [replace, dif_neg hi] using ((continuous_apply i).comp continuous_fst)
  have hDF : ∀ V : T → X, DependsOn (fun U => F (replace T U V))
      ((Q \ T : Finset I) : Set I) := by
    intro V U U' hUU'
    apply hF
    intro i hi
    by_cases hiT : i ∈ T
    · simp only [replace, dif_pos hiT]
    · simp only [replace, dif_neg hiT]
      exact hUU' i (Finset.mem_sdiff.mpr ⟨hi, hiT⟩)
  have hLF : ∀ U : I → X, DependsOn (fun V => F (replace T U V)) (L : Set T) := by
    intro U V V' hVV'
    apply hF
    intro i hi
    by_cases hiT : i ∈ T
    · simp only [replace, dif_pos hiT]
      exact hVV' ⟨i, hiT⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    · simp only [replace, dif_neg hiT]
  have hs := ProductResponseSupport.response_dependsOn μ
    (retainedFactor Φ T x₀) (increment Φ T x₀)
    (fun z : (I → X) × (T → X) => F (replace T z.1 z.2))
    (retainedFactor_continuous Φ hΦc T x₀) (increment_continuous Φ hΦc T x₀)
    (hFc.comp hreplace) (Q \ T) R L (increment_dependsOn D Φ hΦ T x₀) hDF hLF
  have heq : (fun z : (I → X) × (T → X) => action Φ (replace T z.1 z.2)) =
      LocalPotentialElimination.firstAction (retainedFactor Φ T x₀) (increment Φ T x₀) :=
    funext (fun z => action_replace_eq_firstAction D Φ hΦ T hT x₀ z.1 z.2)
  rw [heq]
  apply hs.mono
  intro i hi
  change i ∈ (Q \ T) ∪ L.biUnion R at hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact (mem_sourceSupport D T Q i).mpr
      ⟨(Finset.mem_sdiff.mp hi).2, Or.inl (Finset.mem_sdiff.mp hi).1⟩
  · obtain ⟨e, he, hie⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨his, hiT⟩ := Finset.mem_sdiff.mp hie
    obtain ⟨p, hep, hip⟩ := (mem_factorStar D e.val i).mp his
    exact (mem_sourceSupport D T Q i).mpr
      ⟨hiT, Or.inr ⟨e.val, (Finset.mem_filter.mp he).2, e.property, p, hep, hip⟩⟩
end Response

section Relation
variable {I P : Type*} [Fintype P] [DecidableEq I]

/-- A radius-indexed relation can describe periodic offsets without choosing a metric. -/
def RelationDiameter (Close : ℕ → I → I → Prop) (D : P → Finset I) (r : ℕ) : Prop :=
  ∀ p, ∀ i ∈ D p, ∀ j ∈ D p, Close r i j

theorem factorStar_close (Close : ℕ → I → I → Prop) (D : P → Finset I) (r : ℕ)
    (hD : RelationDiameter Close D r) (e i : I) (hi : i ∈ factorStar D e) :
    Close r e i := by
  obtain ⟨p, hep, hip⟩ := (mem_factorStar D e i).mp hi
  exact hD p e hep i hip

/-- Exact induced interaction supports double the radius in any composable relation. -/
theorem nextSupport_relation (Close : ℕ → I → I → Prop)
    (hsymm : ∀ r i j, Close r i j → Close r j i)
    (hmono : ∀ r s i j, r ≤ s → Close r i j → Close s i j)
    (hadd : ∀ r s i j k, Close r i j → Close s j k → Close (r + s) i k)
    (D : P → Finset I) (T : Finset I) (r : ℕ) (hD : RelationDiameter Close D r) :
    RelationDiameter Close (nextSupport D T) (2 * r) := by
  intro p i hi j hj
  cases p with
  | inl p =>
    exact hmono r (2 * r) i j (by omega)
      (hD p i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).1)
  | inr e =>
    have h1 := hsymm r e.val i
      (factorStar_close Close D r hD e i (Finset.mem_sdiff.mp hi).1)
    have h2 := factorStar_close Close D r hD e j (Finset.mem_sdiff.mp hj).1
    simpa only [two_mul] using hadd r r i e j h1 h2

theorem sourceSupport_relation (Close : ℕ → I → I → Prop)
    (hmono : ∀ r s i j, r ≤ s → Close r i j → Close s i j)
    (hadd : ∀ r s i j k, Close r i j → Close s j k → Close (r + s) i k)
    (D : P → Finset I) (T Q : Finset I) (r s : ℕ)
    (hD : RelationDiameter Close D r) (o : I) (hQ : ∀ i ∈ Q, Close s o i) :
    ∀ i ∈ sourceSupport D T Q, Close (s + r) o i := by
  intro i hi
  rcases ((mem_sourceSupport D T Q i).mp hi).2 with hiQ | ⟨e, heQ, _, p, hep, hip⟩
  · exact hmono s (s + r) o i (Nat.le_add_right _ _) (hQ i hiQ)
  · exact hadd s r o e i (hQ e heQ) (hD p e hep i hip)

omit [DecidableEq I] in
theorem overlap_relation (Close : ℕ → I → I → Prop)
    (hsymm : ∀ r i j, Close r i j → Close r j i)
    (hadd : ∀ r s i j k, Close r i j → Close s j k → Close (r + s) i k)
    (A B : Finset I) (o o' : I) (s t : ℕ)
    (hA : ∀ i ∈ A, Close s o i) (hB : ∀ i ∈ B, Close t o' i)
    (hAB : ¬Disjoint A B) : Close (s + t) o o' := by
  obtain ⟨i, hiA, hiB⟩ := Finset.not_disjoint_iff.mp hAB
  exact hadd s t o i o' (hA i hiA) (hsymm t o' i (hB i hiB))
/-- The computed factor family satisfies the dyadic radius step exactly. -/
theorem nextSupport_dyadic (Close : ℕ → I → I → Prop)
    (hsymm : ∀ r i j, Close r i j → Close r j i)
    (hmono : ∀ r s i j, r ≤ s → Close r i j → Close s i j)
    (hadd : ∀ r s i j k, Close r i j → Close s j k → Close (r + s) i k)
    (D : P → Finset I) (T : Finset I) (j : ℕ)
    (hD : RelationDiameter Close D (2 ^ j)) :
    RelationDiameter Close (nextSupport D T) (2 ^ (j + 1)) := by
  simpa only [pow_succ'] using nextSupport_relation Close hsymm hmono hadd D T (2 ^ j) hD

/-- The same dyadic envelope propagates the actual arbitrary-source support. -/
theorem sourceSupport_dyadic (Close : ℕ → I → I → Prop)
    (hmono : ∀ r s i j, r ≤ s → Close r i j → Close s i j)
    (hadd : ∀ r s i j k, Close r i j → Close s j k → Close (r + s) i k)
    (D : P → Finset I) (T Q : Finset I) (j : ℕ)
    (hD : RelationDiameter Close D (2 ^ j)) (o : I)
    (hQ : ∀ i ∈ Q, Close (2 ^ j) o i) :
    ∀ i ∈ sourceSupport D T Q, Close (2 ^ (j + 1)) o i := by
  simpa only [pow_succ', two_mul] using
    sourceSupport_relation Close hmono hadd D T Q (2 ^ j) (2 ^ j) hD o hQ

end Relation

section Metric
variable {I P : Type*} [Fintype P] [DecidableEq I] [PseudoMetricSpace I]

/-- All pairs within each factor support have distance at most the stated radius. -/
def DiameterBound (D : P → Finset I) (r : ℝ) : Prop :=
  ∀ p, ∀ i ∈ D p, ∀ j ∈ D p, dist i j ≤ r

theorem factorStar_dist (D : P → Finset I) (r : ℝ) (hD : DiameterBound D r)
    (e i : I) (hi : i ∈ factorStar D e) : dist e i ≤ r := by
  obtain ⟨p, hep, hip⟩ := (mem_factorStar D e i).mp hi
  exact hD p e hep i hip

theorem factorStar_diameter (D : P → Finset I) (r : ℝ) (hD : DiameterBound D r)
    (e i j : I) (hi : i ∈ factorStar D e) (hj : j ∈ factorStar D e) :
    dist i j ≤ 2 * r := by
  have h1 := factorStar_dist D r hD e i hi
  have h2 := factorStar_dist D r hD e j hj
  calc
    dist i j ≤ dist i e + dist e j := dist_triangle _ _ _
    _ = dist e i + dist e j := by rw [dist_comm i e]
    _ ≤ 2 * r := by linarith

/-- Exact generated factors have at most twice the preceding interaction diameter. -/
theorem nextSupport_diameter (D : P → Finset I) (T : Finset I) (r : ℝ)
    (hr : 0 ≤ r) (hD : DiameterBound D r) :
    DiameterBound (nextSupport D T) (2 * r) := by
  intro p i hi j hj
  cases p with
  | inl p =>
    have hh := hD p i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).1
    linarith
  | inr e =>
    exact factorStar_diameter D r hD e i j
      (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1

/-- An arbitrary source expands by one preceding factor radius at this step. -/
theorem sourceSupport_radius (D : P → Finset I) (T Q : Finset I)
    (r s : ℝ) (hr : 0 ≤ r) (hD : DiameterBound D r) (o : I)
    (hQ : ∀ i ∈ Q, dist o i ≤ s) :
    ∀ i ∈ sourceSupport D T Q, dist o i ≤ s + r := by
  intro i hi
  rcases ((mem_sourceSupport D T Q i).mp hi).2 with hiQ | ⟨e, heQ, _, p, hep, hip⟩
  · exact (hQ i hiQ).trans (le_add_of_nonneg_right hr)
  · exact (dist_triangle o e i).trans (add_le_add (hQ e heQ) (hD p e hep i hip))

omit [DecidableEq I] in
/-- Overlap of two evolved source supports bounds the separation of their centers. -/
theorem overlap_centers (A B : Finset I) (o o' : I) (s t : ℝ)
    (hA : ∀ i ∈ A, dist o i ≤ s) (hB : ∀ i ∈ B, dist o' i ≤ t)
    (hAB : ¬Disjoint A B) : dist o o' ≤ s + t := by
  obtain ⟨i, hiA, hiB⟩ := Finset.not_disjoint_iff.mp hAB
  calc
    dist o o' ≤ dist o i + dist i o' := dist_triangle _ _ _
    _ = dist o i + dist o' i := by rw [dist_comm i o']
    _ ≤ s + t := add_le_add (hA i hiA) (hB i hiB)
end Metric

/-- Explicit interaction-radius envelope after j exact elimination steps. -/
def radiusEnvelope (r₀ : ℝ) (j : ℕ) : ℝ := 2 ^ j * r₀

/-- Explicit source-radius envelope; each preceding interaction radius is added once. -/
def sourceEnvelope (s₀ r₀ : ℝ) (j : ℕ) : ℝ := s₀ + (2 ^ j - 1) * r₀

theorem radiusEnvelope_zero (r₀ : ℝ) : radiusEnvelope r₀ 0 = r₀ := by
  simp [radiusEnvelope]

theorem radiusEnvelope_succ (r₀ : ℝ) (j : ℕ) :
    radiusEnvelope r₀ (j + 1) = 2 * radiusEnvelope r₀ j := by
  simp only [radiusEnvelope, pow_succ]
  ring

theorem sourceEnvelope_zero (s₀ r₀ : ℝ) : sourceEnvelope s₀ r₀ 0 = s₀ := by
  simp [sourceEnvelope]

theorem sourceEnvelope_succ (s₀ r₀ : ℝ) (j : ℕ) :
    sourceEnvelope s₀ r₀ (j + 1) = sourceEnvelope s₀ r₀ j + radiusEnvelope r₀ j := by
  simp only [sourceEnvelope, radiusEnvelope, pow_succ]
  ring

theorem radiusEnvelope_nonneg (r₀ : ℝ) (hr : 0 ≤ r₀) (j : ℕ) :
    0 ≤ radiusEnvelope r₀ j := mul_nonneg (by positivity) hr

end
end UnifiedTheory.Clay.YangMills.FiniteFactorSupportGrowth
