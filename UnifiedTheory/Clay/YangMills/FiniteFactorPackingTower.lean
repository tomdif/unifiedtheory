/- Iterated maximal independent block packing for arbitrary finite factor towers.
At every stage the block is selected by maximal packing on the actual evolved
support hypergraph inside the remaining active inventory. This yields automatic
stagewise admissibility, quantitative stage density bounds, and complete
exhaustion of the active coordinate inventory in at most |B| steps. -/
import UnifiedTheory.Clay.YangMills.FiniteFactorPacking
import UnifiedTheory.Clay.YangMills.GibbsExhaustedTower

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.FiniteFactorPackingTower
noncomputable section
open MeasureTheory FiniteFactorConditional FiniteFactorElimination
open FiniteFactorSupportGrowth FiniteFactorIteration FiniteFactorResponseIteration
open FiniteFactorPacking GibbsExhaustedTower

universe u v
variable {I P : Type u} {X : Type v}

/-- Two support families with the same independent sets produce identical candidate families. -/
theorem candidates_eq_of_independent_iff {P₁ P₂ : Type u}
    (D₁ : P₁ → Finset I) (D₂ : P₂ → Finset I) (U : Finset I)
    (h : ∀ S : Finset I, Independent D₁ S ↔ Independent D₂ S) :
    candidates D₁ U = candidates D₂ U := by
  classical
  unfold candidates
  apply Finset.filter_congr
  intro S _
  exact h S

private theorem maxCard_choose_congr {C₁ C₂ : Finset (Finset I)} (hC : C₁ = C₂)
    (h₁ : C₁.Nonempty) (h₂ : C₂.Nonempty) :
    Classical.choose (C₁.exists_max_image Finset.card h₁) =
      Classical.choose (C₂.exists_max_image Finset.card h₂) := by
  subst hC
  rfl

/-- Maximal block selection depends only on the equivalence class of independent subsets. -/
theorem chosenBlock_eq_of_independent_iff {P₁ P₂ : Type u}
    (D₁ : P₁ → Finset I) (D₂ : P₂ → Finset I) (U : Finset I)
    (h : ∀ S : Finset I, Independent D₁ S ↔ Independent D₂ S) :
    chosenBlock D₁ U = chosenBlock D₂ U :=
  maxCard_choose_congr (candidates_eq_of_independent_iff D₁ D₂ U h)
    (candidates_nonempty D₁ U) (candidates_nonempty D₂ U)

/-- Reindexing the factor index type preserves block independence. -/
theorem independent_iff_of_equiv {P₁ P₂ : Type u}
    (D₁ : P₁ → Finset I) (D₂ : P₂ → Finset I) (e : P₁ ≃ P₂)
    (he : ∀ p, D₁ p = D₂ (e p)) (S : Finset I) :
    Independent D₁ S ↔ Independent D₂ S := by
  constructor
  · intro h p₂ i hi j hj hip hjp
    have hip' : i ∈ D₁ (e.symm p₂) := by rw [he, Equiv.apply_symm_apply]; exact hip
    have hjp' : j ∈ D₁ (e.symm p₂) := by rw [he, Equiv.apply_symm_apply]; exact hjp
    exact h (e.symm p₂) i hi j hj hip' hjp'
  · intro h p₁ i hi j hj hip hjp
    rw [he] at hip hjp
    exact h (e p₁) i hi j hj hip hjp

variable [DecidableEq I]

/-- Reindexing the factor index type preserves factor stars. -/
theorem factorStar_eq_of_equiv {P₁ P₂ : Type u} [Fintype P₁] [Fintype P₂]
    (D₁ : P₁ → Finset I) (D₂ : P₂ → Finset I) (e : P₁ ≃ P₂)
    (he : ∀ p, D₁ p = D₂ (e p)) (i : I) :
    factorStar D₁ i = factorStar D₂ i := by
  ext j
  simp only [mem_factorStar]
  constructor
  · rintro ⟨p₁, hi, hj⟩
    rw [he] at hi hj
    exact ⟨e p₁, hi, hj⟩
  · rintro ⟨p₂, hi, hj⟩
    refine ⟨e.symm p₂, ?_, ?_⟩
    · rw [he, Equiv.apply_symm_apply]; exact hi
    · rw [he, Equiv.apply_symm_apply]; exact hj

/-- Reindexing the factor index type intertwines one-step evolved support families. -/
theorem nextSupport_eq_of_equiv {P₁ P₂ : Type u} [Fintype P₁] [Fintype P₂]
    (D₁ : P₁ → Finset I) (D₂ : P₂ → Finset I) (e : P₁ ≃ P₂)
    (he : ∀ p, D₁ p = D₂ (e p)) (T : Finset I) (x : P₁ ⊕ T) :
    nextSupport D₁ T x = nextSupport D₂ T (Equiv.sumCongr e (Equiv.refl T) x) := by
  rcases x with p | i
  · simp only [nextSupport, Equiv.sumCongr_apply, Sum.map_inl, Sum.elim_inl, he p]
  · simp only [nextSupport, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply, Sum.elim_inr,
      factorStar_eq_of_equiv D₁ D₂ e he i.val]

/-- Bundled stage data for recursive maximal-packing elimination. -/
structure PackedStage (I : Type u) where
  Idx : Type u
  instFintype : Fintype Idx
  supp : Idx → Finset I
  act : Finset I

/-- One recursive step of maximal independent packing and support evolution. -/
def packedStep (S : PackedStage I) : PackedStage I :=
  letI : Fintype S.Idx := S.instFintype
  let blk := chosenBlock S.supp S.act
  ⟨S.Idx ⊕ blk, inferInstance, nextSupport S.supp blk, S.act \ blk⟩

variable [Fintype P]

/-- Recursive sequence of bundled maximal-packing stages. -/
def packedStage (D : P → Finset I) (B : Finset I) : ℕ → PackedStage I
  | 0 => ⟨P, inferInstance, D, B⟩
  | k + 1 => packedStep (packedStage D B k)

/-- The canonical iterated maximal-packing elimination schedule. -/
def packedSchedule (D : P → Finset I) (B : Finset I) (k : ℕ) : Finset I :=
  chosenBlock (packedStage D B k).supp (packedStage D B k).act

/-- The bundled active set agrees at every depth with the tower active coordinate set. -/
theorem packedStage_act_eq_active (D : P → Finset I) (B : Finset I) :
    ∀ k, (packedStage D B k).act = active B (packedSchedule D B) k
  | 0 => rfl
  | k + 1 => by
    change (packedStage D B k).act \ packedSchedule D B k =
      active B (packedSchedule D B) k \ packedSchedule D B k
    rw [packedStage_act_eq_active D B k]

/-- Canonical index equivalence between the bundled stage and the tower factor index. -/
def packedIndexEquiv (D : P → Finset I) (B : Finset I) :
    (k : ℕ) → (packedStage D B k).Idx ≃ Index P (packedSchedule D B) k
  | 0 => Equiv.refl P
  | k + 1 => Equiv.sumCongr (packedIndexEquiv D B k) (Equiv.refl (packedSchedule D B k))

/-- The bundled support family agrees with the tower support family under the index equivalence. -/
theorem packedStage_supp_eq_supports (D : P → Finset I) (B : Finset I) :
    ∀ k (p : (packedStage D B k).Idx),
      (packedStage D B k).supp p =
        supports D (packedSchedule D B) k (packedIndexEquiv D B k p)
  | 0, _ => rfl
  | k + 1, x => by
    letI : Fintype (packedStage D B k).Idx := (packedStage D B k).instFintype
    exact nextSupport_eq_of_equiv (packedStage D B k).supp
      (supports D (packedSchedule D B) k) (packedIndexEquiv D B k)
      (packedStage_supp_eq_supports D B k) (packedSchedule D B k) x

/-- Every stage of the packed schedule is the maximal independent block for the evolved supports. -/
theorem packedSchedule_eq_chosenBlock (D : P → Finset I) (B : Finset I) (k : ℕ) :
    packedSchedule D B k =
      chosenBlock (supports D (packedSchedule D B) k) (active B (packedSchedule D B) k) := by
  unfold packedSchedule
  rw [packedStage_act_eq_active D B k]
  exact chosenBlock_eq_of_independent_iff (packedStage D B k).supp
    (supports D (packedSchedule D B) k) (active B (packedSchedule D B) k)
    (independent_iff_of_equiv (packedStage D B k).supp
      (supports D (packedSchedule D B) k) (packedIndexEquiv D B k)
      (packedStage_supp_eq_supports D B k))

/-- The iterated maximal-packing schedule is automatically admissible at every depth. -/
theorem packedSchedule_admissible (D : P → Finset I) (B : Finset I) :
    ∀ k, Independent (supports D (packedSchedule D B) k) (packedSchedule D B k) := by
  intro k
  rw [packedSchedule_eq_chosenBlock]
  exact chosenBlock_independent _ _

/-- Each selected block is contained in the remaining active coordinate set. -/
theorem packedSchedule_subset_active (D : P → Finset I) (B : Finset I) :
    ∀ k, packedSchedule D B k ⊆ active B (packedSchedule D B) k := by
  intro k
  rw [packedSchedule_eq_chosenBlock]
  exact chosenBlock_subset _ _

omit [Fintype P] in
/-- Active coordinate sets shrink monotonically with elimination depth. -/
theorem active_subset_of_le (B : Finset I) (T : ℕ → Finset I) {j k : ℕ} (hjk : j ≤ k) :
    active B T k ⊆ active B T j := by
  induction hjk with
  | refl => exact Finset.Subset.rfl
  | @step m _ ih => exact Finset.sdiff_subset.trans ih

omit [Fintype P] in
/-- Any earlier eliminated block is disjoint from all later active coordinate sets. -/
theorem disjoint_active_of_lt (B : Finset I) (T : ℕ → Finset I) {j k : ℕ} (hjk : j < k) :
    Disjoint (T j) (active B T k) := by
  have hsub : active B T k ⊆ active B T (j + 1) := active_subset_of_le B T hjk
  exact Disjoint.mono_right hsub Finset.sdiff_disjoint.symm

/-- Distinct stages of the packed schedule eliminate pairwise disjoint coordinate blocks. -/
theorem packedSchedule_disjoint (D : P → Finset I) (B : Finset I) {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (packedSchedule D B j) (packedSchedule D B k) := by
  rcases lt_or_gt_of_ne hjk with hlt | hgt
  · exact Disjoint.mono_right (packedSchedule_subset_active D B k)
      (disjoint_active_of_lt B (packedSchedule D B) hlt)
  · exact (Disjoint.mono_right (packedSchedule_subset_active D B j)
      (disjoint_active_of_lt B (packedSchedule D B) hgt)).symm

/-- Whenever active coordinates remain, the packed block at that stage is nonempty. -/
theorem packedSchedule_nonempty (D : P → Finset I) (B : Finset I) (k : ℕ)
    (hk : (active B (packedSchedule D B) k).Nonempty) :
    (packedSchedule D B k).Nonempty := by
  rw [packedSchedule_eq_chosenBlock]
  exact chosenBlock_nonempty _ _ hk

/-- Every nonterminal stage strictly decreases the number of active coordinates. -/
theorem active_card_decreases_step (D : P → Finset I) (B : Finset I) (k : ℕ)
    (hk : (active B (packedSchedule D B) k).Nonempty) :
    (active B (packedSchedule D B) (k + 1)).card <
      (active B (packedSchedule D B) k).card := by
  change (active B (packedSchedule D B) k \ packedSchedule D B k).card < _
  rw [packedSchedule_eq_chosenBlock]
  exact active_card_decreases _ _ hk

/-- At depth k, at most |B| - k active coordinates remain. -/
theorem active_card_le_sub (D : P → Finset I) (B : Finset I) :
    ∀ k, (active B (packedSchedule D B) k).card ≤ B.card - k := by
  intro k
  induction k with
  | zero => simp [active]
  | succ k ih =>
    by_cases hk : (active B (packedSchedule D B) k).Nonempty
    · have hlt := active_card_decreases_step D B k hk
      have hpos := Finset.card_pos.mpr hk
      omega
    · have hempty : active B (packedSchedule D B) k = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hk
      have hnext : active B (packedSchedule D B) (k + 1) = ∅ := by
        simp [active, hempty]
      simp [hnext]

/-- The active coordinate inventory is completely exhausted by depth |B|. -/
theorem active_eq_empty_of_card_le (D : P → Finset I) (B : Finset I) {k : ℕ}
    (hk : B.card ≤ k) : active B (packedSchedule D B) k = ∅ := by
  have hle := active_card_le_sub D B k
  have hz : (active B (packedSchedule D B) k).card = 0 := by omega
  exact Finset.card_eq_zero.mp hz

/-- At depth equal to the initial inventory cardinality, no active coordinates remain. -/
theorem active_exhausted (D : P → Finset I) (B : Finset I) :
    active B (packedSchedule D B) B.card = ∅ :=
  active_eq_empty_of_card_le D B le_rfl

/-- Quantitative density lower bound for the initial packed block. -/
theorem packedSchedule_zero_card_bound (D : P → Finset I) (B : Finset I)
    (d₀ t₀ : ℕ) (hD : ∀ p, (D p).card ≤ d₀) (ht : ∀ i, (touching D i).card ≤ t₀) :
    B.card ≤ (t₀ * d₀ + 1) * (packedSchedule D B 0).card := by
  rw [packedSchedule_eq_chosenBlock]
  exact chosenBlock_card_bound_of_incidence D B d₀ t₀ hD ht

/-- Quantitative density lower bound at arbitrary stage k using the evolved support bounds. -/
theorem packedSchedule_stage_card_bound (D : P → Finset I) (B : Finset I)
    (d₀ t₀ : ℕ) (hD : ∀ p, (D p).card ≤ d₀) (ht : ∀ i, (touching D i).card ≤ t₀) (k : ℕ) :
    (active B (packedSchedule D B) k).card ≤
      (2 ^ k * t₀ * sizeEnvelope d₀ t₀ k + 1) * (packedSchedule D B k).card := by
  rw [packedSchedule_eq_chosenBlock]
  exact chosenBlock_card_bound_of_incidence
    (supports D (packedSchedule D B) k) (active B (packedSchedule D B) k)
    (sizeEnvelope d₀ t₀ k) (2 ^ k * t₀)
    (supports_card D (packedSchedule D B) (packedSchedule_admissible D B) d₀ t₀ hD ht k)
    (supports_incidence D (packedSchedule D B) (packedSchedule_admissible D B) t₀ ht k)

section ExhaustedCovariance
variable [Fintype I] [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- Under the iterated maximal-packing schedule, the retained covariance vanishes once N ≥ |B|. -/
theorem packedSchedule_covarianceAt_eq_zero (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (F G : C(I → X, ℝ)) (Q B : Finset I) (hF : DependsOn F (Q : Set I))
    (hD : ∀ p, D p ⊆ B) (hQ : Q ⊆ B) (N : ℕ) (hN : B.card ≤ N) :
    GibbsCoordinateTower.covarianceAt μ (packedSchedule D B)
      ⟨action Φ, action_continuous Φ hΦc⟩ F G N = 0 :=
  covarianceAt_eq_zero_of_exhausted μ D Φ hΦc hΦ (packedSchedule D B)
    (packedSchedule_admissible D B) F G Q B hF hD hQ N
    (active_eq_empty_of_card_le D B hN)

/-- Under the iterated maximal-packing schedule, the initial covariance equals the finite sum of
removed stage covariances through any exhaustion depth N ≥ |B|. -/
theorem packedSchedule_covariance_eq_sum (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (F G : C(I → X, ℝ)) (Q B : Finset I) (hF : DependsOn F (Q : Set I))
    (hD : ∀ p, D p ⊆ B) (hQ : Q ⊆ B) (N : ℕ) (hN : B.card ≤ N) :
    GibbsCoordinateTower.covarianceAt μ (packedSchedule D B)
      ⟨action Φ, action_continuous Φ hΦc⟩ F G 0 =
      ∑ k ∈ Finset.range N,
        GibbsCoordinateTower.coefficient μ (packedSchedule D B)
          ⟨action Φ, action_continuous Φ hΦc⟩ F G k :=
  exhausted_covariance_eq_sum μ D Φ hΦc hΦ (packedSchedule D B)
    (packedSchedule_admissible D B) F G Q B hF hD hQ N
    (active_eq_empty_of_card_le D B hN)

end ExhaustedCovariance
end
end UnifiedTheory.Clay.YangMills.FiniteFactorPackingTower
