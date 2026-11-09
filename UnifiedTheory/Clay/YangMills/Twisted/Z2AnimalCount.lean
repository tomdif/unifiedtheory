/- Lattice-animal count for the `C`-connected spanning sets of `Z2StrongCoupling`, discharging the hypothesis
`hcount` of `area_law`.

Setup: `Δ` bounds the number of plaquettes sharing an edge with any given plaquette (the plaquette itself included),
and `T` is the set of plaquettes touching `C`.

* `rooted inc R S`: every plaquette of `S` is reachable, through plaquettes of `S` sharing an edge, from a plaquette
  of `S ∩ R`. (Several components are allowed, each must meet `R`.)
* `weight_le` (generating-function bound, by a one-seed deletion recursion): for `x = 2^{-Δ}`,
  `Σ_{S ⊆ U, rooted R S} x^|S| ≤ 2^|R ∩ U|`.
  Recursion: pick a seed `r ∈ R ∩ U`. Sets avoiding `r` are rooted sets of `U \ {r}`; for sets containing `r`,
  `S \ {r}` is rooted at `R ∪ N(r)` (`rooted_erase`), and `|N(r)| ≤ Δ`, so the bound `2^{m-1} + x 2^{m-1+Δ} = 2^m`.
* `span_count`: `#{S ∈ span inc C, |S| = n} ≤ 2^|T| · (2^Δ)^n`.
* `area_law_unconditional`: for `0 ≤ t`, `2^Δ t < 1`, and `A` a lower bound on the size of every spanning set,
  `⟨W_C⟩ = N_C/N_∅ ≤ 2^|T| (2^Δ t)^A / (1 - 2^Δ t)`.
-/
import Mathlib
import UnifiedTheory.Clay.YangMills.Twisted.Z2StrongCoupling

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

open Finset Classical

namespace UnifiedTheory.Clay.YangMills.Twisted.Z2AnimalCount

open UnifiedTheory.Clay.YangMills.Twisted.Z2StrongCoupling

variable {P E : Type*} [Fintype P] [Fintype E] [DecidableEq P] [DecidableEq E]

/-- Every plaquette of `S` is connected within `S` to a plaquette of `S ∩ R`. -/
def rooted (inc : P → Finset E) (R S : Finset P) : Prop :=
  ∀ p ∈ S, ∃ q ∈ S, q ∈ R ∧ Relation.ReflTransGen (adj inc S) q p

/-- Plaquettes sharing an edge with `r`. -/
noncomputable def nbr (inc : P → Finset E) (r : P) : Finset P :=
  univ.filter (fun q => (inc r ∩ inc q).Nonempty)

/-- Generating function of rooted subsets of `U`. -/
noncomputable def G (inc : P → Finset E) (x : ℝ) (U R : Finset P) : ℝ :=
  ∑ S ∈ U.powerset.filter (fun S => rooted inc R S), x ^ S.card

theorem rooted_erase (inc : P → Finset E) {R S : Finset P} {r : P} (h : rooted inc R S) :
    rooted inc (R ∪ nbr inc r) (S.erase r) := by
  intro p hp
  obtain ⟨hpr, hpS⟩ := Finset.mem_erase.mp hp
  obtain ⟨q, hqS, hqR, hqp⟩ := h p hpS
  have main : ∀ b, Relation.ReflTransGen (adj inc S) q b → b ≠ r →
      ∃ q' ∈ S.erase r, q' ∈ R ∪ nbr inc r ∧ Relation.ReflTransGen (adj inc (S.erase r)) q' b := by
    intro b hb
    induction hb with
    | refl =>
      intro hne
      exact ⟨q, Finset.mem_erase.mpr ⟨hne, hqS⟩, Finset.mem_union_left _ hqR, Relation.ReflTransGen.refl⟩
    | @tail b c _ hbc ih =>
      intro hc
      obtain ⟨hb, hcS, hne⟩ := hbc
      have hcE : c ∈ S.erase r := Finset.mem_erase.mpr ⟨hc, hcS⟩
      by_cases hbr : b = r
      · subst hbr
        refine ⟨c, hcE, Finset.mem_union_right _ ?_, Relation.ReflTransGen.refl⟩
        simp only [nbr, mem_filter, mem_univ, true_and]; exact hne
      · obtain ⟨q', hq'E, hq'R, hq'b⟩ := ih hbr
        exact ⟨q', hq'E, hq'R, hq'b.tail ⟨Finset.mem_erase.mpr ⟨hbr, hb⟩, hcE, hne⟩⟩
  exact main p hqp hpr

theorem rooted_empty_of (inc : P → Finset E) {R S U : Finset P} (h : rooted inc R S) (hSU : S ⊆ U)
    (hRU : R ∩ U = ∅) : S = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro p hp
  obtain ⟨q, hqS, hqR, _⟩ := h p hp
  have : q ∈ R ∩ U := Finset.mem_inter.mpr ⟨hqR, hSU hqS⟩
  rw [hRU] at this; exact Finset.notMem_empty _ this

theorem weight_le (inc : P → Finset E) (Δ : ℕ) (hΔ : ∀ r, (nbr inc r).card ≤ Δ) (U R : Finset P) :
    G inc ((2 : ℝ) ^ Δ)⁻¹ U R ≤ 2 ^ (R ∩ U).card := by
  set x : ℝ := ((2 : ℝ) ^ Δ)⁻¹ with hx
  have hx0 : 0 ≤ x := by positivity
  induction U using Finset.strongInduction generalizing R with
  | H U ih =>
    by_cases hRU : R ∩ U = ∅
    · -- only the empty set is rooted
      have hsub : U.powerset.filter (fun S => rooted inc R S) ⊆ {∅} := by
        intro S hS
        obtain ⟨hSU, hS⟩ := Finset.mem_filter.mp hS
        rw [Finset.mem_powerset] at hSU
        rw [Finset.mem_singleton]; exact rooted_empty_of inc hS hSU hRU
      unfold G
      calc ∑ S ∈ U.powerset.filter (fun S => rooted inc R S), x ^ S.card
          ≤ ∑ S ∈ ({∅} : Finset (Finset P)), x ^ S.card :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
        _ = 1 := by simp
        _ ≤ 2 ^ (R ∩ U).card := one_le_pow₀ (by norm_num)
    · obtain ⟨r, hr⟩ := Finset.nonempty_iff_ne_empty.mpr hRU
      obtain ⟨hrR, hrU⟩ := Finset.mem_inter.mp hr
      set U' := U.erase r
      have hU' : U' ⊂ U := Finset.erase_ssubset hrU
      set m' := (R ∩ U').card
      have hm : (R ∩ U).card = m' + 1 := by
        simp only [m', U', Finset.inter_erase]
        rw [Finset.card_erase_of_mem hr]
        have : 0 < (R ∩ U).card := Finset.card_pos.mpr ⟨r, hr⟩
        omega
      have hm2 : ((R ∪ nbr inc r) ∩ U').card ≤ m' + Δ := by
        calc ((R ∪ nbr inc r) ∩ U').card ≤ ((R ∩ U') ∪ nbr inc r).card := by
              apply Finset.card_le_card
              intro q hq
              simp only [mem_inter, mem_union] at hq ⊢
              tauto
          _ ≤ (R ∩ U').card + (nbr inc r).card := Finset.card_union_le _ _
          _ ≤ m' + Δ := by have := hΔ r; omega
      have ih1 := ih U' hU' R
      have ih2 := ih U' hU' (R ∪ nbr inc r)
      have ih2' : G inc x U' (R ∪ nbr inc r) ≤ 2 ^ (m' + Δ) :=
        le_trans ih2 (pow_le_pow_right₀ (by norm_num) hm2)
      set A := U.powerset.filter (fun S => rooted inc R S)
      unfold G
      rw [← Finset.sum_filter_add_sum_filter_not A (fun S => r ∈ S)]
      -- sets avoiding `r`
      have hB : ∑ S ∈ A.filter (fun S => ¬ r ∈ S), x ^ S.card ≤ G inc x U' R := by
        unfold G
        apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
        intro S hS
        simp only [A, mem_filter, mem_powerset] at hS ⊢
        refine ⟨?_, hS.1.2⟩
        intro q hq
        exact Finset.mem_erase.mpr ⟨fun h => hS.2 (h ▸ hq), hS.1.1 hq⟩
      -- sets containing `r`
      have hC : ∑ S ∈ A.filter (fun S => r ∈ S), x ^ S.card ≤ x * G inc x U' (R ∪ nbr inc r) := by
        have hinj : Set.InjOn (fun S : Finset P => S.erase r) (A.filter (fun S => r ∈ S)) := by
          intro S hS S' hS' h
          simp only [coe_filter, Set.mem_setOf_eq] at hS hS'
          have h1 := Finset.insert_erase hS.2
          have h2 := Finset.insert_erase hS'.2
          simp only at h
          rw [← h1, ← h2, h]
        have hsum : ∑ S ∈ A.filter (fun S => r ∈ S), x ^ S.card =
            x * ∑ S' ∈ (A.filter (fun S => r ∈ S)).image (fun S => S.erase r), x ^ S'.card := by
          rw [Finset.sum_image hinj, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S hS
          have hrS : r ∈ S := (Finset.mem_filter.mp hS).2
          have hc := Finset.card_erase_add_one hrS
          rw [← hc, pow_succ]; ring
        rw [hsum]
        apply mul_le_mul_of_nonneg_left _ hx0
        unfold G
        apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
        intro S' hS'
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hS'
        simp only [A, mem_filter, mem_powerset] at hS ⊢
        exact ⟨Finset.erase_subset_erase r hS.1.1, rooted_erase inc hS.1.2⟩
      have hxp : x * 2 ^ (m' + Δ) = 2 ^ m' := by
        rw [hx, pow_add]; field_simp
      calc ∑ S ∈ A.filter (fun S => r ∈ S), x ^ S.card + ∑ S ∈ A.filter (fun S => ¬ r ∈ S), x ^ S.card
          ≤ x * 2 ^ (m' + Δ) + 2 ^ m' := by
            gcongr
            · exact le_trans hC (mul_le_mul_of_nonneg_left ih2' hx0)
            · exact le_trans hB ih1
        _ = 2 ^ (R ∩ U).card := by rw [hxp, hm, pow_succ]; ring

/-- Count of rooted sets of size `n`: `≤ 2^|R| (2^Δ)^n`. -/
theorem rooted_count (inc : P → Finset E) (Δ : ℕ) (hΔ : ∀ r, (nbr inc r).card ≤ Δ) (R : Finset P) (n : ℕ) :
    ((((univ : Finset P).powerset.filter (fun S => rooted inc R S)).filter (fun S => S.card = n)).card : ℝ)
      ≤ 2 ^ R.card * ((2 : ℝ) ^ Δ) ^ n := by
  set x : ℝ := ((2 : ℝ) ^ Δ)⁻¹
  have hx : 0 < x := by positivity
  set F := (univ : Finset P).powerset.filter (fun S => rooted inc R S)
  have hW := weight_le inc Δ hΔ univ R
  rw [Finset.inter_univ] at hW
  have h1 : ((F.filter (fun S => S.card = n)).card : ℝ) * x ^ n ≤ G inc x univ R := by
    unfold G
    calc ((F.filter (fun S => S.card = n)).card : ℝ) * x ^ n
        = ∑ S ∈ F.filter (fun S => S.card = n), x ^ S.card := by
          rw [Finset.sum_congr rfl (fun S hS => by rw [(Finset.mem_filter.mp hS).2]), Finset.sum_const,
            nsmul_eq_mul]
      _ ≤ ∑ S ∈ F, x ^ S.card :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
  have hxn : x ^ n * ((2 : ℝ) ^ Δ) ^ n = 1 := by
    rw [← mul_pow]; simp [x]
  calc ((F.filter (fun S => S.card = n)).card : ℝ)
      = ((F.filter (fun S => S.card = n)).card : ℝ) * x ^ n * ((2 : ℝ) ^ Δ) ^ n := by
        rw [mul_assoc, hxn, mul_one]
    _ ≤ 2 ^ R.card * ((2 : ℝ) ^ Δ) ^ n :=
        mul_le_mul_of_nonneg_right (le_trans h1 hW) (by positivity)

/-- **Lattice-animal count** for `C`-connected spanning sets: with `Δ` a bound on the number of plaquettes
sharing an edge with any plaquette and `T` the plaquettes touching `C`,
`#{S ∈ span inc C, |S| = n} ≤ 2^|T| · (2^Δ)^n`. -/
theorem span_count (inc : P → Finset E) (C : Finset E) (Δ : ℕ)
    (hΔ : ∀ p, ((univ : Finset P).filter (fun q => (inc p ∩ inc q).Nonempty)).card ≤ Δ) (n : ℕ) :
    (((span inc C).filter (fun S => S.card = n)).card : ℝ) ≤
      2 ^ ((univ : Finset P).filter (fun p => (inc p ∩ C).Nonempty)).card * ((2 : ℝ) ^ Δ) ^ n := by
  set T := (univ : Finset P).filter (fun p => (inc p ∩ C).Nonempty)
  refine le_trans ?_ (rooted_count inc Δ hΔ T n)
  norm_cast
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  intro S hS
  simp only [span, mem_filter, mem_univ, true_and] at hS
  simp only [mem_filter, mem_powerset, subset_univ, true_and]
  intro p hp
  rw [← hS.2] at hp
  simp only [comp, mem_filter] at hp
  obtain ⟨_, q, hq, hqC, hqp⟩ := hp
  refine ⟨q, hq, ?_, ?_⟩
  · simp only [T, mem_filter, mem_univ, true_and]; exact hqC
  · exact hqp

/-- **Unconditional strong-coupling area law** (only the minimal spanning area `A` is assumed):
`⟨W_C⟩ = N_C/N_∅ ≤ 2^|T| (2^Δ t)^A / (1 - 2^Δ t)` for `0 ≤ t` and `2^Δ t < 1`. -/
theorem area_law_unconditional (inc : P → Finset E) (C : Finset E) (Δ : ℕ)
    (hΔ : ∀ p, ((univ : Finset P).filter (fun q => (inc p ∩ inc q).Nonempty)).card ≤ Δ)
    {t : ℝ} {A : ℕ} (ht : 0 ≤ t) (hKt : (2 : ℝ) ^ Δ * t < 1) (hA : ∀ S ∈ span inc C, A ≤ S.card) :
    N inc C t / N inc ∅ t ≤
      2 ^ ((univ : Finset P).filter (fun p => (inc p ∩ C).Nonempty)).card * ((2 : ℝ) ^ Δ * t) ^ A /
        (1 - (2 : ℝ) ^ Δ * t) :=
  area_law inc C ht (by positivity) (by positivity) hKt hA (span_count inc C Δ hΔ)

end UnifiedTheory.Clay.YangMills.Twisted.Z2AnimalCount
