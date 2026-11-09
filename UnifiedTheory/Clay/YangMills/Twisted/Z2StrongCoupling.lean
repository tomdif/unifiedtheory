/- Strong-coupling area law for Z₂ lattice gauge theory, on an arbitrary finite plaquette–edge complex.

Spins `s : E → Bool` with `sg s e = ±1`, plaquette variable `σ_p = ∏_{e ∈ inc p} sg s e`, and Boltzmann weight
`∏_p (1 + t σ_p)` (this is `e^{β σ_p}/cosh β` with `t = tanh β`). The Wilson loop is `W_C = ∏_{e ∈ C} sg s e`.

* `ht_expansion` (high-temperature expansion, exact): `Σ_s W_C ∏_p (1 + t σ_p) = 2^|E| · N_C(t)`, where
  `N_C(t) = Σ_{X ⊆ P, ∂X = C} t^|X|` and `∂X` is the set of edges in an odd number of plaquettes of `X`.
  So `⟨W_C⟩ = N_C/N_∅` (`wilson_eq`).
* `comp` and `bd_comp`: for `∂X = C`, the plaquettes of `X` connected (by shared edges, within `X`) to a plaquette
  touching `C` form `S` with `∂S = C`, and the rest `X \ S` is closed. `comp_idem`: `S` is its own component.
* `peierls`: `N_C ≤ (Σ_{S ∈ 𝒮_C} t^|S|) · N_∅`, where `𝒮_C` is the set of `C`-connected spanning sets. Hence
  `⟨W_C⟩ ≤ Σ_{S ∈ 𝒮_C} t^|S|` (`wilson_le`).
* `area_law`: if every `S ∈ 𝒮_C` has `|S| ≥ A` (the minimal spanning area) and there are at most `M K^n` sets of size
  `n` (the lattice-animal count, kept as a HYPOTHESIS here), then for `0 ≤ t` and `K t < 1`,
  `⟨W_C⟩ ≤ M (K t)^A / (1 - K t)`: an area law at strong coupling (`t = tanh β` small).

Scope: Z₂, not SU(2). The SU(2) strong-coupling area law (Osterwalder–Seiler) needs the non-abelian character expansion
and a cluster expansion; this file is the abelian template of that argument. -/
import Mathlib
import UnifiedTheory.Clay.YangMills.Twisted.TwistedSubArea

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Classical

namespace UnifiedTheory.Clay.YangMills.Twisted.Z2StrongCoupling

variable {P E : Type*} [Fintype P] [Fintype E] [DecidableEq P] [DecidableEq E]

/-- `±1` value of a spin. -/
def sg (b : Bool) : ℝ := if b then -1 else 1

/-- Number of plaquettes of `X` containing `e`. -/
noncomputable def cnt (inc : P → Finset E) (X : Finset P) (e : E) : ℕ := (X.filter (fun p => e ∈ inc p)).card

/-- Boundary of a plaquette set: edges in an odd number of its plaquettes. -/
noncomputable def bd (inc : P → Finset E) (X : Finset P) : Finset E := univ.filter (fun e => Odd (cnt inc X e))

/-- `N_C(t) = Σ_{∂X = C} t^|X|`. -/
noncomputable def N (inc : P → Finset E) (C : Finset E) (t : ℝ) : ℝ :=
  ∑ X ∈ (univ : Finset (Finset P)).filter (fun X => bd inc X = C), t ^ X.card

theorem sg_pow_sum (m : ℕ) : ∑ b : Bool, sg b ^ m = if Even m then 2 else 0 := by
  simp only [Fintype.sum_bool, sg, if_true]
  rcases Nat.even_or_odd m with h | h
  · rw [h.neg_one_pow, if_pos h]; norm_num
  · rw [h.neg_one_pow, if_neg (Nat.not_even_iff_odd.mpr h)]; norm_num

theorem prod_inc (inc : P → Finset E) (X : Finset P) (f : E → ℝ) :
    ∏ p ∈ X, ∏ e ∈ inc p, f e = ∏ e, f e ^ cnt inc X e := by
  have h1 : ∀ p, ∏ e ∈ inc p, f e = ∏ e, (if e ∈ inc p then f e else 1) := by
    intro p; rw [Finset.prod_ite_mem]; simp
  simp_rw [h1]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl; intro e _
  rw [← Finset.prod_filter, Finset.prod_const]; rfl

theorem prod_C (C : Finset E) (f : E → ℝ) : ∏ e ∈ C, f e = ∏ e, f e ^ (if e ∈ C then 1 else 0) := by
  have : ∀ e, f e ^ (if e ∈ C then 1 else 0) = if e ∈ C then f e else 1 := by
    intro e; split_ifs <;> simp
  simp_rw [this]; rw [Finset.prod_ite_mem univ C, Finset.univ_inter]

theorem even_iff_bd (inc : P → Finset E) (C : Finset E) (X : Finset P) :
    (∀ e, Even ((if e ∈ C then 1 else 0) + cnt inc X e)) ↔ bd inc X = C := by
  constructor
  · intro h; ext e; simp only [bd, mem_filter, mem_univ, true_and]
    have := h e; split_ifs at this with hc
    · simp only [hc, iff_true]; rw [Nat.even_iff] at this; rw [Nat.odd_iff]; omega
    · simp only [hc, iff_false, zero_add] at this ⊢; rw [Nat.even_iff] at this; rw [Nat.odd_iff]; omega
  · intro h e; rw [← h]; simp only [bd, mem_filter, mem_univ, true_and]
    split_ifs with hc
    · rw [Nat.odd_iff] at hc; rw [Nat.even_iff]; omega
    · rw [Nat.odd_iff] at hc; rw [Nat.even_iff]; omega

theorem ht_expansion (inc : P → Finset E) (C : Finset E) (t : ℝ) :
    ∑ s : E → Bool, (∏ e ∈ C, sg (s e)) * ∏ p, (1 + t * ∏ e ∈ inc p, sg (s e)) =
      2 ^ Fintype.card E * N inc C t := by
  have hexp : ∀ s : E → Bool, ∏ p, (1 + t * ∏ e ∈ inc p, sg (s e)) =
      ∑ X ∈ (univ : Finset P).powerset, t ^ X.card * ∏ e, sg (s e) ^ cnt inc X e := by
    intro s
    have := Finset.prod_add (fun p => t * ∏ e ∈ inc p, sg (s e)) (fun _ => (1 : ℝ)) (univ : Finset P)
    simp only [Finset.prod_const_one, mul_one] at this
    rw [show (fun p => 1 + t * ∏ e ∈ inc p, sg (s e)) = (fun p => t * ∏ e ∈ inc p, sg (s e) + 1) from
      funext fun p => add_comm _ _, this]
    apply Finset.sum_congr rfl; intro X _
    rw [Finset.prod_mul_distrib, Finset.prod_const, prod_inc]
  simp_rw [hexp, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Finset.powerset_univ]
  rw [N, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro X _
  have hs : ∀ s : E → Bool, (∏ e ∈ C, sg (s e)) * (t ^ X.card * ∏ e, sg (s e) ^ cnt inc X e) =
      t ^ X.card * ∏ e, sg (s e) ^ ((if e ∈ C then 1 else 0) + cnt inc X e) := by
    intro s; rw [prod_C]; simp_rw [pow_add]; rw [Finset.prod_mul_distrib]; ring
  simp_rw [hs, ← Finset.mul_sum]
  rw [← Fintype.prod_sum (fun e b => sg b ^ ((if e ∈ C then 1 else 0) + cnt inc X e))]
  simp_rw [sg_pow_sum]
  rw [Finset.prod_ite_zero]
  simp only [Finset.mem_univ, true_implies, Finset.prod_const, Finset.card_univ]
  by_cases h : ∀ e, Even ((if e ∈ C then 1 else 0) + cnt inc X e)
  · rw [if_pos h, if_pos ((even_iff_bd inc C X).mp h)]; ring
  · rw [if_neg h, if_neg (fun h' => h ((even_iff_bd inc C X).mpr h'))]; ring

/-- The Gibbs expectation of the Wilson loop is `N_C / N_∅`. -/
theorem wilson_eq (inc : P → Finset E) (C : Finset E) (t : ℝ) :
    (∑ s : E → Bool, (∏ e ∈ C, sg (s e)) * ∏ p, (1 + t * ∏ e ∈ inc p, sg (s e))) /
      (∑ s : E → Bool, ∏ p, (1 + t * ∏ e ∈ inc p, sg (s e))) = N inc C t / N inc ∅ t := by
  have h0 := ht_expansion inc ∅ t
  simp only [Finset.prod_empty, one_mul] at h0
  rw [ht_expansion, h0]
  have : (2 : ℝ) ^ Fintype.card E ≠ 0 := by positivity
  rw [mul_div_mul_left _ _ this]

/-- Two plaquettes of `X` sharing an edge. -/
def adj (inc : P → Finset E) (X : Finset P) (p q : P) : Prop := p ∈ X ∧ q ∈ X ∧ (inc p ∩ inc q).Nonempty

/-- The plaquettes of `X` connected within `X` to a plaquette touching `C`. -/
noncomputable def comp (inc : P → Finset E) (C : Finset E) (X : Finset P) : Finset P :=
  X.filter (fun p => ∃ q ∈ X, (inc q ∩ C).Nonempty ∧ Relation.ReflTransGen (adj inc X) q p)

theorem comp_sub (inc : P → Finset E) (C : Finset E) (X : Finset P) : comp inc C X ⊆ X := Finset.filter_subset _ _

theorem comp_closed (inc : P → Finset E) (C : Finset E) (X : Finset P) {p q : P} {e : E}
    (hp : p ∈ comp inc C X) (hq : q ∈ X) (hep : e ∈ inc p) (heq : e ∈ inc q) : q ∈ comp inc C X := by
  simp only [comp, mem_filter] at hp ⊢
  obtain ⟨hpX, q0, hq0, ht, hr⟩ := hp
  exact ⟨hq, q0, hq0, ht, hr.tail ⟨hpX, hq, ⟨e, Finset.mem_inter.mpr ⟨hep, heq⟩⟩⟩⟩

theorem cnt_comp (inc : P → Finset E) (C : Finset E) (X : Finset P) (e : E) :
    cnt inc (comp inc C X) e = cnt inc X e ∨ cnt inc (comp inc C X) e = 0 := by
  by_cases h : ∃ p ∈ comp inc C X, e ∈ inc p
  · left; obtain ⟨p, hp, he⟩ := h
    unfold cnt; congr 1; ext q; simp only [mem_filter]
    constructor
    · rintro ⟨hq, hqe⟩; exact ⟨comp_sub inc C X hq, hqe⟩
    · rintro ⟨hq, hqe⟩; exact ⟨comp_closed inc C X hp hq he hqe, hqe⟩
  · right; unfold cnt; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p hp hpe; exact h ⟨p, hp, hpe⟩

theorem cnt_sdiff (inc : P → Finset E) (C : Finset E) (X : Finset P) (e : E) :
    cnt inc (X \ comp inc C X) e + cnt inc (comp inc C X) e = cnt inc X e := by
  unfold cnt
  have hd : Disjoint ((X \ comp inc C X).filter (fun p => e ∈ inc p)) ((comp inc C X).filter (fun p => e ∈ inc p)) :=
    Finset.disjoint_filter_filter Finset.sdiff_disjoint
  rw [← Finset.card_union_of_disjoint hd]; congr 1; ext q
  simp only [mem_union, mem_filter, mem_sdiff]
  have := fun h => comp_sub inc C X (a := q) h
  by_cases hq : q ∈ comp inc C X <;> tauto

theorem bd_comp (inc : P → Finset E) (C : Finset E) (X : Finset P) (h : bd inc X = C) :
    bd inc (comp inc C X) = C ∧ bd inc (X \ comp inc C X) = ∅ := by
  have key : ∀ e, (e ∈ C → cnt inc (comp inc C X) e = cnt inc X e) ∧ Odd (cnt inc X e) = (e ∈ C) := by
    intro e
    have hb : e ∈ bd inc X ↔ e ∈ C := by rw [h]
    simp only [bd, mem_filter, mem_univ, true_and] at hb
    refine ⟨fun hc => ?_, propext hb⟩
    have ho := hb.mpr hc
    have hpos : 0 < cnt inc X e := ho.pos
    unfold cnt at hpos; obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    simp only [mem_filter] at hp
    have hpc : p ∈ comp inc C X := by
      simp only [comp, mem_filter]
      exact ⟨hp.1, p, hp.1, ⟨e, Finset.mem_inter.mpr ⟨hp.2, hc⟩⟩, Relation.ReflTransGen.refl⟩
    rcases cnt_comp inc C X e with h1 | h1
    · exact h1
    · exfalso; unfold cnt at h1; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h1
      exact h1 hpc hp.2
  constructor
  · ext e; simp only [bd, mem_filter, mem_univ, true_and]
    by_cases hc : e ∈ C
    · rw [(key e).1 hc, (key e).2]
    · have hev : ¬ Odd (cnt inc X e) := by rw [(key e).2]; exact hc
      simp only [hc, iff_false]
      rcases cnt_comp inc C X e with h1 | h1
      · rw [h1]; exact hev
      · rw [h1]; decide
  · ext e; simp only [bd, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
    have hs := cnt_sdiff inc C X e
    by_cases hc : e ∈ C
    · rw [(key e).1 hc] at hs; have : cnt inc (X \ comp inc C X) e = 0 := by omega
      rw [this]; decide
    · have hev : ¬ Odd (cnt inc X e) := by rw [(key e).2]; exact hc
      rcases cnt_comp inc C X e with h1 | h1
      · rw [h1] at hs; have : cnt inc (X \ comp inc C X) e = 0 := by omega
        rw [this]; decide
      · rw [h1] at hs; rw [add_zero] at hs; rw [hs]; exact hev

theorem comp_idem (inc : P → Finset E) (C : Finset E) (X : Finset P) :
    comp inc C (comp inc C X) = comp inc C X := by
  apply Finset.Subset.antisymm (comp_sub inc C _)
  intro p hp
  have hp' := hp
  simp only [comp, mem_filter] at hp'
  obtain ⟨_, q0, hq0, ht, hr⟩ := hp'
  have hq0c : q0 ∈ comp inc C X := by
    simp only [comp, mem_filter]; exact ⟨hq0, q0, hq0, ht, Relation.ReflTransGen.refl⟩
  have main : ∀ r, Relation.ReflTransGen (adj inc X) q0 r →
      r ∈ comp inc C X ∧ Relation.ReflTransGen (adj inc (comp inc C X)) q0 r := by
    intro r hr'
    induction hr' with
    | refl => exact ⟨hq0c, Relation.ReflTransGen.refl⟩
    | tail _ hab ih =>
      obtain ⟨ha, hb, hne⟩ := hab
      obtain ⟨e, he⟩ := hne
      rw [Finset.mem_inter] at he
      have hbc := comp_closed inc C X ih.1 hb he.1 he.2
      exact ⟨hbc, ih.2.tail ⟨ih.1, hbc, ⟨e, Finset.mem_inter.mpr he⟩⟩⟩
  have := main p hr
  exact Finset.mem_filter.mpr ⟨this.1, q0, hq0c, ht, this.2⟩

/-- `C`-connected spanning sets. -/
noncomputable def span (inc : P → Finset E) (C : Finset E) : Finset (Finset P) :=
  (univ : Finset (Finset P)).filter (fun S => bd inc S = C ∧ comp inc C S = S)

theorem peierls (inc : P → Finset E) (C : Finset E) {t : ℝ} (ht : 0 ≤ t) :
    N inc C t ≤ (∑ S ∈ span inc C, t ^ S.card) * N inc ∅ t := by
  unfold N
  set A := (univ : Finset (Finset P)).filter (fun X => bd inc X = C)
  set Z := (univ : Finset (Finset P)).filter (fun X => bd inc X = ∅)
  let φ : Finset P → Finset P × Finset P := fun X => (comp inc C X, X \ comp inc C X)
  have hinj : Set.InjOn φ A := by
    intro X _ Y _ hXY
    simp only [φ, Prod.mk.injEq] at hXY
    have hX := Finset.union_sdiff_of_subset (comp_sub inc C X)
    have hY := Finset.union_sdiff_of_subset (comp_sub inc C Y)
    rw [hXY.2, hXY.1] at hX
    exact hX.symm.trans hY
  have himg : A.image φ ⊆ span inc C ×ˢ Z := by
    intro x hx
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hx
    simp only [A, mem_filter, mem_univ, true_and] at hX
    have hb := bd_comp inc C X hX
    simp only [φ, Finset.mem_product, span, Z, mem_filter, mem_univ, true_and]
    exact ⟨⟨hb.1, comp_idem inc C X⟩, hb.2⟩
  have hsplit : ∀ X ∈ A, t ^ X.card = (fun x : Finset P × Finset P => t ^ x.1.card * t ^ x.2.card) (φ X) := by
    intro X _
    simp only [φ, ← pow_add]
    rw [add_comm, Finset.card_sdiff_add_card_eq_card (comp_sub inc C X)]
  rw [Finset.sum_congr rfl hsplit, ← Finset.sum_image (f := fun x : Finset P × Finset P => t ^ x.1.card * t ^ x.2.card) hinj]
  calc ∑ x ∈ A.image φ, t ^ x.1.card * t ^ x.2.card
      ≤ ∑ x ∈ span inc C ×ˢ Z, t ^ x.1.card * t ^ x.2.card :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => by positivity)
    _ = (∑ S ∈ span inc C, t ^ S.card) * ∑ Y ∈ Z, t ^ Y.card := by
        rw [Finset.sum_product, Finset.sum_mul_sum]

theorem N_empty_pos (inc : P → Finset E) {t : ℝ} (ht : 0 ≤ t) : 0 < N inc ∅ t := by
  unfold N
  have hmem : (∅ : Finset P) ∈ (univ : Finset (Finset P)).filter (fun X => bd inc X = ∅) := by
    simp only [mem_filter, mem_univ, true_and]; ext e; simp [bd, cnt]
  calc (0 : ℝ) < t ^ (∅ : Finset P).card := by simp
    _ ≤ _ := Finset.single_le_sum (f := fun X : Finset P => t ^ X.card) (fun _ _ => by positivity) hmem

theorem wilson_le (inc : P → Finset E) (C : Finset E) {t : ℝ} (ht : 0 ≤ t) :
    N inc C t / N inc ∅ t ≤ ∑ S ∈ span inc C, t ^ S.card := by
  rw [div_le_iff₀ (N_empty_pos inc ht)]; exact peierls inc C ht

theorem area_law (inc : P → Finset E) (C : Finset E) {t K M : ℝ} {A : ℕ} (ht : 0 ≤ t) (hK : 0 ≤ K)
    (hM : 0 ≤ M) (hKt : K * t < 1) (hA : ∀ S ∈ span inc C, A ≤ S.card)
    (hcount : ∀ n, (((span inc C).filter (fun S => S.card = n)).card : ℝ) ≤ M * K ^ n) :
    N inc C t / N inc ∅ t ≤ M * (K * t) ^ A / (1 - K * t) := by
  refine le_trans (wilson_le inc C ht) ?_
  set r := K * t
  have hr0 : 0 ≤ r := mul_nonneg hK ht
  set Nn := Fintype.card P + 1
  have hmaps : ∀ S ∈ span inc C, S.card ∈ Finset.range Nn := by
    intro S _; simp only [Finset.mem_range, Nn]; exact Nat.lt_succ_of_le (Finset.card_le_univ S)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hterm : ∀ n ∈ Finset.range Nn,
      ∑ S ∈ (span inc C).filter (fun S => S.card = n), t ^ S.card ≤ if A ≤ n then M * r ^ n else 0 := by
    intro n _
    rw [Finset.sum_congr rfl (fun S hS => by rw [(Finset.mem_filter.mp hS).2])]
    rw [Finset.sum_const, nsmul_eq_mul]
    split_ifs with hn
    · calc (((span inc C).filter (fun S => S.card = n)).card : ℝ) * t ^ n ≤ M * K ^ n * t ^ n :=
            mul_le_mul_of_nonneg_right (hcount n) (by positivity)
        _ = M * r ^ n := by rw [mul_pow]; ring
    · have : (span inc C).filter (fun S => S.card = n) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro S hS hc; exact hn (hc ▸ hA S hS)
      rw [this]; simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  by_cases hAN : A ≤ Nn
  · rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le A) hAN]
    have h1 : ∑ n ∈ Finset.Ico 0 A, (if A ≤ n then M * r ^ n else 0) = 0 := by
      apply Finset.sum_eq_zero; intro n hn; rw [Finset.mem_Ico] at hn; rw [if_neg (by omega)]
    rw [h1, zero_add, Finset.sum_Ico_eq_sum_range]
    have h2 : ∀ k ∈ Finset.range (Nn - A), (if A ≤ A + k then M * r ^ (A + k) else 0) = M * r ^ A * r ^ k := by
      intro k _; rw [if_pos (by omega), pow_add]; ring
    rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
    have hg := UnifiedTheory.Clay.YangMills.Twisted.TwistedSubArea.geom_le hr0 hKt (Nn - A)
    calc M * r ^ A * ∑ k ∈ Finset.range (Nn - A), r ^ k ≤ M * r ^ A * (1 / (1 - r)) :=
          mul_le_mul_of_nonneg_left hg (by positivity)
      _ = M * r ^ A / (1 - r) := by ring
  · have h0 : ∑ n ∈ Finset.range Nn, (if A ≤ n then M * r ^ n else 0) = 0 := by
      apply Finset.sum_eq_zero; intro n hn; rw [Finset.mem_range] at hn; rw [if_neg (by omega)]
    rw [h0]; have : 0 < 1 - r := by linarith
    positivity

end UnifiedTheory.Clay.YangMills.Twisted.Z2StrongCoupling
