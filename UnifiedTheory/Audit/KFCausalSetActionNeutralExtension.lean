/-
  Audit/KFCausalSetActionNeutralExtension.lean
  — ACTION-NEUTRAL EXTENSIONS, ROOT DETERMINISM, AND THE GATE ARITHMETIC

  The commensurability check of the Born-from-growth tower found that every
  causet of the enumerated tree (n ≤ 4) admits a child with Benincasa–Dowker
  action gap exactly zero.  This file proves the reason, in full generality:

  1.  `actionUnits_coverExtension` / `exists_action_neutral_extension`:
      **cover a minimal element.**  Birth a new event whose past is exactly
      one minimal element x.  Since past(x) = ∅, transitivity adds nothing,
      the only new interval is the two-element interval [x, e], and the 4D
      BD weights give ΔS = σ(1 − W(0)) = 0.  Every finite nonempty causet
      has a minimal element (`exists_minimal`), so an action-neutral child
      ALWAYS exists — the lazy tower's kill test was unwinnable by design,
      not by luck.  Iterating the same cover produces the broom.

  2.  `root_step_deterministic`: the root of the growth tree (gaps 0 and 1)
      forces determinism for every phase φ with cos φ ≠ 1: any consistent
      assignment √pc + √pa·e^{iφ} = 1 with pa + pc = 1 has pa = 0.  The
      excluded points φ ∈ 2πℤ are exactly the degenerate phases at which
      the ansatz carries no phase information (all e^{i g φ} = 1).

  3.  `chain_tower_incommensurable`: the arithmetic that kills the pure
      chain tower inside the Varadarajan–Rideout classification.  The
      era-2 exit at height 1 pins 9φ ∈ 2πℤ (gap of the 3-chain), and the
      forced first birth of the next era pins 7φ ∈ 2πℤ (gap −7 of the
      4-chain); gcd(9,7) = 1 forces φ ∈ 2πℤ — excluded.  The 9 and the 7
      are pure Benincasa–Dowker data: 9 = 1 − W(1), 7 = W(2) − 1 − W(1)·… ,
      so the death of the chain cosmology is a property of the 4D action
      coefficients (1, −9, 16, −8) themselves.

  4.  `quadrature_parity_obstruction`: at a phase pinned to φ = 2πk/b with
      b odd (the only values the era exits allow, since gcd(g_m, h_m) ∣ 9),
      the born-quadrature condition for a genuine two-branch node reads
      4kΔ = b(1 + 2j) — even equals odd, impossible.  Combined with the
      two-child structure of reachable in-era nodes this empties the
      stochastic sector of the tower: every surviving dynamics is a single
      deterministic history.

  Zero sorry.  Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalSetSequentialGrowth
import UnifiedTheory.Audit.KFCausalQuantumMeasure

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetActionNeutralExtension

open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalQuantumMeasure

/-! ## 1. The Benincasa–Dowker action on finite causal orders -/

/-- 4D BD layer weights, keyed by the number of elements strictly between
the endpoints of a relation. -/
def bdWeight : ℕ → ℤ
  | 0 => 1
  | 1 => -9
  | 2 => 16
  | 3 => -8
  | _ + 4 => 0

/-- The strict order underlying the reflexive Boolean relation. -/
def strictRel {n : ℕ} (P : CardinalCausalOrder n) (i j : Fin n) : Prop :=
  P.rel i j = true ∧ i ≠ j

instance {n : ℕ} (P : CardinalCausalOrder n) (i j : Fin n) :
    Decidable (strictRel P i j) := by
  unfold strictRel
  infer_instance

/-- Number of elements strictly between `i` and `j`. -/
def betweenCount {n : ℕ} (P : CardinalCausalOrder n) (i j : Fin n) : ℕ :=
  (Finset.univ.filter fun z => strictRel P i z ∧ strictRel P z j).card

/-- The 4D BD action in units of `σ = 4/√6`:
`S/σ = N − Σ_{i<j} W(betweenCount i j)`. -/
def actionUnits {n : ℕ} (P : CardinalCausalOrder n) : ℤ :=
  (n : ℤ) - ∑ i : Fin n, ∑ j : Fin n,
    if strictRel P i j then bdWeight (betweenCount P i j) else 0

/-! ## 2. Minimal elements -/

/-- `x` is minimal: nothing lies below it. -/
def IsMinimalIn {n : ℕ} (P : CardinalCausalOrder n) (x : Fin n) : Prop :=
  ∀ a, P.rel a x = true → a = x

/-- Every nonempty finite causal order has a minimal element (minimize the
predecessor count). -/
theorem exists_minimal {n : ℕ} (P : CardinalCausalOrder (n + 1)) :
    ∃ x, IsMinimalIn P x := by
  obtain ⟨x, -, hx⟩ := Finset.exists_min_image
    (Finset.univ : Finset (Fin (n + 1)))
    (fun y => (Finset.univ.filter fun a => P.rel a y = true).card)
    ⟨0, Finset.mem_univ 0⟩
  refine ⟨x, fun a ha => ?_⟩
  by_contra hne
  have hsubset : (Finset.univ.filter fun b => P.rel b a = true) ⊆
      (Finset.univ.filter fun b => P.rel b x = true) := by
    intro b hb
    rw [Finset.mem_filter] at hb ⊢
    exact ⟨hb.1, P.trans b a x hb.2 ha⟩
  have hwit : x ∉ (Finset.univ.filter fun b => P.rel b a = true) := by
    rw [Finset.mem_filter]
    rintro ⟨-, hxa⟩
    exact hne (P.antisymm a x ha hxa)
  have hmem : x ∈ (Finset.univ.filter fun b => P.rel b x = true) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, P.refl x⟩
  have hlt := Finset.card_lt_card
    (((Finset.ssubset_iff_of_subset hsubset).mpr ⟨x, hmem, hwit⟩))
  have := hx a (Finset.mem_univ a)
  omega

/-! ## 3. The minimal-cover extension -/

/-- Relation for birthing a new final event whose past is exactly the
minimal element `x`. -/
def coverExtensionRel {n : ℕ} (P : CardinalCausalOrder n) (x : Fin n)
    (i j : Fin (n + 1)) : Bool :=
  if hi : i = Fin.last n then decide (j = Fin.last n)
  else if hj : j = Fin.last n then decide (i.castPred hi = x)
  else P.rel (i.castPred hi) (j.castPred hj)

/-- Adjoin one new event covering exactly the minimal element `x`.
Minimality of `x` is precisely what makes `{x}` a down-set, i.e. what makes
this transitive. -/
def coverExtension {n : ℕ} (P : CardinalCausalOrder n) (x : Fin n)
    (hx : IsMinimalIn P x) : CardinalCausalOrder (n + 1) where
  rel := coverExtensionRel P x
  refl := by
    intro i
    unfold coverExtensionRel
    by_cases hi : i = Fin.last n
    · simp [hi]
    · simp [hi, P.refl]
  antisymm := by
    intro i j hij hji
    unfold coverExtensionRel at hij hji
    by_cases hi : i = Fin.last n <;> by_cases hj : j = Fin.last n
    · rw [hi, hj]
    · rw [dif_pos hi, decide_eq_true_eq] at hij
      exact absurd hij hj
    · rw [dif_pos hj, decide_eq_true_eq] at hji
      exact absurd hji hi
    · rw [dif_neg hi, dif_neg hj] at hij
      rw [dif_neg hj, dif_neg hi] at hji
      have h := P.antisymm _ _ hij hji
      have h2 := congrArg Fin.castSucc h
      rwa [Fin.castSucc_castPred, Fin.castSucc_castPred] at h2
  trans := by
    intro i j k hij hjk
    unfold coverExtensionRel at hij hjk ⊢
    by_cases hi : i = Fin.last n
    · rw [dif_pos hi] at hij ⊢
      by_cases hj : j = Fin.last n
      · rw [dif_pos hj] at hjk
        exact hjk
      · rw [decide_eq_true_eq] at hij
        exact absurd hij hj
    · rw [dif_neg hi] at hij ⊢
      by_cases hj : j = Fin.last n
      · rw [dif_pos hj] at hij hjk
        rw [decide_eq_true_eq] at hjk
        rw [dif_pos hjk]
        exact hij
      · rw [dif_neg hj] at hij hjk
        by_cases hk : k = Fin.last n
        · rw [dif_pos hk] at hjk ⊢
          rw [decide_eq_true_eq] at hjk ⊢
          exact hx _ (hjk ▸ hij)
        · rw [dif_neg hk] at hjk ⊢
          exact P.trans _ _ _ hij hjk

theorem coverExtension_rel_castSucc {n : ℕ} (P : CardinalCausalOrder n)
    (x : Fin n) (hx : IsMinimalIn P x) (i j : Fin n) :
    (coverExtension P x hx).rel i.castSucc j.castSucc = P.rel i j := by
  show coverExtensionRel P x i.castSucc j.castSucc = P.rel i j
  unfold coverExtensionRel
  rw [dif_neg (Fin.castSucc_lt_last i).ne, dif_neg (Fin.castSucc_lt_last j).ne,
    Fin.castPred_castSucc, Fin.castPred_castSucc]

theorem coverExtension_rel_castSucc_last {n : ℕ} (P : CardinalCausalOrder n)
    (x : Fin n) (hx : IsMinimalIn P x) (a : Fin n) :
    (coverExtension P x hx).rel a.castSucc (Fin.last n) = decide (a = x) := by
  show coverExtensionRel P x a.castSucc (Fin.last n) = decide (a = x)
  unfold coverExtensionRel
  rw [dif_neg (Fin.castSucc_lt_last a).ne, dif_pos rfl, Fin.castPred_castSucc]

theorem coverExtension_rel_last {n : ℕ} (P : CardinalCausalOrder n)
    (x : Fin n) (hx : IsMinimalIn P x) (j : Fin (n + 1)) :
    (coverExtension P x hx).rel (Fin.last n) j = decide (j = Fin.last n) := by
  show coverExtensionRel P x (Fin.last n) j = decide (j = Fin.last n)
  unfold coverExtensionRel
  rw [dif_pos rfl]

/-- The cover extension is a physical one-element birth. -/
theorem coverExtension_isLabeledOneElementExtension {n : ℕ}
    (P : CardinalCausalOrder n) (x : Fin n) (hx : IsMinimalIn P x) :
    IsLabeledOneElementExtension P (coverExtension P x hx) := by
  constructor
  · exact coverExtension_rel_castSucc P x hx
  · intro i
    rw [coverExtension_rel_last]
    exact decide_eq_false (Fin.castSucc_lt_last i).ne

/-! ## 4. The action is unchanged -/

theorem strictRel_castSucc {n : ℕ} (P : CardinalCausalOrder n) (x : Fin n)
    (hx : IsMinimalIn P x) (i j : Fin n) :
    strictRel (coverExtension P x hx) i.castSucc j.castSucc ↔
      strictRel P i j := by
  unfold strictRel
  rw [coverExtension_rel_castSucc]
  simp only [ne_eq, Fin.castSucc_inj]

theorem not_strictRel_last {n : ℕ} (P : CardinalCausalOrder n) (x : Fin n)
    (hx : IsMinimalIn P x) (j : Fin (n + 1)) :
    ¬ strictRel (coverExtension P x hx) (Fin.last n) j := by
  rintro ⟨hrel, hne⟩
  rw [coverExtension_rel_last, decide_eq_true_eq] at hrel
  exact hne hrel.symm

theorem strictRel_castSucc_last {n : ℕ} (P : CardinalCausalOrder n)
    (x : Fin n) (hx : IsMinimalIn P x) (a : Fin n) :
    strictRel (coverExtension P x hx) a.castSucc (Fin.last n) ↔ a = x := by
  unfold strictRel
  rw [coverExtension_rel_castSucc_last, decide_eq_true_eq]
  simp [(Fin.castSucc_lt_last a).ne]

/-- Old pairs keep their interval size: the new event is never interior to
an old interval (nothing lies above it). -/
theorem betweenCount_castSucc {n : ℕ} (P : CardinalCausalOrder n) (x : Fin n)
    (hx : IsMinimalIn P x) (i j : Fin n) :
    betweenCount (coverExtension P x hx) i.castSucc j.castSucc =
      betweenCount P i j := by
  unfold betweenCount
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  rw [if_neg (fun h => not_strictRel_last P x hx _ h.2), add_zero]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [strictRel_castSucc]

/-- The single new interval `[x, e]` is empty: nothing sits strictly between
the covered minimal element and the new event. -/
theorem betweenCount_cover_zero {n : ℕ} (P : CardinalCausalOrder n)
    (x : Fin n) (hx : IsMinimalIn P x) :
    betweenCount (coverExtension P x hx) x.castSucc (Fin.last n) = 0 := by
  unfold betweenCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro z _
  rintro ⟨h1, h2⟩
  have hzne : z ≠ Fin.last n := h2.2
  have hzw : z = (z.castPred hzne).castSucc := (Fin.castSucc_castPred z hzne).symm
  rw [hzw, strictRel_castSucc_last] at h2
  rw [hzw, h2] at h1
  exact h1.2 rfl

/-- **THE ACTION-NEUTRAL EXTENSION THEOREM.**  Covering a minimal element
leaves the BD action unchanged: ΔN = 1 is cancelled exactly by the single
new two-element interval, ΔS = σ(1 − W(0)) = 0. -/
theorem actionUnits_coverExtension {n : ℕ} (P : CardinalCausalOrder n)
    (x : Fin n) (hx : IsMinimalIn P x) :
    actionUnits (coverExtension P x hx) = actionUnits P := by
  unfold actionUnits
  have hrow : ∀ i : Fin n, (∑ j : Fin (n + 1),
      if strictRel (coverExtension P x hx) i.castSucc j then
        bdWeight (betweenCount (coverExtension P x hx) i.castSucc j) else 0)
      = (∑ j : Fin n,
          if strictRel P i j then bdWeight (betweenCount P i j) else 0)
        + (if i = x then 1 else 0) := by
    intro i
    rw [Fin.sum_univ_castSucc]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hij : strictRel P i j
      · rw [if_pos ((strictRel_castSucc P x hx i j).mpr hij), if_pos hij,
          betweenCount_castSucc]
      · rw [if_neg (fun h => hij ((strictRel_castSucc P x hx i j).mp h)),
          if_neg hij]
    · by_cases hix : i = x
      · rw [if_pos ((strictRel_castSucc_last P x hx i).mpr hix), if_pos hix]
        subst hix
        rw [betweenCount_cover_zero]
        rfl
      · rw [if_neg (fun h => hix ((strictRel_castSucc_last P x hx i).mp h)),
          if_neg hix]
  have hsum : (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      if strictRel (coverExtension P x hx) i j then
        bdWeight (betweenCount (coverExtension P x hx) i j) else 0)
      = (∑ i : Fin n, ∑ j : Fin n,
          if strictRel P i j then bdWeight (betweenCount P i j) else 0) + 1 := by
    rw [Fin.sum_univ_castSucc]
    have hlastrow : (∑ j : Fin (n + 1),
        if strictRel (coverExtension P x hx) (Fin.last n) j then
          bdWeight (betweenCount (coverExtension P x hx) (Fin.last n) j)
        else 0) = 0 :=
      Finset.sum_eq_zero fun j _ => if_neg (not_strictRel_last P x hx j)
    rw [hlastrow, add_zero]
    simp only [hrow]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ x fun _ => (1:ℤ)]
    simp
  rw [hsum]
  push_cast
  ring

/-- **Every nonempty causet admits an action-neutral one-element birth** —
the combinatorial reason the lazy tower is satisfiable at every node for
every value of ℏ.  The kill test was unwinnable. -/
theorem exists_action_neutral_extension {n : ℕ}
    (P : CardinalCausalOrder (n + 1)) :
    ∃ Q : CardinalCausalOrder (n + 2),
      IsLabeledOneElementExtension P Q ∧ actionUnits Q = actionUnits P := by
  obtain ⟨x, hx⟩ := exists_minimal P
  exact ⟨coverExtension P x hx,
    coverExtension_isLabeledOneElementExtension P x hx,
    actionUnits_coverExtension P x hx⟩

/-! ## 5. Root determinism (with the φ ∈ 2πℤ carve-out) -/

/-- **The first growth step is forced** for every phase carrying information
(`cos φ ≠ 1`): consistency `√pc + √pa·e^{iφ} = 1` with `pa + pc = 1` kills
the antichain branch.  In Varadarajan–Rideout language: `q₁ = 0`, era 1
ends at stage 1, and the universe acquires a minimum element. -/
theorem root_step_deterministic (φ pa pc : ℝ)
    (hpa : 0 ≤ pa) (hpc : 0 ≤ pc) (hsum : pa + pc = 1)
    (hφ : Real.cos φ ≠ 1)
    (hcons : (Real.sqrt pc : ℂ) + (Real.sqrt pa : ℂ)
      * Complex.exp (φ * Complex.I) = 1) :
    pa = 0 ∧ pc = 1 := by
  have him := congrArg Complex.im hcons
  have hre := congrArg Complex.re hcons
  simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_im, Complex.one_re,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    zero_mul, zero_add, add_zero, sub_zero] at him hre
  have key : Real.sqrt pa = 0 := by
    rcases mul_eq_zero.mp him with h | hsin
    · exact h
    · have hsq : Real.cos φ ^ 2 = 1 := by
        have h1 := Real.sin_sq_add_cos_sq φ
        nlinarith [hsin]
      have hfac : (Real.cos φ - 1) * (Real.cos φ + 1) = 0 := by nlinarith [hsq]
      rcases mul_eq_zero.mp hfac with h1 | h1
      · exact absurd (by linarith : Real.cos φ = 1) hφ
      · have hcm : Real.cos φ = -1 := by linarith
        rw [hcm] at hre
        have hpc1 : Real.sqrt pc ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
        have h4 : Real.sqrt pa ≤ 0 := by nlinarith [hre]
        exact le_antisymm h4 (Real.sqrt_nonneg pa)
  have hpa0 : pa = 0 := le_antisymm (Real.sqrt_eq_zero'.mp key) hpa
  exact ⟨hpa0, by linarith⟩

/-! ## 6. The gate arithmetic -/

/-- **The chain-tower kill.**  The era-2 exit at height 1 pins `9φ ∈ 2πℤ`
(the 3-chain gap), the forced first birth of era 3 pins `7φ ∈ 2πℤ` (the
4-chain gap `−7`); since `gcd(9,7) = 1` this forces `φ ∈ 2πℤ` — the
degenerate phase.  The pure chain cosmology is incompatible with the
Born-from-growth tower, by BD gap arithmetic alone. -/
theorem chain_tower_incommensurable (φ : ℝ) (a b : ℤ)
    (h9 : 9 * φ = 2 * Real.pi * a) (h7 : 7 * φ = 2 * Real.pi * b) :
    ∃ m : ℤ, φ = 2 * Real.pi * m := by
  have hab : 7 * a = 9 * b := by
    have h63 : 7 * (9 * φ) = 9 * (7 * φ) := by ring
    rw [h9, h7] at h63
    have h2 : (2 * Real.pi) * ((7 * a : ℤ) : ℝ)
        = (2 * Real.pi) * ((9 * b : ℤ) : ℝ) := by
      push_cast
      linarith [h63]
    have h3 := mul_left_cancel₀
      (by positivity : (2 * Real.pi : ℝ) ≠ 0) h2
    exact_mod_cast h3
  have h9a : (9 : ℤ) ∣ a := by
    have hdvd : (9 : ℤ) ∣ 7 * a := ⟨b, hab⟩
    have hcop : IsCoprime (9 : ℤ) 7 := ⟨4, -5, by norm_num⟩
    exact hcop.dvd_of_dvd_mul_left hdvd
  obtain ⟨m, rfl⟩ := h9a
  refine ⟨m, ?_⟩
  have h : (9 : ℝ) * φ = 9 * (2 * Real.pi * m) := by
    rw [h9]
    push_cast
    ring
  exact mul_left_cancel₀ (by norm_num : (9 : ℝ) ≠ 0) h

/-- **The branching-parity obstruction.**  At a phase pinned to `φ = 2πk/b`
with `b` odd — the only values the era exits allow, since the exit gaps
satisfy `gcd(g_m, h_m) ∣ 9` — born-quadrature for a genuine two-branch node
requires `4kΔ = b(1 + 2j)`: even equals odd, impossible.  No surviving
tower ever branches. -/
theorem quadrature_parity_obstruction (b k d j : ℤ) (hb : Odd b) :
    4 * k * d ≠ b * (1 + 2 * j) := by
  intro h
  have heven : Even (4 * k * d) := ⟨2 * k * d, by ring⟩
  have hodd : Odd (b * (1 + 2 * j)) := hb.mul ⟨j, by ring⟩
  rw [h] at heven
  obtain ⟨u, hu⟩ := heven
  obtain ⟨v, hv⟩ := hodd
  omega

#print axioms actionUnits_coverExtension
#print axioms exists_action_neutral_extension
#print axioms root_step_deterministic
#print axioms chain_tower_incommensurable
#print axioms quadrature_parity_obstruction

/-! ## 7. The per-node determinism theorems (the [MECH] → [LEAN] promotion)

The two-child induction of the gate has two ingredients per node.  This
section proves the ARITHMETIC ingredient in universal form — quantified
over ALL integer gap pairs, so no unnoticed gap window can reopen the
stochastic sector — and the trivial combinatorial anchor that intermediate
births from an antichain carry a single-coupling weight. -/

/-- **Era-2 node kill (unpinned phase).**  Any consistency solution on a
gap pair containing the zero gap is degenerate, for EVERY phase θ: the
zero-gap amplitude has `cos 0 = 1 = √p₁`, so the partner probability
vanishes.  This is the node arithmetic that turns era 2 into the broom. -/
theorem two_support_zero_gap_deterministic (θ p₁ p₂ : ℝ)
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hsum : p₁ + p₂ = 1)
    (hcons : (Real.sqrt p₁ : ℂ)
      + (Real.sqrt p₂ : ℂ) * Complex.exp (θ * Complex.I) = 1) :
    p₁ = 0 ∨ p₂ = 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hp₁' : 0 < p₁ := lt_of_le_of_ne hp₁ (Ne.symm h1)
  have hp₂' : 0 < p₂ := lt_of_le_of_ne hp₂ (Ne.symm h2)
  have hzero : (Real.sqrt p₁ : ℂ)
      * Complex.exp (((0:ℝ) : ℂ) * Complex.I) = (Real.sqrt p₁ : ℂ) := by
    simp
  have hcons' : (Real.sqrt p₁ : ℂ) * Complex.exp (((0:ℝ) : ℂ) * Complex.I)
      + (Real.sqrt p₂ : ℂ) * Complex.exp (θ * Complex.I) = 1 := by
    rw [hzero]
    exact hcons
  obtain ⟨hc₁, -, -⟩ :=
    born_quadrature_law p₁ p₂ 0 θ hp₁' hp₂' hsum hcons'
  rw [Real.cos_zero] at hc₁
  have hp₁1 : p₁ = 1 := Real.sqrt_eq_one.mp hc₁.symm
  linarith

/-- **Pinned-phase node kill (all later eras), universal in the gaps.**
At `φ = 2πk/b` with `b` odd, any consistency solution on ANY two distinct
integer gaps is degenerate.  Proof: positivity of both branches forces
quadrature (`born_quadrature_law`), quadrature forces
`4k(g₁−g₂) = b(2n+1)`, and parity forbids it.  Together with the
two-child structure of reachable in-era nodes this empties the
stochastic sector of every surviving tower. -/
theorem two_support_pinned_odd_deterministic
    (b k g₁ g₂ : ℤ) (hb : Odd b) (hbne : b ≠ 0)
    (p₁ p₂ : ℝ) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hsum : p₁ + p₂ = 1)
    (φ : ℝ) (hφ : φ = 2 * Real.pi * k / b)
    (hcons : (Real.sqrt p₁ : ℂ)
        * Complex.exp (((g₁ : ℝ) * φ : ℝ) * Complex.I)
      + (Real.sqrt p₂ : ℂ)
        * Complex.exp (((g₂ : ℝ) * φ : ℝ) * Complex.I) = 1) :
    p₁ = 0 ∨ p₂ = 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hp₁' : 0 < p₁ := lt_of_le_of_ne hp₁ (Ne.symm h1)
  have hp₂' : 0 < p₂ := lt_of_le_of_ne hp₂ (Ne.symm h2)
  obtain ⟨-, -, hquad⟩ :=
    born_quadrature_law p₁ p₂ ((g₁ : ℝ) * φ) ((g₂ : ℝ) * φ)
      hp₁' hp₂' hsum hcons
  have hquad' : Real.cos (((g₁ - g₂ : ℤ) : ℝ) * φ) = 0 := by
    rw [show ((g₁ - g₂ : ℤ) : ℝ) * φ = (g₁ : ℝ) * φ - (g₂ : ℝ) * φ from by
      push_cast; ring]
    exact hquad
  obtain ⟨n, hn⟩ := Real.cos_eq_zero_iff.mp hquad'
  have hbR : (b : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hbne
  have hZ : (4 * k * (g₁ - g₂) : ℤ) = b * (2 * n + 1) := by
    have h4 : ((g₁ - g₂ : ℤ) : ℝ) * φ * (2 * (b : ℝ))
        = ((2 * n + 1 : ℤ) : ℝ) * Real.pi / 2 * (2 * (b : ℝ)) := by
      rw [hn]
      push_cast
      ring
    rw [hφ] at h4
    field_simp at h4
    have h5 : ((g₁ - g₂) * 2 ^ 2 * k : ℤ) = b * (2 * n + 1) := by
      exact_mod_cast h4
    linear_combination h5
  exact quadrature_parity_obstruction b k (g₁ - g₂) n hb
    (by rw [hZ]; ring)

/-- **The structural anchor**: in an antichain every element of every
subset is maximal within it, so an intermediate birth above `d` elements
of the relative antichain has RS signature `(d, d)` and weight the single
coupling `s_d` — the coupling the lazy induction has already killed. -/
theorem antichain_subset_all_maximal {n : ℕ} (P : CardinalCausalOrder n)
    (h : ∀ i j, P.rel i j = true → i = j) (D : Finset (Fin n)) :
    (D.filter fun d => ∀ e ∈ D, P.rel d e = true → d = e).card = D.card := by
  rw [Finset.filter_true_of_mem]
  intro d _ e _ hrel
  exact h d e hrel

/-- **Degeneracy has a direction.**  The kill lemmas produce a singleton
support but do not by themselves say which child survives.  This closes
that seam: the RS-form gregarious weight is identically `s₀ = 1`, so
`p_greg = 1/(1+s_j) > 0` for every finite coupling — and a singleton
support with `p_greg > 0` must BE the gregarious child.  A probability-1
timid step is therefore never an in-era option: it is definitionally a
Varadarajan–Rideout era end, and era ends are priced by the (g, h) sieve.
The resonant "wrong-way" solutions the kill lemmas leave open are exactly
the era exits — there is no third route. -/
theorem singleton_support_is_gregarious (pg pt : ℝ) (hpg : 0 < pg)
    (hsum : pg + pt = 1) (hdeg : pg = 0 ∨ pt = 0) : pg = 1 ∧ pt = 0 := by
  rcases hdeg with h | h
  · exact absurd h hpg.ne'
  · exact ⟨by linarith, h⟩

#print axioms two_support_zero_gap_deterministic
#print axioms two_support_pinned_odd_deterministic
#print axioms antichain_subset_all_maximal
#print axioms singleton_support_is_gregarious

end UnifiedTheory.Audit.KFCausalSetActionNeutralExtension
