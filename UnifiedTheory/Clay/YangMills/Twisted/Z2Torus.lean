/- The Z₂ strong-coupling area law on a CONCRETE 4D periodic lattice `(ℤ/L)⁴`, fully unconditional.

* `stokes` (abstract discrete Stokes, any complex): for `η : E → ZMod 2`,
  `Σ_{p ∈ S} Σ_{e ∈ inc p} η e = Σ_{e ∈ ∂S} η e`.
* The torus complex: sites `Fin 4 → ZMod L`, edges `(site, direction)`, plaquettes `(site, μ < ν)` with edges
  `(x,μ), (x+e_μ,ν), (x+e_ν,μ), (x,ν)` (`tinc`).
* `loopC L R T`: the `R × T` rectangle in the `(0,1)` plane at the origin (`mem_loopC` lists its edges explicitly).
* `min_area`: if `∂S = C` then `T · min R (L-R) ≤ |S|`; `min_area_half`: `R T ≤ |S|` when `2R ≤ L`.
  Proof: for the column cochain `η_{k,b}` (direction-1 edges at `x₀ = k`, `x₁ = b`), `δη` is the indicator of the
  `(0,1)` plaquettes at `x₁ = b`, `x₀ ∈ {k-1, k}` (`cob`); Stokes gives `o(k-1) + o(k) = [k = 0 ∨ k = R]` for the
  parities `o(a) = |S ∩ col(a,b)| mod 2`, so either all columns `a < R` or all columns `R ≤ a < L` of row `b` are
  occupied by `S`.
* `nbr_card_le`: every plaquette shares an edge with at most `24` plaquettes (itself included).
* `area_law_torus`, `wilson_area_law_torus`: `⟨W_C⟩ ≤ 2^|T_C| (2^24 t)^{RT} / (1 - 2^24 t)`.
-/
import Mathlib
import UnifiedTheory.Clay.YangMills.Twisted.Z2AnimalCount

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

open Finset Classical

namespace UnifiedTheory.Clay.YangMills.Twisted.Z2Torus

open UnifiedTheory.Clay.YangMills.Twisted.Z2StrongCoupling UnifiedTheory.Clay.YangMills.Twisted.Z2AnimalCount

section Stokes

variable {P E : Type*} [Fintype P] [Fintype E] [DecidableEq P] [DecidableEq E]

theorem cnt_cast (inc : P → Finset E) (S : Finset P) (e : E) :
    ((cnt inc S e : ℕ) : ZMod 2) = if e ∈ bd inc S then 1 else 0 := by
  simp only [bd, mem_filter, mem_univ, true_and]
  split_ifs with h
  · exact ZMod.natCast_eq_one_iff_odd.mpr h
  · exact ZMod.natCast_eq_zero_iff_even.mpr (Nat.not_odd_iff_even.mp h)

/-- **Discrete Stokes** (mod 2): `Σ_{p ∈ S} (δη)(p) = Σ_{e ∈ ∂S} η(e)`. -/
theorem stokes (inc : P → Finset E) (S : Finset P) (η : E → ZMod 2) :
    ∑ p ∈ S, ∑ e ∈ inc p, η e = ∑ e ∈ bd inc S, η e := by
  have h1 : ∀ p, ∑ e ∈ inc p, η e = ∑ e, if e ∈ inc p then η e else 0 := fun p => by simp
  calc ∑ p ∈ S, ∑ e ∈ inc p, η e = ∑ e, ∑ p ∈ S, (if e ∈ inc p then η e else 0) := by
        simp_rw [h1]; exact Finset.sum_comm
    _ = ∑ e, (if e ∈ bd inc S then η e else 0) := by
        apply Finset.sum_congr rfl; intro e _
        rw [← Finset.sum_filter, sum_const, nsmul_eq_mul]
        change ((cnt inc S e : ℕ) : ZMod 2) * η e = _
        rw [cnt_cast]; split_ifs <;> simp
    _ = _ := by simp

end Stokes

section Torus

variable (L : ℕ) [NeZero L]

abbrev Site := Fin 4 → ZMod L
abbrev Ori := {q : Fin 4 × Fin 4 // q.1 < q.2}
abbrev Edge := Site L × Fin 4
abbrev Plaq := Site L × Ori

/-- Unit vector `e_μ`. -/
def unit (μ : Fin 4) : Site L := Pi.single μ 1

/-- Edges of the plaquette `(x, μ<ν)`: `(x,μ), (x+e_μ,ν), (x+e_ν,μ), (x,ν)`. -/
def tinc (p : Plaq L) : Finset (Edge L) :=
  {(p.1, p.2.1.1), (p.1 + unit L p.2.1.1, p.2.1.2), (p.1 + unit L p.2.1.2, p.2.1.1), (p.1, p.2.1.2)}

/-- The `R × T` rectangular loop in the `(0,1)` plane with corner at the origin. -/
def loopC (R T : ℕ) : Finset (Edge L) := univ.filter (fun e =>
  (e.2 = 0 ∧ e.1 2 = 0 ∧ e.1 3 = 0 ∧ (e.1 1 = 0 ∨ e.1 1 = (T : ZMod L)) ∧ (e.1 0).val < R) ∨
  (e.2 = 1 ∧ e.1 2 = 0 ∧ e.1 3 = 0 ∧ (e.1 0 = 0 ∨ e.1 0 = (R : ZMod L)) ∧ (e.1 1).val < T))

/-- The `(0,1)` orientation. -/
def q01 : Ori := ⟨(0, 1), by decide⟩

/-- Column `(a, b)`: the `(0,1)` plaquettes with `x₀ = a`, `x₁ = b` (any `x₂, x₃`). -/
instance : Nonempty (Plaq L) := ⟨(0, q01)⟩
instance : Nonempty (Edge L) := ⟨(0, 0)⟩

def col (a b : ZMod L) : Finset (Plaq L) := univ.filter (fun p => p.2 = q01 ∧ p.1 1 = b ∧ p.1 0 = a)

/-- Column cochain: indicator of direction-1 edges with `x₀ = k`, `x₁ = b`. -/
def eta (k b : ZMod L) (e : Edge L) : ZMod 2 := if e.2 = 1 ∧ e.1 1 = b ∧ e.1 0 = k then 1 else 0

theorem unit_ne_zero (hL : 2 ≤ L) (μ : Fin 4) : unit L μ ≠ 0 := by
  haveI : Fact (1 < L) := ⟨by omega⟩
  intro h
  have := congrFun h μ
  simp [unit] at this

theorem add_unit_ne (hL : 2 ≤ L) (x : Site L) (μ : Fin 4) : x + unit L μ ≠ x := by
  intro h; apply unit_ne_zero L hL μ
  have : x + unit L μ = x + 0 := by rw [h, add_zero]
  exact add_left_cancel this

/-- Coboundary of the column cochain. -/
theorem cob (hL : 2 ≤ L) (k b : ZMod L) (p : Plaq L) :
    ∑ e ∈ tinc L p, eta L k b e =
      (if p ∈ col L (k - 1) b then 1 else 0) + (if p ∈ col L k b then 1 else 0) := by
  obtain ⟨x, ⟨⟨μ, ν⟩, hμν⟩⟩ := p
  simp only at hμν
  have hne : μ ≠ ν := ne_of_lt hμν
  have h1 := add_unit_ne L hL x μ
  have h2 := add_unit_ne L hL x ν
  simp only [tinc]
  rw [sum_insert (by simp [hne, h2.symm]), sum_insert (by simp [hne.symm, h1]),
    sum_insert (by simp [hne, h2]), sum_singleton]
  fin_cases μ <;> fin_cases ν <;> simp at hμν <;>
    simp [eta, col, q01, unit, eq_sub_iff_add_eq] <;> split_ifs <;> simp_all <;> decide

theorem val_cast_lt {a : ℕ} (ha : a < L) : ((a : ZMod L)).val = a := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt ha]

theorem cast_inj {a c : ℕ} (ha : a < L) (hc : c < L) : (a : ZMod L) = (c : ZMod L) ↔ a = c := by
  constructor
  · intro h; have := congrArg ZMod.val h; rwa [val_cast_lt L ha, val_cast_lt L hc] at this
  · intro h; rw [h]

/-- The edges of `loopC`, listed explicitly: direction 0 at `(a,0,0,0)` and `(a,T,0,0)` for `a < R`, direction 1
at `(0,b,0,0)` and `(R,b,0,0)` for `b < T`. -/
theorem mem_loopC (R T : ℕ) (hRL : R < L) (hTL : T < L) (e : Edge L) :
    e ∈ loopC L R T ↔
      (∃ a < R, e = (![(a : ZMod L), 0, 0, 0], 0) ∨ e = (![(a : ZMod L), (T : ZMod L), 0, 0], 0)) ∨
      (∃ b < T, e = (![0, (b : ZMod L), 0, 0], 1) ∨ e = (![(R : ZMod L), (b : ZMod L), 0, 0], 1)) := by
  obtain ⟨y, d⟩ := e
  simp only [loopC, mem_filter, mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro (⟨rfl, h2, h3, h1 | h1, h0⟩ | ⟨rfl, h2, h3, h0 | h0, h1⟩)
    · refine Or.inl ⟨(y 0).val, h0, Or.inl ⟨?_, rfl⟩⟩
      funext i; fin_cases i <;> simp [h1, h2, h3]
    · refine Or.inl ⟨(y 0).val, h0, Or.inr ⟨?_, rfl⟩⟩
      funext i; fin_cases i <;> simp [h1, h2, h3]
    · refine Or.inr ⟨(y 1).val, h1, Or.inl ⟨?_, rfl⟩⟩
      funext i; fin_cases i <;> simp [h0, h2, h3]
    · refine Or.inr ⟨(y 1).val, h1, Or.inr ⟨?_, rfl⟩⟩
      funext i; fin_cases i <;> simp [h0, h2, h3]
  · rintro (⟨a, ha, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨b, hb, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
    · left; refine ⟨rfl, rfl, rfl, Or.inl rfl, ?_⟩; simp [val_cast_lt L (show a < L by omega), ha]
    · left; refine ⟨rfl, rfl, rfl, Or.inr rfl, ?_⟩; simp [val_cast_lt L (show a < L by omega), ha]
    · right; refine ⟨rfl, rfl, rfl, Or.inl rfl, ?_⟩; simp [val_cast_lt L (show b < L by omega), hb]
    · right; refine ⟨rfl, rfl, rfl, Or.inr rfl, ?_⟩; simp [val_cast_lt L (show b < L by omega), hb]

/-- The boundary side of Stokes for the column cochain: `C` has exactly one direction-1 edge at `(k, b)` when
`k ∈ {0, R}`, none otherwise. -/
theorem loop_eta (R T : ℕ) (hTL : T < L) (k : ZMod L) {b : ℕ} (hb : b < T) :
    ∑ e ∈ loopC L R T, eta L k b e = if (k = 0 ∨ k = (R : ZMod L)) then 1 else 0 := by
  simp only [eta]
  rw [Finset.sum_boole]
  split_ifs with hk
  · have : (loopC L R T).filter (fun e : Edge L => e.2 = 1 ∧ e.1 1 = (b : ZMod L) ∧ e.1 0 = k) =
        {(![k, (b : ZMod L), 0, 0], 1)} := by
      ext ⟨y, d⟩
      simp only [loopC, mem_filter, mem_univ, true_and, mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨h, hd, h1, h0⟩
        refine ⟨?_, hd⟩
        rcases h with ⟨hd', _⟩ | ⟨_, h2, h3, _, _⟩
        · rw [hd] at hd'; exact absurd hd' (by decide)
        · funext i; fin_cases i <;> simp [h0, h1, h2, h3]
      · rintro ⟨rfl, rfl⟩
        refine ⟨Or.inr ⟨rfl, by simp, by simp, by simpa using hk, ?_⟩, rfl, by simp, by simp⟩
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [val_cast_lt L (by omega)]; exact hb
    rw [this, card_singleton, Nat.cast_one]
  · have : (loopC L R T).filter (fun e : Edge L => e.2 = 1 ∧ e.1 1 = (b : ZMod L) ∧ e.1 0 = k) = ∅ := by
      rw [filter_eq_empty_iff]
      rintro ⟨y, d⟩ hy ⟨hd, h1, h0⟩
      simp only [loopC, mem_filter, mem_univ, true_and] at hy
      rcases hy with ⟨hd', _⟩ | ⟨_, _, _, h, _⟩
      · simp only at hd hd'; rw [hd] at hd'; exact absurd hd' (by decide)
      · simp only at h0; exact hk (h0 ▸ h)
    rw [this, card_empty, Nat.cast_zero]

/-- Parity of `|S ∩ col(a, b)|`. -/
noncomputable def par (S : Finset (Plaq L)) (a b : ZMod L) : ZMod 2 := ((S.filter (· ∈ col L a b)).card : ZMod 2)

theorem parity_step (hL : 2 ≤ L) (R T : ℕ) (hTL : T < L) (S : Finset (Plaq L))
    (hS : bd (tinc L) S = loopC L R T) (k : ZMod L) {b : ℕ} (hb : b < T) :
    par L S (k - 1) b + par L S k b = if (k = 0 ∨ k = (R : ZMod L)) then 1 else 0 := by
  rw [← loop_eta L R T hTL k hb, ← hS, ← stokes]
  simp_rw [cob L hL]
  rw [sum_add_distrib, sum_boole, sum_boole]; rfl

theorem zmod2_eq_of_add (x y : ZMod 2) (h : x + y = 0) : x = y := by revert x y; decide
theorem zmod2_eq_add_one (x y : ZMod 2) (h : x + y = 1) : y = x + 1 := by revert x y; decide

theorem row_par (hL : 2 ≤ L) (R T : ℕ) (hR : 1 ≤ R) (hRL : R < L) (hTL : T < L) (S : Finset (Plaq L))
    (hS : bd (tinc L) S = loopC L R T) {b : ℕ} (hb : b < T) :
    (∀ a < R, par L S a b = par L S 0 b) ∧
      (∀ a, R ≤ a → a < L → par L S a b = par L S 0 b + 1) := by
  have step : ∀ a : ℕ, a + 1 < L → a + 1 ≠ R → par L S ((a + 1 : ℕ) : ZMod L) b = par L S a b := by
    intro a ha hR'
    have := parity_step L hL R T hTL S hS ((a + 1 : ℕ) : ZMod L) hb
    rw [if_neg] at this
    · have e : ((a + 1 : ℕ) : ZMod L) - 1 = (a : ZMod L) := by push_cast; ring
      rw [e] at this; exact (zmod2_eq_of_add _ _ this).symm
    · rintro (h | h)
      · have := (cast_inj L ha (by omega : 0 < L)).mp (by simpa using h); omega
      · exact hR' ((cast_inj L ha hRL).mp h)
  have low : ∀ a < R, par L S a b = par L S 0 b := by
    intro a ha
    induction a with
    | zero => simp
    | succ a ih => rw [step a (by omega) (by omega), ih (by omega)]
  have atR : par L S R b = par L S 0 b + 1 := by
    have := parity_step L hL R T hTL S hS (R : ZMod L) hb
    rw [if_pos (Or.inr rfl)] at this
    obtain ⟨r, rfl⟩ : ∃ r, R = r + 1 := ⟨R - 1, by omega⟩
    have e : ((r + 1 : ℕ) : ZMod L) - 1 = (r : ZMod L) := by push_cast; ring
    rw [e, low r (by omega)] at this
    exact zmod2_eq_add_one _ _ this
  refine ⟨low, ?_⟩
  intro a haR haL
  induction a with
  | zero => omega
  | succ a ih =>
    rcases Nat.eq_or_lt_of_le haR with h | h
    · rw [← h]; exact atR
    · rw [step a haL (by omega), ih (by omega) (by omega)]

theorem nonempty_of_par {S : Finset (Plaq L)} {a b : ZMod L} (h : par L S a b = 1) :
    (S.filter (· ∈ col L a b)).Nonempty := by
  rw [nonempty_iff_ne_empty]; intro h'; simp [par, h'] at h

/-- Row `b < T` of any spanning surface has at least `min R (L-R)` occupied columns. -/
theorem row_count (R T : ℕ) (hR : 1 ≤ R) (hRL : R < L) (hTL : T < L) (S : Finset (Plaq L))
    (hS : bd (tinc L) S = loopC L R T) {b : ℕ} (hb : b < T) :
    min R (L - R) ≤ ((range L).filter (fun a : ℕ => (S.filter (· ∈ col L a b)).Nonempty)).card := by
  obtain ⟨low, high⟩ := row_par L (by omega) R T hR hRL hTL S hS hb
  have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases h01 (par L S 0 b) with h0 | h0
  · refine le_trans (min_le_right _ _) ?_
    rw [← Nat.card_Ico R L]
    apply card_le_card; intro a ha; rw [mem_Ico] at ha
    rw [mem_filter, mem_range]
    refine ⟨ha.2, nonempty_of_par L ?_⟩
    rw [high a ha.1 ha.2, h0, zero_add]
  · refine le_trans (min_le_left _ _) ?_
    rw [← card_range R]
    apply card_le_card; intro a ha; rw [mem_range] at ha
    rw [mem_filter, mem_range]
    exact ⟨by omega, nonempty_of_par L (by rw [low a ha, h0])⟩

/-- **Minimal spanning area on the torus**: any `S` with `∂S = C` has `|S| ≥ T · min R (L - R)`. -/
theorem min_area (R T : ℕ) (hR : 1 ≤ R) (hRL : R < L) (hTL : T < L) (S : Finset (Plaq L))
    (hS : bd (tinc L) S = loopC L R T) : T * min R (L - R) ≤ S.card := by
  set W := (range T ×ˢ range L).filter (fun ba : ℕ × ℕ => (S.filter (· ∈ col L ba.2 ba.1)).Nonempty)
  have h1 : T * min R (L - R) ≤ W.card := by
    rw [card_filter, sum_product]
    calc T * min R (L - R) = ∑ b ∈ range T, min R (L - R) := by simp
      _ ≤ _ := by
        apply sum_le_sum; intro b hb
        rw [← card_filter]; exact row_count L R T hR hRL hTL S hS (mem_range.mp hb)
  have h2 : W ⊆ S.image (fun p => ((p.1 1).val, (p.1 0).val)) := by
    rintro ⟨b, a⟩ h
    simp only [W, mem_filter, mem_product, mem_range] at h
    obtain ⟨⟨hb, ha⟩, p, hp⟩ := h
    simp only [mem_filter, col, mem_univ, true_and] at hp
    rw [mem_image]; refine ⟨p, hp.1, ?_⟩
    rw [hp.2.2.1, hp.2.2.2, val_cast_lt L (by omega), val_cast_lt L ha]
  exact h1.trans ((card_le_card h2).trans card_image_le)

/-- Minimal area `R T` when `2R ≤ L`. -/
theorem min_area_half (R T : ℕ) (hR : 1 ≤ R) (h2R : 2 * R ≤ L) (hTL : T < L) (S : Finset (Plaq L))
    (hS : bd (tinc L) S = loopC L R T) : R * T ≤ S.card := by
  have := min_area L R T hR (by omega) hTL S hS
  rwa [min_eq_left (by omega), mul_comm] at this

/-- Orientation of the plane `{d, j}`. -/
def orient (d j : Fin 4) : Ori :=
  if h : d < j then ⟨(d, j), h⟩ else if h' : j < d then ⟨(j, d), h'⟩ else q01

/-- Each edge lies in at most `6` plaquettes. -/
theorem containing_card (e : Edge L) : (univ.filter (fun q : Plaq L => e ∈ tinc L q)).card ≤ 6 := by
  obtain ⟨y, d⟩ := e
  have hsub : univ.filter (fun q : Plaq L => (y, d) ∈ tinc L q) ⊆
      ((univ.erase d) ×ˢ (univ : Finset Bool)).image
        (fun js : Fin 4 × Bool => ((if js.2 then y - unit L js.1 else y), orient d js.1)) := by
    rintro ⟨x, ⟨⟨μ, ν⟩, hμν⟩⟩ hq
    simp only [mem_filter, mem_univ, true_and, tinc, mem_insert, mem_singleton, Prod.mk.injEq] at hq
    simp only at hμν
    rw [mem_image]
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨(ν, false), by simp [hμν.ne'], by simp [orient, hμν]⟩
    · exact ⟨(μ, true), by simp [hμν.ne], by simp [orient, hμν, not_lt.mpr hμν.le]⟩
    · exact ⟨(ν, true), by simp [hμν.ne'], by simp [orient, hμν]⟩
    · exact ⟨(μ, false), by simp [hμν.ne], by simp [orient, hμν, not_lt.mpr hμν.le]⟩
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  simp [card_product]

/-- **Concrete `Δ = 24`**: every plaquette shares an edge with at most 24 plaquettes (itself included). -/
theorem nbr_card_le (p : Plaq L) :
    ((univ : Finset (Plaq L)).filter (fun q => (tinc L p ∩ tinc L q).Nonempty)).card ≤ 24 := by
  have hsub : (univ : Finset (Plaq L)).filter (fun q => (tinc L p ∩ tinc L q).Nonempty) ⊆
      (tinc L p).biUnion (fun e => univ.filter (fun q : Plaq L => e ∈ tinc L q)) := by
    intro q hq
    simp only [mem_filter, mem_univ, true_and] at hq
    obtain ⟨e, he⟩ := hq
    rw [mem_inter] at he
    exact mem_biUnion.mpr ⟨e, he.1, by simp [he.2]⟩
  have h4 : (tinc L p).card ≤ 4 := by
    simp only [tinc]
    refine (card_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((card_insert_le _ _).trans ?_)
    simp
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ e ∈ tinc L p, (univ.filter (fun q : Plaq L => e ∈ tinc L q)).card := card_biUnion_le
    _ ≤ ∑ e ∈ tinc L p, 6 := sum_le_sum (fun e _ => containing_card L e)
    _ = (tinc L p).card * 6 := by rw [sum_const, smul_eq_mul]
    _ ≤ 24 := by omega

/-- **Unconditional Z₂ strong-coupling area law on the 4D torus `(ℤ/L)⁴`** for the `R × T` rectangle,
`2R ≤ L`, `T < L`: `N_C/N_∅ ≤ 2^|T_C| (2^24 t)^{RT} / (1 - 2^24 t)`. -/
theorem area_law_torus (R T : ℕ) (hR : 1 ≤ R) (h2R : 2 * R ≤ L) (hTL : T < L) {t : ℝ} (ht : 0 ≤ t)
    (hKt : (2 : ℝ) ^ 24 * t < 1) :
    N (tinc L) (loopC L R T) t / N (tinc L) ∅ t ≤
      2 ^ ((univ : Finset (Plaq L)).filter (fun p => (tinc L p ∩ loopC L R T).Nonempty)).card *
        ((2 : ℝ) ^ 24 * t) ^ (R * T) / (1 - (2 : ℝ) ^ 24 * t) :=
  area_law_unconditional (tinc L) (loopC L R T) 24 (nbr_card_le L) ht hKt (fun S hS => by
    simp only [span, mem_filter, mem_univ, true_and] at hS
    exact min_area_half L R T hR h2R hTL S hS.1)

/-- The same bound for the Gibbs expectation of the Wilson loop, weights `∏_p (1 + t σ_p)`, `t = tanh β`. -/
theorem wilson_area_law_torus (R T : ℕ) (hR : 1 ≤ R) (h2R : 2 * R ≤ L) (hTL : T < L) {t : ℝ} (ht : 0 ≤ t)
    (hKt : (2 : ℝ) ^ 24 * t < 1) :
    (∑ s : Edge L → Bool, (∏ e ∈ loopC L R T, sg (s e)) * ∏ p, (1 + t * ∏ e ∈ tinc L p, sg (s e))) /
      (∑ s : Edge L → Bool, ∏ p, (1 + t * ∏ e ∈ tinc L p, sg (s e))) ≤
      2 ^ ((univ : Finset (Plaq L)).filter (fun p => (tinc L p ∩ loopC L R T).Nonempty)).card *
        ((2 : ℝ) ^ 24 * t) ^ (R * T) / (1 - (2 : ℝ) ^ 24 * t) := by
  rw [wilson_eq]; exact area_law_torus L R T hR h2R hTL ht hKt

end Torus

end UnifiedTheory.Clay.YangMills.Twisted.Z2Torus
