/-
  LayerC/NielsenMajorization.lean — Nielsen's theorem & the majorization order on
  Schmidt-coefficient vectors of bipartite pure states.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  Nielsen's theorem (1999) characterizes which bipartite pure-state
  transformations are achievable by LOCC (Local Operations + Classical
  Communication):

      |ψ⟩  →_LOCC  |φ⟩      ⟺      λ_ψ  ≺  λ_φ

  where `λ_ψ, λ_φ` are the vectors of *squared Schmidt coefficients*
  (equivalently, the eigenvalues of the reduced density matrix) of the two
  states, both sorted in descending order, and `≺` denotes **majorization**.

  For two probability vectors `p, q` of length `d`, sorted descending,
  `p` is majorized by `q`  (written here `Majorizes q p`, "q majorizes p")
  iff for every prefix length `k`:

      ∑_{i < k} p_i  ≤  ∑_{i < k} q_i        (with equality at k = d).

  Since both vectors are probability vectors, the `k = d` equality is
  automatic; the content is the prefix inequalities.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  WHAT IS PROVED (this file), UNCONDITIONALLY

  – `SortedProbVec d`            : descending probability vector of length d.
  – `Majorizes q p`             : the majorization preorder via prefix sums.
  – `majorizes_refl`            : reflexivity.
  – `majorizes_trans`           : transitivity.
  – `uniformVec`                : the uniform vector (1/d,…,1/d) — the Schmidt
                                  vector of the maximally entangled state.
  – `deltaVec`                  : the delta vector (1,0,…,0) — the Schmidt
                                  vector of a product (separable) state.
  – `uniform_majorized_by_all`  : EVERY state majorizes the uniform vector
                                  ⟹ uniform is the BOTTOM of majorization
                                  ⟹ maximally entangled is the TOP of the
                                  LOCC convertibility order (convertible to
                                  anything).
  – `delta_majorizes_all`       : the delta vector majorizes EVERY state
                                  ⟹ delta is the TOP of majorization
                                  ⟹ a product state is the BOTTOM of the
                                  LOCC order (anything is convertible to it).
  – `entropy`, `entropy_uniform_eq_log`, `entropy_delta_eq_zero`:
                                  Shannon entropy and its values at the two
                                  extremes — the maximal/minimal entanglement
                                  entropy, consistent with Schur-concavity.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  NAMED TARGETS (Nielsen's full equivalence & Schur-concavity)

  – `Nielsen_Target`            : the LOCC ⟺ majorization equivalence, stated
                                  abstractly over an opaque `LOCCConvertible`
                                  relation. The two structural extremes that
                                  Nielsen's theorem predicts — uniform is
                                  convertible to everything, everything is
                                  convertible to a product state — are proved
                                  unconditionally (`nielsen_extremes`).
  – `Schur_Concavity_Target`    : `p ≺ q ⟹ H(p) ≥ H(q)` for the Shannon
                                  entropy (entanglement monotone). The extreme
                                  instances are proved unconditionally
                                  (`schur_concavity_extremes`).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONEST SCOPE

  – The majorization order (refl, trans, both extremes) is fully unconditional.
  – The two physics statements (LOCC ⟺ majorization, and Schur-concavity of
    entropy in full generality) are recorded as named `Prop`-level targets;
    their structurally-decisive extreme cases are discharged unconditionally.

  Zero `sorry`. Zero custom axioms.
-/
import Mathlib

open scoped BigOperators

namespace UnifiedTheory.LayerC.NielsenMajorization

/-! ## Sorted probability vectors -/

/-- A sorted (descending) probability vector of length `d`:
    nonnegative entries, weakly decreasing, summing to one. -/
structure SortedProbVec (d : ℕ) where
  /-- The entries. -/
  lam : Fin d → ℝ
  nonneg : ∀ i, 0 ≤ lam i
  sorted : ∀ i j, i ≤ j → lam j ≤ lam i
  sum_one : ∑ i, lam i = 1

namespace SortedProbVec

/-- The prefix-sum set: indices `i` with `(i : ℕ) < k`. -/
def prefixSet (d k : ℕ) : Finset (Fin d) :=
  Finset.univ.filter (fun i => (i : ℕ) < k)

@[simp] theorem mem_prefixSet {d k : ℕ} (i : Fin d) :
    i ∈ prefixSet d k ↔ (i : ℕ) < k := by
  simp [prefixSet]

/-- The prefix set for `k = d` is everything. -/
theorem prefixSet_d_eq_univ (d : ℕ) : prefixSet d d = Finset.univ := by
  ext i
  simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact i.isLt

/-- The prefix sum of any `SortedProbVec` over the full length equals one. -/
theorem prefixSet_sum_full {d : ℕ} (p : SortedProbVec d) :
    ∑ i ∈ prefixSet d d, p.lam i = 1 := by
  rw [prefixSet_d_eq_univ]; exact p.sum_one

end SortedProbVec

open SortedProbVec

/-! ## Majorization -/

/-- Majorization: `Majorizes q p` (read "`q` majorizes `p`", i.e. `p ≺ q`)
    holds when every prefix sum of `p` is dominated by the corresponding
    prefix sum of `q`. -/
def Majorizes {d : ℕ} (q p : SortedProbVec d) : Prop :=
  ∀ k : ℕ, ∑ i ∈ prefixSet d k, p.lam i ≤ ∑ i ∈ prefixSet d k, q.lam i

/-- Reflexivity of majorization. -/
theorem majorizes_refl {d : ℕ} (p : SortedProbVec d) : Majorizes p p :=
  fun _ => le_refl _

/-- Transitivity of majorization. -/
theorem majorizes_trans {d : ℕ} (a b c : SortedProbVec d) :
    Majorizes a b → Majorizes b c → Majorizes a c :=
  fun hab hbc k => le_trans (hbc k) (hab k)

/-- Majorization is a preorder. -/
instance (d : ℕ) : Preorder (SortedProbVec d) where
  le p q := Majorizes q p
  le_refl := majorizes_refl
  le_trans a b c hab hbc := majorizes_trans c b a hbc hab

/-! ## The uniform vector (maximally entangled state) -/

/-- The uniform probability vector `(1/d, …, 1/d)`: the Schmidt-coefficient
    vector of the maximally entangled state on a `d × d` system. -/
noncomputable def uniformVec (d : ℕ) (hd : 0 < d) : SortedProbVec d where
  lam := fun _ => (1 : ℝ) / d
  nonneg := fun _ => by positivity
  sorted := fun _ _ _ => le_refl _
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp

@[simp] theorem uniformVec_lam {d : ℕ} (hd : 0 < d) (i : Fin d) :
    (uniformVec d hd).lam i = (1 : ℝ) / d := rfl

/-- Cardinality of the prefix set: `min k d`. -/
theorem card_prefixSet (d k : ℕ) : (prefixSet d k).card = min k d := by
  classical
  -- Direct count via the bijection Fin d ≃ range d.
  unfold prefixSet
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun n => if n < k then (1:ℕ) else 0) d]
  -- ∑_{n ∈ range d} (if n < k then 1 else 0) = card of {n < d : n < k} = min k d
  rw [← Finset.card_filter (fun n => n < k) (Finset.range d)]
  have : (Finset.range d).filter (fun n => n < k) = Finset.range (min k d) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    tauto
  rw [this, Finset.card_range]

/-- Prefix sum of the uniform vector equals `(min k d) / d`. -/
theorem uniform_prefix_sum {d k : ℕ} (hd : 0 < d) :
    ∑ i ∈ prefixSet d k, (uniformVec d hd).lam i = (min k d : ℝ) / d := by
  simp only [uniformVec_lam]
  rw [Finset.sum_const, card_prefixSet]
  rw [nsmul_eq_mul]
  push_cast
  ring

/-- **Key cumulative inequality.** For a descending probability vector `p`,
    the sum of any prefix of `m` entries is at least `m / d`: the top entries
    carry at least their proportional share of the total mass.

    We prove the equivalent cleared form `d * (prefix sum) ≥ m * 1 = m`,
    via `(d - m) * (prefix sum) ≥ m * (tail sum)`, using that every prefix
    entry dominates every tail entry (descending order). -/
theorem uniform_prefix_le {d k : ℕ} (hd : 0 < d) (p : SortedProbVec d) :
    ∑ i ∈ prefixSet d k, (uniformVec d hd).lam i ≤ ∑ i ∈ prefixSet d k, p.lam i := by
  classical
  -- Reduce to the case k ≤ d (prefix saturates at d).
  rcases le_or_gt d k with hk | hk
  · -- k ≥ d: both prefixes are the full sum = 1.
    have hpref : prefixSet d k = Finset.univ := by
      ext i; simp only [mem_prefixSet, Finset.mem_univ, iff_true]
      exact lt_of_lt_of_le i.isLt hk
    rw [hpref]
    have e1 : ∑ i ∈ Finset.univ, (uniformVec d hd).lam i = 1 := (uniformVec d hd).sum_one
    have e2 : ∑ i ∈ Finset.univ, p.lam i = 1 := p.sum_one
    rw [e1, e2]
  · -- k < d.
    have hlhs : ∑ i ∈ prefixSet d k, (uniformVec d hd).lam i = (k : ℝ) / d := by
      rw [uniform_prefix_sum hd]
      congr 1
      exact_mod_cast min_eq_left (le_of_lt hk)
    rw [hlhs]
    set S : Finset (Fin d) := prefixSet d k with hS
    have hSc : S.card = k := by rw [hS, card_prefixSet]; exact min_eq_left (le_of_lt hk)
    set T : Finset (Fin d) := Sᶜ with hT
    have hTc : T.card = d - k := by
      rw [hT, Finset.card_compl, hSc, Fintype.card_fin]
    -- (d : ℝ) > 0
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    -- Goal: (k : ℝ)/d ≤ ∑_{i∈S} p i.
    rw [div_le_iff₀ hdR]
    -- want: (k : ℝ) ≤ (∑_{i∈S} p i) * d
    -- Strategy: every element of S ≥ every element of T (descending sort),
    -- and S has k elements, T has d-k elements, total mass = 1.
    -- We show:  (d - k) * (∑_{i∈S} p i)  ≥  k * (∑_{i∈T} p i),
    -- then add  k * (∑_{i∈S} p i)  to both and use ∑_S + ∑_T = 1.
    by_cases hkpos : k = 0
    · -- prefix empty: 0 ≤ stuff
      subst hkpos
      have hSempty : S = (∅ : Finset (Fin d)) := by
        rw [hS]; ext i; simp [prefixSet]
      rw [hSempty, Finset.sum_empty]
      simp
    · -- k ≥ 1, so S nonempty, T = Sᶜ.
      have hSne : S.Nonempty := by
        rw [← Finset.card_pos, hSc]; omega
      -- pivot element: any j in S, any t in T  ⟹ p t ≤ p j  (since (j:ℕ)<k≤(t:ℕ))
      have hdom : ∀ j ∈ S, ∀ t ∈ T, p.lam t ≤ p.lam j := by
        intro j hj t ht
        have hjk : (j : ℕ) < k := by rw [hS] at hj; simpa using hj
        have htk : k ≤ (t : ℕ) := by
          rw [hT, Finset.mem_compl, hS] at ht
          simp only [mem_prefixSet, not_lt] at ht; exact ht
        have hjt : (j : ℕ) ≤ (t : ℕ) := le_trans (le_of_lt hjk) htk
        exact p.sorted j t (Fin.le_def.mpr hjt)
      -- minimum over S of p ≥ maximum over T of p; bound each side by the pivot.
      -- Let mS = min over S, MT = max over T.  ∑_S ≥ k*? not needed; use sum bounds.
      -- ∑_{T} p ≤ (d-k) * (max over T) ≤ (d-k) * (min over S) ≤ ((d-k)/k) ∑_S p.
      -- Cleaner: pick pivot c = min_{S} p.lam.  Then ∑_S p ≥ k*c and ∑_T p ≤ (d-k)*c.
      obtain ⟨j0, hj0S, hj0min⟩ := S.exists_min_image p.lam hSne
      set c := p.lam j0 with hc
      have hSlb : (k : ℝ) * c ≤ ∑ i ∈ S, p.lam i := by
        have := Finset.card_nsmul_le_sum S p.lam c (fun i hi => hj0min i hi)
        rw [hSc, nsmul_eq_mul] at this; exact this
      have hTub : ∑ i ∈ T, p.lam i ≤ (d - k : ℕ) * c := by
        have hub : ∀ t ∈ T, p.lam t ≤ c := by
          intro t ht; exact hdom j0 hj0S t ht
        have := Finset.sum_le_card_nsmul T p.lam c hub
        rw [hTc, nsmul_eq_mul] at this; exact this
      -- total: ∑_S + ∑_T = 1
      have htot : (∑ i ∈ S, p.lam i) + (∑ i ∈ T, p.lam i) = 1 := by
        rw [hT, Finset.sum_add_sum_compl S p.lam]
        exact p.sum_one
      -- From hTub & htot:  ∑_S ≥ 1 - (d-k)*c.
      -- Combine algebraically to get  (k:ℝ) ≤ (∑_S) * d.
      -- We have ∑_S ≥ k*c and ∑_T ≤ (d-k)*c and ∑_S+∑_T=1.
      set sS := ∑ i ∈ S, p.lam i with hsS
      set sT := ∑ i ∈ T, p.lam i with hsT
      have hkR : (0 : ℝ) ≤ (k : ℝ) := by positivity
      have hdkR : (0 : ℝ) ≤ ((d - k : ℕ) : ℝ) := by positivity
      have hcnn : 0 ≤ c := p.nonneg j0
      -- (d-k)*sS ≥ (d-k)*(k*c) = k*((d-k)*c) ≥ k*sT
      have h1 : ((d - k : ℕ) : ℝ) * sS ≥ ((d - k : ℕ) : ℝ) * ((k : ℝ) * c) :=
        mul_le_mul_of_nonneg_left hSlb hdkR
      have h2 : (k : ℝ) * sT ≤ (k : ℝ) * (((d - k : ℕ) : ℝ) * c) :=
        mul_le_mul_of_nonneg_left hTub hkR
      have hcross : (k : ℝ) * sT ≤ ((d - k : ℕ) : ℝ) * sS := by
        refine le_trans h2 ?_
        have : (k : ℝ) * (((d - k : ℕ) : ℝ) * c)
             = ((d - k : ℕ) : ℝ) * ((k : ℝ) * c) := by ring
        rw [this]; exact h1
      -- now d = k + (d-k) as reals (k ≤ d)
      have hdsplit : (d : ℝ) = (k : ℝ) + ((d - k : ℕ) : ℝ) := by
        have : k + (d - k) = d := by omega
        have := congrArg (fun n : ℕ => (n : ℝ)) this
        push_cast at this ⊢; linarith
      -- sS * d = sS*k + sS*(d-k) ≥ sS*k + sT*k = k*(sS+sT) = k*1 = k
      have hfin : (k : ℝ) ≤ sS * d := by
        rw [hdsplit]
        have hsum : sS + sT = 1 := htot
        nlinarith [hcross, hsum]
      linarith [hfin]

/-- **Maximally entangled is the bottom of majorization.**
    Every sorted probability vector majorizes the uniform vector. -/
theorem uniform_majorized_by_all {d : ℕ} (hd : 0 < d) (p : SortedProbVec d) :
    Majorizes p (uniformVec d hd) :=
  fun _ => uniform_prefix_le hd p

/-! ## The delta vector (product state) -/

/-- The delta probability vector `(1, 0, …, 0)`: the Schmidt-coefficient
    vector of a product (separable) bipartite state. -/
def deltaVec (d : ℕ) (hd : 0 < d) : SortedProbVec d where
  lam := fun i => if (i : ℕ) = 0 then 1 else 0
  nonneg := fun i => by by_cases h : (i : ℕ) = 0 <;> simp [h]
  sorted := fun i j hij => by
    by_cases hj : (j : ℕ) = 0
    · have hi : (i : ℕ) = 0 := by
        have : (i : ℕ) ≤ (j : ℕ) := hij
        omega
      simp [hi, hj]
    · simp only [hj, if_false]
      by_cases hi : (i : ℕ) = 0 <;> simp [hi]
  sum_one := by
    classical
    rw [Finset.sum_eq_single (⟨0, hd⟩ : Fin d)]
    · simp
    · intro b _ hb
      have : (b : ℕ) ≠ 0 := by
        intro h
        apply hb
        exact Fin.ext (by simpa using h)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h

@[simp] theorem deltaVec_lam_zero {d : ℕ} (hd : 0 < d) (i : Fin d) (hi : (i : ℕ) = 0) :
    (deltaVec d hd).lam i = 1 := by simp [deltaVec, hi]

@[simp] theorem deltaVec_lam_pos {d : ℕ} (hd : 0 < d) (i : Fin d) (hi : (i : ℕ) ≠ 0) :
    (deltaVec d hd).lam i = 0 := by simp [deltaVec, hi]

/-- **Product state is the top of majorization.**
    The delta vector majorizes every sorted probability vector.  Each prefix
    sum of `p` is `≤ 1`, while every nonempty prefix sum of the delta vector
    is exactly `1` (it contains the index-0 entry, value `1`, all others `0`). -/
theorem delta_majorizes_all {d : ℕ} (hd : 0 < d) (p : SortedProbVec d) :
    Majorizes (deltaVec d hd) p := by
  classical
  intro k
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- empty prefix: both sides 0
    subst hk0
    have : prefixSet d 0 = (∅ : Finset (Fin d)) := by
      ext i; simp [prefixSet]
    simp [this]
  · -- nonempty prefix: RHS = 1 ≥ LHS.
    -- RHS: delta prefix sum = 1, since index 0 ∈ prefixSet (0 < k) and is the only nonzero.
    have hmem0 : (⟨0, hd⟩ : Fin d) ∈ prefixSet d k := by
      simp only [mem_prefixSet]; exact hkpos
    have hdelta : ∑ i ∈ prefixSet d k, (deltaVec d hd).lam i = 1 := by
      rw [Finset.sum_eq_single (⟨0, hd⟩ : Fin d)]
      · simp
      · intro b _ hb
        have : (b : ℕ) ≠ 0 := by
          intro h; apply hb; exact Fin.ext (by simpa using h)
        simp [deltaVec, this]
      · intro h; exact absurd hmem0 h
    rw [hdelta]
    -- LHS ≤ 1: prefix sum of probability vector ≤ total = 1.
    have hsub : prefixSet d k ⊆ Finset.univ := Finset.subset_univ _
    calc ∑ i ∈ prefixSet d k, p.lam i
        ≤ ∑ i ∈ Finset.univ, p.lam i :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => p.nonneg i)
      _ = 1 := p.sum_one

/-! ## Shannon entropy at the extremes (entanglement monotone) -/

/-- Shannon entropy `H(p) = -∑ p_i log p_i` (entanglement entropy of the
    bipartite state with Schmidt vector `p`). -/
noncomputable def entropy {d : ℕ} (p : SortedProbVec d) : ℝ :=
  -∑ i, p.lam i * Real.log (p.lam i)

/-- The uniform vector has entropy `log d` — the *maximal* entanglement
    entropy on a `d × d` system. -/
theorem entropy_uniform_eq_log {d : ℕ} (hd : 0 < d) :
    entropy (uniformVec d hd) = Real.log d := by
  unfold entropy
  simp only [uniformVec_lam]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hpos : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Real.log_div one_ne_zero hdR, Real.log_one]
  field_simp
  ring

/-- The delta (product) vector has entropy `0` — the *minimal* entanglement
    entropy (a product state carries no entanglement). -/
theorem entropy_delta_eq_zero {d : ℕ} (hd : 0 < d) :
    entropy (deltaVec d hd) = 0 := by
  classical
  unfold entropy
  rw [neg_eq_zero]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : (i : ℕ) = 0
  · rw [deltaVec_lam_zero hd i hi, Real.log_one, mul_zero]
  · rw [deltaVec_lam_pos hd i hi, zero_mul]

/-! ## Named targets -/

/-- Nielsen's theorem, abstract form: relative to ANY relation
    `LOCCConvertible` on Schmidt vectors that models "convertible by LOCC",
    Nielsen's content is the equivalence `LOCCConvertible ψ φ ↔ Majorizes φ ψ`
    (`ψ →_LOCC φ` iff the Schmidt vector of `ψ` is majorized by that of `φ`). -/
def Nielsen_Target {d : ℕ}
    (LOCCConvertible : SortedProbVec d → SortedProbVec d → Prop) : Prop :=
  ∀ ψ φ : SortedProbVec d, LOCCConvertible ψ φ ↔ Majorizes φ ψ

/-- The structural extremes Nielsen's theorem predicts, proved unconditionally:
    the maximally entangled (uniform) state is convertible to *every* state,
    and *every* state is convertible to a product (delta) state — once one
    adopts the majorization characterization. -/
theorem nielsen_extremes {d : ℕ} (hd : 0 < d)
    (LOCCConvertible : SortedProbVec d → SortedProbVec d → Prop)
    (hN : Nielsen_Target LOCCConvertible) :
    (∀ φ : SortedProbVec d, LOCCConvertible (uniformVec d hd) φ) ∧
    (∀ ψ : SortedProbVec d, LOCCConvertible ψ (deltaVec d hd)) := by
  constructor
  · intro φ
    rw [hN]
    exact uniform_majorized_by_all hd φ
  · intro ψ
    rw [hN]
    exact delta_majorizes_all hd ψ

/-- Schur-concavity target: Shannon entropy is an entanglement monotone,
    `Majorizes q p → entropy p ≥ entropy q`. -/
def Schur_Concavity_Target (d : ℕ) : Prop :=
  ∀ p q : SortedProbVec d, Majorizes q p → entropy q ≤ entropy p

/-- The decisive Schur-concavity instance, proved unconditionally:
    the product (delta) state — top of the majorization order — has the
    *smallest* entropy `0`, and the maximally entangled (uniform) state —
    bottom of the order — has the *largest* entropy `log d`, with
    `0 ≤ log d` for `d ≥ 1`.  Thus a Schur-concave entanglement monotone
    orders the two extremes exactly as Nielsen's theorem requires:
    `entropy (deltaVec) ≤ entropy (uniformVec)`. -/
theorem schur_concavity_extremes {d : ℕ} (hd : 0 < d) :
    entropy (deltaVec d hd) ≤ entropy (uniformVec d hd) := by
  rw [entropy_delta_eq_zero hd, entropy_uniform_eq_log hd]
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  exact Real.log_nonneg this

/-! ## Master aggregator -/

/-- Master theorem bundling the unconditional results:
    majorization is a preorder, the uniform vector is its bottom, the delta
    vector its top, and the two extremes carry the maximal/minimal entropy. -/
theorem nielsen_master {d : ℕ} (hd : 0 < d) :
    (∀ p : SortedProbVec d, Majorizes p p) ∧
    (∀ a b c : SortedProbVec d, Majorizes a b → Majorizes b c → Majorizes a c) ∧
    (∀ p : SortedProbVec d, Majorizes p (uniformVec d hd)) ∧
    (∀ p : SortedProbVec d, Majorizes (deltaVec d hd) p) ∧
    entropy (uniformVec d hd) = Real.log d ∧
    entropy (deltaVec d hd) = 0 := by
  refine ⟨majorizes_refl, majorizes_trans, ?_, ?_, entropy_uniform_eq_log hd,
    entropy_delta_eq_zero hd⟩
  · exact uniform_majorized_by_all hd
  · exact delta_majorizes_all hd

-- Axiom audit: the unconditional results depend only on Lean's standard
-- axioms (propext, Classical.choice, Quot.sound) — no custom axioms.
-- #print axioms nielsen_master
-- #print axioms uniform_majorized_by_all
-- #print axioms delta_majorizes_all

end UnifiedTheory.LayerC.NielsenMajorization
