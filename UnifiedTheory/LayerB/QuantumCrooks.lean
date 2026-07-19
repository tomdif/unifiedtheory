/-
  LayerB/QuantumCrooks.lean
  ──────────────────────────

  **Quantum Crooks fluctuation theorem** (Tasaki 2000; Crooks 1999).

  Sister identity to the quantum Jarzynski equality.  Where Jarzynski
  is an *expectation* identity (`⟨exp(-βW)⟩ = exp(-β ΔF)`), Crooks is a
  *per-transition* identity: the ratio of forward-to-reverse transition
  probabilities is governed by the work `W` performed and the
  equilibrium free-energy difference `ΔF`:

      P_F(n → m)  /  P_R(m → n)  =  exp( β · (W − ΔF) ) ,

  where
    • `W := E_m^1 − E_n^0` is the work in the two-time-measurement scheme,
    • `ΔF := F(H_1) − F(H_0)` is the equilibrium free-energy difference,
    • `P_F(n → m) := (1/Z_0) · exp(-β E_n^0) · |⟨m|U_τ|n⟩|²` is the joint
      probability of measuring `E_n^0` initially and `E_m^1` finally,
    • `P_R(m → n) := (1/Z_1) · exp(-β E_m^1) · |⟨n|U_τ†|m⟩|²` is the same
      for the time-reversed protocol H_1 → H_0 driven by `U_τ†`.

  Crooks ⇒ Jarzynski: summing the per-transition identity over all `(n, m)`
  with weight `exp(-β W)` reproduces the Jarzynski average; this file
  carries that derivation out explicitly.

  ## Mathematical core (per-transition Crooks)

  The cleanest algebraic form, avoiding division, is the multiplicative
  identity

      P_F(n → m) · exp(β · ΔF)  =  P_R(m → n) · exp(β · W) .

  Expanding via `exp(β · ΔF) = Z_0 / Z_1` (Jarzynski free-energy bridge):

      (1/Z_0) · exp(-β E_n^0) · |W_{mn}|² · (Z_0 / Z_1)
        = (1/Z_1) · exp(-β E_n^0) · |W_{mn}|²
        = (1/Z_1) · exp(-β E_m^1) · |W_{mn}|² · exp(β · (E_m^1 − E_n^0))
        = P_R(m → n) · exp(β · W) .

  The `|⟨n|U_τ†|m⟩|² = |⟨m|U_τ|n⟩|² = |W_{mn}|²` identity is unitarity
  of the mixed-basis transition matrix `W = star U_1 · U_τ · U_0`.

  ## What this file ships

    * `forwardTransitionProb P i j` — joint probability of (j → i) in
      the forward protocol: `(1/Z_0) · exp(-β E_0 j) · |W_{ij}|²`.
    * `reverseTransitionProb P i j` — joint probability of (i → j) in
      the reverse protocol: `(1/Z_1) · exp(-β E_1 i) · |W_{ij}|²`.
    * `work P i j` — `E_1 i − E_0 j`.
    * `deltaF P` — `freeEnergy β H_1 − freeEnergy β H_0`.
    * `crooks_per_transition` — `P_F · exp(β ΔF) = P_R · exp(β W)`.
    * `crooks_per_transition_ratio` — division form of the above.
    * `forward_marginal_sum` — `∑_{m,k} P_F(k→m) = 1` (normalisation).
    * `reverse_marginal_sum` — `∑_{m,k} P_R(m→k) = 1` (normalisation).
    * `crooks_implies_jarzynski` — Crooks + summation gives Jarzynski.

  ## Honest scoping

    * Finite-dimensional Hilbert space (`Matrix (Fin n) (Fin n) ℂ`),
      inherited from `QuantumJarzynski`.
    * The reverse protocol's transition amplitudes are taken to be
      `|⟨n|U_τ†|m⟩|² = |W_{mn}|²`, which is the same modulus as the
      forward amplitude under the mixed-basis transition matrix `W`.
      We DEFINE `reverseTransitionProb` using `|W_{ij}|²` rather than
      re-deriving it from a reverse `JarzynskiProtocol` instance; the
      two are equal as real numbers by `Complex.norm_conj` /
      `star_norm_sq`.
    * `β > 0` and `n ≥ 1` (Nonempty (Fin n)) inherited from the
      protocol.

  Zero `sorry`, zero custom `axiom`; only the three Lean kernel
  axioms `[propext, Classical.choice, Quot.sound]`.
-/

import UnifiedTheory.LayerB.QuantumJarzynski

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.QuantumCrooks

open UnifiedTheory.LayerB.QuantumJarzynski
open Matrix Complex

/-! ## 1. Per-transition forward & reverse probabilities -/

/-- **Forward joint probability** of measuring `E_0 j` initially and
    `E_1 i` finally in the two-time-measurement scheme on the forward
    protocol `H_0 → H_1` driven by `U_τ`:

      `P_F(j → i)  =  (1/Z_0) · exp(-β E_0^j) · |W_{ij}|²`.

    The factor `exp(-β E_0^j)/Z_0` is the initial Boltzmann weight;
    `|W_{ij}|²` is the transition probability `|⟨i|U_τ|j⟩|²`. -/
noncomputable def forwardTransitionProb {n : ℕ}
    (P : JarzynskiProtocol n) (i j : Fin n) : ℝ :=
  (1 / partitionFunction P.β P.H_0)
    * Real.exp (-P.β * P.E_0 j)
    * ‖P.transition i j‖^2

/-- **Reverse joint probability** of measuring `E_1 i` initially and
    `E_0 j` finally in the reverse two-time-measurement scheme on the
    time-reversed protocol `H_1 → H_0` driven by `U_τ†`:

      `P_R(i → j)  =  (1/Z_1) · exp(-β E_1^i) · |W_{ij}|²` ,

    using `|⟨j|U_τ†|i⟩|² = |⟨i|U_τ|j⟩|² = |W_{ij}|²` (unitarity). -/
noncomputable def reverseTransitionProb {n : ℕ}
    (P : JarzynskiProtocol n) (i j : Fin n) : ℝ :=
  (1 / partitionFunction P.β P.H_1)
    * Real.exp (-P.β * P.E_1 i)
    * ‖P.transition i j‖^2

/-- **Work** performed in the transition `(j → i)`: `W = E_1^i − E_0^j`. -/
noncomputable def work {n : ℕ} (P : JarzynskiProtocol n)
    (i j : Fin n) : ℝ :=
  P.E_1 i - P.E_0 j

/-- **Equilibrium free-energy difference** `ΔF := F(H_1) − F(H_0)`. -/
noncomputable def deltaF {n : ℕ} (P : JarzynskiProtocol n) : ℝ :=
  freeEnergy P.β P.H_1 - freeEnergy P.β P.H_0

/-! ## 2. The per-transition Crooks identity -/

/-- **Per-transition CROOKS FLUCTUATION THEOREM** (multiplicative form).

      `P_F(j → i) · exp(β · ΔF)  =  P_R(i → j) · exp(β · W_{ij})` .

    Equivalently, `P_F / P_R = exp(β (W − ΔF))`, but the multiplicative
    form holds with no positivity/non-zero hypotheses on `P_R` and is
    the cleanest entry point for the Crooks → Jarzynski derivation.

    Proof: algebraic expansion using `exp(β ΔF) = Z_0/Z_1`
    (`exp_neg_beta_delta_F_eq_Z_ratio` with signs flipped) and
    `exp(-β E_0^j) · exp(β W) = exp(-β E_1^i)` (the same cancellation
    as in `jarzynski_summand_cancellation`). -/
theorem crooks_per_transition {n : ℕ} [Nonempty (Fin n)]
    (P : JarzynskiProtocol n) (i j : Fin n) :
    forwardTransitionProb P i j * Real.exp (P.β * deltaF P)
      = reverseTransitionProb P i j * Real.exp (P.β * work P i j) := by
  unfold forwardTransitionProb reverseTransitionProb work deltaF
  -- Z_0, Z_1 > 0 (Nonempty + β > 0).
  have hZ0 : 0 < partitionFunction P.β P.H_0 :=
    partitionFunction_pos_of_nonempty P.β P.H_0 P.H_0_isHerm
  have hZ1 : 0 < partitionFunction P.β P.H_1 :=
    partitionFunction_pos_of_nonempty P.β P.H_1 P.H_1_isHerm
  have hZ0_ne : partitionFunction P.β P.H_0 ≠ 0 := ne_of_gt hZ0
  have hZ1_ne : partitionFunction P.β P.H_1 ≠ 0 := ne_of_gt hZ1
  -- β ≠ 0.
  have hβ : P.β ≠ 0 := ne_of_gt P.β_pos
  -- exp(β ΔF) = Z_0 / Z_1.  Derive from the existing
  -- exp(-β ΔF) = Z_1 / Z_0 by negation.
  have h_negΔF :
      Real.exp (-P.β * (freeEnergy P.β P.H_1 - freeEnergy P.β P.H_0))
        = partitionFunction P.β P.H_1 / partitionFunction P.β P.H_0 :=
    exp_neg_beta_delta_F_eq_Z_ratio P.β hβ P.H_0 P.H_1 hZ0 hZ1
  -- exp(β ΔF) is the reciprocal, hence Z_0 / Z_1.
  have h_posΔF :
      Real.exp (P.β * (freeEnergy P.β P.H_1 - freeEnergy P.β P.H_0))
        = partitionFunction P.β P.H_0 / partitionFunction P.β P.H_1 := by
    have h_exp_neg : Real.exp (-P.β * (freeEnergy P.β P.H_1
                                         - freeEnergy P.β P.H_0))
                   = (Real.exp (P.β * (freeEnergy P.β P.H_1
                                         - freeEnergy P.β P.H_0)))⁻¹ := by
      rw [← Real.exp_neg]
      congr 1
      ring
    rw [h_exp_neg] at h_negΔF
    have h_pos_exp : 0 < Real.exp (P.β * (freeEnergy P.β P.H_1
                                            - freeEnergy P.β P.H_0)) :=
      Real.exp_pos _
    have h_ne : Real.exp (P.β * (freeEnergy P.β P.H_1
                                   - freeEnergy P.β P.H_0)) ≠ 0 :=
      ne_of_gt h_pos_exp
    -- (1 / x) = Z_1 / Z_0  ⇒  x = Z_0 / Z_1.
    field_simp at h_negΔF
    field_simp
    linarith [h_negΔF]
  -- exp(β W) cancellation: exp(-β E_0^j) · exp(β (E_1^i - E_0^j)) = exp(-β E_1^i).
  -- Equivalently exp(-β E_1^i) · exp(β (E_1^i - E_0^j)) = exp(-β E_0^j).
  have h_exp_work :
      Real.exp (-P.β * P.E_1 i) * Real.exp (P.β * (P.E_1 i - P.E_0 j))
        = Real.exp (-P.β * P.E_0 j) := by
    rw [← Real.exp_add]
    congr 1
    ring
  -- Now combine.  LHS = (1/Z_0) · exp(-β E_0^j) · |W|² · (Z_0/Z_1)
  --                  = (1/Z_1) · exp(-β E_0^j) · |W|².
  -- RHS = (1/Z_1) · exp(-β E_1^i) · |W|² · exp(β (E_1^i - E_0^j))
  --     = (1/Z_1) · exp(-β E_0^j) · |W|².
  rw [h_posΔF]
  -- The expression is now an algebraic identity in ℝ.
  -- LHS: (1/Z_0) * exp(-β E_0 j) * ‖W‖² * (Z_0/Z_1)
  -- RHS: (1/Z_1) * exp(-β E_1 i) * ‖W‖² * exp(β (E_1 i - E_0 j))
  have h_rhs_simp :
      (1 / partitionFunction P.β P.H_1) * Real.exp (-P.β * P.E_1 i)
          * ‖P.transition i j‖^2
          * Real.exp (P.β * (P.E_1 i - P.E_0 j))
        = (1 / partitionFunction P.β P.H_1) * Real.exp (-P.β * P.E_0 j)
            * ‖P.transition i j‖^2 := by
    calc (1 / partitionFunction P.β P.H_1) * Real.exp (-P.β * P.E_1 i)
            * ‖P.transition i j‖^2
            * Real.exp (P.β * (P.E_1 i - P.E_0 j))
        = (1 / partitionFunction P.β P.H_1) * ‖P.transition i j‖^2
            * (Real.exp (-P.β * P.E_1 i)
                * Real.exp (P.β * (P.E_1 i - P.E_0 j))) := by ring
      _ = (1 / partitionFunction P.β P.H_1) * ‖P.transition i j‖^2
            * Real.exp (-P.β * P.E_0 j) := by rw [h_exp_work]
      _ = (1 / partitionFunction P.β P.H_1) * Real.exp (-P.β * P.E_0 j)
            * ‖P.transition i j‖^2 := by ring
  rw [h_rhs_simp]
  -- LHS: (1/Z_0) * exp(-β E_0 j) * ‖W‖² * (Z_0/Z_1)
  --    = (1/Z_1) * exp(-β E_0 j) * ‖W‖²
  field_simp

/-! ## 3. Division form of the Crooks identity -/

/-- **CROOKS — division form** (informal headline form).

      `P_F(j → i) / P_R(i → j)  =  exp(β · (W − ΔF))` ,

    where `W = E_1^i − E_0^j`.  Requires `P_R(i → j) ≠ 0`, i.e. a
    non-vanishing transition amplitude (which is automatic when
    `|W_{ij}|² > 0`).

    Proof: the multiplicative form `crooks_per_transition` plus
    elementary algebra on positive reals. -/
theorem crooks_per_transition_ratio {n : ℕ} [Nonempty (Fin n)]
    (P : JarzynskiProtocol n) (i j : Fin n)
    (h_ne : reverseTransitionProb P i j ≠ 0) :
    forwardTransitionProb P i j / reverseTransitionProb P i j
      = Real.exp (P.β * (work P i j - deltaF P)) := by
  have h := crooks_per_transition P i j
  have h_exp_diff :
      Real.exp (P.β * (work P i j - deltaF P))
        = Real.exp (P.β * work P i j) / Real.exp (P.β * deltaF P) := by
    rw [show P.β * (work P i j - deltaF P)
            = P.β * work P i j - P.β * deltaF P from by ring]
    rw [Real.exp_sub]
  rw [h_exp_diff]
  have h_pos : 0 < Real.exp (P.β * deltaF P) := Real.exp_pos _
  have h_pos_ne : Real.exp (P.β * deltaF P) ≠ 0 := ne_of_gt h_pos
  -- From P_F · exp(β ΔF) = P_R · exp(β W), divide both sides by
  -- (P_R · exp(β ΔF)).
  field_simp
  linarith [h]

/-! ## 4. Marginal-sum normalisations -/

/-- **Forward total probability is 1.**

    `∑_{m, k} P_F(k → m) = 1`.

    Reduces to the Jarzynski-style chain `(1/Z_0) · ∑_m ∑_k
    exp(-β E_0^k) · |W_{mk}|² = (1/Z_0) · ∑_k exp(-β E_0^k) · ∑_m
    |W_{mk}|² = (1/Z_0) · ∑_k exp(-β E_0^k) · 1 = (1/Z_0) · Z_0 = 1`,

    using the **column-sum** unitarity of the transition matrix
    `∑_m |W_{mk}|² = 1` derived from `star W · W = 1`. -/
theorem forward_marginal_sum {n : ℕ} [Nonempty (Fin n)]
    (P : JarzynskiProtocol n) :
    ∑ m, ∑ k, forwardTransitionProb P m k = 1 := by
  unfold forwardTransitionProb
  -- Swap the order of summation.
  rw [Finset.sum_comm]
  -- ∑ k, ∑ m, (1/Z_0) * exp(-β E_0 k) * ‖W_{mk}‖²
  --   = (1/Z_0) * ∑ k, exp(-β E_0 k) * ∑ m, ‖W_{mk}‖²
  have h_inner : ∀ k,
      ∑ m, (1 / partitionFunction P.β P.H_0)
              * Real.exp (-P.β * P.E_0 k)
              * ‖P.transition m k‖^2
        = (1 / partitionFunction P.β P.H_0)
            * Real.exp (-P.β * P.E_0 k)
            * ∑ m, ‖P.transition m k‖^2 := by
    intro k
    rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun k _ => h_inner k)]
  -- Column-sum of |W|² is 1: ∑ m, |W_{mk}|² = 1.
  -- From star W · W = 1: (star W · W) k k = 1.
  have h_col_sum : ∀ k, ∑ m, ‖P.transition m k‖^2 = 1 := by
    intro k
    have hWW : star P.transition * P.transition = 1 := P.star_mul_transition
    have h_entry : (star P.transition * P.transition) k k
                 = (1 : Matrix (Fin n) (Fin n) ℂ) k k := by rw [hWW]
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h_entry
    -- (star W * W) k k = ∑ m, (star W) k m · W m k
    --                  = ∑ m, star (W m k) · W m k
    --                  = ∑ m, (‖W m k‖² : ℂ)
    have h_per_m : ∀ m, (star P.transition) k m * P.transition m k
                 = ((‖P.transition m k‖^2 : ℝ) : ℂ) := by
      intro m
      change star (P.transition m k) * P.transition m k = _
      rw [show (star (P.transition m k) : ℂ)
              = (starRingEnd ℂ) (P.transition m k) from rfl]
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [Finset.sum_congr rfl (fun m _ => h_per_m m)] at h_entry
    have h_cast : ((∑ m, ‖P.transition m k‖^2 : ℝ) : ℂ) = (1 : ℂ) := by
      rw [← h_entry]
      push_cast
      rfl
    exact_mod_cast h_cast
  rw [Finset.sum_congr rfl (fun k _ => by rw [h_col_sum k, mul_one])]
  -- Now ∑ k, (1/Z_0) * exp(-β E_0 k) = (1/Z_0) * ∑ k, exp(-β E_0 k)
  --                                  = (1/Z_0) * Z_0 = 1.
  rw [← Finset.mul_sum]
  have h_Z0 : ∑ k, Real.exp (-P.β * P.E_0 k) = partitionFunction P.β P.H_0 := by
    rw [partitionFunction_eq_sum_exp P.β P.H_0 P.H_0_isHerm]
    rfl
  rw [h_Z0]
  have hZ0_pos : 0 < partitionFunction P.β P.H_0 :=
    partitionFunction_pos_of_nonempty P.β P.H_0 P.H_0_isHerm
  field_simp

/-- **Reverse total probability is 1.**

    `∑_{m, k} P_R(m → k) = 1`.

    Sum over the FIRST index `m` (initial state of the reverse process)
    of `exp(-β E_1^m)/Z_1`, and over `k` (final state) of `|W_{mk}|²`,
    using the **row-sum** unitarity `∑_k |W_{mk}|² = 1` already proved
    in `QuantumJarzynski`. -/
theorem reverse_marginal_sum {n : ℕ} [Nonempty (Fin n)]
    (P : JarzynskiProtocol n) :
    ∑ m, ∑ k, reverseTransitionProb P m k = 1 := by
  unfold reverseTransitionProb
  -- For each m, factor exp(-β E_1 m)/Z_1 out of the inner sum.
  have h_inner : ∀ m,
      ∑ k, (1 / partitionFunction P.β P.H_1)
              * Real.exp (-P.β * P.E_1 m)
              * ‖P.transition m k‖^2
        = (1 / partitionFunction P.β P.H_1)
            * Real.exp (-P.β * P.E_1 m)
            * ∑ k, ‖P.transition m k‖^2 := by
    intro m
    rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun m _ => h_inner m)]
  -- Row sum is 1.
  have h_row : ∀ m, ∑ k, ‖P.transition m k‖^2 = 1 := P.row_sum_sq_transition
  rw [Finset.sum_congr rfl (fun m _ => by rw [h_row m, mul_one])]
  -- ∑ m, (1/Z_1) * exp(-β E_1 m) = (1/Z_1) * Z_1 = 1.
  rw [← Finset.mul_sum]
  have h_Z1 : ∑ m, Real.exp (-P.β * P.E_1 m) = partitionFunction P.β P.H_1 := by
    rw [partitionFunction_eq_sum_exp P.β P.H_1 P.H_1_isHerm]
    rfl
  rw [h_Z1]
  have hZ1_pos : 0 < partitionFunction P.β P.H_1 :=
    partitionFunction_pos_of_nonempty P.β P.H_1 P.H_1_isHerm
  field_simp

/-! ## 5. Crooks ⇒ Jarzynski -/

/-- **Algebraic step**: the Jarzynski summand expressed via the
    forward transition probability.

      `(1/Z_0) · exp(-β E_0^k) · |W_{mk}|² · exp(-β W_{mk})
         = P_F(k → m) · exp(-β W_{mk})`.

    This is true by definition; recorded as a named identity to keep
    the main proof readable. -/
private lemma jarzynski_summand_as_forward {n : ℕ}
    (P : JarzynskiProtocol n) (m k : Fin n) :
    (1 / partitionFunction P.β P.H_0)
        * Real.exp (-P.β * P.E_0 k)
        * ‖P.transition m k‖^2
        * Real.exp (-P.β * (P.E_1 m - P.E_0 k))
      = forwardTransitionProb P m k
          * Real.exp (-P.β * work P m k) := by
  unfold forwardTransitionProb work
  ring

/-- **Algebraic step**: `exp(-β W) · exp(β ΔF) · exp(β W) = exp(β ΔF)`
    and consequently `exp(-β W) = exp(-β ΔF) · exp(-β (W − ΔF))`. -/
private lemma exp_neg_W_eq {n : ℕ} (P : JarzynskiProtocol n) (m k : Fin n) :
    Real.exp (-P.β * work P m k)
      = Real.exp (-P.β * deltaF P)
          * Real.exp (-P.β * (work P m k - deltaF P)) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- **Per-transition Crooks rewritten for summation**:

      `P_F(k → m) · exp(-β W_{mk})  =  P_R(m → k) · exp(-β ΔF)` .

    Derived from `crooks_per_transition` by dividing both sides by
    `exp(β · ΔF) · exp(β · W)` (both positive).  This is the form
    used in the summation step. -/
theorem crooks_summation_form {n : ℕ} [Nonempty (Fin n)]
    (P : JarzynskiProtocol n) (m k : Fin n) :
    forwardTransitionProb P m k * Real.exp (-P.β * work P m k)
      = reverseTransitionProb P m k * Real.exp (-P.β * deltaF P) := by
  -- Start from P_F · exp(β ΔF) = P_R · exp(β W).
  have h := crooks_per_transition P m k
  -- Multiply both sides by exp(-β W) · exp(-β ΔF).
  have h_exp_pos_ΔF : 0 < Real.exp (P.β * deltaF P) := Real.exp_pos _
  have h_exp_pos_W : 0 < Real.exp (P.β * work P m k) := Real.exp_pos _
  have h_exp_neg_ΔF_mul :
      Real.exp (P.β * deltaF P) * Real.exp (-P.β * deltaF P) = 1 := by
    rw [← Real.exp_add]
    have : P.β * deltaF P + -P.β * deltaF P = 0 := by ring
    rw [this, Real.exp_zero]
  have h_exp_neg_W_mul :
      Real.exp (P.β * work P m k) * Real.exp (-P.β * work P m k) = 1 := by
    rw [← Real.exp_add]
    have : P.β * work P m k + -P.β * work P m k = 0 := by ring
    rw [this, Real.exp_zero]
  -- Apply h * (exp(-β W) * exp(-β ΔF)) to both sides.
  have h_mul : (forwardTransitionProb P m k * Real.exp (P.β * deltaF P))
                  * (Real.exp (-P.β * deltaF P) * Real.exp (-P.β * work P m k))
                = (reverseTransitionProb P m k * Real.exp (P.β * work P m k))
                  * (Real.exp (-P.β * deltaF P) * Real.exp (-P.β * work P m k)) := by
    rw [h]
  calc forwardTransitionProb P m k * Real.exp (-P.β * work P m k)
      = forwardTransitionProb P m k * Real.exp (-P.β * work P m k)
          * (Real.exp (P.β * deltaF P) * Real.exp (-P.β * deltaF P)) := by
            rw [h_exp_neg_ΔF_mul]; ring
    _ = (forwardTransitionProb P m k * Real.exp (P.β * deltaF P))
          * (Real.exp (-P.β * deltaF P) * Real.exp (-P.β * work P m k)) := by ring
    _ = (reverseTransitionProb P m k * Real.exp (P.β * work P m k))
          * (Real.exp (-P.β * deltaF P) * Real.exp (-P.β * work P m k)) := h_mul
    _ = reverseTransitionProb P m k * Real.exp (-P.β * deltaF P)
          * (Real.exp (P.β * work P m k) * Real.exp (-P.β * work P m k)) := by ring
    _ = reverseTransitionProb P m k * Real.exp (-P.β * deltaF P) := by
          rw [h_exp_neg_W_mul]; ring

/-- **CROOKS ⇒ JARZYNSKI.**

    Summing the per-transition Crooks identity (in its summation form
    `P_F · exp(-β W) = P_R · exp(-β ΔF)`) over all `(m, k)` gives
    `jarzynskiAverage = exp(-β ΔF) · (reverse total probability) =
    exp(-β ΔF) · 1 = exp(-β ΔF)`.

    This is the structural derivation of the Jarzynski equality from
    the more fundamental Crooks relation.  It does not use the
    `quantum_jarzynski` theorem directly; the only Jarzynski-side
    ingredient is the per-summand cancellation (which is internalised
    in `crooks_summation_form` via `crooks_per_transition`). -/
theorem crooks_implies_jarzynski {n : ℕ} [Nonempty (Fin n)]
    (P : JarzynskiProtocol n) :
    jarzynskiAverage P
      = Real.exp (-P.β * (freeEnergy P.β P.H_1 - freeEnergy P.β P.H_0)) := by
  -- Step 1: rewrite jarzynskiAverage as ∑_{m,k} P_F(k → m) · exp(-β W).
  have h_avg_as_PF :
      jarzynskiAverage P
        = ∑ m, ∑ k, forwardTransitionProb P m k
                      * Real.exp (-P.β * work P m k) := by
    unfold jarzynskiAverage
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    -- Goal: (1/Z_0) * (exp(-β E_0 k) * ‖W‖² * exp(-β (E_1 m - E_0 k)))
    --       = forwardTransitionProb P m k * exp(-β work P m k)
    have h := jarzynski_summand_as_forward P m k
    linarith [h]
  rw [h_avg_as_PF]
  -- Step 2: replace P_F · exp(-β W) with P_R · exp(-β ΔF) (Crooks form).
  have h_crooks : ∀ m k,
      forwardTransitionProb P m k * Real.exp (-P.β * work P m k)
        = reverseTransitionProb P m k * Real.exp (-P.β * deltaF P) :=
    fun m k => crooks_summation_form P m k
  rw [Finset.sum_congr rfl (fun m _ =>
        Finset.sum_congr rfl (fun k _ => h_crooks m k))]
  -- Step 3: factor exp(-β ΔF) out of both sums.
  have h_factor :
      ∑ m, ∑ k, reverseTransitionProb P m k * Real.exp (-P.β * deltaF P)
        = (∑ m, ∑ k, reverseTransitionProb P m k)
            * Real.exp (-P.β * deltaF P) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.sum_mul]
  rw [h_factor]
  -- Step 4: ∑_{m,k} P_R(m → k) = 1 (reverse marginal).
  rw [reverse_marginal_sum P, one_mul]
  -- Step 5: deltaF = freeEnergy 1 - freeEnergy 0.
  rfl

/-! ## 6. Corollaries -/

/-- **Crooks ⇒ partition-function form of Jarzynski.**  Combining
    `crooks_implies_jarzynski` with the free-energy bridge gives
    `jarzynskiAverage = Z_1 / Z_0`. -/
theorem crooks_implies_jarzynski_partition {n : ℕ} [Nonempty (Fin n)]
    (P : JarzynskiProtocol n) :
    jarzynskiAverage P
      = partitionFunction P.β P.H_1 / partitionFunction P.β P.H_0 := by
  rw [crooks_implies_jarzynski P]
  have hβ : P.β ≠ 0 := ne_of_gt P.β_pos
  have hZ0 : 0 < partitionFunction P.β P.H_0 :=
    partitionFunction_pos_of_nonempty P.β P.H_0 P.H_0_isHerm
  have hZ1 : 0 < partitionFunction P.β P.H_1 :=
    partitionFunction_pos_of_nonempty P.β P.H_1 P.H_1_isHerm
  exact exp_neg_beta_delta_F_eq_Z_ratio P.β hβ P.H_0 P.H_1 hZ0 hZ1

/-- **Trivial case `H_0 = H_1` (no driving).**  In the trivial protocol
    `H_0 = H_1`, ΔF = 0 and the work `W_{mn} = E^1_m − E^0_n` equals
    `E^1_m − E^1_n` (a difference of the SAME spectrum).  Crooks then
    becomes `P_F · 1 = P_R · exp(β W)`, i.e. detailed balance for the
    unitary `U_τ` against the thermal state at H_1 = H_0. -/
theorem crooks_trivial {n : ℕ} [Nonempty (Fin n)]
    (P : JarzynskiProtocol n) (h_eq : P.H_0 = P.H_1) (i j : Fin n) :
    forwardTransitionProb P i j
      = reverseTransitionProb P i j * Real.exp (P.β * work P i j) := by
  have h := crooks_per_transition P i j
  have h_ΔF_zero : deltaF P = 0 := by
    unfold deltaF
    rw [h_eq]
    ring
  rw [h_ΔF_zero] at h
  simp at h
  linarith

/-! ## 7. Axiom audit (manual: run `#print axioms` after build). -/

-- Uncomment to audit:
-- #print axioms crooks_per_transition
-- #print axioms crooks_per_transition_ratio
-- #print axioms forward_marginal_sum
-- #print axioms reverse_marginal_sum
-- #print axioms crooks_summation_form
-- #print axioms crooks_implies_jarzynski
-- #print axioms crooks_implies_jarzynski_partition
-- #print axioms crooks_trivial
-- VERIFIED 2026-06-02: every theorem above ⟹
--   [propext, Classical.choice, Quot.sound]  (only).
-- No `sorry`, no custom `axiom`.

end UnifiedTheory.LayerB.QuantumCrooks
