/- Operator-trace forms of the twisted law, and a finite-time error bound, on top of `TwistedNeutral`.

`TwistedNeutral` already has the law `chainLaw T n β` on `ZMod T × (ZMod n)³` for every `T` and `n`, its
identification with the 4D law at `T = n = 2l` (`toChain_law`), the transfer form `schwinger`, the trace
`chainZ_trace`, the kernel two-point function, reflection positivity at even `T`, and the limit `T → ∞`.
None of that is reproved here. This file adds:

* Operator traces with observables inserted. Slice moments are `Tr ∏ₜ (M_{Fₜ} T)` in any Hilbert basis
  (`trace_orderedProduct`), so expectations are ratios of traces, on `chainLaw` for `T ≥ 2`
  (`expectation_trace`, `trace_two_point`) and on the actual law at `T = L = 2n` (`law_expectation_trace`,
  `law_two_point`). The trace of a product of two kernel operators needs no symmetry (`trace_operator_mul`).
* A bound at finite `T` with an explicit error (`two_point_finite`, `connected_finite`). The error is the
  excess `excess n β r = Z(r)/‖T‖^r - 1`, the trace of `T^r` off the vacuum in units of `‖T‖^r`. It is
  defined, not assumed. `connected_of_targetAGap` and `law_connected_of_targetAGap` are conditional on
  the open `TargetAGap`, of which they use only the contraction half. The second states the result for
  `TwistedLocalization.twistedLaw` at `T = L`.
* A proved limit on that route. For every fixed `n` and `r`, `excess n β r` does not stay below `1` as
  `β → ∞` (`excess_not_small`), because `flux_gap_vanishes` makes a flux-odd level nearly degenerate. There
  the error of `two_point_finite` is within `1 - ε` of the trivial bound `2 ‖A‖ ‖B‖`, and
  `connected_finite` is weaker than trivial. Using them uniformly in the coupling at fixed time extent
  needs a sector-resolved replacement, which is not done.

Not proved: any bound on `excess` uniform in `n`, or any upper bound on it other than `T → ∞` at fixed `n`
(`excess_tendsto`, rate uncontrolled); how the threshold in `flux_gap_vanishes` compares with the
trajectories of `TargetAGap`; the gap; `Tr T` at `T = 1`; traces with temporal-link observables (at law
level they are covered by `toChain_law`); reflection positivity at odd `T`; the twisted Gaussian covariance. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedNeutral
import UnifiedTheory.Clay.YangMills.Twisted.TwistedLocalization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedTraceLaw
noncomputable section
open MeasureTheory Filter CompactKernelOperator
open TwistedNeutral (compK compK_apply chainK operator_compK insK insK_apply insK_one trace_comp countable_of_basis
  Chain chainRef chainAction chainAction_continuous chainLaw chainZ schwinger chainZ_trace chainZ_pos
  chainZ_spectrum chainZ_dominance chainLaw_integral chainLaw_preserved tendsto_of_geometric toChain toChain_law)
open scoped InnerProductSpace ComplexConjugate ENNReal Topology

/-! ### The trace of a product of kernels, with no symmetry -/

section Kernels
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ] [μ.WeaklyRegular]

/-- The transposed kernel. -/
def transposeK (K : C(X × X, ℝ)) : C(X × X, ℝ) :=
  ⟨fun p => K (p.2, p.1), K.continuous.comp continuous_swap⟩

theorem transposeK_apply (K : C(X × X, ℝ)) (u v : X) : transposeK K (u, v) = K (v, u) := rfl

theorem transposeK_transposeK (K : C(X × X, ℝ)) : transposeK (transposeK K) = K := by
  ext ⟨u, v⟩
  rfl

theorem operator_toLp (K : C(X × X, ℝ)) (f : C(X, ℂ)) :
    operator μ K (ContinuousMap.toLp 2 μ ℂ f) =
      ContinuousMap.toLp 2 μ ℂ (smoothing μ K (ContinuousMap.toLp 2 μ ℂ f)) := rfl

/-- The adjoint of a kernel operator on continuous tests. -/
theorem operator_inner_continuous (K : C(X × X, ℝ)) (f g : C(X, ℂ)) :
    inner ℂ (operator μ K (ContinuousMap.toLp 2 μ ℂ f)) (ContinuousMap.toLp 2 μ ℂ g) =
      inner ℂ (ContinuousMap.toLp 2 μ ℂ f)
        (operator μ (transposeK K) (ContinuousMap.toLp 2 μ ℂ g)) := by
  rw [operator_toLp, operator_toLp]
  rw [MeasureTheory.ContinuousMap.inner_toLp, MeasureTheory.ContinuousMap.inner_toLp]
  simp_rw [smoothing_continuous_input, ← integral_conj, ← integral_const_mul, ← integral_mul_const]
  have hi : Integrable (fun xy : X × X => g xy.1 * conj ((K xy : ℂ) * f xy.2)) (μ.prod μ) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    fun_prop
  rw [integral_integral_swap hi]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [map_mul, Complex.conj_ofReal, transposeK_apply]
  ring

/-- The Hilbert adjoint of a kernel operator has the transposed kernel. -/
theorem operator_inner (K : C(X × X, ℝ)) (f g : Hilbert μ) :
    inner ℂ (operator μ K f) g = inner ℂ f (operator μ (transposeK K) g) := by
  apply (ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).induction_on₂
    (p := fun f g => inner ℂ (operator μ K f) g = inner ℂ f (operator μ (transposeK K) g))
  · apply isClosed_eq
    · exact ((operator μ K).continuous.comp continuous_fst).inner continuous_snd
    · exact continuous_fst.inner ((operator μ (transposeK K)).continuous.comp continuous_snd)
  · exact operator_inner_continuous μ K


/-- **The trace of a product of two kernel operators.** `TwistedNeutral.trace_comp` with the adjoint moved
over. No positivity or symmetry is used. -/
theorem trace_operator_mul (A B : C(X × X, ℝ)) {ι : Type*} (b : HilbertBasis ι ℂ (Hilbert μ)) :
    HasSum (fun i => inner ℂ (b i) ((operator μ A * operator μ B) (b i)))
      ((∫ u, compK μ A B (u, u) ∂μ : ℝ) : ℂ) := by
  haveI := countable_of_basis μ b
  have h := trace_comp μ b B (transposeK A)
  have hterm (i : ι) : inner ℂ (operator μ (transposeK A) (b i)) (operator μ B (b i)) =
      inner ℂ (b i) ((operator μ A * operator μ B) (b i)) := by
    have h1 := operator_inner μ (transposeK A) (b i) (operator μ B (b i))
    rw [transposeK_transposeK] at h1
    exact h1
  have hval : (∫ x, ∫ w, B (x, w) * transposeK A (x, w) ∂μ ∂μ) = ∫ u, compK μ A B (u, u) ∂μ := by
    simp_rw [compK_apply, transposeK_apply]
    have hi : Integrable (Function.uncurry fun x w => B (x, w) * A (w, x)) (μ.prod μ) := by
      unfold Function.uncurry
      exact Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)
    rw [integral_integral_swap hi]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    exact mul_comm _ _
  rw [hval] at h
  simpa only [hterm] using h

/-- A chain of kernels gives the time-ordered product of operators. -/
theorem operator_chainK (K : ℕ → C(X × X, ℝ)) (m : ℕ) :
    operator μ (chainK μ K m) = ((List.range (m + 1)).map fun k => operator μ (K k)).prod := by
  induction m with
  | zero => simp [chainK]
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ← ih]
    simp only [chainK, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [operator_compK]
    rfl

/-- The trace of a chain of at least two kernels. -/
theorem trace_chainK (m : ℕ) (K : ℕ → C(X × X, ℝ)) {ι : Type*} (b : HilbertBasis ι ℂ (Hilbert μ)) :
    HasSum (fun i => inner ℂ (b i) (((List.range (m + 2)).map fun k => operator μ (K k)).prod (b i)))
      ((∫ u, chainK μ K (m + 1) (u, u) ∂μ : ℝ) : ℂ) := by
  have h := trace_operator_mul μ (chainK μ K m) (K (m + 1)) b
  rw [← operator_chainK μ K (m + 1)]
  simp only [chainK]
  rw [operator_compK]
  exact h


/-! ### Multiplication operators -/

theorem mul_memLp (F : C(X, ℝ)) (f : Hilbert μ) : MemLp (fun u => (F u : ℂ) * f u) 2 μ := by
  refine (Lp.memLp f).of_le_mul (c := ‖F‖) ?_ (Eventually.of_forall fun u => ?_)
  · exact (Complex.continuous_ofReal.comp F.continuous).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f)
  · rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (F.norm_coe_le_norm u) (norm_nonneg _)

/-- Multiplication by a continuous real observable, as an operator on `L²`. -/
def mulOp (F : C(X, ℝ)) : Hilbert μ →L[ℂ] Hilbert μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (mul_memLp μ F f).toLp _
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [(mul_memLp μ F (f + g)).coeFn_toLp, Lp.coeFn_add f g,
          Lp.coeFn_add ((mul_memLp μ F f).toLp _) ((mul_memLp μ F g).toLp _),
          (mul_memLp μ F f).coeFn_toLp, (mul_memLp μ F g).coeFn_toLp] with u h1 h2 h3 h4 h5
        rw [h1, h3, Pi.add_apply, h4, h5, h2, Pi.add_apply]
        ring
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [(mul_memLp μ F (c • f)).coeFn_toLp, Lp.coeFn_smul c f,
          Lp.coeFn_smul c ((mul_memLp μ F f).toLp _), (mul_memLp μ F f).coeFn_toLp]
          with u h1 h2 h3 h4
        simp only [RingHom.id_apply]
        rw [h1, h3, Pi.smul_apply, h4, h2, Pi.smul_apply]
        simp only [smul_eq_mul]
        ring } ‖F‖ fun f => by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [(mul_memLp μ F f).coeFn_toLp] with u hu
    change ‖(mul_memLp μ F f).toLp _ u‖ ≤ _
    rw [hu, norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (F.norm_coe_le_norm u) (norm_nonneg _)

theorem mulOp_ae (F : C(X, ℝ)) (f : Hilbert μ) :
    mulOp μ F f =ᵐ[μ] fun u => (F u : ℂ) * f u :=
  (mul_memLp μ F f).coeFn_toLp


theorem operator_insK (F : C(X, ℝ)) (K : C(X × X, ℝ)) :
    operator μ (insK F K) = mulOp μ F * operator μ K := by
  refine ContinuousLinearMap.ext fun f => ?_
  apply Lp.ext
  change _ =ᵐ[μ] (mulOp μ F (operator μ K f) : X → ℂ)
  filter_upwards [operator_integral μ (insK F K) f, mulOp_ae μ F (operator μ K f),
    operator_integral μ K f] with u h1 h2 h3
  rw [h1, h2, h3, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [insK_apply]
  push_cast
  ring


theorem mulOp_norm_le (F : C(X, ℝ)) (f : Hilbert μ) : ‖mulOp μ F f‖ ≤ ‖F‖ * ‖f‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [mulOp_ae μ F f] with u hu
  rw [hu, norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_right (F.norm_coe_le_norm u) (norm_nonneg _)

/-- Multiplication by a real observable is symmetric. -/
theorem mulOp_symm (F : C(X, ℝ)) (f g : Hilbert μ) :
    inner ℂ (mulOp μ F f) g = inner ℂ f (mulOp μ F g) := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [mulOp_ae μ F f, mulOp_ae μ F g] with u h1 h2
  rw [h1, h2]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

theorem mulOp_one (f : Hilbert μ) : mulOp μ (1 : C(X, ℝ)) f = f := by
  apply Lp.ext
  filter_upwards [mulOp_ae μ 1 f] with u hu
  rw [hu]
  simp


/-! ### Blocks of a time-ordered product -/

section Blocks
variable {M : Type*} [Monoid M]

theorem prod_range_add (G : ℕ → M) (a b : ℕ) :
    ((List.range (a + b)).map G).prod =
      ((List.range a).map G).prod * ((List.range b).map fun k => G (a + k)).prod := by
  rw [List.range_add, List.map_append, List.prod_append, List.map_map]
  rfl

theorem prod_range_const (G : ℕ → M) (P : M) (m : ℕ) (h : ∀ k < m, G k = P) :
    ((List.range m).map G).prod = P ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih fun k hk => h k (by omega)]
    simp [h m (by omega), pow_succ]

end Blocks

end Kernels

/-! ### Spectral lemmas for a symmetric operator -/

section Spectral
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (T : H →L[ℂ] H) (Ω : H) (τ ρ : ℝ)

theorem pow_symm (hsym : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y)) (k : ℕ) (x y : H) :
    inner ℂ ((T ^ k) x) y = inner ℂ x ((T ^ k) y) := by
  induction k generalizing x y with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    change inner ℂ ((T ^ k) (T x)) y = inner ℂ x ((T ^ k) (T y))
    rw [ih, hsym]
    rw [show (T ^ k) (T y) = T ((T ^ k) y) by
      rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← pow_succ, pow_succ']]

theorem pow_top (htop : T Ω = τ • Ω) (k : ℕ) : (T ^ k) Ω = (τ ^ k) • Ω := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    change (T ^ k) (T Ω) = _
    rw [htop, RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, ih, ← RCLike.real_smul_eq_coe_smul (K := ℂ),
      smul_smul, pow_succ]
    ring_nf

theorem orth_step (hsym : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y)) (htop : T Ω = τ • Ω) (f : H)
    (hf : inner ℂ Ω f = 0) : inner ℂ Ω (T f) = 0 := by
  rw [← hsym, htop, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, hf, mul_zero]

/-- Iterated contraction on an invariant set inside the complement of the top vector. -/
theorem pow_contract (P : H → Prop) (hPT : ∀ f, P f → P (T f)) (hρ0 : 0 ≤ ρ) (hτ : 0 ≤ τ)
    (hsym : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y)) (htop : T Ω = τ • Ω)
    (hρ : ∀ f, P f → inner ℂ Ω f = 0 → ‖T f‖ ≤ ρ * τ * ‖f‖) (k : ℕ) (f : H) (hP : P f)
    (hf : inner ℂ Ω f = 0) : inner ℂ Ω ((T ^ k) f) = 0 ∧ P ((T ^ k) f) ∧
      ‖(T ^ k) f‖ ≤ (ρ * τ) ^ k * ‖f‖ := by
  induction k with
  | zero => simpa using ⟨hf, hP⟩
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [pow_succ']
    refine ⟨orth_step T Ω τ hsym htop _ h1, hPT _ h2, ?_⟩
    change ‖T ((T ^ k) f)‖ ≤ _
    calc ‖T ((T ^ k) f)‖ ≤ ρ * τ * ‖(T ^ k) f‖ := hρ _ h2 h1
      _ ≤ ρ * τ * ((ρ * τ) ^ k * ‖f‖) := mul_le_mul_of_nonneg_left h3 (mul_nonneg hρ0 hτ)
      _ = (ρ * τ) ^ (k + 1) * ‖f‖ := by ring

/-- **Clustering from a gap.** Only the second vector has to lie in the set where the contraction is
known. -/
theorem cluster_bound (P : H → Prop) (hPT : ∀ f, P f → P (T f)) (hρ0 : 0 ≤ ρ) (hτ : 0 < τ)
    (hΩ : ‖Ω‖ = 1) (hsym : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y)) (htop : T Ω = τ • Ω)
    (hρ : ∀ f, P f → inner ℂ Ω f = 0 → ‖T f‖ ≤ ρ * τ * ‖f‖) (u v : H)
    (hv : P (v - inner ℂ Ω v • Ω)) (k : ℕ) :
    ‖inner ℂ u ((T ^ k) v) / ((τ ^ k : ℝ) : ℂ) - inner ℂ u Ω * inner ℂ Ω v‖ ≤ ρ ^ k * (‖u‖ * ‖v‖) := by
  have hself : inner ℂ Ω Ω = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hΩ]
    simp
  set w := v - inner ℂ Ω v • Ω with hw
  have horth : inner ℂ Ω w = 0 := by
    rw [hw, inner_sub_right, inner_smul_right, hself, mul_one, sub_self]
  obtain ⟨-, -, hc⟩ := pow_contract T Ω τ ρ P hPT hρ0 hτ.le hsym htop hρ k w hv horth
  have hwn : ‖w‖ ≤ ‖v‖ := by
    have hpy : ‖v‖ ^ 2 = ‖w‖ ^ 2 + ‖inner ℂ Ω v • Ω‖ ^ 2 := by
      have hvw : v = w + inner ℂ Ω v • Ω := by rw [hw]; abel
      have horth1 : inner ℂ w Ω = (0 : ℂ) := by
        rw [← inner_conj_symm, horth]
        simp
      have horth2 : inner ℂ w (inner ℂ Ω v • Ω) = (0 : ℂ) := by
        rw [inner_smul_right, horth1, mul_zero]
      conv_lhs => rw [hvw]
      have := norm_add_sq (𝕜 := ℂ) w (inner ℂ Ω v • Ω)
      rw [horth2] at this
      simpa using this
    nlinarith [norm_nonneg w, norm_nonneg v, sq_nonneg ‖inner ℂ Ω v • Ω‖]
  have hsplit : (T ^ k) v = (T ^ k) w + ((τ ^ k : ℝ) : ℂ) • (inner ℂ Ω v • Ω) := by
    have hvw : v = w + inner ℂ Ω v • Ω := by rw [hw]; abel
    conv_lhs => rw [hvw]
    rw [map_add, map_smul, pow_top T Ω τ htop, smul_comm, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have hpow : 0 < τ ^ k := pow_pos hτ k
  have hpowc : ((τ ^ k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpow.ne'
  have heq : inner ℂ u ((T ^ k) v) / ((τ ^ k : ℝ) : ℂ) - inner ℂ u Ω * inner ℂ Ω v =
      inner ℂ u ((T ^ k) w) / ((τ ^ k : ℝ) : ℂ) := by
    rw [hsplit, inner_add_right, inner_smul_right, inner_smul_right]
    field_simp
    ring
  rw [heq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpow,
    div_le_iff₀ hpow]
  calc ‖inner ℂ u ((T ^ k) w)‖ ≤ ‖u‖ * ‖(T ^ k) w‖ := norm_inner_le_norm _ _
    _ ≤ ‖u‖ * ((ρ * τ) ^ k * ‖w‖) := mul_le_mul_of_nonneg_left hc (norm_nonneg _)
    _ ≤ ‖u‖ * ((ρ * τ) ^ k * ‖v‖) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwn ?_) (norm_nonneg _)
        exact pow_nonneg (mul_nonneg hρ0 hτ.le) k
    _ = ρ ^ k * (‖u‖ * ‖v‖) * τ ^ k := by
        rw [mul_pow]
        ring

/-- Powers of a positive operator have nonnegative diagonal. -/
theorem inner_pow_nonneg (hpos : T.IsPositive) (k : ℕ) (x : H) :
    0 ≤ (inner ℂ x ((T ^ k) x) : ℂ).re := by
  have hsym : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y) := hpos.isSymmetric
  induction k using Nat.twoStepInduction generalizing x with
  | zero =>
    rw [pow_zero]
    exact inner_self_nonneg (𝕜 := ℂ)
  | one =>
    have h := hpos.2 x
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, ← inner_conj_symm, RCLike.conj_re] at h
    simpa using h
  | more k ih _ =>
    have h : inner ℂ x ((T ^ (k + 2)) x) = inner ℂ (T x) ((T ^ k) (T x)) := by
      rw [hsym]
      rw [show (T ^ (k + 2)) x = T ((T ^ k) (T x)) by
        rw [pow_succ', pow_succ]
        rfl]
    rw [h]
    exact ih (T x)

theorem opNorm_pow_le (k : ℕ) : ‖T ^ k‖ ≤ ‖T‖ ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))


/-- **A trace in an eigenbasis is its vacuum term plus the off-vacuum trace.** -/
theorem trace_eigenbasis {w : Type*} (b : HilbertBasis w ℂ H) (lam : w → ℝ)
    (heig : ∀ k, T (b k) = lam k • b k) (hlam0 : ∀ k, 0 ≤ lam k) (k₀ : w) (c : ℂ) (hc : ‖c‖ = 1)
    (hb : b k₀ = c • Ω) (Y : H →L[ℂ] H) (r : ℕ) (a : ℂ)
    (ha : HasSum (fun k => inner ℂ (b k) ((Y * T ^ r) (b k))) a) (z : ℝ)
    (hz : HasSum (fun k => lam k ^ r) z) :
    ‖a - ((lam k₀ ^ r : ℝ) : ℂ) * inner ℂ Ω (Y Ω)‖ ≤ ‖Y‖ * (z - lam k₀ ^ r) := by
  classical
  have hval (k : w) : inner ℂ (b k) ((Y * T ^ r) (b k)) =
      ((lam k ^ r : ℝ) : ℂ) * inner ℂ (b k) (Y (b k)) := by
    change inner ℂ (b k) (Y ((T ^ r) (b k))) = _
    rw [pow_top T (b k) (lam k) (heig k) r, RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul,
      inner_smul_right]
    rfl
  have h0 : inner ℂ (b k₀) (Y (b k₀)) = inner ℂ Ω (Y Ω) := by
    rw [hb, map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul', hc]
    simp
  have hu := ha.update k₀ 0
  have hg := (hz.update k₀ 0).mul_left ‖Y‖
  have hb' := hu.norm_le_of_bounded hg (fun i => ?_)
  · have e1 : (0 : ℂ) - inner ℂ (b k₀) ((Y * T ^ r) (b k₀)) + a =
        a - ((lam k₀ ^ r : ℝ) : ℂ) * inner ℂ Ω (Y Ω) := by
      rw [hval, h0]
      ring
    have e2 : ‖Y‖ * ((0 : ℝ) - lam k₀ ^ r + z) = ‖Y‖ * (z - lam k₀ ^ r) := by ring
    rw [e1, e2] at hb'
    exact hb'
  · by_cases hi : i = k₀
    · subst hi
      simp
    · rw [Function.update_of_ne hi, Function.update_of_ne hi, hval, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hlam0 i) r), mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (hlam0 i) r)
      calc ‖inner ℂ (b i) (Y (b i))‖ ≤ ‖b i‖ * ‖Y (b i)‖ := norm_inner_le_norm _ _
        _ ≤ ‖b i‖ * (‖Y‖ * ‖b i‖) := mul_le_mul_of_nonneg_left (Y.le_opNorm _) (norm_nonneg _)
        _ = ‖Y‖ := by rw [b.orthonormal.1 i]; ring

/-- Two orthonormal vectors extend to a Hilbert basis. -/
theorem exists_basis_pair (e : H) (hΩ : ‖Ω‖ = 1) (he : ‖e‖ = 1) (h0 : inner ℂ Ω e = (0 : ℂ)) :
    ∃ (u : Set H) (b : HilbertBasis u ℂ H) (i₀ i₁ : u), i₀ ≠ i₁ ∧ b i₀ = Ω ∧ b i₁ = e := by
  classical
  have hne : Ω ≠ e := by
    rintro rfl
    rw [inner_self_eq_norm_sq_to_K, hΩ] at h0
    simp at h0
  have h0' : inner ℂ e Ω = (0 : ℂ) := by rw [← inner_conj_symm, h0]; simp
  have hO : Orthonormal ℂ ((↑) : ({Ω, e} : Set H) → H) := by
    rw [orthonormal_subtype_iff_ite]
    intro a ha c hc
    rcases Set.mem_insert_iff.mp ha with rfl | ha'
    · rcases Set.mem_insert_iff.mp hc with rfl | hc'
      · simp [inner_self_eq_norm_sq_to_K, hΩ]
      · rw [Set.mem_singleton_iff.mp hc', if_neg hne, h0]
    · rw [Set.mem_singleton_iff.mp ha']
      rcases Set.mem_insert_iff.mp hc with rfl | hc'
      · rw [if_neg hne.symm, h0']
      · rw [Set.mem_singleton_iff.mp hc']
        simp [inner_self_eq_norm_sq_to_K, he]
  obtain ⟨u, b, hsub, hb⟩ := hO.exists_hilbertBasis_extension
  refine ⟨u, b, ⟨Ω, hsub (Set.mem_insert _ _)⟩, ⟨e, hsub (Set.mem_insert_of_mem _ rfl)⟩, ?_, ?_, ?_⟩
  · intro h
    exact hne (congrArg Subtype.val h)
  · rw [hb]
  · rw [hb]

/-- Log-convexity of `k ↦ ‖Tᵏ e‖`: a lower bound on one step propagates to every step. -/
theorem norm_pow_step (hsym : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y)) (θ : ℝ) (e : H)
    (h1 : θ * ‖e‖ ≤ ‖T e‖) (a : ℕ) : θ * ‖(T ^ a) e‖ ≤ ‖(T ^ (a + 1)) e‖ := by
  induction a with
  | zero => simpa using h1
  | succ a ih =>
    set x := ‖(T ^ a) e‖ with hx
    set y := ‖(T ^ (a + 1)) e‖ with hy
    set z := ‖(T ^ (a + 1 + 1)) e‖ with hz
    have hx0 : 0 ≤ x := norm_nonneg _
    have hy0 : 0 ≤ y := norm_nonneg _
    have hz0 : 0 ≤ z := norm_nonneg _
    have hcs : y ^ 2 ≤ x * z := by
      have hstep (k : ℕ) : (T ^ (k + 1)) e = T ((T ^ k) e) := by
        rw [pow_succ']
        rfl
      have h2 : ((y ^ 2 : ℝ) : ℂ) = inner ℂ ((T ^ a) e) ((T ^ (a + 1 + 1)) e) := by
        have h3 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ((T ^ (a + 1)) e)
        rw [hstep a] at h3
        nth_rewrite 1 [hsym] at h3
        rw [← hstep a, ← hstep (a + 1)] at h3
        rw [h3, hy]
        simp [hstep]
      have h4 : ‖((y ^ 2 : ℝ) : ℂ)‖ = y ^ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [← h4, h2]
      exact norm_inner_le_norm _ _
    rcases hy0.eq_or_lt with hy1 | hy1
    · rw [← hy1, mul_zero]
      exact hz0
    · have hxz : 0 < x * z := lt_of_lt_of_le (by positivity) hcs
      have hxpos : 0 < x := by
        refine lt_of_le_of_ne hx0 fun h => ?_
        rw [← h, zero_mul] at hxz
        exact lt_irrefl _ hxz
      by_contra hcon
      push_neg at hcon
      nlinarith [mul_lt_mul_of_pos_left hcon hxpos]

/-- The lower bound for the iterates. -/
theorem norm_pow_lower (hsym : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y)) (θ : ℝ) (hθ : 0 ≤ θ) (e : H)
    (h1 : θ * ‖e‖ ≤ ‖T e‖) (a : ℕ) : θ ^ a * ‖e‖ ≤ ‖(T ^ a) e‖ := by
  induction a with
  | zero => simp
  | succ a ih =>
    calc θ ^ (a + 1) * ‖e‖ = θ * (θ ^ a * ‖e‖) := by ring
      _ ≤ θ * ‖(T ^ a) e‖ := mul_le_mul_of_nonneg_left ih hθ
      _ ≤ _ := norm_pow_step T hsym θ e h1 a

end Spectral

open WilsonTimeSlab RegulatedGauge PeriodicLattice4 TwistedTransfer
open WilsonSingleLinkStaples (character)

local notation "Q" => WilsonSlabOperator.Q
local notation "Slice" => WilsonSlabOperator.Slice
local notation "sliceHaar" => WilsonSlabOperator.measure

/-! ### Slice moments as operator traces -/

section Traces
variable {T n : ℕ} [NeZero T] [NeZero n]

/-- The unnormalized moment of slice observables under `TwistedNeutral.chainLaw`. -/
def moment (T n : ℕ) [NeZero T] [NeZero n] (β : ℝ) (F : ZMod T → C(Slice n, ℝ)) : ℝ :=
  ∫ c, (∏ t, F t (c.1 t)) * Real.exp (-chainAction T n β c) ∂chainRef T n

/-- The time-ordered product of the observables and the transfer operator. -/
def orderedProduct (T n : ℕ) [NeZero T] [NeZero n] (β : ℝ) (F : ZMod T → C(Slice n, ℝ)) :
    WilsonSlabOperator.Hilbert n →L[ℂ] WilsonSlabOperator.Hilbert n :=
  ((List.range T).map fun k : ℕ => mulOp (sliceHaar n) (F (k : ZMod T)) * transfer n β).prod

/-- **The operator trace of a time-ordered product is the moment of the slice observables.** Valid
in any Hilbert basis, for every coupling and every time extent `T ≥ 2`. -/
theorem trace_orderedProduct (hT : 2 ≤ T) (β : ℝ) (F : ZMod T → C(Slice n, ℝ)) {ι : Type*}
    (b : HilbertBasis ι ℂ (WilsonSlabOperator.Hilbert n)) :
    HasSum (fun i => inner ℂ (b i) (orderedProduct T n β F (b i))) ((moment T n β F : ℝ) : ℂ) := by
  obtain ⟨m, rfl⟩ : ∃ m, T = m + 2 := ⟨T - 2, by omega⟩
  have h := trace_chainK (sliceHaar n) m
    (fun k : ℕ => insK (F (k : ZMod (m + 2))) (twistedKernel n β)) b
  simp only [operator_insK] at h
  unfold moment
  rw [schwinger (m + 2) n F β]
  exact h

/-- `TwistedNeutral.chainZ_trace` for an arbitrary index type and `T ≥ 2`. -/
theorem trace_transfer_pow (hT : 2 ≤ T) (β : ℝ) {ι : Type*}
    (b : HilbertBasis ι ℂ (WilsonSlabOperator.Hilbert n)) :
    HasSum (fun i => inner ℂ (b i) ((transfer n β ^ T) (b i))) ((chainZ T n β : ℝ) : ℂ) := by
  obtain ⟨m, rfl⟩ : ∃ m, T = m + 2 := ⟨T - 2, by omega⟩
  haveI := countable_of_basis (sliceHaar n) b
  exact chainZ_trace n b β m

/-- Slice expectations under `chainLaw` are moments over the partition function. -/
theorem expectation_eq (β : ℝ) (F : ZMod T → C(Slice n, ℝ)) :
    ∫ c, ∏ t, F t (c.1 t) ∂chainLaw T n β = moment T n β F / chainZ T n β :=
  chainLaw_integral n β T _

/-- **Slice expectations are ratios of operator traces.** -/
theorem expectation_trace (hT : 2 ≤ T) (β : ℝ) (F : ZMod T → C(Slice n, ℝ)) {ι : Type*}
    (b : HilbertBasis ι ℂ (WilsonSlabOperator.Hilbert n)) :
    ((∫ c, ∏ t, F t (c.1 t) ∂chainLaw T n β : ℝ) : ℂ) =
      (∑' i, inner ℂ (b i) (orderedProduct T n β F (b i))) /
        ∑' i, inner ℂ (b i) ((transfer n β ^ T) (b i)) := by
  rw [(trace_transfer_pow hT β b).tsum_eq, (trace_orderedProduct hT β F b).tsum_eq, expectation_eq]
  push_cast
  rfl

/-- The observable `A` at time `0`, `B` at time `s`, and nothing elsewhere. -/
def twoObs (T n : ℕ) (A B : C(Slice n, ℝ)) (s : ℕ) (t : ZMod T) : C(Slice n, ℝ) := by
  classical
  exact if t = 0 then A else if t = (s : ZMod T) then B else 1

omit [NeZero n] in
theorem cast_eq_iff {k j : ℕ} (hk : k < T) (hj : j < T) : ((k : ZMod T) = (j : ZMod T)) ↔ k = j := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hj]

omit [NeZero n] in
theorem cast_ne_zero {s : ℕ} (hs : 0 < s) (hsT : s < T) : (s : ZMod T) ≠ 0 := by
  have h00 : ((0 : ℕ) : ZMod T) = 0 := Nat.cast_zero
  rw [← h00, Ne, cast_eq_iff hsT (by omega)]
  omega

/-- The product of observables reduces to the two that are present. -/
theorem prod_twoObs (A B : C(Slice n, ℝ)) (s : ℕ) (hs0 : (s : ZMod T) ≠ 0) (x : ZMod T → Slice n) :
    ∏ t, twoObs T n A B s t (x t) = A (x 0) * B (x s) := by
  classical
  rw [Finset.prod_eq_mul (0 : ZMod T) (s : ZMod T) hs0.symm]
  · simp [twoObs]
    simp [hs0]
  · rintro t - ⟨h0, h1⟩
    simp [twoObs, h0, h1]
  · simp
  · simp

/-- **The two-point operator.** With `s, r > 0` and `s + r = T`, the time-ordered product for `A` at
time `0` and `B` at time `s` is `M_A Tˢ M_B Tʳ`. -/
theorem orderedProduct_twoObs (β : ℝ) (A B : C(Slice n, ℝ)) (s r : ℕ) (hs : 0 < s) (hr : 0 < r)
    (hsr : s + r = T) :
    orderedProduct T n β (twoObs T n A B s) =
      mulOp (sliceHaar n) A * transfer n β ^ s * (mulOp (sliceHaar n) B * transfer n β ^ r) := by
  classical
  obtain ⟨a, rfl⟩ : ∃ a, s = a + 1 := ⟨s - 1, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, r = c + 1 := ⟨r - 1, by omega⟩
  set Tr := transfer n β with hTr
  have hmul (F : C(Slice n, ℝ)) (hF : F = 1) : mulOp (sliceHaar n) F * Tr = Tr := by
    subst hF
    have h := operator_insK (sliceHaar n) (1 : C(Slice n, ℝ)) (twistedKernel n β)
    rw [insK_one] at h
    exact h.symm
  have h00 : ((0 : ℕ) : ZMod T) = 0 := Nat.cast_zero
  have hs0 : ((a + 1 : ℕ) : ZMod T) ≠ 0 := cast_ne_zero (by omega) (by omega)
  let G : ℕ → (WilsonSlabOperator.Hilbert n →L[ℂ] WilsonSlabOperator.Hilbert n) := fun k =>
    mulOp (sliceHaar n) (twoObs T n A B (a + 1) (k : ZMod T)) * Tr
  have hG0 : G 0 = mulOp (sliceHaar n) A * Tr := by
    simp only [G, Nat.cast_zero, twoObs, if_true]
  have hGs : G (a + 1) = mulOp (sliceHaar n) B * Tr := by
    simp only [G, twoObs, if_neg hs0, if_true]
  have hG1 : ∀ k < T, k ≠ 0 → k ≠ a + 1 → G k = Tr := by
    intro k hk h0 h1
    refine hmul _ ?_
    have e0 : (k : ZMod T) ≠ 0 := by
      rw [← h00, Ne, cast_eq_iff hk (by omega)]
      exact h0
    have e1 : (k : ZMod T) ≠ ((a + 1 : ℕ) : ZMod T) := by
      rw [Ne, cast_eq_iff hk (by omega)]
      exact h1
    simp only [twoObs, if_neg e0, if_neg e1]
  have hT : T = (1 + a) + (1 + c) := by omega
  have hprod : orderedProduct T n β (twoObs T n A B (a + 1)) = ((List.range T).map G).prod := rfl
  rw [hprod, hT, prod_range_add G (1 + a) (1 + c), prod_range_add G 1 a,
    prod_range_add (fun k => G (1 + a + k)) 1 c,
    prod_range_const (fun k => G (1 + k)) Tr a (fun k hk => hG1 _ (by omega) (by omega) (by omega)),
    prod_range_const (fun k => G (1 + a + (1 + k))) Tr c
      (fun k hk => hG1 _ (by omega) (by omega) (by omega))]
  have e : 1 + a + 0 = a + 1 := by omega
  simp only [List.range_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, e,
    hG0, hGs]
  simp only [pow_succ', mul_assoc]

/-- The translation of a chain in time. -/
def chainShift (T n : ℕ) [NeZero T] [NeZero n] (t₀ : ZMod T) (c : Chain T n) : Chain T n :=
  (fun t => c.1 (t + t₀), fun t => c.2 (t + t₀))

omit [NeZero n] in
theorem pi_shift_preserving {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν]
    (t₀ : ZMod T) :
    MeasurePreserving (fun (u : ZMod T → Y) t => u (t + t₀)) (Measure.pi fun _ => ν)
      (Measure.pi fun _ => ν) := by
  let E : ZMod T ≃ ZMod T := Equiv.addRight (-t₀)
  have hp := measurePreserving_piCongrLeft (fun _ : ZMod T => ν) E
  have hf : (fun (u : ZMod T → Y) t => u (t + t₀)) =
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : ZMod T => Y) E) := by
    funext u t
    have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ZMod T => Y) E u (t + t₀)
    have he : E (t + t₀) = t := by
      simp [E]
    rw [he] at h
    exact h.symm
  rw [hf]
  exact hp

theorem chainShift_ref (t₀ : ZMod T) :
    MeasurePreserving (chainShift T n t₀) (chainRef T n) (chainRef T n) :=
  (pi_shift_preserving (sliceHaar n) t₀).prod (pi_shift_preserving (temporalHaar (n := n) (G := Q)) t₀)

theorem chainAction_shift (β : ℝ) (t₀ : ZMod T) (c : Chain T n) :
    chainAction T n β (chainShift T n t₀ c) = chainAction T n β c := by
  unfold chainAction chainShift
  congr 1
  have h := Equiv.sum_comp (Equiv.addRight t₀) (fun t => twistedPotential n (c.1 t) +
    temporalAction character 2 (c.1 t) (c.1 (t + 1)) (c.2 t))
  simp only [Equiv.coe_addRight] at h
  rw [← h]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [add_right_comm t t₀ 1]

/-- `chainLaw` is invariant under time translation. -/
theorem chainLaw_shift (β : ℝ) (t₀ : ZMod T) :
    MeasurePreserving (chainShift T n t₀) (chainLaw T n β) (chainLaw T n β) :=
  chainLaw_preserved T n _ β (chainShift_ref t₀) (chainAction_shift β t₀)

theorem integral_of_preserving {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    [TopologicalSpace Z] [OpensMeasurableSpace Z] {μ : Measure Y} {ν : Measure Z} {φ : Y → Z}
    (hφ : MeasurePreserving φ μ ν) {G : Z → ℝ} (hG : Continuous G) :
    ∫ y, G (φ y) ∂μ = ∫ z, G z ∂ν := by
  rw [← hφ.map_eq, integral_map hφ.aemeasurable hG.aestronglyMeasurable]

/-- **The two-point function of slice observables on `chainLaw`, in operator form.** With `s, r > 0`
and `s + r = T`, at any base time, `E[A(u_{t₀}) B(u_{t₀+s})] = Tr(M_A Tˢ M_B Tʳ) / Tr Tᵀ`. -/
theorem trace_two_point (β : ℝ) (A B : C(Slice n, ℝ)) (s r : ℕ) (hs : 0 < s) (hr : 0 < r)
    (hsr : s + r = T) (t₀ : ZMod T) {ι : Type*}
    (b : HilbertBasis ι ℂ (WilsonSlabOperator.Hilbert n)) :
    ((∫ c, A (c.1 t₀) * B (c.1 (t₀ + s)) ∂chainLaw T n β : ℝ) : ℂ) =
      (∑' i, inner ℂ (b i) ((mulOp (sliceHaar n) A * transfer n β ^ s *
        (mulOp (sliceHaar n) B * transfer n β ^ r)) (b i))) /
        ∑' i, inner ℂ (b i) ((transfer n β ^ T) (b i)) := by
  have hs0 : (s : ZMod T) ≠ 0 := cast_ne_zero hs (by omega)
  rw [← orderedProduct_twoObs β A B s r hs hr hsr, ← expectation_trace (by omega) β _ b]
  congr 1
  have hc : Continuous fun c : Chain T n => A (c.1 0) * B (c.1 (s : ZMod T)) := by fun_prop
  simp only [prod_twoObs A B s hs0]
  rw [← integral_of_preserving (chainLaw_shift β t₀) hc]
  refine integral_congr_ae (Eventually.of_forall fun c => ?_)
  simp only [chainShift, zero_add, add_comm (s : ZMod T) t₀]

end Traces

/-! ### The actual twisted law at `T = L = 2n` -/

section ActualLaw
variable (n : ℕ) [NeZero n]

theorem law_integral (β : ℝ) {G : Chain (2 * n) (2 * n) → ℝ} (hG : Continuous G) :
    ∫ U, G (toChain (2 * n) U) ∂TwistedLocalization.twistedLaw n β =
      ∫ c, G c ∂chainLaw (2 * n) (2 * n) β :=
  integral_of_preserving (toChain_law n β) hG

/-- **Slice expectations under the actual twisted law are ratios of operator traces.** -/
theorem law_expectation_trace (β : ℝ) (F : ZMod (2 * n) → C(Slice (2 * n), ℝ)) {ι : Type*}
    (b : HilbertBasis ι ℂ (WilsonSlabOperator.Hilbert (2 * n))) :
    ((∫ U, ∏ t, F t (slice U t) ∂TwistedLocalization.twistedLaw n β : ℝ) : ℂ) =
      (∑' i, inner ℂ (b i) (orderedProduct (2 * n) (2 * n) β F (b i))) /
        ∑' i, inner ℂ (b i) ((transfer (2 * n) β ^ (2 * n)) (b i)) := by
  have hn := NeZero.pos n
  rw [← expectation_trace (by omega) β F b]
  congr 1
  refine law_integral n β (G := fun c => ∏ t, F t (c.1 t)) ?_
  exact continuous_finset_prod _ fun t _ => (F t).continuous.comp (by fun_prop)

/-- **The two-point function of slice observables under the actual twisted law.** With `s, r > 0`
and `s + r = 2n`, at any base time, `E[A(u_{t₀}) B(u_{t₀+s})] = Tr(M_A Tˢ M_B Tʳ) / Tr T^(2n)`. -/
theorem law_two_point (β : ℝ) (A B : C(Slice (2 * n), ℝ)) (s r : ℕ) (hs : 0 < s) (hr : 0 < r)
    (hsr : s + r = 2 * n) (t₀ : ZMod (2 * n)) {ι : Type*}
    (b : HilbertBasis ι ℂ (WilsonSlabOperator.Hilbert (2 * n))) :
    ((∫ U, A (slice U t₀) * B (slice U (t₀ + s)) ∂TwistedLocalization.twistedLaw n β : ℝ) : ℂ) =
      (∑' i, inner ℂ (b i) ((mulOp (sliceHaar (2 * n)) A * transfer (2 * n) β ^ s *
        (mulOp (sliceHaar (2 * n)) B * transfer (2 * n) β ^ r)) (b i))) /
        ∑' i, inner ℂ (b i) ((transfer (2 * n) β ^ (2 * n)) (b i)) := by
  rw [← trace_two_point β A B s r hs hr hsr t₀ b]
  congr 1
  exact law_integral n β (G := fun c => A (c.1 t₀) * B (c.1 (t₀ + s))) (by fun_prop)

end ActualLaw

/-! ### The vacuum term at finite time, and the excess of the trace -/

section FiniteTime
variable (n : ℕ) [NeZero n] (β : ℝ)

/-- **The excess of the trace at time extent `r`:** `Z(r) / ‖T‖^r - 1`. For `β ≥ 0` and `r ≥ 2` this is
the sum of `(λ / ‖T‖)^r` over the eigenvalues other than the top one (`excess_hasSum`). It is a defined
quantity. Controlling it is the open part of any bound at finite time. -/
def excess (r : ℕ) [NeZero r] : ℝ := chainZ r n β / ‖transfer n β‖ ^ r - 1

theorem transfer_symm (x y : WilsonSlabOperator.Hilbert n) :
    inner ℂ (transfer n β x) y = inner ℂ x (transfer n β y) :=
  (transfer_selfAdjoint n β).isSymmetric x y

/-- **An eigenbasis through the vacuum.** `TwistedNeutral.chainZ_spectrum`, with the top eigenvector
placed in the basis by simplicity (`TwistedVacuum.neutral_vacuum`). -/
theorem exists_vacuum_basis (hβ : 0 ≤ β) (Ω : WilsonSlabOperator.Hilbert n) (hΩ : ‖Ω‖ = 1)
    (htop : transfer n β Ω = ‖transfer n β‖ • Ω) :
    ∃ (w : Set (WilsonSlabOperator.Hilbert n)) (b : HilbertBasis w ℂ (WilsonSlabOperator.Hilbert n))
      (lam : w → ℝ) (k₀ : w) (c : ℂ), ‖c‖ = 1 ∧ b k₀ = c • Ω ∧ lam k₀ = ‖transfer n β‖ ∧
      (∀ k, 0 ≤ lam k) ∧ (∀ k, lam k ≤ ‖transfer n β‖) ∧ (∀ k, transfer n β (b k) = lam k • b k) ∧
      ∀ (r : ℕ) [NeZero r], 2 ≤ r → HasSum (fun k => lam k ^ r) (chainZ r n β) := by
  obtain ⟨w, -, b, lam, h0, heig, hsum⟩ := chainZ_spectrum n β hβ
  obtain ⟨Ω₁, -, -, -, hu⟩ := TwistedVacuum.neutral_vacuum n β hβ
  have hself : inner ℂ Ω Ω = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hΩ]
    simp
  obtain ⟨k₀, hk₀⟩ : ∃ k, inner ℂ (b k) Ω ≠ (0 : ℂ) := by
    by_contra hall
    push_neg at hall
    have h := b.hasSum_inner_mul_inner Ω Ω
    simp only [hall, mul_zero] at h
    have h' := h.unique hasSum_zero
    rw [hself] at h'
    exact one_ne_zero h'
  have hle (k : w) : lam k ≤ ‖transfer n β‖ := by
    have h1 := (transfer n β).le_opNorm (b k)
    rw [heig, norm_smul, b.orthonormal.1 k, mul_one, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (h0 k)] at h1
    exact h1
  have hlam : lam k₀ = ‖transfer n β‖ := by
    have h1 := transfer_symm n β (b k₀) Ω
    rw [heig, htop, RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ),
      inner_smul_left, inner_smul_right, RCLike.conj_ofReal] at h1
    exact_mod_cast mul_right_cancel₀ hk₀ h1
  obtain ⟨d, hd⟩ := hu (b k₀) (by rw [heig, hlam])
  obtain ⟨e, he⟩ := hu Ω htop
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [zero_smul] at he
    rw [he, norm_zero] at hΩ
    exact zero_ne_one hΩ
  have hb : b k₀ = (d * e⁻¹) • Ω := by
    rw [hd]
    conv_rhs => rw [he]
    rw [smul_smul, mul_assoc, inv_mul_cancel₀ he0, mul_one]
  have hc : ‖d * e⁻¹‖ = 1 := by
    have h1 := b.orthonormal.1 k₀
    rwa [hb, norm_smul, hΩ, mul_one] at h1
  refine ⟨w, b, lam, k₀, d * e⁻¹, hc, hb, hlam, h0, hle, heig, fun r _ hr => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  exact hsum m

/-- `‖T‖^r ≤ Z(r)`. -/
theorem pow_le_chainZ (hβ : 0 ≤ β) (r : ℕ) [NeZero r] (hr : 2 ≤ r) :
    ‖transfer n β‖ ^ r ≤ chainZ r n β := by
  obtain ⟨-, Ω, hΩ, htop⟩ := top_eigenvector n β hβ
  obtain ⟨w, b, lam, k₀, c, -, -, hlam, h0, -, -, hs⟩ := exists_vacuum_basis n β hβ Ω hΩ htop
  have h := le_hasSum (hs r hr) k₀ fun j _ => pow_nonneg (h0 j) r
  rwa [hlam] at h

/-- `Z(t) ≤ ‖T‖^(t-r) Z(r)`. So `‖T‖^t ≤ Z(t) ≤ ‖T‖^(t-2) Z(2)`. The constant depends on the cutoff. -/
theorem chainZ_le_pow_mul (hβ : 0 ≤ β) (t r : ℕ) [NeZero t] [NeZero r] (hr : 2 ≤ r) (hrt : r ≤ t) :
    chainZ t n β ≤ ‖transfer n β‖ ^ (t - r) * chainZ r n β := by
  obtain ⟨-, Ω, hΩ, htop⟩ := top_eigenvector n β hβ
  obtain ⟨w, b, lam, k₀, c, -, -, -, h0, hle, -, hs⟩ := exists_vacuum_basis n β hβ Ω hΩ htop
  refine hasSum_le (fun k => ?_) (hs t (by omega)) ((hs r hr).mul_left _)
  have ht : lam k ^ t = lam k ^ (t - r) * lam k ^ r := by
    rw [← pow_add]
    congr 1
    omega
  rw [ht]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (h0 k) (hle k) _) (pow_nonneg (h0 k) r)

theorem excess_nonneg (hβ : 0 ≤ β) (r : ℕ) [NeZero r] (hr : 2 ≤ r) : 0 ≤ excess n β r := by
  obtain ⟨hτ, -⟩ := top_eigenvector n β hβ
  have h := (one_le_div (pow_pos hτ r)).mpr (pow_le_chainZ n β hβ r hr)
  unfold excess
  linarith

/-- The excess decreases with the time extent. -/
theorem excess_anti (hβ : 0 ≤ β) (t r : ℕ) [NeZero t] [NeZero r] (hr : 2 ≤ r) (hrt : r ≤ t) :
    excess n β t ≤ excess n β r := by
  obtain ⟨hτ, -⟩ := top_eigenvector n β hβ
  unfold excess
  have hpt : ‖transfer n β‖ ^ t = ‖transfer n β‖ ^ (t - r) * ‖transfer n β‖ ^ r := by
    rw [← pow_add]
    congr 1
    omega
  have hle := chainZ_le_pow_mul n β hβ t r hr hrt
  have h : chainZ t n β / ‖transfer n β‖ ^ t ≤ chainZ r n β / ‖transfer n β‖ ^ r := by
    rw [div_le_div_iff₀ (pow_pos hτ t) (pow_pos hτ r), hpt]
    nlinarith [mul_le_mul_of_nonneg_right hle (pow_pos hτ r).le]
  linarith

/-- At fixed `n` and `β ≥ 0` the excess tends to `0` as the time extent grows, at a rate with no control
(`TwistedNeutral.chainZ_dominance`). -/
theorem excess_tendsto (hβ : 0 ≤ β) : Tendsto (fun m : ℕ => excess n β (m + 2)) atTop (𝓝 0) := by
  obtain ⟨ρ, C, hρ0, hρ1, h⟩ := chainZ_dominance n β hβ
  refine tendsto_of_geometric _ 0 C ρ hρ0 hρ1 fun m => ?_
  rw [sub_zero]
  exact h m

open Classical in
/-- The excess is the sum of `(λ / ‖T‖)^r` off the vacuum, in an eigenbasis through the vacuum. -/
theorem excess_hasSum (hβ : 0 ≤ β) (r : ℕ) [NeZero r] (hr : 2 ≤ r) :
    ∃ (w : Set (WilsonSlabOperator.Hilbert n)) (b : HilbertBasis w ℂ (WilsonSlabOperator.Hilbert n))
      (lam : w → ℝ) (k₀ : w), lam k₀ = ‖transfer n β‖ ∧ (∀ k, transfer n β (b k) = lam k • b k) ∧
      HasSum (Function.update (fun k => (lam k / ‖transfer n β‖) ^ r) k₀ 0) (excess n β r) := by
  obtain ⟨hτ, Ω, hΩ, htop⟩ := top_eigenvector n β hβ
  obtain ⟨w, b, lam, k₀, c, -, -, hlam, -, -, heig, hs⟩ := exists_vacuum_basis n β hβ Ω hΩ htop
  refine ⟨w, b, lam, k₀, hlam, heig, ?_⟩
  have hp := pow_pos hτ r
  have h := (hs r hr).div_const (‖transfer n β‖ ^ r)
  simp only [← div_pow] at h
  have hu := h.update k₀ 0
  convert hu using 1
  unfold excess
  rw [hlam, div_self hτ.ne', one_pow]
  ring

/-- The arithmetic behind `two_point_finite`. -/
theorem ratio_close (m z l : ℝ) (V : ℂ) (M x : ℝ) (hl : 0 < l) (hlz : l ≤ z) (hM : 0 ≤ M) (hx : 0 ≤ x)
    (hV : ‖V‖ ≤ M) (h1 : ‖(m : ℂ) - (l : ℂ) * V‖ ≤ M * (l * x)) (h2 : z - l ≤ l * x) :
    ‖((m / z : ℝ) : ℂ) - V‖ ≤ 2 * M * x := by
  have hz : 0 < z := lt_of_lt_of_le hl hlz
  have hzc : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  have he : ((m / z : ℝ) : ℂ) - V = (((m : ℂ) - (l : ℂ) * V) + ((l - z : ℝ) : ℂ) * V) / (z : ℂ) := by
    push_cast
    field_simp
    ring
  rw [he, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz, div_le_iff₀ hz]
  have h3 : ‖((l - z : ℝ) : ℂ) * V‖ ≤ (l * x) * M := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (by linarith)]
    exact mul_le_mul h2 hV (norm_nonneg _) (by positivity)
  refine (norm_add_le _ _).trans ?_
  nlinarith [mul_le_mul_of_nonneg_left hlz (mul_nonneg hM hx)]

theorem mulOp_opNorm_le (F : C(Slice n, ℝ)) : ‖mulOp (sliceHaar n) F‖ ≤ ‖F‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (mulOp_norm_le (sliceHaar n) F)

/-- **The two-point function at finite time extent.** With `s + r = T`, `s > 0` and `r ≥ 2`, the
expectation under `chainLaw T n β` is the vacuum matrix element up to `2 ‖A‖ ‖B‖ excess(r)`. Nothing is
assumed about the size of the excess. At fixed `n` it is small for large `r` (`excess_tendsto`), and for
large `β` at fixed `r` it is not (`excess_not_small`). -/
theorem two_point_finite (hβ : 0 ≤ β) (Ω : WilsonSlabOperator.Hilbert n) (hΩ : ‖Ω‖ = 1)
    (htop : transfer n β Ω = ‖transfer n β‖ • Ω) (A B : C(Slice n, ℝ)) {T s r : ℕ} [NeZero T] [NeZero r]
    (hs : 0 < s) (hr : 2 ≤ r) (hsr : s + r = T) :
    ‖((∫ c, A (c.1 0) * B (c.1 (s : ZMod T)) ∂chainLaw T n β : ℝ) : ℂ) -
        inner ℂ Ω ((mulOp (sliceHaar n) A * transfer n β ^ s * mulOp (sliceHaar n) B) Ω) /
          ((‖transfer n β‖ ^ s : ℝ) : ℂ)‖ ≤ 2 * (‖A‖ * ‖B‖) * excess n β r := by
  obtain ⟨hτ, -⟩ := top_eigenvector n β hβ
  obtain ⟨w, b, lam, k₀, c, hc, hb, hlam, h0, -, heig, hsum⟩ := exists_vacuum_basis n β hβ Ω hΩ htop
  set Y := mulOp (sliceHaar n) A * transfer n β ^ s * mulOp (sliceHaar n) B with hY
  set τ := ‖transfer n β‖ with hτd
  have hop : orderedProduct T n β (twoObs T n A B s) = Y * transfer n β ^ r := by
    rw [orderedProduct_twoObs β A B s r hs (by omega) hsr, hY]
    simp only [mul_assoc]
  have ha := trace_orderedProduct (T := T) (n := n) (by omega) β (twoObs T n A B s) b
  rw [hop] at ha
  have hmain := trace_eigenbasis (transfer n β) Ω b lam heig h0 k₀ c hc hb Y r _ ha _ (hsum r hr)
  rw [hlam] at hmain
  have hYn : ‖Y‖ ≤ ‖A‖ * ‖B‖ * τ ^ s := by
    calc ‖Y‖ ≤ ‖mulOp (sliceHaar n) A‖ * ‖transfer n β ^ s‖ * ‖mulOp (sliceHaar n) B‖ := by
          rw [hY]
          exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ‖A‖ * τ ^ s * ‖B‖ := by
          refine mul_le_mul (mul_le_mul (mulOp_opNorm_le n A) (opNorm_pow_le _ s) (norm_nonneg _)
            (norm_nonneg _)) (mulOp_opNorm_le n B) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hpT : τ ^ T = τ ^ s * τ ^ r := by rw [← hsr, pow_add]
  have hτs := pow_pos hτ s
  have hτr := pow_pos hτ r
  have hx := excess_nonneg n β hβ r hr
  have hZr : chainZ r n β - τ ^ r = τ ^ r * excess n β r := by
    unfold excess
    rw [← hτd]
    field_simp
  have hVn : ‖inner ℂ Ω (Y Ω) / ((τ ^ s : ℝ) : ℂ)‖ ≤ ‖A‖ * ‖B‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτs, div_le_iff₀ hτs]
    refine (norm_inner_le_norm _ _).trans ?_
    rw [hΩ, one_mul]
    exact (Y.le_opNorm _).trans (by rw [hΩ, mul_one]; exact hYn)
  have hs0 : (s : ZMod T) ≠ 0 := cast_ne_zero hs (by omega)
  have hE : ∫ c, A (c.1 0) * B (c.1 (s : ZMod T)) ∂chainLaw T n β =
      moment T n β (twoObs T n A B s) / chainZ T n β := by
    rw [← expectation_eq]
    simp only [prod_twoObs A B s hs0]
  rw [hE]
  refine ratio_close _ _ (τ ^ T) _ _ _ (pow_pos hτ T) (pow_le_chainZ n β hβ T (by omega))
    (by positivity) hx hVn ?_ ?_
  · have e : ((τ ^ T : ℝ) : ℂ) * (inner ℂ Ω (Y Ω) / ((τ ^ s : ℝ) : ℂ)) =
        ((τ ^ r : ℝ) : ℂ) * inner ℂ Ω (Y Ω) := by
      have hne : ((τ ^ s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτs.ne'
      rw [hpT]
      push_cast
      push_cast at hne
      field_simp
    rw [e]
    refine hmain.trans ?_
    rw [hZr, hpT]
    calc ‖Y‖ * (τ ^ r * excess n β r) ≤ (‖A‖ * ‖B‖ * τ ^ s) * (τ ^ r * excess n β r) :=
          mul_le_mul_of_nonneg_right hYn (by positivity)
      _ = _ := by ring
  · have hanti := excess_anti n β hβ T r hr (by omega)
    have h2 : chainZ T n β - τ ^ T = τ ^ T * excess n β T := by
      unfold excess
      rw [← hτd]
      field_simp
    rw [h2]
    exact mul_le_mul_of_nonneg_left hanti (pow_pos hτ T).le

/-- The observable at time `0` alone. -/
theorem one_point_left (hβ : 0 ≤ β) (Ω : WilsonSlabOperator.Hilbert n) (hΩ : ‖Ω‖ = 1)
    (htop : transfer n β Ω = ‖transfer n β‖ • Ω) (A : C(Slice n, ℝ)) {T s r : ℕ} [NeZero T] [NeZero r]
    (hs : 0 < s) (hr : 2 ≤ r) (hsr : s + r = T) :
    ‖((∫ c, A (c.1 0) ∂chainLaw T n β : ℝ) : ℂ) - inner ℂ Ω (mulOp (sliceHaar n) A Ω)‖ ≤
      2 * ‖A‖ * excess n β r := by
  obtain ⟨hτ, -⟩ := top_eigenvector n β hβ
  have h := two_point_finite n β hβ Ω hΩ htop A 1 (T := T) hs hr hsr
  simp only [ContinuousMap.one_apply, mul_one] at h
  have hval : inner ℂ Ω ((mulOp (sliceHaar n) A * transfer n β ^ s * mulOp (sliceHaar n) 1) Ω) /
      ((‖transfer n β‖ ^ s : ℝ) : ℂ) = inner ℂ Ω (mulOp (sliceHaar n) A Ω) := by
    change inner ℂ Ω (mulOp (sliceHaar n) A ((transfer n β ^ s)
      (mulOp (sliceHaar n) 1 Ω))) / _ = _
    rw [mulOp_one, pow_top _ Ω _ htop, RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul,
      inner_smul_right]
    have hne : ((‖transfer n β‖ ^ s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_pos hτ _).ne'
    change ((‖transfer n β‖ ^ s : ℝ) : ℂ) * _ / _ = _
    field_simp
  rw [hval] at h
  refine h.trans ?_
  have h1 : ‖(1 : C(Slice n, ℝ))‖ ≤ 1 := (ContinuousMap.norm_le _ zero_le_one).mpr (by simp)
  have hx := excess_nonneg n β hβ r hr
  have hA := norm_nonneg A
  have : ‖A‖ * ‖(1 : C(Slice n, ℝ))‖ ≤ ‖A‖ := by nlinarith
  nlinarith

/-- The observable at time `s` alone. -/
theorem one_point_right (hβ : 0 ≤ β) (Ω : WilsonSlabOperator.Hilbert n) (hΩ : ‖Ω‖ = 1)
    (htop : transfer n β Ω = ‖transfer n β‖ • Ω) (B : C(Slice n, ℝ)) {T s r : ℕ} [NeZero T] [NeZero r]
    (hs : 0 < s) (hr : 2 ≤ r) (hsr : s + r = T) :
    ‖((∫ c, B (c.1 (s : ZMod T)) ∂chainLaw T n β : ℝ) : ℂ) - inner ℂ Ω (mulOp (sliceHaar n) B Ω)‖ ≤
      2 * ‖B‖ * excess n β r := by
  obtain ⟨hτ, -⟩ := top_eigenvector n β hβ
  have h := two_point_finite n β hβ Ω hΩ htop 1 B (T := T) hs hr hsr
  simp only [ContinuousMap.one_apply, one_mul] at h
  have hval : inner ℂ Ω ((mulOp (sliceHaar n) 1 * transfer n β ^ s * mulOp (sliceHaar n) B) Ω) /
      ((‖transfer n β‖ ^ s : ℝ) : ℂ) = inner ℂ Ω (mulOp (sliceHaar n) B Ω) := by
    change inner ℂ Ω (mulOp (sliceHaar n) 1 ((transfer n β ^ s)
      (mulOp (sliceHaar n) B Ω))) / _ = _
    rw [mulOp_one, ← pow_symm _ (transfer_symm n β), pow_top _ Ω _ htop,
      RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left]
    have hne : ((‖transfer n β‖ ^ s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_pos hτ _).ne'
    rw [RCLike.conj_ofReal]
    change ((‖transfer n β‖ ^ s : ℝ) : ℂ) * _ / _ = _
    field_simp
  rw [hval] at h
  refine h.trans ?_
  have h1 : ‖(1 : C(Slice n, ℝ))‖ ≤ 1 := (ContinuousMap.norm_le _ zero_le_one).mpr (by simp)
  have hx := excess_nonneg n β hβ r hr
  have hB := norm_nonneg B
  have : ‖(1 : C(Slice n, ℝ))‖ * ‖B‖ ≤ ‖B‖ := by nlinarith
  nlinarith

/-- An expectation under `chainLaw` is bounded by the sup norm. -/
theorem abs_integral_chainLaw_le {T : ℕ} [NeZero T] {G : Chain T n → ℝ} (hG : Continuous G) (M : ℝ)
    (hM : ∀ c, |G c| ≤ M) : |∫ c, G c ∂chainLaw T n β| ≤ M := by
  have hZ := chainZ_pos n β T
  rw [chainLaw_integral, abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
  have hS := (Real.continuous_exp.comp (chainAction_continuous T n β).neg)
  refine (abs_integral_le_integral_abs).trans ?_
  have hint : ∫ c, M * Real.exp (-chainAction T n β c) ∂chainRef T n = M * chainZ T n β := by
    rw [integral_const_mul]
    rfl
  rw [← hint]
  refine integral_mono ?_ ?_ fun c => ?_
  · refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
    exact (hG.mul hS).abs
  · refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
    exact continuous_const.mul hS
  · dsimp only
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hM c) (Real.exp_pos _).le

/-- The connected two-point function under `chainLaw T n β`: `A` at time `0`, `B` at time `s`. -/
def connected (T n : ℕ) [NeZero T] [NeZero n] (β : ℝ) (A B : C(Slice n, ℝ)) (s : ℕ) : ℝ :=
  ∫ c, A (c.1 0) * B (c.1 (s : ZMod T)) ∂chainLaw T n β -
    (∫ c, A (c.1 0) ∂chainLaw T n β) * ∫ c, B (c.1 (s : ZMod T)) ∂chainLaw T n β

/-- The arithmetic behind `connected_finite`. -/
theorem connected_arith (Eab Ea Eb : ℝ) (v a b : ℂ) (α γ x p : ℝ) (hα : 0 ≤ α)
    (h1 : ‖((Eab : ℝ) : ℂ) - v‖ ≤ 2 * (α * γ) * x) (hv : ‖v - a * b‖ ≤ p * (α * γ))
    (h2 : ‖((Ea : ℝ) : ℂ) - a‖ ≤ 2 * α * x) (h3 : ‖((Eb : ℝ) : ℂ) - b‖ ≤ 2 * γ * x) (ha : ‖a‖ ≤ α)
    (hEb : |Eb| ≤ γ) (hx : 0 ≤ x) :
    |Eab - Ea * Eb| ≤ (p + 6 * x) * (α * γ) := by
  have hγ : 0 ≤ γ := (abs_nonneg _).trans hEb
  have hdec : (((Eab - Ea * Eb : ℝ)) : ℂ) =
      (((Eab : ℝ) : ℂ) - v) + (v - a * b) - (((Ea : ℝ) : ℂ) - a) * ((Eb : ℝ) : ℂ) -
        a * (((Eb : ℝ) : ℂ) - b) := by
    push_cast
    ring
  have hfin : ‖((Eab - Ea * Eb : ℝ) : ℂ)‖ ≤
      2 * (α * γ) * x + p * (α * γ) + (2 * α * x) * γ + α * (2 * γ * x) := by
    rw [hdec]
    refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add h1 hv)) ?_)) ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul h2 hEb (abs_nonneg _) (by positivity)
    · rw [norm_mul]
      exact mul_le_mul ha h3 (norm_nonneg _) hα
  rw [Complex.norm_real, Real.norm_eq_abs] at hfin
  refine hfin.trans (le_of_eq ?_)
  ring

/-- **The connected function at finite time extent.** The hypotheses are a contraction by `ρ` on an
invariant set `P` containing the projected state of `B`; the proof takes no other input about the
spectrum. The bound is `ρˢ` plus six times the excess, and is empty unless the excess is below `1/3`. -/
theorem connected_finite (hβ : 0 ≤ β) (Ω : WilsonSlabOperator.Hilbert n) (hΩ : ‖Ω‖ = 1)
    (htop : transfer n β Ω = ‖transfer n β‖ • Ω)
    (P : WilsonSlabOperator.Hilbert n → Prop) (hPT : ∀ f, P f → P (transfer n β f))
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ∀ f, P f → inner ℂ Ω f = 0 →
      ‖transfer n β f‖ ≤ ρ * ‖transfer n β‖ * ‖f‖)
    (A B : C(Slice n, ℝ))
    (hB : P (mulOp (sliceHaar n) B Ω - inner ℂ Ω (mulOp (sliceHaar n) B Ω) • Ω))
    {T s r : ℕ} [NeZero T] [NeZero r] (hs : 0 < s) (hr : 2 ≤ r) (hsr : s + r = T) :
    |connected T n β A B s| ≤ (ρ ^ s + 6 * excess n β r) * (‖A‖ * ‖B‖) := by
  obtain ⟨hτ, -⟩ := top_eigenvector n β hβ
  have hx := excess_nonneg n β hβ r hr
  have h1 := two_point_finite n β hβ Ω hΩ htop A B (T := T) hs hr hsr
  have h2 := one_point_left n β hβ Ω hΩ htop A (T := T) hs hr hsr
  have h3 := one_point_right n β hβ Ω hΩ htop B (T := T) hs hr hsr
  have hu : ‖mulOp (sliceHaar n) A Ω‖ ≤ ‖A‖ := by
    have := mulOp_norm_le (sliceHaar n) A Ω
    rwa [hΩ, mul_one] at this
  have hv : ‖mulOp (sliceHaar n) B Ω‖ ≤ ‖B‖ := by
    have := mulOp_norm_le (sliceHaar n) B Ω
    rwa [hΩ, mul_one] at this
  have hb := cluster_bound (transfer n β) Ω ‖transfer n β‖ ρ P hPT
    hρ0 hτ hΩ (transfer_symm n β) htop hρ (mulOp (sliceHaar n) A Ω) (mulOp (sliceHaar n) B Ω) hB s
  have e1 : inner ℂ Ω ((mulOp (sliceHaar n) A * transfer n β ^ s * mulOp (sliceHaar n) B) Ω) =
      inner ℂ (mulOp (sliceHaar n) A Ω) ((transfer n β ^ s) (mulOp (sliceHaar n) B Ω)) :=
    (mulOp_symm (sliceHaar n) A Ω _).symm
  have e2 : inner ℂ Ω (mulOp (sliceHaar n) A Ω) = inner ℂ (mulOp (sliceHaar n) A Ω) Ω :=
    (mulOp_symm (sliceHaar n) A Ω Ω).symm
  rw [← e2] at hb
  rw [e1] at h1
  have hbA : ‖inner ℂ Ω (mulOp (sliceHaar n) A Ω)‖ ≤ ‖A‖ := by
    refine (norm_inner_le_norm _ _).trans ?_
    rw [hΩ, one_mul]
    exact hu
  have hEB : |∫ c, B (c.1 (s : ZMod T)) ∂chainLaw T n β| ≤ ‖B‖ :=
    abs_integral_chainLaw_le n β (by fun_prop) _ fun c => B.norm_coe_le_norm _
  have hb' := hb.trans (mul_le_mul_of_nonneg_left (mul_le_mul hu hv (norm_nonneg _) (norm_nonneg A))
    (pow_nonneg hρ0 s))
  exact connected_arith _ _ _ _ _ _ _ _ _ _ (norm_nonneg A) h1 hb' h2 h3 hbA hEB hx

/-- Multiplication by a flip-invariant observable commutes with the flips. -/
theorem mulOp_flipOp (B : C(Slice n, ℝ)) (i : Fin 3) (c : ZMod n)
    (hB : ∀ u, B (flip n i c u) = B u) (f : WilsonSlabOperator.Hilbert n) :
    flipOp n i c (mulOp (sliceHaar n) B f) = mulOp (sliceHaar n) B (flipOp n i c f) := by
  have hmp := flip_measurePreserving n i c
  apply Lp.ext
  have h1 : (flipOp n i c (mulOp (sliceHaar n) B f) : Slice n → ℂ) =ᵐ[sliceHaar n]
      ((mulOp (sliceHaar n) B f : Slice n → ℂ) ∘ flip n i c) :=
    Lp.coeFn_compMeasurePreserving _ hmp
  have h2 := hmp.quasiMeasurePreserving.ae_eq_comp (mulOp_ae (sliceHaar n) B f)
  have h3 : (flipOp n i c f : Slice n → ℂ) =ᵐ[sliceHaar n] ((f : Slice n → ℂ) ∘ flip n i c) :=
    Lp.coeFn_compMeasurePreserving _ hmp
  filter_upwards [h1, h2, h3, mulOp_ae (sliceHaar n) B (flipOp n i c f)] with u e1 e2 e3 e4
  rw [e1, e2, e4, e3]
  simp only [Function.comp, hB]

/-- The connected function of a flip-invariant `B`, given a contraction on the neutral complement of a
neutral vacuum. Only that contraction is used, not a lower bound on any level. At one cutoff some
`ρ < 1` always works (`TwistedFiniteGap.finite_gap`), so the content lies in the value of `ρ` and in the
excess. -/
theorem connected_of_contraction (hβ : 0 ≤ β) (Ω : WilsonSlabOperator.Hilbert n) (hΩ : ‖Ω‖ = 1)
    (htop : transfer n β Ω = ‖transfer n β‖ • Ω) (hN : Neutral n Ω) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ∀ f, Neutral n f → inner ℂ Ω f = 0 → ‖transfer n β f‖ ≤ ρ * ‖transfer n β‖ * ‖f‖)
    (A B : C(Slice n, ℝ)) (hB : ∀ i c u, B (flip n i c u) = B u)
    {T s r : ℕ} [NeZero T] [NeZero r] (hs : 0 < s) (hr : 2 ≤ r) (hsr : s + r = T) :
    |connected T n β A B s| ≤ (ρ ^ s + 6 * excess n β r) * (‖A‖ * ‖B‖) := by
  refine connected_finite n β hβ Ω hΩ htop (Neutral n) (fun f hf i c => ?_) ρ hρ0 hρ A B
    (fun i c => ?_) hs hr hsr
  · rw [← transfer_flipOp, hf i c]
  · rw [map_sub, map_smul, mulOp_flipOp n B i c (hB i c), hN i c]

/-- **Conditional on the open `TargetAGap`, at finite time extent.** The bound is
`exp (-c s / n) + 6 excess(r)`. Only the contraction half of the window is used. The excess stays in the
conclusion, and nothing here bounds it. -/
theorem connected_of_targetAGap (b : ℝ) (h : TargetAGap b) :
    ∃ β₀ c : ℝ, 0 < c ∧ ∀ (n : ℕ) [NeZero n], 2 ≤ n → ∀ β, b * Real.log n + β₀ ≤ β → 0 ≤ β →
      ∀ (A B : C(Slice n, ℝ)), (∀ i c u, B (flip n i c u) = B u) →
      ∀ {T s r : ℕ} [NeZero T] [NeZero r], 0 < s → 2 ≤ r → s + r = T →
        |connected T n β A B s| ≤ (Real.exp (-c * s / n) + 6 * excess n β r) * (‖A‖ * ‖B‖) := by
  obtain ⟨β₀, c, C', hc, -, hgap⟩ := h
  refine ⟨β₀, c, hc, fun n _ hn β hβ₁ hβ A B hB T s r _ _ hs hr hsr => ?_⟩
  obtain ⟨Ω, hΩ, htop, hN, hρ, -⟩ := hgap n hn β hβ₁
  have h' := connected_of_contraction n β hβ Ω hΩ htop hN _ (Real.exp_pos _).le hρ A B hB hs hr hsr
  have hexp : Real.exp (-c / n) ^ s = Real.exp (-c * s / n) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rwa [hexp] at h'

/-- The connected function under the actual twisted law at lattice size `2n` is `connected` at `T = L`. -/
theorem law_connected_eq (n : ℕ) [NeZero n] (β : ℝ) (A B : C(Slice (2 * n), ℝ)) (s : ℕ) :
    (∫ U, A (slice U 0) * B (slice U (s : ZMod (2 * n))) ∂TwistedLocalization.twistedLaw n β) -
      (∫ U, A (slice U 0) ∂TwistedLocalization.twistedLaw n β) *
        ∫ U, B (slice U (s : ZMod (2 * n))) ∂TwistedLocalization.twistedLaw n β =
      connected (2 * n) (2 * n) β A B s := by
  unfold connected
  rw [← law_integral n β (G := fun c => A (c.1 0) * B (c.1 (s : ZMod (2 * n)))) (by fun_prop),
    ← law_integral n β (G := fun c => A (c.1 0)) (by fun_prop),
    ← law_integral n β (G := fun c => B (c.1 (s : ZMod (2 * n)))) (by fun_prop)]
  rfl

/-- **Conditional on the open `TargetAGap`, for the actual twisted 4D law at `T = L = 2n`.** The
separation `s` and the complement `r` satisfy `s + r = 2n`. The rate at spatial size `2n` is `c / (2n)`,
so at `s = n` the first term is the constant `exp (-c / 2)`: a box of one unit of `L` shows no decay in
`n`. The excess is not controlled. -/
theorem law_connected_of_targetAGap (b : ℝ) (h : TargetAGap b) :
    ∃ β₀ c : ℝ, 0 < c ∧ ∀ (n : ℕ) [NeZero n] (β : ℝ), b * Real.log ((2 * n : ℕ) : ℝ) + β₀ ≤ β → 0 ≤ β →
      ∀ (A B : C(Slice (2 * n), ℝ)), (∀ i c u, B (flip (2 * n) i c u) = B u) →
      ∀ {s r : ℕ} [NeZero r], 0 < s → 2 ≤ r → s + r = 2 * n →
        |(∫ U, A (slice U 0) * B (slice U (s : ZMod (2 * n))) ∂TwistedLocalization.twistedLaw n β) -
          (∫ U, A (slice U 0) ∂TwistedLocalization.twistedLaw n β) *
            ∫ U, B (slice U (s : ZMod (2 * n))) ∂TwistedLocalization.twistedLaw n β| ≤
          (Real.exp (-c * s / ((2 * n : ℕ) : ℝ)) + 6 * excess (2 * n) β r) * (‖A‖ * ‖B‖) := by
  obtain ⟨β₀, c, hc, hgap⟩ := connected_of_targetAGap b h
  refine ⟨β₀, c, hc, fun n _ β hβ₁ hβ A B hB s r _ hs hr hsr => ?_⟩
  have hn := NeZero.pos n
  rw [law_connected_eq]
  exact hgap (2 * n) (by omega) β hβ₁ hβ A B hB hs hr hsr

end FiniteTime

/-! ### A limit on this route: the flux-odd level keeps the excess from being small -/

section FluxLimit
variable (n : ℕ) [NeZero n] (β : ℝ)

/-- **A vector with a near-top Rayleigh quotient forces excess.** At even time extent the excess is
at least `θ^(2a)`, if a nonzero vector orthogonal to the vacuum is contracted by at most `θ`. -/
theorem excess_even_lower (hβ : 0 ≤ β) (Ω F : WilsonSlabOperator.Hilbert n) (hΩ : ‖Ω‖ = 1)
    (htop : transfer n β Ω = ‖transfer n β‖ • Ω) (hF : F ≠ 0) (horth : inner ℂ Ω F = (0 : ℂ))
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ * ‖transfer n β‖ * ‖F‖ ≤ ‖transfer n β F‖)
    (a : ℕ) [NeZero (2 * a)] (ha : 1 ≤ a) : θ ^ (2 * a) ≤ excess n β (2 * a) := by
  classical
  obtain ⟨hτ, -⟩ := top_eigenvector n β hβ
  set τ := ‖transfer n β‖ with hτd
  have hFn : 0 < ‖F‖ := norm_pos_iff.mpr hF
  set e := ((‖F‖ : ℂ)⁻¹) • F with he
  have hen : ‖e‖ = 1 := by
    rw [he, norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hFn.ne']
  have heo : inner ℂ Ω e = (0 : ℂ) := by rw [he, inner_smul_right, horth, mul_zero]
  have hestep : (θ * τ) * ‖e‖ ≤ ‖transfer n β e‖ := by
    rw [hen, mul_one, he, map_smul, norm_smul, norm_inv, Complex.norm_real, norm_norm,
      inv_mul_eq_div, le_div_iff₀ hFn]
    exact hθ
  obtain ⟨u, b, i₀, i₁, hne, hb0, hb1⟩ := exists_basis_pair Ω e hΩ hen heo
  have ht := Complex.reCLM.hasSum (trace_transfer_pow (T := 2 * a) (n := n) (by omega) β b)
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at ht
  have hle := sum_le_hasSum {i₀, i₁} (fun j _ => inner_pow_nonneg _
    (transfer_positive n β hβ) (2 * a) (b j)) ht
  rw [Finset.sum_pair hne, hb0, hb1] at hle
  have h0 : (inner ℂ Ω ((transfer n β ^ (2 * a)) Ω) : ℂ).re = τ ^ (2 * a) := by
    rw [pow_top _ Ω _ htop, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right,
      inner_self_eq_norm_sq_to_K, hΩ]
    simp only [map_pow, RCLike.ofReal_one, one_pow, mul_one]
    change (((τ : ℝ) : ℂ) ^ (2 * a)).re = _
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have h1 : (θ * τ) ^ (2 * a) ≤ (inner ℂ e ((transfer n β ^ (2 * a)) e) : ℂ).re := by
    have hsplit : (transfer n β ^ (2 * a)) e = (transfer n β ^ a) ((transfer n β ^ a) e) := by
      rw [two_mul, pow_add]
      rfl
    have hmv : inner ℂ e ((transfer n β ^ a) ((transfer n β ^ a) e)) =
        inner ℂ ((transfer n β ^ a) e) ((transfer n β ^ a) e) :=
      (pow_symm _ (transfer_symm n β) a e _).symm
    rw [hsplit, hmv, inner_self_eq_norm_sq_to_K]
    have hre : (((‖(transfer n β ^ a) e‖ : ℝ) : ℂ) ^ 2).re = ‖(transfer n β ^ a) e‖ ^ 2 := by
      norm_cast
    have hre' : ((RCLike.ofReal ‖(transfer n β ^ a) e‖ : ℂ) ^ 2).re = ‖(transfer n β ^ a) e‖ ^ 2 := hre
    rw [hre']
    have hl := norm_pow_lower (transfer n β) (transfer_symm n β) (θ * τ) (by positivity) e hestep a
    rw [hen, mul_one] at hl
    rw [show (θ * τ) ^ (2 * a) = ((θ * τ) ^ a) ^ 2 by rw [← pow_mul, mul_comm a 2]]
    exact pow_le_pow_left₀ (pow_nonneg (by positivity) a) hl 2
  have hpow := pow_pos hτ (2 * a)
  unfold excess
  rw [le_sub_iff_add_le, le_div_iff₀ hpow]
  rw [mul_pow] at h1
  nlinarith

/-- **The same bound at every time extent `r ≥ 2`,** with one more power of `θ`. -/
theorem excess_lower (hβ : 0 ≤ β) (Ω F : WilsonSlabOperator.Hilbert n) (hΩ : ‖Ω‖ = 1)
    (htop : transfer n β Ω = ‖transfer n β‖ • Ω) (hF : F ≠ 0) (horth : inner ℂ Ω F = (0 : ℂ))
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ * ‖transfer n β‖ * ‖F‖ ≤ ‖transfer n β F‖)
    (r : ℕ) [NeZero r] (hr : 2 ≤ r) : θ ^ (r + 1) ≤ excess n β r := by
  obtain ⟨hτ, -⟩ := top_eigenvector n β hβ
  have hFn : 0 < ‖F‖ := norm_pos_iff.mpr hF
  have hθ1 : θ ≤ 1 := by
    have h := (transfer n β).le_opNorm F
    have h' := hθ.trans h
    have hpos : 0 < ‖transfer n β‖ * ‖F‖ := mul_pos hτ hFn
    nlinarith
  set a := (r + 1) / 2 with ha
  have h1 : r ≤ 2 * a := by omega
  have h2 : 2 * a ≤ r + 1 := by omega
  haveI : NeZero (2 * a) := ⟨by omega⟩
  calc θ ^ (r + 1) ≤ θ ^ (2 * a) := pow_le_pow_of_le_one hθ0 hθ1 h2
    _ ≤ excess n β (2 * a) := excess_even_lower n β hβ Ω F hΩ htop hF horth θ hθ0 hθ a (by omega)
    _ ≤ excess n β r := excess_anti n β hβ _ _ hr h1

/-- **At fixed `n` and time extent, large coupling makes the excess at least `1 - ε`.** This is
`TwistedFluxSector.flux_gap_vanishes` fed through `excess_lower`. How the threshold in `β` depends on `n`
is not stated, so this does not locate the failure on a given trajectory `β(n)`. -/
theorem flux_excess (r : ℕ) [NeZero r] (hr : 2 ≤ r) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ β : ℝ in atTop, 1 - ε ≤ excess n β r := by
  have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  set δ := ε / ((r : ℝ) + 1) with hδ
  have hδ0 : 0 < δ := div_pos hε hr1
  have hδ1 : δ ≤ ε := div_le_self hε.le (by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)])
  filter_upwards [TwistedFluxSector.flux_gap_vanishes n δ hδ0, eventually_ge_atTop 0]
    with β hflux hβ
  obtain ⟨Ω, F, hΩ, htop, hF, -, horth, hlow⟩ := hflux
  have h := excess_lower n β hβ Ω F hΩ htop hF horth (1 - δ) (by linarith) hlow r hr
  have hb := one_add_mul_le_pow (a := -δ) (by linarith) (r + 1)
  have e : ((r + 1 : ℕ) : ℝ) * (-δ) = -ε := by
    rw [hδ]
    push_cast
    field_simp
  rw [e, ← sub_eq_add_neg, ← sub_eq_add_neg] at hb
  exact hb.trans h

/-- **No time extent gives uniform vacuum dominance in the coupling.** For fixed `n` and `r ≥ 2`, no
bound `excess n β r ≤ δ` with `δ < 1` holds for all large `β`. So the error of `two_point_finite` and
`connected_finite` cannot be made small by a bound uniform in `β` at fixed time extent. This is a limit
on that error term, not a statement that a neutral correlator differs from its vacuum value. -/
theorem excess_not_small (r : ℕ) [NeZero r] (hr : 2 ≤ r) :
    ¬ ∃ δ : ℝ, δ < 1 ∧ ∀ᶠ β : ℝ in atTop, excess n β r ≤ δ := by
  rintro ⟨δ, hδ, hev⟩
  set ε := min ((1 - δ) / 2) (1 / 2) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε1 : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hε2 : ε ≤ (1 - δ) / 2 := min_le_left _ _
  obtain ⟨β, h1, h2⟩ := (hev.and (flux_excess n r hr ε hε0 hε1)).exists
  linarith

end FluxLimit



end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedTraceLaw
