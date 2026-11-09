/- The neutral sector and the time extent of the twisted law, at finite cutoff.

Flips. `flip4` multiplies by `-1` the links of one direction on one slab, on the 4D lattice. It preserves
every plaquette in every plane, so it preserves the law for all coefficients (`plaquetteProduct_flip4`,
`flip4_law`), and it restricts to `TwistedTransfer.flip` on each slice (`slice_flip4`). Adjacent slab flips
differ by a center gauge transformation (`flip_succ_eq_gauge`), so on gauge-invariant functions, in
particular on the range of `T`, a flip depends only on its direction (`flipOp_transfer_indep`). The
`Neutral` of `TargetAGap` and invariance under the three flips of Target A therefore give the same
spectral window (`neutralWindow_iff`, `targetAGap_iff`). All eight characters of `Z2³` occur among
gauge-invariant vectors (`exists_sector_vector`).

The kernel of `T`. For `β > 0`, `T` is injective on gauge-invariant vectors (`transfer_injective_gauge`), so
its kernel is exactly their orthogonal complement (`transfer_eq_zero_iff`). On such vectors the temporal
links integrate away (`smoothing_gauge`). What remains is the exponential of a Gram kernel of the links in
`ℝ⁴` (`kineticWeight_gram`), whose quadratic form is a positive series of squared moments (`moments_zero`),
and moments determine a vector by Stone-Weierstrass (`integral_zero_of_moments`). So at every cutoff with
`β > 0`: each of the eight sectors has a positive top level, strictly below `‖T‖` off the neutral sector
(`sector_top`); the first excited neutral level exists, with a neutral eigenvector orthogonal to the vacuum
(`neutral_level`); both halves of `NeutralWindow` hold (`exists_neutralWindow`), and the window is exactly
`ρ₂ ≤ ρ ≤ ρ₁` for that level `ρ` (`neutralWindow_iff_level`), so `TargetAGap` is a two-sided bound on one
number (`targetAGap_iff_level`). `T` is strictly positive on gauge-invariant vectors (`form_pos_gauge`). This
is a soft argument: it bounds nothing. At `β = 0` the conclusions fail, since `T` has rank one
(`transfer_zero`, `not_neutralWindow_zero`).

Time extent. `chainLaw T n β` is the twisted law on `ZMod T × (ZMod n)³`, for any `T` and `n`. At
`T = n = 2l` it is the law of `TwistedReflection` (`toChain_law`, `toChain_reflect`). Its partition
function is the diagonal integral of the kernel of `T^T` (`chainZ_eq`) and for `T ≥ 2` the trace of `T^T`,
equal to the sum of `λ^T` over one eigenbasis (`chainZ_trace`, `chainZ_spectrum`, `law_partition_trace`).
Two-point functions of slice observables are double kernel integrals (`two_point`); the operator-trace
forms with observables inserted are in `TwistedTraceLaw`, which builds on this file. At even `T` the law is
reflection positive (`chain_reflection_positive`), for arbitrary spatial size. As `T → ∞` at fixed `n` and
`β` the vacuum dominates: `kernel_dominance` and `chainZ_dominance` give a geometric rate from compactness,
with no control in `n` or `β`, and `two_point_limit` gives the limit with no rate. The integrated weight of
a temporal twist is the trace with a flip inserted (`twist_partition`, `trace_flip`).

Not proved: any bound uniform in `n`, so `TargetAGap` stays open; any quantitative bound on `ρ` or on the
sector levels, even at one cutoff; anything at `β < 0`; reflection positivity at odd `T`; the trace identity
at `T = 1`; or a continuum limit. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedPoincare
import UnifiedTheory.Clay.YangMills.Twisted.TwistedFiniteGap
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedNeutral
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 PeriodicTimeReflection PeriodicPlaquetteReflection
open WilsonTimeSlab WilsonSlabOperator TwistedFlat TwistedTransfer TwistedSliceLift TwistedRectangle
open WilsonPositiveGroundState (complexify)
open scoped InnerProductSpace Quaternion

/-! ### The flips of the four-dimensional lattice -/

section FourD
variable (N : ℕ)

/-- Multiply by `-1` all links of direction `μ` on the slab `x μ = c`. -/
def flip4 (μ : Fin 4) (c : ZMod N) (U : Configuration (Vertex N) Q) : Configuration (Vertex N) Q :=
  fun e => if e.2.2.val = μ ∧ e.1 μ = c then ω * U e else U e

theorem flip4_apply (μ : Fin 4) (c : ZMod N) (U : Configuration (Vertex N) Q) (x : Vertex N)
    (ν : Fin 4) :
    flip4 N μ c U ⟨x, step N x ν, forward N x ν⟩ =
      if ν = μ ∧ x μ = c then ω * U ⟨x, step N x ν, forward N x ν⟩
        else U ⟨x, step N x ν, forward N x ν⟩ := rfl

theorem flip4_flip4 (μ : Fin 4) (c : ZMod N) (U : Configuration (Vertex N) Q) :
    flip4 N μ c (flip4 N μ c U) = U := by
  funext e
  unfold flip4
  by_cases h : e.2.2.val = μ ∧ e.1 μ = c
  · simp only [if_pos h]
    rw [← mul_assoc, ω_mul_ω, one_mul]
  · simp only [if_neg h]

theorem flip4_comm (μ ν : Fin 4) (c d : ZMod N) (U : Configuration (Vertex N) Q) :
    flip4 N μ c (flip4 N ν d U) = flip4 N ν d (flip4 N μ c U) := by
  funext e
  unfold flip4
  by_cases h : e.2.2.val = μ ∧ e.1 μ = c <;> by_cases h' : e.2.2.val = ν ∧ e.1 ν = d
  · simp only [if_pos h, if_pos h']
  · simp only [if_pos h, if_neg h']
  · simp only [if_neg h, if_pos h']
  · simp only [if_neg h, if_neg h']

theorem linkValue_flip4 (μ : Fin 4) (c : ZMod N) (U : Configuration (Vertex N) Q) (x : Vertex N)
    (ν : Fin 4) :
    linkValue N Q (flip4 N μ c U) x ν =
      (if ν = μ ∧ x μ = c then ω else 1) * linkValue N Q U x ν := by
  change (if ν = μ ∧ x μ = c then ω * linkValue N Q U x ν else linkValue N Q U x ν) = _
  split_ifs <;> simp

/-- **A flip preserves every plaquette**, in every plane, on every lattice. -/
theorem plaquetteProduct_flip4 (μ : Fin 4) (c : ZMod N) (U : Configuration (Vertex N) Q)
    (x : Vertex N) (α γ : Fin 4) (h : α ≠ γ) :
    plaquetteProduct N Q (flip4 N μ c U) x α γ = plaquetteProduct N Q U x α γ := by
  unfold plaquetteProduct
  simp only [linkValue_flip4]
  have h1 : (if α = μ ∧ (step N x γ) μ = c then ω else 1 : Q) =
      if α = μ ∧ x μ = c then ω else 1 := by
    by_cases hα : α = μ
    · subst hα
      simp [step, h]
    · simp [hα]
  have h2 : (if γ = μ ∧ (step N x α) μ = c then ω else 1 : Q) =
      if γ = μ ∧ x μ = c then ω else 1 := by
    by_cases hγ : γ = μ
    · subst hγ
      simp [step, h.symm]
    · simp [hγ]
  rw [h1, h2]
  refine sign_cancel _ _ ?_ ?_ _ _ _ _
  · split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- The flips commute with the reflection for spatial directions. -/
theorem reflect_flip4_spatial (μ : Fin 4) (hμ : μ ≠ 0) (c : ZMod N)
    (U : Configuration (Vertex N) Q) :
    reflectConfiguration N Q (flip4 N μ c U) = flip4 N μ c (reflectConfiguration N Q U) := by
  funext e
  rcases e with ⟨x, y, ν, hν⟩
  cases hν
  have hb : (edgeEquiv N ⟨x, step N x ν, ⟨ν, rfl⟩⟩).1 =
      (reflectIndex N (x, ν)).1 := rfl
  have hd : (edgeEquiv N ⟨x, step N x ν, ⟨ν, rfl⟩⟩).2.2.val = ν := rfl
  have hc : ν = μ → ((edgeEquiv N ⟨x, step N x ν, ⟨ν, rfl⟩⟩).1 μ = c ↔ x μ = c) := by
    intro hνμ
    rw [hb]
    have hν0 : ν ≠ 0 := hνμ ▸ hμ
    simp [reflectIndex, hν0, reflectVertex, hμ]
  unfold reflectConfiguration flip4
  simp only [hd]
  by_cases hνμ : ν = μ
  · subst hνμ
    simp only [if_neg hμ, true_and, hc rfl]
  · simp [hνμ]

/-- A temporal flip goes to the mirror slab under the reflection. -/
theorem reflect_flip4_time (c : ZMod N) (U : Configuration (Vertex N) Q) :
    reflectConfiguration N Q (flip4 N 0 c U) = flip4 N 0 (-(c + 1)) (reflectConfiguration N Q U) := by
  funext e
  rcases e with ⟨x, y, ν, hν⟩
  cases hν
  have hb : (edgeEquiv N ⟨x, step N x ν, ⟨ν, rfl⟩⟩).1 =
      (reflectIndex N (x, ν)).1 := rfl
  have hd : (edgeEquiv N ⟨x, step N x ν, ⟨ν, rfl⟩⟩).2.2.val = ν := rfl
  unfold reflectConfiguration flip4
  simp only [hd]
  by_cases hν0 : ν = 0
  · subst hν0
    have hcoord : (edgeEquiv N ⟨x, step N x 0, ⟨0, rfl⟩⟩).1 0 = -(x 0 + 1) := by
      rw [hb]
      simp [reflectIndex, reflectVertex, step]
    have hiff : (-(x 0 + 1) = c) ↔ x 0 = -(c + 1) := by
      constructor
      · intro h; rw [← h]; ring
      · intro h; rw [h]; ring
    simp only [true_and, hcoord, if_true, hiff]
    split_ifs
    · exact inv_ω_mul _
    · rfl
  · simp [hν0]

end FourD

section Law
variable (n : ℕ) [NeZero n]

theorem flip4_reference (N : ℕ) [NeZero N] (μ : Fin 4) (c : ZMod N) :
    MeasurePreserving (flip4 N μ c) (referenceMeasure Q (Vertex N)) (referenceMeasure Q (Vertex N)) := by
  refine measurePreserving_pi (fun _ : Edge (Vertex N) => compactHaar Q)
    (fun _ : Edge (Vertex N) => compactHaar Q)
    (f := fun e q => if e.2.2.val = μ ∧ e.1 μ = c then ω * q else q) (fun e => ?_)
  by_cases h : e.2.2.val = μ ∧ e.1 μ = c
  · simp only [if_pos h]
    exact measurePreserving_mul_left _ (ω : Q)
  · simp only [if_neg h]
    exact MeasurePreserving.id _

/-- The flip as a measurable equivalence. -/
def flip4Equiv (N : ℕ) [NeZero N] (μ : Fin 4) (c : ZMod N) :
    Configuration (Vertex N) Q ≃ᵐ Configuration (Vertex N) Q where
  toFun := flip4 N μ c
  invFun := flip4 N μ c
  left_inv := flip4_flip4 N μ c
  right_inv := flip4_flip4 N μ c
  measurable_toFun := (flip4_reference N μ c).measurable
  measurable_invFun := (flip4_reference N μ c).measurable

open TwistedReflection in
theorem action_flip4 (z : PlaquetteIndex (2 * n) → ℝ) (χ : Q → ℂ) (β c' : ℝ) (μ : Fin 4)
    (c : ZMod (2 * n)) (U : Configuration (Vertex (2 * n)) Q) :
    action n Q z χ β c' (flip4 (2 * n) μ c U) = action n Q z χ β c' U := by
  unfold action term
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [plaquetteProduct_flip4 (2 * n) μ c U p.1 _ _ (ne_of_lt p.2.2)]

open TwistedReflection in
/-- **The law is invariant under every flip**, for all coefficients `z`, and in particular for the
twist. -/
theorem flip4_law (z : PlaquetteIndex (2 * n) → ℝ) (χ : Q → ℂ) (hχ : Continuous χ) (β c' : ℝ)
    (μ : Fin 4) (c : ZMod (2 * n)) :
    MeasurePreserving (flip4 (2 * n) μ c) (law n Q z χ β c') (law n Q z χ β c') := by
  unfold law gibbsMeasure
  apply MeasurePreserving.smul_measure
  apply preserves_withDensity (flip4_reference (2 * n) μ c) _
    (Real.continuous_exp.comp (continuous_action n Q z χ hχ β c').neg).measurable.ennreal_ofReal
  intro U
  exact congrArg (fun t : ℝ => ENNReal.ofReal (Real.exp (-t))) (action_flip4 n z χ β c' μ c U)

open TwistedReflection in
/-- **Selection rule.** An observable odd under some flip has vanishing expectation. -/
theorem odd_expectation (z : PlaquetteIndex (2 * n) → ℝ) (χ : Q → ℂ) (hχ : Continuous χ) (β c' : ℝ)
    (μ : Fin 4) (c : ZMod (2 * n)) (F : Configuration (Vertex (2 * n)) Q → ℂ)
    (hodd : ∀ U, F (flip4 (2 * n) μ c U) = -F U) :
    ∫ U, F U ∂law n Q z χ β c' = 0 := by
  have h := (flip4_law n z χ hχ β c' μ c).integral_comp
    (flip4Equiv (2 * n) μ c).measurableEmbedding F
  simp only [hodd, integral_neg] at h
  have h2 : (2 : ℂ) * ∫ U, F U ∂law n Q z χ β c' = 0 := by
    linear_combination -h
  simpa using h2

end Law

/-! ### The slices of a flipped field -/

section Slices
variable (n : ℕ) [NeZero n]

theorem slice_flip4 (i : Fin 3) (c : ZMod n) (U : Configuration (Vertex n) Q) (t : ZMod n) :
    slice (flip4 n i.succ c U) t = TwistedTransfer.flip n i c (slice U t) := by
  funext e
  have hcond : (e.2.succ = i.succ ∧ embed n t e.1 i.succ = c) ↔ (e.2 = i ∧ e.1 i = c) := by
    rw [Fin.succ_inj]
    exact Iff.rfl
  exact if_congr hcond rfl rfl

theorem temporal_flip4 (i : Fin 3) (c : ZMod n) (U : Configuration (Vertex n) Q) (t : ZMod n) :
    temporal (flip4 n i.succ c U) t = temporal U t := by
  funext x
  have h : ¬ ((0 : Fin 4) = i.succ ∧ embed n t x i.succ = c) := fun h =>
    (Fin.succ_ne_zero i) h.1.symm
  change flip4 n i.succ c U ⟨embed n t x, step n (embed n t x) 0, forward n (embed n t x) 0⟩ = _
  rw [flip4_apply, if_neg h]
  rfl

theorem slice_flip4_zero (c : ZMod n) (U : Configuration (Vertex n) Q) (t : ZMod n) :
    slice (flip4 n 0 c U) t = slice U t := by
  funext e
  have h : ¬ (e.2.succ = (0 : Fin 4) ∧ embed n t e.1 0 = c) := fun h => (Fin.succ_ne_zero _) h.1
  change flip4 n 0 c U ⟨embed n t e.1, step n (embed n t e.1) e.2.succ,
    forward n (embed n t e.1) e.2.succ⟩ = _
  rw [flip4_apply, if_neg h]
  rfl

theorem temporal_flip4_zero (c : ZMod n) (U : Configuration (Vertex n) Q) (t : ZMod n)
    (x : SpatialVertex n) :
    temporal (flip4 n 0 c U) t x = if t = c then ω * temporal U t x else temporal U t x := by
  have h : ((0 : Fin 4) = 0 ∧ embed n t x 0 = c) ↔ t = c := by
    simp [embed]
  exact if_congr h rfl rfl

/-! ### The slab flips are one `Z2` per direction, modulo gauge -/

/-- The center gauge transformation on one hyperplane. -/
def hyper (i : Fin 3) (c : ZMod n) : SliceGauge n Q := fun x => if x i = c then ω else 1

theorem conj_ω (a : Q) : ω * a * ω⁻¹ = a := by
  rw [(ω_commute a).eq, mul_assoc, mul_inv_cancel, mul_one]

/-- **Adjacent slab flips differ by a center gauge transformation.** -/
theorem flip_succ_eq_gauge (i : Fin 3) (c : ZMod n) (u : Slice n) :
    TwistedTransfer.flip n i (c + 1) u =
      gaugeSlice (hyper n i (c + 1)) (TwistedTransfer.flip n i c u) := by
  funext e
  rcases e with ⟨x, j⟩
  change (if j = i ∧ x i = c + 1 then ω * u (x, j) else u (x, j)) =
    (if x i = c + 1 then ω else 1) * (if j = i ∧ x i = c then ω * u (x, j) else u (x, j)) *
      (if (spatialStep n x j) i = c + 1 then ω else 1)⁻¹
  by_cases hj : j = i
  · subst hj
    have hB : (spatialStep n x j) j = c + 1 ↔ x j = c := by
      have hs : spatialStep n x j j = x j + 1 := by simp [spatialStep]
      rw [hs]
      exact add_left_inj 1
    simp only [true_and, hB]
    by_cases hA : x j = c + 1 <;> by_cases hC : x j = c
    · simp only [if_pos hA, if_pos hC]
      exact (conj_ω _).symm
    · simp only [if_pos hA, if_neg hC]
      simp
    · simp only [if_neg hA, if_pos hC, one_mul]
      exact (conj_ω _).symm
    · simp only [if_neg hA, if_neg hC]
      simp
  · have hs : (spatialStep n x j) i = x i := spatialStep_other n x j i (Ne.symm hj)
    simp only [hs, hj, false_and, if_false]
    by_cases hA : x i = c + 1
    · simp only [if_pos hA]
      exact (conj_ω _).symm
    · simp only [if_neg hA]
      simp

/-- Gauge-invariant functions see only the direction of a flip, not its slab. -/
theorem gauge_flip_indep {α : Type*} (f : Slice n → α) (hf : ∀ (h : SliceGauge n Q) u, f (gaugeSlice h u) = f u)
    (i : Fin 3) (c c' : ZMod n) (u : Slice n) :
    f (TwistedTransfer.flip n i c u) = f (TwistedTransfer.flip n i c' u) := by
  have hstep (k : ℕ) : f (TwistedTransfer.flip n i (c + k) u) = f (TwistedTransfer.flip n i c u) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ, ← add_assoc, flip_succ_eq_gauge, hf, ih]
  have hc : c' = c + ((c' - c).val : ZMod n) := by
    rw [ZMod.natCast_val, ZMod.cast_id', id]
    ring
  rw [hc, hstep]

/-! ### The neutral subspace and the three flips -/

local notation "μ'" => WilsonSlabOperator.measure n
local notation "F" => TwistedTransfer.flipOp n

theorem flipOp_embed (i : Fin 3) (c : ZMod n) (f : C(Slice n, ℂ)) :
    F i c (ContinuousMap.toLp 2 (μ') ℂ f) = ContinuousMap.toLp 2 (μ') ℂ
      ⟨fun u => f (TwistedTransfer.flip n i c u), f.continuous.comp (TwistedVacuum.flip_continuous n i c)⟩ := by
  have hmp := flip_measurePreserving n i c
  apply Lp.ext
  have h1 : (F i c (ContinuousMap.toLp 2 (μ') ℂ f) : Slice n → ℂ) =ᵐ[μ']
      ((ContinuousMap.toLp 2 (μ') ℂ f : Hilbert n) ∘ TwistedTransfer.flip n i c) :=
    Lp.coeFn_compMeasurePreserving _ hmp
  have h2 := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ') f
  have h3 := hmp.quasiMeasurePreserving.ae_eq_comp h2
  let g : C(Slice n, ℂ) :=
    ⟨fun u => f (TwistedTransfer.flip n i c u), f.continuous.comp (TwistedVacuum.flip_continuous n i c)⟩
  have h4 := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ') g
  exact h1.trans (h3.trans h4.symm)

theorem flipOp_flipOp (i : Fin 3) (c : ZMod n) (f : Hilbert n) : F i c (F i c f) = f := by
  have hmp := flip_measurePreserving n i c
  apply Lp.ext
  have h1 : (F i c (F i c f) : Slice n → ℂ) =ᵐ[μ'] ((F i c f : Hilbert n) ∘ TwistedTransfer.flip n i c) :=
    Lp.coeFn_compMeasurePreserving _ hmp
  have h2 : (F i c f : Slice n → ℂ) =ᵐ[μ'] ((f : Hilbert n) ∘ TwistedTransfer.flip n i c) :=
    Lp.coeFn_compMeasurePreserving _ hmp
  have h3 := hmp.quasiMeasurePreserving.ae_eq_comp h2
  refine h1.trans (h3.trans (Filter.Eventually.of_forall fun u => ?_))
  simp only [Function.comp, flip_flip]

/-- The output of the transfer operator is a gauge-invariant continuous function. -/
theorem representative_gauge (β : ℝ) (v : Hilbert n) (h : SliceGauge n Q) (u : Slice n) :
    TwistedVacuum.representative n β v (gaugeSlice h u) = TwistedVacuum.representative n β v u := by
  unfold TwistedVacuum.representative
  rw [CompactKernelOperator.smoothing_integral, CompactKernelOperator.smoothing_integral]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  dsimp only
  rw [TwistedTreeGauge.twistedKernel_gauge_left]

theorem transfer_eq_embed (β : ℝ) (v : Hilbert n) :
    TwistedTransfer.transfer n β v =
      ContinuousMap.toLp 2 (μ') ℂ (TwistedVacuum.representative n β v) := rfl

/-- **On the range of `T` each flip depends only on its direction.** -/
theorem flipOp_transfer_indep (β : ℝ) (i : Fin 3) (c c' : ZMod n) (v : Hilbert n) :
    F i c (TwistedTransfer.transfer n β v) = F i c' (TwistedTransfer.transfer n β v) := by
  rw [transfer_eq_embed, flipOp_embed, flipOp_embed]
  congr 1
  ext u
  exact gauge_flip_indep n _ (representative_gauge n β v) i c c' u

/-- Invariance under the three flips, one per direction. This is the `Z2³` of Target A. -/
def Neutral3 (f : Hilbert n) : Prop := ∀ i, F i 0 f = f

theorem Neutral.three {f : Hilbert n} (hf : Neutral n f) : Neutral3 n f := fun i => hf i 0

/-- On the range of `T`, `Z2³` invariance is the same as invariance under all slab flips. -/
theorem neutral_transfer_iff (β : ℝ) (v : Hilbert n) :
    Neutral n (TwistedTransfer.transfer n β v) ↔ Neutral3 n (TwistedTransfer.transfer n β v) := by
  refine ⟨Neutral.three n, fun h i c => ?_⟩
  rw [flipOp_transfer_indep n β i c 0, h i]

/-- A `Z2³`-invariant vector has `Z2³`-invariant image, hence a neutral image. -/
theorem neutral_transfer_of_three (β : ℝ) {f : Hilbert n} (hf : Neutral3 n f) :
    Neutral n (TwistedTransfer.transfer n β f) :=
  (neutral_transfer_iff n β f).mpr fun i => by rw [← transfer_flipOp, hf i]

/-- The closed neutral subspace. -/
def neutralSubspace : Submodule ℂ (Hilbert n) where
  carrier := {f | Neutral n f}
  add_mem' := by
    intro a b ha hb i c
    rw [map_add, ha i c, hb i c]
  zero_mem' := fun i c => map_zero _
  smul_mem' := by
    intro k a ha i c
    rw [map_smulₛₗ, ha i c]
    rfl

theorem neutralSubspace_closed : IsClosed (neutralSubspace n : Set (Hilbert n)) := by
  have : (neutralSubspace n : Set (Hilbert n)) = ⋂ i, ⋂ c, {f | F i c f = f} := by
    ext f
    simp [neutralSubspace, Neutral]
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun c =>
    isClosed_eq (F i c).continuous continuous_id

instance : CompleteSpace (neutralSubspace n) := (neutralSubspace_closed n).completeSpace_coe

/-- The transfer operator maps the neutral subspace to itself. -/
theorem transfer_mem_neutral (β : ℝ) {f : Hilbert n} (hf : f ∈ neutralSubspace n) :
    TwistedTransfer.transfer n β f ∈ neutralSubspace n := fun i c => by
  rw [← transfer_flipOp, hf i c]

/-- **`T` kills a `Z2³`-invariant vector orthogonal to the neutral subspace.** -/
theorem transfer_eq_zero_of_orthogonal (β : ℝ) {b : Hilbert n} (hb : Neutral3 n b)
    (hperp : b ∈ (neutralSubspace n)ᗮ) : TwistedTransfer.transfer n β b = 0 := by
  have hsym : ∀ x y, inner ℂ (TwistedTransfer.transfer n β x) y =
      inner ℂ x (TwistedTransfer.transfer n β y) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (transfer_selfAdjoint n β))
  set t := TwistedTransfer.transfer n β b with ht
  have ht' : t ∈ neutralSubspace n := neutral_transfer_of_three n β hb
  have hTt := transfer_mem_neutral n β ht'
  have h0 : inner ℂ t t = (0 : ℂ) := by
    conv_lhs => rw [ht, hsym]
    exact (Submodule.mem_orthogonal' _ _).mp hperp _ hTt
  exact inner_self_eq_zero.mp h0

/-- Every `Z2³`-invariant vector has a neutral vector of no larger norm with the same image under
`T` and the same pairing with neutral vectors. -/
theorem exists_neutral_part (β : ℝ) {f : Hilbert n} (hf : Neutral3 n f) :
    ∃ a : Hilbert n, Neutral n a ∧ ‖a‖ ≤ ‖f‖ ∧
      TwistedTransfer.transfer n β a = TwistedTransfer.transfer n β f ∧
      ∀ Ω, Neutral n Ω → inner ℂ Ω a = (inner ℂ Ω f : ℂ) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.exists_add_mem_mem_orthogonal (K := neutralSubspace n) f
  have hb3 : Neutral3 n b := by
    intro i
    have h1 := hf i
    rw [map_add, ha i 0] at h1
    exact add_left_cancel h1
  refine ⟨a, ha, ?_, ?_, fun Ω hΩ => ?_⟩
  · have horth : inner ℂ a b = (0 : ℂ) := (Submodule.mem_orthogonal _ _).mp hb a ha
    have hsq := norm_add_sq (𝕜 := ℂ) a b
    rw [horth] at hsq
    simp only [map_zero, mul_zero, add_zero] at hsq
    have : ‖a‖ ^ 2 ≤ ‖a + b‖ ^ 2 := by
      rw [hsq]
      nlinarith [sq_nonneg ‖b‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
  · rw [map_add, transfer_eq_zero_of_orthogonal n β hb3 hb, add_zero]
  · rw [inner_add_right, (Submodule.mem_orthogonal _ _).mp hb Ω hΩ, add_zero]

/-- The window of `TwistedTransfer.NeutralWindow`, with neutrality read as invariance under the
three flips. -/
def NeutralWindow3 (β ρ₁ ρ₂ : ℝ) : Prop :=
  ∃ Ω : Hilbert n, ‖Ω‖ = 1 ∧ TwistedTransfer.transfer n β Ω = ‖TwistedTransfer.transfer n β‖ • Ω ∧
    Neutral3 n Ω ∧
    (∀ f, Neutral3 n f → inner ℂ Ω f = 0 →
      ‖TwistedTransfer.transfer n β f‖ ≤ ρ₁ * ‖TwistedTransfer.transfer n β‖ * ‖f‖) ∧
    ∃ f, Neutral3 n f ∧ inner ℂ Ω f = 0 ∧ f ≠ 0 ∧
      ρ₂ * ‖TwistedTransfer.transfer n β‖ * ‖f‖ ≤ ‖TwistedTransfer.transfer n β f‖

theorem norm_transfer_pos (β : ℝ) : 0 < ‖TwistedTransfer.transfer n β‖ :=
  norm_pos_iff.mpr (transfer_ne_zero n β)

/-- **The two readings of "neutral" give the same spectral window**: the `Neutral` of `TargetAGap`,
invariance under every slab flip, and the `Z2³` of Target A. -/
theorem neutralWindow_iff (β ρ₁ ρ₂ : ℝ) (h₁ : 0 ≤ ρ₁) (h₂ : 0 < ρ₂) :
    NeutralWindow n β ρ₁ ρ₂ ↔ NeutralWindow3 n β ρ₁ ρ₂ := by
  have hlam := norm_transfer_pos n β
  constructor
  · rintro ⟨Ω, hn, htop, hΩ, hc, f, hfn, hfo, hf0, hfl⟩
    refine ⟨Ω, hn, htop, Neutral.three n hΩ, fun g hg hgo => ?_, f, Neutral.three n hfn, hfo, hf0, hfl⟩
    obtain ⟨a, ha, hle, hT, hp⟩ := exists_neutral_part n β hg
    rw [← hT]
    refine (hc a ha (by rw [hp Ω hΩ, hgo])).trans ?_
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  · rintro ⟨Ω, hn, htop, hΩ, hc, f, hfn, hfo, hf0, hfl⟩
    have hΩ' : Neutral n Ω := by
      have hΩT : Ω = TwistedTransfer.transfer n β (((‖TwistedTransfer.transfer n β‖ : ℂ)⁻¹) • Ω) := by
        rw [map_smul, htop, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
        change Ω = (((‖TwistedTransfer.transfer n β‖ : ℂ)⁻¹) * (‖TwistedTransfer.transfer n β‖ : ℂ)) • Ω
        rw [inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hlam.ne'), one_smul]
      rw [hΩT]
      apply (neutral_transfer_iff n β _).mpr
      rw [← hΩT]
      exact hΩ
    obtain ⟨a, ha, hle, hT, hp⟩ := exists_neutral_part n β hfn
    have hpos : 0 < ρ₂ * ‖TwistedTransfer.transfer n β‖ * ‖f‖ := by
      have := norm_pos_iff.mpr hf0
      positivity
    refine ⟨Ω, hn, htop, hΩ', fun g hg hgo => hc g (Neutral.three n hg) hgo, a, ha,
      by rw [hp Ω hΩ', hfo], ?_, ?_⟩
    · rintro rfl
      rw [map_zero] at hT
      rw [← hT, norm_zero] at hfl
      linarith only [hfl, hpos]
    · rw [hT]
      exact (mul_le_mul_of_nonneg_left hle (by positivity)).trans hfl

/-- `TargetAGap` read with the three flips. -/
def TargetAGap3 (b : ℝ) : Prop :=
  ∃ β₀ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ (n : ℕ) [NeZero n], 2 ≤ n →
    ∀ β, b * Real.log n + β₀ ≤ β →
      NeutralWindow3 n β (Real.exp (-c / n)) (Real.exp (-C / n))

theorem targetAGap_iff (b : ℝ) : TargetAGap b ↔ TargetAGap3 b := by
  constructor
  · rintro ⟨β₀, c, C, hc, hcC, h⟩
    refine ⟨β₀, c, C, hc, hcC, fun m _ hm β hβ => ?_⟩
    exact (neutralWindow_iff m β _ _ (Real.exp_pos _).le (Real.exp_pos _)).mp (h m hm β hβ)
  · rintro ⟨β₀, c, C, hc, hcC, h⟩
    refine ⟨β₀, c, C, hc, hcC, fun m _ hm β hβ => ?_⟩
    exact (neutralWindow_iff m β _ _ (Real.exp_pos _).le (Real.exp_pos _)).mpr (h m hm β hβ)

/-! ### The eight sectors -/

/-- The sign of a character value. -/
def sgn (b : Bool) : ℂ := if b then -1 else 1

/-- The sector of a character of `Z2³`: every flip acts by the sign of its direction. -/
def Sector (e : Fin 3 → Bool) (f : Hilbert n) : Prop := ∀ i c, F i c f = sgn (e i) • f

theorem sector_false_iff (f : Hilbert n) : Sector n (fun _ => false) f ↔ Neutral n f := by
  simp [Sector, Neutral, sgn]

theorem transfer_sector (β : ℝ) (e : Fin 3 → Bool) {f : Hilbert n} (hf : Sector n e f) :
    Sector n e (TwistedTransfer.transfer n β f) := fun i c => by
  rw [← transfer_flipOp, hf i c, map_smul]

/-- Distinct sectors are orthogonal. -/
theorem sector_orthogonal (e e' : Fin 3 → Bool) (hne : e ≠ e') {f g : Hilbert n}
    (hf : Sector n e f) (hg : Sector n e' g) : inner ℂ f g = (0 : ℂ) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have h := (F i 0).inner_map_map f g
  rw [hf i 0, hg i 0, inner_smul_left, inner_smul_right] at h
  have hs : (starRingEnd ℂ) (sgn (e i)) * sgn (e' i) = -1 := by
    cases he : e i <;> cases he' : e' i <;> simp_all [sgn]
  rw [← mul_assoc, hs] at h
  linear_combination (-1 / 2 : ℂ) * h

/-! ### Every sector occurs among gauge-invariant vectors -/

/-- The winding holonomy of a slice in direction `i` through the base point. -/
def wind (i : Fin 3) (u : Slice n) : Q := run (lift n u) i.succ (TwistedSliceLift.base n) n

/-- Its real part, the trace of the Polyakov line in direction `i`. -/
def windRe (i : Fin 3) (u : Slice n) : ℝ := ((wind n i u : Q) : ℍ[ℝ]).re

theorem run_lift_continuous' (i : Fin 3) (x : Vertex n) (m : ℕ) :
    Continuous fun u : Slice n => run (lift n u) i.succ x m := by
  induction m with
  | zero => exact continuous_const
  | succ m ih =>
    simp only [run]
    refine ih.mul ?_
    exact continuous_apply ((sp n (walk i.succ x m), i))

theorem windRe_continuous (i : Fin 3) : Continuous (windRe n i) := by
  unfold windRe wind
  exact Quaternion.continuous_re.comp (continuous_subtype_val.comp (run_lift_continuous' n i _ _))

theorem windRe_gauge (i : Fin 3) (h : SliceGauge n Q) (u : Slice n) :
    windRe n i (gaugeSlice h u) = windRe n i u := by
  unfold windRe wind
  rw [lift_gauge, TwistedSliceLift.run_act, walk_card]
  set g := h (sp n (TwistedSliceLift.base n))
  set W := run (lift n u) i.succ (TwistedSliceLift.base n) n
  change ((g : ℍ[ℝ]) * (W : ℍ[ℝ]) * ((g⁻¹ : Q) : ℍ[ℝ])).re = _
  have : ((g⁻¹ : Q) : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 := congrArg Subtype.val (inv_mul_cancel g)
  rw [mul_assoc, TwistedActionJet.re_comm, mul_assoc, this, mul_one]

/-- The flip in another direction leaves a line unchanged. -/
theorem run_flip_other (i j : Fin 3) (hij : i ≠ j) (c : ZMod n) (u : Slice n) (x : Vertex n)
    (m : ℕ) :
    run (lift n (TwistedTransfer.flip n j c u)) i.succ x m = run (lift n u) i.succ x m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [run, ih, lift_succ]
    congr 1
    unfold TwistedTransfer.flip
    simp [hij]

/-- The flip in its own direction crosses a line exactly once. -/
theorem run_flip_same (i : Fin 3) (c : ZMod n) (u : Slice n) (m : ℕ) (hm : m ≤ n) :
    run (lift n (TwistedTransfer.flip n i c u)) i.succ (TwistedSliceLift.base n) m =
      (if c.val < m then ω else 1) * run (lift n u) i.succ (TwistedSliceLift.base n) m := by
  induction m with
  | zero => simp [run]
  | succ m ih =>
    have hm' : m < n := hm
    have hc : (sp n (walk i.succ (TwistedSliceLift.base n) m)) i = (m : ZMod n) := by
      change walk i.succ (TwistedSliceLift.base n) m i.succ = _
      rw [walk_apply_same]
      simp
    have hiff : ((m : ZMod n) = c) ↔ c.val = m := by
      constructor
      · intro h
        rw [← h, ZMod.val_natCast_of_lt hm']
      · intro h
        rw [← h, ZMod.natCast_zmod_val]
    simp only [run, ih (Nat.le_of_lt hm'), lift_succ]
    unfold TwistedTransfer.flip
    simp only [true_and, hc, hiff]
    by_cases h1 : c.val = m
    · have h2 : ¬ c.val < m := by omega
      have h3 : c.val < m + 1 := by omega
      simp only [if_pos h1, if_neg h2, if_pos h3, one_mul]
      rw [← mul_assoc, ← (ω_commute _).eq, mul_assoc]
    · by_cases h2 : c.val < m
      · have h3 : c.val < m + 1 := by omega
        simp only [if_neg h1, if_pos h2, if_pos h3, mul_assoc]
      · have h3 : ¬ c.val < m + 1 := by omega
        simp only [if_neg h1, if_neg h2, if_neg h3, one_mul]

theorem windRe_flip_same (i : Fin 3) (c : ZMod n) (u : Slice n) :
    windRe n i (TwistedTransfer.flip n i c u) = -windRe n i u := by
  unfold windRe wind
  rw [run_flip_same n i c u n le_rfl, if_pos (ZMod.val_lt c), coe_ω_mul]
  simp

theorem windRe_flip_other (i j : Fin 3) (hij : i ≠ j) (c : ZMod n) (u : Slice n) :
    windRe n i (TwistedTransfer.flip n j c u) = windRe n i u := by
  unfold windRe wind
  rw [run_flip_other n i j hij]

theorem windRe_one (i : Fin 3) : windRe n i (fun _ => 1) = 1 := by
  have h : ∀ m : ℕ, run (lift n (fun _ => (1 : Q))) i.succ (TwistedSliceLift.base n) m = 1 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      simp only [run, ih, lift_succ, one_mul]
  unfold windRe wind
  rw [h]
  simp

/-- The product of the traces of the Polyakov lines odd under the character `e`. -/
def sectorObs (e : Fin 3 → Bool) : C(Slice n, ℝ) :=
  ⟨fun u => ∏ i, if e i then windRe n i u else 1,
    continuous_finset_prod _ fun i _ => by
      by_cases h : e i
      · simpa only [h, if_true] using windRe_continuous n i
      · simpa only [h, if_false] using continuous_const⟩

theorem sectorObs_apply (e : Fin 3 → Bool) (u : Slice n) :
    sectorObs n e u = ∏ i, if e i then windRe n i u else 1 := rfl

theorem sectorObs_flip (e : Fin 3 → Bool) (j : Fin 3) (c : ZMod n) (u : Slice n) :
    sectorObs n e (TwistedTransfer.flip n j c u) = (if e j then -1 else 1) * sectorObs n e u := by
  rw [sectorObs_apply, sectorObs_apply]
  have hi (i : Fin 3) : (if e i then windRe n i (TwistedTransfer.flip n j c u) else 1) =
      (if i = j ∧ e i = true then (-1 : ℝ) else 1) * (if e i then windRe n i u else 1) := by
    by_cases hij : i = j
    · subst hij
      by_cases h : e i
      · simp [h, windRe_flip_same]
      · simp [h]
    · by_cases h : e i
      · simp [h, hij, windRe_flip_other n i j hij]
      · simp [h]
  simp only [hi, Finset.prod_mul_distrib]
  congr 1
  fin_cases j <;> simp [Fin.prod_univ_three]

theorem sectorObs_gauge (e : Fin 3 → Bool) (h : SliceGauge n Q) (u : Slice n) :
    sectorObs n e (gaugeSlice h u) = sectorObs n e u := by
  rw [sectorObs_apply, sectorObs_apply]
  simp only [windRe_gauge]

theorem sectorObs_one (e : Fin 3 → Bool) : sectorObs n e (fun _ => 1) = 1 := by
  rw [sectorObs_apply]
  simp only [windRe_one, ite_self, Finset.prod_const_one]

/-- **Each of the eight characters of `Z2³` occurs.** Every sector contains a nonzero vector
represented by a continuous gauge-invariant function: a product of traces of Polyakov lines. So the
flips modulo gauge act on gauge-invariant vectors as exactly `Z2³`. That `T` is nonzero on the sector
is `sector_top`. -/
theorem exists_sector_vector (e : Fin 3 → Bool) :
    ∃ g : C(Slice n, ℝ), (∀ (h : SliceGauge n Q) u, g (gaugeSlice h u) = g u) ∧
      ContinuousMap.toLp 2 (μ') ℂ (complexify g) ≠ 0 ∧
      Sector n e (ContinuousMap.toLp 2 (μ') ℂ (complexify g)) := by
  haveI hmeas : Measure.IsOpenPosMeasure (μ') := by
    change (Measure.pi fun _ : SpatialVertex n × Fin 3 => RegulatedGauge.compactHaar Q).IsOpenPosMeasure
    haveI : (RegulatedGauge.compactHaar Q).IsOpenPosMeasure := GibbsFullSupport.compactHaar_openPos Q
    infer_instance
  refine ⟨sectorObs n e, sectorObs_gauge n e, ?_, fun i c => ?_⟩
  · intro h0
    have hne : complexify (sectorObs n e) = 0 := by
      apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) (μ')
      rw [h0, map_zero]
    have hv := DFunLike.congr_fun hne (fun _ => 1)
    change ((sectorObs n e (fun _ => 1) : ℝ) : ℂ) = 0 at hv
    rw [sectorObs_one] at hv
    simp at hv
  · rw [flipOp_embed, ← map_smul]
    congr 1
    ext u
    change ((sectorObs n e (TwistedTransfer.flip n i c u) : ℝ) : ℂ) = sgn (e i) * ((sectorObs n e u : ℝ) : ℂ)
    rw [sectorObs_flip]
    unfold sgn
    split_ifs <;> simp

end Slices

open scoped ComplexConjugate

section Chain
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- The composition of continuous kernels. -/
def compK (K L : C(X × X, ℝ)) : C(X × X, ℝ) :=
  ⟨fun p => ∫ w, K (p.1, w) * L (w, p.2) ∂μ, by
    let f : X × X → X → ℝ := fun p w => K (p.1, w) * L (w, p.2)
    have hf : Continuous f.uncurry := by
      unfold f Function.uncurry
      fun_prop
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous (μ := μ) hf isCompact_univ)⟩

theorem compK_apply (K L : C(X × X, ℝ)) (x y : X) :
    compK μ K L (x, y) = ∫ w, K (x, w) * L (w, y) ∂μ := rfl

/-- The kernel of a product of `m + 1` transfer steps with step kernels `K 0, …, K m`. -/
def chainK (K : ℕ → C(X × X, ℝ)) : ℕ → C(X × X, ℝ)
  | 0 => K 0
  | m + 1 => compK μ (chainK K m) (K (m + 1))

/-- The integrand of an open chain: `x = p₀, w₁, …, w_m, y = p_{m+1}`. -/
def openW (K : ℕ → X × X → ℝ) : (m : ℕ) → X → (Fin m → X) → X → ℝ
  | 0, x, _, y => K 0 (x, y)
  | m + 1, x, w, y => openW K m x (fun i => w i.castSucc) (w (Fin.last m)) *
      K (m + 1) (w (Fin.last m), y)

theorem openW_continuous (K : ℕ → C(X × X, ℝ)) (m : ℕ) :
    Continuous fun q : X × (Fin m → X) × X =>
      openW (fun j => K j) m q.1 q.2.1 q.2.2 := by
  induction m with
  | zero =>
    simp only [openW]
    fun_prop
  | succ m ih =>
    simp only [openW]
    refine Continuous.mul ?_ ?_
    · have := ih.comp (f := fun q : X × (Fin (m + 1) → X) × X =>
        (q.1, (fun i => q.2.1 i.castSucc), q.2.1 (Fin.last m))) (by fun_prop)
      exact this
    · fun_prop

/-- Integrating the interior of an open chain gives the composed kernel. -/
theorem open_integral (K : ℕ → C(X × X, ℝ)) (m : ℕ) (x y : X) :
    ∫ w : Fin m → X, openW (fun j => K j) m x w y ∂Measure.pi (fun _ => μ) = chainK μ K m (x, y) := by
  induction m generalizing y with
  | zero =>
    simp [openW, chainK]
  | succ m ih =>
    have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) (Fin.last m))
    let G : X × (Fin m → X) → ℝ := fun z =>
      openW (fun j => K j) m x z.2 z.1 * K (m + 1) (z.1, y)
    have hG : Continuous G := by
      refine Continuous.mul ?_ (by fun_prop)
      exact (openW_continuous K m).comp (f := fun z : X × (Fin m → X) => (x, z.2, z.1)) (by fun_prop)
    have hcomp : (fun w : Fin (m + 1) → X => openW (fun j => K j) (m + 1) x w y) =
        G ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => X) (Fin.last m)) := by
      funext w
      simp only [openW, G, Function.comp]
      congr 2
      funext i
      simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
      rfl
    have hint := hmp.integral_comp (MeasurableEquiv.measurableEmbedding _) G
    rw [hcomp]
    change ∫ w, G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => X) (Fin.last m)) w) ∂_ = _
    rw [hint]
    rw [integral_prod _ (hG.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    simp only [chainK, compK_apply, G]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    rw [integral_mul_const, ih]

theorem openW_eq_prod (K : ℕ → X × X → ℝ) (p : ℕ → X) (k : ℕ) :
    openW K k (p 0) (fun i => p (i + 1)) (p (k + 1)) =
      ∏ j ∈ Finset.range (k + 1), K j (p j, p (j + 1)) := by
  induction k with
  | zero => simp [openW]
  | succ k ih =>
    rw [Finset.prod_range_succ, ← ih]
    simp [openW]

/-- The cyclic time index as `Fin`. -/
def timeEquiv (m : ℕ) : ZMod (m + 1) ≃ Fin (m + 1) where
  toFun t := ⟨t.val, ZMod.val_lt t⟩
  invFun b := (b.val : ZMod (m + 1))
  left_inv t := ZMod.natCast_zmod_val t
  right_inv b := Fin.ext (ZMod.val_natCast_of_lt b.2)

theorem prod_zmod (m : ℕ) (g : ZMod (m + 1) → ℝ) :
    ∏ t, g t = ∏ j ∈ Finset.range (m + 1), g (j : ZMod (m + 1)) := by
  rw [← Fin.prod_univ_eq_prod_range (fun j => g (j : ZMod (m + 1)))]
  exact ((timeEquiv m).symm.prod_comp g).symm

/-- **The cycle integral.** The periodic chain of `m + 1` steps with independent slices integrates
to the diagonal of the composed kernel. -/
theorem cycle_integral (m : ℕ) (K : ZMod (m + 1) → C(X × X, ℝ)) :
    ∫ u : ZMod (m + 1) → X, ∏ t, K t (u t, u (t + 1)) ∂Measure.pi (fun _ => μ) =
      ∫ x, chainK μ (fun j => K (j : ZMod (m + 1))) m (x, x) ∂μ := by
  set K' : ℕ → C(X × X, ℝ) := fun j => K (j : ZMod (m + 1)) with hK'
  have hmp₁ := measurePreserving_piCongrLeft (fun _ : Fin (m + 1) => μ) (timeEquiv m)
  have hmp₂ := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0
  have happ (u : ZMod (m + 1) → X) (b : Fin (m + 1)) :
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (m + 1) => X) (timeEquiv m)) u b =
        u (b.val : ZMod (m + 1)) := by
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    rfl
  let H : X × (Fin m → X) → ℝ := fun z => openW (fun j => K' j) m z.1 z.2 z.1
  have hH : Continuous H :=
    (openW_continuous K' m).comp (f := fun z : X × (Fin m → X) => (z.1, z.2, z.1)) (by fun_prop)
  have hinteg (u : ZMod (m + 1) → X) : ∏ t, K t (u t, u (t + 1)) =
      H ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => X) 0)
        ((MeasurableEquiv.piCongrLeft (fun _ : Fin (m + 1) => X) (timeEquiv m)) u)) := by
    rw [prod_zmod]
    let p : ℕ → X := fun k => u (k : ZMod (m + 1))
    have hp : p 0 = p (m + 1) := by
      simp only [p]
      congr 1
      simp
    have h1 := openW_eq_prod (fun j => K' j) p m
    rw [← hp] at h1
    have h2 : H ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => X) 0)
        ((MeasurableEquiv.piCongrLeft (fun _ : Fin (m + 1) => X) (timeEquiv m)) u)) =
        openW (fun j => K' j) m (p 0) (fun i => p (i + 1)) (p 0) := by
      have h0 (v : Fin (m + 1) → X) : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => X) 0) v =
          (v 0, fun j => v j.succ) := by
        refine Prod.ext rfl (funext fun j => ?_)
        change v (Fin.succAbove 0 j) = _
        rw [Fin.zero_succAbove]
      simp only [H, h0, happ]
      rfl
    rw [h2, h1]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [p, Nat.cast_add, Nat.cast_one]
    rfl
  simp only [hinteg]
  have s1 := hmp₁.integral_comp (MeasurableEquiv.measurableEmbedding _)
    (fun v => H ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => X) 0) v))
  have s2 := hmp₂.integral_comp (MeasurableEquiv.measurableEmbedding _) H
  have s1' : ∫ u : ZMod (m + 1) → X, H ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => X) 0)
        ((MeasurableEquiv.piCongrLeft (fun _ : Fin (m + 1) => X) (timeEquiv m)) u))
      ∂Measure.pi (fun _ => μ) =
      ∫ v, H ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => X) 0) v)
        ∂Measure.pi (fun _ => μ) := s1
  rw [s1', s2, integral_prod _ (hH.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact open_integral μ K' m x x

/-! ### The composed kernel is the operator product -/

theorem compK_assoc (K L M : C(X × X, ℝ)) :
    compK μ (compK μ K L) M = compK μ K (compK μ L M) := by
  ext ⟨x, y⟩
  simp only [compK_apply]
  simp_rw [← integral_mul_const, ← integral_const_mul]
  have hi : Integrable (fun z : X × X => K (x, z.2) * L (z.2, z.1) * M (z.1, y)) (μ.prod μ) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)
  rw [integral_integral_swap hi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  dsimp only
  ring

open CompactKernelOperator in
theorem smoothing_compK (K L : C(X × X, ℝ)) (f : C(X, ℂ)) (x : X) :
    smoothing μ (compK μ K L) (ContinuousMap.toLp 2 μ ℂ f) x =
      smoothing μ K (ContinuousMap.toLp 2 μ ℂ (smoothing μ L (ContinuousMap.toLp 2 μ ℂ f))) x := by
  rw [smoothing_continuous_input, smoothing_continuous_input]
  simp_rw [smoothing_continuous_input, compK_apply, ← integral_complex_ofReal,
    ← integral_mul_const, ← integral_const_mul]
  have hi : Integrable (fun z : X × X => ((K (x, z.2) * L (z.2, z.1) : ℝ) : ℂ) * f z.1) (μ.prod μ) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)
  rw [integral_integral_swap hi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  dsimp only
  push_cast
  ring

variable [μ.WeaklyRegular]

open CompactKernelOperator in
theorem operator_compK (K L : C(X × X, ℝ)) :
    operator μ (compK μ K L) = (operator μ K).comp (operator μ L) := by
  refine DFunLike.coe_injective
    ((ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num : (2 : ENNReal) ≠ ⊤)).equalizer
    (operator μ (compK μ K L)).continuous ((operator μ K).comp (operator μ L)).continuous ?_)
  funext f
  change ContinuousMap.toLp 2 μ ℂ (smoothing μ (compK μ K L) (ContinuousMap.toLp 2 μ ℂ f)) =
    ContinuousMap.toLp 2 μ ℂ (smoothing μ K
      (ContinuousMap.toLp 2 μ ℂ (smoothing μ L (ContinuousMap.toLp 2 μ ℂ f))))
  congr 1
  ext x
  exact smoothing_compK μ K L f x

/-- The kernel of `T^(m+1)`. -/
def powK (K : C(X × X, ℝ)) (m : ℕ) : C(X × X, ℝ) := chainK μ (fun _ => K) m

theorem powK_zero (K : C(X × X, ℝ)) : powK μ K 0 = K := rfl

theorem powK_succ (K : C(X × X, ℝ)) (m : ℕ) : powK μ K (m + 1) = compK μ (powK μ K m) K := rfl

open CompactKernelOperator in
/-- **The composed kernel is the operator power.** -/
theorem operator_powK (K : C(X × X, ℝ)) (m : ℕ) :
    operator μ (powK μ K m) = (operator μ K) ^ (m + 1) := by
  induction m with
  | zero => simp [powK_zero]
  | succ m ih =>
    rw [powK_succ, operator_compK, ih, pow_succ]
    rfl

theorem powK_add (K : C(X × X, ℝ)) (a b : ℕ) :
    powK μ K (a + b + 1) = compK μ (powK μ K a) (powK μ K b) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [show a + (b + 1) + 1 = (a + b + 1) + 1 from rfl, powK_succ, ih, powK_succ, compK_assoc]

theorem powK_symm (K : C(X × X, ℝ)) (hK : ∀ x y, K (x, y) = K (y, x)) (m : ℕ) (x y : X) :
    powK μ K m (x, y) = powK μ K m (y, x) := by
  induction m generalizing x y with
  | zero => exact hK x y
  | succ m ih =>
    have h := powK_add μ K 0 m
    rw [show 0 + m + 1 = m + 1 by omega] at h
    rw [powK_succ]
    conv_rhs => rw [← powK_succ, h]
    simp only [compK_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    dsimp only
    rw [ih x w, powK_zero, hK w y]
    ring

/-! ### The trace -/

open CompactKernelOperator

theorem norm_embed_sq (f : C(X, ℂ)) :
    ‖ContinuousMap.toLp 2 μ ℂ f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (ContinuousMap.toLp 2 μ ℂ f)
  rw [MeasureTheory.ContinuousMap.inner_toLp] at h
  have h2 : (fun x => f x * conj (f x)) = fun x => (((‖f x‖ ^ 2 : ℝ)) : ℂ) := by
    funext x
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h2, integral_complex_ofReal] at h
  have h3 : ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) = ((‖ContinuousMap.toLp 2 μ ℂ f‖ ^ 2 : ℝ) : ℂ) := by
    rw [h]
    push_cast
    rfl
  exact (Complex.ofReal_injective h3).symm

theorem smoothing_sq_integrable (K : C(X × X, ℝ)) (f : Hilbert μ) :
    Integrable (fun x => ‖smoothing μ K f x‖ ^ 2) μ :=
  Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)

/-- A continuous kernel gives a Hilbert-Schmidt operator. -/
theorem hs_summable {ι : Type*} (b : HilbertBasis ι ℂ (Hilbert μ)) (K : C(X × X, ℝ)) :
    Summable fun k => ‖operator μ K (b k)‖ ^ 2 := by
  refine summable_of_sum_le (c := ‖K‖ ^ 2) (fun _ => by positivity) fun s => ?_
  have h1 (k : ι) : ‖operator μ K (b k)‖ ^ 2 = ∫ x, ‖smoothing μ K (b k) x‖ ^ 2 ∂μ :=
    norm_embed_sq μ _
  simp only [h1]
  rw [← integral_finset_sum _ fun k _ => smoothing_sq_integrable μ K (b k)]
  have hpt (x : X) : ∑ k ∈ s, ‖smoothing μ K (b k) x‖ ^ 2 ≤ ‖K‖ ^ 2 := by
    have hB := b.orthonormal.sum_inner_products_le (x := row μ K x) (s := s)
    refine le_trans ?_ (hB.trans (pow_le_pow_left₀ (norm_nonneg _) (row_norm_le μ K x) 2))
    refine Finset.sum_le_sum fun k _ => ?_
    change ‖inner ℂ (row μ K x) (b k)‖ ^ 2 ≤ _
    rw [norm_inner_symm]
  calc ∫ x, ∑ k ∈ s, ‖smoothing μ K (b k) x‖ ^ 2 ∂μ ≤ ∫ _, ‖K‖ ^ 2 ∂μ := by
        refine integral_mono (integrable_finset_sum _ fun k _ => smoothing_sq_integrable μ K (b k))
          (integrable_const _) hpt
    _ = ‖K‖ ^ 2 := by simp

/-- **The Hilbert-Schmidt pairing as a sum over a basis.** -/
theorem trace_comp {ι : Type*} [Countable ι] (b : HilbertBasis ι ℂ (Hilbert μ)) (K L : C(X × X, ℝ)) :
    HasSum (fun k => inner ℂ (operator μ L (b k)) (operator μ K (b k)))
      ((∫ x, ∫ w, K (x, w) * L (x, w) ∂μ ∂μ : ℝ) : ℂ) := by
  let G : ι → X → ℂ := fun k x => smoothing μ K (b k) x * conj (smoothing μ L (b k) x)
  have hinner (k : ι) : inner ℂ (operator μ L (b k)) (operator μ K (b k)) = ∫ x, G k x ∂μ :=
    MeasureTheory.ContinuousMap.inner_toLp μ _ _
  have hint (k : ι) : Integrable (G k) μ := by
    refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
    exact (smoothing μ K (b k)).continuous.mul
      (Complex.continuous_conj.comp (smoothing μ L (b k)).continuous)
  have hle (k : ι) : ∫ x, ‖G k x‖ ∂μ ≤
      (‖operator μ K (b k)‖ ^ 2 + ‖operator μ L (b k)‖ ^ 2) / 2 := by
    rw [show ‖operator μ K (b k)‖ ^ 2 = ∫ x, ‖smoothing μ K (b k) x‖ ^ 2 ∂μ from norm_embed_sq μ _,
      show ‖operator μ L (b k)‖ ^ 2 = ∫ x, ‖smoothing μ L (b k) x‖ ^ 2 ∂μ from norm_embed_sq μ _,
      ← integral_add (smoothing_sq_integrable μ K (b k)) (smoothing_sq_integrable μ L (b k)),
      ← integral_div]
    refine integral_mono (hint k).norm
      (((smoothing_sq_integrable μ K (b k)).add (smoothing_sq_integrable μ L (b k))).div_const 2)
      fun x => ?_
    simp only [G, norm_mul, RCLike.norm_conj]
    nlinarith [sq_nonneg (‖smoothing μ K (b k) x‖ - ‖smoothing μ L (b k) x‖)]
  have hsum : Summable fun k => ∫ x, ‖G k x‖ ∂μ :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hle
      (((hs_summable μ b K).add (hs_summable μ b L)).div_const 2)
  have hmain := hasSum_integral_of_summable_integral_norm hint hsum
  have hpt (x : X) : ∑' k, G k x = ((∫ w, K (x, w) * L (x, w) ∂μ : ℝ) : ℂ) := by
    have hP := b.hasSum_inner_mul_inner (row μ K x) (row μ L x)
    have hG (k : ι) : G k x = inner ℂ (row μ K x) (b k) * inner ℂ (b k) (row μ L x) := by
      simp only [G]
      rw [← inner_conj_symm (b k) (row μ L x)]
      rfl
    simp only [hG]
    rw [hP.tsum_eq]
    unfold row
    rw [MeasureTheory.ContinuousMap.inner_toLp, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [rowContinuous, ContinuousMap.coe_mk, Complex.conj_ofReal]
    push_cast
    ring
  simp only [hpt] at hmain
  rw [integral_complex_ofReal] at hmain
  simpa only [hinner] using hmain

/-- **The time extent is the power of `T`.** For a symmetric kernel, the diagonal integral of the
kernel of `T^(m+2)` is its trace, in every countable Hilbert basis. -/
theorem trace_pow {ι : Type*} [Countable ι] (b : HilbertBasis ι ℂ (Hilbert μ)) (K : C(X × X, ℝ))
    (hK : ∀ x y, K (x, y) = K (y, x)) (m : ℕ) :
    HasSum (fun k => inner ℂ (b k) (((operator μ K) ^ (m + 2)) (b k)))
      ((∫ x, powK μ K (m + 1) (x, x) ∂μ : ℝ) : ℂ) := by
  have h := trace_comp μ b (powK μ K m) K
  have hsym : ∀ f g, inner ℂ (operator μ K f) g = inner ℂ f (operator μ K g) :=
    operator_symmetric μ K hK
  have hval : (∫ x, ∫ w, powK μ K m (x, w) * K (x, w) ∂μ ∂μ) = ∫ x, powK μ K (m + 1) (x, x) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [powK_succ, compK_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    dsimp only
    rw [hK w x]
  rw [hval] at h
  convert h using 2 with k
  rw [hsym, operator_powK, pow_succ' _ (m + 1)]
  rfl

/-- Every Hilbert basis of `L²` is countable. -/
theorem countable_of_basis {w : Type*} (b : HilbertBasis w ℂ (Hilbert μ)) : Countable w := by
  haveI : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have hsep : ∀ i j : w, i ≠ j → 1 ≤ dist (b i) (b j) := by
    intro i j hij
    have h0 : inner ℂ (b i) (b j) = (0 : ℂ) := b.orthonormal.2 hij
    have h1 := norm_sub_sq (𝕜 := ℂ) (b i) (b j)
    rw [h0, b.orthonormal.1 i, b.orthonormal.1 j] at h1
    simp only [map_zero, mul_zero, sub_zero, one_pow] at h1
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (b i - b j)]
  have hdisj : (Set.univ : Set w).PairwiseDisjoint fun i => Metric.ball (b i) (1 / 2) := by
    intro i _ j _ hij
    refine Set.disjoint_left.mpr fun x hi hj => ?_
    have h1 := hsep i j hij
    have h3 : dist x (b i) < 1 / 2 := hi
    have h4 : dist x (b j) < 1 / 2 := hj
    rw [dist_comm x (b i)] at h3
    have h5 := dist_triangle (b i) x (b j)
    linarith
  have hc := hdisj.countable_of_isOpen (fun _ _ => Metric.isOpen_ball)
    (fun i _ => ⟨b i, Metric.mem_ball_self (by norm_num)⟩)
  exact Set.countable_univ_iff.mp hc

end Chain

open WilsonSingleLinkStaples (character character_continuous)

section Insert
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- Insert a function of the initial slice in a kernel. -/
def insK (f : C(X, ℝ)) (K : C(X × X, ℝ)) : C(X × X, ℝ) :=
  ⟨fun p => f p.1 * K p, by fun_prop⟩

theorem insK_apply (f : C(X, ℝ)) (K : C(X × X, ℝ)) (x y : X) :
    insK f K (x, y) = f x * K (x, y) := rfl

theorem insK_one (K : C(X × X, ℝ)) : insK 1 K = K := by
  ext p
  simp [insK]

theorem compK_insK (f : C(X, ℝ)) (K L : C(X × X, ℝ)) :
    compK μ (insK f K) L = insK f (compK μ K L) := by
  ext ⟨x, y⟩
  simp only [compK_apply, insK_apply]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  dsimp only
  ring

theorem chainK_congr (K K' : ℕ → C(X × X, ℝ)) (m : ℕ) (h : ∀ j ≤ m, K j = K' j) :
    chainK μ K m = chainK μ K' m := by
  induction m with
  | zero => exact h 0 le_rfl
  | succ m ih =>
    simp only [chainK]
    rw [ih fun j hj => h j (by omega), h (m + 1) le_rfl]

/-- **Two insertions in a chain.** -/
theorem chainK_two (K : C(X × X, ℝ)) (f g : C(X, ℝ)) (s m : ℕ) (Ks : ℕ → C(X × X, ℝ))
    (h0 : Ks 0 = insK f K) (hs : Ks (s + 1) = insK g K)
    (hother : ∀ j ≤ s + 1 + m, j ≠ 0 → j ≠ s + 1 → Ks j = K) :
    chainK μ Ks (s + 1 + m) = compK μ (insK f (powK μ K s)) (insK g (powK μ K m)) := by
  have h1 : ∀ j ≤ s, chainK μ Ks j = insK f (powK μ K j) := by
    intro j hj
    induction j with
    | zero => exact h0
    | succ j ih =>
      simp only [chainK]
      rw [ih (by omega), hother (j + 1) (by omega) (by omega) (by omega), compK_insK]
      rfl
  have h2 : ∀ i ≤ m, chainK μ Ks (s + 1 + i) = compK μ (insK f (powK μ K s)) (insK g (powK μ K i)) := by
    intro i hi
    induction i with
    | zero =>
      change compK μ (chainK μ Ks s) (Ks (s + 1)) = _
      rw [h1 s le_rfl, hs]
      rfl
    | succ i ih =>
      change compK μ (chainK μ Ks (s + 1 + i)) (Ks (s + 1 + i + 1)) = _
      rw [ih (by omega), hother _ (by omega) (by omega) (by omega), compK_assoc, compK_insK μ g]
      rfl
  exact h2 m le_rfl

end Insert

/-! ### The twisted law on a lattice with time extent `T` and spatial size `n` -/

section ChainLaw
variable (T n : ℕ) [NeZero T] [NeZero n]

/-- A field on the lattice `ZMod T × (ZMod n)³`: a slice at each time and a temporal link at each
point of each slab. -/
abbrev Chain := (ZMod T → Slice n) × (ZMod T → SliceGauge n Q)

/-- Independent Haar links. -/
def chainRef : Measure (Chain T n) :=
  (Measure.pi fun _ : ZMod T => WilsonSlabOperator.measure n).prod
    (Measure.pi fun _ : ZMod T => temporalHaar (n := n) (G := Q))

instance : IsProbabilityMeasure (chainRef T n) := by
  unfold chainRef
  infer_instance

/-- The twisted action on `ZMod T × (ZMod n)³`: one term for every plaquette. -/
def chainAction (β : ℝ) (c : Chain T n) : ℝ :=
  β * ∑ t, (twistedPotential n (c.1 t) + temporalAction character 2 (c.1 t) (c.1 (t + 1)) (c.2 t))

theorem chainAction_continuous (β : ℝ) : Continuous (chainAction T n β) := by
  have hc := character_continuous
  unfold chainAction twistedPotential temporalAction temporalHolonomy spatialHolonomy
  fun_prop

/-- The twisted law at time extent `T` and spatial size `n`. -/
def chainLaw (β : ℝ) : Measure (Chain T n) :=
  (∫⁻ c, ENNReal.ofReal (Real.exp (-chainAction T n β c)) ∂chainRef T n)⁻¹ •
    (chainRef T n).withDensity fun c => ENNReal.ofReal (Real.exp (-chainAction T n β c))

/-- The partition function. -/
def chainZ (β : ℝ) : ℝ := ∫ c, Real.exp (-chainAction T n β c) ∂chainRef T n

/-- One slab, with half of each spatial potential. -/
def slabW (β : ℝ) (u v : Slice n) (h : SliceGauge n Q) : ℝ :=
  Real.exp (-(β / 2) * twistedPotential n u) * Real.exp (-β * temporalAction character 2 u v h) *
    Real.exp (-(β / 2) * twistedPotential n v)

theorem slabW_integral (β : ℝ) (u v : Slice n) :
    ∫ h, slabW n β u v h ∂temporalHaar = twistedKernel n β (u, v) := by
  rw [twistedKernel_eq]
  unfold slabW
  rw [integral_mul_const, integral_const_mul]

theorem exp_chainAction (β : ℝ) (c : Chain T n) :
    Real.exp (-chainAction T n β c) = ∏ t, slabW n β (c.1 t) (c.1 (t + 1)) (c.2 t) := by
  have hs : (∑ t : ZMod T, twistedPotential n (c.1 (t + 1))) = ∑ t, twistedPotential n (c.1 t) :=
    Equiv.sum_comp (Equiv.addRight (1 : ZMod T)) (fun t => twistedPotential n (c.1 t))
  unfold slabW chainAction
  simp only [← Real.exp_add]
  rw [← Real.exp_sum]
  congr 1
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hs]
  ring

/-- **Schwinger functions of slice observables are transfer products.** Temporal links integrate
to the twisted kernel at each slab, and the slices compose it around the time circle. -/
theorem schwinger (f : ZMod T → C(Slice n, ℝ)) (β : ℝ) :
    ∫ c, (∏ t, f t (c.1 t)) * Real.exp (-chainAction T n β c) ∂chainRef T n =
      ∫ x, chainK (WilsonSlabOperator.measure n)
        (fun j => insK (f (j : ZMod T)) (twistedKernel n β)) (T - 1) (x, x)
          ∂WilsonSlabOperator.measure n := by
  obtain ⟨m, rfl⟩ : ∃ m, T = m + 1 := ⟨T - 1, (Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne T))).symm⟩
  rw [Nat.add_sub_cancel]
  refine Eq.trans ?_ (cycle_integral (WilsonSlabOperator.measure n) m
    (fun t => insK (f t) (twistedKernel n β)))
  have hcont : Continuous fun c : Chain (m + 1) n =>
      (∏ t, f t (c.1 t)) * Real.exp (-chainAction (m + 1) n β c) := by
    refine Continuous.mul (continuous_finset_prod _ fun t _ => ?_)
      (Real.continuous_exp.comp (chainAction_continuous (m + 1) n β).neg)
    exact (f t).continuous.comp ((continuous_apply t).comp continuous_fst)
  unfold chainRef
  rw [integral_prod _ (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  dsimp only
  simp only [exp_chainAction]
  rw [integral_const_mul,
    integral_fintype_prod_eq_prod (𝕜 := ℝ) (fun t h => slabW n β (u t) (u (t + 1)) h)]
  simp only [slabW_integral, ← Finset.prod_mul_distrib]
  rfl

/-- **The partition function is the diagonal integral of the kernel of `T^(time extent)`.** -/
theorem chainZ_eq (β : ℝ) :
    chainZ T n β = ∫ x, powK (WilsonSlabOperator.measure n) (twistedKernel n β) (T - 1) (x, x)
      ∂WilsonSlabOperator.measure n := by
  have h := schwinger T n (fun _ => 1) β
  simp only [ContinuousMap.one_apply, Finset.prod_const_one, one_mul, insK_one] at h
  exact h

/-- **Periodic time extent `T ≥ 2` is exactly the `T`-th power of the transfer operator.** In every
countable Hilbert basis, the partition function is the trace of `transfer ^ T`. -/
theorem chainZ_trace {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (Hilbert n)) (β : ℝ) (m : ℕ) :
    HasSum (fun k => inner ℂ (b k) (((TwistedTransfer.transfer n β) ^ (m + 2)) (b k)))
      ((chainZ (m + 2) n β : ℝ) : ℂ) := by
  rw [chainZ_eq]
  exact trace_pow (WilsonSlabOperator.measure n) b (twistedKernel n β) (twistedKernel_symm n β) m

/-- **The two-point function.** At time extent `s + m + 2`, with separation `s + 1`, the correlator
of slice observables is a double kernel integral. No operator trace is stated here; the form
`Tr (f T^(s+1) g T^(m+1))` is `TwistedTraceLaw.trace_two_point`. -/
theorem two_point (s m : ℕ) (f g : C(Slice n, ℝ)) (β : ℝ) :
    ∫ c, (f (c.1 0) * g (c.1 ((s + 1 : ℕ) : ZMod (s + m + 2)))) *
        Real.exp (-chainAction (s + m + 2) n β c) ∂chainRef (s + m + 2) n =
      ∫ x, ∫ y, f x * powK (WilsonSlabOperator.measure n) (twistedKernel n β) s (x, y) * g y *
        powK (WilsonSlabOperator.measure n) (twistedKernel n β) m (y, x)
          ∂WilsonSlabOperator.measure n ∂WilsonSlabOperator.measure n := by
  classical
  set τ : ZMod (s + m + 2) := ((s + 1 : ℕ) : ZMod (s + m + 2)) with hτ
  have hcast (j : ℕ) (hj : j < s + m + 2) (i : ℕ) (hi : i < s + m + 2) :
      ((j : ℕ) : ZMod (s + m + 2)) = (i : ℕ) ↔ j = i := by
    constructor
    · intro h
      have := congrArg ZMod.val h
      rwa [ZMod.val_natCast_of_lt hj, ZMod.val_natCast_of_lt hi] at this
    · rintro rfl
      rfl
  have hτ0 : τ ≠ 0 := by
    intro h
    have := (hcast (s + 1) (by omega) 0 (by omega)).mp (by simpa [hτ] using h)
    omega
  let φ : ZMod (s + m + 2) → C(Slice n, ℝ) := fun t => if t = 0 then f else if t = τ then g else 1
  have hprod (c : Chain (s + m + 2) n) : ∏ t, φ t (c.1 t) = f (c.1 0) * g (c.1 τ) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (0 : ZMod (s + m + 2))),
      ← Finset.mul_prod_erase (Finset.univ.erase 0) _
        (Finset.mem_erase.mpr ⟨hτ0, Finset.mem_univ τ⟩)]
    have hrest : ∏ t ∈ (Finset.univ.erase (0 : ZMod (s + m + 2))).erase τ, φ t (c.1 t) = 1 := by
      refine Finset.prod_eq_one fun t ht => ?_
      have h1 := Finset.ne_of_mem_erase ht
      have h2 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht)
      simp [φ, h1, h2]
    rw [hrest, mul_one]
    simp [φ, hτ0]
  have hs := schwinger (s + m + 2) n φ β
  simp only [hprod] at hs
  rw [hs]
  have hsub : s + m + 2 - 1 = s + 1 + m := by omega
  rw [hsub]
  have hchain := chainK_two (WilsonSlabOperator.measure n) (twistedKernel n β) f g s m
    (fun j => insK (φ (j : ZMod (s + m + 2))) (twistedKernel n β))
    (by simp [φ]) (by change insK (φ τ) _ = _; simp [φ, hτ0])
    (fun j hj hj0 hjs => by
      have h1 : ((j : ℕ) : ZMod (s + m + 2)) ≠ 0 := by
        intro h
        exact hj0 ((hcast j (by omega) 0 (by omega)).mp (by simpa using h))
      have h2 : ((j : ℕ) : ZMod (s + m + 2)) ≠ τ := by
        intro h
        exact hjs ((hcast j (by omega) (s + 1) (by omega)).mp h)
      simp only [φ, if_neg h1, if_neg h2, insK_one])
  rw [hchain]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [compK_apply, insK_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  ring

end ChainLaw
/-! ### At `T = L` this is the existing four-dimensional law -/

section Identify

theorem measurePreserving_curry {ι κ Y : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] :
    MeasurePreserving (MeasurableEquiv.curry ι κ Y) (Measure.pi fun _ : ι × κ => ν)
      (Measure.pi fun _ : ι => Measure.pi fun _ : κ => ν) := by
  classical
  set e := (MeasurableEquiv.curry ι κ Y).symm with he
  refine MeasurePreserving.symm e ⟨e.measurable, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [e.map_apply]
  have hpre : e ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ fun i => Set.pi Set.univ fun j => s (i, j) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Prod.forall]
    rfl
  rw [hpre, Measure.pi_pi]
  simp only [Measure.pi_pi]
  exact (Fintype.prod_prod_type (fun p : ι × κ => ν (s p))).symm

variable (N : ℕ) [NeZero N]

/-- Links of the lattice, as slice links and temporal links. -/
def linkEquiv : (ZMod N × (SpatialVertex N × Fin 3)) ⊕ (ZMod N × SpatialVertex N) ≃ Edge (Vertex N) where
  toFun p := match p with
    | Sum.inl q => ⟨embed N q.1 q.2.1, step N (embed N q.1 q.2.1) q.2.2.succ,
        forward N (embed N q.1 q.2.1) q.2.2.succ⟩
    | Sum.inr q => ⟨embed N q.1 q.2, step N (embed N q.1 q.2) 0, forward N (embed N q.1 q.2) 0⟩
  invFun e := Fin.cases (motive := fun _ => (ZMod N × (SpatialVertex N × Fin 3)) ⊕ (ZMod N × SpatialVertex N))
    (Sum.inr (e.1 0, fun i => e.1 i.succ))
    (fun i => Sum.inl (e.1 0, (fun k => e.1 k.succ), i)) e.2.2.val
  left_inv p := by
    rcases p with ⟨t, x, i⟩ | ⟨t, x⟩
    · rfl
    · rfl
  right_inv e := by
    apply (PeriodicTimeReflection.edgeCoordinates N).injective
    rcases e with ⟨x, y, μ, hμ⟩
    cases hμ
    have hx : embed N (x 0) (fun k => x k.succ) = x := (vertexCoordinates (n := N)).left_inv x
    refine Fin.cases ?_ (fun i => ?_) μ
    · exact Prod.ext hx rfl
    · exact Prod.ext hx rfl

/-- A lattice field as a chain of slices and temporal links. -/
def toChain (U : Configuration (Vertex N) Q) : Chain N N := (slice U, temporal U)

theorem toChain_preserving :
    MeasurePreserving (toChain N) (referenceMeasure Q (Vertex N)) (chainRef N N) := by
  have h1 := measurePreserving_piCongrLeft (fun _ : (ZMod N × (SpatialVertex N × Fin 3)) ⊕ (ZMod N × SpatialVertex N) =>
    compactHaar Q) (linkEquiv N).symm
  have h2 := measurePreserving_sumPiEquivProdPi
    (X := fun _ : (ZMod N × (SpatialVertex N × Fin 3)) ⊕ (ZMod N × SpatialVertex N) => Q)
    (fun _ => compactHaar Q)
  have h3 := measurePreserving_curry (ι := ZMod N) (κ := SpatialVertex N × Fin 3) (compactHaar Q)
  have h4 := measurePreserving_curry (ι := ZMod N) (κ := SpatialVertex N) (compactHaar Q)
  have h5 := (h3.prod h4).comp (h2.comp h1)
  convert h5 using 1

theorem plaq_temporal (U : Configuration (Vertex N) Q) (t : ZMod N) (x : SpatialVertex N) (i : Fin 3) :
    PeriodicPlaquetteReflection.plaquetteProduct N Q U (embed N t x) 0 i.succ =
      temporalHolonomy (slice U t) (slice U (t + 1)) (temporal U t) x i := by
  rw [← PeriodicPlaquetteReflection.plaquette_holonomy_eq_product]
  exact actual_temporal_plaquette U t x i

theorem plaq_spatial (U : Configuration (Vertex N) Q) (t : ZMod N) (x : SpatialVertex N) (i j : Fin 3) :
    PeriodicPlaquetteReflection.plaquetteProduct N Q U (embed N t x) i.succ j.succ =
      spatialHolonomy (slice U t) x i j := by
  rw [← PeriodicPlaquetteReflection.plaquette_holonomy_eq_product]
  exact actual_spatial_plaquette U t x i j

theorem sum_planes' (F : Plane → ℝ) :
    ∑ p : Plane, F p = (∑ i : Fin 3, F ⟨(0, i.succ), Fin.succ_pos i⟩) +
      ∑ p : SpatialPlane, F ⟨(p.1.1.succ, p.1.2.succ), Fin.succ_lt_succ_iff.mpr p.2⟩ := by
  have h4 : (Finset.univ : Finset Plane) =
      {⟨(0,1),by decide⟩, ⟨(0,2),by decide⟩, ⟨(0,3),by decide⟩,
       ⟨(1,2),by decide⟩, ⟨(1,3),by decide⟩, ⟨(2,3),by decide⟩} := by decide
  have h3 : (Finset.univ : Finset SpatialPlane) =
      {⟨(0,1),by decide⟩, ⟨(0,2),by decide⟩, ⟨(1,2),by decide⟩} := by decide
  rw [h4, h3]
  repeat rw [Finset.sum_insert (by decide)]
  simp only [Finset.sum_singleton, Fin.sum_univ_three]
  rw [show (⟨((0 : Fin 3).succ, (1 : Fin 3).succ), Fin.succ_lt_succ_iff.mpr (by decide)⟩ : Plane) =
    ⟨(1,2), by decide⟩ from rfl]
  simp only [add_assoc]
  rfl

end Identify

section IdentifyLaw
variable (n : ℕ) [NeZero n]
open TwistedReflection

theorem twist_temporal (t : ZMod (2 * n)) (x : SpatialVertex (2 * n)) (i : Fin 3) :
    spatialTwist n (embed (2 * n) t x, ⟨(0, i.succ), Fin.succ_pos i⟩) = 1 := by
  unfold spatialTwist
  rw [if_neg]
  rintro ⟨h, -⟩
  have h0 : (0 : Fin 4) = 1 := congrArg Prod.fst h
  exact absurd h0 (by decide)

theorem twist_spatial (t : ZMod (2 * n)) (x : SpatialVertex (2 * n)) (p : SpatialPlane) :
    spatialTwist n (embed (2 * n) t x, ⟨(p.1.1.succ, p.1.2.succ), Fin.succ_lt_succ_iff.mpr p.2⟩) =
      spatialSign (2 * n) x p := by
  unfold spatialTwist spatialSign
  refine if_congr ?_ rfl rfl
  change ((p.1.1.succ, p.1.2.succ) = ((1 : Fin 4), (2 : Fin 4)) ∧ x 0 = 0 ∧ x 1 = 0) ↔ _
  refine and_congr_left fun _ => ?_
  rcases p with ⟨⟨a, b⟩, hab⟩
  constructor
  · intro h
    have ha := congrArg Prod.fst h
    have hb := congrArg Prod.snd h
    dsimp only at ha hb ⊢
    have ha' : a = 0 := Fin.succ_injective _ (by simpa using ha)
    have hb' : b = 1 := Fin.succ_injective _ (by simpa using hb)
    rw [ha', hb']
  · intro h
    have ha : a = 0 := congrArg Prod.fst h
    have hb : b = 1 := congrArg Prod.snd h
    subst ha hb
    rfl

/-- **At `T = L = 2n` the chain action is the action of `TwistedReflection`.** -/
theorem action_toChain (β : ℝ) (U : Configuration (Vertex (2 * n)) Q) :
    action n Q (spatialTwist n) character β 2 U = chainAction (2 * n) (2 * n) β (toChain (2 * n) U) := by
  unfold action chainAction
  congr 1
  rw [Fintype.sum_prod_type, sum_vertices]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hcomp : ∀ x : SpatialVertex (2 * n), (∑ p : Plane, term n Q (spatialTwist n) character 2 U (embed (2 * n) t x, p)) =
      (∑ i : Fin 3, (2 - (character (temporalHolonomy (slice U t) (slice U (t + 1)) (temporal U t) x i)).re)) +
      ∑ p : SpatialPlane, (2 - spatialSign (2 * n) x p * (character (spatialHolonomy (slice U t) x p.1.1 p.1.2)).re) := by
    intro x
    rw [sum_planes']
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      unfold term
      rw [twist_temporal, one_mul]
      exact congrArg (fun g => 2 - (character g).re) (plaq_temporal (2 * n) U t x i)
    · refine Finset.sum_congr rfl fun p _ => ?_
      unfold term
      rw [twist_spatial]
      exact congrArg (fun g => 2 - _ * (character g).re) (plaq_spatial (2 * n) U t x p.1.1 p.1.2)
  simp only [hcomp, Finset.sum_add_distrib]
  rw [add_comm]
  rfl

/-- **The existing law pushes forward to the chain law.** -/
theorem toChain_law (β : ℝ) :
    MeasurePreserving (toChain (2 * n))
      (law n Q (spatialTwist n) character β 2) (chainLaw (2 * n) (2 * n) β) := by
  have hmeas : Measurable fun c : Chain (2 * n) (2 * n) =>
      ENNReal.ofReal (Real.exp (-chainAction (2 * n) (2 * n) β c)) :=
    (Real.continuous_exp.comp (chainAction_continuous _ _ β).neg).measurable.ennreal_ofReal
  have h := GibbsReflectionTransport.normalized_transport (toChain_preserving (2 * n)) _ hmeas
  have hd : gibbsDensity (Vertex (2 * n)) Q (action n Q (spatialTwist n) character β 2) =
      (fun c : Chain (2 * n) (2 * n) => ENNReal.ofReal (Real.exp (-chainAction (2 * n) (2 * n) β c))) ∘
        toChain (2 * n) := by
    funext U
    simp only [gibbsDensity, Function.comp, action_toChain]
  unfold law gibbsMeasure gibbsPartition
  rw [hd]
  exact h

/-- The partition function of the existing law is the chain partition function at `T = L = 2n`. Its
trace form is `law_partition_trace`. -/
theorem action_partition (β : ℝ) :
    ∫ U, Real.exp (-action n Q (spatialTwist n) character β 2 U) ∂referenceMeasure Q (Vertex (2 * n)) =
      chainZ (2 * n) (2 * n) β := by
  simp only [action_toChain]
  have h := integral_map (μ := referenceMeasure Q (Vertex (2 * n)))
    (toChain_preserving (2 * n)).measurable.aemeasurable
    (f := fun c : Chain (2 * n) (2 * n) => Real.exp (-chainAction (2 * n) (2 * n) β c))
    (Real.continuous_exp.comp (chainAction_continuous _ _ β).neg).aestronglyMeasurable
  rw [(toChain_preserving (2 * n)).map_eq] at h
  exact h.symm
end IdentifyLaw
/-! ### Reflection positivity at every even time extent -/

section Rearrange
variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ] (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ)
  [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd]

theorem comm4 :
    MeasurePreserving (fun z : (α × β) × (γ × δ) => ((z.1.1, z.2.1), (z.1.2, z.2.2)))
      ((μa.prod μb).prod (μc.prod μd)) ((μa.prod μc).prod (μb.prod μd)) := by
  have h1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have h2 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μb μc μd).symm
  have h3 := (MeasurePreserving.id μa).prod
    ((Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd))
  have h4 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μb μd)
  have h5 := (measurePreserving_prodAssoc μa μc (μb.prod μd)).symm
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

end Rearrange

section Reflection
variable (T n : ℕ) [NeZero T] [NeZero n]

/-- The time reflection through the slice `t = 0`. Temporal links reverse and are inverted. -/
def chainReflect (c : Chain T n) : Chain T n :=
  (fun t => c.1 (-t), fun t x => (c.2 (-(t + 1)) x)⁻¹)

theorem chainReflect_involutive (c : Chain T n) : chainReflect T n (chainReflect T n c) = c := by
  refine Prod.ext (funext fun t => ?_) (funext fun t => funext fun x => ?_)
  · simp [chainReflect]
  · simp [chainReflect]

/-- A slab is unchanged when its slices are exchanged and its temporal links are inverted. -/
theorem temporalAction_reverse (u v : Slice n) (h : SliceGauge n Q) :
    temporalAction character 2 v u (fun x => (h x)⁻¹) = temporalAction character 2 u v h := by
  unfold temporalAction
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have hW : temporalHolonomy v u (fun x => (h x)⁻¹) x i =
      (h x)⁻¹ * (temporalHolonomy u v h x i)⁻¹ * ((h x)⁻¹)⁻¹ := by
    unfold temporalHolonomy
    group
  rw [hW, WilsonSingleLinkStaples.character_classFunction,
    WilsonSingleLinkStaples.character_inverse_re]

theorem temporalAction_continuous :
    Continuous fun z : Slice n × Slice n × SliceGauge n Q =>
      temporalAction character 2 z.1 z.2.1 z.2.2 := by
  have hc := character_continuous
  unfold temporalAction temporalHolonomy
  fun_prop

theorem twistedPotential_continuous : Continuous (twistedPotential n) := by
  have hc := character_continuous
  unfold twistedPotential spatialHolonomy
  fun_prop

/-- Temporal links inverted, as a Haar-preserving map on one slab. -/
theorem inv_preserving :
    MeasurePreserving (fun h : SliceGauge n Q => fun x => (h x)⁻¹)
      (temporalHaar (n := n) (G := Q)) (temporalHaar (n := n) (G := Q)) := by
  exact measurePreserving_pi (fun _ : SpatialVertex n => compactHaar Q)
    (fun _ : SpatialVertex n => compactHaar Q) (f := fun _ q => q⁻¹)
    (fun _ => PeriodicTimeReflection.compactHaar_preserves_inv Q)

variable (k : ℕ)

theorem cast_neg_half : -(((k + 1 : ℕ)) : ZMod (2 * (k + 1))) = ((k + 1 : ℕ) : ZMod (2 * (k + 1))) := by
  have h : (((2 * (k + 1) : ℕ)) : ZMod (2 * (k + 1))) = 0 := ZMod.natCast_self _
  push_cast at h ⊢
  linear_combination -h

/-- The time circle as two arcs: `j` and `-(j + 1)` for `0 ≤ j ≤ k`. -/
def arc : Fin (k + 1) ⊕ Fin (k + 1) → ZMod (2 * (k + 1))
  | Sum.inl j => (j.val : ZMod (2 * (k + 1)))
  | Sum.inr j => -((j.val + 1 : ℕ) : ZMod (2 * (k + 1)))

theorem arc_bijective : Function.Bijective (arc k) := by
  haveI : NeZero (2 * (k + 1)) := ⟨by omega⟩
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp [ZMod.card]; omega⟩
  have hcast (a b : ℕ) (ha : a < 2 * (k + 1)) (hb : b < 2 * (k + 1))
      (h : (a : ZMod (2 * (k + 1))) = b) : a = b := by
    have := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at this
  have hzero (a : ℕ) (ha : a < 2 * (k + 1)) (h : (a : ZMod (2 * (k + 1))) = 0) : a = 0 :=
    hcast a 0 ha (by omega) (by simpa using h)
  rintro (a | a) (b | b) hab
  · simp only [arc] at hab
    exact congrArg Sum.inl (Fin.ext (hcast _ _ (by omega) (by omega) hab))
  · exfalso
    simp only [arc] at hab
    have h0 : ((a.val + (b.val + 1) : ℕ) : ZMod (2 * (k + 1))) = 0 := by
      push_cast at hab ⊢
      linear_combination hab
    have := hzero _ (by omega) h0
    omega
  · exfalso
    simp only [arc] at hab
    have h0 : ((b.val + (a.val + 1) : ℕ) : ZMod (2 * (k + 1))) = 0 := by
      push_cast at hab ⊢
      linear_combination -hab
    have := hzero _ (by omega) h0
    omega
  · simp only [arc] at hab
    have h1 := hcast _ _ (by omega) (by omega) (neg_injective hab)
    exact congrArg Sum.inr (Fin.ext (by omega))

/-- The arcs as an equivalence. -/
def arcEquiv : Fin (k + 1) ⊕ Fin (k + 1) ≃ ZMod (2 * (k + 1)) := Equiv.ofBijective _ (arc_bijective k)

theorem sum_arc (F : ZMod (2 * (k + 1)) → ℝ) :
    ∑ t, F t = ∑ j : Fin (k + 1), F (j.val : ZMod (2 * (k + 1))) +
      ∑ j : Fin (k + 1), F (-((j.val + 1 : ℕ) : ZMod (2 * (k + 1)))) := by
  rw [← (arcEquiv k).sum_comp F, Fintype.sum_sum_type]
  rfl

/-- The fixed slices `t = 0` and `t = k + 1`. -/
abbrev Bdry := Slice n × Slice n

/-- The positive half: interior slices and temporal links of the arc from `0` to `k + 1`. -/
abbrev Half := (Fin k → Slice n) × (Fin (k + 1) → SliceGauge n Q)

def bdry (c : Chain (2 * (k + 1)) n) : Bdry n := (c.1 0, c.1 ((k + 1 : ℕ) : ZMod (2 * (k + 1))))

def half (c : Chain (2 * (k + 1)) n) : Half n k :=
  (fun i => c.1 ((i.val + 1 : ℕ) : ZMod (2 * (k + 1))), fun j => c.2 (j.val : ZMod (2 * (k + 1))))

theorem bdry_reflect (c : Chain (2 * (k + 1)) n) : bdry n k (chainReflect _ n c) = bdry n k c := by
  unfold bdry chainReflect
  dsimp only
  rw [neg_zero, cast_neg_half]

/-- Splitting a field into the boundary, the reflected half and the half. -/
def split (c : Chain (2 * (k + 1)) n) : Bdry n × (Half n k × Half n k) :=
  (bdry n k c, (half n k (chainReflect _ n c), half n k c))

/-- The reference measure of a half. -/
def halfRef : Measure (Half n k) :=
  (Measure.pi fun _ : Fin k => WilsonSlabOperator.measure n).prod
    (Measure.pi fun _ : Fin (k + 1) => temporalHaar (n := n) (G := Q))

instance : IsProbabilityMeasure (halfRef n k) := by
  unfold halfRef
  infer_instance

def bdryRef : Measure (Bdry n) := (WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n)

instance : IsProbabilityMeasure (bdryRef n) := by
  unfold bdryRef
  infer_instance

/-- **The split is an exact factorization of Haar measure.** -/
theorem split_preserving :
    MeasurePreserving (split n k) (chainRef (2 * (k + 1)) n)
      ((bdryRef n).prod ((halfRef n k).prod (halfRef n k))) := by
  let μs := WilsonSlabOperator.measure n
  let μt := temporalHaar (n := n) (G := Q)
  -- arcs
  have harc {Y : Type _} [MeasurableSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν] :
      MeasurePreserving (fun u : ZMod (2 * (k + 1)) → Y =>
        ((fun j : Fin (k + 1) => u (j.val : ZMod (2 * (k + 1)))),
          (fun j : Fin (k + 1) => u (-((j.val + 1 : ℕ) : ZMod (2 * (k + 1)))))))
        (Measure.pi fun _ : ZMod (2 * (k + 1)) => ν)
        ((Measure.pi fun _ : Fin (k + 1) => ν).prod (Measure.pi fun _ : Fin (k + 1) => ν)) := by
    have h1 := measurePreserving_piCongrLeft (fun _ : Fin (k + 1) ⊕ Fin (k + 1) => ν) (arcEquiv k).symm
    have h2 := measurePreserving_sumPiEquivProdPi (X := fun _ : Fin (k + 1) ⊕ Fin (k + 1) => Y)
      (fun _ => ν)
    have h := h2.comp h1
    convert h using 1
    refine funext fun u => Prod.ext (funext fun j => ?_) (funext fun j => ?_)
    · simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, MeasurableEquiv.sumPiEquivProdPi,
        arcEquiv, Equiv.sumPiEquivProdPi]
      rfl
    · simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, MeasurableEquiv.sumPiEquivProdPi,
        arcEquiv, Equiv.sumPiEquivProdPi]
      simp only [arc]
      congr 1
      push_cast
      ring
  have hA₁ := ((measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => μs) 0).prod
    (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => μs) (Fin.last k))).comp (harc μs)
  have hinvpi : MeasurePreserving
      (fun g : Fin (k + 1) → SliceGauge n Q => fun j x => (g j x)⁻¹)
      (Measure.pi fun _ : Fin (k + 1) => μt) (Measure.pi fun _ : Fin (k + 1) => μt) :=
    measurePreserving_pi (fun _ : Fin (k + 1) => μt) (fun _ : Fin (k + 1) => μt)
      (f := fun _ h => fun x => (h x)⁻¹) (fun _ => inv_preserving n)
  have hA₂ := ((MeasurePreserving.id (Measure.pi fun _ : Fin (k + 1) => μt)).prod hinvpi).comp (harc μt)
  have hA := hA₁.prod hA₂
  let πk := Measure.pi fun _ : Fin k => μs
  let πg := Measure.pi fun _ : Fin (k + 1) => μt
  have hB := (comm4 μs πk μs πk).prod (MeasurePreserving.id (πg.prod πg))
  have hC := measurePreserving_prodAssoc (μs.prod μs) (πk.prod πk) (πg.prod πg)
  have hD := (MeasurePreserving.id (μs.prod μs)).prod (comm4 πk πk πg πg)
  have hE := (MeasurePreserving.id (μs.prod μs)).prod
    (Measure.measurePreserving_swap (μ := πk.prod πg) (ν := πk.prod πg))
  have hall := hE.comp (hD.comp (hC.comp (hB.comp hA)))
  convert hall using 1
  funext c
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_))
  · change c.1 0 = c.1 (((0 : Fin (k + 1)).val : ℕ) : ZMod (2 * (k + 1)))
    simp
  · change c.1 ((k + 1 : ℕ) : ZMod (2 * (k + 1))) =
      c.1 (-(((Fin.last k).val + 1 : ℕ) : ZMod (2 * (k + 1))))
    rw [Fin.val_last, cast_neg_half]
  · funext i
    change c.1 (-((i.val + 1 : ℕ) : ZMod (2 * (k + 1)))) =
      c.1 (-(((Fin.succAbove (Fin.last k) i).val + 1 : ℕ) : ZMod (2 * (k + 1))))
    rw [Fin.succAbove_last]
    rfl
  · funext j x
    change (c.2 (-((j.val : ZMod (2 * (k + 1))) + 1)) x)⁻¹ =
      (c.2 (-((j.val + 1 : ℕ) : ZMod (2 * (k + 1)))) x)⁻¹
    push_cast
    rfl
  · funext i
    change c.1 ((i.val + 1 : ℕ) : ZMod (2 * (k + 1))) =
      c.1 (((Fin.succAbove 0 i).val : ℕ) : ZMod (2 * (k + 1)))
    rw [Fin.zero_succAbove]
    rfl
  · rfl

/-- The path `a, s₀, …, s_{k-1}, b` of slices along a half. -/
def pth (a : Slice n) (s : Fin k → Slice n) (b : Slice n) : Fin (k + 2) → Slice n :=
  Fin.cons a (Fin.snoc (α := fun _ => Slice n) s b)

theorem pth_continuous (j : Fin (k + 2)) :
    Continuous fun z : Bdry n × Half n k => pth n k z.1.1 z.2.1 z.1.2 j := by
  refine Fin.cases ?_ (fun j' => ?_) j
  · simp only [pth, Fin.cons_zero]
    fun_prop
  · simp only [pth, Fin.cons_succ]
    refine Fin.lastCases ?_ (fun i => ?_) j'
    · simp only [Fin.snoc_last]
      fun_prop
    · simp only [Fin.snoc_castSucc]
      fun_prop

/-- The action of a half, with half of each boundary potential. -/
def halfAction (β : ℝ) (z : Bdry n × Half n k) : ℝ :=
  β * (twistedPotential n z.1.1 / 2 + twistedPotential n z.1.2 / 2 +
    ∑ i, twistedPotential n (z.2.1 i) +
    ∑ j : Fin (k + 1), temporalAction character 2 (pth n k z.1.1 z.2.1 z.1.2 j.castSucc)
      (pth n k z.1.1 z.2.1 z.1.2 j.succ) (z.2.2 j))

theorem halfAction_continuous (β : ℝ) : Continuous (halfAction n k β) := by
  have hV := twistedPotential_continuous n
  unfold halfAction
  refine continuous_const.mul ?_
  refine Continuous.add (Continuous.add (Continuous.add ?_ ?_) ?_) ?_
  · fun_prop
  · fun_prop
  · fun_prop
  · refine continuous_finset_sum _ fun j _ => ?_
    exact (temporalAction_continuous n).comp (f := fun z : Bdry n × Half n k =>
      (pth n k z.1.1 z.2.1 z.1.2 j.castSucc, pth n k z.1.1 z.2.1 z.1.2 j.succ, z.2.2 j))
      ((pth_continuous n k _).prodMk ((pth_continuous n k _).prodMk (by fun_prop)))

theorem pth_chain (c : Chain (2 * (k + 1)) n) (j : Fin (k + 2)) :
    pth n k (bdry n k c).1 (half n k c).1 (bdry n k c).2 j = c.1 ((j.val : ℕ) : ZMod (2 * (k + 1))) := by
  refine Fin.cases ?_ (fun j' => ?_) j
  · simp [pth, bdry]
  · simp only [pth, Fin.cons_succ]
    refine Fin.lastCases ?_ (fun i => ?_) j'
    · simp only [Fin.snoc_last, bdry, Fin.val_succ, Fin.val_last]
    · simp only [Fin.snoc_castSucc, half, Fin.val_succ, Fin.val_castSucc]

theorem halfAction_chain (β : ℝ) (c : Chain (2 * (k + 1)) n) :
    halfAction n k β (bdry n k c, half n k c) =
      β * (twistedPotential n (c.1 0) / 2 + twistedPotential n (c.1 ((k + 1 : ℕ) : ZMod (2 * (k + 1)))) / 2 +
        ∑ i : Fin k, twistedPotential n (c.1 ((i.val + 1 : ℕ) : ZMod (2 * (k + 1)))) +
        ∑ j : Fin (k + 1), temporalAction character 2 (c.1 (j.val : ZMod (2 * (k + 1))))
          (c.1 ((j.val + 1 : ℕ) : ZMod (2 * (k + 1)))) (c.2 (j.val : ZMod (2 * (k + 1))))) := by
  unfold halfAction
  simp only [pth_chain, Fin.val_castSucc, Fin.val_succ]
  rfl

/-- **The action splits exactly into the two halves.** -/
theorem chainAction_split (β : ℝ) (c : Chain (2 * (k + 1)) n) :
    chainAction (2 * (k + 1)) n β c = halfAction n k β (bdry n k c, half n k (chainReflect _ n c)) +
      halfAction n k β (bdry n k c, half n k c) := by
  have h2 := halfAction_chain n k β (chainReflect _ n c)
  rw [bdry_reflect] at h2
  rw [h2, halfAction_chain]
  unfold chainAction chainReflect
  dsimp only
  rw [Finset.sum_add_distrib, sum_arc, sum_arc, Fin.sum_univ_succ, Fin.sum_univ_castSucc (n := k)
    (f := fun j : Fin (k + 1) => twistedPotential n (c.1 (-((j.val + 1 : ℕ) : ZMod (2 * (k + 1))))))]
  simp only [Fin.val_zero, Nat.cast_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last, neg_zero]
  rw [cast_neg_half]
  have hslab (j : Fin (k + 1)) :
      temporalAction character 2 (c.1 (-((j.val : ℕ) : ZMod (2 * (k + 1)))))
        (c.1 (-((j.val + 1 : ℕ) : ZMod (2 * (k + 1)))))
        (fun x => (c.2 (-((j.val : ZMod (2 * (k + 1))) + 1)) x)⁻¹) =
      temporalAction character 2 (c.1 (-((j.val + 1 : ℕ) : ZMod (2 * (k + 1)))))
        (c.1 (-((j.val + 1 : ℕ) : ZMod (2 * (k + 1))) + 1))
        (c.2 (-((j.val + 1 : ℕ) : ZMod (2 * (k + 1))))) := by
    have e1 : -((j.val + 1 : ℕ) : ZMod (2 * (k + 1))) + 1 = -((j.val : ℕ) : ZMod (2 * (k + 1))) := by
      push_cast
      ring
    have e2 : -((j.val : ZMod (2 * (k + 1))) + 1) = -((j.val + 1 : ℕ) : ZMod (2 * (k + 1))) := by
      push_cast
      rfl
    rw [e1, e2]
    exact temporalAction_reverse n _ _ _
  simp only [hslab]
  have hcast (j : Fin (k + 1)) : ((j.val : ℕ) : ZMod (2 * (k + 1))) + 1 = ((j.val + 1 : ℕ) : ZMod (2 * (k + 1))) := by
    push_cast
    rfl
  simp only [hcast]
  ring

instance : BorelSpace (Half n k) := by
  have h1 : BorelSpace (Fin k → Slice n) := inferInstance
  have h2 : BorelSpace (Fin (k + 1) → SliceGauge n Q) := inferInstance
  exact Prod.borelSpace

instance : BorelSpace (Bdry n × (Half n k × Half n k)) := by
  have h0 : BorelSpace (Bdry n) := Prod.borelSpace
  have h1 : BorelSpace (Half n k × Half n k) := Prod.borelSpace
  exact Prod.borelSpace

open BoundaryReflectionGluing in
/-- **The split carries the chain law to the boundary-gluing law.** -/
theorem split_law (β : ℝ) :
    MeasurePreserving (split n k) (chainLaw (2 * (k + 1)) n β)
      (law (bdryRef n) (halfRef n k) (fun _ => 1) (halfAction n k β)) := by
  have hw : Continuous (weight (X := Half n k) (B := Bdry n) (fun _ => 1) (halfAction n k β)) :=
    weight_continuous _ continuous_const _ (halfAction_continuous n k β)
  have h := GibbsReflectionTransport.normalized_transport (split_preserving n k)
    (fun z => ENNReal.ofReal (weight (fun _ => 1) (halfAction n k β) z)) hw.measurable.ennreal_ofReal
  have hd (c : Chain (2 * (k + 1)) n) : Real.exp (-chainAction (2 * (k + 1)) n β c) =
      weight (fun _ => 1) (halfAction n k β) (split n k c) := by
    rw [chainAction_split]
    simp only [weight, split, one_mul, neg_add_rev, Real.exp_add]
    ring
  have hd' : (fun c => ENNReal.ofReal (Real.exp (-chainAction (2 * (k + 1)) n β c))) =
      (fun z => ENNReal.ofReal (weight (fun _ => 1) (halfAction n k β) z)) ∘ split n k := by
    funext c
    simp only [Function.comp, hd]
  unfold chainLaw
  rw [hd']
  exact h

/-- **Reflection positivity of the twisted law at every even time extent `2 (k + 1)` and every
spatial size `n`.** The observable is any continuous function of the slices `0, …, k + 1` and the
temporal links between them. -/
theorem chain_reflection_positive (β : ℝ) (f : Bdry n × Half n k → ℂ) (hf : Continuous f) :
    0 ≤ (∫ c, star (f (bdry n k (chainReflect _ n c), half n k (chainReflect _ n c))) *
      f (bdry n k c, half n k c) ∂chainLaw (2 * (k + 1)) n β).re ∧
    (∫ c, star (f (bdry n k (chainReflect _ n c), half n k (chainReflect _ n c))) *
      f (bdry n k c, half n k c) ∂chainLaw (2 * (k + 1)) n β).im = 0 := by
  let Φ : Bdry n × (Half n k × Half n k) → ℂ := fun z =>
    star (BoundaryReflectionGluing.halfObservable f (BoundaryReflectionGluing.reflection z)) *
      BoundaryReflectionGluing.halfObservable f z
  have hΦ : Continuous Φ := by
    have h1 : Continuous fun z : Bdry n × (Half n k × Half n k) => f (z.1, z.2.1) :=
      hf.comp (by fun_prop)
    have h2 : Continuous fun z : Bdry n × (Half n k × Half n k) => f (z.1, z.2.2) :=
      hf.comp (by fun_prop)
    exact (continuous_star.comp h1).mul h2
  have hp := split_law n k β
  have hmap := integral_map (μ := chainLaw (2 * (k + 1)) n β) hp.measurable.aemeasurable
    (f := Φ) hΦ.aestronglyMeasurable
  rw [hp.map_eq] at hmap
  have heq : (fun c : Chain (2 * (k + 1)) n =>
      star (f (bdry n k (chainReflect _ n c), half n k (chainReflect _ n c))) *
        f (bdry n k c, half n k c)) = fun c => Φ (split n k c) := by
    funext c
    simp only [Φ, split, BoundaryReflectionGluing.halfObservable, BoundaryReflectionGluing.reflection,
      Prod.swap, bdry_reflect]
  simp only [heq]
  rw [← hmap]
  exact BoundaryReflectionGluing.reflection_positive _ _ _ continuous_const (fun _ => one_pos) _
    (halfAction_continuous n k β) f hf

/-- At `T = L` the reflection is the existing one. -/
theorem toChain_reflect (N : ℕ) [NeZero N] (U : Configuration (Vertex N) Q) :
    toChain N (PeriodicTimeReflection.reflectConfiguration N Q U) = chainReflect N N (toChain N U) := by
  have hv (t : ZMod N) (x : SpatialVertex N) :
      PeriodicTimeReflection.reflectVertex N (embed N t x) = embed N (-t) x := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [PeriodicTimeReflection.reflectVertex, embed]
    · simp [PeriodicTimeReflection.reflectVertex, embed, Fin.succ_ne_zero]
  refine Prod.ext (funext fun t => funext fun e => ?_) (funext fun t => funext fun x => ?_)
  · have h := PeriodicTimeReflection.reflect_link_spatial N Q U (embed N t e.1) e.2.succ (Fin.succ_ne_zero _)
    change PeriodicTimeReflection.linkValue N Q (PeriodicTimeReflection.reflectConfiguration N Q U)
      (embed N t e.1) e.2.succ = PeriodicTimeReflection.linkValue N Q U (embed N (-t) e.1) e.2.succ
    rw [h, hv]
  · have h := PeriodicTimeReflection.reflect_link_time N Q U (embed N t x)
    change PeriodicTimeReflection.linkValue N Q (PeriodicTimeReflection.reflectConfiguration N Q U)
      (embed N t x) 0 = (PeriodicTimeReflection.linkValue N Q U (embed N (-(t + 1)) x) 0)⁻¹
    rw [h, embed_time_step, hv]

end Reflection

open TwistedVacuum
open WilsonPositiveGroundState (complexify)
open CompactKernelOperator
open scoped ComplexConjugate InnerProductSpace Topology

/-! ### Long time extent: the vacuum dominates at fixed cutoff -/

section Dominance

section Abstract
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The powers of a self-adjoint operator with a top eigenvector and a gap, in matrix elements. -/
theorem matrix_element_dominance (A : H →L[ℂ] H)
    (hsym : ∀ x y, inner ℂ (A x) y = inner ℂ x (A y)) (Ω : H) (hΩ : ‖Ω‖ = 1) (lam ρ : ℝ) (hlam : 0 ≤ lam)
    (hρ : 0 ≤ ρ) (htop : A Ω = lam • Ω)
    (hgap : ∀ f, inner ℂ Ω f = 0 → ‖A f‖ ≤ ρ * lam * ‖f‖) (x y : H) (k : ℕ) :
    ‖inner ℂ x ((A ^ k) y) - (lam : ℂ) ^ k * (inner ℂ x Ω * inner ℂ Ω y)‖ ≤
      (ρ * lam) ^ k * (‖x‖ * ‖y‖) := by
  have hself : inner ℂ Ω Ω = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hΩ]
    simp
  set a : ℂ := inner ℂ Ω y with ha
  set p : H := y - a • Ω with hp
  have hpo : inner ℂ Ω p = (0 : ℂ) := by
    rw [hp, inner_sub_right, inner_smul_right, hself, mul_one, ← ha, sub_self]
  have hy : y = a • Ω + p := by
    rw [hp]
    abel
  have hAΩ (k : ℕ) : (A ^ k) Ω = (lam : ℂ) ^ k • Ω := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_smul, htop,
        RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, pow_succ]
      rfl
  have hpow (k : ℕ) : inner ℂ Ω ((A ^ k) p) = (0 : ℂ) ∧ ‖(A ^ k) p‖ ≤ (ρ * lam) ^ k * ‖p‖ := by
    induction k with
    | zero => simpa using hpo
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      rw [pow_succ', ContinuousLinearMap.mul_apply]
      constructor
      · rw [← hsym, htop, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, h1, mul_zero]
      · refine (hgap _ h1).trans ?_
        calc ρ * lam * ‖(A ^ k) p‖ ≤ ρ * lam * ((ρ * lam) ^ k * ‖p‖) :=
              mul_le_mul_of_nonneg_left h2 (mul_nonneg hρ hlam)
          _ = (ρ * lam) ^ (k + 1) * ‖p‖ := by ring
  have hpn : ‖p‖ ≤ ‖y‖ := by
    have hsq := norm_add_sq (𝕜 := ℂ) (a • Ω) p
    rw [inner_smul_left, hpo, mul_zero] at hsq
    simp only [map_zero, mul_zero, add_zero] at hsq
    rw [← hy] at hsq
    have : ‖p‖ ^ 2 ≤ ‖y‖ ^ 2 := by
      rw [hsq]
      nlinarith [sq_nonneg ‖a • Ω‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
  have hsplit : inner ℂ x ((A ^ k) y) - (lam : ℂ) ^ k * (inner ℂ x Ω * a) = inner ℂ x ((A ^ k) p) := by
    conv_lhs => rw [hy]
    rw [map_add, map_smul, hAΩ, inner_add_right, inner_smul_right, inner_smul_right]
    ring
  rw [hsplit]
  refine (norm_inner_le_norm _ _).trans ?_
  have h2 := (hpow k).2
  have hnn : 0 ≤ (ρ * lam) ^ k := pow_nonneg (mul_nonneg hρ hlam) k
  calc ‖x‖ * ‖(A ^ k) p‖ ≤ ‖x‖ * ((ρ * lam) ^ k * ‖y‖) :=
        mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left hpn hnn)) (norm_nonneg _)
    _ = _ := by ring

end Abstract

section Kernels
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- The rows of the powers of the kernel are the powers of the operator on a row. -/
theorem row_powK (K : C(X × X, ℝ)) (hK : ∀ x y, K (x, y) = K (y, x)) (m : ℕ) (y : X) :
    row μ (powK μ K m) y = ((operator μ K) ^ m) (row μ K y) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ← ih]
    change ContinuousMap.toLp 2 μ ℂ (rowContinuous (powK μ K (m + 1)) y) =
      ContinuousMap.toLp 2 μ ℂ (smoothing μ K (row μ (powK μ K m) y))
    congr 1
    ext w
    have h1 : smoothing μ K (row μ (powK μ K m) y) w =
        ∫ z, (K (w, z) : ℂ) * rowContinuous (powK μ K m) y z ∂μ :=
      smoothing_continuous_input μ K _ w
    rw [h1]
    change ((powK μ K (m + 1) (y, w) : ℝ) : ℂ) = _
    rw [powK_succ, compK_apply, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [rowContinuous, ContinuousMap.coe_mk]
    rw [hK z w]
    push_cast
    ring

/-- Matrix elements of powers between rows are the kernels of higher powers. -/
theorem inner_row_pow (K : C(X × X, ℝ)) (hK : ∀ x y, K (x, y) = K (y, x)) (m : ℕ) (x y : X) :
    inner ℂ (row μ K y) (((operator μ K) ^ m) (row μ K x)) = ((powK μ K (m + 1) (x, y) : ℝ) : ℂ) := by
  rw [← row_powK μ K hK]
  unfold row
  rw [MeasureTheory.ContinuousMap.inner_toLp, powK_succ, compK_apply, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [rowContinuous, ContinuousMap.coe_mk, Complex.conj_ofReal]
  rw [hK y z]
  push_cast
  rfl

theorem tendsto_of_geometric (a : ℕ → ℝ) (L C ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (h : ∀ m, |a m - L| ≤ C * ρ ^ m) : Filter.Tendsto a Filter.atTop (𝓝 L) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun m => C * ρ ^ m) (fun _ => norm_nonneg _) h ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1).const_mul C

end Kernels

section Concrete
variable (n : ℕ) [NeZero n] (β : ℝ)

local notation "μ'" => WilsonSlabOperator.measure n
local notation "Kt" => twistedKernel n β
local notation "lam" => ‖TwistedTransfer.transfer n β‖

/-- **The kernel of a high power of `T` is the vacuum projector, up to a geometric error.** The rate
`ρ` is the finite-cutoff gap, with no control in `n` or `β`. -/
theorem kernel_dominance (hβ : 0 ≤ β) :
    ∃ η : C(Slice n, ℝ), (∀ u, 0 < η u) ∧ ‖ContinuousMap.toLp 2 (μ') ℂ (complexify η)‖ = 1 ∧
      (∀ u, (∫ v, Kt (u, v) * η v ∂μ') = lam * η u) ∧
      ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (m : ℕ) (x y : Slice n),
        |powK (μ') Kt (m + 1) (x, y) - lam ^ (m + 2) * (η x * η y)| ≤ (ρ * lam) ^ m * ‖Kt‖ ^ 2 := by
  obtain ⟨η, hη, hnorm, heig⟩ := exists_positive_top n β hβ
  obtain ⟨hlam, -⟩ := top_eigenvector n β hβ
  obtain ⟨Ω', h1, h2, -, h4⟩ := neutral_vacuum n β hβ
  set Ω := ContinuousMap.toLp 2 (μ') ℂ (complexify η) with hΩ
  have hrow (y : Slice n) : inner ℂ (row (μ') Kt y) Ω = ((lam * η y : ℝ) : ℂ) := by
    change smoothing (μ') Kt (ContinuousMap.toLp 2 (μ') ℂ (complexify η)) y = _
    rw [smoothing_continuous_input, ← heig y, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [complexify, ContinuousMap.coe_mk]
    push_cast
    rfl
  have hTΩ : TwistedTransfer.transfer n β Ω = lam • Ω := by
    have hs : smoothing (μ') Kt Ω = (lam : ℂ) • complexify η := by
      ext u
      change inner ℂ (row (μ') Kt u) Ω = _
      rw [hrow]
      simp [complexify]
    change ContinuousMap.toLp 2 (μ') ℂ (smoothing (μ') Kt Ω) = _
    rw [hs, map_smul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  obtain ⟨a, ha⟩ := h4 Ω hTΩ
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    rw [ha, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hsimple : ∀ v, TwistedTransfer.transfer n β v = lam • v → ∃ c : ℂ, v = c • Ω := by
    intro v hv
    obtain ⟨c, hc⟩ := h4 v hv
    refine ⟨c * a⁻¹, ?_⟩
    rw [hc, ha, smul_smul, mul_assoc, inv_mul_cancel₀ ha0, mul_one]
  obtain ⟨ρ, hρ0, hρ1, hgap⟩ := TwistedFiniteGap.gap_of_simple _ (transfer_positive n β hβ)
    (TwistedTransfer.transfer_compact n β) Ω hnorm hTΩ hlam hsimple
  refine ⟨η, hη, hnorm, heig, ρ, hρ0, hρ1, fun m x y => ?_⟩
  have hsym : ∀ x y, inner ℂ (TwistedTransfer.transfer n β x) y =
      inner ℂ x (TwistedTransfer.transfer n β y) := (transfer_positive n β hβ).isSymmetric
  have hdom := matrix_element_dominance (TwistedTransfer.transfer n β) hsym Ω hnorm lam ρ hlam.le hρ0 hTΩ
    hgap (row (μ') Kt y) (row (μ') Kt x) m
  have hin := inner_row_pow (μ') Kt (twistedKernel_symm n β) m x y
  have hk : (TwistedTransfer.transfer n β) = operator (μ') Kt := rfl
  rw [hk] at hdom
  rw [hin, hrow] at hdom
  rw [← hk, show inner ℂ Ω (row (μ') Kt x) = conj (inner ℂ (row (μ') Kt x) Ω) from
    (inner_conj_symm _ _).symm, hrow, Complex.conj_ofReal] at hdom
  have hval : ((powK (μ') Kt (m + 1) (x, y) : ℝ) : ℂ) - (lam : ℂ) ^ m *
      (((lam * η y : ℝ) : ℂ) * ((lam * η x : ℝ) : ℂ)) =
      ((powK (μ') Kt (m + 1) (x, y) - lam ^ (m + 2) * (η x * η y) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hval, Complex.norm_real, Real.norm_eq_abs] at hdom
  refine hdom.trans ?_
  have hnn : 0 ≤ (ρ * lam) ^ m := pow_nonneg (mul_nonneg hρ0 hlam.le) m
  refine mul_le_mul_of_nonneg_left ?_ hnn
  rw [sq]
  exact mul_le_mul (row_norm_le _ _ _) (row_norm_le _ _ _) (norm_nonneg _) (norm_nonneg _)

theorem integral_eta_sq (η : C(Slice n, ℝ)) (hnorm : ‖ContinuousMap.toLp 2 (μ') ℂ (complexify η)‖ = 1) :
    ∫ x, η x * η x ∂μ' = 1 := by
  have h := norm_embed_sq (μ') (complexify η)
  rw [hnorm] at h
  simp only [complexify, ContinuousMap.coe_mk, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  simp only [← sq]
  linarith only [h]

theorem chainZ_pos (T : ℕ) [NeZero T] : 0 < chainZ T n β := by
  apply integral_exp_pos
  exact (Real.continuous_exp.comp (chainAction_continuous T n β).neg).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) |>.congr (Filter.Eventually.of_forall fun _ => rfl)

/-- Expectations under the chain law are ratios. -/
theorem chainLaw_integral (T : ℕ) [NeZero T] (F : Chain T n → ℝ) :
    ∫ c, F c ∂chainLaw T n β =
      (∫ c, F c * Real.exp (-chainAction T n β c) ∂chainRef T n) / chainZ T n β := by
  have hm : Measurable fun c : Chain T n => ENNReal.ofReal (Real.exp (-chainAction T n β c)) :=
    (Real.continuous_exp.comp (chainAction_continuous T n β).neg).measurable.ennreal_ofReal
  have hZ : (∫⁻ c, ENNReal.ofReal (Real.exp (-chainAction T n β c)) ∂chainRef T n) =
      ENNReal.ofReal (chainZ T n β) := by
    unfold chainZ
    have hi : Integrable (fun c : Chain T n => Real.exp (-chainAction T n β c)) (chainRef T n) :=
      (Real.continuous_exp.comp (chainAction_continuous T n β).neg).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    exact (ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).symm
  unfold chainLaw
  rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), hZ]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (chainZ_pos n β T).le, div_eq_inv_mul]
  congr 2
  funext c
  ring

/-- **The partition function at long time extent.** `Z_T / ‖T‖^T → 1`, at fixed `n` and `β`. So the
free energy per unit time is `log ‖T‖`. -/
theorem chainZ_dominance (hβ : 0 ≤ β) :
    ∃ ρ C : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ m : ℕ, |chainZ (m + 2) n β / lam ^ (m + 2) - 1| ≤ C * ρ ^ m := by
  obtain ⟨η, -, hnorm, -, ρ, hρ0, hρ1, hdom⟩ := kernel_dominance n β hβ
  obtain ⟨hlam, -⟩ := top_eigenvector n β hβ
  refine ⟨ρ, ‖Kt‖ ^ 2 / lam ^ 2, hρ0, hρ1, fun m => ?_⟩
  have hZ : chainZ (m + 2) n β = ∫ x, powK (μ') Kt (m + 1) (x, x) ∂μ' := chainZ_eq (m + 2) n β
  have hi1 : Integrable (fun x => powK (μ') Kt (m + 1) (x, x)) (μ') :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun x => lam ^ (m + 2) * (η x * η x)) (μ') :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)
  have hdiff : chainZ (m + 2) n β - lam ^ (m + 2) =
      ∫ x, (powK (μ') Kt (m + 1) (x, x) - lam ^ (m + 2) * (η x * η x)) ∂μ' := by
    rw [integral_sub hi1 hi2, integral_const_mul, integral_eta_sq n η hnorm, mul_one, hZ]
  have hbound : |chainZ (m + 2) n β - lam ^ (m + 2)| ≤ (ρ * lam) ^ m * ‖Kt‖ ^ 2 := by
    rw [hdiff]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ x, |powK (μ') Kt (m + 1) (x, x) - lam ^ (m + 2) * (η x * η x)| ∂μ' ≤
        ∫ _, (ρ * lam) ^ m * ‖Kt‖ ^ 2 ∂μ' :=
          integral_mono (hi1.sub hi2).abs (integrable_const _) fun x => hdom m x x
      _ = _ := by simp
  have hpow : 0 < lam ^ (m + 2) := pow_pos hlam _
  have he : chainZ (m + 2) n β / lam ^ (m + 2) - 1 = (chainZ (m + 2) n β - lam ^ (m + 2)) / lam ^ (m + 2) := by
    field_simp
  rw [he, abs_div, abs_of_pos hpow, div_le_iff₀ hpow]
  refine hbound.trans_eq ?_
  rw [mul_pow, pow_add lam m 2]
  field_simp

/-- **The two-point function at long time extent.** At fixed `n`, `β` and separation `s + 1`, the
expectation under the law of time extent `T → ∞` converges to the vacuum matrix element. Nothing here
is uniform in `n` or `β`. -/
theorem two_point_limit (hβ : 0 ≤ β) (s : ℕ) (f g : C(Slice n, ℝ)) :
    ∃ η : C(Slice n, ℝ), (∀ u, 0 < η u) ∧ ‖ContinuousMap.toLp 2 (μ') ℂ (complexify η)‖ = 1 ∧
      (∀ u, (∫ v, Kt (u, v) * η v ∂μ') = lam * η u) ∧
      Filter.Tendsto (fun m : ℕ => ∫ c, f (c.1 0) * g (c.1 ((s + 1 : ℕ) : ZMod (s + (m + 1) + 2)))
          ∂chainLaw (s + (m + 1) + 2) n β) Filter.atTop
        (𝓝 ((∫ x, ∫ y, f x * η x * powK (μ') Kt s (x, y) * g y * η y ∂μ' ∂μ') / lam ^ (s + 1))) := by
  obtain ⟨η, hη, hnorm, heig, ρ, hρ0, hρ1, hdom⟩ := kernel_dominance n β hβ
  obtain ⟨hlam, -⟩ := top_eigenvector n β hβ
  refine ⟨η, hη, hnorm, heig, ?_⟩
  set P := powK (μ') Kt s with hP
  let G : Slice n × Slice n → ℝ := fun p => f p.1 * P p * g p.2
  have hG : Continuous G := by fun_prop
  -- numerator
  set V : ℝ := ∫ x, ∫ y, f x * η x * P (x, y) * g y * η y ∂μ' ∂μ' with hV
  let N : ℕ → ℝ := fun m => ∫ x, ∫ y, f x * P (x, y) * g y * powK (μ') Kt (m + 1) (y, x) ∂μ' ∂μ'
  have hN (m : ℕ) : |N m / lam ^ (m + 2) - V| ≤
      (‖f‖ * ‖P‖ * ‖g‖ * (‖Kt‖ ^ 2 / lam ^ 2)) * ρ ^ m := by
    have hpow : 0 < lam ^ (m + 2) := pow_pos hlam _
    let R : Slice n × Slice n → ℝ := fun p => powK (μ') Kt (m + 1) (p.2, p.1)
    have hR : Continuous R := by
      have := (powK (μ') Kt (m + 1)).continuous.comp (continuous_snd.prodMk continuous_fst)
      exact this
    have hIGR : Integrable (fun p => G p * R p) ((μ').prod (μ')) :=
      (hG.mul hR).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hNp : N m = ∫ p, G p * R p ∂(μ').prod (μ') := by
      rw [integral_prod _ hIGR]
    have hVc : Continuous fun p : Slice n × Slice n => G p * (η p.2 * η p.1) := by fun_prop
    have hVp : V = ∫ p, G p * (η p.2 * η p.1) ∂(μ').prod (μ') := by
      rw [integral_prod _ (hVc.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
      rw [hV]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [G]
      ring
    have hdiff : N m - lam ^ (m + 2) * V =
        ∫ p, G p * (R p - lam ^ (m + 2) * (η p.2 * η p.1)) ∂(μ').prod (μ') := by
      have hIV : Integrable (fun p => lam ^ (m + 2) * (G p * (η p.2 * η p.1))) ((μ').prod (μ')) :=
        (continuous_const.mul hVc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      rw [hNp, hVp, ← integral_const_mul, ← integral_sub hIGR hIV]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      dsimp only
      ring
    have hGb (p : Slice n × Slice n) : |G p| ≤ ‖f‖ * ‖P‖ * ‖g‖ := by
      simp only [G, abs_mul]
      have h1 : |f p.1| ≤ ‖f‖ := f.norm_coe_le_norm p.1
      have h2 : |P p| ≤ ‖P‖ := P.norm_coe_le_norm p
      have h3 : |g p.2| ≤ ‖g‖ := g.norm_coe_le_norm p.2
      exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)) h3 (abs_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have hbound : |N m - lam ^ (m + 2) * V| ≤ ‖f‖ * ‖P‖ * ‖g‖ * ((ρ * lam) ^ m * ‖Kt‖ ^ 2) := by
      rw [hdiff]
      refine (abs_integral_le_integral_abs).trans ?_
      have hci : Continuous fun p : Slice n × Slice n =>
          G p * (R p - lam ^ (m + 2) * (η p.2 * η p.1)) := by fun_prop
      calc ∫ p, |G p * (R p - lam ^ (m + 2) * (η p.2 * η p.1))| ∂(μ').prod (μ') ≤
          ∫ _, ‖f‖ * ‖P‖ * ‖g‖ * ((ρ * lam) ^ m * ‖Kt‖ ^ 2) ∂(μ').prod (μ') := by
            refine integral_mono (hci.abs.integrable_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace _)) (integrable_const _) fun p => ?_
            dsimp only
            rw [abs_mul]
            exact mul_le_mul (hGb p) (hdom m p.2 p.1) (abs_nonneg _)
              (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))
        _ = _ := by simp
    have he : N m / lam ^ (m + 2) - V = (N m - lam ^ (m + 2) * V) / lam ^ (m + 2) := by
      field_simp
    rw [he, abs_div, abs_of_pos hpow, div_le_iff₀ hpow]
    refine hbound.trans_eq ?_
    rw [mul_pow, pow_add lam m 2]
    field_simp
  have ha := tendsto_of_geometric (fun m => N m / lam ^ (m + 2)) V _ ρ hρ0 hρ1 hN
  obtain ⟨ρ', C', hρ'0, hρ'1, hZd⟩ := chainZ_dominance n β hβ
  have hc := tendsto_of_geometric (fun m => chainZ (m + 2) n β / lam ^ (m + 2)) 1 C' ρ' hρ'0 hρ'1 hZd
  have hshift : Filter.Tendsto (fun m : ℕ => s + m + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  have hb := hc.comp hshift
  have hlim := ((ha.div hb one_ne_zero).div_const (lam ^ (s + 1)))
  rw [div_one] at hlim
  refine hlim.congr fun m => ?_
  have hT : s + (m + 1) + 2 = s + m + 1 + 2 := rfl
  have hE : ∫ c, f (c.1 0) * g (c.1 ((s + 1 : ℕ) : ZMod (s + (m + 1) + 2)))
      ∂chainLaw (s + (m + 1) + 2) n β = N m / chainZ (s + (m + 1) + 2) n β := by
    rw [chainLaw_integral, two_point]
  rw [hE]
  have hZpos := chainZ_pos n β (s + (m + 1) + 2)
  have hZne : chainZ (s + m + 1 + 2) n β ≠ 0 := hZpos.ne'
  change N m / lam ^ (m + 2) / (chainZ (s + m + 1 + 2) n β / lam ^ (s + m + 1 + 2)) / lam ^ (s + 1) =
    N m / chainZ (s + m + 1 + 2) n β
  have hl : lam ≠ 0 := hlam.ne'
  have hp : lam ^ (s + m + 1 + 2) = lam ^ (m + 2) * lam ^ (s + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hp]
  field_simp

end Concrete
end Dominance

/-! ### The flips on the chain -/

section ChainFlips
variable (T n : ℕ) [NeZero T] [NeZero n]

/-- A spatial slab flip acts on every slice. -/
def chainFlip (i : Fin 3) (c : ZMod n) (x : Chain T n) : Chain T n :=
  (fun t => TwistedTransfer.flip n i c (x.1 t), x.2)

/-- A temporal flip acts on the temporal links of one slab. -/
def chainFlipTime (t₀ : ZMod T) (x : Chain T n) : Chain T n :=
  (x.1, fun t y => if t = t₀ then ω * x.2 t y else x.2 t y)

theorem twistedPotential_flip (i : Fin 3) (c : ZMod n) (u : Slice n) :
    twistedPotential n (TwistedTransfer.flip n i c u) = twistedPotential n u := by
  rw [twistedPotential_eq, twistedPotential_eq, potential_flip, defect_flip]

theorem chainAction_flip (β : ℝ) (i : Fin 3) (c : ZMod n) (x : Chain T n) :
    chainAction T n β (chainFlip T n i c x) = chainAction T n β x := by
  unfold chainAction chainFlip
  simp only [twistedPotential_flip, temporalAction_flip]

theorem temporalAction_center (u v : Slice n) (h : SliceGauge n Q) :
    temporalAction character 2 u v (fun y => ω * h y) = temporalAction character 2 u v h := by
  unfold temporalAction temporalHolonomy
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => ?_
  congr 3
  rw [inv_ω_mul]
  apply Subtype.ext
  simp only [coe_mul, ω_coe, neg_mul, mul_neg, neg_neg, one_mul]

theorem chainAction_flipTime (β : ℝ) (t₀ : ZMod T) (x : Chain T n) :
    chainAction T n β (chainFlipTime T n t₀ x) = chainAction T n β x := by
  unfold chainAction chainFlipTime
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases ht : t = t₀
  · simp only [if_pos ht]
    rw [temporalAction_center]
  · simp only [if_neg ht]

theorem chainFlip_ref (i : Fin 3) (c : ZMod n) :
    MeasurePreserving (chainFlip T n i c) (chainRef T n) (chainRef T n) := by
  have h1 : MeasurePreserving (fun u : ZMod T → Slice n => fun t => TwistedTransfer.flip n i c (u t))
      (Measure.pi fun _ : ZMod T => WilsonSlabOperator.measure n)
      (Measure.pi fun _ : ZMod T => WilsonSlabOperator.measure n) :=
    measurePreserving_pi (fun _ : ZMod T => WilsonSlabOperator.measure n)
      (fun _ : ZMod T => WilsonSlabOperator.measure n) (f := fun _ => TwistedTransfer.flip n i c)
      (fun _ => flip_measurePreserving n i c)
  exact h1.prod (MeasurePreserving.id _)

theorem chainFlipTime_ref (t₀ : ZMod T) :
    MeasurePreserving (chainFlipTime T n t₀) (chainRef T n) (chainRef T n) := by
  have hone (s : ZMod T) : MeasurePreserving
      (fun h : SliceGauge n Q => fun y => if s = t₀ then ω * h y else h y)
      (temporalHaar (n := n) (G := Q)) (temporalHaar (n := n) (G := Q)) := by
    by_cases hs : s = t₀
    · simp only [if_pos hs]
      exact measurePreserving_pi (fun _ : SpatialVertex n => compactHaar Q)
        (fun _ : SpatialVertex n => compactHaar Q) (f := fun _ q => ω * q)
        (fun _ => measurePreserving_mul_left _ (ω : Q))
    · simp only [if_neg hs]
      exact MeasurePreserving.id _
  have h2 := measurePreserving_pi (fun _ : ZMod T => temporalHaar (n := n) (G := Q))
    (fun _ : ZMod T => temporalHaar (n := n) (G := Q)) hone
  exact (MeasurePreserving.id _).prod h2

theorem chainLaw_preserved (φ : Chain T n → Chain T n) (β : ℝ)
    (hφ : MeasurePreserving φ (chainRef T n) (chainRef T n))
    (hS : ∀ x, chainAction T n β (φ x) = chainAction T n β x) :
    MeasurePreserving φ (chainLaw T n β) (chainLaw T n β) := by
  unfold chainLaw
  apply MeasurePreserving.smul_measure
  apply preserves_withDensity hφ _
    (Real.continuous_exp.comp (chainAction_continuous T n β).neg).measurable.ennreal_ofReal
  intro x
  simp only [Function.comp, hS]

/-- **The law at time extent `T` is invariant under all the flips.** -/
theorem chainFlip_law (β : ℝ) (i : Fin 3) (c : ZMod n) :
    MeasurePreserving (chainFlip T n i c) (chainLaw T n β) (chainLaw T n β) :=
  chainLaw_preserved T n _ β (chainFlip_ref T n i c) (chainAction_flip T n β i c)

theorem chainFlipTime_law (β : ℝ) (t₀ : ZMod T) :
    MeasurePreserving (chainFlipTime T n t₀) (chainLaw T n β) (chainLaw T n β) :=
  chainLaw_preserved T n _ β (chainFlipTime_ref T n t₀) (chainAction_flipTime T n β t₀)

/-- At `T = L` the chain flips are the flips of the lattice. -/
theorem toChain_flip (N : ℕ) [NeZero N] (i : Fin 3) (c : ZMod N) (U : Configuration (Vertex N) Q) :
    toChain N (flip4 N i.succ c U) = chainFlip N N i c (toChain N U) :=
  Prod.ext (funext fun t => slice_flip4 N i c U t) (funext fun t => temporal_flip4 N i c U t)

theorem toChain_flipTime (N : ℕ) [NeZero N] (c : ZMod N) (U : Configuration (Vertex N) Q) :
    toChain N (flip4 N 0 c U) = chainFlipTime N N c (toChain N U) := by
  refine Prod.ext (funext fun t => slice_flip4_zero N c U t) (funext fun t => funext fun x => ?_)
  exact temporal_flip4_zero N c U t x

/-- **Selection rule at time extent `T`.** A continuous observable odd under a flip has vanishing
expectation. -/
theorem chain_odd_expectation (β : ℝ) (φ : Chain T n → Chain T n)
    (hφ : MeasurePreserving φ (chainLaw T n β) (chainLaw T n β)) (F : Chain T n → ℂ)
    (hF : Continuous F) (hodd : ∀ x, F (φ x) = -F x) : ∫ x, F x ∂chainLaw T n β = 0 := by
  have hmap := integral_map (μ := chainLaw T n β) hφ.measurable.aemeasurable (f := F)
    hF.aestronglyMeasurable
  rw [hφ.map_eq] at hmap
  simp only [hodd, integral_neg] at hmap
  have h2 : (2 : ℂ) * ∫ x, F x ∂chainLaw T n β = 0 := by
    linear_combination hmap
  simpa using h2

end ChainFlips
/-! ### The trace with a flip inserted -/

section TraceFlip
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ] [μ.WeaklyRegular]

/-- **The trace of a symmetry times a power of `T`.** For an involution `g` preserving `μ` and the
symmetric kernel `K`, the trace of `g T^(m+2)` is the integral of the kernel of `T^(m+2)` between
`x` and `g x`. -/
theorem trace_involution {ι : Type*} [Countable ι] (b : HilbertBasis ι ℂ (Hilbert μ))
    (K : C(X × X, ℝ)) (hK : ∀ x y, K (x, y) = K (y, x)) (g : C(X, X))
    (hg : MeasurePreserving g μ μ) (hgg : ∀ x, g (g x) = x) (hKg : ∀ x y, K (g x, g y) = K (x, y))
    (m : ℕ) :
    HasSum (fun k => inner ℂ (b k) ((Lp.compMeasurePreservingₗᵢ ℂ g hg)
        (((operator μ K) ^ (m + 2)) (b k))))
      ((∫ x, powK μ K (m + 1) (x, g x) ∂μ : ℝ) : ℂ) := by
  let F : Hilbert μ →ₗᵢ[ℂ] Hilbert μ := Lp.compMeasurePreservingₗᵢ ℂ g hg
  let E : X ≃ᵐ X :=
    { toFun := g, invFun := g, left_inv := hgg, right_inv := hgg,
      measurable_toFun := g.continuous.measurable, measurable_invFun := g.continuous.measurable }
  have hE : MeasurePreserving E μ μ := hg
  let Lg : C(X × X, ℝ) := ⟨fun p => K (p.1, g p.2), by fun_prop⟩
  have hFF (f : Hilbert μ) : F (F f) = f := by
    apply Lp.ext
    have h1 : (F (F f) : X → ℂ) =ᵐ[μ] ((F f : Hilbert μ) ∘ g) := Lp.coeFn_compMeasurePreserving _ hg
    have h2 : (F f : X → ℂ) =ᵐ[μ] ((f : Hilbert μ) ∘ g) := Lp.coeFn_compMeasurePreserving _ hg
    have h3 := hg.quasiMeasurePreserving.ae_eq_comp h2
    refine h1.trans (h3.trans (Filter.Eventually.of_forall fun u => ?_))
    simp only [Function.comp, hgg]
  have hLg (f : Hilbert μ) : operator μ Lg f = operator μ K (F f) := by
    change ContinuousMap.toLp 2 μ ℂ (smoothing μ Lg f) = ContinuousMap.toLp 2 μ ℂ (smoothing μ K (F f))
    congr 1
    ext x
    rw [smoothing_integral, smoothing_integral]
    have hc : (∫ w, (K (x, w) : ℂ) * (F f) w ∂μ) = ∫ w, (K (x, w) : ℂ) * f (g w) ∂μ := by
      have h2 : (F f : X → ℂ) =ᵐ[μ] ((f : Hilbert μ) ∘ g) := Lp.coeFn_compMeasurePreserving _ hg
      exact integral_congr_ae (h2.mono fun w hw => by dsimp only; rw [hw]; rfl)
    rw [hc]
    have hsub := hE.integral_comp' (fun w => (K (x, g w) : ℂ) * f w)
    change ∫ y, (K (x, g y) : ℂ) * f y ∂μ = _
    rw [← hsub]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    change (K (x, g (g w)) : ℂ) * f (g w) = _
    rw [hgg]
  have hsym : ∀ f h, inner ℂ (operator μ K f) h = inner ℂ f (operator μ K h) :=
    operator_symmetric μ K hK
  have h := trace_comp μ b (powK μ K m) Lg
  have hval : (∫ x, ∫ w, powK μ K m (x, w) * Lg (x, w) ∂μ ∂μ) = ∫ x, powK μ K (m + 1) (x, g x) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [powK_succ, compK_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    dsimp only
    change _ * K (x, g w) = _
    rw [← hKg x (g w), hgg, hK (g x) w]
  rw [hval] at h
  convert h using 2 with k
  have hself (a c : Hilbert μ) : inner ℂ (F a) c = inner ℂ a (F c) := by
    have := F.inner_map_map (F a) c
    rw [hFF] at this
    exact this.symm
  rw [hLg, hsym, operator_powK, hself, pow_succ' _ (m + 1)]
  rfl

end TraceFlip

section Spectrum
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **A positive compact operator has a Hilbert basis of eigenvectors.** -/
theorem exists_eigenbasis (A : H →L[ℂ] H) (hpos : A.IsPositive) (hc : IsCompactOperator A) :
    ∃ (w : Set H) (b : HilbertBasis w ℂ H) (lam : w → ℝ), (∀ k, 0 ≤ lam k) ∧
      ∀ k, A (b k) = lam k • b k := by
  classical
  have hsym : ∀ x y, inner ℂ (A x) y = inner ℂ x (A y) := hpos.isSymmetric
  let P : Set (Set H) := {w | Orthonormal ℂ ((↑) : w → H) ∧ ∀ v ∈ w, ∃ r : ℝ, 0 ≤ r ∧ A v = r • v}
  obtain ⟨w, hw⟩ : ∃ w, Maximal (· ∈ P) w := by
    refine zorn_subset P fun c hcP hchain => ?_
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · rw [Set.sUnion_eq_iUnion]
      refine orthonormal_iUnion_of_directed hchain.directedOn.directed_val fun s => (hcP s.2).1
    · rintro v ⟨s, hs, hv⟩
      exact (hcP hs).2 v hv
  obtain ⟨⟨hon, heig⟩, hmax⟩ := hw
  set M : Submodule ℂ H := (Submodule.span ℂ w).topologicalClosure with hM
  have hspan : ∀ x ∈ Submodule.span ℂ w, A x ∈ Submodule.span ℂ w := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, -, hr⟩ := heig x hx
      rw [hr, RCLike.real_smul_eq_coe_smul (K := ℂ)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hx)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [map_smul]
      exact Submodule.smul_mem _ _ hx
  have hMinv : ∀ x ∈ M, A x ∈ M := by
    intro x hx
    have hsub : Set.MapsTo A (Submodule.span ℂ w : Set H) (Submodule.span ℂ w : Set H) := hspan
    exact map_mem_closure A.continuous hx hsub
  have hMcl : IsClosed (M : Set H) := Submodule.isClosed_topologicalClosure _
  haveI : CompleteSpace M := hMcl.completeSpace_coe
  by_cases htop : M = ⊤
  · have hsp : ⊤ ≤ (Submodule.span ℂ (Set.range ((↑) : w → H))).topologicalClosure := by
      rw [Subtype.range_coe, ← hM, htop]
    let b := HilbertBasis.mk hon hsp
    have hb (k : w) : b k = (k : H) := congrFun (HilbertBasis.coe_mk hon hsp) k
    choose lam hlam0 hlam using fun k : w => heig k k.2
    exact ⟨w, b, lam, hlam0, fun k => by rw [hb, hlam]⟩
  exfalso
  set N : Submodule ℂ H := Mᗮ with hN
  have hNne : N ≠ ⊥ := fun h => htop ((Submodule.orthogonal_eq_bot_iff).mp h)
  have hNcl : IsClosed (N : Set H) := Submodule.isClosed_orthogonal _
  haveI : CompleteSpace N := hNcl.completeSpace_coe
  have hNinv : ∀ f ∈ N, A f ∈ N := by
    intro f hf
    refine (Submodule.mem_orthogonal _ _).mpr fun y hy => ?_
    rw [← hsym]
    exact (Submodule.mem_orthogonal _ _).mp hf _ (hMinv y hy)
  -- a unit eigenvector in the complement
  obtain ⟨v, hvN, hv1, r, hr0, hAv⟩ : ∃ v ∈ N, ‖v‖ = 1 ∧ ∃ r : ℝ, 0 ≤ r ∧ A v = r • v := by
    let R : N →L[ℂ] N := (A.comp N.subtypeL).codRestrict N fun x => hNinv x x.2
    have hRc : IsCompactOperator R :=
      (hc.comp_clm N.subtypeL).codRestrict (fun x => hNinv x x.2) hNcl
    have hRpos : R.IsPositive := by
      refine ⟨fun x y => ?_, fun x => ?_⟩
      · change inner ℂ (A (x : H)) (y : H) = inner ℂ (x : H) (A (y : H))
        exact hpos.isSymmetric _ _
      · exact hpos.2 (x : H)
    by_cases hR0 : R = 0
    · obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hNne
      have hAz : A z = 0 := by
        have := congrArg (fun S : N →L[ℂ] N => ((S ⟨z, hz⟩ : N) : H)) hR0
        simpa [R] using this
      have hzn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
      refine ⟨((‖z‖ : ℂ)⁻¹) • z, Submodule.smul_mem _ _ hz, ?_, 0, le_rfl, ?_⟩
      · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hzn]
      · rw [map_smul, hAz]
        simp
    · obtain ⟨hRp, u, hu, hRu⟩ := PositiveKernelGroundState.positive_compact_top_eigenvector R hRpos hRc hR0
      exact ⟨(u : H), u.2, hu, ‖R‖, hRp.le, congrArg Subtype.val hRu⟩
  have hvw : (v : H) ∉ w := by
    intro hvw
    have hvM : v ∈ M := Submodule.le_topologicalClosure _ (Submodule.subset_span hvw)
    have h0 : inner ℂ v v = (0 : ℂ) := (Submodule.mem_orthogonal _ _).mp hvN v hvM
    rw [inner_self_eq_zero] at h0
    rw [h0, norm_zero] at hv1
    exact zero_ne_one hv1
  have hins : insert v w ∈ P := by
    refine ⟨?_, ?_⟩
    · rw [orthonormal_subtype_iff_ite]
      have hon' := orthonormal_subtype_iff_ite.mp hon
      have hperp (y : H) (hy : y ∈ w) : inner ℂ y v = (0 : ℂ) :=
        (Submodule.mem_orthogonal _ _).mp hvN y
          (Submodule.le_topologicalClosure _ (Submodule.subset_span hy))
      have hne (y : H) (hy : y ∈ w) : y ≠ v := fun h => hvw (h ▸ hy)
      intro a ha c hc
      rcases Set.mem_insert_iff.mp ha with rfl | ha'
      · rcases Set.mem_insert_iff.mp hc with rfl | hc'
        · simp [inner_self_eq_norm_sq_to_K, hv1]
        · rw [if_neg (hne c hc').symm, ← inner_conj_symm, hperp c hc', map_zero]
      · rcases Set.mem_insert_iff.mp hc with rfl | hc'
        · rw [if_neg (hne a ha'), hperp a ha']
        · exact hon' a ha' c hc'
    · rintro y hy
      rcases Set.mem_insert_iff.mp hy with rfl | hy'
      · exact ⟨r, hr0, hAv⟩
      · exact heig y hy'
  exact hvw (hmax hins (Set.subset_insert _ _) (Set.mem_insert _ _))

end Spectrum

section SpectrumZ
variable (n : ℕ) [NeZero n] (β : ℝ)

/-- **The partition function is the sum of the `T`-th powers of the eigenvalues**, for every time
extent `T ≥ 2`. The eigenbasis does not depend on `T`, so all time extents are read off one spectrum.
At `β ≥ 0`. -/
theorem chainZ_spectrum (hβ : 0 ≤ β) :
    ∃ (w : Set (Hilbert n)) (_ : Countable w) (b : HilbertBasis w ℂ (Hilbert n)) (lam : w → ℝ),
      (∀ k, 0 ≤ lam k) ∧ (∀ k, TwistedTransfer.transfer n β (b k) = lam k • b k) ∧
      ∀ m : ℕ, HasSum (fun k => lam k ^ (m + 2)) (chainZ (m + 2) n β) := by
  obtain ⟨w, b, lam, h0, heig⟩ := exists_eigenbasis (TwistedTransfer.transfer n β)
    (transfer_positive n β hβ) (TwistedTransfer.transfer_compact n β)
  haveI hcount : Countable w := countable_of_basis (WilsonSlabOperator.measure n) b
  refine ⟨w, hcount, b, lam, h0, heig, fun m => ?_⟩
  have htr := chainZ_trace n b β m
  have hval (k : w) : inner ℂ (b k) (((TwistedTransfer.transfer n β) ^ (m + 2)) (b k)) =
      ((lam k ^ (m + 2) : ℝ) : ℂ) := by
    have hp (j : ℕ) : ((TwistedTransfer.transfer n β) ^ j) (b k) = ((lam k ^ j : ℝ) : ℂ) • b k := by
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_smul, heig,
          RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
        congr 1
        push_cast
        exact (pow_succ _ _).symm
    rw [hp, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.1 k]
    simp
  simp only [hval] at htr
  exact Complex.hasSum_ofReal.mp htr

end SpectrumZ

/-! ### The law with a temporal twist is the trace with a flip -/

section TemporalTwist
variable (n : ℕ) [NeZero n] (β : ℝ)

local notation "μ'" => WilsonSlabOperator.measure n
local notation "Kt" => twistedKernel n β

/-- The flip as a continuous map. -/
def flipC (i : Fin 3) (c : ZMod n) : C(Slice n, Slice n) :=
  ⟨TwistedTransfer.flip n i c, TwistedVacuum.flip_continuous n i c⟩

/-- **The odd-sector content of the trace.** The trace of `flip · T^(m+2)` is the kernel of
`T^(m+2)` between `x` and its flip. -/
theorem trace_flip {ι : Type*} [Countable ι] (b : HilbertBasis ι ℂ (Hilbert n)) (i : Fin 3)
    (c : ZMod n) (m : ℕ) :
    HasSum (fun k => inner ℂ (b k) (flipOp n i c (((TwistedTransfer.transfer n β) ^ (m + 2)) (b k))))
      ((∫ x, powK (μ') Kt (m + 1) (x, TwistedTransfer.flip n i c x) ∂μ' : ℝ) : ℂ) :=
  trace_involution (μ') b Kt (twistedKernel_symm n β) (flipC n i c) (flip_measurePreserving n i c)
    (flip_flip n i c) (fun x y => twistedKernel_flip n β i c x y) m

/-- A flip of the later slice changes the sign of the temporal holonomies crossing the slab. -/
theorem temporalHolonomy_flip_right (i : Fin 3) (c : ZMod n) (u v : Slice n) (h : SliceGauge n Q)
    (x : SpatialVertex n) (j : Fin 3) :
    temporalHolonomy u (TwistedTransfer.flip n i c v) h x j =
      (if j = i ∧ x i = c then ω else 1) * temporalHolonomy u v h x j := by
  unfold temporalHolonomy TwistedTransfer.flip
  by_cases hc : j = i ∧ x i = c
  · simp only [if_pos hc]
    apply Subtype.ext
    simp only [coe_mul]
    simp [mul_assoc]
  · simp only [if_neg hc, one_mul]

/-- A flip of the later slice is a sign `-1` on one stack of temporal plaquettes in the given slab, in
planes containing time. This is the slab-by-slab identity only: no flux is computed, and it is not
connected here to `TwistedReflection.action` with coefficients `z`. -/
theorem temporalAction_flip_right (i : Fin 3) (c : ZMod n) (u v : Slice n) (h : SliceGauge n Q) :
    temporalAction character 2 u (TwistedTransfer.flip n i c v) h =
      ∑ x : SpatialVertex n, ∑ j : Fin 3,
        (2 - (if j = i ∧ x i = c then (-1 : ℝ) else 1) * (character (temporalHolonomy u v h x j)).re) := by
  unfold temporalAction
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => ?_
  rw [temporalHolonomy_flip_right]
  by_cases hc : j = i ∧ x i = c
  · simp only [if_pos hc, neg_mul, one_mul, sub_neg_eq_add, WilsonSingleLinkStaples.character_re, coe_ω_mul]
    simp
  · simp only [if_neg hc, one_mul]

/-- The action with the later slice of the slab before the time origin flipped. By
`temporalAction_flip_right` this is a sign on one stack of temporal plaquettes of that slab. -/
def twistAction (T : ℕ) [NeZero T] (i : Fin 3) (c : ZMod n) (x : Chain T n) : ℝ :=
  β * ∑ t, (twistedPotential n (x.1 t) + temporalAction character 2 (x.1 t)
    (if t = -1 then TwistedTransfer.flip n i c (x.1 (t + 1)) else x.1 (t + 1)) (x.2 t))

theorem twistAction_continuous (T : ℕ) [NeZero T] (i : Fin 3) (c : ZMod n) :
    Continuous (twistAction n β T i c) := by
  unfold twistAction
  refine continuous_const.mul (continuous_finset_sum _ fun t _ => ?_)
  refine Continuous.add ((twistedPotential_continuous n).comp (by fun_prop)) ?_
  refine (temporalAction_continuous n).comp (f := fun x : Chain T n => (x.1 t,
    (if t = -1 then TwistedTransfer.flip n i c (x.1 (t + 1)) else x.1 (t + 1)), x.2 t)) ?_
  refine (by fun_prop : Continuous fun x : Chain T n => x.1 t).prodMk (Continuous.prodMk ?_ (by fun_prop))
  by_cases ht : t = -1
  · simp only [if_pos ht]
    exact (TwistedVacuum.flip_continuous n i c).comp (by fun_prop)
  · simp only [if_neg ht]
    fun_prop

/-- **The integrated weight with a temporal twist is the trace with a flip.** At time extent `m + 2`,
`∫ exp (-twistAction)` is `∫ K^(m+2)(x, flip x)`. Only this integral is treated: no twisted measure is
constructed. -/
theorem twist_partition (m : ℕ) (i : Fin 3) (c : ZMod n) :
    ∫ x, Real.exp (-twistAction n β (m + 2) i c x) ∂chainRef (m + 2) n =
      ∫ x, powK (μ') Kt (m + 1) (x, TwistedTransfer.flip n i c x) ∂μ' := by
  classical
  let v : Chain (m + 2) n → ZMod (m + 2) → Slice n := fun x t =>
    if t = -1 then TwistedTransfer.flip n i c (x.1 (t + 1)) else x.1 (t + 1)
  have hV (x : Chain (m + 2) n) (t : ZMod (m + 2)) :
      twistedPotential n (v x t) = twistedPotential n (x.1 (t + 1)) := by
    by_cases ht : t = -1
    · simp only [v, if_pos ht, twistedPotential_flip]
    · simp only [v, if_neg ht]
  have hexp (x : Chain (m + 2) n) : Real.exp (-twistAction n β (m + 2) i c x) =
      ∏ t, slabW n β (x.1 t) (v x t) (x.2 t) := by
    have hs : (∑ t : ZMod (m + 2), twistedPotential n (x.1 (t + 1))) =
        ∑ t, twistedPotential n (x.1 t) :=
      Equiv.sum_comp (Equiv.addRight (1 : ZMod (m + 2))) (fun t => twistedPotential n (x.1 t))
    unfold slabW twistAction
    simp only [← Real.exp_add, hV]
    rw [← Real.exp_sum]
    congr 1
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hs]
    ring
  let Lg : C(Slice n × Slice n, ℝ) := ⟨fun p => Kt (p.1, TwistedTransfer.flip n i c p.2),
    (twistedKernel n β).continuous.comp
      (continuous_fst.prodMk ((TwistedVacuum.flip_continuous n i c).comp continuous_snd))⟩
  let Ks : ZMod (m + 2) → C(Slice n × Slice n, ℝ) := fun t => if t = -1 then Lg else Kt
  have hcycle := cycle_integral (μ') (m + 1) Ks
  have hcont : Continuous fun x : Chain (m + 2) n => Real.exp (-twistAction n β (m + 2) i c x) :=
    Real.continuous_exp.comp (twistAction_continuous n β (m + 2) i c).neg
  unfold chainRef
  rw [integral_prod _ (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  have hinner (u : ZMod (m + 2) → Slice n) :
      ∫ h, Real.exp (-twistAction n β (m + 2) i c (u, h))
        ∂Measure.pi (fun _ : ZMod (m + 2) => temporalHaar (n := n) (G := Q)) =
      ∏ t, Ks t (u t, u (t + 1)) := by
    simp only [hexp]
    rw [integral_fintype_prod_eq_prod (𝕜 := ℝ)
      (fun t h => slabW n β (u t) (v (u, fun _ => 1) t) h)]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [slabW_integral]
    by_cases ht : t = -1
    · simp only [v, Ks, if_pos ht]
      rfl
    · simp only [v, Ks, if_neg ht]
  simp only [hinner]
  refine hcycle.trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hcast (j : ℕ) (hj : j ≤ m) : ((j : ℕ) : ZMod (m + 2)) ≠ -1 := by
    intro h
    have h0 : ((j + 1 : ℕ) : ZMod (m + 2)) = 0 := by
      push_cast
      rw [h]
      ring
    have h1 := congrArg ZMod.val h0
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at h1
    omega
  have hlast : ((m + 1 : ℕ) : ZMod (m + 2)) = -1 := by
    have h : ((m + 2 : ℕ) : ZMod (m + 2)) = 0 := ZMod.natCast_self _
    push_cast at h ⊢
    linear_combination h
  have hchain : chainK (μ') (fun j => Ks (j : ZMod (m + 2))) m = powK (μ') Kt m :=
    chainK_congr (μ') _ _ m fun j hj => by simp only [Ks, if_neg (hcast j hj)]
  change compK (μ') (chainK (μ') (fun j => Ks (j : ZMod (m + 2))) m) (Ks ((m + 1 : ℕ) : ZMod (m + 2))) (x, x) = _
  rw [hchain, hlast]
  simp only [Ks, if_true]
  rfl

/-- The even and odd parts of the trace under one flip. The odd-sector trace at time extent `T` is
half the difference of the untwisted and the temporally twisted partition functions. -/
theorem trace_sector {ι : Type*} [Countable ι] (b : HilbertBasis ι ℂ (Hilbert n)) (i : Fin 3)
    (c : ZMod n) (m : ℕ) :
    HasSum (fun k => inner ℂ (b k) (((1 / 2 : ℂ) • (((TwistedTransfer.transfer n β) ^ (m + 2)) (b k) -
        flipOp n i c (((TwistedTransfer.transfer n β) ^ (m + 2)) (b k))))))
      ((((chainZ (m + 2) n β - ∫ x, Real.exp (-twistAction n β (m + 2) i c x) ∂chainRef (m + 2) n) / 2 : ℝ)) : ℂ) := by
  have h1 := chainZ_trace n b β m
  have h2 := trace_flip n β b i c m
  rw [← twist_partition] at h2
  have h3 := (h1.sub h2).mul_left (1 / 2 : ℂ)
  convert h3 using 1
  · funext k
    rw [inner_smul_right, inner_sub_right]
  · push_cast
    ring

end TemporalTwist

section Poincare
variable (n : ℕ) [NeZero n]

/-- The hypotheses of `TwistedPoincare.NeutralObservable` need only the three flips: gauge invariance
supplies the other slabs. -/
theorem neutralObservable_of_three (η g : C(Slice n, ℝ))
    (hgauge : ∀ (h : SliceGauge n Q) u, g (gaugeSlice h u) = g u)
    (hthree : ∀ i u, g (TwistedTransfer.flip n i 0 u) = g u)
    (hmean : ∫ u, g u * η u ^ 2 ∂WilsonSlabOperator.measure n = 0) :
    TwistedPoincare.NeutralObservable n η g where
  gauge := hgauge
  flip i c u := by
    rw [gauge_flip_indep n g hgauge i c 0 u, hthree]
  mean := hmean

/-- Spatial flips commute with the time reflection of the chain. -/
theorem chainReflect_flip (T : ℕ) [NeZero T] (i : Fin 3) (c : ZMod n) (x : Chain T n) :
    chainReflect T n (chainFlip T n i c x) = chainFlip T n i c (chainReflect T n x) := rfl

end Poincare

/-! ### The kernel of the transfer operator -/

section ExpKernel
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι] (φ : ι → C(X, ℝ))

/-- A monomial in the functions `φ`. -/
def mono {k : ℕ} (w : Fin k → ι) : C(X, ℝ) := ∏ j, φ (w j)

omit [Fintype ι] in
theorem mono_apply {k : ℕ} (w : Fin k → ι) (u : X) : mono φ w u = ∏ j, φ (w j) u := by
  simp [mono, ContinuousMap.coe_prod, Finset.prod_apply]

/-- A power of a Gram kernel is a sum of products of monomials. -/
theorem gram_pow (u v : X) (k : ℕ) :
    (∑ i, φ i u * φ i v) ^ k = ∑ w : Fin k → ι, mono φ w u * mono φ w v := by
  classical
  have h := Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset ι))
    (fun _ i => φ i u * φ i v)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.piFinset_univ] at h
  rw [h]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [mono_apply, mono_apply, Finset.prod_mul_distrib]

theorem integrable_conj {F : X → ℂ} (hF : Integrable F μ) : Integrable (fun u => conj (F u)) μ :=
  (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.integrable_comp hF

theorem integrable_cont_mul {F : X → ℂ} (hF : Integrable F μ) (g : C(X, ℝ)) :
    Integrable (fun u => (g u : ℂ) * F u) μ := by
  refine hF.bdd_mul (c := ‖g‖) (Complex.continuous_ofReal.comp g.continuous).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u => by
    rw [Complex.norm_real]
    exact g.norm_coe_le_norm u

/-- The integral of a product of two monomial pieces of a Gram power. -/
theorem integral_conj_mono {F : X → ℂ} (g : C(X, ℝ)) :
    ∫ u, conj (F u) * (g u : ℂ) ∂μ = conj (∫ u, (g u : ℂ) * F u ∂μ) := by
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [map_mul, Complex.conj_ofReal]
  ring

/-- **Strict positivity of an exponential Gram kernel, in moments.** If the quadratic form of
`exp (∑ φᵢ(u) φᵢ(v))` vanishes on `F`, every monomial moment of `F` vanishes. The form is a positive
series of squares of moments. -/
theorem moments_zero {F : X → ℂ} (hF : Integrable F μ)
    (h : ∫ p : X × X, conj (F p.1) * F p.2 * (Real.exp (∑ i, φ i p.1 * φ i p.2) : ℂ) ∂μ.prod μ = 0)
    (k : ℕ) (w : Fin k → ι) : ∫ u, (mono φ w u : ℂ) * F u ∂μ = 0 := by
  classical
  let B : C(X × X, ℝ) :=
    ∑ i, ((φ i).comp ⟨Prod.fst, continuous_fst⟩) * ((φ i).comp ⟨Prod.snd, continuous_snd⟩)
  have hB (p : X × X) : B p = ∑ i, φ i p.1 * φ i p.2 := by
    simp [B, ContinuousMap.coe_sum, Finset.sum_apply]
  have hconj : Integrable (fun u => conj (F u)) μ := integrable_conj hF
  have hFF : Integrable (fun p : X × X => conj (F p.1) * F p.2) (μ.prod μ) := hconj.mul_prod hF
  -- the terms of the series
  let t : ℕ → X × X → ℂ := fun j p => (((B p) ^ j / (j.factorial : ℝ) : ℝ) : ℂ) * (conj (F p.1) * F p.2)
  have hbound (j : ℕ) (p : X × X) : ‖(((B p) ^ j / (j.factorial : ℝ) : ℝ) : ℂ)‖ ≤ ‖B‖ ^ j / (j.factorial : ℝ) := by
    rw [Complex.norm_real, norm_div, norm_pow, Real.norm_natCast]
    gcongr
    exact B.norm_coe_le_norm p
  have hti (j : ℕ) : Integrable (t j) (μ.prod μ) := by
    refine hFF.bdd_mul (c := ‖B‖ ^ j / (j.factorial : ℝ)) ?_ (Filter.Eventually.of_forall (hbound j))
    exact (Continuous.aestronglyMeasurable (by
      have : Continuous fun p : X × X => (B p) ^ j / (j.factorial : ℝ) := by
        have := B.continuous
        fun_prop
      exact Complex.continuous_ofReal.comp this))
  have hnorm (j : ℕ) : ∫ p, ‖t j p‖ ∂μ.prod μ ≤ (‖B‖ ^ j / (j.factorial : ℝ)) * ∫ p, ‖conj (F p.1) * F p.2‖ ∂μ.prod μ := by
    rw [← integral_const_mul]
    refine integral_mono (hti j).norm (hFF.norm.const_mul _) fun p => ?_
    simp only [t]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound j p) (norm_nonneg _)
  have hsum : Summable fun j => ∫ p, ‖t j p‖ ∂μ.prod μ :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg fun p => norm_nonneg _) hnorm
      ((Real.summable_pow_div_factorial ‖B‖).mul_right _)
  have hs := hasSum_integral_of_summable_integral_norm hti hsum
  have htsum (p : X × X) : ∑' j, t j p = conj (F p.1) * F p.2 * (Real.exp (∑ i, φ i p.1 * φ i p.2) : ℂ) := by
    have he := NormedSpace.expSeries_div_hasSum_exp (B p)
    rw [← Real.exp_eq_exp_ℝ, hB] at he
    have hc := (Complex.hasSum_ofReal.mpr he).mul_right (conj (F p.1) * F p.2)
    simp only [t, hB]
    rw [hc.tsum_eq]
    ring
  simp only [htsum, h] at hs
  -- each term is a sum of squares of moments
  let a : ∀ j, (Fin j → ι) → ℂ := fun j w => ∫ u, (mono φ w u : ℂ) * F u ∂μ
  let c : ℕ → ℝ := fun j => (j.factorial : ℝ)⁻¹ * ∑ w : Fin j → ι, ‖a j w‖ ^ 2
  have hcv (j : ℕ) : ∫ p, t j p ∂μ.prod μ = (c j : ℂ) := by
    have ht (p : X × X) : t j p = ∑ w : Fin j → ι, ((j.factorial : ℝ)⁻¹ : ℂ) *
        ((conj (F p.1) * (mono φ w p.1 : ℂ)) * ((mono φ w p.2 : ℂ) * F p.2)) := by
      simp only [t, hB, gram_pow]
      push_cast
      rw [div_eq_inv_mul, mul_assoc, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      ring
    simp only [ht]
    rw [integral_finset_sum]
    · simp only [integral_const_mul]
      have hp (w : Fin j → ι) : ∫ p : X × X, (conj (F p.1) * (mono φ w p.1 : ℂ)) * ((mono φ w p.2 : ℂ) * F p.2) ∂μ.prod μ =
          ((‖a j w‖ ^ 2 : ℝ) : ℂ) := by
        refine (integral_prod_mul (fun u => conj (F u) * (mono φ w u : ℂ)) (fun v => (mono φ w v : ℂ) * F v)).trans ?_
        rw [integral_conj_mono, Complex.conj_mul']
        push_cast
        rfl
      simp only [hp, c]
      push_cast
      rw [Finset.mul_sum]
    · intro w _
      refine Integrable.const_mul ?_ _
      refine Integrable.mul_prod (f := fun u => conj (F u) * (mono φ w u : ℂ))
        (g := fun v => (mono φ w v : ℂ) * F v) ?_ (integrable_cont_mul hF _)
      refine (integrable_conj (integrable_cont_mul hF (mono φ w))).congr (Filter.Eventually.of_forall fun u => ?_)
      simp only [map_mul, Complex.conj_ofReal]
      ring
  simp only [hcv] at hs
  have hs' : HasSum c 0 := by
    have := Complex.hasSum_ofReal.mp (by simpa using hs : HasSum (fun j => (c j : ℂ)) ((0 : ℝ) : ℂ))
    exact this
  have hc0 : c = 0 := (hasSum_zero_iff_of_nonneg fun j => by positivity).mp hs'
  have hk : c k = 0 := congrFun hc0 k
  have hfac : ((k.factorial : ℝ)⁻¹) ≠ 0 := by positivity
  have hzero := (mul_eq_zero.mp hk).resolve_left hfac
  have hw := (Finset.sum_eq_zero_iff_of_nonneg fun w _ => by positivity).mp hzero w (Finset.mem_univ _)
  have : ‖a k w‖ = 0 := by simpa using hw
  exact norm_eq_zero.mp this

/-- A moment functional. -/
theorem integral_add_mul {F : X → ℂ} (hF : Integrable F μ) (g g' : C(X, ℝ)) :
    ∫ u, ((g + g') u : ℂ) * F u ∂μ = (∫ u, (g u : ℂ) * F u ∂μ) + ∫ u, (g' u : ℂ) * F u ∂μ := by
  rw [← integral_add (integrable_cont_mul hF g) (integrable_cont_mul hF g')]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [ContinuousMap.add_apply, Complex.ofReal_add]
  ring

omit [Fintype ι] in
theorem mono_mul {k l : ℕ} (w : Fin k → ι) (w' : Fin l → ι) :
    mono φ w * mono φ w' = mono φ (Fin.append w w') := by
  unfold mono
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

omit [Fintype ι] in
/-- **Vanishing moments force vanishing against all continuous functions**, by Stone-Weierstrass, when
the functions `φ` separate points. -/
theorem integral_zero_of_moments (hsep : ∀ x y : X, x ≠ y → ∃ i, φ i x ≠ φ i y) {F : X → ℂ}
    (hF : Integrable F μ) (h : ∀ (k : ℕ) (w : Fin k → ι), ∫ u, (mono φ w u : ℂ) * F u ∂μ = 0)
    (g : C(X, ℝ)) : ∫ u, (g u : ℂ) * F u ∂μ = 0 := by
  classical
  let A : Subalgebra ℝ C(X, ℝ) := Algebra.adjoin ℝ (Set.range φ)
  have hA : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ := hsep x y hxy
    exact ⟨φ i, ⟨φ i, Algebra.subset_adjoin ⟨i, rfl⟩, rfl⟩, hi⟩
  have htop := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hA
  -- the functional is continuous
  have hcont : Continuous fun g : C(X, ℝ) => ∫ u, (g u : ℂ) * F u ∂μ := by
    let L : C(X, ℝ) →+ ℂ := AddMonoidHom.mk' (fun g => ∫ u, (g u : ℂ) * F u ∂μ) (integral_add_mul hF)
    refine AddMonoidHomClass.continuous_of_bound L (∫ u, ‖F u‖ ∂μ) fun g => ?_
    change ‖∫ u, (g u : ℂ) * F u ∂μ‖ ≤ _
    have hle := norm_integral_le_of_norm_le (f := fun u => (g u : ℂ) * F u) (hF.norm.const_mul ‖g‖)
      (Filter.Eventually.of_forall fun u => by
        rw [norm_mul, Complex.norm_real]
        exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm u) (norm_nonneg _))
    rw [integral_const_mul] at hle
    linarith
  have hclosed : IsClosed {g : C(X, ℝ) | ∫ u, (g u : ℂ) * F u ∂μ = 0} := isClosed_eq hcont continuous_const
  have hmon (m : C(X, ℝ)) (hm : m ∈ Submonoid.closure (Set.range φ)) : ∃ (k : ℕ) (w : Fin k → ι), m = mono φ w := by
    induction hm using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨1, fun _ => i, by simp [mono]⟩
    | one => exact ⟨0, Fin.elim0, by simp [mono]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨k, w, rfl⟩ := hx
      obtain ⟨l, w', rfl⟩ := hy
      exact ⟨k + l, Fin.append w w', mono_mul φ w w'⟩
  have hsub (m : C(X, ℝ)) (hm : m ∈ A) : ∫ u, (m u : ℂ) * F u ∂μ = 0 := by
    have hm' : m ∈ Subalgebra.toSubmodule A := hm
    rw [Algebra.adjoin_eq_span] at hm'
    clear hm
    induction hm' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, w, rfl⟩ := hmon x hx
      exact h k w
    | zero => simp
    | add x y _ _ hx hy => rw [integral_add_mul hF, hx, hy, add_zero]
    | smul a x _ hx =>
      have : ∀ u, ((a • x) u : ℂ) * F u = (a : ℂ) * ((x u : ℂ) * F u) := by
        intro u
        simp only [ContinuousMap.smul_apply, smul_eq_mul, Complex.ofReal_mul]
        ring
      simp only [this]
      rw [integral_const_mul, hx, mul_zero]
  have hg : g ∈ A.topologicalClosure := by rw [htop]; trivial
  have := closure_minimal (s := (A : Set C(X, ℝ))) (fun m hm => hsub m hm) hclosed hg
  exact this

end ExpKernel

section ExpKernelL2
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsProbabilityMeasure μ] [μ.WeaklyRegular]

/-- A vector of `L²` orthogonal, after a positive continuous weight, to all real continuous functions
is zero. -/
theorem eq_zero_of_integral_zero (w : C(X, ℝ)) (hw : ∀ u, 0 < w u) (f : Lp ℂ 2 μ)
    (h : ∀ g : C(X, ℝ), ∫ u, (g u : ℂ) * ((w u : ℂ) * f u) ∂μ = 0) : f = 0 := by
  have hfi : Integrable (fun u => (w u : ℂ) * f u) μ :=
    integrable_cont_mul ((Lp.memLp f).integrable (by norm_num)) w
  have hfi' : Integrable (f : X → ℂ) μ := (Lp.memLp f).integrable (by norm_num)
  have hreal (g : C(X, ℝ)) : ∫ u, (g u : ℂ) * f u ∂μ = 0 := by
    let g' : C(X, ℝ) := ⟨fun u => g u / w u, g.continuous.div w.continuous fun u => (hw u).ne'⟩
    rw [← h g']
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have : (w u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hw u).ne'
    simp only [g', ContinuousMap.coe_mk, Complex.ofReal_div]
    field_simp
  have hcomplex (g : C(X, ℂ)) : inner ℂ (ContinuousMap.toLp 2 μ ℂ g) f = (0 : ℂ) := by
    let a : C(X, ℝ) := ⟨fun u => (g u).re, Complex.continuous_re.comp g.continuous⟩
    let b : C(X, ℝ) := ⟨fun u => (g u).im, Complex.continuous_im.comp g.continuous⟩
    rw [L2.inner_def]
    have hg := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ g
    have hcongr : (fun u => inner ℂ ((ContinuousMap.toLp 2 μ ℂ g : Lp ℂ 2 μ) u) (f u)) =ᵐ[μ]
        fun u => (a u : ℂ) * f u - Complex.I * ((b u : ℂ) * f u) := by
      filter_upwards [hg] with u hu
      rw [hu, RCLike.inner_apply]
      have : conj (g u) = (a u : ℂ) - Complex.I * (b u : ℂ) := by
        apply Complex.ext <;> simp [a, b]
      rw [this]
      ring
    rw [integral_congr_ae hcongr, integral_sub (integrable_cont_mul hfi' a)
      ((integrable_cont_mul hfi' b).const_mul _), integral_const_mul, hreal, hreal]
    simp
  have hall : ∀ y : Lp ℂ 2 μ, inner ℂ y f = (0 : ℂ) := fun y =>
    (ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num : (2 : ENNReal) ≠ ⊤)).induction_on
      (p := fun y => inner ℂ y f = (0 : ℂ)) y
      (isClosed_eq (continuous_id.inner continuous_const) continuous_const) hcomplex
  exact inner_self_eq_zero.mp (hall f)

end ExpKernelL2

/-! ### The transfer operator has no kernel on gauge-invariant vectors -/

section GaugeKernel
variable (n : ℕ) [NeZero n] (β : ℝ)

local notation "μ'" => WilsonSlabOperator.measure n

/-- The four real coordinates of a quaternion. -/
def qc (a : Fin 4) (q : ℍ[ℝ]) : ℝ := ![q.re, q.imI, q.imJ, q.imK] a

theorem qc_continuous (a : Fin 4) : Continuous (qc a) := by
  unfold qc
  fin_cases a
  · exact Quaternion.continuous_re
  · exact Quaternion.continuous_imI
  · exact Quaternion.continuous_imJ
  · exact Quaternion.continuous_imK

/-- A coordinate of one link, scaled by `c`. -/
def linkFeature (c : ℝ) (i : (SpatialVertex n × Fin 3) × Fin 4) : C(Slice n, ℝ) :=
  ⟨fun u => c * qc i.2 ((u i.1 : Q) : ℍ[ℝ]),
    continuous_const.mul ((qc_continuous i.2).comp (continuous_subtype_val.comp (continuous_apply i.1)))⟩

theorem re_inv_mul (a b : Q) :
    (((a⁻¹ * b : Q)) : ℍ[ℝ]).re = ∑ k, qc k (a : ℍ[ℝ]) * qc k (b : ℍ[ℝ]) := by
  change (star (a : ℍ[ℝ]) * (b : ℍ[ℝ])).re = _
  simp [qc, Fin.sum_univ_four, Quaternion.re_mul]

theorem gram_eq (c : ℝ) (u v : Slice n) :
    ∑ i, linkFeature n c i u * linkFeature n c i v =
      c ^ 2 * ∑ e, ((((u e)⁻¹ * v e : Q)) : ℍ[ℝ]).re := by
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [re_inv_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [linkFeature, ContinuousMap.coe_mk]
  ring

/-- The constant in front of the Gram form of the kinetic weight. -/
def kinConst : ℝ := Real.exp (-β * ∑ _e : SpatialVertex n × Fin 3, (2 : ℝ))

/-- **The kinetic weight is the exponential of a Gram kernel**, for `β ≥ 0`: links are unit vectors of
`ℝ⁴`, and `Re (a⁻¹ b)` is their inner product. This is where the sign of `β` enters. -/
theorem kineticWeight_gram (hβ : 0 ≤ β) (u v : Slice n) :
    Real.exp (-β * kineticAction character 2 u v) = kinConst n β *
      Real.exp (∑ i, linkFeature n (Real.sqrt (2 * β)) i u * linkFeature n (Real.sqrt (2 * β)) i v) := by
  rw [gram_eq, Real.sq_sqrt (by positivity), kinConst, ← Real.exp_add]
  congr 1
  unfold kineticAction
  simp only [WilsonSingleLinkStaples.character_re, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem linkFeature_separates (hβ : 0 < β) (u v : Slice n) (huv : u ≠ v) :
    ∃ i, linkFeature n (Real.sqrt (2 * β)) i u ≠ linkFeature n (Real.sqrt (2 * β)) i v := by
  by_contra hne
  push_neg at hne
  apply huv
  have hc : Real.sqrt (2 * β) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  funext e
  have hk (k : Fin 4) : qc k ((u e : Q) : ℍ[ℝ]) = qc k ((v e : Q) : ℍ[ℝ]) :=
    mul_left_cancel₀ hc (hne (e, k))
  apply Subtype.ext
  apply Quaternion.ext
  · exact hk 0
  · exact hk 1
  · exact hk 2
  · exact hk 3

/-- The half-slice weight of the twisted potential. -/
def halfWeight : C(Slice n, ℝ) :=
  ⟨fun u => Real.exp (-(β / 2) * twistedPotential n u),
    Real.continuous_exp.comp (continuous_const.mul (twistedPotential_continuous n))⟩

theorem halfWeight_apply (u : Slice n) :
    halfWeight n β u = Real.exp (-(β / 2) * twistedPotential n u) := rfl

theorem halfWeight_pos (u : Slice n) : 0 < halfWeight n β u := Real.exp_pos _

theorem halfWeight_gauge (h : SliceGauge n Q) (u : Slice n) :
    halfWeight n β (gaugeSlice h u) = halfWeight n β u := by
  simp only [halfWeight_apply, twistedPotential_eq, TwistedTreeGauge.defect_gauge,
    WilsonSlabGauge.potential_gauge _ WilsonSingleLinkStaples.character_classFunction]

/-- The gauge action on `L²`. -/
def gaugeOp (h : SliceGauge n Q) : Hilbert n →ₗᵢ[ℂ] Hilbert n :=
  Lp.compMeasurePreservingₗᵢ ℂ (gaugeSlice h) (WilsonSlabGauge.gauge_preserves_spatial h)

/-- The closed subspace of gauge-invariant vectors. -/
def gaugeSubspace : Submodule ℂ (Hilbert n) where
  carrier := {f | ∀ h, gaugeOp n h f = f}
  add_mem' := by
    intro a b ha hb h
    rw [map_add, ha h, hb h]
  zero_mem' := fun h => map_zero _
  smul_mem' := by
    intro k a ha h
    rw [map_smulₛₗ, ha h]
    rfl

theorem gaugeSubspace_closed : IsClosed (gaugeSubspace n : Set (Hilbert n)) := by
  have : (gaugeSubspace n : Set (Hilbert n)) = ⋂ h, {f | gaugeOp n h f = f} := by
    ext f
    simp [gaugeSubspace]
  rw [this]
  exact isClosed_iInter fun h => isClosed_eq (gaugeOp n h).continuous continuous_id

instance : CompleteSpace (gaugeSubspace n) := (gaugeSubspace_closed n).completeSpace_coe

theorem gauge_ae {f : Hilbert n} (hf : f ∈ gaugeSubspace n) (h : SliceGauge n Q) :
    (fun u => f (gaugeSlice h u)) =ᵐ[μ'] f := by
  have h1 : (gaugeOp n h f : Slice n → ℂ) =ᵐ[μ'] ((f : Hilbert n) ∘ gaugeSlice h) :=
    Lp.coeFn_compMeasurePreserving f (WilsonSlabGauge.gauge_preserves_spatial h)
  rw [hf h] at h1
  exact h1.symm

/-- A continuous gauge-invariant function is a gauge-invariant vector. -/
theorem embed_mem_gauge (g : C(Slice n, ℂ)) (hg : ∀ (h : SliceGauge n Q) u, g (gaugeSlice h u) = g u) :
    ContinuousMap.toLp 2 (μ') ℂ g ∈ gaugeSubspace n := by
  intro h
  have hmp := WilsonSlabGauge.gauge_preserves_spatial (n := n) (G := Q) h
  apply Lp.ext
  have h1 : (gaugeOp n h (ContinuousMap.toLp 2 (μ') ℂ g) : Slice n → ℂ) =ᵐ[μ']
      ((ContinuousMap.toLp 2 (μ') ℂ g : Hilbert n) ∘ gaugeSlice h) :=
    Lp.coeFn_compMeasurePreserving _ hmp
  have h2 := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ') g
  have h3 := hmp.quasiMeasurePreserving.ae_eq_comp h2
  refine h1.trans (h3.trans (Filter.EventuallyEq.trans ?_ h2.symm))
  exact Filter.Eventually.of_forall fun u => hg h u

/-- The image of the transfer operator is gauge invariant. -/
theorem transfer_mem_gauge (f : Hilbert n) : TwistedTransfer.transfer n β f ∈ gaugeSubspace n := by
  rw [transfer_eq_embed]
  exact embed_mem_gauge n _ (representative_gauge n β f)

/-- **Temporal links integrate away on gauge-invariant vectors.** There `T` is the multiplication by
the half-slice weights around the plain kinetic kernel, with no gauge average. -/
theorem smoothing_gauge {f : Hilbert n} (hf : f ∈ gaugeSubspace n) (u : Slice n) :
    smoothing (μ') (twistedKernel n β) f u = (halfWeight n β u : ℂ) *
      ∫ v, (Real.exp (-β * kineticAction character 2 u v) : ℂ) * ((halfWeight n β v : ℂ) * f v) ∂μ' := by
  set F : Slice n → ℂ := fun v => (halfWeight n β v : ℂ) * f v with hFd
  have hFi : Integrable F μ' := integrable_cont_mul ((Lp.memLp f).integrable (by norm_num)) _
  have hkin (v : Slice n) (h : SliceGauge n Q) :
      Real.exp (-β * temporalAction character 2 u v h) =
        Real.exp (-β * kineticAction character 2 u (gaugeSlice h v)) := by
    rw [temporalAction_eq _ WilsonSingleLinkStaples.character_classFunction]
  have hcont : Continuous fun p : Slice n × SliceGauge n Q =>
      Real.exp (-β * kineticAction character 2 u (gaugeSlice p.2 p.1)) := by
    simp only [← hkin]
    refine Real.continuous_exp.comp (continuous_const.mul ?_)
    exact (temporalAction_continuous n).comp (f := fun p : Slice n × SliceGauge n Q => (u, p.1, p.2)) (by fun_prop)
  have hstep (v : Slice n) : (twistedKernel n β (u, v) : ℂ) * f v = (halfWeight n β u : ℂ) *
      ∫ h, (Real.exp (-β * kineticAction character 2 u (gaugeSlice h v)) : ℂ) * F v ∂temporalHaar := by
    rw [integral_mul_const, integral_complex_ofReal, twistedKernel_eq]
    simp only [hkin, hFd, halfWeight_apply]
    push_cast
    ring
  rw [smoothing_integral]
  simp only [hstep]
  rw [integral_const_mul]
  congr 1
  let Gc : C(Slice n × SliceGauge n Q, ℝ) := ⟨_, hcont⟩
  have hint : Integrable (Function.uncurry fun (v : Slice n) (h : SliceGauge n Q) =>
      (Real.exp (-β * kineticAction character 2 u (gaugeSlice h v)) : ℂ) * F v) ((μ').prod temporalHaar) := by
    refine (hFi.comp_fst temporalHaar).bdd_mul (c := ‖Gc‖)
      (Complex.continuous_ofReal.comp hcont).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    change ‖((Gc p : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real]
    exact Gc.norm_coe_le_norm p
  rw [integral_integral_swap hint]
  have hinner (h : SliceGauge n Q) :
      ∫ v, (Real.exp (-β * kineticAction character 2 u (gaugeSlice h v)) : ℂ) * F v ∂μ' =
        ∫ v, (Real.exp (-β * kineticAction character 2 u v) : ℂ) * F v ∂μ' := by
    have hmp := WilsonSlabGauge.gauge_preserves_spatial (n := n) (G := Q) h
    have hequiv : MeasurePreserving (WilsonSlabGauge.gaugeHomeomorph (n := n) (G := Q) h).toMeasurableEquiv μ' μ' := hmp
    rw [← hequiv.integral_comp' (fun v => (Real.exp (-β * kineticAction character 2 u v) : ℂ) * F v)]
    refine integral_congr_ae ?_
    filter_upwards [gauge_ae n hf h] with v hv
    change _ = (Real.exp (-β * kineticAction character 2 u (gaugeSlice h v)) : ℂ) * ((halfWeight n β (gaugeSlice h v) : ℂ) * f (gaugeSlice h v))
    rw [halfWeight_gauge, hv]
  simp only [hinner, integral_const, probReal_univ, one_smul]
  rfl

/-- **The transfer operator is injective on gauge-invariant vectors, for `β > 0`.** The kinetic kernel
is a positive multiple of `exp ⟪Φ u, Φ v⟫` with `Φ` the embedding of the links in `ℝ⁴`, so its quadratic
form is a series of squares of moments with positive coefficients. Moments of all orders separate
continuous functions by Stone-Weierstrass. No bound on the inverse comes out of this. -/
theorem transfer_injective_gauge (hβ : 0 < β) {f : Hilbert n} (hf : f ∈ gaugeSubspace n)
    (h0 : TwistedTransfer.transfer n β f = 0) : f = 0 := by
  haveI hmeas : Measure.IsOpenPosMeasure (μ') := by
    change (Measure.pi fun _ : SpatialVertex n × Fin 3 => RegulatedGauge.compactHaar Q).IsOpenPosMeasure
    haveI : (RegulatedGauge.compactHaar Q).IsOpenPosMeasure := GibbsFullSupport.compactHaar_openPos Q
    infer_instance
  have hrep : TwistedVacuum.representative n β f = 0 := by
    apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) (μ')
    rw [map_zero, ← transfer_eq_embed, h0]
  set F : Slice n → ℂ := fun v => (halfWeight n β v : ℂ) * f v with hFd
  have hFi : Integrable F μ' := integrable_cont_mul ((Lp.memLp f).integrable (by norm_num)) _
  set φ := linkFeature n (Real.sqrt (2 * β)) with hφ
  have hC : (kinConst n β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have hrow (u : Slice n) : ∫ v, (Real.exp (∑ i, φ i u * φ i v) : ℂ) * F v ∂μ' = 0 := by
    have h1 := smoothing_gauge n β hf u
    have h2 : smoothing (μ') (twistedKernel n β) f u = 0 := by
      have := DFunLike.congr_fun hrep u
      exact this
    rw [h2] at h1
    have h3 := (mul_eq_zero.mp h1.symm).resolve_left (Complex.ofReal_ne_zero.mpr (halfWeight_pos n β u).ne')
    simp only [kineticWeight_gram n β hβ.le, Complex.ofReal_mul, mul_assoc] at h3
    rw [integral_const_mul] at h3
    exact (mul_eq_zero.mp h3).resolve_left hC
  have hquad : ∫ p : Slice n × Slice n, conj (F p.1) * F p.2 * (Real.exp (∑ i, φ i p.1 * φ i p.2) : ℂ)
      ∂(μ').prod (μ') = 0 := by
    let E : C(Slice n × Slice n, ℝ) := ⟨fun p => Real.exp (∑ i, φ i p.1 * φ i p.2), by
      refine Real.continuous_exp.comp (continuous_finset_sum _ fun i _ => ?_)
      exact ((φ i).continuous.comp continuous_fst).mul ((φ i).continuous.comp continuous_snd)⟩
    have hi : Integrable (fun p : Slice n × Slice n => conj (F p.1) * F p.2 * (Real.exp (∑ i, φ i p.1 * φ i p.2) : ℂ))
        ((μ').prod (μ')) := by
      have hFF : Integrable (fun p : Slice n × Slice n => conj (F p.1) * F p.2) ((μ').prod (μ')) :=
        (integrable_conj hFi).mul_prod hFi
      refine (hFF.bdd_mul (c := ‖E‖) (Complex.continuous_ofReal.comp E.continuous).aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => ?_)).congr (Filter.Eventually.of_forall fun p => ?_)
      · change ‖((E p : ℝ) : ℂ)‖ ≤ _
        rw [Complex.norm_real]
        exact E.norm_coe_le_norm p
      · exact mul_comm _ _
    rw [integral_prod _ hi]
    have (u : Slice n) : ∫ v, conj (F u) * F v * (Real.exp (∑ i, φ i u * φ i v) : ℂ) ∂μ' = 0 := by
      have : ∀ v, conj (F u) * F v * (Real.exp (∑ i, φ i u * φ i v) : ℂ) =
          conj (F u) * ((Real.exp (∑ i, φ i u * φ i v) : ℂ) * F v) := fun v => by ring
      simp only [this]
      rw [integral_const_mul, hrow, mul_zero]
    simp only [this, integral_zero]
  refine eq_zero_of_integral_zero (halfWeight n β) (halfWeight_pos n β) f fun g => ?_
  exact integral_zero_of_moments φ (linkFeature_separates n β hβ) hFi (moments_zero φ hFi hquad) g

end GaugeKernel

section KernelOfT
variable (n : ℕ) [NeZero n] (β : ℝ)

local notation "μ'" => WilsonSlabOperator.measure n

theorem transfer_symm' (x y : Hilbert n) :
    inner ℂ (TwistedTransfer.transfer n β x) y = inner ℂ x (TwistedTransfer.transfer n β y) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (TwistedTransfer.transfer_selfAdjoint n β) x y

/-- **The exact kernel of `T`.** For `β > 0`, `T v = 0` holds exactly when `v` is orthogonal to the
gauge-invariant vectors. At `β = 0` this fails, since `T` has rank one (`transfer_zero`). -/
theorem transfer_eq_zero_iff (hβ : 0 < β) (v : Hilbert n) :
    TwistedTransfer.transfer n β v = 0 ↔ v ∈ (gaugeSubspace n)ᗮ := by
  have hperp (b : Hilbert n) (hb : b ∈ (gaugeSubspace n)ᗮ) : TwistedTransfer.transfer n β b = 0 := by
    have h0 : inner ℂ (TwistedTransfer.transfer n β b) (TwistedTransfer.transfer n β b) = (0 : ℂ) := by
      rw [transfer_symm']
      exact (Submodule.mem_orthogonal' _ _).mp hb _ (transfer_mem_gauge n β _)
    exact inner_self_eq_zero.mp h0
  refine ⟨fun hv => ?_, hperp v⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.exists_add_mem_mem_orthogonal (K := gaugeSubspace n) v
  rw [map_add, hperp b hb, add_zero] at hv
  rw [transfer_injective_gauge n β hβ ha hv, zero_add]
  exact hb

/-- **`T` is strictly positive on gauge-invariant vectors, for `β > 0`.** There are no null vectors on
that subspace. No lower bound on the form comes out of this. -/
theorem form_pos_gauge (hβ : 0 < β) {f : Hilbert n} (hf : f ∈ gaugeSubspace n) (hf0 : f ≠ 0) :
    0 < (inner ℂ f (TwistedTransfer.transfer n β f)).re := by
  have hpos := transfer_positive n β hβ.le
  have hnn (g : Hilbert n) : 0 ≤ (inner ℂ g (TwistedTransfer.transfer n β g)).re := by
    have := hpos.2 g
    rw [ContinuousLinearMap.reApplyInnerSelf_apply] at this
    rw [← inner_conj_symm, Complex.conj_re]
    exact this
  refine lt_of_le_of_ne (hnn f) fun h0 => hf0 (transfer_injective_gauge n β hβ hf ?_)
  set y := TwistedTransfer.transfer n β f with hy
  -- expand the form along `f - t y`
  have hexp (t : ℝ) : (inner ℂ (f - (t : ℂ) • y) (TwistedTransfer.transfer n β (f - (t : ℂ) • y))).re =
      (inner ℂ f y).re - 2 * t * ‖y‖ ^ 2 + t ^ 2 * (inner ℂ y (TwistedTransfer.transfer n β y)).re := by
    have hyy : inner ℂ y y = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      simp
    have hfTy : inner ℂ f (TwistedTransfer.transfer n β y) = inner ℂ y y := by
      rw [← transfer_symm']
    rw [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_sub_right, inner_smul_left,
      inner_smul_left, inner_smul_right, inner_smul_right, hfTy, hyy, ← hy]
    simp only [Complex.conj_ofReal, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.mul_im, add_zero]
    ring
  set a := ‖y‖ ^ 2 with ha
  set b := (inner ℂ y (TwistedTransfer.transfer n β y)).re with hb
  have hb0 : 0 ≤ b := hnn y
  have ha0 : 0 ≤ a := by positivity
  have hkey := hnn (f - (((a / (b + 1) : ℝ)) : ℂ) • y)
  rw [hexp, ← h0] at hkey
  have hb1 : 0 < b + 1 := by linarith
  have hval : 0 - 2 * (a / (b + 1)) * a + (a / (b + 1)) ^ 2 * b = -(a ^ 2 * (b + 2)) / (b + 1) ^ 2 := by
    field_simp
    ring
  have ha2 : a ^ 2 * (b + 2) ≤ 0 := by
    have h1 : 0 ≤ -(a ^ 2 * (b + 2)) / (b + 1) ^ 2 := by
      rw [← hval]
      exact hkey
    have h2 := (div_nonneg_iff.mp h1)
    rcases h2 with ⟨h3, -⟩ | ⟨-, h3⟩
    · linarith
    · have : 0 < (b + 1) ^ 2 := by positivity
      linarith
  have hazero : a = 0 := by
    have hb2 : 0 < b + 2 := by linarith
    have : a ^ 2 ≤ 0 := by nlinarith [sq_nonneg a]
    exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm this (sq_nonneg a))
  exact norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp hazero)

/-- At `β = 0` the kernel is `1`, and `T` is the rank-one projection on the constants. -/
theorem transfer_zero (f : Hilbert n) :
    TwistedTransfer.transfer n 0 f =
      inner ℂ (ContinuousMap.toLp 2 (μ') ℂ (1 : C(Slice n, ℂ))) f •
        ContinuousMap.toLp 2 (μ') ℂ (1 : C(Slice n, ℂ)) := by
  have hK (u v : Slice n) : twistedKernel n 0 (u, v) = 1 := by
    rw [twistedKernel_eq]
    simp [integral_const, probReal_univ]
  have hrow (u : Slice n) : row (μ') (twistedKernel n 0) u = ContinuousMap.toLp 2 (μ') ℂ (1 : C(Slice n, ℂ)) := by
    unfold row
    congr 1
    ext v
    simp [rowContinuous, hK]
  rw [transfer_eq_embed, ← map_smul]
  congr 1
  ext u
  change inner ℂ (row (μ') (twistedKernel n 0) u) f = _
  rw [hrow]
  simp

/-- **The top of a positive compact operator on an invariant closed subspace.** -/
theorem top_on_invariant {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (hpos : A.IsPositive) (hc : IsCompactOperator A) (W : Submodule ℂ H)
    [CompleteSpace W] (hW : ∀ x ∈ W, A x ∈ W) (x : H) (hx : x ∈ W) (hAx : A x ≠ 0) :
    ∃ v ∈ W, ‖v‖ = 1 ∧ ∃ lam : ℝ, 0 < lam ∧ A v = lam • v ∧ ∀ f ∈ W, ‖A f‖ ≤ lam * ‖f‖ := by
  let P : H →L[ℂ] H := W.starProjection
  have hPadj : ContinuousLinearMap.adjoint P = P := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (Submodule.starProjection_isSymmetric W)).adjoint_eq
  have hPfix (f : H) (hf : f ∈ W) : P f = f := Submodule.starProjection_eq_self_iff.mpr hf
  let S : H →L[ℂ] H := P ∘L A ∘L P
  have hS (f : H) (hf : f ∈ W) : S f = A f := by
    change P (A (P f)) = A f
    rw [hPfix f hf, hPfix _ (hW f hf)]
  have hSpos : S.IsPositive := by
    have := hpos.conj_adjoint P
    rwa [hPadj] at this
  have hSc : IsCompactOperator S := (hc.comp_clm P).clm_comp P
  have hS0 : S ≠ 0 := by
    intro h0
    apply hAx
    rw [← hS x hx, h0]
    rfl
  obtain ⟨hnorm, v, hv, hSv⟩ := PositiveKernelGroundState.positive_compact_top_eigenvector S hSpos hSc hS0
  have hvW : v ∈ W := by
    have h1 : S v ∈ W := Submodule.starProjection_apply_mem W _
    have h2 : v = ((‖S‖ : ℂ)⁻¹) • S v := by
      rw [hSv, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
      change v = (((‖S‖ : ℂ)⁻¹) * (‖S‖ : ℂ)) • v
      rw [inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hnorm.ne'), one_smul]
    rw [h2]
    exact W.smul_mem _ h1
  refine ⟨v, hvW, hv, ‖S‖, hnorm, by rw [← hS v hvW, hSv], fun f hf => ?_⟩
  rw [← hS f hf]
  exact S.le_opNorm f

/-! ### Every sector has a positive top level -/

/-- The closed subspace of a character of `Z2³`. -/
def sectorSubspace (e : Fin 3 → Bool) : Submodule ℂ (Hilbert n) where
  carrier := {f | Sector n e f}
  add_mem' := by
    intro a b ha hb i c
    rw [map_add, ha i c, hb i c, smul_add]
  zero_mem' := fun i c => by rw [map_zero, smul_zero]
  smul_mem' := by
    intro k a ha i c
    rw [map_smulₛₗ, ha i c, smul_comm]
    rfl

theorem sectorSubspace_closed (e : Fin 3 → Bool) : IsClosed (sectorSubspace n e : Set (Hilbert n)) := by
  have : (sectorSubspace n e : Set (Hilbert n)) =
      ⋂ i, ⋂ c, {f | TwistedTransfer.flipOp n i c f = sgn (e i) • f} := by
    ext f
    simp [sectorSubspace, Sector]
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun c =>
    isClosed_eq (TwistedTransfer.flipOp n i c).continuous (continuous_const.smul continuous_id)

/-- **`T` is nonzero on each of the eight sectors, for `β > 0`.** The top of `T` on the sector is a
positive eigenvalue with an eigenvector in the sector, and it lies strictly below `‖T‖` away from the
neutral sector. Its size is not controlled. -/
theorem sector_top (hβ : 0 < β) (e : Fin 3 → Bool) :
    ∃ v, Sector n e v ∧ ‖v‖ = 1 ∧ ∃ lam : ℝ, 0 < lam ∧ lam ≤ ‖TwistedTransfer.transfer n β‖ ∧
      TwistedTransfer.transfer n β v = lam • v ∧
      (∀ f, Sector n e f → ‖TwistedTransfer.transfer n β f‖ ≤ lam * ‖f‖) ∧
      (e ≠ (fun _ => false) → lam < ‖TwistedTransfer.transfer n β‖) := by
  obtain ⟨g, hgg, hg0, hgs⟩ := exists_sector_vector n e
  have hmem : ContinuousMap.toLp 2 (μ') ℂ (complexify g) ∈ gaugeSubspace n :=
    embed_mem_gauge n _ fun h u => by
      change ((g (gaugeSlice h u) : ℝ) : ℂ) = ((g u : ℝ) : ℂ)
      rw [hgg]
  haveI : CompleteSpace (sectorSubspace n e) := (sectorSubspace_closed n e).completeSpace_coe
  obtain ⟨v, hv, hn, lam, hlam, hTv, hle⟩ := top_on_invariant (TwistedTransfer.transfer n β)
    (transfer_positive n β hβ.le) (TwistedTransfer.transfer_compact n β) (sectorSubspace n e)
    (fun x hx => transfer_sector n β e hx) _ hgs
    (fun h0 => hg0 (transfer_injective_gauge n β hβ hmem h0))
  have hlamle : lam ≤ ‖TwistedTransfer.transfer n β‖ := by
    have h1 := (TwistedTransfer.transfer n β).le_opNorm v
    rw [hTv, norm_smul, hn, mul_one, mul_one, Real.norm_eq_abs, abs_of_pos hlam] at h1
    exact h1
  refine ⟨v, hv, hn, lam, hlam, hlamle, hTv, hle, fun hne => lt_of_le_of_ne hlamle fun heq => ?_⟩
  obtain ⟨Ω, h1, -, h3, h4⟩ := TwistedVacuum.neutral_vacuum n β hβ.le
  rw [heq] at hTv
  obtain ⟨c, hc⟩ := h4 v hTv
  have horth : inner ℂ Ω v = (0 : ℂ) :=
    sector_orthogonal n (fun _ => false) e hne.symm ((sector_false_iff n Ω).mpr h3) hv
  have hself : inner ℂ Ω Ω = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, h1]
    simp
  rw [hc, inner_smul_right, hself, mul_one] at horth
  rw [hc, horth, zero_smul, norm_zero] at hn
  exact zero_ne_one hn

/-! ### The first excited neutral level -/

/-- A slice with a prescribed link `q` on the slab `x i = 0` of direction `i`, and `1` elsewhere. -/
def slabSlice (i : Fin 3) (q : Q) : Slice n := fun e => if e.2 = i ∧ e.1 i = 0 then q else 1

theorem run_slabSlice (i : Fin 3) (q : Q) (m : ℕ) (hm : m ≤ n) :
    run (lift n (slabSlice n i q)) i.succ (TwistedSliceLift.base n) m = if 0 < m then q else 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm' : m < n := hm
    have hc : (sp n (walk i.succ (TwistedSliceLift.base n) m)) i = (m : ZMod n) := by
      change walk i.succ (TwistedSliceLift.base n) m i.succ = _
      rw [walk_apply_same]
      simp
    have hiff : ((m : ZMod n) = 0) ↔ m = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact ⟨fun h => Nat.eq_zero_of_dvd_of_lt h hm', fun h => by simp [h]⟩
    simp only [run, ih (Nat.le_of_lt hm'), lift_succ]
    unfold slabSlice
    simp only [true_and, hc, hiff]
    by_cases h : m = 0
    · subst h
      simp
    · have : 0 < m := Nat.pos_of_ne_zero h
      simp [h, this]

/-- A unit quaternion with vanishing real part. -/
def unitI : Q := ⟨⟨0, 1, 0, 0⟩, by
  rw [Unitary.mem_iff]
  constructor <;> ext <;> simp⟩

theorem windRe_slabSlice (i : Fin 3) (q : Q) : windRe n i (slabSlice n i q) = ((q : Q) : ℍ[ℝ]).re := by
  unfold windRe wind
  rw [run_slabSlice n i q n le_rfl, if_pos (Nat.pos_of_ne_zero (NeZero.ne n))]

/-- The square of the trace of a Polyakov line: neutral, gauge invariant and not constant. -/
def polySq : C(Slice n, ℝ) :=
  ⟨fun u => windRe n 0 u ^ 2, (windRe_continuous n 0).pow 2⟩

theorem polySq_flip (i : Fin 3) (c : ZMod n) (u : Slice n) :
    polySq n (TwistedTransfer.flip n i c u) = polySq n u := by
  change windRe n 0 _ ^ 2 = windRe n 0 u ^ 2
  by_cases h : (0 : Fin 3) = i
  · subst h
    rw [windRe_flip_same]
    ring
  · rw [windRe_flip_other n 0 i h]

theorem polySq_gauge (h : SliceGauge n Q) (u : Slice n) : polySq n (gaugeSlice h u) = polySq n u := by
  change windRe n 0 _ ^ 2 = windRe n 0 u ^ 2
  rw [windRe_gauge]

/-- A continuous flip-invariant function is a neutral vector. -/
theorem embed_neutral (g : C(Slice n, ℝ)) (hg : ∀ i c u, g (TwistedTransfer.flip n i c u) = g u) :
    Neutral n (ContinuousMap.toLp 2 (μ') ℂ (complexify g)) := by
  intro i c
  rw [flipOp_embed]
  congr 1
  ext u
  change ((g (TwistedTransfer.flip n i c u) : ℝ) : ℂ) = ((g u : ℝ) : ℂ)
  rw [hg]

/-- Given a unit vector `Ω`, there is a nonzero neutral gauge-invariant vector orthogonal to it. -/
theorem exists_neutral_orth (Ω : Hilbert n) (hn : ‖Ω‖ = 1) (hN : Neutral n Ω) (hG : Ω ∈ gaugeSubspace n) :
    ∃ x, x ∈ neutralSubspace n ∧ x ∈ gaugeSubspace n ∧ inner ℂ Ω x = (0 : ℂ) ∧ x ≠ 0 := by
  haveI hmeas : Measure.IsOpenPosMeasure (μ') := by
    change (Measure.pi fun _ : SpatialVertex n × Fin 3 => RegulatedGauge.compactHaar Q).IsOpenPosMeasure
    haveI : (RegulatedGauge.compactHaar Q).IsOpenPosMeasure := GibbsFullSupport.compactHaar_openPos Q
    infer_instance
  have hself : inner ℂ Ω Ω = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hn]
    simp
  have hgen (a : Hilbert n) (haN : Neutral n a) (haG : a ∈ gaugeSubspace n)
      (hne : a - inner ℂ Ω a • Ω ≠ 0) :
      ∃ x, x ∈ neutralSubspace n ∧ x ∈ gaugeSubspace n ∧ inner ℂ Ω x = (0 : ℂ) ∧ x ≠ 0 :=
    ⟨a - inner ℂ Ω a • Ω, (neutralSubspace n).sub_mem haN ((neutralSubspace n).smul_mem _ hN),
      (gaugeSubspace n).sub_mem haG ((gaugeSubspace n).smul_mem _ hG),
      by rw [inner_sub_right, inner_smul_right, hself, mul_one, sub_self], hne⟩
  let g0 : C(Slice n, ℝ) := 1
  let a0 := ContinuousMap.toLp 2 (μ') ℂ (complexify g0)
  let a1 := ContinuousMap.toLp 2 (μ') ℂ (complexify (polySq n))
  have ha0N : Neutral n a0 := embed_neutral n g0 fun _ _ _ => rfl
  have ha1N : Neutral n a1 := embed_neutral n _ (polySq_flip n)
  have ha0G : a0 ∈ gaugeSubspace n := embed_mem_gauge n _ fun _ _ => rfl
  have ha1G : a1 ∈ gaugeSubspace n := embed_mem_gauge n _ fun h u => by
    change ((polySq n (gaugeSlice h u) : ℝ) : ℂ) = ((polySq n u : ℝ) : ℂ)
    rw [polySq_gauge]
  by_cases h0 : a0 - inner ℂ Ω a0 • Ω = 0
  · by_cases h1 : a1 - inner ℂ Ω a1 • Ω = 0
    · exfalso
      set c0 : ℂ := inner ℂ Ω a0
      set c1 : ℂ := inner ℂ Ω a1
      have e0 : a0 = c0 • Ω := sub_eq_zero.mp h0
      have e1 : a1 = c1 • Ω := sub_eq_zero.mp h1
      have hprop : c0 • a1 = c1 • a0 := by rw [e0, e1, smul_smul, smul_smul, mul_comm]
      have hfun : c0 • complexify (polySq n) = c1 • complexify g0 := by
        apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) (μ')
        rw [map_smul, map_smul]
        exact hprop
      have hval (u : Slice n) : c0 * ((polySq n u : ℝ) : ℂ) = c1 := by
        have := DFunLike.congr_fun hfun u
        change c0 * ((polySq n u : ℝ) : ℂ) = c1 * ((1 : ℝ) : ℂ) at this
        simpa using this
      have hu1 : polySq n (fun _ => 1) = 1 := by
        change windRe n 0 _ ^ 2 = 1
        rw [windRe_one]
        norm_num
      have hu2 : polySq n (slabSlice n 0 unitI) = 0 := by
        change windRe n 0 _ ^ 2 = 0
        rw [windRe_slabSlice]
        simp [unitI]
      have h3 := hval (fun _ => 1)
      have h4 := hval (slabSlice n 0 unitI)
      rw [hu1] at h3
      rw [hu2] at h4
      simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero] at h3 h4
      have hc0 : c0 = 0 := h3.trans h4.symm
      have ha00 : a0 = 0 := by rw [e0, hc0, zero_smul]
      have hzero : complexify g0 = 0 := by
        apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) (μ')
        rw [map_zero]
        exact ha00
      have := DFunLike.congr_fun hzero (fun _ => 1)
      change ((1 : ℝ) : ℂ) = 0 at this
      simp at this
    · exact hgen a1 ha1N ha1G h1
  · exact hgen a0 ha0N ha0G h0

/-- **The first excited neutral level exists at every cutoff, for `β > 0`.** It is an eigenvalue
`ρ ‖T‖` with `0 < ρ < 1`, with a neutral eigenvector orthogonal to the vacuum, and `ρ ‖T‖` is the exact
norm of `T` on the neutral complement of the vacuum. `ρ` is not controlled in `n` or `β`. -/
theorem neutral_level (hβ : 0 < β) :
    ∃ (Ω v : Hilbert n) (ρ : ℝ), ‖Ω‖ = 1 ∧ TwistedTransfer.transfer n β Ω = ‖TwistedTransfer.transfer n β‖ • Ω ∧
      Neutral n Ω ∧ (∀ w, TwistedTransfer.transfer n β w = ‖TwistedTransfer.transfer n β‖ • w → ∃ c : ℂ, w = c • Ω) ∧
      0 < ρ ∧ ρ < 1 ∧ ‖v‖ = 1 ∧ Neutral n v ∧ inner ℂ Ω v = (0 : ℂ) ∧
      TwistedTransfer.transfer n β v = (ρ * ‖TwistedTransfer.transfer n β‖) • v ∧
      ∀ f, Neutral n f → inner ℂ Ω f = (0 : ℂ) →
        ‖TwistedTransfer.transfer n β f‖ ≤ ρ * ‖TwistedTransfer.transfer n β‖ * ‖f‖ := by
  obtain ⟨Ω, hn, htop, hN, hsimple⟩ := TwistedVacuum.neutral_vacuum n β hβ.le
  have hlam := norm_transfer_pos n β
  set L := ‖TwistedTransfer.transfer n β‖ with hL
  have hG : Ω ∈ gaugeSubspace n := by
    have hΩT : Ω = TwistedTransfer.transfer n β (((L : ℂ)⁻¹) • Ω) := by
      rw [map_smul, htop, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
      change Ω = (((L : ℂ)⁻¹) * (L : ℂ)) • Ω
      rw [inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hlam.ne'), one_smul]
    rw [hΩT]
    exact transfer_mem_gauge n β _
  obtain ⟨x, hxN, hxG, hxo, hx0⟩ := exists_neutral_orth n Ω hn hN hG
  let W : Submodule ℂ (Hilbert n) := neutralSubspace n ⊓ (ℂ ∙ Ω)ᗮ
  have hWmem (f : Hilbert n) : f ∈ W ↔ Neutral n f ∧ inner ℂ Ω f = (0 : ℂ) := by
    change f ∈ neutralSubspace n ∧ f ∈ (ℂ ∙ Ω)ᗮ ↔ _
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    rfl
  haveI : CompleteSpace W := by
    have hc : IsClosed (W : Set (Hilbert n)) :=
      (neutralSubspace_closed n).inter (Submodule.isClosed_orthogonal _)
    exact hc.completeSpace_coe
  have hinv : ∀ f ∈ W, TwistedTransfer.transfer n β f ∈ W := by
    intro f hf
    obtain ⟨h1, h2⟩ := (hWmem f).mp hf
    refine (hWmem _).mpr ⟨transfer_mem_neutral n β h1, ?_⟩
    rw [← transfer_symm', htop, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, h2, mul_zero]
  obtain ⟨v, hvW, hvn, lam, hlam0, hTv, hle⟩ := top_on_invariant (TwistedTransfer.transfer n β)
    (transfer_positive n β hβ.le) (TwistedTransfer.transfer_compact n β) W hinv x ((hWmem x).mpr ⟨hxN, hxo⟩)
    (fun h0 => hx0 (transfer_injective_gauge n β hβ hxG h0))
  obtain ⟨hvN, hvo⟩ := (hWmem v).mp hvW
  have hself : inner ℂ Ω Ω = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hn]
    simp
  have hlamle : lam ≤ L := by
    have h1 := (TwistedTransfer.transfer n β).le_opNorm v
    rw [hTv, norm_smul, hvn, mul_one, mul_one, Real.norm_eq_abs, abs_of_pos hlam0] at h1
    exact h1
  have hlt : lam < L := by
    refine lt_of_le_of_ne hlamle fun heq => ?_
    rw [heq] at hTv
    obtain ⟨c, hc⟩ := hsimple v hTv
    rw [hc, inner_smul_right, hself, mul_one] at hvo
    rw [hc, hvo, zero_smul, norm_zero] at hvn
    exact zero_ne_one hvn
  refine ⟨Ω, v, lam / L, hn, htop, hN, hsimple, div_pos hlam0 hlam, (div_lt_one hlam).mpr hlt, hvn, hvN, hvo, ?_, ?_⟩
  · rw [div_mul_cancel₀ _ hlam.ne']
    exact hTv
  · intro f hfN hfo
    rw [div_mul_cancel₀ _ hlam.ne']
    exact hle f ((hWmem f).mpr ⟨hfN, hfo⟩)

/-- **The window of Target A holds at every cutoff, for `β > 0`**, with both constants equal to the
exact level `ρ`. So both halves of `NeutralWindow` hold at one cutoff, and `TargetAGap` is purely a
statement of uniformity in `n`. -/
theorem exists_neutralWindow (hβ : 0 < β) : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ NeutralWindow n β ρ ρ := by
  obtain ⟨Ω, v, ρ, hn, htop, hN, -, hρ, hρ1, hvn, hvN, hvo, hTv, hle⟩ := neutral_level n β hβ
  refine ⟨ρ, hρ, hρ1, Ω, hn, htop, hN, hle, v, hvN, hvo, ?_, ?_⟩
  · rintro rfl
    simp at hvn
  · rw [hTv, norm_smul, hvn, mul_one, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hρ.le (norm_nonneg _))]

/-- **`NeutralWindow` is a statement about one number.** For `β > 0` there is `ρ ∈ (0, 1)`, the exact
first excited neutral level in units of `‖T‖`, such that for `ρ₂ > 0` the window holds exactly when
`ρ₂ ≤ ρ ≤ ρ₁`. `TargetAGap` asks for two-sided bounds on this number along a trajectory, and these remain
open. -/
theorem neutralWindow_iff_level (hβ : 0 < β) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ ρ₁ ρ₂ : ℝ, 0 < ρ₂ → (NeutralWindow n β ρ₁ ρ₂ ↔ ρ₂ ≤ ρ ∧ ρ ≤ ρ₁) := by
  obtain ⟨Ω, v, ρ, hn, htop, hN, hsimple, hρ, hρ1, hvn, hvN, hvo, hTv, hle⟩ := neutral_level n β hβ
  have hlam := norm_transfer_pos n β
  set L := ‖TwistedTransfer.transfer n β‖ with hL
  have hself : inner ℂ Ω Ω = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hn]
    simp
  have hTvn : ‖TwistedTransfer.transfer n β v‖ = ρ * L := by
    rw [hTv, norm_smul, hvn, mul_one, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine ⟨ρ, hρ, hρ1, fun ρ₁ ρ₂ h₂ => ⟨?_, ?_⟩⟩
  · rintro ⟨Ω', hn', htop', hN', hc, f, hfN, hfo, hf0, hfl⟩
    obtain ⟨c, hc'⟩ := hsimple Ω' htop'
    have hcn : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc'
      rw [hc', norm_zero] at hn'
      exact zero_ne_one hn'
    have hΩf : inner ℂ Ω f = (0 : ℂ) := by
      rw [hc', inner_smul_left] at hfo
      exact (mul_eq_zero.mp hfo).resolve_left (by simpa using hcn)
    have hfpos : 0 < ‖f‖ := norm_pos_iff.mpr hf0
    constructor
    · have := hfl.trans (hle f hfN hΩf)
      have h' : ρ₂ * (L * ‖f‖) ≤ ρ * (L * ‖f‖) := by nlinarith
      exact le_of_mul_le_mul_right h' (by positivity)
    · have h1 : inner ℂ Ω' v = (0 : ℂ) := by
        rw [hc', inner_smul_left, hvo, mul_zero]
      have h2 := hc v hvN h1
      rw [hTvn, hvn, mul_one] at h2
      exact le_of_mul_le_mul_right h2 hlam
  · rintro ⟨h1, h2⟩
    refine ⟨Ω, hn, htop, hN, fun f hfN hfo => (hle f hfN hfo).trans ?_, v, hvN, hvo, ?_, ?_⟩
    · gcongr
    · rintro rfl
      simp at hvn
    · rw [hTvn, hvn, mul_one]
      gcongr

/-- **`β > 0` is necessary.** At `β = 0` the second half of the window fails, since `T` has rank one. -/
theorem not_neutralWindow_zero (ρ₁ ρ₂ : ℝ) (h₂ : 0 < ρ₂) : ¬ NeutralWindow n 0 ρ₁ ρ₂ := by
  rintro ⟨Ω, hn, htop, -, -, f, -, hfo, hf0, hfl⟩
  have hlam := norm_transfer_pos n 0
  set L := ‖TwistedTransfer.transfer n 0‖ with hL
  set a := ContinuousMap.toLp 2 (μ') ℂ (1 : C(Slice n, ℂ)) with ha
  have hΩ : (L : ℂ) • Ω = inner ℂ a Ω • a := by
    rw [← transfer_zero, htop, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have hc : inner ℂ a Ω ≠ (0 : ℂ) := by
    intro h0
    rw [h0, zero_smul] at hΩ
    have := (smul_eq_zero.mp hΩ).resolve_left (Complex.ofReal_ne_zero.mpr hlam.ne')
    rw [this, norm_zero] at hn
    exact zero_ne_one hn
  have hTf : TwistedTransfer.transfer n 0 f = 0 := by
    rw [transfer_zero]
    have h1 : inner ℂ ((L : ℂ) • Ω) f = (0 : ℂ) := by
      rw [inner_smul_left, hfo, mul_zero]
    rw [hΩ, inner_smul_left] at h1
    have h2 : inner ℂ a f = (0 : ℂ) := (mul_eq_zero.mp h1).resolve_left ((map_ne_zero _).mpr hc)
    rw [h2, zero_smul]
  rw [hTf, norm_zero] at hfl
  have : 0 < ρ₂ * L * ‖f‖ := by
    have := norm_pos_iff.mpr hf0
    positivity
  linarith

/-- The first excited neutral level in units of `‖T‖`, for `β > 0`. -/
def neutralLevel (n : ℕ) [NeZero n] (β : ℝ) : ℝ :=
  if h : 0 < β then Classical.choose (neutralWindow_iff_level n β h) else 0

theorem neutralLevel_spec (hβ : 0 < β) :
    0 < neutralLevel n β ∧ neutralLevel n β < 1 ∧ ∀ ρ₁ ρ₂ : ℝ, 0 < ρ₂ →
      (NeutralWindow n β ρ₁ ρ₂ ↔ ρ₂ ≤ neutralLevel n β ∧ neutralLevel n β ≤ ρ₁) := by
  unfold neutralLevel
  rw [dif_pos hβ]
  exact Classical.choose_spec (neutralWindow_iff_level n β hβ)

/-- **`TargetAGap` as a statement about one number.** It is exactly a two-sided bound on `neutralLevel`
along a trajectory that stays in `β > 0`. This is a reformulation, and it proves neither bound. -/
theorem targetAGap_iff_level (b : ℝ) :
    TargetAGap b ↔ ∃ β₀ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ (n : ℕ) [NeZero n], 2 ≤ n → ∀ β, b * Real.log n + β₀ ≤ β →
      0 < β ∧ Real.exp (-C / n) ≤ neutralLevel n β ∧ neutralLevel n β ≤ Real.exp (-c / n) := by
  constructor
  · rintro ⟨β₀, c, C, hc, hcC, h⟩
    refine ⟨β₀, c, C, hc, hcC, fun m _ hm β hβ => ?_⟩
    have hpos : 0 < β := by
      by_contra hne
      push_neg at hne
      exact not_neutralWindow_zero m _ _ (Real.exp_pos _) (h m hm 0 (hβ.trans hne))
    obtain ⟨-, -, hw⟩ := neutralLevel_spec m β hpos
    obtain ⟨h1, h2⟩ := (hw _ _ (Real.exp_pos _)).mp (h m hm β hβ)
    exact ⟨hpos, h1, h2⟩
  · rintro ⟨β₀, c, C, hc, hcC, h⟩
    refine ⟨β₀, c, C, hc, hcC, fun m _ hm β hβ => ?_⟩
    obtain ⟨hpos, h1, h2⟩ := h m hm β hβ
    obtain ⟨-, -, hw⟩ := neutralLevel_spec m β hpos
    exact (hw _ _ (Real.exp_pos _)).mpr ⟨h1, h2⟩

end KernelOfT

section LawTrace
open TwistedReflection
variable (n : ℕ) [NeZero n]

/-- `chainZ_trace` for every time extent `T ≥ 2` and every Hilbert basis. -/
theorem chainZ_trace_of_two_le (m T : ℕ) [NeZero m] [NeZero T] (hT : 2 ≤ T) {ι : Type*}
    (b : HilbertBasis ι ℂ (WilsonSlabOperator.Hilbert m)) (β : ℝ) :
    HasSum (fun k => inner ℂ (b k) (((TwistedTransfer.transfer m β) ^ T) (b k))) ((chainZ T m β : ℝ) : ℂ) := by
  obtain ⟨r, rfl⟩ : ∃ r, T = r + 2 := ⟨T - 2, by omega⟩
  haveI := countable_of_basis (WilsonSlabOperator.measure m) b
  exact chainZ_trace m b β r

/-- **The partition function of the existing law at `T = L = 2n` is the trace of `T^(2n)`**, in every
Hilbert basis. -/
theorem law_partition_trace {ι : Type*} (b : HilbertBasis ι ℂ (WilsonSlabOperator.Hilbert (2 * n))) (β : ℝ) :
    HasSum (fun k => inner ℂ (b k) (((TwistedTransfer.transfer (2 * n) β) ^ (2 * n)) (b k)))
      ((∫ U, Real.exp (-action n Q (spatialTwist n) character β 2 U)
        ∂referenceMeasure Q (Vertex (2 * n)) : ℝ) : ℂ) := by
  rw [action_partition]
  have : 2 ≤ 2 * n := by
    have := Nat.pos_of_ne_zero (NeZero.ne n)
    omega
  exact chainZ_trace_of_two_le (2 * n) (2 * n) this b β

end LawTrace

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedNeutral
