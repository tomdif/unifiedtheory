/- The Wilson gradient flow of the twisted action on the compact configuration space, at unit coupling.

Deterministic, for every lattice size and with no smallness: global existence and uniqueness for all real times
(`wf`, `wf_unique`), the group law and joint continuity, covariance under gauge transformations, center flips, the
time reflection and translations up to a center flip (`wf_gauge`, `wf_flip`, `wf_reflect`, `wf_Rκ`), the energy
identity (`energy_wf`), the Bochner identity for the squared force (`hasDerivAt_force`), the smoothing inequality
`forceSq(t) ≤ (1/t + 96)(S(0) - S(t))` (`wf_smoothing`), a local energy inequality with no constant depending on the
lattice size (`local_energy`, `flow_locality`), and the static bounds `forceSq ≤ 96 S` (`force_static`), its local form
`‖V_e‖² ≤ 24 Σ_{p ∋ e} term_p` (`link_force_local`), and `‖V_e‖ ≤ 12` (`link_field_le`).

Decay in flow time, only near the flat fields. If `S ≤ (1/(1408 N⁵))²`, then `3 S ≤ N² forceSq` (`grad_dom`), so
`S(t) ≤ exp(-3t/N²) S(0)` for all `t ≥ 0` (`wf_action_decay`), and the flow converges to a flat field (`wf_tendsto_flat`).
The rate is of the expected form `c/N²`. The threshold
comes only from `near_flat`: `grad_dom_of_target` needs only a target with `dist² ≤ K S`, `K √S ≤ 1/100` and `S ≤ 1/100`.

Decay cannot hold in general, and this is proved. For every `m` with `2m + 1 ≤ N²` the constant-flux field `critLink` is
a fixed point, with action between `4(2m+1)²` and `((2m+1)π)²` and all defects at most `(2m+1)π/N²`
(`exists_critical_field`). So no bound on the defects alone, at any scale `e ≥ π/N²`, and no bound on the energy density
alone gives decay (`exists_critical_at_scale`), and gradient domination fails on `{S ≤ π²}` (`not_grad_dom`). A proof of
decay for typical fields at `β` growing like `log N` has to use the measure, not only the size of the field.

For the law, at zero flow time, the local mean bounds are those of `TwistedLocalTail`, which are stronger than
`law_term_mean`. At positive flow time they extend by the action decrease and translation up to a center flip, and nothing
else: `Σ_P E[term ∘ wf t] ≤ 4 log cap(24β) / β` (`law_plaquette_mean_wf`), `≤ (3 + 1/N)(-log mass(6β))/β`
(`law_plaquette_mean_wf_log`), `≤ 27/β` when `-log mass(6β) ≤ n` (`law_plaquette_mean_wf_explicit`), and the force at one
site is at most `96 · 4 log cap(24β) / β` (`law_force_local_static`). These do not decrease in `t`. Smoothing adds nothing
to them: it survives at the level of the law only with the dissipated action on the right (`law_force_dissipation`). Decay
of the mean is `law_action_wf_decay` and `law_plaquette_mean_decay`, whose extra term is the tail of the action above the
threshold of `near_flat`. That term is small only for `β` of order `N¹⁴ log N`, where the theory is close to free.

An exact identity for the actual measure: `β E[forceSq] = 12 (12 N⁴ - E[S])` for every `β > 0` and every lattice size
(`law_force_exact`), from `TwistedIBP.gibbs_ibp` summed over a unit basis. With `forceSq ≤ 96 S` it gives the lower bound
`E[S] ≥ 144 N⁴ / (96 β + 12)` (`law_action_ge`). With the Hessian ceiling it gives a strict decrease of the mean action by
`(1 - exp(-96 t))/(8β)` times `12 N⁴ - E[S]`, at every `β` (`law_action_wf_strict`). That is a fixed multiple of `1/β` per
site, it stops growing past `t ≈ 1/96`, and it is not decay in flow time.

Not proved, and not implied. This is not the uniform bound of Target A. On a trajectory `β ~ log N`, nothing here shows
the flowed energy decreasing beyond the fixed amount above. There is no sup bound on the flowed field below the threshold
of `near_flat`, no convergence as `N → ∞`, no nontriviality, and no reflection positivity for flowed observables:
`wf_reflect` is only a covariance, and a flowed observable is not supported on a half lattice. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedIBP
import UnifiedTheory.Clay.YangMills.Twisted.TwistedCovariant
import UnifiedTheory.Clay.YangMills.Twisted.TwistedLocalTail
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedFlow
noncomputable section
open Filter Topology Set Metric MeasureTheory
open scoped Quaternion RealInnerProductSpace NNReal
open WilsonSingleLinkStaples (Q character character_re)

/-! ### Gradient flow on a product of unit spheres in `ℍ` -/

section Abstract
variable {ι : Type*} [Fintype ι]

/-- The ambient Hilbert space. -/
abbrev Amb (ι : Type*) [Fintype ι] := PiLp 2 fun _ : ι => ℍ[ℝ]

/-- `‖x‖²` times the component of `w` orthogonal to `x`. On the unit sphere this is the tangential
projection of `w`. -/
def tang (w x : ℍ[ℝ]) : ℍ[ℝ] := ‖x‖ ^ 2 • w - ⟪w, x⟫ • x

theorem inner_tang (w x : ℍ[ℝ]) : ⟪tang w x, x⟫ = 0 := by
  simp only [tang, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  ring

/-- The negative tangential gradient of `S`, at every point of the ambient space. -/
def field (S : Amb ι → ℝ) (x : Amb ι) : Amb ι :=
  WithLp.toLp 2 fun e => -tang (gradient S x e) (x e)

theorem field_apply (S : Amb ι → ℝ) (x : Amb ι) (e : ι) :
    field S x e = -tang (gradient S x e) (x e) := rfl

theorem inner_field (S : Amb ι → ℝ) (x : Amb ι) (e : ι) : ⟪field S x e, x e⟫ = 0 := by
  rw [field_apply, inner_neg_left, inner_tang, neg_zero]

/-- Every link has unit length. -/
def Sph (x : Amb ι) : Prop := ∀ e, ‖x e‖ = 1

theorem norm_sq_amb (x : Amb ι) : ‖x‖ ^ 2 = ∑ e, ‖x e‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]

theorem inner_amb (x y : Amb ι) : ⟪x, y⟫ = ∑ e, ⟪x e, y e⟫ := PiLp.inner_apply x y

theorem Sph.norm_sq {x : Amb ι} (hx : Sph x) : ‖x‖ ^ 2 = Fintype.card ι := by
  rw [norm_sq_amb]
  simp [hx _]

theorem contDiff_gradient {S : Amb ι → ℝ} (hS : ContDiff ℝ 2 S) : ContDiff ℝ 1 (gradient S) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ S) := hS.fderiv_right (m := 1) (by norm_num)
  have hg : gradient S = fun x => ∑ i, fderiv ℝ S x (stdOrthonormalBasis ℝ (Amb ι) i) •
      stdOrthonormalBasis ℝ (Amb ι) i := by
    funext x
    have h := (stdOrthonormalBasis ℝ (Amb ι)).sum_repr' (gradient S x)
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [real_inner_comm]
    simp [gradient]
  rw [hg]
  refine ContDiff.sum fun i _ => ?_
  exact (hd.clm_apply contDiff_const).smul contDiff_const

theorem contDiff_field {S : Amb ι → ℝ} (hS : ContDiff ℝ 2 S) : ContDiff ℝ 1 (field S) := by
  have hg := contDiff_gradient hS
  refine (contDiff_piLp 2).2 fun e => ?_
  simp only [field_apply, tang]
  have h1 : ContDiff ℝ 1 fun x : Amb ι => gradient S x e :=
    (contDiff_piLp_apply (p := 2) (i := e)).comp hg
  have h2 : ContDiff ℝ 1 fun x : Amb ι => x e := contDiff_piLp_apply (p := 2) (i := e)
  exact (((h2.norm_sq ℝ).smul h1).sub ((h1.inner ℝ h2).smul h2)).neg

/-- A cutoff equal to one on a ball containing all unit configurations. -/
def bump (ι : Type*) [Fintype ι] : ContDiffBump (0 : Amb ι) where
  rIn := √(Fintype.card ι) + 1
  rOut := √(Fintype.card ι) + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- The truncated field, compactly supported. -/
def tf (S : Amb ι → ℝ) (x : Amb ι) : Amb ι := bump ι x • field S x

theorem Sph.bump_eq {x : Amb ι} (hx : Sph x) : bump ι x = 1 := by
  refine (bump ι).one_of_mem_closedBall ?_
  rw [mem_closedBall_zero_iff]
  have h := hx.norm_sq
  have : ‖x‖ = √(Fintype.card ι) := by
    rw [← h, Real.sqrt_sq (norm_nonneg _)]
  rw [this]
  change _ ≤ √(Fintype.card ι) + 1
  linarith

theorem tf_eq {S : Amb ι → ℝ} {x : Amb ι} (hx : Sph x) : tf S x = field S x := by
  rw [tf, hx.bump_eq, one_smul]

theorem contDiff_tf {S : Amb ι → ℝ} (hS : ContDiff ℝ 2 S) : ContDiff ℝ 1 (tf S) :=
  (bump ι).contDiff.smul (contDiff_field hS)

theorem hasCompactSupport_tf (S : Amb ι → ℝ) : HasCompactSupport (tf S) :=
  (bump ι).hasCompactSupport.smul_right

theorem exists_lipschitz_tf {S : Amb ι → ℝ} (hS : ContDiff ℝ 2 S) : ∃ K, LipschitzWith K (tf S) :=
  (contDiff_tf hS).lipschitzWith_of_hasCompactSupport (hasCompactSupport_tf S) (by norm_num)

theorem exists_bound_tf {S : Amb ι → ℝ} (hS : ContDiff ℝ 2 S) : ∃ L : ℝ≥0, ∀ x, ‖tf S x‖ ≤ L := by
  obtain ⟨C, hC⟩ := (hasCompactSupport_tf S).exists_bound_of_continuous (contDiff_tf hS).continuous
  refine ⟨⟨max C 0, le_max_right _ _⟩, fun x => (hC x).trans (le_max_left _ _)⟩

/-- Solutions of the truncated equation on an arbitrary interval: the field is globally Lipschitz and
bounded, so a single application of Picard-Lindelöf reaches any time. -/
theorem exists_local {S : Amb ι → ℝ} (hS : ContDiff ℝ 2 S) (x : Amb ι) (T : ℝ) (hT : 0 < T) :
    ∃ α : ℝ → Amb ι, α 0 = x ∧ ∀ t ∈ Icc (-T) T, HasDerivWithinAt α (tf S (α t)) (Icc (-T) T) t := by
  obtain ⟨K, hK⟩ := exists_lipschitz_tf hS
  obtain ⟨L, hL⟩ := exists_bound_tf hS
  have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT.le⟩
  have hPL : IsPicardLindelof (fun _ => tf S) (tmin := -T) (tmax := T) ⟨0, h0⟩ x
      (L * ⟨T, hT.le⟩) 0 L K := by
    refine IsPicardLindelof.of_time_independent (fun y _ => hL y) hK.lipschitzOnWith ?_
    simp [NNReal.coe_mul]
  exact hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

theorem exists_global {S : Amb ι → ℝ} (hS : ContDiff ℝ 2 S) (x : Amb ι) :
    ∃ γ : ℝ → Amb ι, γ 0 = x ∧ ∀ t, HasDerivAt γ (tf S (γ t)) t := by
  obtain ⟨K, hK⟩ := exists_lipschitz_tf hS
  have hex (T : {T : ℝ // 0 < T}) := exists_local hS x T.1 T.2
  choose α hα0 hα using hex
  have hder (T : {T : ℝ // 0 < T}) (t : ℝ) (ht : t ∈ Ioo (-T.1) T.1) :
      HasDerivAt (α T) (tf S (α T t)) t :=
    (hα T t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  -- Compatibility of the solutions on nested intervals.
  have hcompat (T T' : {T : ℝ // 0 < T}) (h : T.1 ≤ T'.1) :
      EqOn (α T) (α T') (Icc (-T.1) T.1) := by
    have h0 : (0 : ℝ) ∈ Ioo (-T.1) T.1 := ⟨by linarith [T.2], T.2⟩
    have hsub : Icc (-T.1) T.1 ⊆ Icc (-T'.1) T'.1 :=
      Icc_subset_Icc (by linarith) h
    refine ODE_solution_unique_of_mem_Icc (v := fun _ => tf S) (s := fun _ => univ) (K := K)
      (fun _ _ => hK.lipschitzOnWith) h0
      (fun t ht => (hα T t ht).continuousWithinAt)
      (fun t ht => hder T t ht) (fun _ _ => mem_univ _)
      (fun t ht => ((hα T' t (hsub ht)).mono hsub).continuousWithinAt)
      (fun t ht => (hα T' t (hsub (Ioo_subset_Icc_self ht))).hasDerivAt
        (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2])))
      (fun _ _ => mem_univ _) (by rw [hα0, hα0])
  let τ (t : ℝ) : {T : ℝ // 0 < T} := ⟨|t| + 1, by positivity⟩
  have hagree (T : {T : ℝ // 0 < T}) (s : ℝ) (hs : |s| ≤ T.1) : α (τ s) s = α T s := by
    have hsτ : |s| ≤ (τ s).1 := by simp [τ]
    rcases le_total (τ s).1 T.1 with h | h
    · exact hcompat _ _ h (abs_le.1 hsτ)
    · exact (hcompat _ _ h (abs_le.1 hs)).symm
  refine ⟨fun t => α (τ t) t, ?_, fun t => ?_⟩
  · exact hα0 _
  · have ht : t ∈ Ioo (-(τ t).1) (τ t).1 := by
      have := abs_le.1 (le_refl |t|)
      constructor <;> simp only [τ] <;> linarith
    have hd := hder (τ t) t ht
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact hagree _ s (abs_le.2 ⟨hs.1.le, hs.2.le⟩)

theorem hasDerivAt_coord {γ : ℝ → Amb ι} {v : Amb ι} {t : ℝ} (h : HasDerivAt γ v t) (e : ι) :
    HasDerivAt (fun s => γ s e) (v e) t :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℍ[ℝ]) e).hasFDerivAt.comp_hasDerivAt t h

theorem hasDerivAt_amb {γ : ℝ → Amb ι} {v : Amb ι} {t : ℝ}
    (h : ∀ e, HasDerivAt (fun s => γ s e) (v e) t) : HasDerivAt γ v t := by
  have := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℍ[ℝ])).symm.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_pi.2 h)
  exact this


variable {S : Amb ι → ℝ}

/-- An integral curve of the negative tangential gradient. -/
def IsLine (S : Amb ι → ℝ) (γ : ℝ → Amb ι) : Prop := ∀ t, HasDerivAt γ (field S (γ t)) t

theorem norm_conserved {γ : ℝ → Amb ι} {c : ℝ → ℝ}
    (h : ∀ t, HasDerivAt γ (c t • field S (γ t)) t) (e : ι) (t t' : ℝ) :
    ‖γ t e‖ = ‖γ t' e‖ := by
  have hd (s : ℝ) : HasDerivAt (fun s => ‖γ s e‖ ^ 2) 0 s := by
    have := (hasDerivAt_coord (h s) e).norm_sq
    convert this using 1
    change _ = 2 * ⟪γ s e, c s • field S (γ s) e⟫
    rw [real_inner_smul_right, real_inner_comm, inner_field]
    ring
  have hc := is_const_of_deriv_eq_zero (f := fun s => ‖γ s e‖ ^ 2)
    (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t t'
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hc

theorem IsLine.sph {γ : ℝ → Amb ι} (h : IsLine S γ) {t₀ : ℝ} (h0 : Sph (γ t₀)) (t : ℝ) : Sph (γ t) := by
  intro e
  rw [norm_conserved (c := fun _ => 1) (S := S) (γ := γ)
    (fun s => by simpa using h s) e t t₀]
  exact h0 e

theorem IsLine.tf {γ : ℝ → Amb ι} (h : IsLine S γ) {t₀ : ℝ} (h0 : Sph (γ t₀)) (t : ℝ) :
    HasDerivAt γ (tf S (γ t)) t := by
  rw [tf_eq (h.sph h0 t)]
  exact h t

theorem exists_line (hS : ContDiff ℝ 2 S) {x : Amb ι} (hx : Sph x) :
    ∃ γ : ℝ → Amb ι, γ 0 = x ∧ IsLine S γ := by
  obtain ⟨γ, h0, hγ⟩ := exists_global hS x
  have hs (t : ℝ) : Sph (γ t) := fun e => by
    rw [norm_conserved (c := fun s => bump ι (γ s)) (S := S) (γ := γ) hγ e t 0, h0]
    exact hx e
  exact ⟨γ, h0, fun t => by simpa only [tf_eq (hs t)] using hγ t⟩

theorem IsLine.unique (hS : ContDiff ℝ 2 S) {γ δ : ℝ → Amb ι} (h : IsLine S γ) (h' : IsLine S δ)
    {t₀ : ℝ} (h0 : Sph (γ t₀)) (heq : γ t₀ = δ t₀) : γ = δ := by
  obtain ⟨K, hK⟩ := exists_lipschitz_tf hS
  have h0' : Sph (δ t₀) := heq ▸ h0
  exact ODE_solution_unique_univ (v := fun _ => TwistedFlow.tf S) (s := fun _ => univ) (K := K)
    (fun _ => hK.lipschitzOnWith) (fun t => ⟨h.tf h0 t, mem_univ _⟩)
    (fun t => ⟨h'.tf h0' t, mem_univ _⟩) heq

theorem IsLine.shift {γ : ℝ → Amb ι} (h : IsLine S γ) (a : ℝ) : IsLine S fun t => γ (t + a) :=
  fun t => (h (t + a)).comp_add_const t a

/-! ### The flow on unit configurations -/

theorem unit_norm (q : Q) : ‖(q : ℍ[ℝ])‖ = 1 := by
  have h : star (q : ℍ[ℝ]) * q = 1 := Unitary.star_mul_self_of_mem q.2
  have h1 := congrArg norm h
  rw [norm_mul, norm_star, norm_one] at h1
  nlinarith [norm_nonneg (q : ℍ[ℝ]), sq_nonneg (‖(q : ℍ[ℝ])‖ - 1)]

theorem star_mul_unit {x : ℍ[ℝ]} (h : ‖x‖ = 1) : star x * x = 1 := by
  rw [Quaternion.star_mul_self, Quaternion.normSq_eq_norm_mul_self, h]
  norm_num

theorem mul_star_unit {x : ℍ[ℝ]} (h : ‖x‖ = 1) : x * star x = 1 := by
  rw [Quaternion.self_mul_star, Quaternion.normSq_eq_norm_mul_self, h]
  norm_num

/-- The inclusion of unit configurations. -/
def emb (U : ι → Q) : Amb ι := WithLp.toLp 2 fun e => (U e : ℍ[ℝ])

theorem emb_apply (U : ι → Q) (e : ι) : emb U e = (U e : ℍ[ℝ]) := rfl

theorem emb_sph (U : ι → Q) : Sph (emb U) := fun e => unit_norm (U e)

theorem continuous_emb : Continuous (emb : (ι → Q) → Amb ι) := by
  refine (PiLp.continuous_toLp 2 _).comp ?_
  exact continuous_pi fun e => continuous_subtype_val.comp (continuous_apply e)

/-- A point of the sphere as a unit configuration. -/
def ofSph (x : Amb ι) (hx : Sph x) : ι → Q :=
  fun e => ⟨x e, Unitary.mem_iff.2 ⟨star_mul_unit (hx e), mul_star_unit (hx e)⟩⟩

theorem emb_ofSph (x : Amb ι) (hx : Sph x) : emb (ofSph x hx) = x := rfl

theorem ofSph_emb (U : ι → Q) : ofSph (emb U) (emb_sph U) = U := rfl

theorem emb_injective : Function.Injective (emb : (ι → Q) → Amb ι) := by
  intro U V h
  funext e
  apply Subtype.ext
  exact congrArg (fun x : Amb ι => x e) h

/-- The integral curve through a unit configuration. -/
def line (hS : ContDiff ℝ 2 S) (U : ι → Q) : ℝ → Amb ι :=
  Classical.choose (exists_line hS (emb_sph U))

theorem line_zero (hS : ContDiff ℝ 2 S) (U : ι → Q) : line hS U 0 = emb U :=
  (Classical.choose_spec (exists_line hS (emb_sph U))).1

theorem line_isLine (hS : ContDiff ℝ 2 S) (U : ι → Q) : IsLine S (line hS U) :=
  (Classical.choose_spec (exists_line hS (emb_sph U))).2

theorem line_sph (hS : ContDiff ℝ 2 S) (U : ι → Q) (t : ℝ) : Sph (line hS U t) :=
  (line_isLine hS U).sph (t₀ := 0) (by rw [line_zero]; exact emb_sph U) t

/-- **The gradient flow on the compact configuration space, for all times.** -/
def wflow (hS : ContDiff ℝ 2 S) (t : ℝ) (U : ι → Q) : ι → Q := ofSph (line hS U t) (line_sph hS U t)

theorem emb_wflow (hS : ContDiff ℝ 2 S) (t : ℝ) (U : ι → Q) : emb (wflow hS t U) = line hS U t := rfl

/-- Existence and uniqueness: `t ↦ wflow t U` is the only integral curve through `U`. -/
theorem wflow_unique (hS : ContDiff ℝ 2 S) (U : ι → Q) {γ : ℝ → Amb ι} (hγ : IsLine S γ)
    (h0 : γ 0 = emb U) : γ = fun t => emb (wflow hS t U) :=
  hγ.unique hS (line_isLine hS U) (t₀ := 0) (by rw [h0]; exact emb_sph U)
    (by change _ = line hS U 0; rw [h0, line_zero])

theorem wflow_isLine (hS : ContDiff ℝ 2 S) (U : ι → Q) : IsLine S fun t => emb (wflow hS t U) :=
  line_isLine hS U

theorem wflow_zero (hS : ContDiff ℝ 2 S) (U : ι → Q) : wflow hS 0 U = U := by
  apply emb_injective
  rw [emb_wflow, line_zero]

theorem wflow_add (hS : ContDiff ℝ 2 S) (s t : ℝ) (U : ι → Q) :
    wflow hS s (wflow hS t U) = wflow hS (s + t) U := by
  apply emb_injective
  have h := wflow_unique hS (wflow hS t U) ((line_isLine hS U).shift t)
    (by rw [zero_add]; rfl)
  have := congrFun h s
  exact this.symm

/-! ### Continuity -/

theorem hasDerivAt_rev {γ : ℝ → Amb ι} (h : IsLine S γ) {t₀ : ℝ} (h0 : Sph (γ t₀)) (s : ℝ) :
    HasDerivAt (fun s => γ (-s)) (-(TwistedFlow.tf S (γ (-s)))) s := by
  have := (h.tf h0 (-s)).scomp s (hasDerivAt_neg s)
  simpa [Function.comp_def] using this

theorem dist_line_le (hS : ContDiff ℝ 2 S) {K : ℝ≥0} (hK : LipschitzWith K (TwistedFlow.tf S))
    (U V : ι → Q) (t : ℝ) :
    dist (line hS U t) (line hS V t) ≤ dist (emb U) (emb V) * Real.exp (K * |t|) := by
  have s0 (W : ι → Q) : Sph (line hS W 0) := by rw [line_zero]; exact emb_sph W
  rcases le_total 0 t with ht | ht
  · have := dist_le_of_trajectories_ODE (v := fun _ => TwistedFlow.tf S) (K := K)
      (f := line hS U) (g := line hS V) (a := 0) (b := t) (δ := dist (emb U) (emb V))
      (fun _ => hK)
      (fun s _ => ((line_isLine hS U).tf (s0 U) s).continuousAt.continuousWithinAt)
      (fun s _ => ((line_isLine hS U).tf (s0 U) s).hasDerivWithinAt)
      (fun s _ => ((line_isLine hS V).tf (s0 V) s).continuousAt.continuousWithinAt)
      (fun s _ => ((line_isLine hS V).tf (s0 V) s).hasDerivWithinAt)
      (by rw [line_zero, line_zero]) t ⟨ht, le_rfl⟩
    rw [sub_zero] at this
    rwa [abs_of_nonneg ht]
  · have hn : LipschitzWith K (fun x => -(TwistedFlow.tf S x)) := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [dist_neg_neg]
      exact hK.dist_le_mul x y
    have := dist_le_of_trajectories_ODE (v := fun _ x => -(TwistedFlow.tf S x)) (K := K)
      (f := fun s => line hS U (-s)) (g := fun s => line hS V (-s)) (a := 0) (b := -t)
      (δ := dist (emb U) (emb V)) (fun _ => hn)
      (fun s _ => (hasDerivAt_rev (line_isLine hS U) (s0 U) s).continuousAt.continuousWithinAt)
      (fun s _ => (hasDerivAt_rev (line_isLine hS U) (s0 U) s).hasDerivWithinAt)
      (fun s _ => (hasDerivAt_rev (line_isLine hS V) (s0 V) s).continuousAt.continuousWithinAt)
      (fun s _ => (hasDerivAt_rev (line_isLine hS V) (s0 V) s).hasDerivWithinAt)
      (by simp only [neg_zero, line_zero]; exact le_rfl) (-t) ⟨by linarith, le_rfl⟩
    simp only [neg_neg, sub_zero] at this
    rwa [abs_of_nonpos ht]

theorem dist_line_time_le (hS : ContDiff ℝ 2 S) {L : ℝ≥0} (hL : ∀ x, ‖TwistedFlow.tf S x‖ ≤ L)
    (U : ι → Q) (s t : ℝ) : dist (line hS U s) (line hS U t) ≤ L * |s - t| := by
  have s0 : Sph (line hS U 0) := by rw [line_zero]; exact emb_sph U
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := univ)
    (f := line hS U) (f' := fun r => TwistedFlow.tf S (line hS U r)) (C := L) (x := t) (y := s)
    (fun r _ => ((line_isLine hS U).tf s0 r).hasDerivWithinAt) (fun r _ => hL _) convex_univ
    (mem_univ _) (mem_univ _)
  rw [dist_eq_norm]
  simpa [Real.norm_eq_abs] using this

/-- The flow is jointly continuous in time and configuration. -/
theorem continuous_wflow (hS : ContDiff ℝ 2 S) :
    Continuous fun p : ℝ × (ι → Q) => wflow hS p.1 p.2 := by
  obtain ⟨K, hK⟩ := exists_lipschitz_tf hS
  obtain ⟨L, hL⟩ := exists_bound_tf hS
  have hline : Continuous fun p : ℝ × (ι → Q) => line hS p.2 p.1 := by
    rw [continuous_iff_continuousAt]
    rintro ⟨t₀, U₀⟩
    rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
    have hb (p : ℝ × (ι → Q)) : dist (line hS p.2 p.1) (line hS U₀ t₀) ≤
        dist (emb p.2) (emb U₀) * Real.exp (K * |p.1|) + L * |p.1 - t₀| := by
      refine (dist_triangle _ (line hS U₀ p.1) _).trans ?_
      exact add_le_add (dist_line_le hS hK _ _ _) (dist_line_time_le hS hL _ _ _)
    refine squeeze_zero (fun _ => dist_nonneg) hb ?_
    have hcont : Continuous fun p : ℝ × (ι → Q) =>
        dist (emb p.2) (emb U₀) * Real.exp (K * |p.1|) + L * |p.1 - t₀| := by
      exact (((continuous_emb.comp continuous_snd).dist continuous_const).mul
        (Real.continuous_exp.comp (continuous_const.mul (continuous_abs.comp continuous_fst)))).add
        (continuous_const.mul (continuous_abs.comp (continuous_fst.sub continuous_const)))
    have := hcont.tendsto (t₀, U₀)
    simpa using this
  refine continuous_pi fun e => Continuous.subtype_mk ?_ _
  exact (PiLp.continuous_apply 2 _ e).comp hline


/-! ### Energy -/

theorem hasDerivAt_comp_S (hS : ContDiff ℝ 2 S) {c : ℝ → Amb ι} {v : Amb ι} {t : ℝ}
    (hc : HasDerivAt c v t) : HasDerivAt (fun s => S (c s)) ⟪gradient S (c t), v⟫ t := by
  have hd : DifferentiableAt ℝ S (c t) := (hS.differentiable (by norm_num)) (c t)
  have := hd.hasGradientAt.hasFDerivAt.comp_hasDerivAt t hc
  simpa [InnerProductSpace.toDual_apply_apply] using this

theorem tang_unit (w : ℍ[ℝ]) {x : ℍ[ℝ]} (hx : ‖x‖ = 1) : tang w x = w - ⟪w, x⟫ • x := by
  simp [tang, hx]

theorem inner_tang_self (w : ℍ[ℝ]) {x : ℍ[ℝ]} (hx : ‖x‖ = 1) :
    ⟪w, tang w x⟫ = ‖tang w x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  conv_rhs => lhs; rw [tang_unit w hx]
  rw [inner_sub_left, real_inner_smul_left, real_inner_comm (tang w x) x, inner_tang]
  ring

theorem norm_tang_sq (w : ℍ[ℝ]) {x : ℍ[ℝ]} (hx : ‖x‖ = 1) :
    ‖tang w x‖ ^ 2 = ‖w‖ ^ 2 - ⟪w, x⟫ ^ 2 := by
  rw [← inner_tang_self w hx, tang_unit w hx, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  ring

theorem inner_grad_field {x : Amb ι} (hx : Sph x) :
    ⟪gradient S x, field S x⟫ = -‖field S x‖ ^ 2 := by
  rw [inner_amb, norm_sq_amb, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [field_apply, inner_neg_right, inner_tang_self _ (hx e), norm_neg]

/-- The action decreases along the flow, with rate exactly the squared force. -/
theorem hasDerivAt_energy (hS : ContDiff ℝ 2 S) {γ : ℝ → Amb ι} (h : IsLine S γ) {t₀ : ℝ}
    (h0 : Sph (γ t₀)) (t : ℝ) : HasDerivAt (fun s => S (γ s)) (-‖field S (γ t)‖ ^ 2) t := by
  have := hasDerivAt_comp_S hS (h t)
  rwa [inner_grad_field (h.sph h0 t)] at this

theorem energy_antitone (hS : ContDiff ℝ 2 S) {γ : ℝ → Amb ι} (h : IsLine S γ) {t₀ : ℝ}
    (h0 : Sph (γ t₀)) : Antitone fun s => S (γ s) :=
  antitone_of_deriv_nonpos (fun s => (hasDerivAt_energy hS h h0 s).differentiableAt)
    fun s => by
      rw [(hasDerivAt_energy hS h h0 s).deriv]
      nlinarith [sq_nonneg ‖field S (γ s)‖]

theorem continuous_norm_field (hS : ContDiff ℝ 2 S) {γ : ℝ → Amb ι} (h : IsLine S γ) :
    Continuous fun s => ‖field S (γ s)‖ ^ 2 := by
  have hc : Continuous γ := continuous_iff_continuousAt.2 fun t => (h t).continuousAt
  exact (((contDiff_field hS).continuous.comp hc).norm).pow 2

/-- The energy identity. -/
theorem energy_identity (hS : ContDiff ℝ 2 S) {γ : ℝ → Amb ι} (h : IsLine S γ) {t₀ : ℝ}
    (h0 : Sph (γ t₀)) (a b : ℝ) :
    S (γ a) - S (γ b) = ∫ s in a..b, ‖field S (γ s)‖ ^ 2 := by
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b)
    (f := fun s => S (γ s)) (f' := fun s => -‖field S (γ s)‖ ^ 2)
    (fun s _ => hasDerivAt_energy hS h h0 s)
    ((continuous_norm_field hS h).neg.intervalIntegrable _ _)
  rw [intervalIntegral.integral_neg] at hint
  linarith only [hint]

/-! ### The second derivative along the rotation curve -/

/-- The curve `s ↦ exp(s ξ) x`, link by link. -/
def expCurve (ξ x : Amb ι) (s : ℝ) : Amb ι :=
  WithLp.toLp 2 fun e => NormedSpace.exp (s • ξ e) * x e

/-- Left multiplication, link by link. -/
def lmul (ξ x : Amb ι) : Amb ι := WithLp.toLp 2 fun e => ξ e * x e

theorem lmul_apply (ξ x : Amb ι) (e : ι) : lmul ξ x e = ξ e * x e := rfl

/-- The second derivative of `S` along `s ↦ exp(s ξ) x` at `s = 0`. -/
def hess (S : Amb ι → ℝ) (x ξ : Amb ι) : ℝ :=
  deriv (deriv fun s => S (expCurve ξ x s)) 0

theorem expCurve_zero (ξ x : Amb ι) : expCurve ξ x 0 = x := by
  refine PiLp.ext fun e => ?_
  simp [expCurve]

theorem expCurve_d1 (ξ x : Amb ι) (s : ℝ) : HasDerivAt (expCurve ξ x)
    (WithLp.toLp 2 fun e => NormedSpace.exp (s • ξ e) * ξ e * x e) s :=
  hasDerivAt_amb fun e => (hasDerivAt_exp_smul_const (ξ e) s).mul_const (x e)

theorem expCurve_d2 (ξ x : Amb ι) (s : ℝ) : HasDerivAt
    (fun s => (WithLp.toLp 2 fun e => NormedSpace.exp (s • ξ e) * ξ e * x e : Amb ι))
    (WithLp.toLp 2 fun e => NormedSpace.exp (s • ξ e) * ξ e * ξ e * x e) s :=
  hasDerivAt_amb fun e => ((hasDerivAt_exp_smul_const (ξ e) s).mul_const (ξ e)).mul_const (x e)

theorem hess_eq (hS : ContDiff ℝ 2 S) (x ξ : Amb ι) :
    hess S x ξ = ⟪fderiv ℝ (gradient S) x (lmul ξ x), lmul ξ x⟫ + ⟪gradient S x, lmul ξ (lmul ξ x)⟫ := by
  have hW := contDiff_gradient hS
  have hd : deriv (fun s => S (expCurve ξ x s)) = fun s => ⟪gradient S (expCurve ξ x s),
      (WithLp.toLp 2 fun e => NormedSpace.exp (s • ξ e) * ξ e * x e : Amb ι)⟫ :=
    funext fun s => (hasDerivAt_comp_S hS (expCurve_d1 ξ x s)).deriv
  have hWd : HasFDerivAt (gradient S) (fderiv ℝ (gradient S) (expCurve ξ x 0)) (expCurve ξ x 0) :=
    (hW.differentiable (by norm_num) _).hasFDerivAt
  have hc := hWd.comp_hasDerivAt (0 : ℝ) (expCurve_d1 ξ x 0)
  have hi := HasDerivAt.inner ℝ hc (expCurve_d2 ξ x 0)
  unfold hess
  rw [hd]
  have e1 : (WithLp.toLp 2 fun e => NormedSpace.exp ((0 : ℝ) • ξ e) * ξ e * x e : Amb ι) = lmul ξ x := by
    refine PiLp.ext fun e => ?_
    simp [lmul]
  have e2 : (WithLp.toLp 2 fun e => NormedSpace.exp ((0 : ℝ) • ξ e) * ξ e * ξ e * x e : Amb ι) =
      lmul ξ (lmul ξ x) := by
    refine PiLp.ext fun e => ?_
    simp [lmul, mul_assoc]
  have hi' := hi.deriv
  rw [e1, e2] at hi'
  simp only [Function.comp_apply, expCurve_zero] at hi'
  rw [add_comm]
  exact hi'

/-- The frame rotation carrying `x` along the flow: `field = rot · x`. -/
def rot (S : Amb ι → ℝ) (x : Amb ι) : Amb ι := WithLp.toLp 2 fun e => field S x e * star (x e)

theorem rot_apply (x : Amb ι) (e : ι) : rot S x e = field S x e * star (x e) := rfl

theorem star_eq_neg_of_re {q : ℍ[ℝ]} (h : q.re = 0) : star q = -q := by
  ext <;> simp [h]

theorem rot_star (x : Amb ι) (e : ι) : star (rot S x e) = -rot S x e := by
  apply star_eq_neg_of_re
  have := inner_field S x e
  rwa [Quaternion.inner_def] at this

theorem lmul_rot {x : Amb ι} (hx : Sph x) : lmul (rot S x) x = field S x := by
  refine PiLp.ext fun e => ?_
  simp only [lmul_apply, rot_apply]
  rw [mul_assoc, star_mul_unit (hx e), mul_one]

theorem norm_rot {x : Amb ι} (hx : Sph x) (e : ι) : ‖rot S x e‖ = ‖field S x e‖ := by
  rw [rot_apply, norm_mul, norm_star, hx e, mul_one]

theorem mul_self_of_skew {q : ℍ[ℝ]} (h : star q = -q) : q * q = -((‖q‖ ^ 2 : ℝ) : ℍ[ℝ]) := by
  have := Quaternion.self_mul_star q
  rw [h, Quaternion.normSq_eq_norm_mul_self, mul_neg] at this
  rw [sq, ← this, neg_neg]

theorem hess_rot (hS : ContDiff ℝ 2 S) {x : Amb ι} (hx : Sph x) :
    hess S x (rot S x) = ⟪fderiv ℝ (gradient S) x (field S x), field S x⟫ -
      ∑ e, ⟪gradient S x e, x e⟫ * ‖field S x e‖ ^ 2 := by
  rw [hess_eq hS, lmul_rot hx, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  rw [inner_amb]
  refine Finset.sum_congr rfl fun e _ => ?_
  have he : field S x e = rot S x e * x e := by rw [← lmul_apply, lmul_rot hx]
  have h1 : rot S x e * field S x e = (rot S x e * rot S x e) * x e := by rw [mul_assoc, ← he]
  rw [lmul_apply, h1, mul_self_of_skew (rot_star x e), norm_rot hx, neg_mul, inner_neg_right]
  congr 1
  rw [Quaternion.coe_mul_eq_smul, real_inner_smul_right]
  ring

/-- **Bochner identity along the flow.** The squared force changes at minus twice the Hessian in the
direction of the force. -/
theorem hasDerivAt_force (hS : ContDiff ℝ 2 S) {γ : ℝ → Amb ι} (h : IsLine S γ) {t₀ : ℝ}
    (h0 : Sph (γ t₀)) (t : ℝ) :
    HasDerivAt (fun s => ‖field S (γ s)‖ ^ 2) (-2 * hess S (γ t) (rot S (γ t))) t := by
  have hs (s : ℝ) := h.sph h0 s
  have hW := contDiff_gradient hS
  have hWd : HasFDerivAt (gradient S) (fderiv ℝ (gradient S) (γ t)) (γ t) :=
    (hW.differentiable (by norm_num) _).hasFDerivAt
  have hc := hWd.comp_hasDerivAt t (h t)
  set d : Amb ι := fderiv ℝ (gradient S) (γ t) (field S (γ t)) with hd
  have hfun : (fun s => ‖field S (γ s)‖ ^ 2) =
      fun s => ∑ e, (‖gradient S (γ s) e‖ ^ 2 - ⟪gradient S (γ s) e, γ s e⟫ ^ 2) := by
    funext s
    rw [norm_sq_amb]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [field_apply, norm_neg, norm_tang_sq _ (hs s e)]
  rw [hfun]
  have hterm (e : ι) : HasDerivAt
      (fun s => ‖gradient S (γ s) e‖ ^ 2 - ⟪gradient S (γ s) e, γ s e⟫ ^ 2)
      (2 * ⟪gradient S (γ t) e, d e⟫ - 2 * ⟪gradient S (γ t) e, γ t e⟫ *
        (⟪gradient S (γ t) e, field S (γ t) e⟫ + ⟪d e, γ t e⟫)) t := by
    have h1 : HasDerivAt (fun s => gradient S (γ s) e) (d e) t := hasDerivAt_coord hc e
    have h2 := hasDerivAt_coord (h t) e
    have := (h1.norm_sq).sub ((HasDerivAt.inner ℝ h1 h2).pow 2)
    convert this using 1
    simp
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun e (_ : e ∈ Finset.univ) => hterm e
  convert hsum using 1
  rw [hess_rot hS (hs t), inner_amb, mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hu := hs t e
  have hV : gradient S (γ t) e = -field S (γ t) e + ⟪gradient S (γ t) e, γ t e⟫ • γ t e := by
    rw [field_apply, neg_neg, tang_unit _ hu]
    abel
  have hVV : ⟪gradient S (γ t) e, field S (γ t) e⟫ = -‖field S (γ t) e‖ ^ 2 := by
    rw [field_apply, inner_neg_right, inner_tang_self _ hu, norm_neg]
  have hdw : ⟪gradient S (γ t) e, d e⟫ = -⟪d e, field S (γ t) e⟫ +
      ⟪gradient S (γ t) e, γ t e⟫ * ⟪d e, γ t e⟫ := by
    conv_lhs => rw [hV]
    rw [inner_add_left, inner_neg_left, real_inner_smul_left, real_inner_comm (d e),
      real_inner_comm (d e)]
  rw [hVV, hdw]
  ring


/-! ### From a Hessian floor to smoothing -/

/-- The scalar core: with `E' = -D`, `D' = -2h` and `h ≥ -Λ D` on `[0, t]`, the rate `D` grows at most
exponentially, and `D t ≤ (1/t + 2Λ)(E 0 - E t)`. -/
theorem ode_core {E D h : ℝ → ℝ} {t Λ : ℝ} (ht : 0 < t) (hΛ : 0 < Λ)
    (hE : ∀ s, HasDerivAt E (-D s) s) (hD : ∀ s, HasDerivAt D (-2 * h s) s) (hD0 : 0 ≤ D t)
    (hh : ∀ s ∈ Icc 0 t, -Λ * D s ≤ h s) :
    (∀ s ∈ Icc 0 t, D t ≤ Real.exp (2 * Λ * (t - s)) * D s) ∧ D t ≤ (1 / t + 2 * Λ) * (E 0 - E t) := by
  have hgrow : ∀ s ∈ Icc 0 t, D t ≤ Real.exp (2 * Λ * (t - s)) * D s := by
    let g : ℝ → ℝ := fun s => Real.exp (-(2 * Λ) * s) * D s
    have hg (s : ℝ) : HasDerivAt g (Real.exp (-(2 * Λ) * s) * (-(2 * Λ)) * D s +
        Real.exp (-(2 * Λ) * s) * (-2 * h s)) s := by
      have h1 : HasDerivAt (fun s => Real.exp (-(2 * Λ) * s)) (Real.exp (-(2 * Λ) * s) * (-(2 * Λ))) s := by
        simpa using ((hasDerivAt_id s).const_mul (-(2 * Λ))).exp
      exact h1.mul (hD s)
    have hanti : AntitoneOn g (Icc 0 t) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 t)
        (HasDerivAt.continuousOn fun s _ => hg s) (fun s _ => (hg s).differentiableAt.differentiableWithinAt)
        fun s hs => ?_
      rw [(hg s).deriv]
      have hs' := hh s (interior_subset hs)
      have hp := Real.exp_pos (-(2 * Λ) * s)
      have : Real.exp (-(2 * Λ) * s) * (-(2 * Λ)) * D s + Real.exp (-(2 * Λ) * s) * (-2 * h s) =
          Real.exp (-(2 * Λ) * s) * (-(2 * Λ * D s) - 2 * h s) := by ring
      rw [this]
      exact mul_nonpos_of_nonneg_of_nonpos hp.le (by nlinarith only [hs'])
    intro s hs
    have hle := hanti hs (right_mem_Icc.2 ht.le) hs.2
    simp only [g] at hle
    have e : Real.exp (2 * Λ * (t - s)) * Real.exp (-(2 * Λ) * t) = Real.exp (-(2 * Λ) * s) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hp := Real.exp_pos (-(2 * Λ) * t)
    have hp' := Real.exp_pos (2 * Λ * (t - s))
    have hm := mul_le_mul_of_nonneg_left hle hp'.le
    have e1 : Real.exp (2 * Λ * (t - s)) * (Real.exp (-(2 * Λ) * t) * D t) = D t * Real.exp (-(2 * Λ) * s) := by
      rw [← mul_assoc, e]
      ring
    have e2 : Real.exp (2 * Λ * (t - s)) * (Real.exp (-(2 * Λ) * s) * D s) =
        (Real.exp (2 * Λ * (t - s)) * D s) * Real.exp (-(2 * Λ) * s) := by ring
    rw [e1, e2] at hm
    exact le_of_mul_le_mul_right hm (Real.exp_pos _)
  refine ⟨hgrow, ?_⟩
  -- The comparison function.
  let c : ℝ := D t / (2 * Λ)
  let G : ℝ → ℝ := fun s => E s + c * Real.exp (-(2 * Λ) * (t - s))
  have hG (s : ℝ) : HasDerivAt G (-D s + c * (Real.exp (-(2 * Λ) * (t - s)) * (2 * Λ))) s := by
    have h1 : HasDerivAt (fun s => Real.exp (-(2 * Λ) * (t - s)))
        (Real.exp (-(2 * Λ) * (t - s)) * (2 * Λ)) s := by
      have : HasDerivAt (fun s => -(2 * Λ) * (t - s)) (2 * Λ) s := by
        simpa using ((hasDerivAt_id s).const_sub t).const_mul (-(2 * Λ))
      exact this.exp
    exact (hE s).add (h1.const_mul c)
  have hanti : AntitoneOn G (Icc 0 t) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 t)
      (HasDerivAt.continuousOn fun s _ => hG s) (fun s _ => (hG s).differentiableAt.differentiableWithinAt)
      fun s hs => ?_
    rw [(hG s).deriv]
    have hs' := hgrow s (interior_subset hs)
    have hc : c * (Real.exp (-(2 * Λ) * (t - s)) * (2 * Λ)) = D t * Real.exp (-(2 * Λ) * (t - s)) := by
      simp only [c]
      field_simp
    rw [hc]
    have hp := Real.exp_pos (-(2 * Λ) * (t - s))
    have hm := mul_le_mul_of_nonneg_right hs' hp.le
    have e : Real.exp (2 * Λ * (t - s)) * D s * Real.exp (-(2 * Λ) * (t - s)) = D s := by
      have : Real.exp (2 * Λ * (t - s)) * Real.exp (-(2 * Λ) * (t - s)) = 1 := by
        rw [← Real.exp_add]
        simp
      calc _ = (Real.exp (2 * Λ * (t - s)) * Real.exp (-(2 * Λ) * (t - s))) * D s := by ring
        _ = D s := by rw [this, one_mul]
    rw [e] at hm
    linarith only [hm]
  have hle := hanti (left_mem_Icc.2 ht.le) (right_mem_Icc.2 ht.le) ht.le
  simp only [G, sub_self, mul_zero, Real.exp_zero, mul_one, sub_zero] at hle
  set u : ℝ := 2 * Λ * t with hu
  have hu0 : 0 < u := by positivity
  have he : Real.exp (-(2 * Λ) * t) = Real.exp (-u) := by
    congr 1
    rw [hu]
    ring
  rw [he] at hle
  -- `(1 + u) e^{-u} ≤ 1`.
  have hexp : (1 + u) * Real.exp (-u) ≤ 1 := by
    have h1 := Real.add_one_le_exp u
    have hp := Real.exp_pos (-u)
    have : Real.exp u * Real.exp (-u) = 1 := by
      rw [← Real.exp_add]
      simp
    nlinarith only [h1, hp, this]
  have hcdef : c * (2 * Λ) = D t := by
    simp only [c]
    field_simp
  have hc0 : 0 ≤ c := by positivity
  have hgap : c * (1 - Real.exp (-u)) ≤ E 0 - E t := by linarith only [hle]
  have hfac : 1 / t + 2 * Λ = (1 + u) / t := by
    rw [hu]
    field_simp
  rw [hfac]
  have hmain : D t * t ≤ (1 + u) * (E 0 - E t) := by
    have h1 : (1 + u) * (c * (1 - Real.exp (-u))) ≤ (1 + u) * (E 0 - E t) :=
      mul_le_mul_of_nonneg_left hgap (by positivity)
    have h2 : D t * t = c * u := by
      rw [hu, ← hcdef]
      ring
    have h3 : c * u ≤ (1 + u) * (c * (1 - Real.exp (-u))) := by
      have : u ≤ (1 + u) * (1 - Real.exp (-u)) := by nlinarith only [hexp]
      nlinarith only [mul_le_mul_of_nonneg_left this hc0]
    linarith only [h1, h2, h3]
  rw [div_mul_eq_mul_div, le_div_iff₀ ht]
  exact hmain

/-- **Smoothing, from a Hessian floor on the sublevel set.** -/
theorem smoothing (hS : ContDiff ℝ 2 S) {γ : ℝ → Amb ι} (h : IsLine S γ) (h0 : Sph (γ 0)) {t Λ : ℝ}
    (ht : 0 < t) (hΛ : 0 < Λ)
    (hfloor : ∀ x, Sph x → S x ≤ S (γ 0) → ∀ ξ : Amb ι, (∀ e, star (ξ e) = -ξ e) →
      -Λ * ‖ξ‖ ^ 2 ≤ hess S x ξ) :
    (∀ s ∈ Icc 0 t, ‖field S (γ t)‖ ^ 2 ≤ Real.exp (2 * Λ * (t - s)) * ‖field S (γ s)‖ ^ 2) ∧
      ‖field S (γ t)‖ ^ 2 ≤ (1 / t + 2 * Λ) * (S (γ 0) - S (γ t)) := by
  refine ode_core (E := fun s => S (γ s)) (D := fun s => ‖field S (γ s)‖ ^ 2)
    (h := fun s => hess S (γ s) (rot S (γ s))) ht hΛ (hasDerivAt_energy hS h h0)
    (hasDerivAt_force hS h h0) (by positivity) fun s hs => ?_
  have hx := h.sph h0 s
  have := hfloor (γ s) hx (energy_antitone hS h h0 hs.1) (rot S (γ s)) (rot_star _)
  have hn : ‖rot S (γ s)‖ ^ 2 = ‖field S (γ s)‖ ^ 2 := by
    rw [norm_sq_amb, norm_sq_amb]
    exact Finset.sum_congr rfl fun e _ => by rw [norm_rot hx]
  rwa [hn] at this

/-! ### Covariance -/

/-- Multiplication by unit quaternions on the two sides, as a linear isometry of `ℍ`. -/
def mulIso (a b : Q) : ℍ[ℝ] ≃ₗᵢ[ℝ] ℍ[ℝ] where
  toFun q := (a : ℍ[ℝ]) * q * b
  invFun q := star (a : ℍ[ℝ]) * q * star (b : ℍ[ℝ])
  map_add' x y := by rw [mul_add, add_mul]
  map_smul' c x := by simp
  left_inv x := by
    have h1 : star (a : ℍ[ℝ]) * a = 1 := Unitary.star_mul_self_of_mem a.2
    have h2 : (b : ℍ[ℝ]) * star (b : ℍ[ℝ]) = 1 := Unitary.mul_star_self_of_mem b.2
    calc star (a : ℍ[ℝ]) * ((a : ℍ[ℝ]) * x * b) * star (b : ℍ[ℝ])
        = (star (a : ℍ[ℝ]) * a) * x * ((b : ℍ[ℝ]) * star (b : ℍ[ℝ])) := by
          simp only [mul_assoc]
      _ = x := by rw [h1, h2, one_mul, mul_one]
  right_inv x := by
    have h1 : (a : ℍ[ℝ]) * star (a : ℍ[ℝ]) = 1 := Unitary.mul_star_self_of_mem a.2
    have h2 : star (b : ℍ[ℝ]) * b = 1 := Unitary.star_mul_self_of_mem b.2
    calc (a : ℍ[ℝ]) * (star (a : ℍ[ℝ]) * x * star (b : ℍ[ℝ])) * b
        = ((a : ℍ[ℝ]) * star (a : ℍ[ℝ])) * x * (star (b : ℍ[ℝ]) * b) := by
          simp only [mul_assoc]
      _ = x := by rw [h1, h2, one_mul, mul_one]
  norm_map' x := by
    change ‖(a : ℍ[ℝ]) * x * b‖ = ‖x‖
    rw [norm_mul, norm_mul, unit_norm, unit_norm, one_mul, mul_one]

/-- The induced isometry of the ambient space. -/
def ambIso (a b : ι → Q) : Amb ι ≃ₗᵢ[ℝ] Amb ι :=
  LinearIsometryEquiv.piLpCongrRight 2 fun e => mulIso (a e) (b e)

theorem ambIso_apply (a b : ι → Q) (x : Amb ι) (e : ι) :
    ambIso a b x e = (a e : ℍ[ℝ]) * x e * b e := rfl

/-- The action of `(a, b)` on unit configurations. -/
def actQ (a b : ι → Q) (U : ι → Q) : ι → Q := fun e => a e * U e * b e

theorem emb_actQ (a b U : ι → Q) : emb (actQ a b U) = ambIso a b (emb U) := rfl

theorem gradient_ambIso (hS : ContDiff ℝ 2 S) (a b : ι → Q) (hinv : ∀ x, S (ambIso a b x) = S x)
    (x : Amb ι) : gradient S (ambIso a b x) = ambIso a b (gradient S x) := by
  set T := ambIso a b
  have hdiff (y : Amb ι) : DifferentiableAt ℝ S y := hS.differentiable (by norm_num) y
  have hcomp : HasFDerivAt (S ∘ T) ((fderiv ℝ S (T x)).comp (T.toContinuousLinearEquiv : Amb ι →L[ℝ] Amb ι)) x :=
    (hdiff (T x)).hasFDerivAt.comp x T.toContinuousLinearEquiv.hasFDerivAt
  have hS' : S ∘ T = S := funext hinv
  rw [hS'] at hcomp
  have heq := hcomp.unique (hdiff x).hasFDerivAt
  refine ext_inner_right ℝ fun y => ?_
  obtain ⟨z, rfl⟩ := T.surjective y
  have h1 : ⟪gradient S (T x), T z⟫ = fderiv ℝ S (T x) (T z) := by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  have h2 : ⟪T (gradient S x), T z⟫ = fderiv ℝ S x z := by
    rw [LinearIsometryEquiv.inner_map_map]
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  rw [h1, h2]
  exact congrArg (fun L : Amb ι →L[ℝ] ℝ => L z) heq

theorem field_ambIso (hS : ContDiff ℝ 2 S) (a b : ι → Q) (hinv : ∀ x, S (ambIso a b x) = S x)
    (x : Amb ι) : field S (ambIso a b x) = ambIso a b (field S x) := by
  refine PiLp.ext fun e => ?_
  rw [field_apply, gradient_ambIso hS a b hinv]
  change -tang (mulIso (a e) (b e) (gradient S x e)) (mulIso (a e) (b e) (x e)) =
    mulIso (a e) (b e) (-tang (gradient S x e) (x e))
  simp only [tang, map_neg, map_sub, map_smul, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.inner_map_map]

/-- **Covariance.** The flow commutes with every two-sided unit multiplication preserving `S`. This
covers both gauge transformations and center flips. -/
theorem wflow_actQ (hS : ContDiff ℝ 2 S) (a b : ι → Q) (hinv : ∀ x, S (ambIso a b x) = S x)
    (t : ℝ) (U : ι → Q) : wflow hS t (actQ a b U) = actQ a b (wflow hS t U) := by
  apply emb_injective
  have hl : IsLine S fun s => ambIso a b (emb (wflow hS s U)) := fun s => by
    rw [field_ambIso hS a b hinv]
    exact (ambIso a b).toContinuousLinearEquiv.hasFDerivAt.comp_hasDerivAt s (wflow_isLine hS U s)
  have h := wflow_unique hS (actQ a b U) hl (by rw [wflow_zero, emb_actQ])
  exact (congrFun h t).symm

/-! ### The field depends only on the restriction of `S` to the sphere -/

theorem expCurve_d0 (ξ x : Amb ι) : HasDerivAt (expCurve ξ x) (lmul ξ x) 0 := by
  have h := expCurve_d1 ξ x 0
  have e : (WithLp.toLp 2 fun e => NormedSpace.exp ((0 : ℝ) • ξ e) * ξ e * x e : Amb ι) = lmul ξ x := by
    refine PiLp.ext fun e => ?_
    simp [lmul]
  rwa [e] at h

theorem re_of_star {q : ℍ[ℝ]} (h : star q = -q) : q.re = 0 := by
  have := congrArg QuaternionAlgebra.re h
  simp only [Quaternion.re_star, Quaternion.re_neg] at this
  linarith only [this]

theorem inner_lmul_eq {w x ξ : ℍ[ℝ]} (hx : ‖x‖ = 1) (hξ : star ξ = -ξ) :
    ⟪w, ξ * x⟫ = -⟪(-tang w x) * star x, ξ⟫ := by
  have h1 : ⟪(-tang w x) * star x, ξ⟫ = ⟪-tang w x, ξ * x⟫ := by
    simp only [Quaternion.inner_def, star_mul, mul_assoc]
  have h2 : ⟪x, ξ * x⟫ = 0 := by
    rw [Quaternion.inner_def, star_mul, ← mul_assoc, mul_star_unit hx, one_mul, hξ]
    have := re_of_star hξ
    simp [this]
  rw [h1, inner_neg_left, neg_neg, tang_unit w hx, inner_sub_left, real_inner_smul_left, h2]
  ring

/-- The force is the gradient: the rate of `S` along any rotation `ξ` is `-⟪rot, ξ⟫`. -/
theorem inner_grad_lmul {x ξ : Amb ι} (hx : Sph x) (hξ : ∀ e, star (ξ e) = -ξ e) :
    ⟪gradient S x, lmul ξ x⟫ = -⟪rot S x, ξ⟫ := by
  rw [inner_amb, inner_amb, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun e _ => inner_lmul_eq (hx e) (hξ e)

theorem norm_exp_skew {ξ : ℍ[ℝ]} (hξ : star ξ = -ξ) (s : ℝ) : ‖NormedSpace.exp (s • ξ)‖ = 1 := by
  letI : NormedAlgebra ℚ ℍ[ℝ] := NormedAlgebra.restrictScalars ℚ ℝ ℍ[ℝ]
  have hs : star (s • ξ) = -(s • ξ) := by rw [Quaternion.star_smul, hξ, smul_neg]
  exact unit_norm ⟨NormedSpace.exp (s • ξ), NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (x := s • ξ) hs⟩

theorem expCurve_sph {x ξ : Amb ι} (hx : Sph x) (hξ : ∀ e, star (ξ e) = -ξ e) (s : ℝ) :
    Sph (expCurve ξ x s) := fun e => by
  change ‖NormedSpace.exp (s • ξ e) * x e‖ = 1
  rw [norm_mul, norm_exp_skew (hξ e), hx e, one_mul]

/-- The field depends only on the restriction of `S` to the unit configurations. -/
theorem field_congr {S₁ S₂ : Amb ι → ℝ} (h₁ : ContDiff ℝ 2 S₁) (h₂ : ContDiff ℝ 2 S₂)
    (h : ∀ x, Sph x → S₁ x = S₂ x) {x : Amb ι} (hx : Sph x) : field S₁ x = field S₂ x := by
  set ξ : Amb ι := rot S₁ x - rot S₂ x with hξdef
  have hξ (e : ι) : star (ξ e) = -ξ e := by
    have e1 : ξ e = rot S₁ x e - rot S₂ x e := rfl
    rw [e1, star_sub, rot_star, rot_star]
    abel
  have hfun : (fun s => S₁ (expCurve ξ x s)) = fun s => S₂ (expCurve ξ x s) :=
    funext fun s => h _ (expCurve_sph hx hξ s)
  have d₁ := hasDerivAt_comp_S h₁ (expCurve_d0 ξ x)
  have d₂ := hasDerivAt_comp_S h₂ (expCurve_d0 ξ x)
  rw [hfun] at d₁
  have heq := d₁.unique d₂
  rw [expCurve_zero, inner_grad_lmul hx hξ, inner_grad_lmul hx hξ] at heq
  have hz : ⟪ξ, ξ⟫ = 0 := by
    conv_lhs => lhs; rw [hξdef]
    rw [inner_sub_left]
    linarith only [heq]
  have h0 : ξ = 0 := inner_self_eq_zero.1 hz
  have hrot : rot S₁ x = rot S₂ x := sub_eq_zero.1 h0
  rw [← lmul_rot (S := S₁) hx, ← lmul_rot (S := S₂) hx, hrot]

/-! ### Covariance under permutations of the links -/

/-- A permutation of the links followed by an isometry on each link. -/
def permIso (σ : ι ≃ ι) (A : ι → ℍ[ℝ] ≃ₗᵢ[ℝ] ℍ[ℝ]) : Amb ι ≃ₗᵢ[ℝ] Amb ι :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℍ[ℝ] σ.symm).trans (LinearIsometryEquiv.piLpCongrRight 2 A)

theorem permIso_apply (σ : ι ≃ ι) (A : ι → ℍ[ℝ] ≃ₗᵢ[ℝ] ℍ[ℝ]) (x : Amb ι) (e : ι) :
    permIso σ A x e = A e (x (σ e)) := by
  simp [permIso]

theorem gradient_comp_iso (hS : ContDiff ℝ 2 S) (T : Amb ι ≃ₗᵢ[ℝ] Amb ι) (x : Amb ι) :
    T (gradient (S ∘ T) x) = gradient S (T x) := by
  have hdiff (y : Amb ι) : DifferentiableAt ℝ S y := hS.differentiable (by norm_num) y
  have hcomp : HasFDerivAt (S ∘ T) ((fderiv ℝ S (T x)).comp (T.toContinuousLinearEquiv : Amb ι →L[ℝ] Amb ι)) x :=
    (hdiff (T x)).hasFDerivAt.comp x T.toContinuousLinearEquiv.hasFDerivAt
  refine ext_inner_right ℝ fun y => ?_
  obtain ⟨z, rfl⟩ := T.surjective y
  rw [LinearIsometryEquiv.inner_map_map]
  have h1 : ⟪gradient S (T x), T z⟫ = fderiv ℝ S (T x) (T z) := by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  have h2 : ⟪gradient (S ∘ T) x, z⟫ = fderiv ℝ (S ∘ T) x z := by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  rw [h1, h2, hcomp.fderiv]
  rfl

theorem tang_iso (A : ℍ[ℝ] ≃ₗᵢ[ℝ] ℍ[ℝ]) (w x : ℍ[ℝ]) : tang (A w) (A x) = A (tang w x) := by
  simp only [tang, map_sub, map_smul, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.inner_map_map]

theorem field_permIso (hS : ContDiff ℝ 2 S) (σ : ι ≃ ι) (A : ι → ℍ[ℝ] ≃ₗᵢ[ℝ] ℍ[ℝ]) (x : Amb ι) :
    field S (permIso σ A x) = permIso σ A (field (S ∘ permIso σ A) x) := by
  refine PiLp.ext fun e => ?_
  rw [permIso_apply, field_apply, field_apply, ← gradient_comp_iso hS, permIso_apply, permIso_apply, tang_iso,
    map_neg]

theorem Sph.permIso {x : Amb ι} (hx : Sph x) (σ : ι ≃ ι) (A : ι → ℍ[ℝ] ≃ₗᵢ[ℝ] ℍ[ℝ]) :
    Sph (TwistedFlow.permIso σ A x) := fun e => by
  rw [permIso_apply, LinearIsometryEquiv.norm_map, hx]

/-- **Covariance under a symmetry permuting the links.** If `T = permIso σ A` preserves `S` on the unit
configurations, the field is equivariant at unit configurations and the flow commutes with `T`. -/
theorem field_symm (hS : ContDiff ℝ 2 S) (σ : ι ≃ ι) (A : ι → ℍ[ℝ] ≃ₗᵢ[ℝ] ℍ[ℝ])
    (hinv : ∀ x, Sph x → S (TwistedFlow.permIso σ A x) = S x) {x : Amb ι} (hx : Sph x) :
    field S (TwistedFlow.permIso σ A x) = TwistedFlow.permIso σ A (field S x) := by
  have hc : ContDiff ℝ 2 (S ∘ TwistedFlow.permIso σ A) :=
    hS.comp (TwistedFlow.permIso σ A).toContinuousLinearEquiv.contDiff
  rw [field_permIso hS, field_congr hc hS (fun y hy => hinv y hy) hx]

theorem wflow_symm (hS : ContDiff ℝ 2 S) (σ : ι ≃ ι) (A : ι → ℍ[ℝ] ≃ₗᵢ[ℝ] ℍ[ℝ])
    (hinv : ∀ x, Sph x → S (TwistedFlow.permIso σ A x) = S x) (t : ℝ) (U V : ι → Q)
    (hV : emb V = TwistedFlow.permIso σ A (emb U)) :
    emb (wflow hS t V) = TwistedFlow.permIso σ A (emb (wflow hS t U)) := by
  have hl : IsLine S fun s => TwistedFlow.permIso σ A (emb (wflow hS s U)) := fun s => by
    rw [field_symm hS σ A hinv (emb_sph _)]
    exact (TwistedFlow.permIso σ A).toContinuousLinearEquiv.hasFDerivAt.comp_hasDerivAt s (wflow_isLine hS U s)
  have h := wflow_unique hS V hl (by rw [wflow_zero, hV])
  exact (congrFun h t).symm

end Abstract

open PeriodicLattice4 TwistedFlat CommutingShifts TwistedHessian TwistedActionJet TwistedSmallField
open TwistedStability TwistedLandau TwistedLocalization TwistedReflection TwistedHessianField TwistedIBP
open TwistedCovariant
open PeriodicPlaquetteReflection PeriodicTimeReflection RegulatedGauge

/-! ### The twisted action on the ambient space -/

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

/-- The forward edge at `x` in direction `μ`. -/
def ed (x : V') (μ : Fin 4) : Edge V' := ⟨x, step (2 * n) x μ, forward (2 * n) x μ⟩

theorem ed_coords (e : Edge V') :
    ed n (edgeCoordinates (2 * n) e).1 (edgeCoordinates (2 * n) e).2 = e :=
  (edgeCoordinates (2 * n)).left_inv e

theorem sum_edges (g : Edge V' → ℝ) : ∑ e, g e = ∑ μ, ∑ x, g (ed n x μ) := by
  rw [← (edgeCoordinates (2 * n)).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- The plaquette as a polynomial on the ambient space. -/
def plaqA (y : Amb (Edge V')) (p : PlaquetteIndex (2 * n)) : ℍ[ℝ] :=
  y (ed n p.1 p.2.1.1) * y (ed n (step (2 * n) p.1 p.2.1.1) p.2.1.2) *
    star (y (ed n (step (2 * n) p.1 p.2.1.2) p.2.1.1)) * star (y (ed n p.1 p.2.1.2))

def termA (p : PlaquetteIndex (2 * n)) (y : Amb (Edge V')) : ℝ :=
  2 - spatialTwist n p * (2 * (plaqA n y p).re)

/-- The unit-coupling twisted action, extended as a polynomial. -/
def actA (y : Amb (Edge V')) : ℝ := ∑ p, termA n p y

theorem contDiff_termA (p : PlaquetteIndex (2 * n)) : ContDiff ℝ 2 (termA n p) := by
  have hl (e : Edge V') : ContDiff ℝ 2 fun y : Amb (Edge V') => y e :=
    contDiff_piLp_apply (p := 2) (i := e)
  have hs (e : Edge V') : ContDiff ℝ 2 fun y : Amb (Edge V') => star (y e) := by
    have h : (fun y : Amb (Edge V') => star (y e)) = fun y => (2 * (y e).re) • (1 : ℍ[ℝ]) - y e := by
      funext y
      ext <;> simp
      ring
    rw [h]
    exact ((contDiff_const.mul (reCLM.contDiff.comp (hl e))).smul contDiff_const).sub (hl e)
  have hP : ContDiff ℝ 2 fun y => plaqA n y p :=
    (((hl _).mul (hl _)).mul (hs _)).mul (hs _)
  have hre : ContDiff ℝ 2 fun y => (plaqA n y p).re := reCLM.contDiff.comp hP
  exact contDiff_const.sub (contDiff_const.mul (contDiff_const.mul hre))

theorem contDiff_actA : ContDiff ℝ 2 (actA n) :=
  ContDiff.sum fun p _ => contDiff_termA n p

theorem termA_emb (U : Configuration V' Q) (p : PlaquetteIndex (2 * n)) :
    termA n p (emb U) = term n Q (spatialTwist n) character 2 U p := by
  unfold termA term
  rw [character_re]
  rfl

theorem actA_emb (U : Configuration V' Q) : actA n (emb U) = actionOne n U := by
  unfold actA actionOne action
  rw [one_mul]
  exact Finset.sum_congr rfl fun p _ => termA_emb n U p

/-- **The Wilson flow of the twisted action**, at unit coupling. -/
def wf (t : ℝ) (U : Configuration V' Q) : Configuration V' Q := wflow (contDiff_actA n) t U

/-- The squared force at a configuration. -/
def forceSq (U : Configuration V' Q) : ℝ := ‖field (actA n) (emb U)‖ ^ 2

theorem wf_isLine (U : Configuration V' Q) : IsLine (actA n) fun t => emb (wf n t U) :=
  wflow_isLine _ U

theorem wf_sph (U : Configuration V' Q) (t : ℝ) : Sph (emb (wf n t U)) := emb_sph _

theorem wf_zero (U : Configuration V' Q) : wf n 0 U = U := wflow_zero _ U

theorem wf_add (s t : ℝ) (U : Configuration V' Q) : wf n s (wf n t U) = wf n (s + t) U :=
  wflow_add _ s t U

/-- Uniqueness of the flow. -/
theorem wf_unique (U : Configuration V' Q) {γ : ℝ → Configuration V' Q}
    (hγ : IsLine (actA n) fun t => emb (γ t)) (h0 : γ 0 = U) : γ = fun t => wf n t U := by
  funext t
  have h := wflow_unique (contDiff_actA n) U hγ (by rw [h0])
  exact emb_injective (congrFun h t)

theorem continuous_wf : Continuous fun p : ℝ × Configuration V' Q => wf n p.1 p.2 :=
  continuous_wflow _

/-- The action decreases along the flow. -/
theorem action_wf_antitone (U : Configuration V' Q) : Antitone fun t => actionOne n (wf n t U) := by
  have := energy_antitone (contDiff_actA n) (wf_isLine n U) (t₀ := 0) (wf_sph n U 0)
  simpa only [actA_emb] using this

theorem hasDerivAt_action_wf (U : Configuration V' Q) (t : ℝ) :
    HasDerivAt (fun s => actionOne n (wf n s U)) (-forceSq n (wf n t U)) t := by
  have := hasDerivAt_energy (contDiff_actA n) (wf_isLine n U) (t₀ := 0) (wf_sph n U 0) t
  simpa only [actA_emb] using this

theorem continuous_forceSq : Continuous (forceSq n) :=
  (((contDiff_field (contDiff_actA n)).continuous.comp continuous_emb).norm).pow 2

/-- **The energy identity.** -/
theorem energy_wf (U : Configuration V' Q) (t : ℝ) :
    actionOne n U - actionOne n (wf n t U) = ∫ s in (0 : ℝ)..t, forceSq n (wf n s U) := by
  have := energy_identity (contDiff_actA n) (wf_isLine n U) (t₀ := 0) (wf_sph n U 0) 0 t
  simpa only [actA_emb, wf_zero] using this

/-! ### Covariance -/

theorem re_conj_comm (g : Q) (P : ℍ[ℝ]) : ((g : ℍ[ℝ]) * P * star (g : ℍ[ℝ])).re = P.re := by
  rw [re_comm, ← mul_assoc, Unitary.star_mul_self_of_mem g.2, one_mul]

theorem gauge_four (g₁ g₂ g₃ g₄ : Q) (y₁ y₂ y₃ y₄ : ℍ[ℝ]) :
    ((g₁ : ℍ[ℝ]) * y₁ * ((g₂⁻¹ : Q) : ℍ[ℝ])) * ((g₂ : ℍ[ℝ]) * y₂ * ((g₃⁻¹ : Q) : ℍ[ℝ])) *
        star ((g₄ : ℍ[ℝ]) * y₃ * ((g₃⁻¹ : Q) : ℍ[ℝ])) * star ((g₁ : ℍ[ℝ]) * y₄ * ((g₄⁻¹ : Q) : ℍ[ℝ])) =
      (g₁ : ℍ[ℝ]) * (y₁ * y₂ * star y₃ * star y₄) * star (g₁ : ℍ[ℝ]) := by
  have hinv (g : Q) : ((g⁻¹ : Q) : ℍ[ℝ]) = star (g : ℍ[ℝ]) := rfl
  have c₁ (g : Q) (z : ℍ[ℝ]) : star (g : ℍ[ℝ]) * ((g : ℍ[ℝ]) * z) = z := by
    rw [← mul_assoc, Unitary.star_mul_self_of_mem g.2, one_mul]
  simp only [hinv, star_mul, star_star, mul_assoc, c₁]

/-- The polynomial action is gauge invariant on the whole ambient space. -/
theorem actA_gauge (h : V' → Q) (y : Amb (Edge V')) :
    actA n (ambIso (fun e => h e.1) (fun e => (h e.2.1)⁻¹) y) = actA n y := by
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold termA
  rcases p with ⟨x, ⟨⟨μ, ν⟩, hμν⟩⟩
  simp only [plaqA, ambIso_apply, ed]
  have hc : step (2 * n) (step (2 * n) x ν) μ = step (2 * n) (step (2 * n) x μ) ν :=
    step_comm (2 * n) x ν μ
  rw [congrArg h hc, gauge_four, re_conj_comm]

/-- **Gauge covariance of the flow.** -/
theorem wf_gauge (h : V' → Q) (t : ℝ) (U : Configuration V' Q) :
    wf n t (gauge V' Q h U) = gauge V' Q h (wf n t U) :=
  wflow_actQ (contDiff_actA n) (fun e => h e.1) (fun e => (h e.2.1)⁻¹) (actA_gauge n h) t U

/-- A center flip: a field of central signs whose product around every plaquette is one. -/
structure IsCenterFlip (s : Edge V' → Q) : Prop where
  central : ∀ e, s e = 1 ∨ s e = ω
  plaq : ∀ x μ ν, μ < ν → s (ed n x μ) * s (ed n (step (2 * n) x μ) ν) * s (ed n (step (2 * n) x ν) μ) *
    s (ed n x ν) = 1

theorem center_real (q : Q) (h : q = 1 ∨ q = ω) : ∃ r : ℝ, (q : ℍ[ℝ]) = (r : ℍ[ℝ]) := by
  rcases h with rfl | rfl
  · exact ⟨1, by simp⟩
  · exact ⟨-1, by simp [ω_coe]⟩

theorem flip_four (r₁ r₂ r₃ r₄ : ℝ) (hprod : r₁ * r₂ * r₃ * r₄ = 1) (y₁ y₂ y₃ y₄ : ℍ[ℝ]) :
    ((r₁ : ℍ[ℝ]) * y₁ * 1) * ((r₂ : ℍ[ℝ]) * y₂ * 1) * star ((r₃ : ℍ[ℝ]) * y₃ * 1) *
        star ((r₄ : ℍ[ℝ]) * y₄ * 1) = y₁ * y₂ * star y₃ * star y₄ := by
  simp only [mul_one, Quaternion.coe_mul_eq_smul, Quaternion.star_smul, smul_mul_assoc, mul_smul_comm,
    smul_smul]
  convert one_smul ℝ _ using 2
  rw [← hprod]
  ring

theorem actA_flip (s : Edge V' → Q) (hs : IsCenterFlip n s) (y : Amb (Edge V')) :
    actA n (ambIso s (fun _ => 1) y) = actA n y := by
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold termA
  rcases p with ⟨x, ⟨⟨μ, ν⟩, hμν⟩⟩
  simp only [plaqA, ambIso_apply]
  obtain ⟨r₁, h₁⟩ := center_real _ (hs.central (ed n x μ))
  obtain ⟨r₂, h₂⟩ := center_real _ (hs.central (ed n (step (2 * n) x μ) ν))
  obtain ⟨r₃, h₃⟩ := center_real _ (hs.central (ed n (step (2 * n) x ν) μ))
  obtain ⟨r₄, h₄⟩ := center_real _ (hs.central (ed n x ν))
  have hprod : r₁ * r₂ * r₃ * r₄ = 1 := by
    have h1 : ((s (ed n x μ) * s (ed n (step (2 * n) x μ) ν) * s (ed n (step (2 * n) x ν) μ) *
        s (ed n x ν) : Q) : ℍ[ℝ]) = 1 := by rw [hs.plaq x μ ν hμν]; rfl
    have h2 : ((s (ed n x μ) * s (ed n (step (2 * n) x μ) ν) * s (ed n (step (2 * n) x ν) μ) *
        s (ed n x ν) : Q) : ℍ[ℝ]) = (r₁ : ℍ[ℝ]) * r₂ * r₃ * r₄ := by
      rw [← h₁, ← h₂, ← h₃, ← h₄]; rfl
    rw [h2] at h1
    have h3 : ((r₁ * r₂ * r₃ * r₄ : ℝ) : ℍ[ℝ]) = ((1 : ℝ) : ℍ[ℝ]) := by
      push_cast
      exact h1
    exact Quaternion.coe_injective h3
  have hone : (((1 : Q) : ℍ[ℝ])) = 1 := rfl
  rw [h₁, h₂, h₃, h₄, hone, flip_four r₁ r₂ r₃ r₄ hprod]

/-- **Center-flip covariance of the flow.** -/
theorem wf_flip (s : Edge V' → Q) (hs : IsCenterFlip n s) (t : ℝ) (U : Configuration V' Q) :
    wf n t (fun e => s e * U e) = fun e => s e * wf n t U e := by
  have h := wflow_actQ (contDiff_actA n) s (fun _ => 1) (actA_flip n s hs) t U
  have e (V : Configuration V' Q) : actQ s (fun _ => 1) V = fun e => s e * V e :=
    funext fun e => mul_one _
  rw [e, e] at h
  exact h

open Classical in
/-- The flip of one slab of links: direction `i`, at `x i = c`. -/
def slabFlip (i : Fin 4) (c : ZMod (2 * n)) (e : Edge V') : Q :=
  if e.2.2.val = i ∧ e.1 i = c then ω else 1

theorem slabFlip_ed (i : Fin 4) (c : ZMod (2 * n)) (x : V') (μ : Fin 4) :
    slabFlip n i c (ed n x μ) = if μ = i ∧ x i = c then ω else 1 := rfl

theorem isCenterFlip_slab (i : Fin 4) (c : ZMod (2 * n)) : IsCenterFlip n (slabFlip n i c) := by
  classical
  refine ⟨fun e => ?_, fun x μ ν h => ?_⟩
  · unfold slabFlip
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · have hne : μ ≠ ν := ne_of_lt h
    have hstep (y : V') (κ : Fin 4) (hκ : κ ≠ i) : step (2 * n) y κ i = y i := by
      simp [step, hκ.symm]
    have ωω : ω * ω = 1 := by
      apply Subtype.ext
      simp [ω_coe]
    simp only [slabFlip_ed]
    by_cases hμ : μ = i
    · subst hμ
      have hν : ν ≠ μ := hne.symm
      simp only [hstep x ν hν, hν, false_and, if_false, mul_one, true_and]
      split_ifs
      · exact ωω
      · simp
    · by_cases hν : ν = i
      · subst hν
        simp only [hμ, false_and, if_false, one_mul, mul_one, true_and, hstep x μ hμ]
        split_ifs
        · exact ωω
        · simp
      · simp [hμ, hν]

/-! ### Rotations in coordinates -/

/-- The rotation of `TwistedIBP.flow`, as a point of the ambient space. -/
def rotOf (X : Fin 3 → Fin 4 → Section (2 * n)) : Amb (Edge V') :=
  WithLp.toLp 2 (edgeRot n X)

theorem expCurve_flow (X : Fin 3 → Fin 4 → Section (2 * n)) (U : Configuration V' Q) (s : ℝ) :
    expCurve (rotOf n X) (emb U) s = emb (TwistedIBP.flow n X s U) := by
  refine PiLp.ext fun e => ?_
  rw [emb_apply, flow_apply]
  rfl

/-- The colour coordinates of an imaginary configuration. -/
def coords (ξ : Amb (Edge V')) : Fin 3 → Fin 4 → Section (2 * n) :=
  fun a μ => WithLp.toLp 2 fun x => ![(ξ (ed n x μ)).imI, (ξ (ed n x μ)).imJ, (ξ (ed n x μ)).imK] a

theorem imag_coords {ξ : Amb (Edge V')} (hξ : ∀ e, star (ξ e) = -ξ e) (μ : Fin 4) (x : V') :
    imag (coords n ξ) μ x = ξ (ed n x μ) := by
  have h0 := re_of_star (hξ (ed n x μ))
  unfold imag coords
  rw [Fin.sum_univ_three]
  ext <;> simp [basis, h0]

theorem rotOf_coords {ξ : Amb (Edge V')} (hξ : ∀ e, star (ξ e) = -ξ e) : rotOf n (coords n ξ) = ξ := by
  refine PiLp.ext fun e => ?_
  change imag (coords n ξ) (edgeCoordinates (2 * n) e).2 (edgeCoordinates (2 * n) e).1 = _
  rw [imag_coords n hξ, ed_coords]

theorem coords_norm {ξ : Amb (Edge V')} (hξ : ∀ e, star (ξ e) = -ξ e) :
    ∑ a, ∑ μ, ‖coords n ξ a μ‖ ^ 2 = ‖ξ‖ ^ 2 := by
  rw [← Xh_norm, norm_sq_amb, sum_edges]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [norm_sq_field]
  exact Finset.sum_congr rfl fun x _ => by rw [Xh_apply, imag_coords n hξ]

theorem hess_coords {ξ : Amb (Edge V')} (hξ : ∀ e, star (ξ e) = -ξ e) (U : Configuration V' Q) :
    hess (actA n) (emb U) ξ =
      deriv (deriv fun t => action n Q (spatialTwist n) character 1 2 (TwistedIBP.flow n (coords n ξ) t U)) 0 := by
  unfold hess
  have : (fun s => actA n (expCurve ξ (emb U) s)) =
      fun t => action n Q (spatialTwist n) character 1 2 (TwistedIBP.flow n (coords n ξ) t U) := by
    funext s
    conv_lhs => rw [← rotOf_coords n hξ, expCurve_flow, actA_emb]
    rfl
  rw [this]

/-- The second derivative is at least `-48 ‖X‖²`, at every configuration. -/
theorem second_ge (L : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) :
    -48 * ∑ a, ∑ μ, ‖X a μ‖ ^ 2 ≤
      deriv (deriv fun t => action n Q (spatialTwist n) character 1 2 (cfg n L X t)) 0 := by
  obtain ⟨s₁, s₂, h₁, h₂, -, h₀₂⟩ := action_jet n 1 L X
  have hd : (deriv fun t => action n Q (spatialTwist n) character 1 2 (cfg n L X t)) = s₁ :=
    funext fun t => (h₁ t).deriv
  rw [hd, (h₂ 0).deriv, h₀₂, one_mul]
  have h : ∑ p : PlaquetteIndex (2 * n), -(8 * linkSq n X p.1 p.2.1.1 p.2.1.2) ≤
      ∑ p : PlaquetteIndex (2 * n), -(2 * (Sc n L X p * plaqC n L X p.1 p.2.1.1 p.2.1.2).re) := by
    refine Finset.sum_le_sum fun p _ => ?_
    have a := (abs_le.1 (Sc_re_le n L X p)).2
    have b := linkSum_sq n X p.1 p.2.1.1 p.2.1.2
    linarith only [a, b]
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum] at h
  have hl : ∑ p : PlaquetteIndex (2 * n), linkSq n X p.1 p.2.1.1 p.2.1.2 =
      6 * ∑ a, ∑ μ, ‖X a μ‖ ^ 2 := link_count n X
  rw [hl] at h
  linarith only [h]

/-- A Hessian floor at every unit configuration, uniform in the lattice size. -/
theorem hess_floor {x ξ : Amb (Edge V')} (hx : Sph x) (hξ : ∀ e, star (ξ e) = -ξ e) :
    -48 * ‖ξ‖ ^ 2 ≤ hess (actA n) x ξ := by
  have e : x = emb (ofSph x hx) := rfl
  rw [e, hess_coords n hξ, ← coords_norm n hξ]
  exact second_ge n _ _

theorem defect_sq_le (U : Configuration V' Q) (x : V') (μ ν : Fin 4) (h : μ < ν) :
    defect (linkValue (2 * n) Q U) μ ν x ^ 2 ≤ actionOne n U := by
  rw [TwistedNearFlat.actionOne_eq]
  unfold actionL
  let f : PlaquetteIndex (2 * n) → ℝ := fun p => defect (linkValue (2 * n) Q U) p.2.1.1 p.2.1.2 p.1 ^ 2
  have h1 : f (x, ⟨(μ, ν), h⟩) ≤ ∑ p, f p :=
    Finset.single_le_sum (f := f) (fun p _ => sq_nonneg (defect (linkValue (2 * n) Q U) p.2.1.1 p.2.1.2 p.1))
      (Finset.mem_univ _)
  exact h1

/-- The Hessian floor on the sublevel set of the action, from the covariant Hessian bound. -/
theorem hess_floor_small {x ξ : Amb (Edge V')} (hx : Sph x) (hξ : ∀ e, star (ξ e) = -ξ e) {S₀ : ℝ}
    (hS : actA n x ≤ S₀) : -(192 * S₀ + 48 * √S₀) * ‖ξ‖ ^ 2 ≤ hess (actA n) x ξ := by
  have e : x = emb (ofSph x hx) := rfl
  set U := ofSph x hx with hU
  rw [e, actA_emb] at hS
  have hS0 : 0 ≤ S₀ := (TwistedIBP.action_nonneg n 1 zero_le_one U |>.trans (by
    rw [action_eq_mul, one_mul]; exact hS))
  have hδ (y : V') (μ ν : Fin 4) (h : μ < ν) : defect (linkValue (2 * n) Q U) μ ν y ≤ √S₀ :=
    Real.le_sqrt_of_sq_le ((defect_sq_le n U y μ ν h).trans hS)
  have := hessian_cov_lower n 1 zero_le_one (linkValue (2 * n) Q U) (coords n ξ) (√S₀)
    (Real.sqrt_nonneg _) (fun y μ ν h => hδ y μ ν h)
  rw [e, hess_coords n hξ]
  have hc : 0 ≤ curlEnergy (covShift (linkValue (2 * n) Q U)) (Xh n (coords n ξ)) := by
    unfold curlEnergy
    refine Finset.sum_nonneg fun μ _ => Finset.sum_nonneg fun ν _ => ?_
    split_ifs <;> positivity
  rw [coords_norm n hξ, Real.sq_sqrt hS0, one_mul] at this
  have h2 : -(192 * S₀ + 48 * √S₀) * ‖ξ‖ ^ 2 ≤ curlEnergy (covShift (linkValue (2 * n) Q U))
      (Xh n (coords n ξ)) - (192 * S₀ + 48 * √S₀) * ‖ξ‖ ^ 2 := by linarith only [hc]
  exact h2.trans this

/-- **Smoothing, uniform in the lattice size.** For every configuration and `t > 0`, the squared force at
flow time `t` is at most `(1/t + 96)` times the action lost by time `t`. The action on the right is the
total action, so this is a statement about densities only after dividing by the volume. -/
theorem wf_smoothing (U : Configuration V' Q) {t : ℝ} (ht : 0 < t) :
    forceSq n (wf n t U) ≤ (1 / t + 96) * (actionOne n U - actionOne n (wf n t U)) := by
  have h := (smoothing (contDiff_actA n) (wf_isLine n U) (wf_sph n U 0) (t := t) (Λ := 48) ht
    (by norm_num) (fun x hx _ ξ hξ => hess_floor n hx hξ)).2
  simp only [actA_emb, wf_zero] at h
  convert h using 2
  norm_num

/-- The squared force grows at most at rate `96`, uniformly in the lattice size. -/
theorem wf_force_growth (U : Configuration V' Q) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    forceSq n (wf n t U) ≤ Real.exp (96 * (t - s)) * forceSq n (wf n s U) := by
  rcases hst.eq_or_lt with rfl | hlt
  · simp
  have ht : 0 < t := hs.trans_lt hlt
  have h := (smoothing (contDiff_actA n) (wf_isLine n U) (wf_sph n U 0) (t := t) (Λ := 48) ht
    (by norm_num) (fun x hx _ ξ hξ => hess_floor n hx hξ)).1 s ⟨hs, hst⟩
  have e : 2 * (48 : ℝ) * (t - s) = 96 * (t - s) := by ring
  rwa [e] at h

/-- **Sharper smoothing at small total action.** If `192 S + 48 √S ≤ Λ`, with `S` the initial action, the
rate `96` improves to `2Λ`. So `t · forceSq(t) ≤ 2 S` whenever `2Λ t ≤ 1`. The hypothesis is on the total action, and it
improves on `96` only when `S` is below about `0.15`. -/
theorem wf_smoothing_small (U : Configuration V' Q) {t Λ : ℝ} (ht : 0 < t) (hΛ : 0 < Λ)
    (hle : 192 * actionOne n U + 48 * √(actionOne n U) ≤ Λ) :
    forceSq n (wf n t U) ≤ (1 / t + 2 * Λ) * (actionOne n U - actionOne n (wf n t U)) := by
  have h := (smoothing (contDiff_actA n) (wf_isLine n U) (wf_sph n U 0) (t := t) (Λ := Λ) ht hΛ
    (fun x hx hS ξ hξ => by
      have hS' : actA n x ≤ actionOne n U := by
        have := hS
        simpa only [wf_zero, actA_emb] using this
      have hf := hess_floor_small n hx hξ hS'
      refine le_trans ?_ hf
      have := sq_nonneg ‖ξ‖
      nlinarith only [this, hle])).2
  simpa only [actA_emb, wf_zero] using h

/-- A field with no force is a fixed point of the flow. -/
theorem wf_of_force_zero (U : Configuration V' Q) (h : forceSq n U = 0) (t : ℝ) : wf n t U = U := by
  have hF : field (actA n) (emb U) = 0 := norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 h)
  have hc : IsLine (actA n) fun _ : ℝ => emb U := fun s => by
    rw [hF]
    exact hasDerivAt_const s _
  exact (congrFun (wf_unique n U (γ := fun _ => U) hc rfl) t).symm

/-- A zero-action field is a fixed point of the flow. -/
theorem wf_of_action_zero (U : Configuration V' Q) (h : actionOne n U = 0) (t : ℝ) : wf n t U = U := by
  have hmin : IsLocalMin (fun s => actionOne n (wf n s U)) 0 := by
    refine Eventually.of_forall fun s => ?_
    simp only [wf_zero, h]
    have := TwistedIBP.action_nonneg n 1 zero_le_one (wf n s U)
    rwa [action_eq_mul, one_mul] at this
  have hd := hmin.hasDerivAt_eq_zero (hasDerivAt_action_wf n U 0)
  rw [wf_zero] at hd
  exact wf_of_force_zero n U (by linarith only [hd]) t

/-! ### First-order rates along the flow -/

/-- The action's rate at a configuration along a rotation, in the plaquette form of `TwistedIBP`. -/
theorem sum_Ap {ξ : Amb (Edge V')} (hξ : ∀ e, star (ξ e) = -ξ e) (U : Configuration V' Q) :
    2 * ∑ p, Ap n (coords n ξ) p U = ⟪rot (actA n) (emb U), ξ⟫ := by
  obtain ⟨s₁, -, h₁, -, h₀₁, -⟩ := action_jet n 1 (linkValue (2 * n) Q U) (coords n ξ)
  have hfun : (fun s => actA n (expCurve ξ (emb U) s)) =
      fun t => action n Q (spatialTwist n) character 1 2 (cfg n (linkValue (2 * n) Q U) (coords n ξ) t) := by
    funext s
    conv_lhs => rw [← rotOf_coords n hξ, expCurve_flow, actA_emb]
    rfl
  have h2 := hasDerivAt_comp_S (contDiff_actA n) (expCurve_d0 ξ (emb U))
  rw [hfun, expCurve_zero, inner_grad_lmul (emb_sph U) hξ] at h2
  have h3 := h2.unique (h₁ 0)
  rw [h₀₁, one_mul, Finset.sum_neg_distrib, ← Finset.mul_sum] at h3
  have h4 : ⟪rot (actA n) (emb U), ξ⟫ = 2 * ∑ p : PlaquetteIndex (2 * n),
      (Zp n (linkValue (2 * n) Q U) (coords n ξ) p *
        plaqC n (linkValue (2 * n) Q U) (coords n ξ) p.1 p.2.1.1 p.2.1.2).re := by
    linarith only [h3]
  rw [h4]
  rfl

/-- The rate of one plaquette along the flow. -/
theorem hasDerivAt_term_wf (U : Configuration V' Q) (t : ℝ) (p : PlaquetteIndex (2 * n)) :
    HasDerivAt (fun s => term n Q (spatialTwist n) character 2 (wf n s U) p)
      (-2 * Ap n (coords n (rot (actA n) (emb (wf n t U)))) p (wf n t U)) t := by
  set x := emb (wf n t U) with hx
  set ρ := rot (actA n) x with hρ
  have hsph : Sph x := emb_sph _
  have hstar : ∀ e, star (ρ e) = -ρ e := rot_star x
  have hG : HasFDerivAt (termA n p) (fderiv ℝ (termA n p) x) x :=
    ((contDiff_termA n p).differentiable (by norm_num) x).hasFDerivAt
  have h1 := hG.comp_hasDerivAt t (wf_isLine n U t)
  have hc : HasDerivAt (fun s => termA n p (expCurve ρ x s)) (fderiv ℝ (termA n p) x (field (actA n) x)) 0 := by
    have hd := expCurve_d0 ρ x
    rw [lmul_rot hsph] at hd
    have hG' : HasFDerivAt (termA n p) (fderiv ℝ (termA n p) x) (expCurve ρ x 0) := by
      rw [expCurve_zero]
      exact hG
    exact hG'.comp_hasDerivAt 0 hd
  obtain ⟨f₁, f₂, j₁, -, j₀, -⟩ := term_jet n (linkValue (2 * n) Q (wf n t U)) (coords n ρ) p
  have hfun : (fun s => termA n p (expCurve ρ x s)) =
      fun s => term n Q (spatialTwist n) character 2 (cfg n (linkValue (2 * n) Q (wf n t U)) (coords n ρ) s) p := by
    funext s
    conv_lhs => rw [← rotOf_coords n hstar, expCurve_flow, termA_emb]
    rfl
  rw [hfun] at hc
  have hval := hc.unique (j₁ 0)
  rw [j₀] at hval
  have hfun2 : (fun s => term n Q (spatialTwist n) character 2 (wf n s U) p) =
      (termA n p) ∘ fun s => emb (wf n s U) := by
    funext s
    exact (termA_emb n _ p).symm
  rw [hfun2]
  convert h1 using 1
  rw [hval]
  simp only [Ap]
  ring

/-! ### The local energy inequality -/

/-- The four link contributions to a plaquette rate. -/
def b₁ (L : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (x : V') (μ ν : Fin 4) : ℝ :=
  ((plaqOf n L X x μ ν).Y₁ * plaqC n L X x μ ν).re
def b₂ (L : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (x : V') (μ ν : Fin 4) : ℝ :=
  ((plaqOf n L X x μ ν).Y₂ * plaqC n L X x μ ν).re
def b₃ (L : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (x : V') (μ ν : Fin 4) : ℝ :=
  ((plaqOf n L X x μ ν).Y₃ * plaqC n L X x μ ν).re
def b₄ (L : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (x : V') (μ ν : Fin 4) : ℝ :=
  ((plaqOf n L X x μ ν).Y₄ * plaqC n L X x μ ν).re

theorem Ap_eq (X : Fin 3 → Fin 4 → Section (2 * n)) (p : PlaquetteIndex (2 * n)) (U : Configuration V' Q) :
    Ap n X p U = b₁ n (linkValue (2 * n) Q U) X p.1 p.2.1.1 p.2.1.2 + b₂ n (linkValue (2 * n) Q U) X p.1 p.2.1.1 p.2.1.2 +
      b₃ n (linkValue (2 * n) Q U) X p.1 p.2.1.1 p.2.1.2 + b₄ n (linkValue (2 * n) Q U) X p.1 p.2.1.1 p.2.1.2 := by
  simp only [Ap, Zp, b₁, b₂, b₃, b₄, add_mul, Quaternion.re_add]

theorem norm_plaqC_sub_one (L : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (x : V') (μ ν : Fin 4) :
    ‖plaqC n L X x μ ν - 1‖ = defect L μ ν x := by
  unfold plaqC defect d
  have hP : ((plaqOf n L X x μ ν).P : ℍ[ℝ]) =
      ((L x μ * L (step (2 * n) x μ) ν * (L (step (2 * n) x ν) μ)⁻¹ * (L x ν)⁻¹ : Q) : ℍ[ℝ]) := rfl
  rw [hP]
  generalize ((L x μ * L (step (2 * n) x μ) ν * (L (step (2 * n) x ν) μ)⁻¹ * (L x ν)⁻¹ : Q) : ℍ[ℝ]) = P
  rcases (by unfold twistExp; split_ifs <;> simp : twistExp μ ν x = 0 ∨ twistExp μ ν x = 1)
    with hc | hc
  · rw [hc]
    simp
  · rw [hc]
    simp only [if_true, pow_one, ω_coe]
    rw [← norm_neg]
    congr 1
    ext <;> simp <;> ring

theorem re_imag_mul_le {q c : ℍ[ℝ]} (hq : q.re = 0) : |(q * c).re| ≤ ‖q‖ * ‖c - 1‖ := by
  have h : (q * c).re = (q * (c - 1)).re := by
    rw [mul_sub, mul_one, Quaternion.re_sub, hq, sub_zero]
  rw [h, ← norm_mul]
  exact re_abs_le _

theorem re_imag (X : Fin 3 → Fin 4 → Section (2 * n)) (μ : Fin 4) (x : V') : (imag X μ x).re = 0 :=
  re_of_star (imag_star X μ x)

theorem re_conj_imag (g : Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (μ : Fin 4) (x : V') :
    ((g : ℍ[ℝ]) * imag X μ x * ((g⁻¹ : Q) : ℍ[ℝ])).re = 0 := by
  have := re_conj_comm g (imag X μ x)
  rw [re_imag] at this
  exact this

theorem b₂_abs (L : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (x : V') (μ ν : Fin 4) :
    |b₂ n L X x μ ν| ≤ ‖imag X ν (step (2 * n) x μ)‖ * defect L μ ν x := by
  rw [← norm_plaqC_sub_one n L X]
  refine (re_imag_mul_le ?_).trans_eq ?_
  · exact re_conj_imag n _ X ν _
  · simp only [plaqOf]
    rw [conj_norm]

theorem b₃_abs (L : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (x : V') (μ ν : Fin 4) :
    |b₃ n L X x μ ν| ≤ ‖imag X μ (step (2 * n) x ν)‖ * defect L μ ν x := by
  rw [← norm_plaqC_sub_one n L X]
  refine (re_imag_mul_le ?_).trans_eq ?_
  · simp only [plaqOf, Quaternion.re_neg, neg_eq_zero]
    exact re_conj_imag n _ X μ _
  · simp only [plaqOf]
    rw [norm_neg, conj_norm]

/-- Rescaling a direction link by link rescales each contribution by the weight at its tail. -/
theorem b_scale (L : V' → Fin 4 → Q) (X X' : Fin 3 → Fin 4 → Section (2 * n)) (w : V' → ℝ)
    (h : ∀ μ x, imag X' μ x = w x • imag X μ x) (x : V') (μ ν : Fin 4) :
    b₁ n L X' x μ ν = w x * b₁ n L X x μ ν ∧
    b₂ n L X' x μ ν = w (step (2 * n) x μ) * b₂ n L X x μ ν ∧
    b₃ n L X' x μ ν = w (step (2 * n) x ν) * b₃ n L X x μ ν ∧
    b₄ n L X' x μ ν = w x * b₄ n L X x μ ν := by
  have hc : plaqC n L X' x μ ν = plaqC n L X x μ ν := rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [b₁, b₂, b₃, b₄, hc]
    simp only [plaqOf, h, mul_smul_comm, smul_mul_assoc, neg_mul, Quaternion.re_smul, smul_eq_mul,
      Quaternion.re_neg]
    try ring

/-- The count of the two transverse links of each plaquette: each link lies in three planes. -/
theorem count_two (g : V' → Fin 4 → ℝ) :
    ∑ p : PlaquetteIndex (2 * n), (g (step (2 * n) p.1 p.2.1.1) p.2.1.2 + g (step (2 * n) p.1 p.2.1.2) p.2.1.1) =
      3 * ∑ μ, ∑ x, g x μ := by
  let M : Fin 4 → ℝ := fun μ => ∑ x, g x μ
  have hM : M = fun μ => ∑ x, g x μ := rfl
  have hpl (μ ν : Fin 4) : ∑ x, (g (step (2 * n) x μ) ν + g (step (2 * n) x ν) μ) = M ν + M μ := by
    rw [Finset.sum_add_distrib, sum_step (fun y => g y ν) μ, sum_step (fun y => g y μ) ν]
  have hL : ∑ p : PlaquetteIndex (2 * n),
      (g (step (2 * n) p.1 p.2.1.1) p.2.1.2 + g (step (2 * n) p.1 p.2.1.2) p.2.1.1) =
      ∑ d : Plane, (M d.1.2 + M d.1.1) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ => hpl d.1.1 d.1.2
  have hP : ∑ d : Plane, (M d.1.2 + M d.1.1) = ∑ μ, ∑ ν, if μ < ν then M ν + M μ else 0 :=
    plane_sum (fun μ ν => M ν + M μ)
  rw [hL, hP]
  change _ = 3 * ∑ μ, M μ
  simp (decide := true) only [Fin.sum_univ_four, if_true, if_false]
  ring

/-- The weighted action. -/
def wAction (w : V' → ℝ) (U : Configuration V' Q) : ℝ :=
  ∑ p, w p.1 * term n Q (spatialTwist n) character 2 U p

/-- The weighted squared force. -/
def wForce (w : V' → ℝ) (U : Configuration V' Q) : ℝ :=
  ∑ e : Edge V', w e.1 * ‖field (actA n) (emb U) e‖ ^ 2

theorem term_nonneg (U : Configuration V' Q) (p : PlaquetteIndex (2 * n)) :
    0 ≤ term n Q (spatialTwist n) character 2 U p := by
  rcases p with ⟨x, ⟨⟨μ, ν⟩, h⟩⟩
  rw [term_eq_defect_sq]
  exact sq_nonneg _

/-- **Static form of the local energy inequality.** The weight may vary slowly, by a factor `1 + κ` across a
link. No constant depends on the lattice size. -/
theorem wAction_rate_le (U : Configuration V' Q) (w : V' → ℝ) (κ : ℝ) (hκ : 0 ≤ κ) (hw0 : ∀ x, 0 ≤ w x)
    (hw : ∀ x μ, |w (step (2 * n) x μ) - w x| ≤ κ * w x ∧ |w (step (2 * n) x μ) - w x| ≤ κ * w (step (2 * n) x μ)) :
    ∑ p, w p.1 * (-2 * Ap n (coords n (rot (actA n) (emb U))) p U) ≤
      -(1 / 2) * wForce n w U + 12 * κ ^ 2 * (1 + κ) * wAction n w U := by
  set ρ := rot (actA n) (emb U) with hρ
  have hsph : Sph (emb U) := emb_sph U
  have hstar : ∀ e, star (ρ e) = -ρ e := rot_star (emb U)
  set L := linkValue (2 * n) Q U with hL
  set X := coords n ρ with hX
  -- The weighted direction.
  let ρw : Amb (Edge V') := WithLp.toLp 2 fun e => w e.1 • ρ e
  have hstarw : ∀ e, star (ρw e) = -ρw e := fun e => by
    change star (w e.1 • ρ e) = -(w e.1 • ρ e)
    rw [Quaternion.star_smul, hstar e, smul_neg]
  set Xw := coords n ρw with hXw
  have himag (μ : Fin 4) (x : V') : imag X μ x = ρ (ed n x μ) := imag_coords n hstar μ x
  have himagw (μ : Fin 4) (x : V') : imag Xw μ x = w x • imag X μ x := by
    rw [imag_coords n hstarw, himag]
    rfl
  have hscale := b_scale n L X Xw w himagw
  -- The total.
  have hglobal : 2 * ∑ p, Ap n Xw p U = wForce n w U := by
    rw [sum_Ap n hstarw U, inner_amb]
    refine Finset.sum_congr rfl fun e _ => ?_
    change ⟪ρ e, w e.1 • ρ e⟫ = _
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hρ, norm_rot hsph]
  -- The pointwise inequality on a plaquette.
  let r : V' → Fin 4 → ℝ := fun x μ => ‖ρ (ed n x μ)‖
  have hpt (p : PlaquetteIndex (2 * n)) : w p.1 * (-2 * Ap n X p U) ≤ -2 * Ap n Xw p U +
      (w (step (2 * n) p.1 p.2.1.1) * r (step (2 * n) p.1 p.2.1.1) p.2.1.2 ^ 2 +
        w (step (2 * n) p.1 p.2.1.2) * r (step (2 * n) p.1 p.2.1.2) p.2.1.1 ^ 2) / 6 +
      12 * κ ^ 2 * (1 + κ) * (w p.1 * term n Q (spatialTwist n) character 2 U p) := by
    rcases p with ⟨x, ⟨⟨μ, ν⟩, h⟩⟩
    simp only
    rw [Ap_eq, Ap_eq, term_eq_defect_sq]
    simp only
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hscale x μ ν
    rw [h₁, h₂, h₃, h₄]
    have ab₂ := b₂_abs n L X x μ ν
    have ab₃ := b₃_abs n L X x μ ν
    rw [himag] at ab₂ ab₃
    set D := defect L μ ν x with hD
    have hD0 : 0 ≤ D := defect_nonneg _ _ _ _
    set B₁ := b₁ n L X x μ ν
    set B₂ := b₂ n L X x μ ν
    set B₃ := b₃ n L X x μ ν
    set B₄ := b₄ n L X x μ ν
    set a := w x with ha
    set b := w (step (2 * n) x μ) with hb
    set c := w (step (2 * n) x ν) with hc
    set r₂ := r (step (2 * n) x μ) ν with hr₂
    set r₃ := r (step (2 * n) x ν) μ with hr₃
    change |B₂| ≤ r₂ * D at ab₂
    change |B₃| ≤ r₃ * D at ab₃
    have hr₂0 : 0 ≤ r₂ := norm_nonneg _
    have hr₃0 : 0 ≤ r₃ := norm_nonneg _
    have hb0 : 0 ≤ b := hw0 _
    have hc0 : 0 ≤ c := hw0 _
    have ha0 : 0 ≤ a := hw0 _
    obtain ⟨wb₁, wb₂⟩ := hw x μ
    obtain ⟨wc₁, wc₂⟩ := hw x ν
    -- One transverse link.
    have one (e A s : ℝ) (he0 : 0 ≤ e) (hs0 : 0 ≤ s) (hA : |A| ≤ s * D) (hdiff : |e - a| ≤ κ * e)
        (hup : e - a ≤ κ * a) :
        2 * (e - a) * A ≤ e * s ^ 2 / 6 + 6 * κ ^ 2 * (1 + κ) * (a * D ^ 2) := by
      have h1 : 2 * (e - a) * A ≤ 2 * (κ * e) * (s * D) := by
        have : |2 * (e - a) * A| ≤ 2 * (κ * e) * (s * D) := by
          rw [abs_mul, abs_mul, abs_two]
          have := mul_le_mul hdiff hA (abs_nonneg _) (by positivity)
          nlinarith only [this]
        exact (le_abs_self _).trans this
      have h2 : 2 * (κ * e) * (s * D) ≤ e * s ^ 2 / 6 + 6 * κ ^ 2 * e * D ^ 2 := by
        have := mul_nonneg he0 (sq_nonneg (s - 6 * κ * D))
        nlinarith only [this]
      have h3 : e ≤ (1 + κ) * a := by linarith only [hup]
      have h4 : 6 * κ ^ 2 * e * D ^ 2 ≤ 6 * κ ^ 2 * (1 + κ) * (a * D ^ 2) := by
        have := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 6 * κ ^ 2 * D ^ 2)
        nlinarith only [this]
      linarith only [h1, h2, h4]
    have o₂ := one b B₂ r₂ hb0 hr₂0 ab₂ wb₂ ((le_abs_self _).trans wb₁)
    have o₃ := one c B₃ r₃ hc0 hr₃0 ab₃ wc₂ ((le_abs_self _).trans wc₁)
    nlinarith only [o₂, o₃]
  have hsum := Finset.sum_le_sum fun p (_ : p ∈ Finset.univ) => hpt p
  refine hsum.trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_div]
  have hc := count_two n (fun x μ => w x * r x μ ^ 2)
  rw [hc]
  have hF : wForce n w U = ∑ μ, ∑ x, w x * r x μ ^ 2 := by
    unfold wForce
    rw [sum_edges]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun x _ => ?_
    simp only [r]
    rw [hρ, norm_rot hsph]
    rfl
  rw [← hF]
  unfold wAction
  linarith only [hglobal]

theorem hasDerivAt_wAction (U : Configuration V' Q) (w : V' → ℝ) (t : ℝ) :
    HasDerivAt (fun s => wAction n w (wf n s U))
      (∑ p, w p.1 * (-2 * Ap n (coords n (rot (actA n) (emb (wf n t U)))) p (wf n t U))) t :=
  HasDerivAt.fun_sum fun p _ => (hasDerivAt_term_wf n U t p).const_mul (w p.1)

theorem continuous_wForce (w : V' → ℝ) : Continuous (wForce n w) := by
  unfold wForce
  refine continuous_finset_sum _ fun e _ => continuous_const.mul ?_
  exact ((PiLp.continuous_apply 2 _ e).comp
    ((contDiff_field (contDiff_actA n)).continuous.comp continuous_emb)).norm.pow 2

theorem wForce_nonneg (w : V' → ℝ) (hw0 : ∀ x, 0 ≤ w x) (U : Configuration V' Q) : 0 ≤ wForce n w U :=
  Finset.sum_nonneg fun e _ => mul_nonneg (hw0 _) (sq_nonneg _)

theorem wAction_nonneg (w : V' → ℝ) (hw0 : ∀ x, 0 ≤ w x) (U : Configuration V' Q) : 0 ≤ wAction n w U :=
  Finset.sum_nonneg fun p _ => mul_nonneg (hw0 _) (term_nonneg n U p)

theorem continuous_wf_right (t : ℝ) : Continuous (wf n t) :=
  (continuous_wf n).comp (continuous_const.prodMk continuous_id)

/-- **The local energy inequality, uniform in the lattice size.** For a weight varying by at most a factor
`1 + κ` across a link, the weighted action grows at rate at most `12 κ² (1 + κ)`, and its dissipation controls
the weighted force, integrated in flow time. -/
theorem local_energy (U : Configuration V' Q) (w : V' → ℝ) (κ : ℝ) (hκ : 0 ≤ κ) (hw0 : ∀ x, 0 ≤ w x)
    (hw : ∀ x μ, |w (step (2 * n) x μ) - w x| ≤ κ * w x ∧ |w (step (2 * n) x μ) - w x| ≤ κ * w (step (2 * n) x μ))
    {t : ℝ} (ht : 0 ≤ t) :
    wAction n w (wf n t U) + (1 / 2) * ∫ s in (0 : ℝ)..t, wForce n w (wf n s U) ≤
      Real.exp (12 * κ ^ 2 * (1 + κ) * t) * wAction n w U := by
  set C := 12 * κ ^ 2 * (1 + κ) with hC
  have hC0 : 0 ≤ C := by positivity
  let A : ℝ → ℝ := fun s => wAction n w (wf n s U)
  let F : ℝ → ℝ := fun s => wForce n w (wf n s U)
  have hFc : Continuous F := (continuous_wForce n w).comp
    ((continuous_wf n).comp (continuous_id.prodMk continuous_const))
  let E : ℝ → ℝ := fun s => Real.exp (-C * s)
  have hE (s : ℝ) : HasDerivAt E (Real.exp (-C * s) * (-C)) s := by
    simpa [E] using ((hasDerivAt_id s).const_mul (-C)).exp
  have hEc : Continuous E := Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hI (s : ℝ) : HasDerivAt (fun u => ∫ r in (0 : ℝ)..u, E r * F r) (E s * F s) s :=
    ((hEc.mul hFc).integral_hasStrictDerivAt 0 s).hasDerivAt
  let G : ℝ → ℝ := fun s => E s * A s + (1 / 2) * ∫ r in (0 : ℝ)..s, E r * F r
  have hG (s : ℝ) : HasDerivAt G (Real.exp (-C * s) * (-C) * A s + E s *
      (∑ p, w p.1 * (-2 * Ap n (coords n (rot (actA n) (emb (wf n s U)))) p (wf n s U))) +
        (1 / 2) * (E s * F s)) s :=
    ((hE s).mul (hasDerivAt_wAction n U w s)).add ((hI s).const_mul (1 / 2))
  have hanti : Antitone G := by
    refine antitone_of_deriv_nonpos (fun s => (hG s).differentiableAt) fun s => ?_
    rw [(hG s).deriv]
    have hr := wAction_rate_le n (wf n s U) w κ hκ hw0 hw
    have hEp : 0 < E s := Real.exp_pos _
    change Real.exp (-C * s) * (-C) * A s + E s * _ + _ ≤ _
    have hmul := mul_le_mul_of_nonneg_left hr hEp.le
    change E s * _ ≤ E s * (-(1 / 2) * F s + C * A s) at hmul
    change E s * (-C) * A s + E s * _ + (1 / 2) * (E s * F s) ≤ 0
    nlinarith only [hmul]
  have hle := hanti ht
  have hG0 : G 0 = A 0 := by simp [G, E]
  have hAt : A 0 = wAction n w U := by simp only [A, wf_zero]
  rw [hG0, hAt] at hle
  -- Remove the weight from the integral.
  have hint : E t * ∫ s in (0 : ℝ)..t, F s ≤ ∫ s in (0 : ℝ)..t, E s * F s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on ht ((continuous_const.mul hFc).intervalIntegrable _ _)
      ((hEc.mul hFc).intervalIntegrable _ _) fun s hs => ?_
    refine mul_le_mul_of_nonneg_right ?_ (wForce_nonneg n w hw0 _)
    exact Real.exp_le_exp.2 (by nlinarith only [hs.2, hC0])
  have hEt : 0 < E t := Real.exp_pos _
  have hcomb : E t * (A t + (1 / 2) * ∫ s in (0 : ℝ)..t, F s) ≤ wAction n w U := by
    have : G t = E t * A t + (1 / 2) * ∫ s in (0 : ℝ)..t, E s * F s := rfl
    rw [this] at hle
    nlinarith only [hle, hint]
  have hinv : Real.exp (C * t) * E t = 1 := by
    simp only [E]
    rw [← Real.exp_add]
    simp
  have := mul_le_mul_of_nonneg_left hcomb (Real.exp_pos (C * t)).le
  rw [← mul_assoc, hinv, one_mul] at this
  exact this

/-! ### Concrete exponential weights -/

/-- The `ℓ¹` distance on the torus. -/
def tdist (x₀ x : V') : ℕ := ∑ μ, (x μ - x₀ μ).valMinAbs.natAbs

theorem natAbs_one_le : ((1 : ZMod (2 * n)).valMinAbs.natAbs) ≤ 1 := by
  haveI : NeZero (2 * n) := ⟨by have := NeZero.ne n; omega⟩
  rw [ZMod.valMinAbs_natAbs_eq_min]
  refine (min_le_left _ _).trans ?_
  rw [ZMod.val_one_eq_one_mod]
  exact Nat.mod_le _ _

theorem natAbs_add_one (a : ZMod (2 * n)) :
    (a + 1).valMinAbs.natAbs ≤ a.valMinAbs.natAbs + 1 ∧ a.valMinAbs.natAbs ≤ (a + 1).valMinAbs.natAbs + 1 := by
  have h1 := natAbs_one_le n
  constructor
  · have := ZMod.natAbs_valMinAbs_add_le a 1
    have h2 := Int.natAbs_add_le a.valMinAbs (1 : ZMod (2 * n)).valMinAbs
    omega
  · have := ZMod.natAbs_valMinAbs_add_le (a + 1) (-1)
    have h2 := Int.natAbs_add_le (a + 1).valMinAbs (-1 : ZMod (2 * n)).valMinAbs
    have h3 := ZMod.natAbs_valMinAbs_neg (1 : ZMod (2 * n))
    rw [add_neg_cancel_right] at this
    omega

theorem tdist_self (x₀ : V') : tdist n x₀ x₀ = 0 := by
  simp [tdist]

theorem tdist_step (x₀ x : V') (μ : Fin 4) :
    tdist n x₀ (step (2 * n) x μ) ≤ tdist n x₀ x + 1 ∧ tdist n x₀ x ≤ tdist n x₀ (step (2 * n) x μ) + 1 := by
  classical
  have hone : ∑ κ : Fin 4, (if κ = μ then 1 else 0 : ℕ) = 1 := by simp
  have hk (κ : Fin 4) : (step (2 * n) x μ κ - x₀ κ).valMinAbs.natAbs ≤
        (x κ - x₀ κ).valMinAbs.natAbs + (if κ = μ then 1 else 0) ∧
      (x κ - x₀ κ).valMinAbs.natAbs ≤
        (step (2 * n) x μ κ - x₀ κ).valMinAbs.natAbs + (if κ = μ then 1 else 0) := by
    by_cases h : κ = μ
    · subst h
      have e : step (2 * n) x κ κ - x₀ κ = (x κ - x₀ κ) + 1 := by
        simp [step]
        ring
      rw [e, if_pos rfl]
      exact natAbs_add_one n _
    · have e : step (2 * n) x μ κ = x κ := by simp [step, Pi.single_apply, h]
      rw [e, if_neg h]
      simp
  constructor
  · unfold tdist
    calc _ ≤ ∑ κ, ((x κ - x₀ κ).valMinAbs.natAbs + (if κ = μ then 1 else 0)) :=
          Finset.sum_le_sum fun κ _ => (hk κ).1
      _ = _ := by rw [Finset.sum_add_distrib, hone]
  · unfold tdist
    calc _ ≤ ∑ κ, ((step (2 * n) x μ κ - x₀ κ).valMinAbs.natAbs + (if κ = μ then 1 else 0)) :=
          Finset.sum_le_sum fun κ _ => (hk κ).2
      _ = _ := by rw [Finset.sum_add_distrib, hone]

/-- The exponential weight around `x₀`. -/
def expW (η : ℝ) (x₀ x : V') : ℝ := Real.exp (-η * tdist n x₀ x)

theorem two_sided {a b y : ℝ} (ha : 0 < a) (hb : 0 < b) (hy : 1 ≤ y) (h1 : b ≤ y * a) (h2 : a ≤ y * b) :
    |b - a| ≤ (y - 1) * a ∧ |b - a| ≤ (y - 1) * b := by
  have hy0 : 0 < y := by linarith only [hy]
  have key {a b : ℝ} (ha : 0 < a) (h2 : a ≤ y * b) : a - b ≤ (y - 1) * a := by
    by_contra hc
    push_neg at hc
    have := mul_pos hy0 (sub_pos.2 hc)
    nlinarith only [this, h2, mul_nonneg ha.le (sq_nonneg (y - 1))]
  constructor
  · rw [abs_le]
    constructor
    · linarith only [key ha h2]
    · linarith only [h1]
  · rw [abs_le]
    constructor
    · linarith only [h2]
    · linarith only [key hb h1]

theorem expW_vary (η : ℝ) (hη : 0 ≤ η) (x₀ x : V') (μ : Fin 4) :
    |expW n η x₀ (step (2 * n) x μ) - expW n η x₀ x| ≤ (Real.exp η - 1) * expW n η x₀ x ∧
      |expW n η x₀ (step (2 * n) x μ) - expW n η x₀ x| ≤
        (Real.exp η - 1) * expW n η x₀ (step (2 * n) x μ) := by
  obtain ⟨d₁, d₂⟩ := tdist_step n x₀ x μ
  have c₁ : (tdist n x₀ (step (2 * n) x μ) : ℝ) ≤ tdist n x₀ x + 1 := by exact_mod_cast d₁
  have c₂ : (tdist n x₀ x : ℝ) ≤ tdist n x₀ (step (2 * n) x μ) + 1 := by exact_mod_cast d₂
  refine two_sided (Real.exp_pos _) (Real.exp_pos _) (Real.one_le_exp hη) ?_ ?_
  · unfold expW
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith only [c₂, hη])
  · unfold expW
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith only [c₁, hη])

/-- **Diffusive locality of the flow, uniform in the lattice size.** For `0 < η ≤ 1` the squared defect of one
plaquette at flow time `t` is bounded by the initial squared defects, weighted by `exp(-η · distance)`, up to the
factor `exp(144 η² t)`. The choice `η = 1/√t` gives a range `√t` and a constant factor. -/
theorem flow_locality (U : Configuration V' Q) (p₀ : PlaquetteIndex (2 * n)) {η t : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (ht : 0 ≤ t) :
    term n Q (spatialTwist n) character 2 (wf n t U) p₀ +
        (1 / 2) * ∫ s in (0 : ℝ)..t, wForce n (expW n η p₀.1) (wf n s U) ≤
      Real.exp (144 * η ^ 2 * t) *
        ∑ p, Real.exp (-η * tdist n p₀.1 p.1) * term n Q (spatialTwist n) character 2 U p := by
  set w := expW n η p₀.1 with hw
  have hw0 (x : V') : 0 ≤ w x := (Real.exp_pos _).le
  set κ := Real.exp η - 1 with hκ
  have hκ0 : 0 ≤ κ := sub_nonneg.2 (Real.one_le_exp hη.le)
  have hle := local_energy n U w κ hκ0 hw0 (fun x μ => expW_vary n η hη.le p₀.1 x μ) ht
  -- The constant.
  have hexp : Real.exp η ≤ 1 + 2 * η := by
    have h := Real.abs_exp_sub_one_sub_id_le (x := η) (by rw [abs_of_pos hη]; exact hη1)
    have h' := (abs_le.1 h).2
    nlinarith only [h', hη, hη1]
  have hκ2 : κ ≤ 2 * η := by simp only [hκ]; linarith only [hexp]
  have hκ3 : 1 + κ ≤ 3 := by simp only [hκ]; linarith only [hexp, hη1]
  have hC : 12 * κ ^ 2 * (1 + κ) ≤ 144 * η ^ 2 := by
    have h1 : κ ^ 2 ≤ (2 * η) ^ 2 := pow_le_pow_left₀ hκ0 hκ2 2
    have h2 : κ ^ 2 * (1 + κ) ≤ (2 * η) ^ 2 * 3 :=
      mul_le_mul h1 hκ3 (by linarith only [hκ0]) (by positivity)
    nlinarith only [h2]
  have hA0 := wAction_nonneg n w hw0 U
  have hexpC : Real.exp (12 * κ ^ 2 * (1 + κ) * t) ≤ Real.exp (144 * η ^ 2 * t) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hC ht)
  have hw1 : w p₀.1 = 1 := by simp [hw, expW, tdist_self]
  have hsingle : term n Q (spatialTwist n) character 2 (wf n t U) p₀ ≤ wAction n w (wf n t U) := by
    have := Finset.single_le_sum (f := fun p => w p.1 * term n Q (spatialTwist n) character 2 (wf n t U) p)
      (fun p _ => mul_nonneg (hw0 _) (term_nonneg n _ p)) (Finset.mem_univ p₀)
    simpa only [hw1, one_mul] using this
  calc _ ≤ wAction n w (wf n t U) + (1 / 2) * ∫ s in (0 : ℝ)..t, wForce n w (wf n s U) := by
        linarith only [hsingle]
    _ ≤ _ := hle
    _ ≤ Real.exp (144 * η ^ 2 * t) * wAction n w U := mul_le_mul_of_nonneg_right hexpC hA0
    _ = _ := rfl

/-! ### Reflection -/

/-- Quaternion conjugation as an isometry. -/
def starIso : ℍ[ℝ] ≃ₗᵢ[ℝ] ℍ[ℝ] where
  toFun := star
  invFun := star
  map_add' := star_add
  map_smul' c x := Quaternion.star_smul c x
  left_inv := star_star
  right_inv := star_star
  norm_map' := norm_star

/-- The reflection, as a symmetry of the ambient space. -/
def reflA (e : Edge V') : ℍ[ℝ] ≃ₗᵢ[ℝ] ℍ[ℝ] :=
  if e.2.2.val = 0 then starIso else LinearIsometryEquiv.refl ℝ ℍ[ℝ]

theorem emb_reflect (U : Configuration V' Q) :
    emb (reflectConfiguration (2 * n) Q U) = permIso (edgeEquiv (2 * n)) (reflA n) (emb U) := by
  refine PiLp.ext fun e => ?_
  rw [permIso_apply, emb_apply, emb_apply]
  unfold reflectConfiguration reflA
  split_ifs <;> rfl

theorem action_reflect (U : Configuration V' Q) :
    actionOne n (reflectConfiguration (2 * n) Q U) = actionOne n U := by
  unfold actionOne action
  congr 1
  have hr (p : PlaquetteIndex (2 * n)) :
      term n Q (spatialTwist n) character 2 U (reflectPlaquette (2 * n) p) =
        term n Q (spatialTwist n) character 2 (reflectConfiguration (2 * n) Q U) p := by
    unfold term
    rw [reflected_plaquette_character (2 * n) Q character WilsonSingleLinkStaples.character_classFunction
      WilsonSingleLinkStaples.character_inverse_re U p, spatialTwist_invariant n p]
    rfl
  simp only [← hr]
  exact Equiv.sum_comp (reflectPlaquette_involutive (2 * n)).toPerm
    (fun p => term n Q (spatialTwist n) character 2 U p)

/-- **Reflection covariance of the flow.** The flow commutes with the time reflection of the
reflection-positivity argument. The flow is not local, so a flowed observable on the positive half is not
supported there, and this does not by itself give reflection positivity for flowed observables. -/
theorem wf_reflect (t : ℝ) (U : Configuration V' Q) :
    wf n t (reflectConfiguration (2 * n) Q U) = reflectConfiguration (2 * n) Q (wf n t U) := by
  apply emb_injective
  rw [emb_reflect]
  refine wflow_symm (contDiff_actA n) (edgeEquiv (2 * n)) (reflA n) (fun x hx => ?_) t U _ (emb_reflect n U)
  have e : x = emb (ofSph x hx) := rfl
  rw [e, ← emb_reflect, actA_emb, actA_emb, action_reflect]

/-! ### Translations, up to a center flip -/

/-- Translation of the links by one step in direction `κ`. -/
def shiftE (κ : Fin 4) : Edge V' ≃ Edge V' :=
  (edgeCoordinates (2 * n)).trans
    ((Equiv.prodCongr (stepEquiv κ) (Equiv.refl _)).trans (edgeCoordinates (2 * n)).symm)

theorem shiftE_ed (κ : Fin 4) (x : V') (μ : Fin 4) : shiftE n κ (ed n x μ) = ed n (step (2 * n) x κ) μ := rfl

open Classical in
/-- The links whose sign moves the twist stack one step in direction `κ`. Translations in directions `0` and `3`
preserve the twist and need no sign. -/
def sgnCond (κ : Fin 4) (x : V') (μ : Fin 4) : Prop :=
  ((κ = 1 ∧ μ = 2) ∨ (κ = 2 ∧ μ = 1)) ∧ x 1 = 0 ∧ x 2 = 0

open Classical in
def sgn (κ : Fin 4) (e : Edge V') : Q := if sgnCond n κ e.1 e.2.2.val then ω else 1

open Classical in
def rs (κ : Fin 4) (x : V') (μ : Fin 4) : ℝ := if sgnCond n κ x μ then -1 else 1

theorem sgn_coe (κ : Fin 4) (x : V') (μ : Fin 4) : ((sgn n κ (ed n x μ) : Q) : ℍ[ℝ]) = (rs n κ x μ : ℍ[ℝ]) := by
  classical
  change ((if sgnCond n κ x μ then ω else 1 : Q) : ℍ[ℝ]) = ((if sgnCond n κ x μ then -1 else 1 : ℝ) : ℍ[ℝ])
  split_ifs
  · simp [ω_coe]
  · simp

/-- The sign moves the twist. -/
theorem twist_sign (κ : Fin 4) (x : V') (μ ν : Fin 4) (h : μ < ν) :
    spatialTwist n (x, ⟨(μ, ν), h⟩) * (rs n κ x μ * rs n κ (step (2 * n) x μ) ν * rs n κ (step (2 * n) x ν) μ *
      rs n κ x ν) = spatialTwist n (step (2 * n) x κ, ⟨(μ, ν), h⟩) := by
  classical
  rw [spatialTwist_eq, spatialTwist_eq]
  unfold twistExp rs sgnCond
  have hs (y : V') (a b : Fin 4) : step (2 * n) y a b = y b + if a = b then 1 else 0 := by
    simp [step, Pi.single_apply, eq_comm]
  simp only [hs]
  fin_cases κ <;> fin_cases μ <;> fin_cases ν <;> first | exact absurd h (by decide) | skip
  all_goals
    simp (decide := true) only [Fin.mk_zero, Fin.mk_one, Fin.reduceFinMk, zero_add, Nat.reduceAdd, add_zero, if_true, if_false,
      Fin.isValue, true_and, false_and, and_false, and_true, or_false, false_or, reduceCtorEq, one_ne_zero, zero_ne_one]
  all_goals (try split_ifs) <;> (try norm_num) <;> (try simp_all)

/-- Translation by one step, with the compensating center flip. -/
def Rκ (κ : Fin 4) (U : Configuration V' Q) : Configuration V' Q :=
  fun e => sgn n κ e * U (shiftE n κ e)

def Tκ (κ : Fin 4) : Amb (Edge V') ≃ₗᵢ[ℝ] Amb (Edge V') :=
  permIso (shiftE n κ) fun e => mulIso (sgn n κ e) 1

theorem emb_Rκ (κ : Fin 4) (U : Configuration V' Q) : emb (Rκ n κ U) = Tκ n κ (emb U) := by
  refine PiLp.ext fun e => ?_
  rw [Tκ, permIso_apply]
  change ((sgn n κ e * U (shiftE n κ e) : Q) : ℍ[ℝ]) = ((sgn n κ e : Q) : ℍ[ℝ]) * (U (shiftE n κ e) : ℍ[ℝ]) * ((1 : Q) : ℍ[ℝ])
  have : ((1 : Q) : ℍ[ℝ]) = 1 := rfl
  rw [this, mul_one]
  rfl

theorem sign_four (r₁ r₂ r₃ r₄ : ℝ) (y₁ y₂ y₃ y₄ : ℍ[ℝ]) :
    ((r₁ : ℍ[ℝ]) * y₁) * ((r₂ : ℍ[ℝ]) * y₂) * star ((r₃ : ℍ[ℝ]) * y₃) * star ((r₄ : ℍ[ℝ]) * y₄) =
      (r₁ * r₂ * r₃ * r₄) • (y₁ * y₂ * star y₃ * star y₄) := by
  simp only [Quaternion.coe_mul_eq_smul, Quaternion.star_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  ring

/-- A plaquette term of the translated field is the term of the original field at the translated plaquette. -/
theorem term_Rκ (κ : Fin 4) (U : Configuration V' Q) (x : V') (P : Plane) :
    term n Q (spatialTwist n) character 2 (Rκ n κ U) (x, P) =
      term n Q (spatialTwist n) character 2 U (step (2 * n) x κ, P) := by
  rcases P with ⟨⟨μ, ν⟩, h⟩
  rw [← termA_emb, ← termA_emb]
  unfold termA
  have hP : plaqA n (emb (Rκ n κ U)) (x, ⟨(μ, ν), h⟩) =
      (rs n κ x μ * rs n κ (step (2 * n) x μ) ν * rs n κ (step (2 * n) x ν) μ * rs n κ x ν) •
        plaqA n (emb U) (step (2 * n) x κ, ⟨(μ, ν), h⟩) := by
    have e₁ (y : V') (lam : Fin 4) : emb (Rκ n κ U) (ed n y lam) =
        (rs n κ y lam : ℍ[ℝ]) * emb U (ed n (step (2 * n) y κ) lam) := by
      rw [← sgn_coe]
      rfl
    simp only [plaqA, e₁]
    rw [sign_four, step_comm (2 * n) x μ κ, step_comm (2 * n) x ν κ]
  rw [hP, Quaternion.re_smul, smul_eq_mul, ← twist_sign n κ x μ ν h]
  ring

theorem sum_plaq (f : PlaquetteIndex (2 * n) → ℝ) : ∑ p, f p = ∑ x : V', ∑ P : Plane, f (x, P) :=
  Fintype.sum_prod_type _

theorem action_Rκ (κ : Fin 4) (U : Configuration V' Q) : actionOne n (Rκ n κ U) = actionOne n U := by
  unfold actionOne action
  congr 1
  rw [sum_plaq, sum_plaq]
  simp only [term_Rκ]
  exact Equiv.sum_comp (stepEquiv (N := 2 * n) κ) fun y =>
    ∑ P : Plane, term n Q (spatialTwist n) character 2 U (y, P)

/-- **Translation covariance of the flow, up to the center flip.** -/
theorem wf_Rκ (κ : Fin 4) (t : ℝ) (U : Configuration V' Q) : wf n t (Rκ n κ U) = Rκ n κ (wf n t U) := by
  apply emb_injective
  rw [emb_Rκ]
  refine wflow_symm (contDiff_actA n) (shiftE n κ) (fun e => mulIso (sgn n κ e) 1) (fun x hx => ?_) t U _
    (emb_Rκ n κ U)
  have e : x = emb (ofSph x hx) := rfl
  change actA n (Tκ n κ x) = _
  rw [e, ← emb_Rκ, actA_emb, actA_emb, action_Rκ]

theorem field_Rκ (κ : Fin 4) (U : Configuration V' Q) (x : V') (μ : Fin 4) :
    ‖field (actA n) (emb (Rκ n κ U)) (ed n x μ)‖ = ‖field (actA n) (emb U) (ed n (step (2 * n) x κ) μ)‖ := by
  rw [emb_Rκ]
  have := field_symm (contDiff_actA n) (shiftE n κ) (fun e => mulIso (sgn n κ e) 1) (fun y hy => ?_) (emb_sph U)
  · change field (actA n) (Tκ n κ (emb U)) = Tκ n κ _ at this
    rw [this, Tκ, permIso_apply, LinearIsometryEquiv.norm_map, shiftE_ed]
  · have e : y = emb (ofSph y hy) := rfl
    change actA n (Tκ n κ y) = _
    rw [e, ← emb_Rκ, actA_emb, actA_emb, action_Rκ]

/-- `Rκ` preserves Haar measure on configurations. -/
theorem Rκ_preserving (κ : Fin 4) :
    MeasurePreserving (Rκ n κ) (referenceMeasure Q V') (referenceMeasure Q V') := by
  classical
  have h₁ : MeasurePreserving (fun (U : Configuration V' Q) e => U (shiftE n κ e))
      (referenceMeasure Q V') (referenceMeasure Q V') := by
    have h := measurePreserving_piCongrLeft (fun _ : Edge V' => compactHaar Q) (shiftE n κ).symm
    convert h using 1
    funext U e
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  have h₂ : MeasurePreserving (fun (U : Configuration V' Q) e => sgn n κ e * U e)
      (referenceMeasure Q V') (referenceMeasure Q V') :=
    measurePreserving_pi (μ := fun _ : Edge V' => compactHaar Q) (fun _ => compactHaar Q)
      (f := fun e q => sgn n κ e * q) fun e => measurePreserving_mul_left _ _
  exact h₂.comp h₁

/-- A function on the torus invariant under all unit steps is constant. -/
theorem const_of_step (g : V' → ℝ) (hg : ∀ κ x, g (step (2 * n) x κ) = g x) (x y : V') : g y = g x := by
  haveI : NeZero (2 * n) := ⟨by have := NeZero.ne n; omega⟩
  have hk (κ : Fin 4) (k : ℕ) (z : V') : g (z + k • Pi.single κ (1 : ZMod (2 * n))) = g z := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [succ_nsmul, ← add_assoc]
      exact (hg κ _).trans ih
  have hc (κ : Fin 4) (c : ZMod (2 * n)) (z : V') : g (z + Pi.single κ c) = g z := by
    have e : (Pi.single κ c : V') = c.val • Pi.single κ (1 : ZMod (2 * n)) := by
      funext i
      by_cases hi : i = κ
      · subst hi
        simp
      · simp [Pi.single_apply, hi]
    rw [e]
    exact hk κ _ z
  have hy : y = x + Pi.single 0 (y 0 - x 0) + Pi.single 1 (y 1 - x 1) + Pi.single 2 (y 2 - x 2) +
      Pi.single 3 (y 3 - x 3) := by
    funext i
    fin_cases i <;> simp
  rw [hy, hc, hc, hc, hc]

/-! ### Flowed observables and the twisted law -/

section Law
variable (β : ℝ)

theorem integrable_law {f : Configuration V' Q → ℝ} (hf : Continuous f) : Integrable f (twistedLaw n β) := by
  haveI : IsProbabilityMeasure (twistedLaw n β) :=
    law_probability n Q (spatialTwist n) character WilsonSingleLinkStaples.character_continuous β 2
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem continuous_term' (p : PlaquetteIndex (2 * n)) :
    Continuous fun U : Configuration V' Q => term n Q (spatialTwist n) character 2 U p :=
  continuous_term n Q (spatialTwist n) character WilsonSingleLinkStaples.character_continuous 2 p

/-- The mean flowed action does not exceed the mean action. -/
theorem law_action_wf {t : ℝ} (ht : 0 ≤ t) :
    ∫ U, actionOne n (wf n t U) ∂twistedLaw n β ≤ ∫ U, actionOne n U ∂twistedLaw n β :=
  integral_mono (integrable_law n β ((continuous_actionOne n).comp (continuous_wf_right n t)))
    (integrable_law n β (continuous_actionOne n)) fun U => by
      have := action_wf_antitone n U ht
      simpa only [wf_zero] using this

/-- The tail of the flowed action is no worse than the tail in `action_tail`. -/
theorem law_action_wf_tail {t s : ℝ} (ht : 0 ≤ t) (hβ : 1 / 32 ≤ β) :
    twistedLaw n β {U | s ≤ actionOne n (wf n t U)} ≤
      ENNReal.ofReal (Real.exp (-β * s) * SU2GaussianMass.cap (24 * β) ^ linkCount n) := by
  refine (measure_mono fun U hU => ?_).trans (action_tail n β s hβ)
  have := action_wf_antitone n U ht
  simp only [wf_zero] at this
  exact (show s ≤ _ from hU).trans this

/-- **Smoothing at the level of the law.** The mean squared force at `t > 0` is at most `(1/t + 96)` times the mean
action dissipated by time `t`. Keeping the dissipated action is what gives this content: with the mean action alone on
the right it would be weaker than `force_static` at every `t > 0` (`law_force_static`). -/
theorem law_force_dissipation {t : ℝ} (ht : 0 < t) :
    ∫ U, forceSq n (wf n t U) ∂twistedLaw n β ≤
      (1 / t + 96) * (∫ U, actionOne n U ∂twistedLaw n β - ∫ U, actionOne n (wf n t U) ∂twistedLaw n β) := by
  have hi0 := integrable_law n β (continuous_actionOne n)
  have hit := integrable_law n β ((continuous_actionOne n).comp (continuous_wf_right n t))
  have e : ∫ U, actionOne n U ∂twistedLaw n β - ∫ U, actionOne n (wf n t U) ∂twistedLaw n β =
      ∫ U, (actionOne n U - actionOne n (wf n t U)) ∂twistedLaw n β := (integral_sub hi0 hit).symm
  rw [e, ← integral_const_mul]
  exact integral_mono (integrable_law n β ((continuous_forceSq n).comp (continuous_wf_right n t)))
    ((hi0.sub hit).const_mul _) fun U => wf_smoothing n U ht

/-- The Gibbs bound. The mean action is at most `links · log cap(24β) / β`, uniformly in the lattice size per
link, by comparing `x` with `exp(x - a) + a - 1`. `TwistedLocalTail.energy_le_log` is stronger for every `β ≥ 1/32`. This
form stays because it needs nothing from that module, and `TwistedLimit` uses its consequences. -/
theorem law_action_le (hβ : 1 / 32 ≤ β) :
    ∫ U, actionOne n U ∂twistedLaw n β ≤ linkCount n * Real.log (SU2GaussianMass.cap (24 * β)) / β := by
  have hβ0 : 0 < β := by linarith only [hβ]
  have hM := SU2GaussianMass.mass_pos (24 * β)
  have hcap := SU2GaussianMass.mass_cap_lower (24 * β) (by linarith only [hβ])
  set M := SU2GaussianMass.mass (24 * β)
  set K := SU2GaussianMass.cap (24 * β)
  have hK : 0 < K := by
    by_contra hc
    push_neg at hc
    nlinarith only [hM, hc, hcap]
  set S := action n Q (spatialTwist n) character β 2 with hS
  have hSc : Continuous S := continuous_action n Q (spatialTwist n) character
    WilsonSingleLinkStaples.character_continuous β 2
  -- The inverse partition function.
  have hZ : (gibbsPartition (Vertex (2 * n)) Q S)⁻¹.toReal ≤ K ^ linkCount n := by
    have hl := partition_lower n β hβ0.le
    have hMp : 0 < M ^ linkCount n := pow_pos hM _
    have hKp : 0 < K ^ linkCount n := pow_pos hK _
    have hprod : 1 ≤ M ^ linkCount n * K ^ linkCount n := by
      rw [← mul_pow]
      exact one_le_pow₀ hcap
    have hne : ENNReal.ofReal (M ^ linkCount n) ≠ 0 := by
      simpa [ENNReal.ofReal_eq_zero] using hMp
    have hle : (gibbsPartition (Vertex (2 * n)) Q S)⁻¹ ≤ (ENNReal.ofReal (M ^ linkCount n))⁻¹ :=
      ENNReal.inv_le_inv.2 hl
    refine (ENNReal.toReal_mono (by simp [hne]) hle).trans ?_
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hMp.le, inv_eq_one_div, div_le_iff₀ hMp]
    linarith only [hprod]
  haveI hprob : IsProbabilityMeasure (twistedLaw n β) :=
    law_probability n Q (spatialTwist n) character WilsonSingleLinkStaples.character_continuous β 2
  -- The exponential moment.
  have hmom : ∫ U, Real.exp (S U) ∂twistedLaw n β ≤ K ^ linkCount n := by
    rw [law_integral]
    have : ∫ U, Real.exp (-action n Q (spatialTwist n) character β 2 U) * Real.exp (S U)
        ∂referenceMeasure Q V' = 1 := by
      have e (U : Configuration V' Q) : Real.exp (-action n Q (spatialTwist n) character β 2 U) * Real.exp (S U) = 1 := by
        rw [← Real.exp_add, hS]
        simp
      simp only [e]
      simp
    rw [this, mul_one]
    exact hZ
  set a : ℝ := linkCount n * Real.log K with ha
  have hpt (U : Configuration V' Q) : S U ≤ Real.exp (-a) * Real.exp (S U) + a - 1 := by
    have := Real.add_one_le_exp (S U - a)
    rw [sub_eq_add_neg, Real.exp_add, mul_comm] at this
    linarith only [this]
  have hexp : Real.exp (-a) * K ^ linkCount n = 1 := by
    have : K ^ linkCount n = Real.exp a := by
      rw [ha, Real.exp_nat_mul, Real.exp_log hK]
    rw [this, ← Real.exp_add]
    simp
  have hexpc : Continuous fun U => Real.exp (S U) := Real.continuous_exp.comp hSc
  have hint : ∫ U, S U ∂twistedLaw n β ≤ a := by
    calc _ ≤ ∫ U, (Real.exp (-a) * Real.exp (S U) + a - 1) ∂twistedLaw n β :=
          integral_mono (integrable_law n β hSc)
            (integrable_law n β ((continuous_const.mul hexpc).add continuous_const |>.sub continuous_const)) hpt
      _ = Real.exp (-a) * ∫ U, Real.exp (S U) ∂twistedLaw n β + a - 1 := by
          have e : (fun U => Real.exp (-a) * Real.exp (S U) + a - 1) =
              fun U => Real.exp (-a) * Real.exp (S U) + (a - 1) := funext fun U => by ring
          simp only [e]
          rw [integral_add ((integrable_law n β hexpc).const_mul _) (integrable_const _), integral_const_mul]
          simp
          ring
      _ ≤ Real.exp (-a) * K ^ linkCount n + a - 1 := by
          have := mul_le_mul_of_nonneg_left hmom (Real.exp_pos (-a)).le
          linarith only [this]
      _ = a := by rw [hexp]; ring
  have hSeq : (fun U => S U) = fun U => β * actionOne n U := funext fun U => action_eq_mul n β U
  rw [hSeq, integral_const_mul] at hint
  rw [le_div_iff₀ hβ0]
  linarith only [hint]

/-- **The mean flowed action per link** is at most `log cap(24β) / β`, for every flow time and every size. -/
theorem law_action_wf_le {t : ℝ} (ht : 0 ≤ t) (hβ : 1 / 32 ≤ β) :
    ∫ U, actionOne n (wf n t U) ∂twistedLaw n β ≤ linkCount n * Real.log (SU2GaussianMass.cap (24 * β)) / β :=
  (law_action_wf n β ht).trans (law_action_le n β hβ)

/-! ### From global means to local means -/

/-- The twisted law is invariant under translation with the compensating flip. -/
theorem law_Rκ (κ : Fin 4) {f : Configuration V' Q → ℝ} (hf : Continuous f) :
    ∫ U, f (Rκ n κ U) ∂twistedLaw n β = ∫ U, f U ∂twistedLaw n β := by
  rw [law_integral, law_integral]
  congr 1
  set S := action n Q (spatialTwist n) character β 2 with hS
  have hSc : Continuous S := continuous_action n Q (spatialTwist n) character
    WilsonSingleLinkStaples.character_continuous β 2
  have hinv (U : Configuration V' Q) : S (Rκ n κ U) = S U := by
    rw [hS, action_eq_mul, action_eq_mul, action_Rκ]
  have hg : Continuous fun U => Real.exp (-S U) * f U := (Real.continuous_exp.comp hSc.neg).mul hf
  have hp := Rκ_preserving n κ
  have hm := integral_map hp.measurable.aemeasurable (f := fun U => Real.exp (-S U) * f U)
    (μ := referenceMeasure Q V') hg.aestronglyMeasurable
  rw [hp.map_eq] at hm
  rw [hm]
  simp only [hinv]

theorem continuous_termW (t : ℝ) (p : PlaquetteIndex (2 * n)) :
    Continuous fun U : Configuration V' Q => term n Q (spatialTwist n) character 2 (wf n t U) p :=
  (continuous_term' n p).comp (continuous_wf_right n t)

theorem law_term_step (t : ℝ) (P : Plane) (κ : Fin 4) (x : V') :
    ∫ U, term n Q (spatialTwist n) character 2 (wf n t U) (step (2 * n) x κ, P) ∂twistedLaw n β =
      ∫ U, term n Q (spatialTwist n) character 2 (wf n t U) (x, P) ∂twistedLaw n β := by
  rw [← law_Rκ n β κ (continuous_termW n t (x, P))]
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  change _ = term n Q (spatialTwist n) character 2 (wf n t (Rκ n κ U)) (x, P)
  rw [wf_Rκ, term_Rκ]

theorem actionOne_sum (U : Configuration V' Q) :
    actionOne n U = ∑ x : V', ∑ P : Plane, term n Q (spatialTwist n) character 2 U (x, P) := by
  unfold actionOne action
  rw [one_mul, sum_plaq]

theorem card_vertex : ((Fintype.card V' : ℕ) : ℝ) = ((2 * n : ℕ) : ℝ) ^ 4 := by
  haveI : NeZero (2 * n) := ⟨by have := NeZero.ne n; omega⟩
  simp [ZMod.card]

theorem linkCount_vertex : (linkCount n : ℝ) = 4 * (Fintype.card V' : ℕ) := by
  rw [linkCount_eq, card_vertex]
  push_cast
  ring

theorem card_vertex_pos : (0 : ℝ) < (Fintype.card V' : ℕ) := by
  rw [card_vertex]
  have : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by
    have := NeZero.pos n
    exact_mod_cast (by omega : 0 < 2 * n)
  positivity

/-- The mean flowed action is the volume times the local mean, at every site. -/
theorem law_action_wf_eq (t : ℝ) (x₀ : V') :
    ∫ U, actionOne n (wf n t U) ∂twistedLaw n β =
      (Fintype.card V' : ℕ) * ∑ P : Plane, ∫ U, term n Q (spatialTwist n) character 2 (wf n t U) (x₀, P) ∂twistedLaw n β := by
  have hi (x : V') (P : Plane) := integrable_law n β (continuous_termW n t (x, P))
  simp only [actionOne_sum]
  rw [integral_finset_sum _ fun x _ => integrable_finset_sum _ fun P _ => hi x P]
  simp only [integral_finset_sum _ fun P _ => hi _ P]
  have hconst (x : V') (P : Plane) :
      ∫ U, term n Q (spatialTwist n) character 2 (wf n t U) (x, P) ∂twistedLaw n β =
        ∫ U, term n Q (spatialTwist n) character 2 (wf n t U) (x₀, P) ∂twistedLaw n β :=
    const_of_step n (fun y => ∫ U, term n Q (spatialTwist n) character 2 (wf n t U) (y, P) ∂twistedLaw n β)
      (fun κ y => law_term_step n β t P κ y) x₀ x
  simp only [hconst]
  simp

/-- **A local mean bound for flowed plaquettes, uniform in the lattice size and in the flow time.** At every
site and every `t ≥ 0`, the mean squared defects of the six plaquettes based there sum to at most
`4 log cap(24β) / β`. The proof uses only that the flow lowers the action and commutes with translation up to a
center flip. It does not see any decay in `t`, and the flow time plays no role in the bound. -/
theorem law_plaquette_mean_wf {t : ℝ} (ht : 0 ≤ t) (hβ : 1 / 32 ≤ β) (x : V') :
    ∑ P : Plane, ∫ U, term n Q (spatialTwist n) character 2 (wf n t U) (x, P) ∂twistedLaw n β ≤
      4 * Real.log (SU2GaussianMass.cap (24 * β)) / β := by
  have h := law_action_wf_le n β ht hβ
  have hβ0 : 0 < β := by linarith only [hβ]
  rw [law_action_wf_eq n β t x, linkCount_vertex] at h
  have hV := card_vertex_pos n
  have e : (4 * ((Fintype.card V' : ℕ) : ℝ)) * Real.log (SU2GaussianMass.cap (24 * β)) / β =
      ((Fintype.card V' : ℕ) : ℝ) * (4 * Real.log (SU2GaussianMass.cap (24 * β)) / β) := by ring
  rw [e] at h
  exact le_of_mul_le_mul_left h hV

theorem law_term_mean_wf {t : ℝ} (ht : 0 ≤ t) (hβ : 1 / 32 ≤ β) (p : PlaquetteIndex (2 * n)) :
    ∫ U, term n Q (spatialTwist n) character 2 (wf n t U) p ∂twistedLaw n β ≤
      4 * Real.log (SU2GaussianMass.cap (24 * β)) / β := by
  refine le_trans ?_ (law_plaquette_mean_wf n β ht hβ p.1)
  exact Finset.single_le_sum (f := fun P : Plane =>
    ∫ U, term n Q (spatialTwist n) character 2 (wf n t U) (p.1, P) ∂twistedLaw n β)
    (fun P _ => integral_nonneg fun U => term_nonneg n _ _) (Finset.mem_univ p.2)

/-- Markov's inequality for one plaquette, at any flow time. At `t = 0` `TwistedLocalTail.defect_tail` is stronger.
There is no volume factor here. A union over all plaquettes would bring back the factor `N⁴`. -/
theorem law_term_tail {t ε : ℝ} (ht : 0 ≤ t) (hβ : 1 / 32 ≤ β) (p : PlaquetteIndex (2 * n)) (hε : 0 < ε) :
    (twistedLaw n β).real {U | ε ≤ term n Q (spatialTwist n) character 2 (wf n t U) p} ≤
      4 * Real.log (SU2GaussianMass.cap (24 * β)) / β / ε := by
  have h := mul_meas_ge_le_integral_of_nonneg (μ := twistedLaw n β)
    (Eventually.of_forall fun U => term_nonneg n (wf n t U) p) (integrable_law n β (continuous_termW n t p)) ε
  rw [le_div_iff₀ hε, mul_comm]
  exact h.trans (law_term_mean_wf n β ht hβ p)

/-- The bare form, `t = 0`. This is not a new bound: `TwistedLocalTail.defect_sq_le_log` with `log_form_le` implies it. It
stays because `TwistedLimit` uses this form. -/
theorem law_term_mean (hβ : 1 / 32 ≤ β) (p : PlaquetteIndex (2 * n)) :
    ∫ U, term n Q (spatialTwist n) character 2 U p ∂twistedLaw n β ≤
      4 * Real.log (SU2GaussianMass.cap (24 * β)) / β := by
  have := law_term_mean_wf n β le_rfl hβ p
  simpa only [wf_zero] using this

/-! ### The force, link by link -/

/-- The mean squared force on one link at flow time `t`. -/
def linkForce (t : ℝ) (x : V') (μ : Fin 4) : ℝ :=
  ∫ U, ‖field (actA n) (emb (wf n t U)) (ed n x μ)‖ ^ 2 ∂twistedLaw n β

theorem continuous_linkF (t : ℝ) (x : V') (μ : Fin 4) :
    Continuous fun U => ‖field (actA n) (emb (wf n t U)) (ed n x μ)‖ ^ 2 :=
  ((PiLp.continuous_apply 2 _ (ed n x μ)).comp ((contDiff_field (contDiff_actA n)).continuous.comp
    (continuous_emb.comp (continuous_wf_right n t)))).norm.pow 2

theorem linkForce_step (t : ℝ) (μ κ : Fin 4) (x : V') :
    linkForce n β t (step (2 * n) x κ) μ = linkForce n β t x μ := by
  unfold linkForce
  rw [← law_Rκ n β κ (continuous_linkF n t x μ)]
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  change _ = ‖field (actA n) (emb (wf n t (Rκ n κ U))) (ed n x μ)‖ ^ 2
  rw [wf_Rκ, field_Rκ]

theorem law_force_eq (t : ℝ) (x₀ : V') :
    ∫ U, forceSq n (wf n t U) ∂twistedLaw n β = (Fintype.card V' : ℕ) * ∑ μ, linkForce n β t x₀ μ := by
  have hs (V : Configuration V' Q) : forceSq n V = ∑ μ, ∑ x, ‖field (actA n) (emb V) (ed n x μ)‖ ^ 2 := by
    unfold forceSq
    rw [norm_sq_amb, sum_edges]
  simp only [hs]
  have hi (x : V') (μ : Fin 4) := integrable_law n β (continuous_linkF n t x μ)
  rw [integral_finset_sum _ fun μ _ => integrable_finset_sum _ fun x _ => hi x μ]
  simp only [integral_finset_sum _ fun x _ => hi x _]
  have hconst (x : V') (μ : Fin 4) : linkForce n β t x μ = linkForce n β t x₀ μ :=
    const_of_step n (fun y => linkForce n β t y μ) (fun κ y => linkForce_step n β t μ κ y) x₀ x
  change ∑ μ, ∑ x, linkForce n β t x μ = _
  simp only [hconst]
  simp [Finset.mul_sum]

/-! ### Rotations at one link -/

theorem continuous_rot : Continuous fun U : Configuration V' Q => rot (actA n) (emb U) := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun e => ?_)
  exact ((PiLp.continuous_apply 2 _ e).comp ((contDiff_field (contDiff_actA n)).continuous.comp
    continuous_emb)).mul (continuous_star.comp ((PiLp.continuous_apply 2 _ e).comp continuous_emb))

/-- The rate of the action at coupling `β` along a rotation. -/
theorem rate_coords {ξ : Amb (Edge V')} (hξ : ∀ e, star (ξ e) = -ξ e) (U : Configuration V' Q) :
    deriv (SAt n β (coords n ξ) U) 0 = β * -⟪rot (actA n) (emb U), ξ⟫ := by
  have hfun : SAt n β (coords n ξ) U = fun s => β * actA n (expCurve ξ (emb U) s) := by
    funext s
    conv_rhs => rw [← rotOf_coords n hξ, expCurve_flow, actA_emb]
    exact action_eq_mul n β _
  have h2 := hasDerivAt_comp_S (contDiff_actA n) (expCurve_d0 ξ (emb U))
  rw [expCurve_zero, inner_grad_lmul (emb_sph U) hξ] at h2
  rw [hfun]
  exact (h2.const_mul β).deriv

open Classical in
/-- A unit rotation on one link, in one colour. -/
def unitDir (e : Edge V') (a : Fin 3) : Amb (Edge V') := WithLp.toLp 2 (Pi.single e (basis a))

theorem basis_star (a : Fin 3) : star (basis a) = -basis a := by
  fin_cases a <;> ext <;> simp [basis]

theorem basis_norm (a : Fin 3) : ‖basis a‖ ^ 2 = 1 := by
  rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
  fin_cases a <;> simp [basis]

theorem unitDir_star (e₀ : Edge V') (a : Fin 3) (e : Edge V') :
    star (unitDir n e₀ a e) = -unitDir n e₀ a e := by
  classical
  change star ((Pi.single e₀ (basis a) : Edge V' → ℍ[ℝ]) e) = -(Pi.single e₀ (basis a) : Edge V' → ℍ[ℝ]) e
  by_cases h : e = e₀
  · subst h
    simp [basis_star]
  · simp [Pi.single_apply, h]

theorem unitDir_norm (e₀ : Edge V') (a : Fin 3) : ‖unitDir n e₀ a‖ ^ 2 = 1 := by
  classical
  rw [norm_sq_amb, Finset.sum_eq_single e₀]
  · change ‖(Pi.single e₀ (basis a) : Edge V' → ℍ[ℝ]) e₀‖ ^ 2 = 1
    simp [basis_norm]
  · intro e _ h
    change ‖(Pi.single e₀ (basis a) : Edge V' → ℍ[ℝ]) e‖ ^ 2 = 0
    simp [Pi.single_apply, h]
  · simp

theorem inner_unitDir (y : Amb (Edge V')) (e₀ : Edge V') (a : Fin 3) :
    ⟪y, unitDir n e₀ a⟫ = ⟪y e₀, basis a⟫ := by
  classical
  rw [inner_amb, Finset.sum_eq_single e₀]
  · change ⟪y e₀, (Pi.single e₀ (basis a) : Edge V' → ℍ[ℝ]) e₀⟫ = _
    simp
  · intro e _ h
    change ⟪y e, (Pi.single e₀ (basis a) : Edge V' → ℍ[ℝ]) e⟫ = 0
    simp [Pi.single_apply, h]
  · simp

theorem norm_sq_of_re {q : ℍ[ℝ]} (h : q.re = 0) : ‖q‖ ^ 2 = ∑ a, ⟪q, basis a⟫ ^ 2 := by
  rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def', Fin.sum_univ_three, h]
  simp [Quaternion.inner_def, basis]

theorem forceSq_coords (U : Configuration V' Q) :
    forceSq n U = ∑ e, ∑ a, ⟪rot (actA n) (emb U), unitDir n e a⟫ ^ 2 := by
  unfold forceSq
  rw [norm_sq_amb]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← norm_rot (emb_sph U), norm_sq_of_re (re_of_star (rot_star (emb U) e))]
  simp only [inner_unitDir]

end Law

/-! ### Static bounds on the force -/

/-- `‖rot‖² = forceSq`. -/
theorem forceSq_eq_rot (U : Configuration V' Q) : forceSq n U = ‖rot (actA n) (emb U)‖ ^ 2 := by
  unfold forceSq
  rw [norm_sq_amb, norm_sq_amb]
  exact Finset.sum_congr rfl fun e _ => by rw [norm_rot (emb_sph U)]

/-- **The force is at most `96` times the action, at every field.** No flow enters. -/
theorem force_static (U : Configuration V' Q) : forceSq n U ≤ 96 * actionOne n U := by
  set ρ := rot (actA n) (emb U) with hρ
  have hstar : ∀ e, star (ρ e) = -ρ e := rot_star (emb U)
  have h2 := sum_Ap n hstar U
  have hF : forceSq n U = ‖ρ‖ ^ 2 := forceSq_eq_rot n U
  rw [real_inner_self_eq_norm_sq, ← hρ, ← hF] at h2
  set X := coords n ρ with hX
  set L := linkValue (2 * n) Q U with hL
  have hA : (∑ p, Ap n X p U) ^ 2 ≤
      (∑ p : PlaquetteIndex (2 * n), linkSum n X p.1 p.2.1.1 p.2.1.2 ^ 2) *
        (∑ p : PlaquetteIndex (2 * n), defect L p.2.1.1 p.2.1.2 p.1 ^ 2) := by
    have h1 : |∑ p, Ap n X p U| ≤ ∑ p : PlaquetteIndex (2 * n),
        linkSum n X p.1 p.2.1.1 p.2.1.2 * defect L p.2.1.1 p.2.1.2 p.1 :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun p _ => TwistedLocalTail.Ap_abs_le_defect n X p U)
    calc (∑ p, Ap n X p U) ^ 2 = |∑ p, Ap n X p U| ^ 2 := (sq_abs _).symm
      _ ≤ (∑ p : PlaquetteIndex (2 * n), linkSum n X p.1 p.2.1.1 p.2.1.2 * defect L p.2.1.1 p.2.1.2 p.1) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hS : ∑ p : PlaquetteIndex (2 * n), defect L p.2.1.1 p.2.1.2 p.1 ^ 2 = actionOne n U := by
    rw [TwistedNearFlat.actionOne_eq]
    rfl
  have hLs : ∑ p : PlaquetteIndex (2 * n), linkSum n X p.1 p.2.1.1 p.2.1.2 ^ 2 ≤ 24 * forceSq n U := by
    have h3 : ∑ p : PlaquetteIndex (2 * n), linkSq n X p.1 p.2.1.1 p.2.1.2 = 6 * ∑ a, ∑ μ, ‖X a μ‖ ^ 2 :=
      link_count n X
    rw [coords_norm n hstar, ← hF] at h3
    calc _ ≤ ∑ p : PlaquetteIndex (2 * n), 4 * linkSq n X p.1 p.2.1.1 p.2.1.2 :=
          Finset.sum_le_sum fun p _ => linkSum_sq n X _ _ _
      _ = _ := by rw [← Finset.mul_sum, h3]; ring
  rw [hS] at hA
  have hS0 : 0 ≤ actionOne n U := by
    rw [← hS]; exact Finset.sum_nonneg fun p _ => sq_nonneg _
  have hF0 : 0 ≤ forceSq n U := by rw [hF]; positivity
  rcases hF0.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have hmul : forceSq n U ^ 2 ≤ 96 * forceSq n U * actionOne n U := by
      have hsq : forceSq n U ^ 2 = 4 * (∑ p, Ap n X p U) ^ 2 := by rw [← h2]; ring
      rw [hsq]
      have := mul_le_mul_of_nonneg_right hLs hS0
      nlinarith only [hA, this]
    have : forceSq n U * forceSq n U ≤ forceSq n U * (96 * actionOne n U) := by nlinarith only [hmul]
    exact le_of_mul_le_mul_left this hpos

/-- Each link lies in two plaquettes of each of three planes. -/
theorem count_four (g : V' → Fin 4 → ℝ) :
    ∑ p : PlaquetteIndex (2 * n), (g p.1 p.2.1.1 + g (step (2 * n) p.1 p.2.1.1) p.2.1.2 +
      g (step (2 * n) p.1 p.2.1.2) p.2.1.1 + g p.1 p.2.1.2) = 6 * ∑ μ, ∑ x, g x μ := by
  let M : Fin 4 → ℝ := fun μ => ∑ x, g x μ
  have hpl (μ ν : Fin 4) : ∑ x, (g x μ + g (step (2 * n) x μ) ν + g (step (2 * n) x ν) μ + g x ν) =
      2 * M μ + 2 * M ν := by
    simp only [Finset.sum_add_distrib]
    rw [sum_step (fun y => g y ν) μ, sum_step (fun y => g y μ) ν]
    change M μ + M ν + M μ + M ν = _
    ring
  have hL : ∑ p : PlaquetteIndex (2 * n), (g p.1 p.2.1.1 + g (step (2 * n) p.1 p.2.1.1) p.2.1.2 +
      g (step (2 * n) p.1 p.2.1.2) p.2.1.1 + g p.1 p.2.1.2) = ∑ d : Plane, (2 * M d.1.1 + 2 * M d.1.2) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ => hpl d.1.1 d.1.2
  have hP : ∑ d : Plane, (2 * M d.1.1 + 2 * M d.1.2) = ∑ μ, ∑ ν, if μ < ν then 2 * M μ + 2 * M ν else 0 :=
    plane_sum (fun μ ν => 2 * M μ + 2 * M ν)
  rw [hL, hP]
  change _ = 6 * ∑ μ, M μ
  simp (decide := true) only [Fin.sum_univ_four, if_true, if_false]
  ring

theorem re_four (A B C D : ℍ[ℝ]) (hA : A.re = 0) (hB : B.re = 0) (hC : C.re = 0) (hD : D.re = 0) :
    (A + B + C + D).re = 0 := by
  simp [hA, hB, hC, hD]

theorem Zp_re_zero (L : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (p : PlaquetteIndex (2 * n)) :
    (Zp n L X p).re = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := Y_re n L X p.1 p.2.1.1 p.2.1.2
  have e : Zp n L X p = (plaqOf n L X p.1 p.2.1.1 p.2.1.2).Y₁ + (plaqOf n L X p.1 p.2.1.1 p.2.1.2).Y₂ +
      (plaqOf n L X p.1 p.2.1.1 p.2.1.2).Y₃ + (plaqOf n L X p.1 p.2.1.1 p.2.1.2).Y₄ := rfl
  rw [e]
  exact re_four _ _ _ _ h1 h2 h3 h4

theorem plaqC_norm (L : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (x : V') (μ ν : Fin 4) :
    ‖plaqC n L X x μ ν‖ = 1 := by
  unfold plaqC
  rw [norm_smul, unit_norm]
  split_ifs <;> simp

/-- The rate of one plaquette is at most the sum of the link norms. -/
theorem Ap_abs_le_linkSum (X : Fin 3 → Fin 4 → Section (2 * n)) (p : PlaquetteIndex (2 * n)) (U : Configuration V' Q) :
    |Ap n X p U| ≤ linkSum n X p.1 p.2.1.1 p.2.1.2 := by
  set L := linkValue (2 * n) Q U
  have h1 : |Ap n X p U| ≤ ‖Zp n L X p * plaqC n L X p.1 p.2.1.1 p.2.1.2‖ := re_abs_le _
  rw [norm_mul, plaqC_norm, mul_one] at h1
  refine h1.trans ?_
  rw [← plaq_norms]
  exact norm_add₄_le

/-- **Each link carries force at most `12`, at every field.** The rotation at one link is a rate of the six plaquettes
through it, and each contributes at most `2`. -/
theorem link_field_le (U : Configuration V' Q) (e₀ : Edge V') : ‖field (actA n) (emb U) e₀‖ ≤ 12 := by
  classical
  rw [← norm_rot (emb_sph U)]
  set ρ := rot (actA n) (emb U) with hρ
  have hρs : ∀ e, star (ρ e) = -ρ e := rot_star (emb U)
  set ξ : Amb (Edge V') := WithLp.toLp 2 (Pi.single e₀ (ρ e₀)) with hξ
  have hξa (e : Edge V') : ξ e = if e = e₀ then ρ e₀ else 0 := by
    simp [hξ, Pi.single_apply]
  have hstar : ∀ e, star (ξ e) = -ξ e := by
    intro e
    rw [hξa]
    split_ifs
    · exact hρs e₀
    · simp
  have h2 := sum_Ap n hstar U
  have hin : ⟪ρ, ξ⟫ = ‖ρ e₀‖ ^ 2 := by
    rw [inner_amb, Finset.sum_eq_single e₀ (fun e _ he => by simp [hξa, he]) (fun h => absurd (Finset.mem_univ _) h),
      hξa, if_pos rfl, real_inner_self_eq_norm_sq]
  rw [hin] at h2
  set X := coords n ξ with hX
  have hsum : ∑ μ, ∑ x, ‖imag X μ x‖ = ‖ρ e₀‖ := by
    have hg : ∑ e, ‖ξ e‖ = ‖ρ e₀‖ := by
      rw [Finset.sum_eq_single e₀ (fun e _ he => by simp [hξa, he]) (fun h => absurd (Finset.mem_univ _) h),
        hξa, if_pos rfl]
    rw [← hg, sum_edges]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun x _ => by rw [imag_coords n hstar]
  have hcount := count_four n (fun x μ => ‖imag X μ x‖)
  have hle : ‖ρ e₀‖ ^ 2 ≤ 2 * (6 * ‖ρ e₀‖) := by
    rw [← h2, ← hsum, ← hcount]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact (Finset.sum_le_sum fun p _ => le_abs_self _).trans
      (Finset.sum_le_sum fun p _ => Ap_abs_le_linkSum n X p U)
  have hn := norm_nonneg (ρ e₀)
  rcases hn.eq_or_lt with h0 | hpos
  · rw [← h0]
    norm_num
  · have : ‖ρ e₀‖ * ‖ρ e₀‖ ≤ ‖ρ e₀‖ * 12 := by nlinarith only [hle]
    exact le_of_mul_le_mul_left this hpos

/-- The force at one site is at most `576`, at every field. -/
theorem site_force_le (U : Configuration V' Q) (x : V') : ∑ μ, ‖field (actA n) (emb U) (ed n x μ)‖ ^ 2 ≤ 576 := by
  calc _ ≤ ∑ _μ : Fin 4, (144 : ℝ) := Finset.sum_le_sum fun μ _ => by
        have := link_field_le n U (ed n x μ)
        have h0 := norm_nonneg (field (actA n) (emb U) (ed n x μ))
        nlinarith only [this, h0]
    _ = 576 := by norm_num

open Classical in
/-- How many times the link `e₀` occurs in the plaquette `p`. -/
def inc (e₀ : Edge V') (p : PlaquetteIndex (2 * n)) : ℝ :=
  (if ed n p.1 p.2.1.1 = e₀ then 1 else 0) + (if ed n (step (2 * n) p.1 p.2.1.1) p.2.1.2 = e₀ then 1 else 0) +
    (if ed n (step (2 * n) p.1 p.2.1.2) p.2.1.1 = e₀ then 1 else 0) + (if ed n p.1 p.2.1.2 = e₀ then 1 else 0)

theorem inc_nonneg (e₀ : Edge V') (p : PlaquetteIndex (2 * n)) : 0 ≤ inc n e₀ p := by
  unfold inc
  split_ifs <;> norm_num

/-- Each link lies in six plaquettes, counted with multiplicity. -/
theorem sum_inc (e₀ : Edge V') : ∑ p, inc n e₀ p = 6 := by
  classical
  have h := count_four n (fun x μ => if ed n x μ = e₀ then (1 : ℝ) else 0)
  have h1 : ∑ μ, ∑ x, (if ed n x μ = e₀ then (1 : ℝ) else 0) = 1 := by
    rw [← sum_edges n (fun e => if e = e₀ then (1 : ℝ) else 0)]
    simp
  rw [h1, mul_one] at h
  convert h using 2

/-- **The force at one link is controlled by the plaquettes through that link, at every field.** No constant depends on
the lattice size and no other plaquette enters. Summed over links this gives `force_static`. -/
theorem link_force_local (U : Configuration V' Q) (e₀ : Edge V') :
    ‖field (actA n) (emb U) e₀‖ ^ 2 ≤ 24 * ∑ p, inc n e₀ p * term n Q (spatialTwist n) character 2 U p := by
  classical
  rw [← norm_rot (emb_sph U)]
  set ρ := rot (actA n) (emb U) with hρ
  have hρs : ∀ e, star (ρ e) = -ρ e := rot_star (emb U)
  set ξ : Amb (Edge V') := WithLp.toLp 2 (Pi.single e₀ (ρ e₀)) with hξ
  have hξa (e : Edge V') : ξ e = if e = e₀ then ρ e₀ else 0 := by
    simp [hξ, Pi.single_apply]
  have hstar : ∀ e, star (ξ e) = -ξ e := by
    intro e
    rw [hξa]
    split_ifs
    · exact hρs e₀
    · simp
  have h2 := sum_Ap n hstar U
  have hin : ⟪ρ, ξ⟫ = ‖ρ e₀‖ ^ 2 := by
    rw [inner_amb, Finset.sum_eq_single e₀ (fun e _ he => by simp [hξa, he]) (fun h => absurd (Finset.mem_univ _) h),
      hξa, if_pos rfl, real_inner_self_eq_norm_sq]
  rw [hin] at h2
  set X := coords n ξ with hX
  set w := ‖ρ e₀‖ with hw
  set L := linkValue (2 * n) Q U with hL
  have hnorm (κ : Fin 4) (y : V') : ‖imag X κ y‖ = w * (if ed n y κ = e₀ then 1 else 0) := by
    rw [imag_coords n hstar, hξa]
    split_ifs <;> simp [hw]
  have hsum : ∀ p : PlaquetteIndex (2 * n), linkSum n X p.1 p.2.1.1 p.2.1.2 = w * inc n e₀ p := by
    intro p
    unfold linkSum inc
    rw [hnorm, hnorm, hnorm, hnorm]
    ring
  have hle : w ^ 2 ≤ 2 * (w * ∑ p : PlaquetteIndex (2 * n), inc n e₀ p * defect L p.2.1.1 p.2.1.2 p.1) := by
    rw [← h2]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => (le_abs_self _).trans ?_
    refine (TwistedLocalTail.Ap_abs_le_defect n X p U).trans (le_of_eq ?_)
    rw [hsum]
    ring
  have hw0 : 0 ≤ w := norm_nonneg _
  have hS0 : 0 ≤ ∑ p : PlaquetteIndex (2 * n), inc n e₀ p * defect L p.2.1.1 p.2.1.2 p.1 :=
    Finset.sum_nonneg fun p _ => mul_nonneg (inc_nonneg n e₀ p) (defect_nonneg _ _ _ _)
  have hlin : w ≤ 2 * ∑ p : PlaquetteIndex (2 * n), inc n e₀ p * defect L p.2.1.1 p.2.1.2 p.1 := by
    rcases hw0.eq_or_lt with h0 | hpos
    · rw [← h0]
      positivity
    · have : w * w ≤ w * (2 * ∑ p : PlaquetteIndex (2 * n), inc n e₀ p * defect L p.2.1.1 p.2.1.2 p.1) := by
        nlinarith only [hle]
      exact le_of_mul_le_mul_left this hpos
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (Finset.univ : Finset (PlaquetteIndex (2 * n)))
    (r := fun p => inc n e₀ p * defect L p.2.1.1 p.2.1.2 p.1) (f := fun p => inc n e₀ p)
    (g := fun p => inc n e₀ p * defect L p.2.1.1 p.2.1.2 p.1 ^ 2)
    (fun p _ => inc_nonneg n e₀ p) (fun p _ => mul_nonneg (inc_nonneg n e₀ p) (sq_nonneg _))
    (fun p _ => by ring)
  rw [sum_inc] at hcs
  have hterm : ∑ p, inc n e₀ p * term n Q (spatialTwist n) character 2 U p =
      ∑ p : PlaquetteIndex (2 * n), inc n e₀ p * defect L p.2.1.1 p.2.1.2 p.1 ^ 2 := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rcases p with ⟨x, ⟨⟨μ, ν⟩, h⟩⟩
    rw [term_eq_defect_sq n U x μ ν h]
  rw [hterm]
  have hsq := pow_le_pow_left₀ hw0 hlin 2
  nlinarith only [hsq, hcs]

/-- The mean squared force at flow time `t`, from `force_static` and the action decrease. This does not decrease in `t`,
and the bound `(1/t + 96) E[S]` that smoothing would give is weaker at every `t > 0`. -/
theorem law_force_static (β : ℝ) {t : ℝ} (ht : 0 ≤ t) (hβ : 1 / 32 ≤ β) :
    ∫ U, forceSq n (wf n t U) ∂twistedLaw n β ≤
      96 * (linkCount n * Real.log (SU2GaussianMass.cap (24 * β)) / β) := by
  have hm : ∫ U, forceSq n (wf n t U) ∂twistedLaw n β ≤ ∫ U, 96 * actionOne n (wf n t U) ∂twistedLaw n β :=
    integral_mono (integrable_law n β ((continuous_forceSq n).comp (continuous_wf_right n t)))
      ((integrable_law n β ((continuous_actionOne n).comp (continuous_wf_right n t))).const_mul _)
      fun U => force_static n (wf n t U)
  rw [integral_const_mul] at hm
  have := law_action_wf_le n β ht hβ
  linarith only [hm, this]

/-- The local form: the mean squared force at one site, uniformly in the lattice size and the flow time. -/
theorem law_force_local_static (β : ℝ) {t : ℝ} (ht : 0 ≤ t) (hβ : 1 / 32 ≤ β) (x : V') :
    ∑ μ, linkForce n β t x μ ≤ 96 * (4 * Real.log (SU2GaussianMass.cap (24 * β)) / β) := by
  have h := law_force_static n β ht hβ
  rw [law_force_eq n β t x, linkCount_vertex] at h
  have hV := card_vertex_pos n
  have e : 96 * (4 * ((Fintype.card V' : ℕ) : ℝ) * Real.log (SU2GaussianMass.cap (24 * β)) / β) =
      ((Fintype.card V' : ℕ) : ℝ) * (96 * (4 * Real.log (SU2GaussianMass.cap (24 * β)) / β)) := by ring
  rw [e] at h
  exact le_of_mul_le_mul_left h hV

/-- The energy bound carried to positive flow time. Any bound `E[S] ≤ N⁴ b` at flow time zero holds for the six plaquettes
at each site at every `t ≥ 0`. -/
theorem law_plaquette_mean_of_energy (β : ℝ) {t b : ℝ} (ht : 0 ≤ t)
    (hb : ∫ U, actionOne n U ∂twistedLaw n β ≤ ((2 * n : ℕ) : ℝ) ^ 4 * b) (x : V') :
    ∑ P : Plane, ∫ U, term n Q (spatialTwist n) character 2 (wf n t U) (x, P) ∂twistedLaw n β ≤ b := by
  have hN : (0 : ℝ) < ((2 * n : ℕ) : ℝ) ^ 4 := by
    rw [← card_vertex]
    exact pow_pos (by exact_mod_cast card_vertex_pos n) 1 |>.trans_eq (pow_one _)
  have h1 := (law_action_wf n β ht).trans hb
  rw [law_action_wf_eq n β t x, card_vertex] at h1
  exact le_of_mul_le_mul_left h1 hN

/-- **The flowed mean from the free-energy bound of `TwistedLocalTail`.** This replaces `log cap(24β)` by the smaller
`-log mass(6β)`, for every `β > 0`. It does not decrease in `t`. -/
theorem law_plaquette_mean_wf_log (β : ℝ) {t : ℝ} (ht : 0 ≤ t) (hβ : 0 < β) (x : V') :
    ∑ P : Plane, ∫ U, term n Q (spatialTwist n) character 2 (wf n t U) (x, P) ∂twistedLaw n β ≤
      (3 + 1 / ((2 * n : ℕ) : ℝ)) * -Real.log (SU2GaussianMass.mass (6 * β)) / β := by
  refine law_plaquette_mean_of_energy n β ht ?_ x
  have hN : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by
    have := NeZero.pos n
    exact_mod_cast (by omega : 0 < 2 * n)
  have h := TwistedLocalTail.energy_le_log n β hβ
  rw [← mul_div_assoc, le_div_iff₀ hβ, mul_comm _ β]
  refine h.trans (le_of_eq ?_)
  field_simp

/-- **The flowed mean with no logarithm.** While `-log mass(6β) ≤ n`, the six plaquettes at a site have total mean squared
defect at most `27/β`, at every flow time. The range is a condition on `n` against `β`. It does not decrease in `t`. At
`t = 0` the value of `TwistedLocalTail.energy_le` at `l ≈ 0.29` is smaller. Only the total action is monotone along the
flow, so the per-plane bound `defect_sq_le_explicit` does not transfer to `t > 0` by this argument. -/
theorem law_plaquette_mean_wf_explicit (β : ℝ) {t : ℝ} (ht : 0 ≤ t) (hβ : 0 < β)
    (hc : -Real.log (SU2GaussianMass.mass (6 * β)) ≤ n) (x : V') :
    ∑ P : Plane, ∫ U, term n Q (spatialTwist n) character 2 (wf n t U) (x, P) ∂twistedLaw n β ≤ 27 / β := by
  refine law_plaquette_mean_of_energy n β ht ?_ x
  have hN : (0 : ℝ) < ((2 * n : ℕ) : ℝ) ^ 4 := by
    have := NeZero.pos n
    positivity
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast NeZero.pos n
  have hn0 : (0 : ℝ) < n := by linarith only [hn]
  have hE := TwistedLocalTail.energy_le n β (1 / 4) hβ (by norm_num) (by norm_num)
  have hL2 := Real.log_two_lt_d9
  have hL0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h24 : Real.log (6 / (1 / 4)) ≤ 5 * Real.log 2 := by
    have h := Real.log_le_log (by norm_num) (by norm_num : (6 / (1 / 4) : ℝ) ≤ 2 ^ 5)
    rw [Real.log_pow] at h
    exact_mod_cast h
  have h6u : Real.log 6 ≤ 3 * Real.log 2 := by
    have h := Real.log_le_log (by norm_num) (by norm_num : (6 : ℝ) ≤ 2 ^ 3)
    rw [Real.log_pow] at h
    exact_mod_cast h
  have h6l : 2 * Real.log 2 ≤ Real.log 6 := by
    have h := Real.log_le_log (by norm_num) (by norm_num : (2 : ℝ) ^ 2 ≤ 6)
    rw [Real.log_pow] at h
    exact_mod_cast h
  have h1n : 9 / (4 * (n : ℝ)) * Real.log 6 ≤ 9 / 4 * (3 * Real.log 2) := by
    have h9 : 9 / (4 * (n : ℝ)) ≤ 9 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith only [hn]
    exact mul_le_mul h9 h6u (Real.log_nonneg (by norm_num)) (by norm_num)
  have h2n : 2 / (n : ℝ) * -Real.log (SU2GaussianMass.mass (6 * β)) ≤ 2 := by
    calc _ ≤ 2 / (n : ℝ) * n := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = 2 := by field_simp
  have hconst : TwistedLocalTail.energyConst n β (1 / 4) ≤ 81 / 4 := by
    unfold TwistedLocalTail.energyConst
    linarith only [h24, h6l, h1n, h2n, hL2]
  rw [← mul_div_assoc, le_div_iff₀ hβ]
  have hmul := mul_le_mul_of_nonneg_left hconst hN.le
  change TwistedLocalTail.energy n β * β ≤ _
  nlinarith only [hE, hmul]

/-! ### Gradient domination and decay near the flat fields -/

theorem norm_sq_split (q : ℍ[ℝ]) : ‖q‖ ^ 2 = q.re ^ 2 + ‖q.im‖ ^ 2 := by
  rw [sq, ← Quaternion.normSq_eq_norm_mul_self, sq ‖q.im‖, ← Quaternion.normSq_eq_norm_mul_self,
    Quaternion.normSq_def', Quaternion.normSq_def']
  simp
  ring

theorem norm_im_le (q : ℍ[ℝ]) : ‖q.im‖ ≤ ‖q‖ := by
  have h := norm_sq_split q
  exact abs_le_of_sq_le_sq' (by nlinarith only [h, sq_nonneg q.re]) (norm_nonneg _) |>.2

theorem im_sub_one (q : ℍ[ℝ]) : (q - 1).im = q.im := by ext <;> simp

theorem norm_im_le_sub_one (q : ℍ[ℝ]) : ‖q.im‖ ≤ ‖q - 1‖ := by
  rw [← im_sub_one]
  exact norm_im_le _

theorem star_im_eq (q : ℍ[ℝ]) : star q.im = -q.im := by ext <;> simp

/-- The remainder of the first-order expansion of a product of four quaternions near one. -/
theorem four_expansion (A₁ A₂ A₃ A₄ : ℍ[ℝ]) (h₂ : ‖A₂‖ = 1) (h₃ : ‖A₃‖ = 1) :
    ‖A₁ * A₂ * A₃ * A₄ - 1 - ((A₁ - 1) + (A₂ - 1) + (A₃ - 1) + (A₄ - 1))‖ ≤
      (‖A₁ - 1‖ + ‖A₂ - 1‖ + ‖A₃ - 1‖ + ‖A₄ - 1‖) ^ 2 / 2 := by
  have e : A₁ * A₂ * A₃ * A₄ - 1 - ((A₁ - 1) + (A₂ - 1) + (A₃ - 1) + (A₄ - 1)) =
      (A₁ - 1) * (A₂ - 1) + (A₁ * A₂ - 1) * (A₃ - 1) + (A₁ * A₂ * A₃ - 1) * (A₄ - 1) := by noncomm_ring
  have s₂ : ‖A₁ * A₂ - 1‖ ≤ ‖A₁ - 1‖ + ‖A₂ - 1‖ := by
    have : A₁ * A₂ - 1 = (A₁ - 1) * A₂ + (A₂ - 1) := by noncomm_ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, h₂, mul_one]
  have s₃ : ‖A₁ * A₂ * A₃ - 1‖ ≤ ‖A₁ * A₂ - 1‖ + ‖A₃ - 1‖ := by
    have : A₁ * A₂ * A₃ - 1 = (A₁ * A₂ - 1) * A₃ + (A₃ - 1) := by noncomm_ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, h₃, mul_one]
  rw [e]
  have n₁ := norm_nonneg (A₁ - 1)
  have n₂ := norm_nonneg (A₂ - 1)
  have n₃ := norm_nonneg (A₃ - 1)
  have n₄ := norm_nonneg (A₄ - 1)
  have b₁ : ‖(A₁ - 1) * (A₂ - 1) + (A₁ * A₂ - 1) * (A₃ - 1) + (A₁ * A₂ * A₃ - 1) * (A₄ - 1)‖ ≤
      ‖A₁ - 1‖ * ‖A₂ - 1‖ + ‖A₁ * A₂ - 1‖ * ‖A₃ - 1‖ + ‖A₁ * A₂ * A₃ - 1‖ * ‖A₄ - 1‖ := by
    refine (norm_add₃_le).trans ?_
    simp only [norm_mul, le_refl]
  have m₃ := mul_le_mul_of_nonneg_right s₂ n₃
  have m₄ := mul_le_mul_of_nonneg_right (show ‖A₁ * A₂ * A₃ - 1‖ ≤ ‖A₁ - 1‖ + ‖A₂ - 1‖ + ‖A₃ - 1‖ by
    linarith only [s₂, s₃]) n₄
  nlinarith only [b₁, m₃, m₄, sq_nonneg ‖A₁ - 1‖, sq_nonneg ‖A₂ - 1‖, sq_nonneg ‖A₃ - 1‖, sq_nonneg ‖A₄ - 1‖]

theorem im_add_coe (r : ℝ) (w : ℍ[ℝ]) : ((r : ℍ[ℝ]) + w).im = w.im := by ext <;> simp

theorem im_of_re_zero {w : ℍ[ℝ]} (h : w.re = 0) : w.im = w := by ext <;> simp [h]

/-- The imaginary part of a conjugate. -/
theorem conj_im (g r : Q) :
    (((g * r * g⁻¹ : Q) : ℍ[ℝ])).im = (g : ℍ[ℝ]) * (r : ℍ[ℝ]).im * ((g⁻¹ : Q) : ℍ[ℝ]) := by
  have h1 : (g : ℍ[ℝ]) * ((g⁻¹ : Q) : ℍ[ℝ]) = 1 := congrArg Subtype.val (mul_inv_cancel g)
  have e : ((g * r * g⁻¹ : Q) : ℍ[ℝ]) = (((r : ℍ[ℝ]).re : ℝ) : ℍ[ℝ]) +
      (g : ℍ[ℝ]) * (r : ℍ[ℝ]).im * ((g⁻¹ : Q) : ℍ[ℝ]) := by
    change (g : ℍ[ℝ]) * (r : ℍ[ℝ]) * ((g⁻¹ : Q) : ℍ[ℝ]) = _
    conv_lhs => rw [← Quaternion.re_add_im (r : ℍ[ℝ])]
    rw [mul_add, add_mul, Quaternion.mul_coe_eq_smul, smul_mul_assoc, h1, ← Quaternion.coe_mul_eq_smul, mul_one]
  rw [e, im_add_coe]
  exact im_of_re_zero (TwistedHessianField.conj_re g _ (by simp))

/-- **First-order Stokes at one plaquette.** If the links `Rₑ · e` form a plaquette of value `σ = ±1`, then the
imaginary part of `σ · P` is minus the frame-transported sum of the imaginary parts of the `Rₑ`, up to the square of
the total rotation. -/
theorem plaq_stokes (a b c e Ra Rb Rc Re : Q) (σ : ℝ)
    (hP : (((Ra * a) * (Rb * b) * (Rc * c)⁻¹ * (Re * e)⁻¹ : Q) : ℍ[ℝ]) = (σ : ℍ[ℝ])) :
    ‖(σ • ((a * b * c⁻¹ * e⁻¹ : Q) : ℍ[ℝ])).im +
        ((Ra : ℍ[ℝ]).im + (a : ℍ[ℝ]) * (Rb : ℍ[ℝ]).im * ((a⁻¹ : Q) : ℍ[ℝ]) +
          -(((a * b * c⁻¹ : Q) : ℍ[ℝ]) * (Rc : ℍ[ℝ]).im * (((a * b * c⁻¹)⁻¹ : Q) : ℍ[ℝ])) +
          -(((a * b * c⁻¹ * e⁻¹ : Q) : ℍ[ℝ]) * (Re : ℍ[ℝ]).im * (((a * b * c⁻¹ * e⁻¹)⁻¹ : Q) : ℍ[ℝ])))‖ ≤
      (d Ra 1 + d Rb 1 + d Rc 1 + d Re 1) ^ 2 / 2 := by
  set P := a * b * c⁻¹ * e⁻¹ with hPd
  set g := a * b * c⁻¹ with hg
  set A₂ : Q := a * Rb * a⁻¹ with hA₂
  set A₃ : Q := g * Rc⁻¹ * g⁻¹ with hA₃
  set A₄ : Q := P * Re⁻¹ * P⁻¹ with hA₄
  have hprod : (Ra * a) * (Rb * b) * (Rc * c)⁻¹ * (Re * e)⁻¹ = Ra * A₂ * A₃ * A₄ * P := by
    rw [hA₂, hA₃, hA₄, hPd, hg]
    group
  rw [hprod] at hP
  set W : Q := Ra * A₂ * A₃ * A₄ with hW
  -- `W` is the conjugate of `σ P`.
  have hPs : (P : ℍ[ℝ]) * star (P : ℍ[ℝ]) = 1 := Unitary.mul_star_self_of_mem P.2
  have hstar : (W : ℍ[ℝ]) = star (σ • (P : ℍ[ℝ])) := by
    have h1 : (W : ℍ[ℝ]) * (P : ℍ[ℝ]) = (σ : ℍ[ℝ]) := hP
    have h2 : (W : ℍ[ℝ]) = (σ : ℍ[ℝ]) * star (P : ℍ[ℝ]) := by
      rw [← h1, mul_assoc, hPs, mul_one]
    rw [h2, Quaternion.star_smul, Quaternion.coe_mul_eq_smul]
  have him : (σ • (P : ℍ[ℝ])).im = -(W : ℍ[ℝ]).im := by
    rw [hstar]
    ext <;> simp
  have dist (r : Q) : ‖((r⁻¹ : Q) : ℍ[ℝ]) - 1‖ = d r 1 := by
    have := d_mul_left r⁻¹ r 1
    rw [inv_mul_cancel, mul_one] at this
    rw [d_comm] at this
    exact this
  have conjdist (k r : Q) : ‖((k * r * k⁻¹ : Q) : ℍ[ℝ]) - 1‖ = d r 1 := by
    have h := d_mul_right k⁻¹ (k * r) (k * 1)
    rw [mul_one, mul_inv_cancel] at h
    change d (k * r * k⁻¹) 1 = _
    rw [h]
    have h2 := d_mul_left k r 1
    rwa [mul_one] at h2
  have t₁ : ‖(Ra : ℍ[ℝ]) - 1‖ = d Ra 1 := rfl
  have t₂ : ‖(A₂ : ℍ[ℝ]) - 1‖ = d Rb 1 := conjdist a Rb
  have t₃ : ‖(A₃ : ℍ[ℝ]) - 1‖ = d Rc 1 := by
    rw [hA₃, conjdist]
    exact dist Rc
  have t₄ : ‖(A₄ : ℍ[ℝ]) - 1‖ = d Re 1 := by
    rw [hA₄, conjdist]
    exact dist Re
  have im₂ : (A₂ : ℍ[ℝ]).im = (a : ℍ[ℝ]) * (Rb : ℍ[ℝ]).im * ((a⁻¹ : Q) : ℍ[ℝ]) := conj_im a Rb
  have stari (r : Q) : (((r⁻¹ : Q) : ℍ[ℝ])).im = -(r : ℍ[ℝ]).im := by
    change (star (r : ℍ[ℝ])).im = _
    ext <;> simp
  have im₃ : (A₃ : ℍ[ℝ]).im = -((g : ℍ[ℝ]) * (Rc : ℍ[ℝ]).im * ((g⁻¹ : Q) : ℍ[ℝ])) := by
    rw [hA₃, conj_im, stari, mul_neg, neg_mul]
  have im₄ : (A₄ : ℍ[ℝ]).im = -((P : ℍ[ℝ]) * (Re : ℍ[ℝ]).im * ((P⁻¹ : Q) : ℍ[ℝ])) := by
    rw [hA₄, conj_im, stari, mul_neg, neg_mul]
  have hexp := four_expansion (Ra : ℍ[ℝ]) A₂ A₃ A₄ (unit_norm _) (unit_norm _)
  rw [t₁, t₂, t₃, t₄] at hexp
  rw [him, ← im₂, ← im₃, ← im₄]
  refine le_trans ?_ hexp
  have hW' : (W : ℍ[ℝ]) = (Ra : ℍ[ℝ]) * A₂ * A₃ * A₄ := rfl
  have e : -(W : ℍ[ℝ]).im + ((Ra : ℍ[ℝ]).im + (A₂ : ℍ[ℝ]).im + (A₃ : ℍ[ℝ]).im + (A₄ : ℍ[ℝ]).im) =
      -((W : ℍ[ℝ]) - 1 - (((Ra : ℍ[ℝ]) - 1) + ((A₂ : ℍ[ℝ]) - 1) + ((A₃ : ℍ[ℝ]) - 1) + ((A₄ : ℍ[ℝ]) - 1))).im := by
    ext <;> simp <;> ring
  rw [e, norm_neg, ← hW']
  exact norm_im_le _

/-- The rate of a plaquette in terms of the imaginary part of its value. -/
theorem re_mul_im {Z : ℍ[ℝ]} (hZ : Z.re = 0) (c : ℍ[ℝ]) : (Z * c).re = -⟪Z, c.im⟫ := by
  rw [Quaternion.inner_def]
  simp [hZ]

/-- **Lower bound for the rate toward a flat field, at one plaquette.** -/
theorem rate_toward (c Z : ℍ[ℝ]) (hc : ‖c‖ = 1) (hZ : Z.re = 0) (τ : ℝ) (h : ‖c.im + Z‖ ≤ τ) :
    ‖c - 1‖ ^ 2 - ‖c - 1‖ ^ 4 / 4 - τ * ‖c - 1‖ ≤ (Z * c).re := by
  have hnorm := norm_sq_split c
  have hd := norm_sq_split (c - 1)
  rw [im_sub_one] at hd
  have hre : (c - 1).re = c.re - 1 := by simp
  rw [hre] at hd
  rw [hc] at hnorm
  set v := c.im with hv
  set δ := ‖c - 1‖ with hδ
  have hδ2 : c.re = 1 - δ ^ 2 / 2 := by nlinarith only [hnorm, hd]
  have hv2 : ‖v‖ ^ 2 = δ ^ 2 - δ ^ 4 / 4 := by
    rw [hδ2] at hnorm
    nlinarith only [hnorm]
  have hvδ : ‖v‖ ≤ δ := norm_im_le_sub_one c
  rw [re_mul_im hZ]
  have hZe : Z = (v + Z) - v := by abel
  have hin : ⟪Z, v⟫ = ⟪v + Z, v⟫ - ‖v‖ ^ 2 := by
    conv_lhs => rw [hZe]
    rw [inner_sub_left, real_inner_self_eq_norm_sq]
  have hcs : ⟪v + Z, v⟫ ≤ τ * δ := by
    refine (real_inner_le_norm _ _).trans ?_
    exact mul_le_mul h hvδ (norm_nonneg _) ((norm_nonneg _).trans h)
  rw [hin, hv2]
  linarith only [hcs]

/-- The rotation at each link toward another field, truncated to its imaginary part. -/
def toward (L Lf : V' → Fin 4 → Q) : Amb (Edge V') :=
  WithLp.toLp 2 fun e => ((Lf (edgeCoordinates (2 * n) e).1 (edgeCoordinates (2 * n) e).2 *
    (L (edgeCoordinates (2 * n) e).1 (edgeCoordinates (2 * n) e).2)⁻¹ : Q) : ℍ[ℝ]).im

theorem toward_ed (L Lf : V' → Fin 4 → Q) (x : V') (μ : Fin 4) :
    toward n L Lf (ed n x μ) = ((Lf x μ * (L x μ)⁻¹ : Q) : ℍ[ℝ]).im := rfl

theorem toward_star (L Lf : V' → Fin 4 → Q) (e : Edge V') : star (toward n L Lf e) = -toward n L Lf e :=
  star_im_eq _

theorem d_ratio (f l : Q) : d (f * l⁻¹) 1 = d f l := by
  have h := d_mul_right l⁻¹ f l
  rwa [mul_inv_cancel] at h

theorem toward_norm (L Lf : V' → Fin 4 → Q) (x : V') (μ : Fin 4) :
    ‖toward n L Lf (ed n x μ)‖ ≤ d (Lf x μ) (L x μ) := by
  rw [toward_ed, ← d_ratio]
  exact norm_im_le_sub_one _

/-- The total link distance around a plaquette. -/
def perim (L Lf : V' → Fin 4 → Q) (x : V') (μ ν : Fin 4) : ℝ :=
  d (Lf x μ) (L x μ) + d (Lf (step (2 * n) x μ) ν) (L (step (2 * n) x μ) ν) +
    d (Lf (step (2 * n) x ν) μ) (L (step (2 * n) x ν) μ) + d (Lf x ν) (L x ν)

theorem imag_toward (L Lf : V' → Fin 4 → Q) (κ : Fin 4) (y : V') :
    imag (coords n (toward n L Lf)) κ y = ((Lf y κ * (L y κ)⁻¹ : Q) : ℍ[ℝ]).im :=
  (imag_coords n (toward_star n L Lf) κ y).trans (toward_ed n L Lf y κ)

theorem Zp_toward (L Lf : V' → Fin 4 → Q) (x : V') (μ ν : Fin 4) (h : μ < ν) :
    Zp n L (coords n (toward n L Lf)) (x, ⟨(μ, ν), h⟩) =
      ((Lf x μ * (L x μ)⁻¹ : Q) : ℍ[ℝ]).im +
        (L x μ : ℍ[ℝ]) * ((Lf (step (2 * n) x μ) ν * (L (step (2 * n) x μ) ν)⁻¹ : Q) : ℍ[ℝ]).im *
          (((L x μ)⁻¹ : Q) : ℍ[ℝ]) +
        -(((L x μ * L (step (2 * n) x μ) ν * (L (step (2 * n) x ν) μ)⁻¹ : Q) : ℍ[ℝ]) *
          ((Lf (step (2 * n) x ν) μ * (L (step (2 * n) x ν) μ)⁻¹ : Q) : ℍ[ℝ]).im *
          (((L x μ * L (step (2 * n) x μ) ν * (L (step (2 * n) x ν) μ)⁻¹)⁻¹ : Q) : ℍ[ℝ])) +
        -(((L x μ * L (step (2 * n) x μ) ν * (L (step (2 * n) x ν) μ)⁻¹ * (L x ν)⁻¹ : Q) : ℍ[ℝ]) *
          ((Lf x ν * (L x ν)⁻¹ : Q) : ℍ[ℝ]).im *
          (((L x μ * L (step (2 * n) x μ) ν * (L (step (2 * n) x ν) μ)⁻¹ * (L x ν)⁻¹)⁻¹ : Q) : ℍ[ℝ])) := by
  simp only [Zp, plaqOf, imag_toward]

/-- The twist sign of a plaquette, from a target with no defect. -/
theorem target_prod (Lf : V' → Fin 4 → Q) (x : V') (μ ν : Fin 4) (h0 : defect Lf μ ν x = 0) :
    ((Lf x μ * Lf (step (2 * n) x μ) ν * (Lf (step (2 * n) x ν) μ)⁻¹ * (Lf x ν)⁻¹ : Q) : ℍ[ℝ]) =
      ((if twistExp μ ν x = 1 then (-1 : ℝ) else 1 : ℝ) : ℍ[ℝ]) := by
  unfold defect d at h0
  rw [norm_eq_zero, sub_eq_zero] at h0
  rw [h0]
  rcases twistExp_cases n μ ν x with h1 | h1
  · simp [h1]
  · simp [h1]

/-- The first-order Stokes identity for a plaquette of `L` against a target with no defect. -/
theorem stokes_toward (L Lf : V' → Fin 4 → Q) (x : V') (μ ν : Fin 4) (h : μ < ν) (h0 : defect Lf μ ν x = 0) :
    ‖(plaqC n L (coords n (toward n L Lf)) x μ ν).im + Zp n L (coords n (toward n L Lf)) (x, ⟨(μ, ν), h⟩)‖ ≤
      perim n L Lf x μ ν ^ 2 / 2 := by
  have hk := target_prod n Lf x μ ν h0
  have hst := plaq_stokes (L x μ) (L (step (2 * n) x μ) ν) (L (step (2 * n) x ν) μ) (L x ν)
    (Lf x μ * (L x μ)⁻¹) (Lf (step (2 * n) x μ) ν * (L (step (2 * n) x μ) ν)⁻¹)
    (Lf (step (2 * n) x ν) μ * (L (step (2 * n) x ν) μ)⁻¹) (Lf x ν * (L x ν)⁻¹)
    (if twistExp μ ν x = 1 then (-1 : ℝ) else 1) (by simpa only [inv_mul_cancel_right] using hk)
  simp only [d_ratio] at hst
  rw [Zp_toward]
  exact hst

theorem Ap_toward (U : Configuration V' Q) (Lf : V' → Fin 4 → Q) (hf : ∀ x μ ν, μ < ν → defect Lf μ ν x = 0)
    (p : PlaquetteIndex (2 * n)) :
    defect (linkValue (2 * n) Q U) p.2.1.1 p.2.1.2 p.1 ^ 2 -
        defect (linkValue (2 * n) Q U) p.2.1.1 p.2.1.2 p.1 ^ 4 / 4 -
        perim n (linkValue (2 * n) Q U) Lf p.1 p.2.1.1 p.2.1.2 ^ 2 / 2 *
          defect (linkValue (2 * n) Q U) p.2.1.1 p.2.1.2 p.1 ≤
      Ap n (coords n (toward n (linkValue (2 * n) Q U) Lf)) p U := by
  rcases p with ⟨x, ⟨⟨μ, ν⟩, hμν⟩⟩
  have hr := rate_toward (plaqC n (linkValue (2 * n) Q U) (coords n (toward n (linkValue (2 * n) Q U) Lf)) x μ ν)
    (Zp n (linkValue (2 * n) Q U) (coords n (toward n (linkValue (2 * n) Q U) Lf)) (x, ⟨(μ, ν), hμν⟩))
    (plaqC_norm n _ _ x μ ν) (Zp_re_zero n _ _ _) _ (stokes_toward n _ Lf x μ ν hμν (hf x μ ν hμν))
  rw [plaqC_defect] at hr
  exact hr

/-- **Gradient domination from a flat target.** If some field with no defect is within squared distance `K S` of `U`, and
`K √S ≤ 1/100`, then `3 S ≤ K forceSq`. The threshold in `grad_dom` comes only from the existence of the target. -/
theorem grad_dom_of_target (U : Configuration V' Q) (Lf : V' → Fin 4 → Q) (K : ℝ) (hK : 0 ≤ K)
    (hf : ∀ x μ ν, μ < ν → defect Lf μ ν x = 0)
    (hD : ∑ μ, ∑ x, d (Lf x μ) (linkValue (2 * n) Q U x μ) ^ 2 ≤ K * actionOne n U)
    (hS : actionOne n U ≤ 1 / 100) (hKS : K * √(actionOne n U) ≤ 1 / 100) :
    3 * actionOne n U ≤ K * forceSq n U := by
  set L := linkValue (2 * n) Q U with hL
  set ξ := toward n L Lf with hξ
  have hstar : ∀ e, star (ξ e) = -ξ e := toward_star n L Lf
  set ρ := rot (actA n) (emb U) with hρ
  set S := actionOne n U with hSd
  set Dt := ∑ μ, ∑ x, d (Lf x μ) (L x μ) ^ 2 with hDt
  have hS0 : 0 ≤ S := by
    have := TwistedIBP.action_nonneg n 1 zero_le_one U
    rwa [action_eq_mul, one_mul] at this
  have hSum : ∑ p : PlaquetteIndex (2 * n), defect L p.2.1.1 p.2.1.2 p.1 ^ 2 = S := by
    rw [hSd, TwistedNearFlat.actionOne_eq]
    rfl
  set s := √S with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = S := Real.sq_sqrt hS0
  have hdp (p : PlaquetteIndex (2 * n)) : defect L p.2.1.1 p.2.1.2 p.1 ^ 2 ≤ S := by
    rw [← hSum]
    exact Finset.single_le_sum (f := fun p : PlaquetteIndex (2 * n) => defect L p.2.1.1 p.2.1.2 p.1 ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ p)
  have hdp' (p : PlaquetteIndex (2 * n)) : defect L p.2.1.1 p.2.1.2 p.1 ≤ s := Real.le_sqrt_of_sq_le (hdp p)
  -- The rate toward the target.
  have hrate := sum_Ap n hstar U
  have hlow : ∑ p : PlaquetteIndex (2 * n), (2 * defect L p.2.1.1 p.2.1.2 p.1 ^ 2 -
      defect L p.2.1.1 p.2.1.2 p.1 ^ 2 * S / 2 -
        4 * (d (Lf p.1 p.2.1.1) (L p.1 p.2.1.1) ^ 2 + d (Lf (step (2 * n) p.1 p.2.1.1) p.2.1.2) (L (step (2 * n) p.1 p.2.1.1) p.2.1.2) ^ 2 +
          d (Lf (step (2 * n) p.1 p.2.1.2) p.2.1.1) (L (step (2 * n) p.1 p.2.1.2) p.2.1.1) ^ 2 + d (Lf p.1 p.2.1.2) (L p.1 p.2.1.2) ^ 2) * s) ≤
      ⟪ρ, ξ⟫ := by
    rw [← hrate, Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    have h := Ap_toward n U Lf hf p
    have hd0 := defect_nonneg L p.2.1.1 p.2.1.2 p.1
    have hd1 := hdp p
    have hd2 := hdp' p
    set δ := defect L p.2.1.1 p.2.1.2 p.1
    have hT : perim n L Lf p.1 p.2.1.1 p.2.1.2 ^ 2 ≤ 4 * (d (Lf p.1 p.2.1.1) (L p.1 p.2.1.1) ^ 2 + d (Lf (step (2 * n) p.1 p.2.1.1) p.2.1.2) (L (step (2 * n) p.1 p.2.1.1) p.2.1.2) ^ 2 +
          d (Lf (step (2 * n) p.1 p.2.1.2) p.2.1.1) (L (step (2 * n) p.1 p.2.1.2) p.2.1.1) ^ 2 + d (Lf p.1 p.2.1.2) (L p.1 p.2.1.2) ^ 2) := by
      unfold perim
      set t₁ := d (Lf p.1 p.2.1.1) (L p.1 p.2.1.1)
      set t₂ := d (Lf (step (2 * n) p.1 p.2.1.1) p.2.1.2) (L (step (2 * n) p.1 p.2.1.1) p.2.1.2)
      set t₃ := d (Lf (step (2 * n) p.1 p.2.1.2) p.2.1.1) (L (step (2 * n) p.1 p.2.1.2) p.2.1.1)
      set t₄ := d (Lf p.1 p.2.1.2) (L p.1 p.2.1.2)
      nlinarith only [sq_nonneg (t₁ - t₂), sq_nonneg (t₁ - t₃), sq_nonneg (t₁ - t₄), sq_nonneg (t₂ - t₃),
        sq_nonneg (t₂ - t₄), sq_nonneg (t₃ - t₄)]
    set T := perim n L Lf p.1 p.2.1.1 p.2.1.2
    set W := 4 * (d (Lf p.1 p.2.1.1) (L p.1 p.2.1.1) ^ 2 + d (Lf (step (2 * n) p.1 p.2.1.1) p.2.1.2) (L (step (2 * n) p.1 p.2.1.1) p.2.1.2) ^ 2 +
          d (Lf (step (2 * n) p.1 p.2.1.2) p.2.1.1) (L (step (2 * n) p.1 p.2.1.2) p.2.1.1) ^ 2 + d (Lf p.1 p.2.1.2) (L p.1 p.2.1.2) ^ 2)
    have m1 : T ^ 2 * δ ≤ W * s := mul_le_mul hT hd2 hd0 (by positivity)
    have m2 : δ ^ 4 ≤ δ ^ 2 * S := by
      have : δ ^ 4 = δ ^ 2 * δ ^ 2 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hd1 (sq_nonneg _)
    linarith only [h, m1, m2]
  have hfour := count_four n (fun x μ => d (Lf x μ) (L x μ) ^ 2)
  have hsumval : ∑ p : PlaquetteIndex (2 * n), (2 * defect L p.2.1.1 p.2.1.2 p.1 ^ 2 -
      defect L p.2.1.1 p.2.1.2 p.1 ^ 2 * S / 2 -
        4 * (d (Lf p.1 p.2.1.1) (L p.1 p.2.1.1) ^ 2 + d (Lf (step (2 * n) p.1 p.2.1.1) p.2.1.2) (L (step (2 * n) p.1 p.2.1.1) p.2.1.2) ^ 2 +
          d (Lf (step (2 * n) p.1 p.2.1.2) p.2.1.1) (L (step (2 * n) p.1 p.2.1.2) p.2.1.1) ^ 2 + d (Lf p.1 p.2.1.2) (L p.1 p.2.1.2) ^ 2) * s) =
      2 * S - S * S / 2 - 24 * Dt * s := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hSum, ← Finset.sum_div, ← Finset.sum_mul, hSum,
      ← Finset.sum_mul, ← Finset.mul_sum, hfour]
    ring
  rw [hsumval] at hlow
  -- The size of the direction.
  have hξ2 : ‖ξ‖ ^ 2 ≤ Dt := by
    rw [norm_sq_amb, sum_edges]
    refine Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun x _ => ?_
    exact pow_le_pow_left₀ (norm_nonneg _) (toward_norm n L Lf x μ) 2
  set κ := √K with hκ
  have hκ0 : 0 ≤ κ := Real.sqrt_nonneg _
  have hκ2 : κ ^ 2 = K := Real.sq_sqrt hK
  have hξ3 : ‖ξ‖ ≤ κ * s := by
    refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
    rw [mul_pow, hs2, hκ2]
    exact hξ2.trans hD
  have hcs : ⟪ρ, ξ⟫ ≤ ‖ρ‖ * (κ * s) :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hξ3 (norm_nonneg _))
  have hmain : 7 / 4 * s ^ 2 ≤ ‖ρ‖ * (κ * s) := by
    have e1 : S * S / 2 ≤ S * (1 / 200) := by nlinarith only [hS, hS0]
    have e2 : 24 * Dt * s ≤ 24 * (K * S) * s := mul_le_mul_of_nonneg_right (by linarith only [hD]) hs0
    have e3 : 24 * (K * S) * s ≤ 24 * S * (1 / 100) := by
      have := mul_le_mul_of_nonneg_left hKS hS0
      nlinarith only [this]
    rw [hs2]
    linarith only [hlow, hcs, e1, e2, e3, hS0]
  rw [forceSq_eq_rot]
  rcases hs0.eq_or_lt with h0 | hpos
  · have : S = 0 := by
      rw [← hs2, ← h0]
      norm_num
    rw [this, mul_zero]
    positivity
  · have hdiv : 7 / 4 * s ≤ ‖ρ‖ * κ := by
      have : s * (7 / 4 * s) ≤ s * (‖ρ‖ * κ) := by nlinarith only [hmain]
      exact le_of_mul_le_mul_left this hpos
    have hsq := pow_le_pow_left₀ (by positivity) hdiv 2
    rw [mul_pow, mul_pow, hs2, hκ2] at hsq
    nlinarith only [hsq, hS0]

/-- A flat target from `near_flat`. -/
theorem exists_target (L : V' → Fin 4 → Q) (hS : actionL L ≤ (1 / (1408 * ((2 * n : ℕ) : ℝ) ^ 5)) ^ 2) :
    ∃ Lf : V' → Fin 4 → Q, (∀ x μ ν, μ < ν → defect Lf μ ν x = 0) ∧
      ∑ μ, ∑ x, d (Lf x μ) (L x μ) ^ 2 ≤ ((2 * n : ℕ) : ℝ) ^ 2 * actionL L := by
  obtain ⟨c₃, c₀, g, h₃, h₀, hD⟩ := TwistedNearFlat.near_flat n L hS
  refine ⟨TwistedNearFlat.shift c₃ c₀ (act (fun x => (g x)⁻¹) flatLink), ?_, le_trans (le_of_eq ?_) hD⟩
  · intro x μ ν h
    rw [TwistedNearFlat.defect_shift c₃ c₀ h₃ h₀ _ μ ν h.ne, defect_act]
    unfold defect
    rw [flatLink_flat x μ ν h]
    simp [d]
  · change _ = ∑ μ, ∑ x, d (act g (TwistedNearFlat.shift c₃ c₀ L) x μ) (flatLink x μ) ^ 2
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun x _ => ?_
    congr 1
    set s := TwistedNearFlat.sgn c₃ c₀ x μ with hs
    have hss : s * s = 1 := by
      have hcase : s = 1 ∨ s = ω := TwistedNearFlat.sgn_cases c₃ c₀ h₃ h₀ x μ
      rcases hcase with h | h <;> rw [h]
      · simp
      · apply Subtype.ext
        simp
    set g' := g (step (2 * n) x μ)
    have e1 : TwistedNearFlat.shift c₃ c₀ (act (fun x => (g x)⁻¹) flatLink) x μ =
        s * ((g x)⁻¹ * (flatLink x μ * g')) := by
      change s * ((g x)⁻¹ * flatLink x μ * g'⁻¹⁻¹) = _
      rw [inv_inv, mul_assoc ((g x)⁻¹)]
    have e2 : act g (TwistedNearFlat.shift c₃ c₀ L) x μ = g x * (s * L x μ) * g'⁻¹ := rfl
    have h1 : d (g x * (s * L x μ) * g'⁻¹) (flatLink x μ) = d (g x * (s * L x μ)) (flatLink x μ * g') := by
      have := d_mul_right g' (g x * (s * L x μ) * g'⁻¹) (flatLink x μ)
      rw [inv_mul_cancel_right] at this
      exact this.symm
    have h2 : d (g x * (s * L x μ)) (flatLink x μ * g') = d (s * L x μ) ((g x)⁻¹ * (flatLink x μ * g')) := by
      have := d_mul_left (g x)⁻¹ (g x * (s * L x μ)) (flatLink x μ * g')
      rw [inv_mul_cancel_left] at this
      exact this.symm ▸ rfl
    have h3 : d (s * L x μ) ((g x)⁻¹ * (flatLink x μ * g')) = d (L x μ) (s * ((g x)⁻¹ * (flatLink x μ * g'))) := by
      have := d_mul_left s (s * L x μ) ((g x)⁻¹ * (flatLink x μ * g'))
      rw [← mul_assoc s s, hss, one_mul] at this
      exact this.symm
    rw [e1, e2, h1, h2, h3, d_comm]

/-- The threshold of `near_flat`. -/
def flatThreshold : ℝ := (1 / (1408 * ((2 * n : ℕ) : ℝ) ^ 5)) ^ 2

/-- **Gradient domination near the flat fields.** Below the threshold of `near_flat`, the action is bounded by the
squared force, with the constant `N²/3`. It is false on `{S ≤ π²}` (`not_grad_dom`). -/
theorem grad_dom (U : Configuration V' Q) (hS : actionOne n U ≤ flatThreshold n) :
    3 * actionOne n U ≤ ((2 * n : ℕ) : ℝ) ^ 2 * forceSq n U := by
  have hS' : actionL (linkValue (2 * n) Q U) ≤ (1 / (1408 * ((2 * n : ℕ) : ℝ) ^ 5)) ^ 2 := by
    rw [← TwistedNearFlat.actionOne_eq]
    exact hS
  obtain ⟨Lf, hf, hD⟩ := exists_target n _ hS'
  rw [← TwistedNearFlat.actionOne_eq] at hD
  set N : ℝ := ((2 * n : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by
    have := NeZero.pos n
    rw [hN]
    exact_mod_cast (by omega : 1 ≤ 2 * n)
  have hS0 : 0 ≤ actionOne n U := by
    have := TwistedIBP.action_nonneg n 1 zero_le_one U
    rwa [action_eq_mul, one_mul] at this
  have hsle : √(actionOne n U) ≤ 1 / (1408 * N ^ 5) := Real.sqrt_le_iff.2 ⟨by positivity, hS⟩
  have hs0 := Real.sqrt_nonneg (actionOne n U)
  have hN5 : 1 ≤ N ^ 5 := one_le_pow₀ hN1
  have hN2 : N ^ 2 ≤ N ^ 5 := pow_le_pow_right₀ hN1 (by norm_num)
  have hNs : N ^ 5 * √(actionOne n U) ≤ 1 / 1408 := by
    have hp : 0 < N ^ 5 := by positivity
    calc N ^ 5 * √(actionOne n U) ≤ N ^ 5 * (1 / (1408 * N ^ 5)) := mul_le_mul_of_nonneg_left hsle hp.le
      _ = 1 / 1408 := by field_simp
  have h2s : N ^ 2 * √(actionOne n U) ≤ 1 / 100 :=
    ((mul_le_mul_of_nonneg_right hN2 hs0).trans hNs).trans (by norm_num)
  have h1s : √(actionOne n U) ≤ 1 / 1408 := le_trans (by nlinarith only [hN5, hs0]) hNs
  have hS100 : actionOne n U ≤ 1 / 100 := by
    rw [← Real.sq_sqrt hS0]
    nlinarith only [h1s, hs0]
  exact grad_dom_of_target n U Lf (N ^ 2) (by positivity) hf hD hS100 h2s

/-- **Exponential decay of the action near the flat fields.** Below the threshold of `near_flat`, the action decays at
rate `3/N²` for all positive flow times. -/
theorem wf_action_decay (U : Configuration V' Q) (hS : actionOne n U ≤ flatThreshold n)
    {t : ℝ} (ht : 0 ≤ t) :
    actionOne n (wf n t U) ≤ Real.exp (-(3 / ((2 * n : ℕ) : ℝ) ^ 2) * t) * actionOne n U := by
  set N : ℝ := ((2 * n : ℕ) : ℝ) with hN
  have hNpos : 0 < N := by
    have := NeZero.pos n
    rw [hN]
    exact_mod_cast (by omega : 0 < 2 * n)
  set c : ℝ := 3 / N ^ 2 with hc
  have hg (s : ℝ) : HasDerivAt (fun r => Real.exp (c * r) * actionOne n (wf n r U))
      (Real.exp (c * s) * c * actionOne n (wf n s U) + Real.exp (c * s) * -forceSq n (wf n s U)) s := by
    have h1 : HasDerivAt (fun r => Real.exp (c * r)) (Real.exp (c * s) * c) s := by
      have := ((hasDerivAt_id s).const_mul c).exp
      simpa using this
    exact h1.mul (hasDerivAt_action_wf n U s)
  have hanti : AntitoneOn (fun r => Real.exp (c * r) * actionOne n (wf n r U)) (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
    · exact fun r _ => (hg r).continuousAt.continuousWithinAt
    · exact fun r _ => (hg r).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Ici] at hr
      rw [(hg r).deriv]
      have hanti := action_wf_antitone n U hr.le
      simp only [wf_zero] at hanti
      have hdom := grad_dom n (wf n r U) (hanti.trans hS)
      have hdiv : c * actionOne n (wf n r U) ≤ forceSq n (wf n r U) := by
        rw [hc, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        linarith only [hdom]
      have he := Real.exp_pos (c * r)
      nlinarith only [hdiv, he]
  have h := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
  simp only [mul_zero, Real.exp_zero, one_mul, wf_zero] at h
  have e : Real.exp (-c * t) * (Real.exp (c * t) * actionOne n (wf n t U)) = actionOne n (wf n t U) := by
    rw [← mul_assoc, ← Real.exp_add]
    simp
  rw [← e]
  exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

/-- The squared force decays at the same rate, through `force_static`. -/
theorem wf_force_decay (U : Configuration V' Q) (hS : actionOne n U ≤ flatThreshold n) {t : ℝ} (ht : 0 ≤ t) :
    forceSq n (wf n t U) ≤ 96 * (Real.exp (-(3 / ((2 * n : ℕ) : ℝ) ^ 2) * t) * actionOne n U) :=
  (force_static n _).trans (mul_le_mul_of_nonneg_left (wf_action_decay n U hS ht) (by norm_num))

/-- **Every field below the threshold flows to a flat field.** The limit has zero action. -/
theorem wf_tendsto_flat (U : Configuration V' Q) (hS : actionOne n U ≤ flatThreshold n) :
    ∃ W : Configuration V' Q, actionOne n W = 0 ∧ Tendsto (fun t => wf n t U) atTop (𝓝 W) := by
  set N : ℝ := ((2 * n : ℕ) : ℝ) with hN
  have hNp : 0 < N := by
    have := NeZero.pos n
    rw [hN]
    exact_mod_cast (by omega : 0 < 2 * n)
  set c : ℝ := 3 / N ^ 2 with hc
  have hc0 : 0 < c := by positivity
  have hS0 : 0 ≤ actionOne n U := by
    have := TwistedIBP.action_nonneg n 1 zero_le_one U
    rwa [action_eq_mul, one_mul] at this
  set γ : ℝ → Amb (Edge V') := fun t => emb (wf n t U) with hγ
  have hd := wf_isLine n U
  set K : ℝ := √(96 * actionOne n U) with hK
  have hbound (t : ℝ) (ht : 0 ≤ t) : ‖field (actA n) (γ t)‖ ≤ K * Real.exp (-(c / 2) * t) := by
    have h : ‖field (actA n) (γ t)‖ ^ 2 ≤ 96 * (Real.exp (-c * t) * actionOne n U) := wf_force_decay n U hS ht
    have e : (K * Real.exp (-(c / 2) * t)) ^ 2 = 96 * (Real.exp (-c * t) * actionOne n U) := by
      rw [mul_pow, hK, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
      have e2 : ((2 : ℕ) : ℝ) * (-(c / 2) * t) = -c * t := by
        push_cast
        ring
      rw [e2]
      ring
    rw [← e] at h
    exact (abs_le_of_sq_le_sq' h (by positivity)).2
  have hint : IntegrableOn (fun t => field (actA n) (γ t)) (Set.Ioi 0) := by
    have hcont : Continuous fun t => field (actA n) (γ t) :=
      (contDiff_field (contDiff_actA n)).continuous.comp (continuous_iff_continuousAt.2 fun t => (hd t).continuousAt)
    refine Integrable.mono' (g := fun t => K * Real.exp (-(c / 2) * t))
      ((integrableOn_exp_mul_Ioi (by linarith only [hc0]) 0).const_mul K)
      hcont.aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => hbound t (le_of_lt ht))
  have hlim := tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi (a := 0) (f := γ)
    (f' := fun t => field (actA n) (γ t)) (fun t _ => hd t) hint
  set x := limUnder atTop γ with hx
  have hsph : Sph x := by
    intro e
    have h1 : Tendsto (fun t => ‖γ t e‖) atTop (𝓝 ‖x e‖) :=
      (((PiLp.continuous_apply 2 _ e).tendsto x).comp hlim).norm
    have h2 : (fun t => ‖γ t e‖) = fun _ => (1 : ℝ) := funext fun t => wf_sph n U t e
    rw [h2] at h1
    exact (tendsto_nhds_unique h1 tendsto_const_nhds)
  have hW : Tendsto (fun t => wf n t U) atTop (𝓝 (ofSph x hsph)) := by
    refine tendsto_pi_nhds.2 fun e => ?_
    refine tendsto_subtype_rng.2 ?_
    exact ((PiLp.continuous_apply 2 _ e).tendsto x).comp hlim
  refine ⟨ofSph x hsph, ?_, hW⟩
  have h1 : Tendsto (fun t => actionOne n (wf n t U)) atTop (𝓝 (actionOne n (ofSph x hsph))) :=
    ((continuous_actionOne n).tendsto _).comp hW
  have hexp : Tendsto (fun t => Real.exp (-c * t) * actionOne n U) atTop (𝓝 0) := by
    have h3 : Tendsto (fun t : ℝ => Real.exp (-c * t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith only [hc0]))
    simpa using h3.mul_const (actionOne n U)
  have h2 : Tendsto (fun t => actionOne n (wf n t U)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp
      (Eventually.of_forall fun t => ?_) ((eventually_ge_atTop 0).mono fun t ht => wf_action_decay n U hS ht)
    have := TwistedIBP.action_nonneg n 1 zero_le_one (wf n t U)
    rwa [action_eq_mul, one_mul] at this
  exact tendsto_nhds_unique h1 h2

/-- The action is at most `24 N⁴`, since each of the `6 N⁴` plaquettes has squared defect at most `4`. -/
theorem action_le_total (U : Configuration V' Q) : actionOne n U ≤ 24 * ((2 * n : ℕ) : ℝ) ^ 4 := by
  have h1 (p : PlaquetteIndex (2 * n)) : term n Q (spatialTwist n) character 2 U p ≤ 4 := by
    rcases p with ⟨x, ⟨⟨μ, ν⟩, h⟩⟩
    rw [term_eq_defect_sq n U x μ ν h]
    have hd : defect (linkValue (2 * n) Q U) μ ν x ≤ 2 := by
      unfold defect d
      refine (norm_sub_le _ _).trans ?_
      rw [unit_norm, unit_norm]
      norm_num
    have := defect_nonneg (linkValue (2 * n) Q U) μ ν x
    nlinarith only [hd, this]
  rw [actionOne_sum]
  have hcard : (Fintype.card Plane : ℝ) = 6 := by
    have : Fintype.card Plane = 6 := by decide
    rw [this]
    norm_num
  calc _ ≤ ∑ _x : V', ∑ _P : Plane, (4 : ℝ) := Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun P _ => h1 (x, P)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_vertex, hcard]
      ring

/-- **Decay of the mean action from any flow time `t₀`.** The first term decays at rate `3/N²`. The second is the
probability that the flowed action at `t₀` is above the threshold of `near_flat`, times the largest possible action. No
bound on that tail is known beyond the one at `t₀ = 0`, since the flow lowers the action and nothing more is proved. A
bound for `β` growing like `log N` would be needed for this to say anything on a physical trajectory, and it is open. -/
theorem law_action_wf_decay_from (β : ℝ) {t₀ t : ℝ} (ht : 0 ≤ t) :
    ∫ U, actionOne n (wf n (t + t₀) U) ∂twistedLaw n β ≤
      Real.exp (-(3 / ((2 * n : ℕ) : ℝ) ^ 2) * t) * ∫ U, actionOne n (wf n t₀ U) ∂twistedLaw n β +
        24 * ((2 * n : ℕ) : ℝ) ^ 4 * (twistedLaw n β).real {U | flatThreshold n ≤ actionOne n (wf n t₀ U)} := by
  set c := Real.exp (-(3 / ((2 * n : ℕ) : ℝ) ^ 2) * t) with hc
  set A : Set (Configuration V' Q) := {U | flatThreshold n ≤ actionOne n (wf n t₀ U)} with hA
  have hAm : MeasurableSet A :=
    (isClosed_le continuous_const ((continuous_actionOne n).comp (continuous_wf_right n t₀))).measurableSet
  have hpt (U : Configuration V' Q) : actionOne n (wf n (t + t₀) U) ≤
      c * actionOne n (wf n t₀ U) + 24 * ((2 * n : ℕ) : ℝ) ^ 4 * A.indicator 1 U := by
    have hS0 : 0 ≤ actionOne n (wf n t₀ U) := by
      have := TwistedIBP.action_nonneg n 1 zero_le_one (wf n t₀ U)
      rwa [action_eq_mul, one_mul] at this
    by_cases hU : U ∈ A
    · rw [Set.indicator_of_mem hU, Pi.one_apply, mul_one]
      have h1 := action_le_total n (wf n (t + t₀) U)
      have h2 := mul_nonneg (Real.exp_pos (-(3 / ((2 * n : ℕ) : ℝ) ^ 2) * t)).le hS0
      linarith only [h1, h2]
    · rw [Set.indicator_of_notMem hU, mul_zero, add_zero, ← wf_add]
      exact wf_action_decay n _ (le_of_lt (not_le.1 hU)) ht
  have hprob : IsProbabilityMeasure (twistedLaw n β) := inferInstance
  have hi1 : Integrable (fun U => c * actionOne n (wf n t₀ U)) (twistedLaw n β) :=
    (integrable_law n β ((continuous_actionOne n).comp (continuous_wf_right n t₀))).const_mul _
  have hi2 : Integrable (fun U => 24 * ((2 * n : ℕ) : ℝ) ^ 4 * A.indicator (1 : Configuration V' Q → ℝ) U) (twistedLaw n β) :=
    ((integrable_const (1 : ℝ)).indicator hAm).const_mul _
  have hint : ∫ U, actionOne n (wf n (t + t₀) U) ∂twistedLaw n β ≤ ∫ U, (c * actionOne n (wf n t₀ U) +
      24 * ((2 * n : ℕ) : ℝ) ^ 4 * A.indicator (1 : Configuration V' Q → ℝ) U) ∂twistedLaw n β :=
    integral_mono (integrable_law n β ((continuous_actionOne n).comp (continuous_wf_right n (t + t₀))))
      (hi1.add hi2) hpt
  rwa [integral_add hi1 hi2, integral_const_mul, integral_const_mul, integral_indicator_one hAm] at hint

/-- **Decay of the mean flowed action.** The second term is the tail of the bare action above the threshold of `near_flat`.
It is small only for `β` of order `N¹⁴ log N`, where the theory is close to free. -/
theorem law_action_wf_decay (β : ℝ) (hβ : 1 / 32 ≤ β) {t : ℝ} (ht : 0 ≤ t) :
    ∫ U, actionOne n (wf n t U) ∂twistedLaw n β ≤
      Real.exp (-(3 / ((2 * n : ℕ) : ℝ) ^ 2) * t) * (linkCount n * Real.log (SU2GaussianMass.cap (24 * β)) / β) +
        24 * ((2 * n : ℕ) : ℝ) ^ 4 *
          (Real.exp (-β * flatThreshold n) * SU2GaussianMass.cap (24 * β) ^ linkCount n) := by
  have h := law_action_wf_decay_from n β (t₀ := 0) ht
  simp only [add_zero, wf_zero] at h
  refine h.trans (add_le_add (mul_le_mul_of_nonneg_left (law_action_le n β hβ) (Real.exp_pos _).le) ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine ENNReal.toReal_le_of_le_ofReal ?_ (action_tail n β (flatThreshold n) hβ)
  have hcap : 0 < SU2GaussianMass.cap (24 * β) := by
    have hM := SU2GaussianMass.mass_pos (24 * β)
    have hcap := SU2GaussianMass.mass_cap_lower (24 * β) (by linarith only [hβ])
    by_contra hcn
    push_neg at hcn
    nlinarith only [hM, hcn, hcap]
  positivity

/-- The mean flowed squared defects at one site, with the same decay and the volume factor removed. -/
theorem law_plaquette_mean_decay (β : ℝ) (hβ : 1 / 32 ≤ β) {t : ℝ} (ht : 0 ≤ t) (x : V') :
    ∑ P : Plane, ∫ U, term n Q (spatialTwist n) character 2 (wf n t U) (x, P) ∂twistedLaw n β ≤
      Real.exp (-(3 / ((2 * n : ℕ) : ℝ) ^ 2) * t) * (4 * Real.log (SU2GaussianMass.cap (24 * β)) / β) +
        24 * (Real.exp (-β * flatThreshold n) * SU2GaussianMass.cap (24 * β) ^ linkCount n) := by
  have h := law_action_wf_decay n β hβ ht
  rw [law_action_wf_eq n β t x, linkCount_vertex] at h
  have hV := card_vertex_pos n
  refine le_of_mul_le_mul_left (h.trans (le_of_eq ?_)) hV
  rw [card_vertex]
  ring

/-- **At flow time `(4/3) N² log N` the total mean action has lost its volume factor.** This is still a statement only
for `β` of order `N¹⁴ log N`, where the second term is small. -/
theorem law_action_large_time (β : ℝ) (hβ : 1 / 32 ≤ β) {t : ℝ}
    (ht : 4 / 3 * ((2 * n : ℕ) : ℝ) ^ 2 * Real.log ((2 * n : ℕ) : ℝ) ≤ t) :
    ∫ U, actionOne n (wf n t U) ∂twistedLaw n β ≤
      4 * Real.log (SU2GaussianMass.cap (24 * β)) / β +
        24 * ((2 * n : ℕ) : ℝ) ^ 4 *
          (Real.exp (-β * flatThreshold n) * SU2GaussianMass.cap (24 * β) ^ linkCount n) := by
  set N : ℝ := ((2 * n : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by
    have := NeZero.pos n
    rw [hN]
    exact_mod_cast (by omega : 1 ≤ 2 * n)
  have hNp : 0 < N := by linarith only [hN1]
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have ht0 : 0 ≤ t := le_trans (by positivity) ht
  refine (law_action_wf_decay n β hβ ht0).trans (add_le_add ?_ le_rfl)
  have hexp : Real.exp (-(3 / N ^ 2) * t) ≤ (N ^ 4)⁻¹ := by
    have h3 : 4 * Real.log N ≤ 3 / N ^ 2 * t := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith only [ht]
    have e : (N ^ 4)⁻¹ = Real.exp (-(4 * Real.log N)) := by
      rw [Real.exp_neg, mul_comm, Real.exp_mul, Real.exp_log hNp]
      norm_cast
    rw [e, neg_mul]
    exact Real.exp_le_exp.2 (neg_le_neg h3)
  have hβ0 : 0 < β := by linarith only [hβ]
  have hc0 := TwistedLocalTail.log_cap_nonneg (24 * β) (by linarith only [hβ])
  have hl : (linkCount n : ℝ) * Real.log (SU2GaussianMass.cap (24 * β)) / β =
      N ^ 4 * (4 * Real.log (SU2GaussianMass.cap (24 * β)) / β) := by
    rw [linkCount_vertex, card_vertex]
    ring
  rw [hl, ← mul_assoc]
  have hc1 : Real.exp (-(3 / N ^ 2) * t) * N ^ 4 ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hexp (by positivity : 0 ≤ N ^ 4)
    rwa [inv_mul_cancel₀ (by positivity)] at this
  have hq : 0 ≤ 4 * Real.log (SU2GaussianMass.cap (24 * β)) / β := by positivity
  have := mul_le_mul_of_nonneg_right hc1 hq
  rwa [one_mul] at this

/-! ### The exact mean force -/

theorem secondCoeff_single (A B C D : ℍ[ℝ]) (hA : A ≠ 0 → B = 0 ∧ C = 0 ∧ D = 0) (hB : B ≠ 0 → C = 0 ∧ D = 0)
    (hC : C ≠ 0 → D = 0) : secondCoeff A B C D = A * A + B * B + C * C + D * D := by
  by_cases h1 : A = 0
  · by_cases h2 : B = 0
    · by_cases h3 : C = 0
      · simp [secondCoeff, h1, h2, h3]
      · obtain rfl := hC h3
        simp [secondCoeff, h1, h2]
    · obtain ⟨rfl, rfl⟩ := hB h2
      simp [secondCoeff, h1]
  · obtain ⟨rfl, rfl, rfl⟩ := hA h1
    simp [secondCoeff]

theorem re_sq_mul {Y : ℍ[ℝ]} (hY : Y.re = 0) (c : ℍ[ℝ]) : (Y * Y * c).re = -(‖Y‖ ^ 2 * c.re) := by
  rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
  simp [hY]
  ring

/-- With at most one of four imaginary rotations nonzero, only the squares survive. -/
theorem second_single (A B C D c : ℍ[ℝ]) (rA : A.re = 0) (rB : B.re = 0) (rC : C.re = 0) (rD : D.re = 0)
    (hA : A ≠ 0 → B = 0 ∧ C = 0 ∧ D = 0) (hB : B ≠ 0 → C = 0 ∧ D = 0) (hC : C ≠ 0 → D = 0) :
    -(2 * (secondCoeff A B C D * c).re) = 2 * c.re * (‖A‖ ^ 2 + ‖B‖ ^ 2 + ‖C‖ ^ 2 + ‖D‖ ^ 2) := by
  rw [secondCoeff_single A B C D hA hB hC]
  simp only [add_mul]
  change -(2 * ((A * A * c).re + (B * B * c).re + (C * C * c).re + (D * D * c).re)) = _
  rw [re_sq_mul rA, re_sq_mul rB, re_sq_mul rC, re_sq_mul rD]
  ring

theorem ed_inj {x y : V'} {μ ν : Fin 4} (h : ed n x μ = ed n y ν) : x = y ∧ μ = ν := by
  have h1 := congrArg (edgeCoordinates (2 * n)) h
  have h2 : (x, μ) = (y, ν) := h1
  exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

/-- A single unit rotation touches a plaquette in at most one link, so only the squares survive. -/
theorem Sc_unit_re (L : V' → Fin 4 → Q) (e₀ : Edge V') (a : Fin 3) (x : V') (μ ν : Fin 4) (h : μ < ν) :
    -(2 * (Sc n L (coords n (unitDir n e₀ a)) (x, ⟨(μ, ν), h⟩) *
        plaqC n L (coords n (unitDir n e₀ a)) x μ ν).re) =
      2 * (plaqC n L (coords n (unitDir n e₀ a)) x μ ν).re *
        (‖unitDir n e₀ a (ed n x μ)‖ ^ 2 + ‖unitDir n e₀ a (ed n (step (2 * n) x μ) ν)‖ ^ 2 +
          ‖unitDir n e₀ a (ed n (step (2 * n) x ν) μ)‖ ^ 2 + ‖unitDir n e₀ a (ed n x ν)‖ ^ 2) := by
  classical
  have hne : μ ≠ ν := h.ne
  have hs := unitDir_star n e₀ a
  have iX (κ : Fin 4) (y : V') : imag (coords n (unitDir n e₀ a)) κ y = unitDir n e₀ a (ed n y κ) := imag_coords n hs κ y
  have hz (e : Edge V') (he : e ≠ e₀) : unitDir n e₀ a e = 0 := by
    change (Pi.single e₀ (basis a) : Edge V' → ℍ[ℝ]) e = 0
    simp [he]
  obtain ⟨r1, r2, r3, r4⟩ := Y_re n L (coords n (unitDir n e₀ a)) x μ ν
  have n1 : ‖(plaqOf n L (coords n (unitDir n e₀ a)) x μ ν).Y₁‖ = ‖unitDir n e₀ a (ed n x μ)‖ := by
    rw [← iX]; rfl
  have n2 : ‖(plaqOf n L (coords n (unitDir n e₀ a)) x μ ν).Y₂‖ = ‖unitDir n e₀ a (ed n (step (2 * n) x μ) ν)‖ := by
    rw [← iX]
    exact conj_norm _ _
  have n3 : ‖(plaqOf n L (coords n (unitDir n e₀ a)) x μ ν).Y₃‖ = ‖unitDir n e₀ a (ed n (step (2 * n) x ν) μ)‖ := by
    rw [← iX]
    change ‖-_‖ = _
    rw [norm_neg]
    exact conj_norm _ _
  have n4 : ‖(plaqOf n L (coords n (unitDir n e₀ a)) x μ ν).Y₄‖ = ‖unitDir n e₀ a (ed n x ν)‖ := by
    rw [← iX]
    change ‖-_‖ = _
    rw [norm_neg]
    exact conj_norm _ _
  have zr {Y : ℍ[ℝ]} {e : Edge V'} (hn : ‖Y‖ = ‖unitDir n e₀ a e‖) (he : e ≠ e₀) : Y = 0 := by
    rw [← norm_eq_zero, hn, hz e he, norm_zero]
  have sp {Y : ℍ[ℝ]} {e : Edge V'} (hn : ‖Y‖ = ‖unitDir n e₀ a e‖) (hY : Y ≠ 0) : e = e₀ := by
    by_contra h'
    exact hY (zr hn h')
  have key := second_single _ _ _ _ (plaqC n L (coords n (unitDir n e₀ a)) x μ ν) r1 r2 r3 r4
    (fun hA => ⟨zr n2 fun h' => hne (ed_inj n ((sp n1 hA).trans h'.symm)).2,
      zr n3 fun h' => TwistedLandau.step_ne x ν (ed_inj n ((sp n1 hA).trans h'.symm)).1.symm,
      zr n4 fun h' => hne (ed_inj n ((sp n1 hA).trans h'.symm)).2⟩)
    (fun hB => ⟨zr n3 fun h' => hne (ed_inj n ((sp n2 hB).trans h'.symm)).2.symm,
      zr n4 fun h' => TwistedLandau.step_ne x μ (ed_inj n ((sp n2 hB).trans h'.symm)).1⟩)
    (fun hC => zr n4 fun h' => hne (ed_inj n ((sp n3 hC).trans h'.symm)).2)
  rw [n1, n2, n3, n4] at key
  exact key

theorem sum_unitDir (e' : Edge V') : ∑ e, ∑ a, ‖unitDir n e a e'‖ ^ 2 = 3 := by
  classical
  have h (e : Edge V') (a : Fin 3) (he : e ≠ e') : unitDir n e a e' = 0 := by
    change (Pi.single e (basis a) : Edge V' → ℍ[ℝ]) e' = 0
    simp [he.symm]
  have h1 (a : Fin 3) : ‖unitDir n e' a e'‖ ^ 2 = 1 := by
    change ‖(Pi.single e' (basis a) : Edge V' → ℍ[ℝ]) e'‖ ^ 2 = 1
    rw [Pi.single_eq_same, basis_norm]
  rw [Finset.sum_eq_single e' (fun e _ he => by simp [h e _ he]) (fun hc => absurd (Finset.mem_univ _) hc)]
  simp [h1]

/-- **The trace of the second derivative over a unit basis.** It is `24 Re c` for each plaquette. -/
theorem trace_second (U : Configuration V' Q) :
    ∑ e, ∑ a, ∑ p, -(2 * (Sc n (linkValue (2 * n) Q U) (coords n (unitDir n e a)) p *
        plaqC n (linkValue (2 * n) Q U) (coords n (unitDir n e a)) p.1 p.2.1.1 p.2.1.2).re) =
      12 * (12 * ((2 * n : ℕ) : ℝ) ^ 4 - actionOne n U) := by
  set L := linkValue (2 * n) Q U with hL
  have hc0 (X X' : Fin 3 → Fin 4 → Section (2 * n)) (x : V') (μ ν : Fin 4) :
      plaqC n L X x μ ν = plaqC n L X' x μ ν := rfl
  have hp (p : PlaquetteIndex (2 * n)) : ∑ e, ∑ a, -(2 * (Sc n L (coords n (unitDir n e a)) p *
      plaqC n L (coords n (unitDir n e a)) p.1 p.2.1.1 p.2.1.2).re) =
      12 * (2 - defect L p.2.1.1 p.2.1.2 p.1 ^ 2) := by
    rcases p with ⟨x, ⟨⟨μ, ν⟩, h⟩⟩
    set c := plaqC n L (fun _ _ => 0) x μ ν with hc
    have hcn : ‖c‖ = 1 := plaqC_norm n L _ x μ ν
    have hd : defect L μ ν x = ‖c - 1‖ := (plaqC_defect n L _ x μ ν).symm
    have hre : ‖c - 1‖ ^ 2 = 2 - 2 * c.re := by
      have h1 := norm_sq_split c
      have h2 := norm_sq_split (c - 1)
      rw [im_sub_one] at h2
      rw [hcn] at h1
      have h3 : (c - 1).re = c.re - 1 := by simp
      rw [h3] at h2
      nlinarith only [h1, h2]
    have hstep (e : Edge V') (a : Fin 3) : -(2 * (Sc n L (coords n (unitDir n e a)) (x, ⟨(μ, ν), h⟩) *
        plaqC n L (coords n (unitDir n e a)) x μ ν).re) =
        2 * c.re * (‖unitDir n e a (ed n x μ)‖ ^ 2 + ‖unitDir n e a (ed n (step (2 * n) x μ) ν)‖ ^ 2 +
          ‖unitDir n e a (ed n (step (2 * n) x ν) μ)‖ ^ 2 + ‖unitDir n e a (ed n x ν)‖ ^ 2) := by
      rw [Sc_unit_re]
      rfl
    dsimp only
    simp only [hstep, ← Finset.mul_sum, Finset.sum_add_distrib, sum_unitDir]
    rw [hd, hre]
    ring
  have hswap : (∑ e : Edge V', ∑ a : Fin 3, ∑ p : PlaquetteIndex (2 * n), -(2 * (Sc n L (coords n (unitDir n e a)) p *
      plaqC n L (coords n (unitDir n e a)) p.1 p.2.1.1 p.2.1.2).re)) =
      ∑ p : PlaquetteIndex (2 * n), ∑ e : Edge V', ∑ a : Fin 3, -(2 * (Sc n L (coords n (unitDir n e a)) p *
      plaqC n L (coords n (unitDir n e a)) p.1 p.2.1.1 p.2.1.2).re) :=
    (Finset.sum_congr rfl fun e _ => Finset.sum_comm).trans Finset.sum_comm
  rw [hswap]
  simp only [hp]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, TwistedNearFlat.actionOne_eq]
  have hcard : (Fintype.card (PlaquetteIndex (2 * n)) : ℝ) = 6 * ((2 * n : ℕ) : ℝ) ^ 4 := by
    have h6 : Fintype.card Plane = 6 := by decide
    rw [Fintype.card_prod, h6, Nat.cast_mul, card_vertex]
    push_cast
    ring
  have hs : ∑ p : PlaquetteIndex (2 * n), (2 : ℝ) = 12 * ((2 * n : ℕ) : ℝ) ^ 4 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    ring
  rw [hs]
  rfl

/-- **The exact mean squared force.** For every `β > 0` and every lattice size, `β E[forceSq] = 12 (12 N⁴ - E[S])`. -/
theorem law_force_exact (β : ℝ) (hβ : 0 < β) :
    β * ∫ U, forceSq n U ∂twistedLaw n β =
      12 * (12 * ((2 * n : ℕ) : ℝ) ^ 4 - ∫ U, actionOne n U ∂twistedLaw n β) := by
  have hprob : IsProbabilityMeasure (twistedLaw n β) :=
    law_probability n Q (spatialTwist n) character WilsonSingleLinkStaples.character_continuous β 2
  have hc (e : Edge V') (a : Fin 3) : Continuous fun U : Configuration V' Q =>
      ⟪rot (actA n) (emb U), unitDir n e a⟫ ^ 2 :=
    ((continuous_rot n).inner continuous_const).pow 2
  have hd (U : Configuration V' Q) (X : Fin 3 → Fin 4 → Section (2 * n)) :
      deriv (deriv (SAt n β X U)) 0 = β * ∑ p, -(2 * (Sc n (linkValue (2 * n) Q U) X p *
        plaqC n (linkValue (2 * n) Q U) X p.1 p.2.1.1 p.2.1.2).re) := by
    obtain ⟨s₁, s₂, h₁, h₂, -, h₀₂⟩ := action_jet n β (linkValue (2 * n) Q U) X
    have e : deriv (SAt n β X U) = s₁ := funext fun t => (h₁ t).deriv
    rw [e, (h₂ 0).deriv, h₀₂]
  have hi2 (e : Edge V') (a : Fin 3) :
      Integrable (fun U => deriv (deriv (SAt n β (coords n (unitDir n e a)) U)) 0) (twistedLaw n β) := by
    obtain ⟨-, m₂, -, b₂, -, -⟩ := ibp_reference n β hβ.le (coords n (unitDir n e a))
    exact Integrable.of_bound m₂.aestronglyMeasurable _ (Eventually.of_forall fun U => by simpa using b₂ U)
  have hone (e : Edge V') (a : Fin 3) : β ^ 2 * ∫ U, ⟪rot (actA n) (emb U), unitDir n e a⟫ ^ 2 ∂twistedLaw n β =
      ∫ U, deriv (deriv (SAt n β (coords n (unitDir n e a)) U)) 0 ∂twistedLaw n β := by
    have hξ := unitDir_star n e a
    have h := gibbs_ibp n β hβ.le (coords n (unitDir n e a))
    simp only [rate_coords n β hξ] at h
    have e1 (U : Configuration V' Q) : (β * -⟪rot (actA n) (emb U), unitDir n e a⟫) ^ 2 =
        β ^ 2 * ⟪rot (actA n) (emb U), unitDir n e a⟫ ^ 2 := by ring
    simp only [e1] at h
    rw [integral_const_mul] at h
    exact h
  have hsum : β ^ 2 * ∫ U, forceSq n U ∂twistedLaw n β =
      ∫ U, ∑ e, ∑ a, deriv (deriv (SAt n β (coords n (unitDir n e a)) U)) 0 ∂twistedLaw n β := by
    simp only [forceSq_coords]
    rw [integral_finset_sum _ fun e _ => integrable_finset_sum _ fun a _ => integrable_law n β (hc e a),
      integral_finset_sum _ fun e _ => integrable_finset_sum _ fun a _ => hi2 e a]
    simp only [integral_finset_sum _ fun a _ => integrable_law n β (hc _ a),
      integral_finset_sum _ fun a _ => hi2 _ a]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => hone e a
  have hpt (U : Configuration V' Q) : ∑ e, ∑ a, deriv (deriv (SAt n β (coords n (unitDir n e a)) U)) 0 =
      β * (12 * (12 * ((2 * n : ℕ) : ℝ) ^ 4 - actionOne n U)) := by
    rw [← trace_second n U]
    simp only [hd, Finset.mul_sum]
  simp only [hpt] at hsum
  rw [integral_const_mul, integral_const_mul, integral_sub (integrable_const _) (integrable_law n β (continuous_actionOne n)),
    integral_const] at hsum
  simp only [probReal_univ, smul_eq_mul, one_mul] at hsum
  have hβne : β ≠ 0 := hβ.ne'
  have e : β * (β * ∫ U, forceSq n U ∂twistedLaw n β) = β * (12 * (12 * ((2 * n : ℕ) : ℝ) ^ 4 - ∫ U, actionOne n U ∂twistedLaw n β)) := by
    rw [← hsum]
    ring
  exact mul_left_cancel₀ hβne e

/-- **A lower bound on the mean action, for every `β > 0` and every lattice size.** -/
theorem law_action_ge (β : ℝ) (hβ : 0 < β) :
    144 * ((2 * n : ℕ) : ℝ) ^ 4 ≤ (96 * β + 12) * ∫ U, actionOne n U ∂twistedLaw n β := by
  have h := law_force_exact n β hβ
  have hm : ∫ U, forceSq n U ∂twistedLaw n β ≤ ∫ U, 96 * actionOne n U ∂twistedLaw n β :=
    integral_mono (integrable_law n β (continuous_forceSq n))
      ((integrable_law n β (continuous_actionOne n)).const_mul _) (force_static n)
  rw [integral_const_mul] at hm
  have := mul_le_mul_of_nonneg_left hm hβ.le
  nlinarith only [h, this]

/-- The site form of `law_action_ge`: the six plaquettes at a site have total mean squared defect at least
`144 / (96 β + 12)`, which is about `1.5/β`, for every `β > 0` and every lattice size. -/
theorem law_plaquette_mean_ge (β : ℝ) (hβ : 0 < β) (x : V') :
    144 / (96 * β + 12) ≤ ∑ P : Plane, ∫ U, term n Q (spatialTwist n) character 2 U (x, P) ∂twistedLaw n β := by
  have h := law_action_ge n β hβ
  have h0 := law_action_wf_eq n β 0 x
  simp only [wf_zero] at h0
  rw [h0, ← card_vertex] at h
  have hV := card_vertex_pos n
  rw [div_le_iff₀ (by positivity)]
  refine le_of_mul_le_mul_left ?_ hV
  linarith only [h]

/-- The site form of `law_force_exact`, at flow time zero. -/
theorem law_force_local_exact (β : ℝ) (hβ : 0 < β) (x : V') :
    β * ∑ μ, linkForce n β 0 x μ =
      12 * (12 - ∑ P : Plane, ∫ U, term n Q (spatialTwist n) character 2 U (x, P) ∂twistedLaw n β) := by
  have h := law_force_exact n β hβ
  have h0 := law_action_wf_eq n β 0 x
  have h1 := law_force_eq n β 0 x
  simp only [wf_zero] at h0 h1
  rw [h0, h1, ← card_vertex] at h
  have hV := (card_vertex_pos n).ne'
  refine mul_left_cancel₀ hV ?_
  linear_combination h

/-- The mean squared force at flow time zero is at most `144 N⁴ / β`. -/
theorem law_force_bare (β : ℝ) (hβ : 0 < β) :
    ∫ U, forceSq n U ∂twistedLaw n β ≤ 144 * ((2 * n : ℕ) : ℝ) ^ 4 / β := by
  have h := law_force_exact n β hβ
  have hS : 0 ≤ ∫ U, actionOne n U ∂twistedLaw n β := integral_nonneg fun U => by
    have := TwistedIBP.action_nonneg n 1 zero_le_one U
    rwa [action_eq_mul, one_mul] at this
  rw [le_div_iff₀ hβ]
  nlinarith only [h, hS]

/-- The mean squared force at flow time `t`, from the bare value and the growth `exp(96 t)`. There is no logarithm and no
condition on `β`, but it is exponential in `t`. -/
theorem law_force_wf_exp (β : ℝ) {t : ℝ} (ht : 0 ≤ t) (hβ : 0 < β) :
    ∫ U, forceSq n (wf n t U) ∂twistedLaw n β ≤ Real.exp (96 * t) * (144 * ((2 * n : ℕ) : ℝ) ^ 4 / β) := by
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (law_force_bare n β hβ) (Real.exp_pos _).le)
  rw [← integral_const_mul]
  refine integral_mono (integrable_law n β ((continuous_forceSq n).comp (continuous_wf_right n t)))
    ((integrable_law n β (continuous_forceSq n)).const_mul _) fun U => ?_
  have := wf_force_growth n U le_rfl ht
  simpa only [wf_zero, sub_zero] using this

/-- The site form. It says nothing once `exp(96 t) ≥ 4 β`, since `site_force_le` gives `576` at every field, and nothing at
any `t` for `β ≤ 1/4`. It beats `law_force_local_static` only for `t` below about `0.05`. -/
theorem law_force_local_exp (β : ℝ) {t : ℝ} (ht : 0 ≤ t) (hβ : 0 < β) (x : V') :
    ∑ μ, linkForce n β t x μ ≤ Real.exp (96 * t) * (144 / β) := by
  have h := law_force_wf_exp n β ht hβ
  rw [law_force_eq n β t x, ← card_vertex] at h
  have hV := card_vertex_pos n
  have e : Real.exp (96 * t) * (144 * ((Fintype.card V' : ℕ) : ℝ) / β) =
      ((Fintype.card V' : ℕ) : ℝ) * (Real.exp (96 * t) * (144 / β)) := by ring
  rw [e] at h
  exact le_of_mul_le_mul_left h hV

/-- The second derivative is at most `48 ‖ξ‖²`, at every configuration. -/
theorem hess_ceiling {x ξ : Amb (Edge V')} (hx : Sph x) (hξ : ∀ e, star (ξ e) = -ξ e) :
    hess (actA n) x ξ ≤ 48 * ‖ξ‖ ^ 2 := by
  have e : x = emb (ofSph x hx) := rfl
  rw [e, hess_coords n hξ, ← coords_norm n hξ]
  obtain ⟨s₁, s₂, h₁, h₂, -, h₀₂⟩ := action_jet n 1 (linkValue (2 * n) Q (ofSph x hx)) (coords n ξ)
  have hd : (deriv fun t => action n Q (spatialTwist n) character 1 2 (TwistedIBP.flow n (coords n ξ) t (ofSph x hx))) = s₁ :=
    funext fun t => (h₁ t).deriv
  rw [hd, (h₂ 0).deriv, h₀₂]
  have := second_le n 1 zero_le_one (linkValue (2 * n) Q (ofSph x hx)) (coords n ξ)
  linarith only [this]

/-- **The force cannot drop faster than at rate `96`.** -/
theorem wf_force_lower (U : Configuration V' Q) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-(96 * t)) * forceSq n U ≤ forceSq n (wf n t U) := by
  have hF (s : ℝ) : HasDerivAt (fun r => forceSq n (wf n r U))
      (-2 * hess (actA n) (emb (wf n s U)) (rot (actA n) (emb (wf n s U)))) s :=
    hasDerivAt_force (contDiff_actA n) (wf_isLine n U) (t₀ := 0) (wf_sph n U 0) s
  have hg (s : ℝ) : HasDerivAt (fun r => Real.exp (96 * r) * forceSq n (wf n r U))
      (Real.exp (96 * s) * 96 * forceSq n (wf n s U) +
        Real.exp (96 * s) * (-2 * hess (actA n) (emb (wf n s U)) (rot (actA n) (emb (wf n s U))))) s := by
    have h1 : HasDerivAt (fun r => Real.exp (96 * r)) (Real.exp (96 * s) * 96) s := by
      have := ((hasDerivAt_id s).const_mul 96).exp
      simpa using this
    exact h1.mul (hF s)
  have hmono : MonotoneOn (fun r => Real.exp (96 * r) * forceSq n (wf n r U)) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact fun r _ => (hg r).continuousAt.continuousWithinAt
    · exact fun r _ => (hg r).differentiableAt.differentiableWithinAt
    · intro r _
      rw [(hg r).deriv]
      have hc := hess_ceiling n (emb_sph (wf n r U)) (rot_star (S := actA n) (emb (wf n r U)))
      rw [← forceSq_eq_rot] at hc
      have he := Real.exp_pos (96 * r)
      nlinarith only [hc, he]
  have h := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
  simp only [mul_zero, Real.exp_zero, one_mul, wf_zero] at h
  have e : Real.exp (-(96 * t)) * (Real.exp (96 * t) * forceSq n (wf n t U)) = forceSq n (wf n t U) := by
    rw [← mul_assoc, ← Real.exp_add]
    simp
  rw [← e]
  exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

/-- The action lost by time `t` is at least the initial squared force times `(1 - exp(-96 t))/96`. -/
theorem wf_dissipation_lower (U : Configuration V' Q) {t : ℝ} (ht : 0 ≤ t) :
    (1 - Real.exp (-(96 * t))) / 96 * forceSq n U ≤ actionOne n U - actionOne n (wf n t U) := by
  have hg (s : ℝ) : HasDerivAt (fun r => actionOne n (wf n r U) + (1 - Real.exp (-(96 * r))) / 96 * forceSq n U)
      (-forceSq n (wf n s U) + Real.exp (-(96 * s)) * forceSq n U) s := by
    have h1 : HasDerivAt (fun r => (1 - Real.exp (-(96 * r))) / 96 * forceSq n U)
        (Real.exp (-(96 * s)) * forceSq n U) s := by
      have h2 : HasDerivAt (fun r : ℝ => Real.exp (-(96 * r))) (Real.exp (-(96 * s)) * -96) s := by
        have := ((hasDerivAt_id s).const_mul 96).neg.exp
        simpa using this
      have h3 := ((h2.const_sub 1).div_const 96).mul_const (forceSq n U)
      convert h3 using 1
      ring
    exact (hasDerivAt_action_wf n U s).add h1
  have hanti : AntitoneOn (fun r => actionOne n (wf n r U) + (1 - Real.exp (-(96 * r))) / 96 * forceSq n U)
      (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
    · exact fun r _ => (hg r).continuousAt.continuousWithinAt
    · exact fun r _ => (hg r).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Ici] at hr
      rw [(hg r).deriv]
      have := wf_force_lower n U hr.le
      linarith only [this]
  have h := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
  simp only [mul_zero, neg_zero, Real.exp_zero, sub_self, zero_div, zero_mul, add_zero, wf_zero] at h
  linarith only [h]

/-- **A strict decrease of the mean action at every `β`.** The mean action at flow time `t` is below the bare one by
`(1 - exp(-96 t))/(8β)` times `12 N⁴ - E[S]`. This is a decrease by a fixed multiple of `1/β` per site, and it does not
grow past `t ≈ 1/96`. So it is not a decay in flow time. It holds on a trajectory `β ~ log N`. -/
theorem law_action_wf_strict (β : ℝ) (hβ : 0 < β) {t : ℝ} (ht : 0 ≤ t) :
    ∫ U, actionOne n (wf n t U) ∂twistedLaw n β ≤ ∫ U, actionOne n U ∂twistedLaw n β -
      (1 - Real.exp (-(96 * t))) / (8 * β) * (12 * ((2 * n : ℕ) : ℝ) ^ 4 - ∫ U, actionOne n U ∂twistedLaw n β) := by
  have hi0 : Integrable (fun U => actionOne n U) (twistedLaw n β) := integrable_law n β (continuous_actionOne n)
  have hit : Integrable (fun U => actionOne n (wf n t U)) (twistedLaw n β) :=
    integrable_law n β ((continuous_actionOne n).comp (continuous_wf_right n t))
  have hm : ∫ U, (1 - Real.exp (-(96 * t))) / 96 * forceSq n U ∂twistedLaw n β ≤
      ∫ U, (actionOne n U - actionOne n (wf n t U)) ∂twistedLaw n β :=
    integral_mono ((integrable_law n β (continuous_forceSq n)).const_mul _) (hi0.sub hit)
      fun U => wf_dissipation_lower n U ht
  rw [integral_const_mul, integral_sub hi0 hit] at hm
  have hF := law_force_exact n β hβ
  have hFe : ∫ U, forceSq n U ∂twistedLaw n β =
      12 * (12 * ((2 * n : ℕ) : ℝ) ^ 4 - ∫ U, actionOne n U ∂twistedLaw n β) / β := by
    rw [eq_div_iff hβ.ne', mul_comm]
    exact hF
  rw [hFe] at hm
  have e : (1 - Real.exp (-(96 * t))) / 96 * (12 * (12 * ((2 * n : ℕ) : ℝ) ^ 4 - ∫ U, actionOne n U ∂twistedLaw n β) / β) =
      (1 - Real.exp (-(96 * t))) / (8 * β) * (12 * ((2 * n : ℕ) : ℝ) ^ 4 - ∫ U, actionOne n U ∂twistedLaw n β) := by
    field_simp
    ring
  rw [e] at hm
  linarith only [hm]

/-- The site form of `law_action_wf_strict`, with `e₀` the bare mean of the six plaquettes at the site. -/
theorem law_plaquette_mean_strict (β : ℝ) (hβ : 0 < β) {t : ℝ} (ht : 0 ≤ t) (x : V') :
    ∑ P : Plane, ∫ U, term n Q (spatialTwist n) character 2 (wf n t U) (x, P) ∂twistedLaw n β ≤
      ∑ P : Plane, ∫ U, term n Q (spatialTwist n) character 2 U (x, P) ∂twistedLaw n β -
        (1 - Real.exp (-(96 * t))) / (8 * β) *
          (12 - ∑ P : Plane, ∫ U, term n Q (spatialTwist n) character 2 U (x, P) ∂twistedLaw n β) := by
  have h := law_action_wf_strict n β hβ ht
  have h0 := law_action_wf_eq n β 0 x
  simp only [wf_zero] at h0
  rw [law_action_wf_eq n β t x, h0, ← card_vertex] at h
  have hV := card_vertex_pos n
  set e₀ := ∑ P : Plane, ∫ U, term n Q (spatialTwist n) character 2 U (x, P) ∂twistedLaw n β
  refine le_of_mul_le_mul_left (h.trans (le_of_eq ?_)) hV
  ring

/-! ### Fixed points of the flow above the threshold -/

/-- A rotation about the first imaginary axis. -/
def phaseI (θ : ℝ) : Q := ⟨⟨Real.cos θ, Real.sin θ, 0, 0⟩, by
  have h := Real.sin_sq_add_cos_sq θ
  rw [Unitary.mem_iff]
  constructor <;> ext <;> simp <;> nlinarith only [h]⟩

@[simp] theorem phaseI_re (θ : ℝ) : ((phaseI θ : Q) : ℍ[ℝ]).re = Real.cos θ := rfl
@[simp] theorem phaseI_imI (θ : ℝ) : ((phaseI θ : Q) : ℍ[ℝ]).imI = Real.sin θ := rfl
@[simp] theorem phaseI_imJ (θ : ℝ) : ((phaseI θ : Q) : ℍ[ℝ]).imJ = 0 := rfl
@[simp] theorem phaseI_imK (θ : ℝ) : ((phaseI θ : Q) : ℍ[ℝ]).imK = 0 := rfl

theorem phaseI_mul (a b : ℝ) : phaseI a * phaseI b = phaseI (a + b) := by
  apply Subtype.ext
  change ((phaseI a : Q) : ℍ[ℝ]) * ((phaseI b : Q) : ℍ[ℝ]) = ((phaseI (a + b) : Q) : ℍ[ℝ])
  ext <;> simp [Real.cos_add, Real.sin_add] <;> ring

theorem phaseI_zero : phaseI 0 = 1 := by
  apply Subtype.ext
  ext <;> simp [phaseI]

theorem phaseI_inv (a : ℝ) : (phaseI a)⁻¹ = phaseI (-a) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [phaseI_mul, add_neg_cancel, phaseI_zero]

theorem phaseI_add_pi (a : ℝ) : phaseI (a + Real.pi) = ω * phaseI a := by
  apply Subtype.ext
  change ((phaseI (a + Real.pi) : Q) : ℍ[ℝ]) = (-1 : ℍ[ℝ]) * ((phaseI a : Q) : ℍ[ℝ])
  ext <;> simp [Real.cos_add_pi, Real.sin_add_pi]

theorem phaseI_add_odd (a : ℝ) (m : ℕ) : phaseI (a + (2 * m + 1) * Real.pi) = ω * phaseI a := by
  rw [← phaseI_add_pi]
  have e : a + (2 * (m : ℝ) + 1) * Real.pi = a + Real.pi + m * (2 * Real.pi) := by ring
  rw [e]
  apply Subtype.ext
  ext
  · exact Real.cos_add_nat_mul_two_pi _ _
  · exact Real.sin_add_nat_mul_two_pi _ _
  · rfl
  · rfl

/-- Conjugation by a rotation about the first imaginary axis preserves the first imaginary component. -/
theorem conj_phaseI_imI (θ : ℝ) (v : ℍ[ℝ]) :
    (((phaseI θ : Q) : ℍ[ℝ]) * v * (((phaseI θ)⁻¹ : Q) : ℍ[ℝ])).imI = v.imI := by
  rw [phaseI_inv]
  have h := Real.sin_sq_add_cos_sq θ
  simp [Real.cos_neg, Real.sin_neg]
  linear_combination v.imI * h

theorem d_phaseI_sq (θ : ℝ) : d (phaseI θ) 1 ^ 2 = 2 - 2 * Real.cos θ := by
  unfold d
  rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
  have h := Real.sin_sq_add_cos_sq θ
  simp
  nlinarith only [h]

variable (m : ℕ)

/-- The coordinate shifted so that its wrap-around sits at `0`. -/
def critCoord (s : ZMod (2 * n)) : ℝ := ((s - 1).val : ℝ)

theorem val_add_one_cases {N : ℕ} [Fact (1 < N)] (t : ZMod N) (h : t + 1 ≠ 0) : (t + 1).val = t.val + 1 := by
  haveI : NeZero N := ⟨by have := Fact.out (p := 1 < N); omega⟩
  rw [ZMod.val_add, ZMod.val_one]
  apply Nat.mod_eq_of_lt
  by_contra hc
  have hlt := ZMod.val_lt t
  have heq : t.val + 1 = N := by omega
  apply h
  have : ((t.val + 1 : ℕ) : ZMod N) = 0 := by rw [heq]; exact ZMod.natCast_self N
  push_cast at this
  rwa [ZMod.natCast_zmod_val] at this

theorem fact_one_lt : Fact (1 < 2 * n) := ⟨by have := NeZero.pos n; omega⟩

attribute [local instance] fact_one_lt

theorem critCoord_succ (s : ZMod (2 * n)) (hs : s ≠ 0) : critCoord n (s + 1) = critCoord n s + 1 := by
  unfold critCoord
  have h : s - 1 + 1 ≠ 0 := by rwa [sub_add_cancel]
  have := val_add_one_cases (s - 1) h
  rw [sub_add_cancel] at this
  rw [add_sub_cancel_right, this]
  push_cast
  ring

theorem critCoord_one : critCoord n 1 = 0 := by
  unfold critCoord
  simp

theorem critCoord_zero : critCoord n 0 = ((2 * n : ℕ) : ℝ) - 1 := by
  unfold critCoord
  rw [zero_sub]
  have hv : (-1 : ZMod (2 * n)).val = 2 * n - 1 := by
    rw [ZMod.neg_val, if_neg (one_ne_zero), ZMod.val_one]
  rw [hv, Nat.cast_sub (by have := NeZero.pos n; omega)]
  simp

/-- The flux of each plaquette of the plane `(1,2)`. -/
def critFlux : ℝ := (2 * m + 1) * Real.pi / ((2 * n : ℕ) : ℝ) ^ 2

theorem lat_pos : 0 < ((2 * n : ℕ) : ℝ) := by
  have := NeZero.pos n
  exact_mod_cast (by omega : 0 < 2 * n)

theorem lat_flux : ((2 * n : ℕ) : ℝ) ^ 2 * critFlux n m = (2 * m + 1) * Real.pi := by
  have := lat_pos n
  unfold critFlux
  field_simp

/-- Constant abelian flux through the plane `(1,2)`, with the wrap-around jump placed at the twisted plaquette. -/
def critLink (x : V') (μ : Fin 4) : Q :=
  if μ = 1 then phaseI (critFlux n m * critCoord n (x 2))
  else if μ = 2 then (if x 2 = 0 then phaseI (-(((2 * n : ℕ) : ℝ) * critFlux n m) * critCoord n (x 1)) else 1) else 1

theorem critLink_one (x : V') : critLink n m x 1 = phaseI (critFlux n m * critCoord n (x 2)) := rfl

theorem critLink_two (x : V') : critLink n m x 2 =
    if x 2 = 0 then phaseI (-(((2 * n : ℕ) : ℝ) * critFlux n m) * critCoord n (x 1)) else 1 := rfl

theorem critLink_zero (x : V') : critLink n m x 0 = 1 := by
  simp [critLink]

theorem critLink_three (x : V') : critLink n m x 3 = 1 := by
  simp [critLink]

theorem critLink_step_zero (x : V') (μ : Fin 4) : critLink n m (step (2 * n) x 0) μ = critLink n m x μ := by
  unfold critLink
  rw [step_other x 0 1 (by decide), step_other x 0 2 (by decide)]

theorem critLink_step_three (x : V') (μ : Fin 4) : critLink n m (step (2 * n) x 3) μ = critLink n m x μ := by
  unfold critLink
  rw [step_other x 3 1 (by decide), step_other x 3 2 (by decide)]

theorem step_self (x : V') (μ : Fin 4) : step (2 * n) x μ μ = x μ + 1 := by
  simp [step]

/-- The plaquette value on the plane `(1,2)`. -/
theorem crit_plaq12 (x : V') :
    critLink n m x 1 * critLink n m (step (2 * n) x 1) 2 * (critLink n m (step (2 * n) x 2) 1)⁻¹ * (critLink n m x 2)⁻¹ =
      ω ^ twistExp 1 2 x * phaseI (-critFlux n m) := by
  have hNu := lat_flux n m
  rw [critLink_one, critLink_two, critLink_one, critLink_two, step_other x 1 2 (by decide), step_self, step_self]
  by_cases h2 : x 2 = 0
  · by_cases h1 : x 1 = 0
    · have ht : twistExp 1 2 x = 1 := by simp [twistExp, h1, h2]
      simp only [h2, h1, if_true, zero_add, critCoord_one, critCoord_zero, ht, pow_one, ← phaseI_add_odd _ m]
      simp only [phaseI_inv, phaseI_mul]
      congr 1
      linear_combination hNu
    · have ht : twistExp 1 2 x = 0 := by simp [twistExp, h1]
      have hy := critCoord_succ n _ h1
      simp only [h2, if_true, zero_add, critCoord_one, critCoord_zero, ht, pow_zero, one_mul, hy]
      simp only [phaseI_inv, phaseI_mul]
      congr 1
      ring
  · have ht : twistExp 1 2 x = 0 := by simp [twistExp, h2]
    have hy := critCoord_succ n _ h2
    simp only [h2, if_false, ht, pow_zero, one_mul, mul_one, inv_one, hy]
    simp only [phaseI_inv, phaseI_mul]
    congr 1
    ring

/-- The other planes carry no flux. -/
theorem crit_plaq_other (x : V') (μ ν : Fin 4) (h : μ < ν) (hne : ¬(μ = 1 ∧ ν = 2)) :
    critLink n m x μ * critLink n m (step (2 * n) x μ) ν * (critLink n m (step (2 * n) x ν) μ)⁻¹ * (critLink n m x ν)⁻¹ = 1 := by
  have hc : ν = 3 ∨ μ = 0 := by
    revert μ ν
    decide
  rcases hc with rfl | rfl
  · rw [critLink_three, critLink_three, critLink_step_three]
    simp
  · rw [critLink_zero, critLink_zero, critLink_step_zero]
    simp

theorem twistExp_other (x : V') (μ ν : Fin 4) (hne : ¬(μ = 1 ∧ ν = 2)) : twistExp μ ν x = 0 := by
  unfold twistExp
  rw [if_neg]
  tauto

theorem critLink_phaseI (x : V') (μ : Fin 4) : ∃ θ, critLink n m x μ = phaseI θ := by
  unfold critLink
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨0, phaseI_zero.symm⟩
  · exact ⟨0, phaseI_zero.symm⟩

/-- The field as a configuration. -/
def critU : Configuration V' Q := fun e => critLink n m (edgeCoordinates (2 * n) e).1 (edgeCoordinates (2 * n) e).2

theorem critU_link : linkValue (2 * n) Q (critU n m) = critLink n m := rfl

theorem conj_of_phaseI {g : Q} (hg : ∃ θ, g = phaseI θ) (v : ℍ[ℝ]) :
    ((g : ℍ[ℝ]) * v * ((g⁻¹ : Q) : ℍ[ℝ])).imI = v.imI := by
  obtain ⟨θ, rfl⟩ := hg
  exact conj_phaseI_imI θ v

/-- The twist-free value of a plaquette of the plane `(1,2)`. -/
theorem crit_plaqC12 (X : Fin 3 → Fin 4 → Section (2 * n)) (x : V') :
    plaqC n (critLink n m) X x 1 2 = ((phaseI (-critFlux n m) : Q) : ℍ[ℝ]) := by
  have h := crit_plaq12 n m x
  unfold plaqC
  change (if twistExp 1 2 x = 1 then (-1 : ℝ) else 1) • ((critLink n m x 1 * critLink n m (step (2 * n) x 1) 2 *
    (critLink n m (step (2 * n) x 2) 1)⁻¹ * (critLink n m x 2)⁻¹ : Q) : ℍ[ℝ]) = _
  rw [h]
  rcases twistExp_cases n 1 2 x with h1 | h1 <;> rw [h1]
  · simp
  · change ((-1 : ℝ) • (((ω ^ 1 * phaseI (-critFlux n m) : Q)) : ℍ[ℝ])) = _
    rw [pow_one]
    change (-1 : ℝ) • ((-1 : ℍ[ℝ]) * ((phaseI (-critFlux n m) : Q) : ℍ[ℝ])) = _
    simp

theorem crit_plaqC_other (X : Fin 3 → Fin 4 → Section (2 * n)) (x : V') (μ ν : Fin 4) (h : μ < ν)
    (hne : ¬(μ = 1 ∧ ν = 2)) : plaqC n (critLink n m) X x μ ν = 1 := by
  unfold plaqC
  change (if twistExp μ ν x = 1 then (-1 : ℝ) else 1) • ((critLink n m x μ * critLink n m (step (2 * n) x μ) ν *
    (critLink n m (step (2 * n) x ν) μ)⁻¹ * (critLink n m x ν)⁻¹ : Q) : ℍ[ℝ]) = _
  rw [crit_plaq_other n m x μ ν h hne, twistExp_other n x μ ν hne]
  simp

/-- The first imaginary component of the transported sum telescopes. -/
theorem crit_Zp_imI (X : Fin 3 → Fin 4 → Section (2 * n)) (x : V') (h : (1 : Fin 4) < 2) :
    (Zp n (critLink n m) X (x, ⟨(1, 2), h⟩)).imI =
      (imag X 1 x).imI + (imag X 2 (step (2 * n) x 1)).imI - (imag X 1 (step (2 * n) x 2)).imI - (imag X 2 x).imI := by
  obtain ⟨θ₁, h₁⟩ := critLink_phaseI n m x 1
  obtain ⟨θ₂, h₂⟩ := critLink_phaseI n m (step (2 * n) x 1) 2
  obtain ⟨θ₃, h₃⟩ := critLink_phaseI n m (step (2 * n) x 2) 1
  obtain ⟨θ₄, h₄⟩ := critLink_phaseI n m x 2
  have hg : critLink n m x 1 * critLink n m (step (2 * n) x 1) 2 * (critLink n m (step (2 * n) x 2) 1)⁻¹ =
      phaseI (θ₁ + θ₂ + -θ₃) := by
    rw [h₁, h₂, h₃, phaseI_inv, phaseI_mul, phaseI_mul]
  have hP : critLink n m x 1 * critLink n m (step (2 * n) x 1) 2 * (critLink n m (step (2 * n) x 2) 1)⁻¹ * (critLink n m x 2)⁻¹ =
      phaseI (θ₁ + θ₂ + -θ₃ + -θ₄) := by
    rw [hg, h₄, phaseI_inv, phaseI_mul]
  have e2 := conj_of_phaseI ⟨θ₁, h₁⟩ (imag X 2 (step (2 * n) x 1))
  have e3 := conj_of_phaseI ⟨_, hg⟩ (imag X 1 (step (2 * n) x 2))
  have e4 := conj_of_phaseI ⟨_, hP⟩ (imag X 2 x)
  simp only [Zp, plaqOf, Quaternion.imI_add, Quaternion.imI_neg, e2, e3, e4]
  ring

/-- The rates of all plaquettes sum to zero, in every direction. -/
theorem crit_sum_Ap (X : Fin 3 → Fin 4 → Section (2 * n)) : ∑ p, Ap n X p (critU n m) = 0 := by
  have h12 : (1 : Fin 4) < 2 := by decide
  have hsingle (x : V') : ∑ P : Plane, Ap n X (x, P) (critU n m) = Ap n X (x, ⟨(1, 2), h12⟩) (critU n m) := by
    refine Finset.sum_eq_single _ (fun P _ hP => ?_) (fun h => absurd (Finset.mem_univ _) h)
    obtain ⟨⟨μ, ν⟩, h⟩ := P
    have hne : ¬(μ = 1 ∧ ν = 2) := by
      rintro ⟨rfl, rfl⟩
      exact hP rfl
    change (Zp n (critLink n m) X (x, ⟨(μ, ν), h⟩) * plaqC n (critLink n m) X x μ ν).re = 0
    rw [crit_plaqC_other n m X x μ ν h hne, mul_one]
    exact Zp_re_zero n _ _ _
  have hval (x : V') : Ap n X (x, ⟨(1, 2), h12⟩) (critU n m) = Real.sin (critFlux n m) *
      ((imag X 1 x).imI + (imag X 2 (step (2 * n) x 1)).imI - (imag X 1 (step (2 * n) x 2)).imI - (imag X 2 x).imI) := by
    change (Zp n (critLink n m) X (x, ⟨(1, 2), h12⟩) * plaqC n (critLink n m) X x 1 2).re = _
    rw [crit_plaqC12, ← crit_Zp_imI n m X x h12]
    have hr := Zp_re_zero n (critLink n m) X (x, ⟨(1, 2), h12⟩)
    simp [hr, Real.sin_neg]
    ring
  rw [sum_plaq]
  simp only [hsingle, hval]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_step (fun y => (imag X 2 y).imI) 1, sum_step (fun y => (imag X 1 y).imI) 2]
  simp

/-- **The field is critical.** Its force vanishes. -/
theorem crit_force : forceSq n (critU n m) = 0 := by
  have hstar := rot_star (S := actA n) (emb (critU n m))
  have h := sum_Ap n hstar (critU n m)
  rw [crit_sum_Ap, mul_zero, real_inner_self_eq_norm_sq] at h
  rw [forceSq_eq_rot, ← h]

/-- The defect of the plane `(1,2)`. -/
theorem crit_defect12 (x : V') : defect (critLink n m) 1 2 x ^ 2 = 2 - 2 * Real.cos (critFlux n m) := by
  unfold defect
  rw [crit_plaq12]
  have := d_mul_left (ω ^ twistExp 1 2 x) (phaseI (-critFlux n m)) 1
  rw [mul_one] at this
  rw [this, d_phaseI_sq, Real.cos_neg]

theorem crit_defect_other (x : V') (μ ν : Fin 4) (h : μ < ν) (hne : ¬(μ = 1 ∧ ν = 2)) : defect (critLink n m) μ ν x = 0 := by
  unfold defect
  rw [crit_plaq_other n m x μ ν h hne, twistExp_other n x μ ν hne]
  simp [d]

/-- The action of the critical field. -/
theorem crit_action : actionOne n (critU n m) = ((2 * n : ℕ) : ℝ) ^ 4 * (2 - 2 * Real.cos (critFlux n m)) := by
  have h12 : (1 : Fin 4) < 2 := by decide
  rw [TwistedNearFlat.actionOne_eq, critU_link]
  unfold actionL
  rw [sum_plaq]
  have hsingle (x : V') : ∑ P : Plane, defect (critLink n m) P.1.1 P.1.2 x ^ 2 = 2 - 2 * Real.cos (critFlux n m) := by
    rw [← crit_defect12 n m x]
    refine Finset.sum_eq_single (⟨(1, 2), h12⟩ : Plane) (fun P _ hP => ?_) (fun h => absurd (Finset.mem_univ _) h)
    obtain ⟨⟨μ, ν⟩, h⟩ := P
    have hne : ¬(μ = 1 ∧ ν = 2) := by
      rintro ⟨rfl, rfl⟩
      exact hP rfl
    simp only
    rw [crit_defect_other n m x μ ν h hne]
    simp
  simp only [hsingle]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_vertex]

theorem crit_defect_le (x : V') (μ ν : Fin 4) (h : μ < ν) : defect (critLink n m) μ ν x ≤ critFlux n m := by
  have hu : 0 ≤ critFlux n m := by unfold critFlux; positivity
  by_cases hne : μ = 1 ∧ ν = 2
  · obtain ⟨rfl, rfl⟩ := hne
    refine abs_le_of_sq_le_sq' ?_ hu |>.2
    rw [crit_defect12]
    have := Real.one_sub_sq_div_two_le_cos (x := critFlux n m)
    linarith only [this]
  · rw [crit_defect_other n m x μ ν h hne]
    exact hu

theorem crit_action_le : actionOne n (critU n m) ≤ ((2 * m + 1) * Real.pi) ^ 2 := by
  rw [crit_action]
  have h := Real.one_sub_sq_div_two_le_cos (x := critFlux n m)
  have hN := lat_pos n
  have e : ((2 * n : ℕ) : ℝ) ^ 4 * critFlux n m ^ 2 = ((2 * m + 1) * Real.pi) ^ 2 := by
    rw [← lat_flux n m]
    ring
  have h2 : 2 - 2 * Real.cos (critFlux n m) ≤ critFlux n m ^ 2 := by linarith only [h]
  calc _ ≤ ((2 * n : ℕ) : ℝ) ^ 4 * critFlux n m ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := e

theorem four_le_crit_action (hm : 2 * m + 1 ≤ 4 * n ^ 2) : 4 * (2 * (m : ℝ) + 1) ^ 2 ≤ actionOne n (critU n m) := by
  rw [crit_action]
  have hN := lat_pos n
  have hu0 : 0 ≤ critFlux n m := by unfold critFlux; positivity
  have hmr : (2 * (m : ℝ) + 1) ≤ ((2 * n : ℕ) : ℝ) ^ 2 := by
    have : ((2 * m + 1 : ℕ) : ℝ) ≤ ((4 * n ^ 2 : ℕ) : ℝ) := by exact_mod_cast hm
    push_cast at this ⊢
    nlinarith only [this]
  have hule : |critFlux n m| ≤ Real.pi := by
    rw [abs_of_nonneg hu0]
    unfold critFlux
    rw [div_le_iff₀ (by positivity), mul_comm]
    exact mul_le_mul_of_nonneg_left hmr Real.pi_pos.le
  have h := Real.cos_le_one_sub_mul_cos_sq hule
  have hp := Real.pi_pos
  have e : ((2 * n : ℕ) : ℝ) ^ 4 * (2 * (2 / Real.pi ^ 2 * critFlux n m ^ 2)) = 4 * (2 * (m : ℝ) + 1) ^ 2 := by
    have e2 : ((2 * n : ℕ) : ℝ) ^ 4 * critFlux n m ^ 2 = ((2 * m + 1) * Real.pi) ^ 2 := by
      rw [← lat_flux n m]
      ring
    calc _ = (4 / Real.pi ^ 2) * (((2 * n : ℕ) : ℝ) ^ 4 * critFlux n m ^ 2) := by ring
      _ = _ := by rw [e2]; field_simp
  rw [← e]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  linarith only [h]

/-- **Fixed points of the flow at every scale of defect above `π/N²`.** For `2m + 1 ≤ N²` there is a field with no force,
all defects at most `(2m+1)π/N²`, and action at least `4(2m+1)²`. So its plaquette energy density is of the same order
as the square of its defect bound, and it never decays. -/
theorem exists_critical_field (hm : 2 * m + 1 ≤ 4 * n ^ 2) : ∃ U : Configuration V' Q, forceSq n U = 0 ∧ (∀ t, wf n t U = U) ∧
    4 * (2 * (m : ℝ) + 1) ^ 2 ≤ actionOne n U ∧ actionOne n U ≤ ((2 * m + 1) * Real.pi) ^ 2 ∧
    ∀ x μ ν, μ < ν → defect (linkValue (2 * n) Q U) μ ν x ≤ (2 * m + 1) * Real.pi / ((2 * n : ℕ) : ℝ) ^ 2 :=
  ⟨critU n m, crit_force n m, wf_of_force_zero n _ (crit_force n m), four_le_crit_action n m hm, crit_action_le n m,
    crit_defect_le n m⟩

/-- **No hypothesis on defects alone gives decay.** At any scale `e` with `π/N² ≤ e ≤ π` there is a fixed point of the
flow with all defects at most `e` and action at least `(4/(9π²)) e² N⁴`, so with energy density comparable to `e²`. -/
theorem exists_critical_at_scale {e : ℝ} (he1 : Real.pi / ((2 * n : ℕ) : ℝ) ^ 2 ≤ e) (he2 : e ≤ Real.pi) :
    ∃ U : Configuration V' Q, (∀ t, wf n t U = U) ∧ (∀ x μ ν, μ < ν → defect (linkValue (2 * n) Q U) μ ν x ≤ e) ∧
      4 / (9 * Real.pi ^ 2) * e ^ 2 * ((2 * n : ℕ) : ℝ) ^ 4 ≤ actionOne n U := by
  have hp := Real.pi_pos
  have hN := lat_pos n
  set N : ℝ := ((2 * n : ℕ) : ℝ) with hNd
  have hy1 : 1 ≤ e * N ^ 2 / Real.pi := by
    rw [le_div_iff₀ hp, one_mul]
    rwa [div_le_iff₀ (by positivity)] at he1
  set y := e * N ^ 2 / Real.pi with hy
  -- The largest odd integer not above `y`.
  obtain ⟨m, hm1, hm2⟩ : ∃ m : ℕ, 2 * (m : ℝ) + 1 ≤ y ∧ y < 2 * (m : ℝ) + 3 := by
    refine ⟨⌊(y - 1) / 2⌋₊, ?_, ?_⟩
    · have := Nat.floor_le (show 0 ≤ (y - 1) / 2 by linarith only [hy1])
      linarith only [this]
    · have := Nat.lt_floor_add_one ((y - 1) / 2)
      linarith only [this]
  have hkN : (2 * (m : ℝ) + 1) ≤ N ^ 2 := by
    refine hm1.trans ?_
    rw [hy, div_le_iff₀ hp, mul_comm]
    exact mul_le_mul_of_nonneg_left he2 (by positivity)
  have hmle : 2 * m + 1 ≤ 4 * n ^ 2 := by
    have e4 : N ^ 2 = ((4 * n ^ 2 : ℕ) : ℝ) := by
      rw [hNd]
      push_cast
      ring
    rw [e4] at hkN
    exact_mod_cast hkN
  obtain ⟨U, -, hfix, hlow, -, hdef⟩ := exists_critical_field n m hmle
  refine ⟨U, hfix, fun x μ ν h => (hdef x μ ν h).trans ?_, le_trans ?_ hlow⟩
  · rw [div_le_iff₀ (by positivity)]
    have : (2 * (m : ℝ) + 1) * Real.pi ≤ y * Real.pi := mul_le_mul_of_nonneg_right hm1 hp.le
    refine this.trans (le_of_eq ?_)
    rw [hy]
    field_simp
    rw [hNd]
  · -- `y ≤ 3(2m+1)`.
    have hk3 : y ≤ 3 * (2 * (m : ℝ) + 1) := by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith only [hm2, this]
    have hy0 : 0 ≤ y := by linarith only [hy1]
    have hsq : y ^ 2 ≤ 9 * (2 * (m : ℝ) + 1) ^ 2 := by
      have := pow_le_pow_left₀ hy0 hk3 2
      nlinarith only [this]
    have e3 : 4 / (9 * Real.pi ^ 2) * e ^ 2 * N ^ 4 = 4 / 9 * y ^ 2 := by
      rw [hy]
      field_simp
    rw [e3]
    nlinarith only [hsq]

/-- No gradient domination on the sublevel set `{S ≤ π²}`, with any constant and at any lattice size. -/
theorem not_grad_dom (c : ℝ) (hc : 0 < c) : ¬ ∀ U : Configuration V' Q, actionOne n U ≤ Real.pi ^ 2 →
    c * actionOne n U ≤ forceSq n U := by
  intro h
  have h1 := h (critU n 0) (by simpa using crit_action_le n 0)
  rw [crit_force] at h1
  have hm : 2 * 0 + 1 ≤ 4 * n ^ 2 := by
    have := NeZero.pos n
    have : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ this
    omega
  have h2 := four_le_crit_action n 0 hm
  norm_num at h2
  nlinarith only [h1, h2, hc]


end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedFlow
