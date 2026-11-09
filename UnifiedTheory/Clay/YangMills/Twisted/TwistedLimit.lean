/- Limits of bounded Schwinger functions of the twisted law along a coupling trajectory, and what each formal OS
property is worth. No requirement of the Clay problem is delivered here, and no nontrivial continuum limit is constructed.

Trivial, by Tychonoff and closedness, for every compact group and every sequence of couplings (`exists_limit`,
`physical_limit_exists`, `smeared_exists_limit`): a subsequence of bounded labelled Schwinger functions converges, and
normalization, boundedness, permutation symmetry and reflection positivity on half-supported labels survive. None of this
constructs a theory: the whole package holds for the constant `2^(number of labels)` by algebra, with no measure and no
hypothesis (`constant_package`), and that constant has a Gram form of rank one (`constant_gram`).

Collapse of plaquette labels. On every SU(2) trajectory with `β → ∞`, whole sequence and at any flow times, including
`t ∝ N²`, bounded plaquette functions tend to that constant, both ordinary and reflected, at flow time zero, under
four-dimensional flow and under slice flow (`flowed_schwinger_tendsto`, `bare_limit_is_constant`, `flowed_limit_is_constant`,
`sliceFlow_limit_is_constant`, `smeared_tendsto_constant`). These are short corollaries of `TwistedFlow.law_term_mean_wf`, and
are what a lattice-scale plaquette is expected to do in any asymptotically free theory. They exclude only unrescaled
plaquette labels, and say nothing against a continuum limit.

Floors. Each link has `12/(8β + 1) ≤ Σ_{P ∋ link} E[term P]` at every lattice size (`link_floor`), by integration by parts
in the three colours, exact at `β = 0`. Summed over a site this is `TwistedFlow.law_action_ge`, with the same constant, so
what is added is the local form. Then `exp(-96t) · 12/(8β + 1) ≤ Σ_P E[term ∘ wf t]` (`flowed_floor`) at every flow time. It is
exponentially weak in `t`. The unsubtracted energy density in physical units diverges on any trajectory with `β` at most
cubic in the size, at flow time zero (`quartic_divergence`) and at flow times below `log N / 96`
(`flowed_quartic_divergence`). Nothing excludes the flowed energy collapsing faster than `N⁻⁴` at `t ∝ N²`.

Reflection positivity at positive flow time. Lean does not prove failure for any observable of the twisted law. The lattice
scale flowed limit on `β → ∞` is constant and so trivially reflection positive (`flowed_limit_is_constant`). What is proved
is conditional and in a model. A kernel `K(s + s')` positive semidefinite on positive rational times, with zero slope at
coincidence, never drops below `K 0` (`hankel_floor`, `not_hankel_of_smooth_decay`, linked to `LimitPackage` by
`package_hankel`, whose only instance here is the constant kernel, `package_hankel_constant`). The free flowed chain of one
mode, which is not an observable of the law, fails a two-point minor at every fixed physical flow time, at positive times up
to a physical size depending on the flow time, for every `n` and every stiffness, and passes the minor at times `0, 1` at flow
time zero (`chain_physical_times`, `chain_minor_negative`, `chain_zero_convex`, with `chain_heat` and `chain_green`
identifying the chain). For the actual law at finite lattice, the failure is numerics only.

Slice flow. Observables computed from one time slice are half-supported at any flow time, so they keep exact reflection
positivity (`static_upper`, `sliceFlow_limit_exists`). They also have exact lattice translations in every direction in
reflected form, the reflected word reduces to an ordinary one (`sliceObs_Rκ`, `sliceObs_reflect`, `slice_osEntry_shift`,
`slice_osEntry_word`), and all of this passes to the limit on a trajectory containing every rational point
(`sliceFlow_os_limit`). Four-dimensional flowed labels have translations only in one-word form (`limit_translation`) and no
reflection positivity. So slice flow repairs the package at positive flow time. On plaquette labels it gains nothing for
nontriviality, by the collapse above.

A nonconstant limit on the actual law. Winding loops in direction `3` have the size of the torus, so the plaquette collapse
misses them. Their odd words have mean zero exactly, by a slab flip, at every size and coupling (`polyWord_odd`). When
`(2N)² √(log cap(24β)/β) → 0`, so roughly `β ≫ N⁴ log N`, and such trajectories exist for every sequence of sizes
(`exists_loop_trajectory`), Stokes and the twist force every loop to one common sign, so the limit is `parityW`: one on even
words and zero on odd ones (`polyakov_os_tendsto`, `polyakov_package`). Its Gram form has rank two (`parityW_gram`,
`parityW_separates`), and its connected two-point function is one at every separation (`polyakov_connected_tendsto`). This is
the long-range order of a center sign on a nearly free torus, not a continuum field theory, and flip-even functions are
constant in it (`parityW_even`). It shows that item 2 of Target A, a nonzero connected separated two-point function, is not
the right test unless restricted to neutral observables. For couplings outside this range only numerics speak
(`scripts/yang_mills_limit_flow_rp_probe.py`).

Physical-size rectangles. Slice-flowed rectangles of physical size, with the sign of the twist they enclose, are the
family on which nontriviality stays open. They have the package with exact reflection positivity on every trajectory
(`sliceLoop_limit_exists`), and collapse when `β ≫ N⁴ log N`, because Stokes bounds them by area times mean defect
(`rectObs_sub_le`, `sliceLoop_os_tendsto`, `not_sliceLoopConnected`). `SliceLoopConnected` names the open statement.

Not proved. Nontriviality of any limit in the neutral sector, for any labels, on any trajectory that could be a continuum
limit, in particular at `β ~ log N`. Any uniform bound for subtracted or renormalized observables, or for a flowed energy
times `N⁴`. Any lower bound on a separated connected function except the winding sign above. That any flowed kernel of the
actual law is differentiable at coincidence, or violates reflection positivity. Identification of the free chain with the
gauge field. A lattice with `T ≠ L`. Continuity in the translation, rotation invariance, regularity, clustering, reconstruction,
large volume. Any group other than SU(2) beyond the trivial part: the center twist does not exist for `G₂`, `F₄`, `E₈`
(`no_sign_twist_of_trivial_center`), and the floor and collapse use quaternions throughout. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedFlow
import UnifiedTheory.Clay.YangMills.Twisted.TwistedSlice
import UnifiedTheory.Clay.YangMills.Twisted.TwistedSliceLift
import UnifiedTheory.Clay.YangMills.Twisted.TwistedNeutral
import UnifiedTheory.Clay.YangMills.CountableCorrelationCompactness
import UnifiedTheory.Clay.YangMills.PeriodicCellSampling
import UnifiedTheory.Clay.YangMills.L1HierarchyCompactness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedLimit
noncomputable section
open MeasureTheory Filter Topology
open PeriodicLattice4 RegulatedGauge PeriodicHalfSplit PeriodicHalfAction PeriodicHalfGeometry
open PeriodicTimeReflection PeriodicPlaquetteReflection PeriodicSiteReflection TwistedReflection

/-! ### Words in labelled observables -/

section Words
variable {Ω ι : Type*}

/-- The product of the observables named by a list of labels. -/
def word (O : ι → Ω → ℂ) (w : List ι) (U : Ω) : ℂ := (w.map fun i => O i U).prod

/-- The product of the sup bounds of a list of labels. -/
def wordBound (B : ι → ℝ) (w : List ι) : ℝ := (w.map B).prod

@[simp] theorem word_nil (O : ι → Ω → ℂ) (U : Ω) : word O [] U = 1 := rfl

theorem word_cons (O : ι → Ω → ℂ) (i : ι) (w : List ι) (U : Ω) :
    word O (i :: w) U = O i U * word O w U := by
  simp [word]

theorem word_perm (O : ι → Ω → ℂ) {w w' : List ι} (h : w.Perm w') (U : Ω) :
    word O w U = word O w' U :=
  (h.map _).prod_eq

theorem wordBound_nonneg (B : ι → ℝ) (hB : ∀ i, 0 ≤ B i) (w : List ι) : 0 ≤ wordBound B w := by
  induction w with
  | nil => simp [wordBound]
  | cons i w ih =>
    have e : wordBound B (i :: w) = B i * wordBound B w := by simp [wordBound]
    rw [e]
    exact mul_nonneg (hB i) ih

theorem word_norm_le (O : ι → Ω → ℂ) (B : ι → ℝ) (hB : ∀ i, 0 ≤ B i) (hO : ∀ i U, ‖O i U‖ ≤ B i)
    (w : List ι) (U : Ω) : ‖word O w U‖ ≤ wordBound B w := by
  induction w with
  | nil => simp [wordBound]
  | cons i w ih =>
    have e : wordBound B (i :: w) = B i * wordBound B w := by simp [wordBound]
    rw [word_cons, norm_mul, e]
    exact mul_le_mul (hO i U) ih (norm_nonneg _) (hB i)

theorem word_continuous [TopologicalSpace Ω] (O : ι → Ω → ℂ) (hO : ∀ i, Continuous (O i)) (w : List ι) :
    Continuous (word O w) := by
  induction w with
  | nil => exact continuous_const
  | cons i w ih =>
    have e : word O (i :: w) = fun U => O i U * word O w U := by
      funext U
      exact word_cons O i w U
    rw [e]
    exact (hO i).mul ih

end Words

/-! ### Reflection positivity at one lattice size, for any compact group -/

section OneLattice
variable (n : ℕ) [NeZero n] (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

local notation "V'" => Vertex (2 * n)
local notation "θ" => reflectConfiguration (2 * n) G

/-- A complex observable that does not depend on the links of the open lower half. -/
def UpperLocalC (F : Configuration V' G → ℂ) : Prop :=
  ∀ b x y, F (assemble n G (b, (x, y))) = F (assemble n G (b, (x, 1)))

theorem UpperLocalC.word {ι : Type*} {O : ι → Configuration V' G → ℂ} {w : List ι}
    (h : ∀ i ∈ w, UpperLocalC n G (O i)) : UpperLocalC n G (TwistedLimit.word O w) := by
  induction w with
  | nil => intro b x y; simp
  | cons i w ih =>
    intro b x y
    rw [word_cons, word_cons, h i (by simp) b x y,
      ih (fun j hj => h j (List.mem_cons_of_mem i hj)) b x y]

/-- **Reflection positivity for complex observables of the closed upper half**, in the form used below. -/
theorem reflected_form (z : PlaquetteIndex (2 * n) → ℝ) (hz : ReflectionInvariant n z)
    (χ : G → ℂ) (hcχ : Continuous χ) (hχ : ClassFunction G χ)
    (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ)
    (F : Configuration V' G → ℂ) (hF : Continuous F) (hloc : UpperLocalC n G F) :
    0 ≤ (∫ U, star (F U) * F (θ U) ∂law n G z χ β c).re ∧
      (∫ U, star (F U) * F (θ U) ∂law n G z χ β c).im = 0 := by
  let f : BoundaryConfiguration n G × HalfConfiguration n G → ℂ :=
    fun s => F (assemble n G (s.1, (s.2, 1)))
  have hf : Continuous f := hF.comp ((continuous_assemble n G).comp
    (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)))
  have h := TwistedReflection.reflection_positive n G z hz χ hcχ hχ hinv β c f hf
  have hobs (U : Configuration V' G) : PeriodicSiteReflection.observable n G f U = F (θ U) := by
    obtain ⟨s, rfl⟩ : ∃ s, U = assemble n G s := ⟨_, (assemble_split n G U).symm⟩
    rw [reflect_assemble, hloc]
    change f ((splitConfiguration n G (assemble n G s)).1, (splitConfiguration n G (assemble n G s)).2.2) = _
    have hs : splitConfiguration n G (assemble n G s) = s := split_assemble n G s
    rw [hs]
  have hobsθ (U : Configuration V' G) : PeriodicSiteReflection.observable n G f (θ U) = F U := by
    rw [hobs, reflectConfiguration_involutive (2 * n) G U]
  simp only [hobsθ, hobs] at h
  exact h

/-- The finite Gram form of reflection positivity for a family of half-supported observables. -/
theorem gram_nonneg {J : Type*} (s : Finset J) (z : PlaquetteIndex (2 * n) → ℝ) (hz : ReflectionInvariant n z)
    (χ : G → ℂ) (hcχ : Continuous χ) (hχ : ClassFunction G χ)
    (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ)
    (F : J → Configuration V' G → ℂ) (hF : ∀ j, Continuous (F j)) (hloc : ∀ j ∈ s, UpperLocalC n G (F j))
    (a : J → ℂ) :
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (a i) * a j * ∫ U, star (F i U) * F j (θ U) ∂law n G z χ β c).re ∧
      (∑ i ∈ s, ∑ j ∈ s, star (a i) * a j * ∫ U, star (F i U) * F j (θ U) ∂law n G z χ β c).im = 0 := by
  haveI : IsProbabilityMeasure (law n G z χ β c) := law_probability n G z χ hcχ β c
  have hθ : Continuous θ := ReflectedDefectBound.continuous_reflection G (2 * n)
  have hint (i j : J) : Integrable (fun U => star (F i U) * F j (θ U)) (law n G z χ β c) :=
    (((hF i).star).mul ((hF j).comp hθ)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let T : Configuration V' G → ℂ := fun U => ∑ j ∈ s, a j * F j U
  have hTc : Continuous T := continuous_finset_sum _ fun j _ => continuous_const.mul (hF j)
  have hTloc : UpperLocalC n G T := by
    intro b x y
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hloc j hj b x y]
  have h := reflected_form n G z hz χ hcχ hχ hinv β c T hTc hTloc
  have e : ∫ U, star (T U) * T (θ U) ∂law n G z χ β c =
      ∑ i ∈ s, ∑ j ∈ s, star (a i) * a j * ∫ U, star (F i U) * F j (θ U) ∂law n G z χ β c := by
    have e₁ (U : Configuration V' G) : star (T U) * T (θ U) =
        ∑ i ∈ s, ∑ j ∈ s, star (a i) * a j * (star (F i U) * F j (θ U)) := by
      simp only [T, star_sum]
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [star_mul']
      ring
    simp only [e₁]
    rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => (hint i j).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ fun j _ => (hint i j).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact integral_const_mul _ _
  rw [e] at h
  exact h

end OneLattice

/-! ### Subsequential limits along a trajectory, for any compact group -/

section Trajectory
variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (N : ℕ → ℕ) [∀ k, NeZero (N k)] (ι : Type*)

/-- A family of labelled bounded continuous observables on the lattices of a trajectory. The label is what stays
fixed as the lattice is refined; nothing here says that the labels have any physical meaning. -/
structure LabelSystem where
  obs : ∀ k, ι → Configuration (Vertex (2 * N k)) G → ℂ
  cont : ∀ k i, Continuous (obs k i)
  bound : ι → ℝ
  bound_nonneg : ∀ i, 0 ≤ bound i
  obs_le : ∀ k i U, ‖obs k i U‖ ≤ bound i

variable {G N ι}
variable (L : LabelSystem G N ι) (z : ∀ k, PlaquetteIndex (2 * N k) → ℝ) (χ : G → ℂ) (β : ℕ → ℝ) (c : ℝ)

/-- The reflected Schwinger function at the `k`-th lattice. The first word sits at the configuration, the second
at its reflection. Taking the first word empty, or the second, gives ordinary Schwinger functions. -/
def osEntry (k : ℕ) (a b : List ι) : ℂ :=
  ∫ U, star (word (L.obs k) a U) * word (L.obs k) b (reflectConfiguration (2 * N k) G U)
    ∂law (N k) G (z k) χ (β k) c

theorem osEntry_norm_le (hcχ : Continuous χ) (k : ℕ) (a b : List ι) :
    ‖osEntry L z χ β c k a b‖ ≤ wordBound L.bound a * wordBound L.bound b := by
  haveI : IsProbabilityMeasure (law (N k) G (z k) χ (β k) c) := law_probability (N k) G (z k) χ hcχ (β k) c
  refine (norm_integral_le_of_norm_le_const (C := wordBound L.bound a * wordBound L.bound b)
    (Eventually.of_forall fun U => ?_)).trans (by simp)
  rw [norm_mul, norm_star]
  exact mul_le_mul (word_norm_le _ _ L.bound_nonneg (L.obs_le k) a U)
    (word_norm_le _ _ L.bound_nonneg (L.obs_le k) b _) (norm_nonneg _)
    (wordBound_nonneg _ L.bound_nonneg a)

/-- The formal properties a limit of Schwinger functions can inherit by closedness alone. `Pos` names the labels
counted as positive time. Nothing in this list distinguishes a nontrivial theory from a constant one. -/
structure LimitPackage (Pos : ι → Prop) (W : List ι × List ι → ℂ) : Prop where
  normalized : W ([], []) = 1
  bounded : ∀ a b, ‖W (a, b)‖ ≤ wordBound L.bound a * wordBound L.bound b
  symmetric : ∀ a a' b b', a.Perm a' → b.Perm b' → W (a, b) = W (a', b')
  reflection_positive : ∀ {J : Type} (s : Finset J) (w : J → List ι) (e : J → ℂ), (∀ j ∈ s, ∀ i ∈ w j, Pos i) →
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (e i) * e j * W (w i, w j)).re ∧
      (∑ i ∈ s, ∑ j ∈ s, star (e i) * e j * W (w i, w j)).im = 0

/-- **Compactness and the passage of reflection positivity, for every compact group.** For every trajectory of
sizes, couplings and reflection-invariant coefficients, some subsequence converges on every pair of words, and
the limit has all the properties of `LimitPackage`.

This is Tychonoff plus closedness. It holds for every sequence of couplings whatever, including a constant
sequence and one growing as fast as you like, and for reflection-invariant coefficients that are not center
twists at all. So it cannot see Yang-Mills, renormalization or nontriviality. -/
theorem exists_limit [Countable ι] (hz : ∀ k, ReflectionInvariant (N k) (z k))
    (hcχ : Continuous χ) (hχ : ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re)
    (Pos : ι → Prop) (hPos : ∀ i, Pos i → ∀ᶠ k in atTop, UpperLocalC (N k) G (L.obs k i)) :
    ∃ (W : List ι × List ι → ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ a b, Tendsto (fun k => osEntry L z χ β c (φ k) a b) atTop (𝓝 (W (a, b)))) ∧
      LimitPackage L Pos W := by
  obtain ⟨W, φ, hφ, hW, hb⟩ := CountableCorrelationCompactness.exists_common_subsequence
    (fun k (p : List ι × List ι) => osEntry L z χ β c k p.1 p.2)
    (fun p => wordBound L.bound p.1 * wordBound L.bound p.2)
    (fun k p => osEntry_norm_le L z χ β c hcχ k p.1 p.2)
  have hconv (a b : List ι) : Tendsto (fun k => osEntry L z χ β c (φ k) a b) atTop (𝓝 (W (a, b))) :=
    hW (a, b)
  refine ⟨W, φ, hφ, hconv, ?_, fun a b => hb (a, b), ?_, ?_⟩
  · have hone (k : ℕ) : osEntry L z χ β c (φ k) [] [] = 1 := by
      haveI : IsProbabilityMeasure (law (N (φ k)) G (z (φ k)) χ (β (φ k)) c) :=
        law_probability (N (φ k)) G (z (φ k)) χ hcχ (β (φ k)) c
      simp [osEntry]
    refine tendsto_nhds_unique (hconv [] []) ?_
    simp only [hone]
    exact tendsto_const_nhds
  · intro a a' b b' ha hb'
    refine tendsto_nhds_unique (hconv a b) ?_
    have e (k : ℕ) : osEntry L z χ β c (φ k) a b = osEntry L z χ β c (φ k) a' b' := by
      unfold osEntry
      simp only [word_perm _ ha, word_perm _ hb']
    simp only [e]
    exact hconv a' b'
  · intro J s w e hpos
    classical
    have hev : ∀ᶠ k in atTop, ∀ j ∈ s, ∀ i ∈ w j, UpperLocalC (N (φ k)) G (L.obs (φ k) i) := by
      rw [Filter.eventually_all_finset]
      intro j hj
      have : ∀ᶠ k in atTop, ∀ i ∈ (w j).toFinset, UpperLocalC (N (φ k)) G (L.obs (φ k) i) := by
        rw [Filter.eventually_all_finset]
        intro i hi
        exact hφ.tendsto_atTop.eventually (hPos i (hpos j hj i (List.mem_toFinset.mp hi)))
      filter_upwards [this] with k hk i hi
      exact hk i (List.mem_toFinset.mpr hi)
    have hlim : Tendsto (fun k => ∑ i ∈ s, ∑ j ∈ s, star (e i) * e j * osEntry L z χ β c (φ k) (w i) (w j)) atTop
        (𝓝 (∑ i ∈ s, ∑ j ∈ s, star (e i) * e j * W (w i, w j))) :=
      tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => tendsto_const_nhds.mul (hconv _ _)
    have hg : ∀ᶠ k in atTop, 0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (e i) * e j * osEntry L z χ β c (φ k) (w i) (w j)).re ∧
        (∑ i ∈ s, ∑ j ∈ s, star (e i) * e j * osEntry L z χ β c (φ k) (w i) (w j)).im = 0 := by
      filter_upwards [hev] with k hk
      exact gram_nonneg (N (φ k)) G s (z (φ k)) (hz _) χ hcχ hχ hinv (β (φ k)) c
        (fun j => word (L.obs (φ k)) (w j)) (fun j => word_continuous _ (L.cont _) _)
        (fun j hj => UpperLocalC.word (N (φ k)) G (hk j hj)) e
    constructor
    · exact ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp hlim) (hg.mono fun k hk => hk.1)
    · refine tendsto_nhds_unique (Complex.continuous_im.tendsto _ |>.comp hlim) ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hg] with k hk
      exact hk.2.symm

end Trajectory

/-! ### Concrete labels: plaquettes at physical sites, for any compact group -/

section Physical
variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- A rational point of the unit torus and a plane. The lattice has side `2n`, so the physical size is one. -/
abbrev PhysLabel := (Fin 4 → ℚ) × Plane

/-- The lattice site containing a physical point, by the same floor rule as the cell sampler. -/
def site (n : ℕ) (x : Fin 4 → ℚ) : Vertex (2 * n) :=
  fun μ => ((⌊x μ * ((2 * n : ℕ) : ℚ)⌋ : ℤ) : ZMod (2 * n))

/-- The twisted real plaquette value: `z_p Re χ(P_p)`. -/
def plaqReal (n : ℕ) [NeZero n] (χ : G → ℂ) (U : Configuration (Vertex (2 * n)) G)
    (p : PlaquetteIndex (2 * n)) : ℝ :=
  spatialTwist n p * (χ (plaquetteProduct (2 * n) G U p.1 p.2.1.1 p.2.1.2)).re

theorem term_eq_sub_plaqReal (n : ℕ) [NeZero n] (χ : G → ℂ) (c : ℝ) (U : Configuration (Vertex (2 * n)) G)
    (p : PlaquetteIndex (2 * n)) :
    term n G (spatialTwist n) χ c U p = c - plaqReal G n χ U p := rfl

theorem plaqReal_continuous (n : ℕ) [NeZero n] (χ : G → ℂ) (hcχ : Continuous χ)
    (p : PlaquetteIndex (2 * n)) :
    Continuous fun U : Configuration (Vertex (2 * n)) G => plaqReal G n χ U p := by
  have h := continuous_term n G (spatialTwist n) χ hcχ 0 p
  have e : (fun U : Configuration (Vertex (2 * n)) G => plaqReal G n χ U p) =
      fun U => 0 - term n G (spatialTwist n) χ 0 U p := by
    funext U
    rw [term_eq_sub_plaqReal]
    ring
  rw [e]
  exact continuous_const.sub h

theorem plaqReal_abs_le (n : ℕ) [NeZero n] (χ : G → ℂ) (B : ℝ) (hB : ∀ g, ‖χ g‖ ≤ B)
    (U : Configuration (Vertex (2 * n)) G) (p : PlaquetteIndex (2 * n)) : |plaqReal G n χ U p| ≤ B := by
  have hz : |spatialTwist n p| = 1 := by
    have h := spatialTwist_sq n p
    have : |spatialTwist n p| * |spatialTwist n p| = 1 := by rw [← abs_mul, h, abs_one]
    nlinarith only [this, abs_nonneg (spatialTwist n p)]
  unfold plaqReal
  rw [abs_mul, hz, one_mul]
  exact (Complex.abs_re_le_norm _).trans (hB _)

variable (N : ℕ → ℕ) [∀ k, NeZero (N k)]

/-- Plaquettes at physical sites, as a label system on the actual twisted lattices. -/
def physLabels (χ : G → ℂ) (hcχ : Continuous χ) (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ g, ‖χ g‖ ≤ B) :
    LabelSystem G N PhysLabel where
  obs k l U := ((plaqReal G (N k) χ U (site (N k) l.1, l.2) : ℝ) : ℂ)
  cont k l := Complex.continuous_ofReal.comp (plaqReal_continuous G (N k) χ hcχ _)
  bound _ := B
  bound_nonneg _ := hB0
  obs_le k l U := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact plaqReal_abs_le G (N k) χ B hB U _

/-- A physical point strictly inside the upper half of the time circle. -/
def PosLabel (l : PhysLabel) : Prop := 0 < l.1 0 ∧ l.1 0 < 1 / 2

theorem site_time_val (n : ℕ) [NeZero n] (q : Fin 4 → ℚ) (h1 : q 0 < 1 / 2)
    (hn : 1 ≤ q 0 * ((2 * n : ℕ) : ℚ)) : 0 < (site n q 0).val ∧ (site n q 0).val < n := by
  have hnpos : (0 : ℚ) < ((2 * n : ℕ) : ℚ) := by
    have := NeZero.pos n
    exact_mod_cast (by omega : 0 < 2 * n)
  have hfl : 1 ≤ ⌊q 0 * ((2 * n : ℕ) : ℚ)⌋ := Int.le_floor.mpr (by exact_mod_cast hn)
  have hlt : ⌊q 0 * ((2 * n : ℕ) : ℚ)⌋ < (n : ℤ) := by
    rw [Int.floor_lt]
    have hnq : (0 : ℚ) < n := by exact_mod_cast NeZero.pos n
    push_cast
    nlinarith only [h1, hnq]
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ ⌊q 0 * ((2 * n : ℕ) : ℚ)⌋)
  have hval : (site n q 0).val = m := by
    unfold site
    rw [hm, Int.cast_natCast, ZMod.val_natCast_of_lt (by omega)]
  rw [hval]
  omega

/-- Every positive physical label is eventually an observable of the open upper half. -/
theorem physLabels_upper (hN : Tendsto N atTop atTop) (χ : G → ℂ) (hcχ : Continuous χ) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ g, ‖χ g‖ ≤ B) (l : PhysLabel) (hl : PosLabel l) :
    ∀ᶠ k in atTop, UpperLocalC (N k) G ((physLabels G N χ hcχ B hB0 hB).obs k l) := by
  obtain ⟨h0, h1⟩ := hl
  have hev : ∀ᶠ k in atTop, 1 ≤ l.1 0 * ((2 * N k : ℕ) : ℚ) := by
    obtain ⟨m, hm⟩ := exists_nat_ge (1 / l.1 0)
    filter_upwards [hN.eventually_ge_atTop m] with k hk
    have hk' : (m : ℚ) ≤ (N k : ℚ) := by exact_mod_cast hk
    have : 1 / l.1 0 ≤ (N k : ℚ) := hm.trans hk'
    rw [div_le_iff₀ h0] at this
    push_cast
    have hNk : (0 : ℚ) ≤ N k := by positivity
    nlinarith only [this, h0, hNk]
  filter_upwards [hev] with k hk b x y
  obtain ⟨hv0, hvn⟩ := site_time_val (N k) l.1 h1 hk
  have hpos : PositiveP (N k) (site (N k) l.1, l.2) := by
    change Positive (N k) (site (N k) l.1, l.2.1.1)
    unfold Positive
    split_ifs
    · exact hvn
    · exact ⟨hv0, hvn⟩
  change ((plaqReal G (N k) χ _ (site (N k) l.1, l.2) : ℝ) : ℂ) = ((plaqReal G (N k) χ _ (site (N k) l.1, l.2) : ℝ) : ℂ)
  unfold plaqReal
  rw [positive_plaquette_independent (N k) G _ hpos b x y 1]

end Physical

/-! ### A general limit of words whose letters converge in mean to a constant -/

section Collapse
variable {Ω : ℕ → Type*} [∀ k, TopologicalSpace (Ω k)] [∀ k, CompactSpace (Ω k)] [∀ k, MeasurableSpace (Ω k)]
  [∀ k, OpensMeasurableSpace (Ω k)] {ι : Type*}
  (μ : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (μ k)]
  (O : ∀ k, ι → Ω k → ℂ) (hO : ∀ k i, Continuous (O k i)) (M : ℝ) (hM : 0 ≤ M)
  (hle : ∀ k i U, ‖O k i U‖ ≤ M)

include hO hM hle in
/-- If every letter tends to the constant `M` in mean, so does every word, to `M^length`. -/
theorem word_tendsto_L1 (hd : ∀ i, Tendsto (fun k => ∫ U, ‖O k i U - M‖ ∂μ k) atTop (𝓝 0)) (w : List ι) :
    Tendsto (fun k => ∫ U, ‖word (O k) w U - (M : ℂ) ^ w.length‖ ∂μ k) atTop (𝓝 0) := by
  induction w with
  | nil => simp [word]
  | cons i w ih =>
    have hbd (k : ℕ) (U : Ω k) : ‖word (O k) w U‖ ≤ M ^ w.length := by
      have := word_norm_le (O k) (fun _ => M) (fun _ => hM) (hle k) w U
      simpa [wordBound] using this
    have hW (k : ℕ) : Continuous fun U => ‖word (O k) w U - (M : ℂ) ^ w.length‖ :=
      ((word_continuous _ (hO k) w).sub continuous_const).norm
    have hL (k : ℕ) : Continuous fun U => ‖O k i U - M‖ := ((hO k i).sub continuous_const).norm
    have hC (k : ℕ) : Continuous fun U => ‖word (O k) (i :: w) U - (M : ℂ) ^ (i :: w).length‖ :=
      ((word_continuous _ (hO k) _).sub continuous_const).norm
    have hbound (k : ℕ) : ∫ U, ‖word (O k) (i :: w) U - (M : ℂ) ^ (i :: w).length‖ ∂μ k ≤
        M ^ w.length * ∫ U, ‖O k i U - M‖ ∂μ k + M * ∫ U, ‖word (O k) w U - (M : ℂ) ^ w.length‖ ∂μ k := by
      have hI₁ : Integrable (fun U => M ^ w.length * ‖O k i U - M‖) (μ k) :=
        (continuous_const.mul (hL k)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hI₂ : Integrable (fun U => M * ‖word (O k) w U - (M : ℂ) ^ w.length‖) (μ k) :=
        (continuous_const.mul (hW k)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add hI₁ hI₂]
      refine integral_mono ((hC k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (hI₁.add hI₂) fun U => ?_
      have e : word (O k) (i :: w) U - (M : ℂ) ^ (i :: w).length =
          (O k i U - M) * word (O k) w U + M * (word (O k) w U - (M : ℂ) ^ w.length) := by
        rw [word_cons, List.length_cons, pow_succ]
        ring
      change ‖word (O k) (i :: w) U - (M : ℂ) ^ (i :: w).length‖ ≤
        M ^ w.length * ‖O k i U - M‖ + M * ‖word (O k) w U - (M : ℂ) ^ w.length‖
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hbd k U) (norm_nonneg _)
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hM]
    refine squeeze_zero (fun k => integral_nonneg fun U => norm_nonneg _) hbound ?_
    simpa using ((hd i).const_mul (M ^ w.length)).add (ih.const_mul M)

include hO hM hle in
theorem word_tendsto (hd : ∀ i, Tendsto (fun k => ∫ U, ‖O k i U - M‖ ∂μ k) atTop (𝓝 0)) (w : List ι) :
    Tendsto (fun k => ∫ U, word (O k) w U ∂μ k) atTop (𝓝 ((M : ℂ) ^ w.length)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) (word_tendsto_L1 μ O hO M hM hle hd w)
  have hW : Continuous (word (O k) w) := word_continuous _ (hO k) w
  have hi : Integrable (word (O k) w) (μ k) :=
    hW.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have e : ∫ U, word (O k) w U ∂μ k - (M : ℂ) ^ w.length = ∫ U, (word (O k) w U - (M : ℂ) ^ w.length) ∂μ k := by
    rw [integral_sub hi (integrable_const _)]
    simp
  rw [e]
  exact norm_integral_le_integral_norm _

end Collapse

/-! ### SU(2): the bounded plaquette limit is constant on every trajectory with `β → ∞` -/

section SU2
open TwistedFlow TwistedLocalization TwistedSlice
open WilsonSingleLinkStaples (Q character character_re)

theorem character_norm_le (q : Q) : ‖character q‖ ≤ 2 := by
  have e : character q = ((2 * (q : Quaternion ℝ).re : ℝ) : ℂ) := SU2QuaternionCoordinates.trace_toMatrix q
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have := TwistedFlat.re_le_one q
  norm_num
  linarith only [this]

/-- `log cap(24β) / β → 0`. The Gaussian mass only costs a power of `β`. -/
theorem log_cap_div_tendsto :
    Tendsto (fun β : ℝ => Real.log (SU2GaussianMass.cap (24 * β)) / β) atTop (𝓝 0) := by
  set K : ℝ := 4 * SU2ScalarTilt.partition 0 / Real.Gamma (3 / 2) with hK
  have hKpos : 0 < K := by
    have h1 := SU2ScalarTilt.partition_pos 0
    have h2 := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
    positivity
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using this
  have h2 : Tendsto (fun β : ℝ => 24 * β) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 24)
  have h3 := (h1.comp h2).const_mul (36 : ℝ)
  have h4 : Tendsto (fun β : ℝ => Real.log K / β) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h5 := h4.add h3
  simp only [mul_zero, add_zero] at h5
  refine h5.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with β hβ
  have hs : 0 < 24 * β := by positivity
  have hcap : SU2GaussianMass.cap (24 * β) = K * ((24 * β) * Real.sqrt (24 * β)) := by
    unfold SU2GaussianMass.cap
    rw [hK]
    ring
  have hsq : Real.log (Real.sqrt (24 * β)) = Real.log (24 * β) / 2 := Real.log_sqrt hs.le
  have hsp : 0 < Real.sqrt (24 * β) := Real.sqrt_pos.mpr hs
  rw [hcap, Real.log_mul hKpos.ne' (by positivity), Real.log_mul hs.ne' hsp.ne', hsq]
  simp only [Function.comp]
  field_simp
  ring

variable (N : ℕ → ℕ) [∀ k, NeZero (N k)] (β : ℕ → ℝ)

local instance instLawProb (k : ℕ) : IsProbabilityMeasure (twistedLaw (N k) (β k)) :=
  law_probability (N k) Q (spatialTwist (N k)) character WilsonSingleLinkStaples.character_continuous (β k) 2

/-- The plaquette labels for the actual `SU(2)` twisted law. -/
abbrev su2Labels : LabelSystem Q N PhysLabel :=
  physLabels Q N character WilsonSingleLinkStaples.character_continuous 2 (by norm_num) character_norm_le

theorem plaq_sub_two (n : ℕ) [NeZero n] (U : Configuration (Vertex (2 * n)) Q) (p : PlaquetteIndex (2 * n)) :
    ‖((plaqReal Q n character U p : ℝ) : ℂ) - ((2 : ℝ) : ℂ)‖ = term n Q (spatialTwist n) character 2 U p := by
  have e : ((plaqReal Q n character U p : ℝ) : ℂ) - ((2 : ℝ) : ℂ) =
      ((-(term n Q (spatialTwist n) character 2 U p) : ℝ) : ℂ) := by
    rw [term_eq_sub_plaqReal]
    push_cast
    ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (TwistedFlat.term_nonneg n U p)]

/-- Flowed plaquettes, at an arbitrary flow time `t k` on the `k`-th lattice. Flow times of order `N²` are allowed,
as in Target A. -/
def flowedLabels (t : ℕ → ℝ) : LabelSystem Q N PhysLabel where
  obs k l U := (su2Labels N).obs k l (wf (N k) (t k) U)
  cont k l := ((su2Labels N).cont k l).comp (continuous_wf_right (N k) (t k))
  bound := (su2Labels N).bound
  bound_nonneg := (su2Labels N).bound_nonneg
  obs_le k l _ := (su2Labels N).obs_le k l _

variable {β}

theorem eventually_mean_small (hβ : Tendsto β atTop atTop) :
    Tendsto (fun k => 4 * Real.log (SU2GaussianMass.cap (24 * β k)) / β k) atTop (𝓝 0) := by
  have h := (log_cap_div_tendsto.comp hβ).const_mul (4 : ℝ)
  simp only [mul_zero] at h
  refine h.congr fun k => ?_
  simp only [Function.comp]
  ring

/-- Any choice of plaquette at any flow time has mean squared defect tending to zero, in the lattice's own units. -/
theorem flowed_term_tendsto (hβ : Tendsto β atTop atTop) (t : ℕ → ℝ) (ht : ∀ k, 0 ≤ t k)
    (p : ∀ k, PlaquetteIndex (2 * N k)) :
    Tendsto (fun k => ∫ U, term (N k) Q (spatialTwist (N k)) character 2 (wf (N k) (t k) U) (p k)
      ∂twistedLaw (N k) (β k)) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => TwistedFlat.term_nonneg _ _ _) ?_
    (eventually_mean_small hβ)
  filter_upwards [hβ.eventually_ge_atTop (1 / 32)] with k hk
  exact law_term_mean_wf (N k) (β k) (ht k) hk (p k)

/-- **Every flowed plaquette Schwinger function converges to a constant.** For every trajectory with `β → ∞`, every
sequence of lattice sizes, and every sequence of flow times, whole sequence and no subsequence. In particular flow
times proportional to `N²` do not change this: an unrenormalized flowed plaquette has no connected limit. This is what
a lattice-scale plaquette is expected to do at `β → ∞` in any asymptotically free theory, including one with a nontrivial
continuum limit, so it is not an obstruction to a continuum theory. It only excludes unrescaled plaquette labels as the
carriers of one. Loops of physical size and rescaled or subtracted observables are not covered. -/
theorem flowed_schwinger_tendsto (hβ : Tendsto β atTop atTop) (t : ℕ → ℝ) (ht : ∀ k, 0 ≤ t k) (w : List PhysLabel) :
    Tendsto (fun k => ∫ U, word ((flowedLabels N t).obs k) w U ∂twistedLaw (N k) (β k)) atTop
      (𝓝 ((((2 : ℝ) : ℂ)) ^ w.length)) := by
  refine word_tendsto (fun k => twistedLaw (N k) (β k)) (fun k => (flowedLabels N t).obs k)
    (fun k i => (flowedLabels N t).cont k i) 2 (by norm_num) (fun k i U => (flowedLabels N t).obs_le k i U)
    (fun l => ?_) w
  have h := flowed_term_tendsto N hβ t ht (fun k => (site (N k) l.1, l.2))
  refine h.congr fun k => ?_
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  exact (plaq_sub_two (N k) _ _).symm

/-- Connected flowed plaquette functions of every order tend to zero. -/
theorem flowed_connected_tendsto (hβ : Tendsto β atTop atTop) (t : ℕ → ℝ) (ht : ∀ k, 0 ≤ t k)
    (a b : List PhysLabel) :
    Tendsto (fun k => ∫ U, word ((flowedLabels N t).obs k) a U * word ((flowedLabels N t).obs k) b U ∂twistedLaw (N k) (β k) -
      (∫ U, word ((flowedLabels N t).obs k) a U ∂twistedLaw (N k) (β k)) *
        ∫ U, word ((flowedLabels N t).obs k) b U ∂twistedLaw (N k) (β k)) atTop (𝓝 0) := by
  have happ (k : ℕ) (U : Configuration (Vertex (2 * N k)) Q) :
      word ((flowedLabels N t).obs k) a U * word ((flowedLabels N t).obs k) b U =
        word ((flowedLabels N t).obs k) (a ++ b) U := by
    simp [word]
  simp only [happ]
  have h := (flowed_schwinger_tendsto N hβ t ht (a ++ b)).sub
    ((flowed_schwinger_tendsto N hβ t ht a).mul (flowed_schwinger_tendsto N hβ t ht b))
  have e : ((2 : ℝ) : ℂ) ^ (a ++ b).length - ((2 : ℝ) : ℂ) ^ a.length * ((2 : ℝ) : ℂ) ^ b.length = 0 := by
    rw [List.length_append, pow_add, sub_self]
  rw [e] at h
  exact h

/-- Reflection invariance of the twisted law. -/
theorem law_θ (n : ℕ) [NeZero n] (b : ℝ) {f : Configuration (Vertex (2 * n)) Q → ℝ} (hf : Continuous f) :
    ∫ U, f (reflectConfiguration (2 * n) Q U) ∂twistedLaw n b = ∫ U, f U ∂twistedLaw n b := by
  rw [TwistedIBP.law_integral, TwistedIBP.law_integral]
  congr 1
  set S := action n Q (spatialTwist n) character b 2 with hS
  have hSc : Continuous S := continuous_action n Q (spatialTwist n) character
    WilsonSingleLinkStaples.character_continuous b 2
  have hinv (U : Configuration (Vertex (2 * n)) Q) : S (reflectConfiguration (2 * n) Q U) = S U := by
    rw [hS, action_eq_mul, action_eq_mul, action_reflect]
  have hg : Continuous fun U => Real.exp (-S U) * f U := (Real.continuous_exp.comp hSc.neg).mul hf
  have hp := reference_preserves_reflection (2 * n) Q
  have hm := integral_map hp.measurable.aemeasurable (f := fun U => Real.exp (-S U) * f U)
    (μ := referenceMeasure Q (Vertex (2 * n))) hg.aestronglyMeasurable
  rw [hp.map_eq] at hm
  rw [hm]
  simp only [hinv]

/-- The letters of a reflected entry: the left word at the configuration, the right word at its reflection. -/
def osLetters {ι : Type*} (L : LabelSystem Q N ι) (k : ℕ) : ι ⊕ ι → Configuration (Vertex (2 * N k)) Q → ℂ
  | Sum.inl l, U => star (L.obs k l U)
  | Sum.inr l, U => L.obs k l (reflectConfiguration (2 * N k) Q U)

theorem osLetters_word {ι : Type*} (L : LabelSystem Q N ι) (k : ℕ) (a b : List ι)
    (U : Configuration (Vertex (2 * N k)) Q) :
    word (osLetters N L k) (a.map Sum.inl ++ b.map Sum.inr) U =
      star (word (L.obs k) a U) * word (L.obs k) b (reflectConfiguration (2 * N k) Q U) := by
  have hl : ∀ a : List ι, word (osLetters N L k) (a.map Sum.inl) U = star (word (L.obs k) a U) := by
    intro a
    induction a with
    | nil => simp
    | cons i a ih =>
      rw [List.map_cons, word_cons, word_cons, ih, star_mul']
      rfl
  have hr : ∀ b : List ι, word (osLetters N L k) (b.map Sum.inr) U =
      word (L.obs k) b (reflectConfiguration (2 * N k) Q U) := by
    intro b
    induction b with
    | nil => simp
    | cons i b ih =>
      rw [List.map_cons, word_cons, word_cons, ih]
      rfl
  have happ : word (osLetters N L k) (a.map Sum.inl ++ b.map Sum.inr) U =
      word (osLetters N L k) (a.map Sum.inl) U * word (osLetters N L k) (b.map Sum.inr) U := by
    simp [word]
  rw [happ, hl, hr]

/-- If every letter of a label system bounded by `2` tends to `2` in mean under the twisted law, every reflected entry
tends to the constant. The reflected letters need no separate bound, by `law_θ`. -/
theorem os_tendsto_of_mean {ι : Type*} (L : LabelSystem Q N ι) (hle : ∀ k l U, ‖L.obs k l U‖ ≤ 2)
    (hd : ∀ l, Tendsto (fun k => ∫ U, ‖L.obs k l U - ((2 : ℝ) : ℂ)‖ ∂twistedLaw (N k) (β k)) atTop (𝓝 0))
    (a b : List ι) :
    Tendsto (fun k => osEntry L (fun k => spatialTwist (N k)) character β 2 k a b) atTop
      (𝓝 (((2 : ℝ) : ℂ) ^ (a.length + b.length))) := by
  have hcont (k : ℕ) (i : ι ⊕ ι) : Continuous (osLetters N L k i) := by
    rcases i with l | l
    · exact (L.cont k l).star
    · exact (L.cont k l).comp (ReflectedDefectBound.continuous_reflection Q (2 * N k))
  have hle' (k : ℕ) (i : ι ⊕ ι) (U : Configuration (Vertex (2 * N k)) Q) :
      ‖osLetters N L k i U‖ ≤ 2 := by
    rcases i with l | l
    · change ‖star _‖ ≤ 2
      rw [norm_star]
      exact hle k l U
    · exact hle k l _
  have hd' (i : ι ⊕ ι) : Tendsto (fun k => ∫ U, ‖osLetters N L k i U - ((2 : ℝ) : ℂ)‖
      ∂twistedLaw (N k) (β k)) atTop (𝓝 0) := by
    rcases i with l | l
    · refine (hd l).congr fun k => integral_congr_ae (Eventually.of_forall fun U => ?_)
      change ‖L.obs k l U - ((2 : ℝ) : ℂ)‖ = ‖star (L.obs k l U) - ((2 : ℝ) : ℂ)‖
      have h2 : star (((2 : ℝ) : ℂ)) = ((2 : ℝ) : ℂ) := Complex.conj_ofReal 2
      rw [← norm_star (L.obs k l U - ((2 : ℝ) : ℂ)), star_sub, h2]
    · refine (hd l).congr fun k => ?_
      have hc : Continuous fun U => ‖L.obs k l U - ((2 : ℝ) : ℂ)‖ := ((L.cont k l).sub continuous_const).norm
      exact (law_θ (N k) (β k) hc).symm
  have h := word_tendsto (fun k => twistedLaw (N k) (β k)) (fun k => osLetters N L k) hcont 2 (by norm_num) hle' hd'
    (a.map Sum.inl ++ b.map Sum.inr)
  simp only [List.length_append, List.length_map] at h
  refine h.congr fun k => integral_congr_ae (Eventually.of_forall fun U => ?_)
  exact osLetters_word N L k a b U

/-- **The reflected flowed plaquette function converges to a constant**, on every trajectory with `β → ∞`, at any flow
times. Flow time zero is the bare plaquette. -/
theorem flowed_os_tendsto (hβ : Tendsto β atTop atTop) (t : ℕ → ℝ) (ht : ∀ k, 0 ≤ t k) (a b : List PhysLabel) :
    Tendsto (fun k => osEntry (flowedLabels N t) (fun k => spatialTwist (N k)) character β 2 k a b) atTop
      (𝓝 (((2 : ℝ) : ℂ) ^ (a.length + b.length))) := by
  refine os_tendsto_of_mean N (flowedLabels N t) (fun k l U => (flowedLabels N t).obs_le k l U) (fun l => ?_) a b
  exact (flowed_term_tendsto N hβ t ht (fun k => (site (N k) l.1, l.2))).congr fun k =>
    integral_congr_ae (Eventually.of_forall fun U => (plaq_sub_two (N k) _ _).symm)

/-- The reflected bare plaquette function converges to the same constant. -/
theorem bare_os_tendsto (hβ : Tendsto β atTop atTop) (a b : List PhysLabel) :
    Tendsto (fun k => osEntry (su2Labels N) (fun k => spatialTwist (N k)) character β 2 k a b) atTop
      (𝓝 (((2 : ℝ) : ℂ) ^ (a.length + b.length))) := by
  refine os_tendsto_of_mean N _ (fun k l U => (su2Labels N).obs_le k l _) (fun l => ?_) a b
  refine (flowed_term_tendsto N hβ (fun _ => 0) (fun _ => le_rfl) (fun k => (site (N k) l.1, l.2))).congr fun k =>
    integral_congr_ae (Eventually.of_forall fun U => ?_)
  rw [← plaq_sub_two, wf_zero]
  rfl

/-- **The actual bare limit is constant.** Any subsequential limit of the reflected bare plaquette functions on a
trajectory with `β → ∞` is `2^(number of labels)`. This is the measure content; the next theorem is algebra. -/
theorem bare_limit_is_constant (hβ : Tendsto β atTop atTop) (W : List PhysLabel × List PhysLabel → ℂ) (φ : ℕ → ℕ)
    (hφ : StrictMono φ)
    (hW : ∀ a b, Tendsto (fun k => osEntry (su2Labels N) (fun k => spatialTwist (N k)) character β 2 (φ k) a b) atTop
      (𝓝 (W (a, b)))) :
    W = fun p => ((2 : ℝ) : ℂ) ^ (p.1.length + p.2.length) := by
  funext p
  exact tendsto_nhds_unique (hW p.1 p.2) ((bare_os_tendsto N hβ p.1 p.2).comp hφ.tendsto_atTop)

/-- The same for flowed labels, at any flow times. `LimitPackage` holds for this limit by `constant_package`, so the
lattice-scale flowed family does satisfy reflection positivity in the limit, whatever it does on a finite lattice. -/
theorem flowed_limit_is_constant (hβ : Tendsto β atTop atTop) (t : ℕ → ℝ) (ht : ∀ k, 0 ≤ t k)
    (W : List PhysLabel × List PhysLabel → ℂ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hW : ∀ a b, Tendsto (fun k => osEntry (flowedLabels N t) (fun k => spatialTwist (N k)) character β 2 (φ k) a b)
      atTop (𝓝 (W (a, b)))) :
    W = fun p => ((2 : ℝ) : ℂ) ^ (p.1.length + p.2.length) := by
  funext p
  exact tendsto_nhds_unique (hW p.1 p.2) ((flowed_os_tendsto N hβ t ht p.1 p.2).comp hφ.tendsto_atTop)

/-- The constant has a Gram form of rank one, so the Hilbert space it reconstructs has dimension at most one. -/
theorem constant_gram {ι J : Type*} (s : Finset J) (w : J → List ι) (e : J → ℂ) :
    ∑ i ∈ s, ∑ j ∈ s, star (e i) * e j * ((2 : ℝ) : ℂ) ^ ((w i).length + (w j).length) =
      star (∑ j ∈ s, e j * ((2 : ℝ) : ℂ) ^ (w j).length) * ∑ j ∈ s, e j * ((2 : ℝ) : ℂ) ^ (w j).length := by
  rw [star_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [star_mul', star_pow, pow_add]
  have : star (((2 : ℝ) : ℂ)) = ((2 : ℝ) : ℂ) := Complex.conj_ofReal 2
  rw [this]
  ring

/-- **`LimitPackage` cannot imply nontriviality.** This is algebra about the constant `2^(number of labels)`: no
measure, no hypothesis on the trajectory, and any choice of positive labels. So the package has a one-dimensional
model for every label system bounded by `2`, and any argument for nontriviality has to use something else. -/
theorem constant_package {ι : Type*} (L : LabelSystem Q N ι) (hb : ∀ l, L.bound l = 2) (Pos : ι → Prop) :
    LimitPackage L Pos (fun p => ((2 : ℝ) : ℂ) ^ (p.1.length + p.2.length)) := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro a b
    have hfun : L.bound = fun _ => 2 := funext hb
    have h (l : List ι) : wordBound L.bound l = 2 ^ l.length := by
      simp [wordBound, hfun]
    rw [h, h]
    simp [pow_add]
  · intro a a' b b' ha hb'
    simp [ha.length_eq, hb'.length_eq]
  · intro J s w e _
    classical
    rw [constant_gram]
    set v := ∑ j ∈ s, e j * ((2 : ℝ) : ℂ) ^ (w j).length
    have h : star v * v = ((Complex.normSq v : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.normSq_eq_conj_mul_self]
    rw [h]
    exact ⟨by simpa using Complex.normSq_nonneg v, by simp⟩

end SU2

/-! ### A volume-free lower bound on the mean plaquette defect

Integration by parts along one link, in its three colours. With `D` the sum of the mean squared defects of the six
plaquettes through a link, `E[(∂S)²] = E[∂²S]` reads, up to the elementary bounds below, `12 β D ≥ 18 - 3 D / 2`. -/

section Floor
open TwistedFlow TwistedLocalization TwistedSlice TwistedIBP TwistedHessianField TwistedActionJet
open TwistedSmallField TwistedHessian
open WilsonSingleLinkStaples (Q character character_re)
open scoped Quaternion

/-- At most one of four quaternions is nonzero. -/
def OneSlot (A B C D : ℍ[ℝ]) : Prop :=
  (B = 0 ∧ C = 0 ∧ D = 0) ∨ (A = 0 ∧ C = 0 ∧ D = 0) ∨ (A = 0 ∧ B = 0 ∧ D = 0) ∨ (A = 0 ∧ B = 0 ∧ C = 0)

theorem OneSlot.second {A B C D : ℍ[ℝ]} (h : OneSlot A B C D) :
    secondCoeff A B C D = (A + B + C + D) * (A + B + C + D) := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp [secondCoeff]

theorem OneSlot.norm_sq {A B C D : ℍ[ℝ]} (h : OneSlot A B C D) :
    ‖A + B + C + D‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 + ‖C‖ ^ 2 + ‖D‖ ^ 2 := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp

theorem pure_sq_mul_re (Z c : ℍ[ℝ]) (hZ : Z.re = 0) : (Z * Z * c).re = -(‖Z‖ ^ 2 * c.re) := by
  have hn : ‖Z‖ ^ 2 = Z.imI ^ 2 + Z.imJ ^ 2 + Z.imK ^ 2 := by
    rw [sq ‖Z‖, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def', hZ]
    ring
  rw [hn]
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, hZ]
  ring

theorem rate_sq_le (Z c : ℍ[ℝ]) (hZ : Z.re = 0) (hc : ‖c‖ = 1) :
    (Z * c).re ^ 2 ≤ ‖Z‖ ^ 2 * (2 - 2 * c.re) := by
  have hn : ‖Z‖ ^ 2 = Z.imI ^ 2 + Z.imJ ^ 2 + Z.imK ^ 2 := by
    rw [sq ‖Z‖, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def', hZ]
    ring
  have hcn : c.re ^ 2 + c.imI ^ 2 + c.imJ ^ 2 + c.imK ^ 2 = 1 := by
    have : ‖c‖ ^ 2 = 1 := by rw [hc]; norm_num
    rw [sq ‖c‖, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def'] at this
    linarith only [this]
  rw [hn]
  simp only [Quaternion.re_mul, hZ, zero_mul, zero_sub]
  have hcs : (Z.imI * c.imI + Z.imJ * c.imJ + Z.imK * c.imK) ^ 2 ≤
      (Z.imI ^ 2 + Z.imJ ^ 2 + Z.imK ^ 2) * (c.imI ^ 2 + c.imJ ^ 2 + c.imK ^ 2) := by
    nlinarith only [sq_nonneg (Z.imI * c.imJ - Z.imJ * c.imI), sq_nonneg (Z.imI * c.imK - Z.imK * c.imI),
      sq_nonneg (Z.imJ * c.imK - Z.imK * c.imJ)]
  have hr : c.imI ^ 2 + c.imJ ^ 2 + c.imK ^ 2 ≤ 2 - 2 * c.re := by
    nlinarith only [hcn, sq_nonneg (1 - c.re)]
  have hZn : 0 ≤ Z.imI ^ 2 + Z.imJ ^ 2 + Z.imK ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hr hZn
  have e : (-(Z.imI * c.imI) - Z.imJ * c.imJ - Z.imK * c.imK) ^ 2 =
      (Z.imI * c.imI + Z.imJ * c.imJ + Z.imK * c.imK) ^ 2 := by ring
  rw [e]
  exact hcs.trans this

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

theorem term_eq_plaqC (X : Fin 3 → Fin 4 → Section (2 * n)) (U : Configuration V' Q) (p : PlaquetteIndex (2 * n)) :
    term n Q (spatialTwist n) character 2 U p =
      2 - 2 * (plaqC n (linkValue (2 * n) Q U) X p.1 p.2.1.1 p.2.1.2).re := by
  rcases p with ⟨x, ⟨⟨μ, ν⟩, h⟩⟩
  have e := term_cfg n (linkValue (2 * n) Q U) X 0 x μ ν h
  have hf : cfg n (linkValue (2 * n) Q U) X 0 = U := flow_zero n X U
  rw [hf] at e
  rw [e]
  simp [G, plaqC]

/-- The unit vector of one link, in the colour direction `v`. -/
def unitLink (v : Fin 3 → ℝ) (x₀ : V') (m : Fin 4) : Fin 3 → Fin 4 → Section (2 * n) :=
  fun a μ => if μ = m then v a • EuclideanSpace.single x₀ (1 : ℝ) else 0

/-- The first colour direction. -/
def e₀ : Fin 3 → ℝ := fun a => if a = 0 then 1 else 0

theorem e₀_unit : ∑ a, e₀ a ^ 2 = 1 := by
  simp [e₀]

theorem imag_unitLink (v : Fin 3 → ℝ) (x₀ : V') (m μ : Fin 4) (y : V') :
    imag (unitLink n v x₀ m) μ y = if μ = m ∧ y = x₀ then ∑ a, v a • basis a else 0 := by
  classical
  unfold imag unitLink
  by_cases hμ : μ = m
  · by_cases hy : y = x₀
    · simp [hμ, hy]
    · simp [hμ, hy]
  · simp [hμ]

theorem norm_imag_unitLink {v : Fin 3 → ℝ} (hv : ∑ a, v a ^ 2 = 1) (x₀ : V') (m μ : Fin 4) (y : V') :
    ‖imag (unitLink n v x₀ m) μ y‖ ^ 2 = if μ = m ∧ y = x₀ then 1 else 0 := by
  rw [imag_unitLink]
  split_ifs
  · rw [basis_coord_norm, hv]
  · simp

theorem step_ne (y : V') (κ : Fin 4) : step (2 * n) y κ ≠ y := by
  intro h
  haveI : Fact (1 < 2 * n) := ⟨by have := NeZero.pos n; omega⟩
  have hc := congrFun h κ
  simp only [step, Pi.add_apply, Pi.single_eq_same] at hc
  simp at hc

theorem oneSlot_imag (v : Fin 3 → ℝ) (x₀ : V') (m : Fin 4) (y : V') (μ ν : Fin 4) (h : μ < ν) :
    OneSlot (imag (unitLink n v x₀ m) μ y) (imag (unitLink n v x₀ m) ν (step (2 * n) y μ))
      (imag (unitLink n v x₀ m) μ (step (2 * n) y ν)) (imag (unitLink n v x₀ m) ν y) := by
  have hne : μ ≠ ν := h.ne
  simp only [imag_unitLink]
  by_cases h₁ : μ = m ∧ y = x₀
  · have h₂ : ¬ (ν = m ∧ step (2 * n) y μ = x₀) := fun h' => hne (h₁.1.trans h'.1.symm)
    have h₃ : ¬ (μ = m ∧ step (2 * n) y ν = x₀) := fun h' => step_ne n y ν (h'.2.trans h₁.2.symm)
    have h₄ : ¬ (ν = m ∧ y = x₀) := fun h' => hne (h₁.1.trans h'.1.symm)
    left
    simp [h₂, h₃, h₄]
  · by_cases h₂ : ν = m ∧ step (2 * n) y μ = x₀
    · have h₃ : ¬ (μ = m ∧ step (2 * n) y ν = x₀) := fun h' => hne (h'.1.trans h₂.1.symm)
      have h₄ : ¬ (ν = m ∧ y = x₀) := fun h' => step_ne n y μ (h₂.2.trans h'.2.symm)
      right; left
      simp [h₁, h₃, h₄]
    · by_cases h₃ : μ = m ∧ step (2 * n) y ν = x₀
      · have h₄ : ¬ (ν = m ∧ y = x₀) := fun h' => hne (h₃.1.trans h'.1.symm)
        right; right; left
        simp [h₁, h₂, h₄]
      · right; right; right
        simp [h₁, h₂, h₃]

theorem Y_norms (L : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (x : V') (μ ν : Fin 4) :
    ‖(plaqOf n L X x μ ν).Y₁‖ = ‖imag X μ x‖ ∧ ‖(plaqOf n L X x μ ν).Y₂‖ = ‖imag X ν (step (2 * n) x μ)‖ ∧
      ‖(plaqOf n L X x μ ν).Y₃‖ = ‖imag X μ (step (2 * n) x ν)‖ ∧ ‖(plaqOf n L X x μ ν).Y₄‖ = ‖imag X ν x‖ := by
  dsimp only [plaqOf]
  refine ⟨rfl, conj_norm _ _, ?_, ?_⟩
  · rw [norm_neg, conj_norm]
  · rw [norm_neg, conj_norm]

theorem oneSlot_Y (v : Fin 3 → ℝ) (x₀ : V') (m : Fin 4) (L : V' → Fin 4 → Q) (y : V') (μ ν : Fin 4) (h : μ < ν) :
    OneSlot (plaqOf n L (unitLink n v x₀ m) y μ ν).Y₁ (plaqOf n L (unitLink n v x₀ m) y μ ν).Y₂
      (plaqOf n L (unitLink n v x₀ m) y μ ν).Y₃ (plaqOf n L (unitLink n v x₀ m) y μ ν).Y₄ := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := Y_norms n L (unitLink n v x₀ m) y μ ν
  have z₁ : imag (unitLink n v x₀ m) μ y = 0 → (plaqOf n L (unitLink n v x₀ m) y μ ν).Y₁ = 0 := fun e => by
    rw [← norm_eq_zero, h₁, e, norm_zero]
  have z₂ : imag (unitLink n v x₀ m) ν (step (2 * n) y μ) = 0 → (plaqOf n L (unitLink n v x₀ m) y μ ν).Y₂ = 0 := fun e => by
    rw [← norm_eq_zero, h₂, e, norm_zero]
  have z₃ : imag (unitLink n v x₀ m) μ (step (2 * n) y ν) = 0 → (plaqOf n L (unitLink n v x₀ m) y μ ν).Y₃ = 0 := fun e => by
    rw [← norm_eq_zero, h₃, e, norm_zero]
  have z₄ : imag (unitLink n v x₀ m) ν y = 0 → (plaqOf n L (unitLink n v x₀ m) y μ ν).Y₄ = 0 := fun e => by
    rw [← norm_eq_zero, h₄, e, norm_zero]
  rcases oneSlot_imag n v x₀ m y μ ν h with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
  · exact Or.inl ⟨z₂ a, z₃ b, z₄ c⟩
  · exact Or.inr (Or.inl ⟨z₁ a, z₃ b, z₄ c⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨z₁ a, z₂ b, z₄ c⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨z₁ a, z₂ b, z₃ c⟩))

/-- The weight of a plaquette for this link: one if the plaquette contains it, and zero otherwise. -/
abbrev wt (x₀ : V') (m : Fin 4) (q : PlaquetteIndex (2 * n)) : ℝ :=
  linkSq n (unitLink n e₀ x₀ m) q.1 q.2.1.1 q.2.1.2

/-- The weight does not depend on the colour direction. -/
theorem linkSq_unit {v : Fin 3 → ℝ} (hv : ∑ a, v a ^ 2 = 1) (x₀ : V') (m : Fin 4) (q : PlaquetteIndex (2 * n)) :
    linkSq n (unitLink n v x₀ m) q.1 q.2.1.1 q.2.1.2 = wt n x₀ m q := by
  simp only [wt, linkSq, norm_imag_unitLink n hv, norm_imag_unitLink n e₀_unit]

theorem wt_cases (x₀ : V') (m : Fin 4) (q : PlaquetteIndex (2 * n)) : wt n x₀ m q = 0 ∨ wt n x₀ m q = 1 := by
  rcases q with ⟨y, ⟨⟨μ, ν⟩, h⟩⟩
  have hs := oneSlot_imag n e₀ x₀ m y μ ν h
  simp only [wt, linkSq]
  rcases hs with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ <;> simp only [a, b, c, norm_imag_unitLink n e₀_unit] <;>
    split_ifs <;> norm_num

theorem Zp_norm_sq {v : Fin 3 → ℝ} (hv : ∑ a, v a ^ 2 = 1) (x₀ : V') (m : Fin 4) (L : V' → Fin 4 → Q)
    (q : PlaquetteIndex (2 * n)) :
    ‖Zp n L (unitLink n v x₀ m) q‖ ^ 2 = wt n x₀ m q := by
  rcases q with ⟨y, ⟨⟨μ, ν⟩, h⟩⟩
  obtain ⟨h₁, h₂, h₃, h₄⟩ := Y_norms n L (unitLink n v x₀ m) y μ ν
  rw [← linkSq_unit n hv]
  unfold Zp
  rw [(oneSlot_Y n v x₀ m L y μ ν h).norm_sq, h₁, h₂, h₃, h₄]
  rfl

theorem Zp_re (v : Fin 3 → ℝ) (x₀ : V') (m : Fin 4) (L : V' → Fin 4 → Q) (q : PlaquetteIndex (2 * n)) :
    (Zp n L (unitLink n v x₀ m) q).re = 0 := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := Y_re n L (unitLink n v x₀ m) q.1 q.2.1.1 q.2.1.2
  simp only [Zp, Quaternion.re_add, h₁, h₂, h₃, h₄, add_zero]

/-- The second-order part of one plaquette along a single link. -/
theorem Bp_single {v : Fin 3 → ℝ} (hv : ∑ a, v a ^ 2 = 1) (x₀ : V') (m : Fin 4) (q : PlaquetteIndex (2 * n)) (U : Configuration V' Q) :
    Bp n (unitLink n v x₀ m) q U = -(wt n x₀ m q * (1 - term n Q (spatialTwist n) character 2 U q / 2)) := by
  have hc := term_eq_plaqC n (unitLink n v x₀ m) U q
  have hslot : Sc n (linkValue (2 * n) Q U) (unitLink n v x₀ m) q =
      Zp n (linkValue (2 * n) Q U) (unitLink n v x₀ m) q * Zp n (linkValue (2 * n) Q U) (unitLink n v x₀ m) q := by
    rcases q with ⟨y, ⟨⟨μ, ν⟩, h⟩⟩
    unfold Sc Zp
    dsimp only
    exact (oneSlot_Y n v x₀ m (linkValue (2 * n) Q U) y μ ν h).second
  have hre := pure_sq_mul_re (Zp n (linkValue (2 * n) Q U) (unitLink n v x₀ m) q)
    (plaqC n (linkValue (2 * n) Q U) (unitLink n v x₀ m) q.1 q.2.1.1 q.2.1.2) (Zp_re n v x₀ m _ q)
  have hn := Zp_norm_sq n hv x₀ m (linkValue (2 * n) Q U) q
  rw [hn, ← hslot] at hre
  have hB : Bp n (unitLink n v x₀ m) q U = (Sc n (linkValue (2 * n) Q U) (unitLink n v x₀ m) q *
      plaqC n (linkValue (2 * n) Q U) (unitLink n v x₀ m) q.1 q.2.1.1 q.2.1.2).re := rfl
  rw [hB, hre, hc]
  ring

theorem Ap_sq_single {v : Fin 3 → ℝ} (hv : ∑ a, v a ^ 2 = 1) (x₀ : V') (m : Fin 4) (q : PlaquetteIndex (2 * n)) (U : Configuration V' Q) :
    Ap n (unitLink n v x₀ m) q U ^ 2 ≤ wt n x₀ m q * term n Q (spatialTwist n) character 2 U q := by
  have hc := term_eq_plaqC n (unitLink n v x₀ m) U q
  unfold Ap
  rw [hc, ← Zp_norm_sq n hv x₀ m (linkValue (2 * n) Q U) q]
  exact rate_sq_le _ _ (Zp_re n v x₀ m _ q) (norm_plaqC n _ _ _ _ _)

theorem Ap_of_wt {v : Fin 3 → ℝ} (hv : ∑ a, v a ^ 2 = 1) (x₀ : V') (m : Fin 4) (q : PlaquetteIndex (2 * n)) (U : Configuration V' Q) :
    wt n x₀ m q * Ap n (unitLink n v x₀ m) q U = Ap n (unitLink n v x₀ m) q U := by
  rcases wt_cases n x₀ m q with h | h
  · have h' := Ap_sq_single n hv x₀ m q U
    rw [h, zero_mul] at h'
    have : Ap n (unitLink n v x₀ m) q U = 0 := by nlinarith only [h', sq_nonneg (Ap n (unitLink n v x₀ m) q U)]
    rw [this, mul_zero]
  · rw [h, one_mul]

theorem unitLink_norm {v : Fin 3 → ℝ} (hv : ∑ a, v a ^ 2 = 1) (x₀ : V') (m : Fin 4) :
    ∑ a, ∑ μ, ‖unitLink n v x₀ m a μ‖ ^ 2 = 1 := by
  classical
  rw [← hv]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single m]
  · simp [unitLink, norm_smul]
  · intro μ _ hμ
    simp [unitLink, hμ]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem wt_sum (x₀ : V') (m : Fin 4) : ∑ q, wt n x₀ m q = 6 := by
  have h := link_count n (unitLink n e₀ x₀ m)
  rw [unitLink_norm n e₀_unit, mul_one] at h
  exact h

theorem Ttot_sq_le {v : Fin 3 → ℝ} (hv : ∑ a, v a ^ 2 = 1) (x₀ : V') (m : Fin 4) (U : Configuration V' Q) :
    Ttot n (unitLink n v x₀ m) U ^ 2 ≤ 6 * ∑ q, wt n x₀ m q * term n Q (spatialTwist n) character 2 U q := by
  have e : Ttot n (unitLink n v x₀ m) U = ∑ q, wt n x₀ m q * Ap n (unitLink n v x₀ m) q U :=
    Finset.sum_congr rfl fun q _ => (Ap_of_wt n hv x₀ m q U).symm
  rw [e]
  refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans ?_
  have hw : ∑ q, wt n x₀ m q ^ 2 = 6 := by
    rw [← wt_sum n x₀ m]
    refine Finset.sum_congr rfl fun q _ => ?_
    rcases wt_cases n x₀ m q with h | h <;> simp [h]
  rw [hw]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q _ => Ap_sq_single n hv x₀ m q U) (by norm_num)

/-- The basic colour directions. -/
def eC (c : Fin 3) : Fin 3 → ℝ := fun a => if a = c then 1 else 0

theorem eC_unit (c : Fin 3) : ∑ a, eC c a ^ 2 = 1 := by
  rw [Finset.sum_eq_single c]
  · simp [eC]
  · intro a _ ha
    simp [eC, ha]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The rate along one link is linear in the colour direction. -/
theorem Ttot_linear (v : Fin 3 → ℝ) (x₀ : V') (m : Fin 4) (U : Configuration V' Q) :
    Ttot n (unitLink n v x₀ m) U = ∑ c, v c * Ttot n (unitLink n (eC c) x₀ m) U := by
  have himag (μ : Fin 4) (y : V') : imag (unitLink n v x₀ m) μ y = ∑ c, v c • imag (unitLink n (eC c) x₀ m) μ y := by
    simp only [imag_unitLink]
    split_ifs
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_eq_single c]
      · simp [eC]
      · intro a _ ha
        simp [eC, ha]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · simp
  have hZp (q : PlaquetteIndex (2 * n)) : Zp n (linkValue (2 * n) Q U) (unitLink n v x₀ m) q =
      ∑ c, v c • Zp n (linkValue (2 * n) Q U) (unitLink n (eC c) x₀ m) q := by
    unfold Zp plaqOf
    dsimp only
    rw [himag, himag, himag, himag]
    simp only [Fin.sum_univ_three, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, neg_add, smul_add, smul_neg]
    abel
  have hAp (q : PlaquetteIndex (2 * n)) : Ap n (unitLink n v x₀ m) q U =
      ∑ c, v c * Ap n (unitLink n (eC c) x₀ m) q U := by
    unfold Ap
    rw [hZp]
    have hP (c : Fin 3) : plaqC n (linkValue (2 * n) Q U) (unitLink n (eC c) x₀ m) q.1 q.2.1.1 q.2.1.2 =
        plaqC n (linkValue (2 * n) Q U) (unitLink n v x₀ m) q.1 q.2.1.1 q.2.1.2 := rfl
    simp only [hP, Fin.sum_univ_three, add_mul, smul_mul_assoc, Quaternion.re_add, Quaternion.re_smul, smul_eq_mul]
  unfold Ttot
  simp only [Finset.mul_sum, hAp]
  exact Finset.sum_comm

/-- The three colours of one link together have the same bound as one. -/
theorem sum_Ttot_sq_le (x₀ : V') (m : Fin 4) (U : Configuration V' Q) :
    ∑ c, Ttot n (unitLink n (eC c) x₀ m) U ^ 2 ≤
      6 * ∑ q, wt n x₀ m q * term n Q (spatialTwist n) character 2 U q := by
  set T : Fin 3 → ℝ := fun c => Ttot n (unitLink n (eC c) x₀ m) U with hT
  have hS0 : 0 ≤ ∑ c, T c ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hR0 : 0 ≤ 6 * ∑ q, wt n x₀ m q * term n Q (spatialTwist n) character 2 U q := by
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun q _ => mul_nonneg ?_ (TwistedFlat.term_nonneg n U q))
    rcases wt_cases n x₀ m q with h | h <;> simp [h]
  rcases hS0.eq_or_lt with h0 | hpos
  · change ∑ c, T c ^ 2 ≤ _
    rw [← h0]
    exact hR0
  · set s := Real.sqrt (∑ c, T c ^ 2) with hs
    have hspos : 0 < s := Real.sqrt_pos.mpr hpos
    have hss : s ^ 2 = ∑ c, T c ^ 2 := Real.sq_sqrt hS0
    have hv : ∑ c, (T c / s) ^ 2 = 1 := by
      simp only [div_pow]
      rw [← Finset.sum_div, ← hss]
      exact div_self (by positivity)
    have hTv : Ttot n (unitLink n (fun c => T c / s) x₀ m) U = s := by
      rw [Ttot_linear]
      have e : ∑ c, T c / s * Ttot n (unitLink n (eC c) x₀ m) U = (∑ c, T c ^ 2) / s := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [sq]
        ring
      rw [e, ← hss]
      field_simp
    have h := Ttot_sq_le n hv x₀ m U
    rw [hTv, hss] at h
    exact h

variable (β : ℝ)

/-- **The six plaquettes through one link.** At every `β ≥ 0` and every lattice size, the sum of the mean squared
defects of the plaquettes through a link is at least `12/(8β + 1)`. This is exact at `β = 0`, where each mean is `2`.
The proof uses `E[(∂S)²] = E[∂²S]` in the three colours of the link and elementary quaternion bounds, no translation
invariance and no smallness. Summed over the links through a site it gives `TwistedFlow.law_action_ge`, with the same
constant, so what this adds to that bound is that it holds link by link. -/
theorem link_floor (hβ : 0 ≤ β) (x₀ : V') (m : Fin 4) :
    12 / (8 * β + 1) ≤ ∑ q, wt n x₀ m q * ∫ U, term n Q (spatialTwist n) character 2 U q ∂twistedLaw n β := by
  haveI hprob : IsProbabilityMeasure (twistedLaw n β) :=
    law_probability n Q (spatialTwist n) character WilsonSingleLinkStaples.character_continuous β 2
  have hiT (q : PlaquetteIndex (2 * n)) := integrable_law n β (continuous_term' n q)
  set D := ∑ q, wt n x₀ m q * ∫ U, term n Q (spatialTwist n) character 2 U q ∂twistedLaw n β with hD
  have hB (c : Fin 3) : -∑ q, ∫ U, Bp n (unitLink n (eC c) x₀ m) q U ∂twistedLaw n β = 6 - D / 2 := by
    have e (q : PlaquetteIndex (2 * n)) : ∫ U, Bp n (unitLink n (eC c) x₀ m) q U ∂twistedLaw n β =
        -(wt n x₀ m q * (1 - (∫ U, term n Q (spatialTwist n) character 2 U q ∂twistedLaw n β) / 2)) := by
      simp only [Bp_single n (eC_unit c)]
      rw [integral_neg, integral_const_mul, integral_sub (integrable_const _) ((hiT q).div_const 2),
        integral_const, integral_div]
      simp
    simp only [e, Finset.sum_neg_distrib, neg_neg, mul_sub, mul_one, Finset.sum_sub_distrib, wt_sum]
    rw [hD, Finset.sum_div]
    congr 1
    exact Finset.sum_congr rfl fun q _ => by ring
  have hiC (c : Fin 3) : Integrable (fun U => Ttot n (unitLink n (eC c) x₀ m) U ^ 2) (twistedLaw n β) :=
    integrable_law n β ((Ttot_continuous n _).pow 2)
  have hT : ∑ c, ∫ U, Ttot n (unitLink n (eC c) x₀ m) U ^ 2 ∂twistedLaw n β ≤ 6 * D := by
    rw [← integral_finset_sum _ fun c _ => hiC c]
    have hc : Continuous fun U => 6 * ∑ q, wt n x₀ m q * term n Q (spatialTwist n) character 2 U q :=
      continuous_const.mul (continuous_finset_sum _ fun q _ => continuous_const.mul (continuous_term' n q))
    refine (integral_mono (integrable_finset_sum _ fun c _ => hiC c) (integrable_law n β hc)
      (fun U => sum_Ttot_sq_le n x₀ m U)).trans_eq ?_
    rw [integral_const_mul, integral_finset_sum _ fun q _ => (hiT q).const_mul _, hD]
    congr 1
    exact Finset.sum_congr rfl fun q _ => integral_const_mul _ _
  have hforce (c : Fin 3) : 2 * β * ∫ U, Ttot n (unitLink n (eC c) x₀ m) U ^ 2 ∂twistedLaw n β = 6 - D / 2 := by
    rw [force_sq n β hβ (unitLink n (eC c) x₀ m), hB]
  have hsum : 3 * (6 - D / 2) = 2 * β * ∑ c, ∫ U, Ttot n (unitLink n (eC c) x₀ m) U ^ 2 ∂twistedLaw n β := by
    rw [Finset.mul_sum]
    simp only [hforce]
    simp
    ring
  have hkey : 3 * (6 - D / 2) ≤ 2 * β * (6 * D) := by
    rw [hsum]
    exact mul_le_mul_of_nonneg_left hT (by positivity)
  have hpos : 0 < 8 * β + 1 := by positivity
  rw [div_le_iff₀ hpos]
  nlinarith only [hkey]

/-- The four links of each plaquette. -/
theorem wt_sum_links (q : PlaquetteIndex (2 * n)) : ∑ x₀ : V', ∑ m : Fin 4, wt n x₀ m q = 4 := by
  classical
  rcases q with ⟨y, ⟨⟨μ, ν⟩, h⟩⟩
  have hone (μ' : Fin 4) (y' : V') : ∑ x₀ : V', ∑ m : Fin 4, ‖imag (unitLink n e₀ x₀ m) μ' y'‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single y']
    · rw [Finset.sum_eq_single μ']
      · rw [norm_imag_unitLink n e₀_unit]
        simp
      · intro b _ hb
        rw [norm_imag_unitLink n e₀_unit, if_neg]
        exact fun h' => hb h'.1.symm
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    · intro b _ hb
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [norm_imag_unitLink n e₀_unit, if_neg]
      exact fun h' => hb h'.2.symm
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  simp only [wt, linkSq, Finset.sum_add_distrib, hone]
  norm_num

/-- **The floor at one site**, at every lattice size and `β ≥ 0`. This has the same constant as
`TwistedFlow.law_action_ge`, by a different summation. -/
theorem site_floor (hβ0 : 0 ≤ β) (x : V') :
    12 / (8 * β + 1) ≤ ∑ P : Plane, ∫ U, term n Q (spatialTwist n) character 2 U (x, P) ∂twistedLaw n β := by
  have hsum : ∑ x₀ : V', ∑ m : Fin 4, (12 / (8 * β + 1)) ≤
      ∑ x₀ : V', ∑ m : Fin 4, ∑ q, wt n x₀ m q * ∫ U, term n Q (spatialTwist n) character 2 U q ∂twistedLaw n β :=
    Finset.sum_le_sum fun x₀ _ => Finset.sum_le_sum fun m _ => link_floor n β hβ0 x₀ m
  have hswap : ∑ x₀ : V', ∑ m : Fin 4, ∑ q, wt n x₀ m q * ∫ U, term n Q (spatialTwist n) character 2 U q ∂twistedLaw n β =
      4 * ∫ U, actionOne n U ∂twistedLaw n β := by
    have hi (q : PlaquetteIndex (2 * n)) := integrable_law n β (continuous_term' n q)
    have hact : ∫ U, actionOne n U ∂twistedLaw n β =
        ∑ q, ∫ U, term n Q (spatialTwist n) character 2 U q ∂twistedLaw n β := by
      have : (fun U => actionOne n U) = fun U => ∑ q, term n Q (spatialTwist n) character 2 U q := by
        funext U
        unfold actionOne action
        rw [one_mul]
      rw [this, integral_finset_sum _ fun q _ => hi q]
    rw [hact, Finset.mul_sum]
    simp only [Finset.sum_comm (s := (Finset.univ : Finset (Fin 4))) (t := (Finset.univ : Finset (PlaquetteIndex (2 * n))))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [← Finset.sum_mul, wt_sum_links]
  have hL := law_action_wf_eq n β 0 x
  simp only [wf_zero] at hL
  rw [hswap, hL] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hV := card_vertex_pos n
  have hV' : (0 : ℝ) < (Fintype.card V' : ℕ) := hV
  have : ((Fintype.card V' : ℕ) : ℝ) * ((4 : ℕ) * (12 / (8 * β + 1))) ≤
      4 * (((Fintype.card V' : ℕ) : ℝ) * ∑ P : Plane, ∫ U, term n Q (spatialTwist n) character 2 U (x, P) ∂twistedLaw n β) := hsum
  have h2 : ((Fintype.card V' : ℕ) : ℝ) * (12 / (8 * β + 1)) ≤
      ((Fintype.card V' : ℕ) : ℝ) * ∑ P : Plane, ∫ U, term n Q (spatialTwist n) character 2 U (x, P) ∂twistedLaw n β := by
    push_cast at this
    linarith only [this]
  exact le_of_mul_le_mul_left h2 hV'

/-- **Two-sided bound on the mean action per site, uniform in the lattice size.** At every site, for `β ≥ 1/32`,
`12/(8β + 1) ≤ Σ_P E[term(x, P)] ≤ 4 log cap(24β) / β`. So bare plaquette defects are of order `1/β` up to a logarithm,
at every volume. -/
theorem site_two_sided (hβ : 1 / 32 ≤ β) (x : V') :
    12 / (8 * β + 1) ≤ ∑ P : Plane, ∫ U, term n Q (spatialTwist n) character 2 U (x, P) ∂twistedLaw n β ∧
      ∑ P : Plane, ∫ U, term n Q (spatialTwist n) character 2 U (x, P) ∂twistedLaw n β ≤
        4 * Real.log (SU2GaussianMass.cap (24 * β)) / β :=
  ⟨site_floor n β (by linarith only [hβ]) x, by simpa only [wf_zero] using law_plaquette_mean_wf n β le_rfl hβ x⟩

/-- The action cannot fall faster than `exp(-96 t)` along the flow, by `force_static`. -/
theorem action_wf_lower (U : Configuration V' Q) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-(96 * t)) * actionOne n U ≤ actionOne n (wf n t U) := by
  have hd (s : ℝ) : HasDerivAt (fun r => Real.exp (96 * r) * actionOne n (wf n r U))
      (Real.exp (96 * s) * 96 * actionOne n (wf n s U) + Real.exp (96 * s) * -forceSq n (wf n s U)) s := by
    have h₁ : HasDerivAt (fun r => Real.exp (96 * r)) (Real.exp (96 * s) * 96) s := by
      have := ((hasDerivAt_id s).const_mul (96 : ℝ)).exp
      simpa using this
    exact h₁.mul (hasDerivAt_action_wf n U s)
  have hmono : Monotone fun r => Real.exp (96 * r) * actionOne n (wf n r U) := by
    refine monotone_of_deriv_nonneg (fun r => (hd r).differentiableAt) fun r => ?_
    rw [(hd r).deriv]
    have := force_static n (wf n r U)
    have hE := Real.exp_pos (96 * r)
    nlinarith only [this, hE]
  have h := hmono ht
  simp only [mul_zero, Real.exp_zero, one_mul, wf_zero] at h
  have hE := Real.exp_pos (-(96 * t))
  have e : Real.exp (-(96 * t)) * Real.exp (96 * t) = 1 := by
    rw [← Real.exp_add]
    simp
  calc Real.exp (-(96 * t)) * actionOne n U ≤ Real.exp (-(96 * t)) * (Real.exp (96 * t) * actionOne n (wf n t U)) :=
        mul_le_mul_of_nonneg_left h hE.le
    _ = actionOne n (wf n t U) := by rw [← mul_assoc, e, one_mul]

/-- **A lower bound on the flowed action.** At every site, flow time, size and `β ≥ 0`, the sum of the mean flowed
defects is at least `exp(-96 t) · 12/(8β + 1)`. It is exponentially weak in the flow time, where the free theory has a
power law. It is useful only for `t` of order `log N`. At `t ∝ N²` it says nothing about whether the flowed energy
collapses faster than `N⁻⁴`, which is what the flow coupling of Target A needs excluded. -/
theorem flowed_floor (hβ : 0 ≤ β) {t : ℝ} (ht : 0 ≤ t) (x : V') :
    Real.exp (-(96 * t)) * (12 / (8 * β + 1)) ≤
      ∑ P : Plane, ∫ U, term n Q (spatialTwist n) character 2 (wf n t U) (x, P) ∂twistedLaw n β := by
  have hsite : 12 / (8 * β + 1) ≤ ∑ P : Plane, ∫ U, term n Q (spatialTwist n) character 2 U (x, P) ∂twistedLaw n β :=
    site_floor n β hβ x
  have hE := Real.exp_pos (-(96 * t))
  have hL₀ := law_action_wf_eq n β 0 x
  have hLt := law_action_wf_eq n β t x
  simp only [wf_zero] at hL₀
  have hmono : Real.exp (-(96 * t)) * ∫ U, actionOne n U ∂twistedLaw n β ≤ ∫ U, actionOne n (wf n t U) ∂twistedLaw n β := by
    rw [← integral_const_mul]
    exact integral_mono ((integrable_law n β (continuous_actionOne n)).const_mul _)
      (integrable_law n β ((continuous_actionOne n).comp (continuous_wf_right n t))) fun U => action_wf_lower n U ht
  rw [hL₀, hLt] at hmono
  have hV := card_vertex_pos n
  have hV' : (0 : ℝ) < (Fintype.card V' : ℕ) := hV
  have h₁ : ((Fintype.card V' : ℕ) : ℝ) * (Real.exp (-(96 * t)) *
      ∑ P : Plane, ∫ U, term n Q (spatialTwist n) character 2 U (x, P) ∂twistedLaw n β) ≤
      ((Fintype.card V' : ℕ) : ℝ) * ∑ P : Plane, ∫ U, term n Q (spatialTwist n) character 2 (wf n t U) (x, P) ∂twistedLaw n β := by
    calc _ = Real.exp (-(96 * t)) * (((Fintype.card V' : ℕ) : ℝ) *
          ∑ P : Plane, ∫ U, term n Q (spatialTwist n) character 2 U (x, P) ∂twistedLaw n β) := by ring
      _ ≤ _ := hmono
  have h₂ := le_of_mul_le_mul_left h₁ hV'
  exact (mul_le_mul_of_nonneg_left hsite hE.le).trans h₂

end Floor

/-! ### Lattice-step translations, exact on the lattice and closed under limits -/

section Translate
open TwistedFlow TwistedLocalization
open WilsonSingleLinkStaples (Q character character_re)

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

/-- The law is invariant under the compensated translation, for complex continuous observables as well. -/
theorem law_Rκ_complex (β : ℝ) (κ : Fin 4) {F : Configuration V' Q → ℂ} (hF : Continuous F) :
    ∫ U, F (Rκ n κ U) ∂twistedLaw n β = ∫ U, F U ∂twistedLaw n β := by
  haveI : IsProbabilityMeasure (twistedLaw n β) :=
    law_probability n Q (spatialTwist n) character WilsonSingleLinkStaples.character_continuous β 2
  have hiF : Integrable F (twistedLaw n β) :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hRc : Continuous (Rκ n κ) := by
    unfold Rκ
    fun_prop
  have hiR : Integrable (fun U => F (Rκ n κ U)) (twistedLaw n β) :=
    (hF.comp hRc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply Complex.ext
  · have e₁ : (∫ U, F (Rκ n κ U) ∂twistedLaw n β).re = ∫ U, (F (Rκ n κ U)).re ∂twistedLaw n β :=
      (integral_re hiR).symm
    have e₂ : (∫ U, F U ∂twistedLaw n β).re = ∫ U, (F U).re ∂twistedLaw n β := (integral_re hiF).symm
    rw [e₁, e₂]
    exact law_Rκ n β κ (Complex.continuous_re.comp hF)
  · have e₁ : (∫ U, F (Rκ n κ U) ∂twistedLaw n β).im = ∫ U, (F (Rκ n κ U)).im ∂twistedLaw n β :=
      (integral_im hiR).symm
    have e₂ : (∫ U, F U ∂twistedLaw n β).im = ∫ U, (F U).im ∂twistedLaw n β := (integral_im hiF).symm
    rw [e₁, e₂]
    exact law_Rκ n β κ (Complex.continuous_im.comp hF)

theorem plaqReal_Rκ (κ : Fin 4) (U : Configuration V' Q) (x : V') (P : Plane) :
    plaqReal Q n character (Rκ n κ U) (x, P) = plaqReal Q n character U (step (2 * n) x κ, P) := by
  have h := term_Rκ n κ U x P
  rw [term_eq_sub_plaqReal, term_eq_sub_plaqReal] at h
  linarith only [h]

/-- A list of plaquette values at flow time `t`, at sites shifted by `s`. -/
def shiftedWord (t : ℝ) (w : List (V' × Plane)) (s : V') (U : Configuration V' Q) : ℂ :=
  word (fun (l : V' × Plane) U => ((plaqReal Q n character (wf n t U) (l.1 + s, l.2) : ℝ) : ℂ)) w U

theorem shiftedWord_continuous (t : ℝ) (w : List (V' × Plane)) (s : V') : Continuous (shiftedWord n t w s) :=
  word_continuous _ (fun _ => Complex.continuous_ofReal.comp
    ((plaqReal_continuous Q n character WilsonSingleLinkStaples.character_continuous _).comp
      (continuous_wf_right n t))) w

theorem shiftedWord_step (t : ℝ) (w : List (V' × Plane)) (s : V') (κ : Fin 4) (U : Configuration V' Q) :
    shiftedWord n t w (step (2 * n) s κ) U = shiftedWord n t w s (Rκ n κ U) := by
  induction w with
  | nil => simp [shiftedWord]
  | cons l w ih =>
    unfold shiftedWord at ih ⊢
    rw [word_cons, word_cons, ih, wf_Rκ, plaqReal_Rκ]
    have e : step (2 * n) (l.1 + s) κ = l.1 + step (2 * n) s κ := by
      simp only [step, add_assoc]
    rw [e]

/-- **Exact translation invariance of the lattice functions**, at any flow time, for any integer vector. -/
theorem shifted_integral (β t : ℝ) (w : List (V' × Plane)) (s : V') :
    ∫ U, shiftedWord n t w s U ∂twistedLaw n β = ∫ U, shiftedWord n t w 0 U ∂twistedLaw n β := by
  have hstep (κ : Fin 4) (y : V') : ∫ U, shiftedWord n t w (step (2 * n) y κ) U ∂twistedLaw n β =
      ∫ U, shiftedWord n t w y U ∂twistedLaw n β := by
    simp only [shiftedWord_step]
    exact law_Rκ_complex n β κ (shiftedWord_continuous n t w y)
  have hre := const_of_step n (fun s => (∫ U, shiftedWord n t w s U ∂twistedLaw n β).re)
    (fun κ y => congrArg Complex.re (hstep κ y)) 0 s
  have him := const_of_step n (fun s => (∫ U, shiftedWord n t w s U ∂twistedLaw n β).im)
    (fun κ y => congrArg Complex.im (hstep κ y)) 0 s
  exact Complex.ext hre him

theorem site_add (a x : Fin 4 → ℚ) (ha : ∀ μ, ∃ m : ℤ, a μ * ((2 * n : ℕ) : ℚ) = m) :
    site n (x + a) = site n x + site n a := by
  funext μ
  obtain ⟨m, hm⟩ := ha μ
  simp only [site, Pi.add_apply]
  rw [add_mul, hm, Int.floor_add_intCast, Int.floor_intCast]
  push_cast
  rfl

end Translate

section TranslateLimit
open TwistedFlow TwistedLocalization
open WilsonSingleLinkStaples (Q character character_re)

variable (N : ℕ → ℕ) [∀ k, NeZero (N k)] (t : ℕ → ℝ)

/-- Move every physical point of a label by the same amount. -/
def shiftLabel (a : Fin 4 → ℚ) (l : PhysLabel) : PhysLabel := (l.1 + a, l.2)

theorem flowed_word_shift (β : ℝ) (k : ℕ) (a : Fin 4 → ℚ)
    (ha : ∀ μ, ∃ m : ℤ, a μ * ((2 * N k : ℕ) : ℚ) = m) (w : List PhysLabel) :
    ∫ U, word ((flowedLabels N t).obs k) (w.map (shiftLabel a)) U ∂twistedLaw (N k) β =
      ∫ U, word ((flowedLabels N t).obs k) w U ∂twistedLaw (N k) β := by
  have hw (w : List PhysLabel) (s : Vertex (2 * N k)) (hs : s = site (N k) a) (U : Configuration (Vertex (2 * N k)) Q) :
      word ((flowedLabels N t).obs k) (w.map (shiftLabel a)) U =
        shiftedWord (N k) (t k) (w.map fun l => (site (N k) l.1, l.2)) s U := by
    induction w with
    | nil => simp [shiftedWord]
    | cons l w ih =>
      unfold shiftedWord at ih ⊢
      rw [List.map_cons, List.map_cons, word_cons, word_cons, ih]
      congr 1
      change ((plaqReal Q (N k) character _ (site (N k) (l.1 + a), l.2) : ℝ) : ℂ) = _
      rw [site_add (N k) a l.1 ha, hs]
  have hw0 (w : List PhysLabel) (U : Configuration (Vertex (2 * N k)) Q) :
      word ((flowedLabels N t).obs k) w U =
        shiftedWord (N k) (t k) (w.map fun l => (site (N k) l.1, l.2)) 0 U := by
    induction w with
    | nil => simp [shiftedWord]
    | cons l w ih =>
      unfold shiftedWord at ih ⊢
      rw [List.map_cons, word_cons, word_cons, ih, add_zero]
      rfl
  simp only [hw w _ rfl, hw0 w]
  exact shifted_integral (N k) β (t k) _ _

/-- Every rational translation is eventually a lattice translation on the trajectory `N k = (k + 1)!`. -/
theorem factorial_grid (a : Fin 4 → ℚ) :
    ∀ᶠ k : ℕ in atTop, ∀ μ, ∃ m : ℤ, a μ * ((2 * (k + 1).factorial : ℕ) : ℚ) = m := by
  rw [show (∀ᶠ k : ℕ in atTop, ∀ μ, ∃ m : ℤ, a μ * ((2 * (k + 1).factorial : ℕ) : ℚ) = m) ↔
    (∀ μ, ∀ᶠ k : ℕ in atTop, ∃ m : ℤ, a μ * ((2 * (k + 1).factorial : ℕ) : ℚ) = m) from eventually_all]
  intro μ
  filter_upwards [eventually_ge_atTop (a μ).den] with k hk
  have hd : (a μ).den ∣ (k + 1).factorial := Nat.dvd_factorial (a μ).den_pos (by omega)
  obtain ⟨c, hc⟩ := hd
  refine ⟨(a μ).num * (2 * c : ℕ), ?_⟩
  have hq : a μ * ((a μ).den : ℚ) = (a μ).num := Rat.mul_den_eq_num _
  rw [hc]
  push_cast
  calc a μ * (2 * (((a μ).den : ℚ) * c)) = (a μ * ((a μ).den : ℚ)) * (2 * c) := by ring
    _ = _ := by rw [hq]

/-- **Translation invariance passes to the limit, for one-word flowed functions.** For flowed plaquette labels, any
subsequential limit of real Schwinger functions, with `S` and its convergence as hypotheses, is invariant under every
rational translation that is eventually a lattice translation. All rationals qualify only on a trajectory like
`N k = (k + 1)!`. This is closedness again. It gives no continuity in the translation and no rotation invariance, and no
reflection positivity for these labels. The family with both is in `sliceFlow_os_limit`. -/
theorem limit_translation (β : ℕ → ℝ) (a : Fin 4 → ℚ)
    (ha : ∀ᶠ k in atTop, ∀ μ, ∃ m : ℤ, a μ * ((2 * N k : ℕ) : ℚ) = m)
    (S : List PhysLabel → ℂ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hS : ∀ w, Tendsto (fun k => ∫ U, word ((flowedLabels N t).obs (φ k)) w U ∂twistedLaw (N (φ k)) (β (φ k))) atTop (𝓝 (S w)))
    (w : List PhysLabel) : S (w.map (shiftLabel a)) = S w := by
  refine tendsto_nhds_unique (hS _) ((hS w).congr' ?_)
  filter_upwards [hφ.tendsto_atTop.eventually ha] with k hk
  exact (flowed_word_shift N t (β (φ k)) (φ k) a hk w).symm

end TranslateLimit

/-! ### The Schwartz-smeared twisted hierarchy, in the language of the untwisted modules -/

section Smeared
open TwistedFlow TwistedLocalization
open WilsonSingleLinkStaples (Q character character_re)
open scoped NNReal

variable (n : ℕ) [NeZero n]

/-- The moment of a tuple of twisted plaquettes. -/
def smearedCoeff (β : ℝ) (m : ℕ) (q : Fin m → PlaquetteIndex (2 * n)) : ℂ :=
  ∫ U, ∏ j, ((plaqReal Q n character U (q j) : ℝ) : ℂ) ∂twistedLaw n β

/-- The cell kernel of the twisted law, by the floor sampler of the untwisted hierarchy. -/
def smearedKernel (a : ℝ) (plane : Plane) (β : ℝ) (m : ℕ) (x : ContinuumControl.Configuration m) : ℂ :=
  smearedCoeff n β m (PeriodicCellSampling.sampleConfiguration m (2 * n) a plane x)

theorem smearedKernel_measurable (a : ℝ) (plane : Plane) (β : ℝ) (m : ℕ) :
    Measurable (smearedKernel n a plane β m) :=
  (measurable_of_countable (smearedCoeff n β m)).comp
    (PeriodicCellSampling.sampleConfiguration_measurable m (2 * n) a plane)

theorem plaq_norm_le (U : Configuration (Vertex (2 * n)) Q) (p : PlaquetteIndex (2 * n)) :
    ‖((plaqReal Q n character U p : ℝ) : ℂ)‖ ≤ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact plaqReal_abs_le Q n character 2 character_norm_le U p

theorem prod_continuous (m : ℕ) (q : Fin m → PlaquetteIndex (2 * n)) :
    Continuous fun U : Configuration (Vertex (2 * n)) Q => ∏ j, ((plaqReal Q n character U (q j) : ℝ) : ℂ) :=
  continuous_finset_prod _ fun j _ => Complex.continuous_ofReal.comp
    (plaqReal_continuous Q n character WilsonSingleLinkStaples.character_continuous (q j))

theorem smearedKernel_bound (a : ℝ) (plane : Plane) (β : ℝ) (m : ℕ) (x : ContinuumControl.Configuration m) :
    ‖smearedKernel n a plane β m x‖ ≤ ((2 ^ m : ℝ≥0) : ℝ) := by
  haveI : IsProbabilityMeasure (twistedLaw n β) :=
    law_probability n Q (spatialTwist n) character WilsonSingleLinkStaples.character_continuous β 2
  push_cast
  refine (norm_integral_le_of_norm_le_const (C := (2 : ℝ) ^ m) (Eventually.of_forall fun U => ?_)).trans (by simp)
  rw [norm_prod]
  refine (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun j _ => plaq_norm_le n U _).trans ?_
  simp

/-- The Schwartz-smeared Schwinger hierarchy of the actual twisted law. -/
def smearedHierarchy (a : ℝ) (plane : Plane) (β : ℝ) : ContinuumControl.Hierarchy :=
  L1HierarchyCompactness.kernelHierarchy (fun m => smearedKernel n a plane β m)
    (fun m => smearedKernel_measurable n a plane β m) (fun m => 2 ^ m)
    (fun m x => smearedKernel_bound n a plane β m x)

theorem prod_sub_le {J : Type*} (s : Finset J) (b : J → ℂ) (h : ∀ j, ‖b j‖ ≤ 2) :
    ‖∏ j ∈ s, b j - (2 : ℂ) ^ s.card‖ ≤ 2 ^ s.card * ∑ j ∈ s, ‖b j - 2‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, Finset.sum_insert hi, pow_succ]
    have hP : ‖∏ j ∈ s, b j‖ ≤ 2 ^ s.card := by
      rw [norm_prod]
      refine (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun j _ => h j).trans ?_
      simp
    have e : b i * ∏ j ∈ s, b j - (2 : ℂ) ^ s.card * 2 =
        (b i - 2) * ∏ j ∈ s, b j + 2 * (∏ j ∈ s, b j - (2 : ℂ) ^ s.card) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    have hd := norm_nonneg (b i - 2)
    have hpow : (0 : ℝ) < 2 ^ s.card := by positivity
    have h₁ : ‖b i - 2‖ * ‖∏ j ∈ s, b j‖ ≤ ‖b i - 2‖ * 2 ^ s.card := mul_le_mul_of_nonneg_left hP hd
    have h₂ := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 2)
    have e₂ : (2 : ℝ) ^ (s.card + 1) = 2 * 2 ^ s.card := by ring
    rw [e₂]
    nlinarith only [h₁, h₂, mul_nonneg hd hpow.le]

theorem smearedCoeff_sub_le (β : ℝ) (hβ : 1 / 32 ≤ β) (m : ℕ) (q : Fin m → PlaquetteIndex (2 * n)) :
    ‖smearedCoeff n β m q - (2 : ℂ) ^ m‖ ≤
      2 ^ m * (m * (4 * Real.log (SU2GaussianMass.cap (24 * β)) / β)) := by
  haveI : IsProbabilityMeasure (twistedLaw n β) :=
    law_probability n Q (spatialTwist n) character WilsonSingleLinkStaples.character_continuous β 2
  have hi : Integrable (fun U : Configuration (Vertex (2 * n)) Q => ∏ j, ((plaqReal Q n character U (q j) : ℝ) : ℂ))
      (twistedLaw n β) :=
    (prod_continuous n m q).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have e : smearedCoeff n β m q - (2 : ℂ) ^ m =
      ∫ U, (∏ j, ((plaqReal Q n character U (q j) : ℝ) : ℂ) - (2 : ℂ) ^ m) ∂twistedLaw n β := by
    rw [integral_sub hi (integrable_const _)]
    simp [smearedCoeff]
  rw [e]
  have hiT (p : PlaquetteIndex (2 * n)) := integrable_law n β (continuous_term' n p)
  have hpt (U : Configuration (Vertex (2 * n)) Q) :
      ‖∏ j, ((plaqReal Q n character U (q j) : ℝ) : ℂ) - (2 : ℂ) ^ m‖ ≤
        2 ^ m * ∑ j, term n Q (spatialTwist n) character 2 U (q j) := by
    have h := prod_sub_le (Finset.univ : Finset (Fin m)) (fun j => ((plaqReal Q n character U (q j) : ℝ) : ℂ))
      (fun j => plaq_norm_le n U (q j))
    simp only [Finset.card_univ, Fintype.card_fin] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have := plaq_sub_two n U (q j)
    push_cast at this
    exact this
  refine (norm_integral_le_of_norm_le ((integrable_finset_sum _ fun j _ => hiT (q j)).const_mul _)
    (Eventually.of_forall hpt)).trans ?_
  rw [integral_const_mul, integral_finset_sum _ fun j _ => hiT (q j)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hs : ∑ j, ∫ U, term n Q (spatialTwist n) character 2 U (q j) ∂twistedLaw n β ≤
      ∑ _j : Fin m, (4 * Real.log (SU2GaussianMass.cap (24 * β)) / β) :=
    Finset.sum_le_sum fun j _ => law_term_mean n β hβ (q j)
  simpa using hs

variable (N : ℕ → ℕ) [∀ k, NeZero (N k)] (a : ℕ → ℝ) (plane : Plane) {β : ℕ → ℝ}

/-- A common subsequence at every order and every Schwartz test, for any trajectory. This is the twisted form of
`WilsonCellCompactness.exists_hierarchy_limit`, with the same content: boundedness and compactness only. -/
theorem smeared_exists_limit (β : ℕ → ℝ) :
    ∃ (W : ContinuumControl.Hierarchy) (φ : ℕ → ℕ), StrictMono φ ∧
      ContinuumControl.WeakConvergence
        (fun k => smearedHierarchy (N (φ k)) (a (φ k)) plane (β (φ k))) W ∧
      ∀ m f, ‖W.correlation m f‖ ≤ BoundedKernelDistribution.boundSeminorm volume (2 ^ m) f := by
  obtain ⟨W, φ, hφ, hW, hb⟩ := L1HierarchyCompactness.exists_bounded_kernel_hierarchy_limit
    (fun m k => smearedKernel (N k) (a k) plane (β k) m)
    (fun m k => smearedKernel_measurable (N k) (a k) plane (β k) m) (fun m => 2 ^ m)
    (fun m k x => smearedKernel_bound (N k) (a k) plane (β k) m x)
  exact ⟨W, φ, hφ, hW, hb⟩

/-- **The smeared bare twisted hierarchy converges to a constant distribution, on any trajectory with `β → ∞`.** At
every order and every Schwartz test the whole sequence tends to `2^m ∫ f`, whatever the lattice sizes and spacings.
This is the twisted analogue of the collapse in `OSWeakCouplingCollapse`, with an explicit rate. -/
theorem smeared_tendsto_constant (hβ : Tendsto β atTop atTop) (m : ℕ) (f : ContinuumControl.CorrelationTest m) :
    Tendsto (fun k => (smearedHierarchy (N k) (a k) plane (β k)).correlation m f) atTop
      (𝓝 ((2 : ℂ) ^ m * ∫ x, f x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hrate := ((eventually_mean_small hβ).const_mul ((2 : ℝ) ^ m * (m : ℝ))).mul_const (∫ x, ‖f x‖)
  simp only [mul_zero, zero_mul] at hrate
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hrate
  filter_upwards [hβ.eventually_ge_atTop (1 / 32)] with k hk
  have hfi : Integrable f (volume : Measure (ContinuumControl.Configuration m)) := f.integrable
  have hKi := BoundedKernelDistribution.kernel_integrable volume (smearedKernel (N k) (a k) plane (β k) m)
    (smearedKernel_measurable (N k) (a k) plane (β k) m) (2 ^ m)
    (fun x => smearedKernel_bound (N k) (a k) plane (β k) m x) f
  have e : (smearedHierarchy (N k) (a k) plane (β k)).correlation m f - (2 : ℂ) ^ m * ∫ x, f x =
      ∫ x, (smearedKernel (N k) (a k) plane (β k) m x - (2 : ℂ) ^ m) * f x := by
    have : (smearedHierarchy (N k) (a k) plane (β k)).correlation m f =
        ∫ x, smearedKernel (N k) (a k) plane (β k) m x * f x := rfl
    rw [this, ← integral_const_mul, ← integral_sub hKi (hfi.const_mul _)]
    simp only [sub_mul]
  rw [e]
  set C := (2 : ℝ) ^ m * (m : ℝ) * (4 * Real.log (SU2GaussianMass.cap (24 * β k)) / β k) with hC
  have hpt (x : ContinuumControl.Configuration m) :
      ‖(smearedKernel (N k) (a k) plane (β k) m x - (2 : ℂ) ^ m) * f x‖ ≤ C * ‖f x‖ := by
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have := smearedCoeff_sub_le (N k) (β k) hk m (PeriodicCellSampling.sampleConfiguration m (2 * N k) (a k) plane x)
    rw [hC, mul_assoc]
    exact this
  refine (norm_integral_le_of_norm_le (hfi.norm.const_mul C) (Eventually.of_forall hpt)).trans ?_
  rw [integral_const_mul]

end Smeared

/-! ### Which rescalings of a plaquette can have a finite nonzero limit -/

section Window
open TwistedFlow TwistedLocalization
open WilsonSingleLinkStaples (Q character character_re)

variable (N : ℕ → ℕ) [∀ k, NeZero (N k)] {β : ℕ → ℝ}

theorem denom_pos {b : ℝ} (hb : 1 / 32 ≤ b) : 0 < 8 * b + 1 := by linarith only [hb]

/-- **An unsubtracted bare plaquette cannot be rescaled faster than `β`.** If `Z k/(8 β k + 1) → ∞`, the mean of
`Z k` times the defect sum at any site diverges, so the rescaled bare family has no bounded limit at all. -/
theorem rescaled_bare_diverges (Z : ℕ → ℝ) (hβ : ∀ k, 1 / 32 ≤ β k)
    (hZ : Tendsto (fun k => Z k / (8 * β k + 1)) atTop atTop) (x : ∀ k, Vertex (2 * N k)) :
    Tendsto (fun k => Z k * ∑ P : Plane, ∫ U, term (N k) Q (spatialTwist (N k)) character 2 U (x k, P)
      ∂twistedLaw (N k) (β k)) atTop atTop := by
  have h12 : Tendsto (fun k => 12 * (Z k / (8 * β k + 1))) atTop atTop :=
    hZ.const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono' _ ?_ h12
  filter_upwards [hZ.eventually_gt_atTop 0] with k hk
  have hd := denom_pos (hβ k)
  have hZ0 : 0 < Z k := by
    by_contra hc
    push_neg at hc
    have := div_nonpos_of_nonpos_of_nonneg hc hd.le
    linarith only [this, hk]
  have h := mul_le_mul_of_nonneg_left (site_two_sided (N k) (β k) (hβ k) (x k)).1 hZ0.le
  calc 12 * (Z k / (8 * β k + 1)) = Z k * (12 / (8 * β k + 1)) := by ring
    _ ≤ _ := h

/-- **The quartic divergence.** A lattice energy density in physical units multiplies the plaquette defect by the
fourth power of the side. If `β` grows no faster than a cubic in the size, in particular on every asymptotically free
trajectory, the unsubtracted mean diverges. This is the expected mixing with the identity, not a sign of trouble: it
says a uniform bound for a local curvature observable has to subtract, so the compactness of the bounded theorems
above does not reach it. It is a statement about the first moment only. -/
theorem quartic_divergence (hN : Tendsto N atTop atTop) (hβ : ∀ k, 1 / 32 ≤ β k) (C : ℝ) (hC : 0 ≤ C)
    (hle : ∀ k, β k ≤ C * (N k : ℝ) ^ 3) (x : ∀ k, Vertex (2 * N k)) :
    Tendsto (fun k => ((2 * N k : ℕ) : ℝ) ^ 4 * ∑ P : Plane, ∫ U, term (N k) Q (spatialTwist (N k)) character 2 U (x k, P)
      ∂twistedLaw (N k) (β k)) atTop atTop := by
  refine rescaled_bare_diverges N _ hβ ?_ x
  have hNr : Tendsto (fun k => (N k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have hlin : Tendsto (fun k => 16 / (8 * C + 1) * (N k : ℝ)) atTop atTop :=
    hNr.const_mul_atTop (by positivity)
  refine tendsto_atTop_mono (fun k => ?_) hlin
  have hNk : (1 : ℝ) ≤ N k := by exact_mod_cast NeZero.one_le
  have hd := denom_pos (hβ k)
  have hN3 : (0 : ℝ) < (N k : ℝ) ^ 3 := by positivity
  have hdle : 8 * β k + 1 ≤ (8 * C + 1) * (N k : ℝ) ^ 3 := by
    have h1 : (1 : ℝ) ≤ (N k : ℝ) ^ 3 := one_le_pow₀ hNk
    nlinarith only [hle k, h1]
  rw [le_div_iff₀ hd]
  push_cast
  have hC1 : 0 < 8 * C + 1 := by positivity
  calc 16 / (8 * C + 1) * (N k : ℝ) * (8 * β k + 1)
      ≤ 16 / (8 * C + 1) * (N k : ℝ) * ((8 * C + 1) * (N k : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hdle (by positivity)
    _ = (2 * (N k : ℝ)) ^ 4 := by
        field_simp
        ring

/-- The same divergence at small flow times. If `N exp(-96 t) → ∞`, so `t` stays below `log N / 96`, the unsubtracted
flowed energy density in physical units diverges too. So a fixed flow coupling needs flow times beyond that scale. This
says nothing at `t ∝ N²`, which is where Target A works. -/
theorem flowed_quartic_divergence (hN : ∀ k, 1 ≤ N k) (hβ : ∀ k, 0 ≤ β k) (C : ℝ) (hC : 0 ≤ C)
    (hle : ∀ k, β k ≤ C * (N k : ℝ) ^ 3) (t : ℕ → ℝ) (ht : ∀ k, 0 ≤ t k)
    (hsmall : Tendsto (fun k => (N k : ℝ) * Real.exp (-(96 * t k))) atTop atTop) (x : ∀ k, Vertex (2 * N k)) :
    Tendsto (fun k => ((2 * N k : ℕ) : ℝ) ^ 4 * ∑ P : Plane, ∫ U, term (N k) Q (spatialTwist (N k)) character 2
      (wf (N k) (t k) U) (x k, P) ∂twistedLaw (N k) (β k)) atTop atTop := by
  have hlin : Tendsto (fun k => 192 / (8 * C + 1) * ((N k : ℝ) * Real.exp (-(96 * t k)))) atTop atTop :=
    hsmall.const_mul_atTop (by positivity)
  refine tendsto_atTop_mono (fun k => ?_) hlin
  have hNk : (1 : ℝ) ≤ N k := by exact_mod_cast hN k
  have hf := flowed_floor (N k) (β k) (hβ k) (ht k) (x k)
  have hdle : 8 * β k + 1 ≤ (8 * C + 1) * (N k : ℝ) ^ 3 := by
    have h1 : (1 : ℝ) ≤ (N k : ℝ) ^ 3 := one_le_pow₀ hNk
    nlinarith only [hle k, h1]
  have hd : 0 < 8 * β k + 1 := by linarith only [hβ k]
  have hE := Real.exp_pos (-(96 * t k))
  have hP : 0 < ((2 * N k : ℕ) : ℝ) ^ 4 := by
    have : (0 : ℝ) < ((2 * N k : ℕ) : ℝ) := by
      push_cast
      linarith only [hNk]
    positivity
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hf hP.le)
  push_cast
  have hC1 : 0 < 8 * C + 1 := by positivity
  have h12 : 12 / ((8 * C + 1) * (N k : ℝ) ^ 3) ≤ 12 / (8 * β k + 1) :=
    div_le_div_of_nonneg_left (by norm_num) hd hdle
  calc 192 / (8 * C + 1) * ((N k : ℝ) * Real.exp (-(96 * t k)))
      = (2 * (N k : ℝ)) ^ 4 * (Real.exp (-(96 * t k)) * (12 / ((8 * C + 1) * (N k : ℝ) ^ 3))) := by
        have : (N k : ℝ) ≠ 0 := by linarith only [hNk]
        field_simp
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h12 hE.le) (by positivity)

end Window

/-! ### What a reflection-positive stationary kernel can do at coincidence

Item 3 of Target A asks that reflection positivity survive for the flowed functions of item 1. A flowed observable is
not supported on a half lattice, so `reflection_positive` has no proof for it. This section is conditional and abstract:
it says what reflection positivity would force on a stationary two-point kernel. No flowed kernel of the actual law is
known to meet its hypotheses, and the only kernel of a limit identified in this file is the constant one, for which
the conclusion is trivially true. -/

section FlowNoGo

/-- A reflection-positive stationary two-point function, read across a time plane: `K (s + s')` is positive
semidefinite on the strictly positive rational times up to `R`, which are the times `PosLabel` allows. On a time circle
of length `T`, take `R < T / 2`. -/
def HankelPSD (K : ℝ → ℝ) (R : ℝ) : Prop :=
  ∀ (s : Finset ℚ) (e : ℚ → ℝ), (∀ a ∈ s, 0 < a ∧ (a : ℝ) ≤ R) → 0 ≤ ∑ a ∈ s, ∑ b ∈ s, e a * e b * K ((a : ℝ) + b)

/-- Two points suffice: reflection positivity gives midpoint convexity at positive times. -/
theorem hankel_midpoint {K : ℝ → ℝ} {R : ℝ} (h : HankelPSD K R) {a b : ℚ} (ha : 0 < a) (ha' : (a : ℝ) ≤ R) (hb : 0 < b)
    (hb' : (b : ℝ) ≤ R) : 2 * K ((a : ℝ) + b) ≤ K (2 * a) + K (2 * b) := by
  classical
  by_cases hab : a = b
  · subst hab
    have e : (a : ℝ) + a = 2 * a := by ring
    rw [e]
    linarith only
  · have := h {a, b} (fun x => if x = a then 1 else -1) (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨ha, ha'⟩
      · rw [Finset.mem_singleton.mp hx]
        exact ⟨hb, hb'⟩)
    rw [Finset.sum_pair hab, Finset.sum_pair hab, Finset.sum_pair hab] at this
    simp only [if_true, if_neg (Ne.symm hab)] at this
    have e₁ : (a : ℝ) + a = 2 * a := by ring
    have e₂ : (b : ℝ) + b = 2 * b := by ring
    have e₃ : (b : ℝ) + a = a + b := by ring
    rw [e₁, e₂, e₃] at this
    linarith only [this]

/-- **A reflection-positive kernel with zero slope at coincidence never drops below its coincident value.** The
hypothesis is reflection positivity at strictly positive rational times only, and the conclusion is at rational
separations. Time zero is not used: the increments are compared from `x` to `2x` upward, and the slope hypothesis
controls the first step. -/
theorem hankel_floor {K : ℝ → ℝ} {R : ℝ} (h : HankelPSD K R)
    (hd : Tendsto (fun x => (K x - K 0) / x) (𝓝[>] 0) (𝓝 0)) {τ : ℚ} (hτ : 0 < τ) (hτR : (τ : ℝ) ≤ 2 * R) :
    K 0 ≤ K τ := by
  have hτr : (0 : ℝ) < τ := by exact_mod_cast hτ
  -- increments on the rational grid `i x`, `i ≥ 1`, are nondecreasing
  have hgrid (x : ℚ) (hx : 0 < x) (j : ℕ) (hj : (((j : ℝ) + 1) * x) ≤ 2 * R) :
      K (((j : ℝ) + 1) * x) - K x ≥ (j : ℝ) * (K (2 * x) - K x) := by
    have hxr : (0 : ℝ) < x := by exact_mod_cast hx
    have hinc : ∀ i : ℕ, ((i : ℝ) + 2) * x ≤ 2 * R →
        K (2 * x) - K x ≤ K (((i : ℝ) + 2) * x) - K (((i : ℝ) + 1) * x) := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        intro hi
        push_cast at hi ⊢
        have hle : ((i : ℝ) + 2) * x ≤ 2 * R := by nlinarith only [hi, hxr]
        have hm := hankel_midpoint h (a := ((i : ℚ) + 1) * x / 2) (b := ((i : ℚ) + 3) * x / 2)
          (by positivity) (by push_cast; nlinarith only [hi, hxr]) (by positivity) (by
            push_cast
            nlinarith only [hi, hxr])
        push_cast at hm
        have e₁ : ((i : ℝ) + 1) * x / 2 + ((i : ℝ) + 3) * x / 2 = ((i : ℝ) + 2) * x := by ring
        have e₂ : 2 * (((i : ℝ) + 1) * x / 2) = ((i : ℝ) + 1) * x := by ring
        have e₃ : 2 * (((i : ℝ) + 3) * x / 2) = ((i : ℝ) + 3) * x := by ring
        rw [e₁, e₂, e₃] at hm
        have e₄ : (i : ℝ) + 1 + 2 = (i : ℝ) + 3 := by ring
        have e₅ : (i : ℝ) + 1 + 1 = (i : ℝ) + 2 := by ring
        rw [e₄, e₅]
        linarith only [ih hle, hm]
    induction j with
    | zero => simp
    | succ j ih =>
      push_cast at hj ⊢
      have hle : ((j : ℝ) + 1) * x ≤ 2 * R := by nlinarith only [hj, hxr]
      have h₁ := hinc j (by nlinarith only [hj])
      have e₁ : (j : ℝ) + 1 + 1 = (j : ℝ) + 2 := by ring
      rw [e₁]
      have h₂ := ih hle
      nlinarith only [h₁, h₂]
  -- along `x_j = τ/(j+1)` the slope hypothesis controls both correction terms
  set x : ℕ → ℝ := fun j => (τ : ℝ) / ((j : ℝ) + 1) with hxdef
  have hxpos (j : ℕ) : 0 < x j := by
    change 0 < (τ : ℝ) / ((j : ℝ) + 1)
    positivity
  have hx0 : Tendsto x atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, hxdef] using tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop) (a := (τ : ℝ))
  have hxW : Tendsto x atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hx0, Eventually.of_forall hxpos⟩
  have h2xW : Tendsto (fun j => 2 * x j) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun j => mul_pos (by norm_num) (hxpos j)⟩
    simpa using hx0.const_mul (2 : ℝ)
  have hs1 := hd.comp hxW
  have hs2 := hd.comp h2xW
  have hKx : Tendsto (fun j => K (x j)) atTop (𝓝 (K 0)) := by
    have h₁ := (hx0.mul hs1).add_const (K 0)
    simp only [zero_mul, zero_add] at h₁
    refine h₁.congr fun j => ?_
    simp only [Function.comp]
    have := (hxpos j).ne'
    field_simp
    ring
  -- the bounded factor `j x_j` times a null sequence
  have hcorr : Tendsto (fun j : ℕ => (j : ℝ) * (K (2 * x j) - K (x j))) atTop (𝓝 0) := by
    have hnull : Tendsto (fun j => 2 * ((K (2 * x j) - K 0) / (2 * x j)) - (K (x j) - K 0) / x j) atTop (𝓝 0) := by
      simpa [Function.comp] using (hs2.const_mul (2 : ℝ)).sub hs1
    have hb : ∀ j : ℕ, |(j : ℝ) * x j| ≤ τ := by
      intro j
      have hj : (0 : ℝ) ≤ j := by positivity
      rw [abs_of_nonneg (mul_nonneg hj (hxpos j).le)]
      change (j : ℝ) * ((τ : ℝ) / ((j : ℝ) + 1)) ≤ τ
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith only [hτr, hj]
    refine squeeze_zero_norm (a := fun j => (τ : ℝ) * |2 * ((K (2 * x j) - K 0) / (2 * x j)) - (K (x j) - K 0) / x j|) (fun j => ?_) ?_
    · have e : (j : ℝ) * (K (2 * x j) - K (x j)) =
          ((j : ℝ) * x j) * (2 * ((K (2 * x j) - K 0) / (2 * x j)) - (K (x j) - K 0) / x j) := by
        have := (hxpos j).ne'
        field_simp
        ring
      rw [e, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hb j) (abs_nonneg _)
    · simpa using (hnull.abs).const_mul (τ : ℝ)
  have hlim := hKx.add hcorr
  rw [add_zero] at hlim
  refine le_of_tendsto' hlim fun j => ?_
  have hjq : (0 : ℚ) < (j : ℚ) + 1 := by positivity
  have hq := hgrid (τ / ((j : ℚ) + 1)) (div_pos hτ hjq) j (by
    push_cast
    have e : ((j : ℝ) + 1) * ((τ : ℝ) / ((j : ℝ) + 1)) = τ := by field_simp
    rw [e]
    exact hτR)
  push_cast at hq
  have e : ((j : ℝ) + 1) * ((τ : ℝ) / ((j : ℝ) + 1)) = τ := by field_simp
  rw [e] at hq
  change K (x j) + (j : ℝ) * (K (2 * x j) - K (x j)) ≤ K τ
  have hq' : K (τ : ℝ) - K (x j) ≥ (j : ℝ) * (K (2 * x j) - K (x j)) := hq
  linarith only [hq']

/-- The link from `LimitPackage` to `HankelPSD`, for labels at rational times. Stationarity of the limit two-point
function is an input: `exists_limit` supplies a package only for half-supported labels. `package_hankel_constant` is
the only instance in this file. For a flowed family, the package itself would be an assumption. -/
theorem package_hankel {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    {N : ℕ → ℕ} [∀ k, NeZero (N k)] {ι : Type*} (L : LabelSystem G N ι) (Pos : ι → Prop)
    (W : List ι × List ι → ℂ) (hP : LimitPackage L Pos W) (l : ℚ → ι) (K : ℝ → ℝ) (R : ℝ)
    (hl : ∀ a : ℚ, 0 < a → (a : ℝ) ≤ R → Pos (l a))
    (hK : ∀ a b : ℚ, 0 < a → (a : ℝ) ≤ R → 0 < b → (b : ℝ) ≤ R → W ([l a], [l b]) = ((K ((a : ℝ) + b) : ℝ) : ℂ)) :
    HankelPSD K R := by
  intro s e hs
  have h := (hP.reflection_positive s (fun a => [l a]) (fun a => ((e a : ℝ) : ℂ))
    (fun j hj i hi => by
      rw [List.mem_singleton] at hi
      subst hi
      exact hl j (hs j hj).1 (hs j hj).2)).1
  have e₁ : ∑ i ∈ s, ∑ j ∈ s, star (((e i : ℝ) : ℂ)) * ((e j : ℝ) : ℂ) * W ([l i], [l j]) =
      ((∑ a ∈ s, ∑ b ∈ s, e a * e b * K ((a : ℝ) + b) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    rw [hK i j (hs i hi).1 (hs i hi).2 (hs j hj).1 (hs j hj).2, Complex.star_def, Complex.conj_ofReal]
  rw [e₁, Complex.ofReal_re] at h
  exact h

/-- An even function differentiable at zero has zero slope there. -/
theorem slope_of_even {K : ℝ → ℝ} (hev : ∀ x, K (-x) = K x) (hd : DifferentiableAt ℝ K 0) :
    Tendsto (fun x => (K x - K 0) / x) (𝓝[>] 0) (𝓝 0) := by
  have hD := hd.hasDerivAt
  have hneg : HasDerivAt (fun x => K (-x)) (-deriv K 0) 0 := by
    have h' : HasDerivAt K (deriv K 0) (-(0 : ℝ)) := by simpa using hD
    simpa using h'.scomp (0 : ℝ) (hasDerivAt_neg 0)
  have hfn : (fun x => K (-x)) = K := funext hev
  rw [hfn] at hneg
  have hz : deriv K 0 = 0 := by
    have := hD.unique hneg
    linarith only [this]
  have hs := hasDerivAt_iff_tendsto_slope.mp hD
  rw [hz] at hs
  have hs' := hs.mono_left (nhdsWithin_mono 0 (fun x (hx : 0 < x) => (ne_of_gt hx : x ≠ 0)))
  refine hs'.congr fun x => ?_
  simp only [slope, vsub_eq_sub, sub_zero, smul_eq_mul]
  rw [div_eq_inv_mul]

/-- **No kernel smooth at coincidence that decays is reflection positive at positive times.** If `K` is even,
differentiable at zero, and strictly below its coincident value at one positive rational separation in the window,
then it is not positive semidefinite on the positive rational times. A kernel like `exp(-m|τ|)` has a cusp at zero and
escapes. Whether any flowed kernel of the actual law, or of any of its limits, is differentiable at coincidence and
decays is not proved here. -/
theorem not_hankel_of_smooth_decay {K : ℝ → ℝ} {R : ℝ} (hev : ∀ x, K (-x) = K x) (hd : DifferentiableAt ℝ K 0)
    {τ : ℚ} (hτ : 0 < τ) (hτR : (τ : ℝ) ≤ 2 * R) (hdrop : K τ < K 0) : ¬ HankelPSD K R :=
  fun h => absurd (hankel_floor h (slope_of_even hev hd) hτ hτR) (not_le.mpr hdrop)

/-- The hypotheses of `package_hankel` have one instance in this file: the constant limit, whose kernel is constant. So
the floor is an empty statement for it, and `not_hankel_of_smooth_decay` has no instance among the laws here. -/
theorem package_hankel_constant (N : ℕ → ℕ) [∀ k, NeZero (N k)] (P : Plane) : HankelPSD (fun _ => 4) (1 / 4) := by
  refine package_hankel (su2Labels N) PosLabel _ (constant_package N (su2Labels N) (fun _ => rfl) PosLabel)
    (fun q => (fun μ => if μ = 0 then q else 0, P)) _ _ (fun a ha ha' => ?_) (fun a b _ _ _ _ => ?_)
  · have ha'' : a ≤ 1 / 4 := by
      have h' : (a : ℝ) ≤ ((1 / 4 : ℚ) : ℝ) := by
        push_cast
        exact ha'
      exact_mod_cast h'
    exact ⟨by simpa using ha, by
      simp only [if_true]
      linarith only [ha'']⟩
  · norm_num

end FlowNoGo

/-! ### An exact model: the free flowed chain on a time circle of length `2n`

One spatial mode with stiffness `κ > 0`: `c_t` is `exp(2tΔ)(κ - Δ)⁻¹` on the circle, the flowed covariance of a free
field. This is a free model, and not an observable of the twisted law. The twisted Gaussian has this form mode by mode,
with `κ` a nonzero twisted spatial stiffness, but that identification with the gauge field is not formalized here, and
the failure of reflection positivity below is not a theorem about the actual flowed law. -/

section FreeChain
open Real

variable (n : ℕ) (κ : ℝ)

/-- The time momentum of mode `j`. -/
def modeE (j : ℕ) : ℝ := π * j / n

/-- The time stiffness of mode `j`. -/
def modeμ (j : ℕ) : ℝ := 2 - 2 * cos (modeE n j)

/-- The flowed weight of mode `j`. -/
def modeW (t : ℝ) (j : ℕ) : ℝ := exp (-(2 * t * modeμ n j)) / (κ + modeμ n j)

/-- The flowed covariance at time separation `τ`. -/
def chain (t : ℝ) (τ : ℕ) : ℝ :=
  (1 / (2 * n : ℝ)) * ∑ j ∈ Finset.range (2 * n), cos (modeE n j * τ) * modeW n κ t j

theorem modeμ_nonneg (j : ℕ) : 0 ≤ modeμ n j := by
  unfold modeμ
  linarith only [cos_le_one (modeE n j)]

/-- The second difference at unit separation, as a mode sum. -/
theorem chain_second_diff (t : ℝ) :
    chain n κ t 0 + chain n κ t 2 - 2 * chain n κ t 1 =
      -((1 / (2 * n : ℝ)) * ∑ j ∈ Finset.range (2 * n), modeμ n j * cos (modeE n j) * modeW n κ t j) := by
  unfold chain
  rw [← mul_add, mul_left_comm, ← mul_sub, ← mul_neg]
  have h2 : (2 : ℝ) * ∑ j ∈ Finset.range (2 * n), cos (modeE n j * ((1 : ℕ) : ℝ)) * modeW n κ t j =
      ∑ j ∈ Finset.range (2 * n), 2 * (cos (modeE n j * ((1 : ℕ) : ℝ)) * modeW n κ t j) := Finset.mul_sum _ _ _
  rw [h2, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  simp only [one_div, mul_eq_mul_left_iff]
  left
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc2 : cos (modeE n j * ((2 : ℕ) : ℝ)) = 2 * cos (modeE n j) ^ 2 - 1 := by
    rw [show modeE n j * ((2 : ℕ) : ℝ) = 2 * modeE n j by push_cast; ring, cos_two_mul]
  simp only [Nat.cast_zero, mul_zero, cos_zero, Nat.cast_one, mul_one, hc2, modeμ]
  ring

/-- The covariance solves the heat equation `∂ₜ c = 2 Δ c`. -/
theorem chain_heat (t : ℝ) (τ : ℕ) :
    HasDerivAt (fun s => chain n κ s (τ + 1))
      (2 * (chain n κ t (τ + 2) + chain n κ t τ - 2 * chain n κ t (τ + 1))) t := by
  unfold chain
  have hterm (j : ℕ) : HasDerivAt (fun s => cos (modeE n j * ((τ + 1 : ℕ) : ℝ)) * modeW n κ s j)
      (cos (modeE n j * ((τ + 1 : ℕ) : ℝ)) * (-(2 * modeμ n j) * modeW n κ t j)) t := by
    refine HasDerivAt.const_mul _ ?_
    unfold modeW
    have h₁ : HasDerivAt (fun s => -(2 * s * modeμ n j)) (-(2 * modeμ n j)) t := by
      have := ((hasDerivAt_id t).const_mul (2 : ℝ)).mul_const (modeμ n j)
      simpa using this.neg
    have h₂ := (h₁.exp).div_const (κ + modeμ n j)
    convert h₂ using 1
    ring
  have hsum := (HasDerivAt.fun_sum (u := Finset.range (2 * n)) fun j _ => hterm j).const_mul (1 / (2 * n : ℝ))
  convert hsum using 1
  rw [← mul_add]
  have hring : ∀ c A S : ℝ, 2 * (c * A - 2 * (c * S)) = c * (2 * (A - 2 * S)) := fun _ _ _ => by ring
  rw [hring]
  congr 1
  rw [← Finset.sum_add_distrib, Finset.mul_sum _ _ (2 : ℝ), ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e₁ : modeE n j * ((τ + 2 : ℕ) : ℝ) = modeE n j * ((τ + 1 : ℕ) : ℝ) + modeE n j := by push_cast; ring
  have e₂ : modeE n j * (τ : ℝ) = modeE n j * ((τ + 1 : ℕ) : ℝ) - modeE n j := by push_cast; ring
  rw [e₁, e₂, cos_add, cos_sub]
  unfold modeμ
  ring

/-- For `s` strictly between `0` and `2n`, the cosines of mode `j` sum to zero. -/
theorem sum_cos_eq_zero (hn : 0 < n) (s : ℕ) (hs : 0 < s) (hs' : s < 2 * n) :
    ∑ j ∈ Finset.range (2 * n), cos (modeE n j * s) = 0 := by
  set ζ : ℂ := Complex.exp ((π * s / n : ℝ) * Complex.I) with hζ
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have hζT : ζ ^ (2 * n) = 1 := by
    rw [hζ, ← Complex.exp_nat_mul]
    have : ((2 * n : ℕ) : ℂ) * (((π * s / n : ℝ) : ℂ) * Complex.I) = (s : ℂ) * (2 * π * Complex.I) := by
      push_cast
      have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hnR
      field_simp
    rw [this]
    exact Complex.exp_nat_mul_two_pi_mul_I s
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [hζ, Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    have hre : (π * s / n : ℝ) = m * (2 * π) := by
      have h' : ((π * s / n : ℝ) : ℂ) * Complex.I = ((m * (2 * π) : ℝ) : ℂ) * Complex.I := by
        rw [hm]
        push_cast
        ring
      exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero h'
    have hpi : π ≠ 0 := pi_ne_zero
    have hs2 : (s : ℝ) = m * (2 * n) := by
      field_simp at hre
      linarith only [hre]
    have hs3 : (s : ℤ) = m * (2 * n) := by exact_mod_cast hs2
    have hspos : (0 : ℤ) < s := by exact_mod_cast hs
    have hslt : (s : ℤ) < 2 * n := by exact_mod_cast hs'
    have hnpos : (0 : ℤ) < n := by exact_mod_cast hn
    have hm0 : 0 < m := by
      by_contra hc
      push_neg at hc
      nlinarith only [hs3, hc, hnpos, hspos]
    nlinarith only [hs3, hm0, hnpos, hslt]
  have hgeom : ∑ j ∈ Finset.range (2 * n), ζ ^ j = 0 := by
    have := geom_sum_mul ζ (2 * n)
    rw [hζT, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hζ1)
  have hre := congrArg Complex.re hgeom
  rw [Complex.re_sum] at hre
  simp only [Complex.zero_re] at hre
  rw [← hre]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hζ, ← Complex.exp_nat_mul]
  have : (j : ℂ) * (((π * s / n : ℝ) : ℂ) * Complex.I) = ((modeE n j * s : ℝ) : ℂ) * Complex.I := by
    unfold modeE
    push_cast
    ring
  rw [this, Complex.exp_ofReal_mul_I_re]

/-- At flow time zero the chain is the lattice Green function: `(κ - Δ) c₀ = 0` away from the source. -/
theorem chain_green (hn : 0 < n) (hκ : 0 < κ) (τ : ℕ) (hτ : τ + 1 < 2 * n) :
    (κ + 2) * chain n κ 0 (τ + 1) - chain n κ 0 (τ + 2) - chain n κ 0 τ = 0 := by
  unfold chain
  have hsum := sum_cos_eq_zero n hn (τ + 1) (by omega) hτ
  have e : (κ + 2) * ((1 / (2 * n : ℝ)) * ∑ j ∈ Finset.range (2 * n), cos (modeE n j * ((τ + 1 : ℕ) : ℝ)) * modeW n κ 0 j) -
      (1 / (2 * n : ℝ)) * ∑ j ∈ Finset.range (2 * n), cos (modeE n j * ((τ + 2 : ℕ) : ℝ)) * modeW n κ 0 j -
      (1 / (2 * n : ℝ)) * ∑ j ∈ Finset.range (2 * n), cos (modeE n j * (τ : ℝ)) * modeW n κ 0 j =
      (1 / (2 * n : ℝ)) * ∑ j ∈ Finset.range (2 * n), cos (modeE n j * ((τ + 1 : ℕ) : ℝ)) := by
    rw [mul_left_comm, ← mul_sub, ← mul_sub]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e₁ : modeE n j * ((τ + 2 : ℕ) : ℝ) = modeE n j * ((τ + 1 : ℕ) : ℝ) + modeE n j := by push_cast; ring
    have e₂ : modeE n j * (τ : ℝ) = modeE n j * ((τ + 1 : ℕ) : ℝ) - modeE n j := by push_cast; ring
    have hpos : κ + modeμ n j ≠ 0 := by
      have := modeμ_nonneg n j
      positivity
    have hw : modeW n κ 0 j * (κ + modeμ n j) = 1 := by
      unfold modeW
      simp only [mul_zero, zero_mul, neg_zero, exp_zero]
      field_simp
    rw [e₁, e₂, cos_add, cos_sub]
    have hμ : κ + 2 - 2 * cos (modeE n j) = κ + modeμ n j := by
      unfold modeμ
      ring
    calc _ = cos (modeE n j * ((τ + 1 : ℕ) : ℝ)) * (modeW n κ 0 j * (κ + 2 - 2 * cos (modeE n j))) := by ring
      _ = _ := by rw [hμ, hw, mul_one]
  rw [e, hsum, mul_zero]

/-- **At flow time zero the two-point minor at times `0, 1` holds.** This is the one minor checked at `t = 0`. It says
that the failure below comes from the flow, not from the model, at least for this minor. -/
theorem chain_zero_convex (hn : 0 < n) (hκ : 0 < κ) :
    2 * chain n κ 0 1 ≤ chain n κ 0 0 + chain n κ 0 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsd := chain_second_diff n κ 0
  have hE (j : ℕ) : modeE n (n + j) = π + modeE n j := by
    unfold modeE
    push_cast
    field_simp
  have hpair : ∑ j ∈ Finset.range (2 * n), modeμ n j * cos (modeE n j) * modeW n κ 0 j ≤ 0 := by
    rw [two_mul, Finset.sum_range_add, ← Finset.sum_add_distrib]
    refine Finset.sum_nonpos fun j _ => ?_
    set C := cos (modeE n j) with hC
    have hC1 := cos_le_one (modeE n j)
    have hC2 := neg_one_le_cos (modeE n j)
    rw [← hC] at hC1 hC2
    have hμ₁ : modeμ n j = 2 - 2 * C := rfl
    have hμ₂ : modeμ n (n + j) = 2 + 2 * C := by
      unfold modeμ
      rw [hE, cos_add, cos_pi, sin_pi]
      rw [← hC]
      ring
    have hc₂ : cos (modeE n (n + j)) = -C := by
      rw [hE, cos_add, cos_pi, sin_pi, ← hC]
      ring
    unfold modeW
    simp only [mul_zero, zero_mul, neg_zero, exp_zero]
    rw [hc₂, hμ₁, hμ₂]
    have hd₁ : 0 < κ + (2 - 2 * C) := by linarith only [hκ, hC1]
    have hd₂ : 0 < κ + (2 + 2 * C) := by linarith only [hκ, hC2]
    have e : (2 - 2 * C) * C * (1 / (κ + (2 - 2 * C))) + (2 + 2 * C) * -C * (1 / (κ + (2 + 2 * C))) =
        -(4 * κ * C ^ 2) / ((κ + (2 - 2 * C)) * (κ + (2 + 2 * C))) := by
      have h₁ := hd₁.ne'
      have h₂ := hd₂.ne'
      rw [eq_div_iff (mul_ne_zero h₁ h₂)]
      calc _ = (2 - 2 * C) * C * ((κ + (2 + 2 * C)) * ((κ + (2 - 2 * C)) * (1 / (κ + (2 - 2 * C))))) +
            (2 + 2 * C) * -C * ((κ + (2 - 2 * C)) * ((κ + (2 + 2 * C)) * (1 / (κ + (2 + 2 * C))))) := by ring
        _ = _ := by
          rw [mul_one_div_cancel h₁, mul_one_div_cancel h₂]
          ring
    rw [e]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith only [hκ, sq_nonneg C]) (by positivity)
  have hp : (0 : ℝ) ≤ 1 / (2 * n : ℝ) := by positivity
  have := mul_nonpos_of_nonneg_of_nonpos hp hpair
  linarith only [hsd, this]

/-- A general two-point minor of the chain, as a mode sum. -/
theorem chain_minor_sum (t : ℝ) (a b : ℕ) :
    chain n κ t (2 * a) + chain n κ t (2 * b) - 2 * chain n κ t (a + b) =
      -((1 / (2 * n : ℝ)) * ∑ j ∈ Finset.range (2 * n),
        2 * cos (modeE n j * ((a + b : ℕ) : ℝ)) * (1 - cos (modeE n j * ((b : ℝ) - a))) * modeW n κ t j) := by
  unfold chain
  rw [← mul_add, mul_left_comm, ← mul_sub, ← mul_neg]
  have h2 : (2 : ℝ) * ∑ j ∈ Finset.range (2 * n), cos (modeE n j * ((a + b : ℕ) : ℝ)) * modeW n κ t j =
      ∑ j ∈ Finset.range (2 * n), 2 * (cos (modeE n j * ((a + b : ℕ) : ℝ)) * modeW n κ t j) := Finset.mul_sum _ _ _
  rw [h2, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have e₁ : modeE n j * ((2 * a : ℕ) : ℝ) = modeE n j * ((a + b : ℕ) : ℝ) - modeE n j * ((b : ℝ) - a) := by
    push_cast
    ring
  have e₂ : modeE n j * ((2 * b : ℕ) : ℝ) = modeE n j * ((a + b : ℕ) : ℝ) + modeE n j * ((b : ℝ) - a) := by
    push_cast
    ring
  rw [e₁, e₂, cos_sub, cos_add]
  ring

/-- The stiffness cut below which `cos (m E)` cannot be negative. -/
def cutμ (m : ℕ) : ℝ := 2 - 2 * cos (π / (2 * m))

/-- If `cos (m E_j) < 0` then mode `j` is at least as stiff as the cut. -/
theorem cutμ_le_of_cos_neg (hn : 0 < n) (m j : ℕ) (hm : 0 < m) (hj : j < 2 * n)
    (hneg : cos (modeE n j * (m : ℝ)) < 0) : cutμ m ≤ modeμ n j := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hth0 : 0 < π / (2 * (m : ℝ)) := by positivity
  have hth : π / (2 * (m : ℝ)) ≤ π / 2 := div_le_div_of_nonneg_left pi_pos.le (by norm_num) (by linarith only [hmR])
  have hE0 : 0 ≤ modeE n j := by unfold modeE; positivity
  have hE2 : modeE n j < 2 * π := by
    unfold modeE
    have hj' : (j : ℝ) < 2 * n := by exact_mod_cast hj
    rw [div_lt_iff₀ hnR]
    nlinarith only [hj', pi_pos]
  by_contra hc
  push_neg at hc
  have hcos : cos (π / (2 * (m : ℝ))) < cos (modeE n j) := by
    unfold cutμ modeμ at hc
    linarith only [hc]
  have key : ∀ E : ℝ, 0 ≤ E → E ≤ π → cos (π / (2 * (m : ℝ))) < cos E → 0 ≤ cos (E * (m : ℝ)) := by
    intro E hE0 hEπ hE
    have hle : E ≤ π / (2 * (m : ℝ)) := by
      by_contra hgt
      push_neg at hgt
      exact absurd hE (not_lt.mpr (cos_le_cos_of_nonneg_of_le_pi hth0.le hEπ hgt.le))
    refine cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
    · have : 0 ≤ E * (m : ℝ) := by positivity
      linarith only [this, pi_pos]
    · have : E * (m : ℝ) ≤ π / (2 * (m : ℝ)) * m := mul_le_mul_of_nonneg_right hle (by positivity)
      have e : π / (2 * (m : ℝ)) * m = π / 2 := by field_simp
      linarith only [this, e]
  by_cases hE : modeE n j ≤ π
  · exact absurd hneg (not_lt.mpr (key _ hE0 hE hcos))
  · push_neg at hE
    have h₁ : cos (2 * π - modeE n j) = cos (modeE n j) := cos_two_pi_sub _
    have h₂ := key (2 * π - modeE n j) (by linarith only [hE2]) (by linarith only [hE]) (by rw [h₁]; exact hcos)
    have e : cos ((2 * π - modeE n j) * (m : ℝ)) = cos (modeE n j * (m : ℝ)) := by
      have e' : (2 * π - modeE n j) * (m : ℝ) = (m : ℝ) * (2 * π) - modeE n j * (m : ℝ) := by ring
      rw [e', cos_nat_mul_two_pi_sub]
    rw [e] at h₂
    exact absurd hneg (not_lt.mpr h₂)

theorem modeμ_one_lt_cut (hn : 0 < n) {m : ℕ} (hm : 0 < m) (hmn : 4 * m ≤ n) : modeμ n 1 < cutμ m := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmnR : 4 * (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hE1 : modeE n 1 = π / n := by
    unfold modeE
    simp
  unfold modeμ cutμ
  have : cos (π / (2 * (m : ℝ))) < cos (modeE n 1) := by
    rw [hE1]
    refine cos_lt_cos_of_nonneg_of_le_pi (by positivity) ?_ ?_
    · exact div_le_self pi_pos.le (by nlinarith only [hm, hmR, (by exact_mod_cast hm : (1 : ℝ) ≤ m)])
    · exact div_lt_div_of_pos_left pi_pos (by positivity) (by linarith only [hmnR, hmR])
  linarith only [this]

/-- **The flowed chain fails a two-point minor of reflection positivity at any pair of times with `a + b ≤ n/4`,** past
an explicit flow time. The threshold compares the lowest mode with the modes stiff enough to make `cos ((a+b) E)`
negative, so it grows as `a + b` grows. -/
theorem chain_minor_negative {a b : ℕ} (hab : a < b) (hmn : 4 * (a + b) ≤ n) (hκ : 0 < κ) {t : ℝ} (ht : 0 ≤ t)
    (hlarge : 16 * (n : ℝ) * (κ + 1) / (κ * modeμ n 1) < exp (2 * t * (cutμ (a + b) - modeμ n 1))) :
    chain n κ t (2 * a) + chain n κ t (2 * b) < 2 * chain n κ t (a + b) := by
  have hm : 0 < a + b := by omega
  have hn0 : 0 < n := by omega
  have hnR : (4 : ℝ) ≤ n := by
    have : 4 ≤ n := by omega
    exact_mod_cast this
  have hnpos : (0 : ℝ) < n := by linarith only [hnR]
  set m := a + b with hmdef
  have hmnR : 4 * (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hE1 : modeE n 1 = π / n := by
    unfold modeE
    simp
  have hE1pos : 0 < modeE n 1 := by
    rw [hE1]
    exact div_pos pi_pos hnpos
  have hmE : modeE n 1 * (m : ℝ) ≤ π / 4 := by
    rw [hE1, div_mul_eq_mul_div, div_le_iff₀ hnpos]
    nlinarith only [hmnR, pi_pos]
  have hs2 : (1 : ℝ) ≤ sqrt 2 := by
    rw [show (1 : ℝ) = sqrt 1 by simp]
    exact sqrt_le_sqrt (by norm_num)
  have hc4 : ∀ x : ℝ, 0 ≤ x → x ≤ π / 4 → 1 / 2 ≤ cos x := by
    intro x h0 h1
    have h : sqrt 2 / 2 ≤ cos x := by
      rw [← cos_pi_div_four]
      exact cos_le_cos_of_nonneg_of_le_pi h0 (by linarith only [pi_pos]) h1
    linarith only [h, hs2]
  have hdR : (1 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
    linarith only [this]
  have hdm : (b : ℝ) - a ≤ m := by
    rw [hmdef]
    push_cast
    have : (0 : ℝ) ≤ a := by positivity
    linarith only [this]
  have hmR1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hE1le : modeE n 1 ≤ π / 4 := by
    have := mul_le_mul_of_nonneg_left hmR1 hE1pos.le
    linarith only [this, hmE]
  have hμ1pos : 0 < modeμ n 1 := by
    unfold modeμ
    have : cos (modeE n 1) < cos 0 :=
      cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith only [hE1le, pi_pos]) hE1pos
    rw [cos_zero] at this
    linarith only [this]
  have hμ1le : modeμ n 1 ≤ 1 := by
    unfold modeμ
    linarith only [hc4 _ hE1pos.le hE1le]
  have hcut := modeμ_one_lt_cut n hn0 hm hmn
  set b' := 4 * exp (-(2 * t * cutμ m)) / κ with hb'
  have hb'pos : 0 < b' := by positivity
  have hwpos (j : ℕ) : 0 ≤ modeW n κ t j := by
    unfold modeW
    have := modeμ_nonneg n j
    positivity
  have hterm (j : ℕ) (hj : j ∈ Finset.range (2 * n)) :
      -b' ≤ 2 * cos (modeE n j * ((a + b : ℕ) : ℝ)) * (1 - cos (modeE n j * ((b : ℝ) - a))) * modeW n κ t j := by
    have hj' := Finset.mem_range.mp hj
    rw [← hmdef]
    set C := cos (modeE n j * (m : ℝ))
    set D := cos (modeE n j * ((b : ℝ) - a))
    have hD1 : D ≤ 1 := cos_le_one _
    have hD2 : -1 ≤ D := neg_one_le_cos _
    by_cases hC : 0 ≤ C
    · have := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC) (sub_nonneg.mpr hD1)) (hwpos j)
      linarith only [this, hb'pos]
    · push_neg at hC
      have hstiff := cutμ_le_of_cos_neg n hn0 m j hm hj' hC
      have hC2 : -1 ≤ C := neg_one_le_cos _
      have hw₁ : modeW n κ t j ≤ exp (-(2 * t * cutμ m)) / κ := by
        unfold modeW
        have hexp : exp (-(2 * t * modeμ n j)) ≤ exp (-(2 * t * cutμ m)) := by
          apply exp_le_exp.mpr
          have := mul_le_mul_of_nonneg_left hstiff (by positivity : 0 ≤ 2 * t)
          linarith only [this]
        exact div_le_div₀ (exp_pos _).le hexp hκ (by linarith only [hκ, modeμ_nonneg n j])
      have hprod : -4 ≤ 2 * C * (1 - D) := by nlinarith only [hC, hC2, hD1, hD2]
      have h4 : -4 * modeW n κ t j ≤ 2 * C * (1 - D) * modeW n κ t j :=
        mul_le_mul_of_nonneg_right hprod (hwpos j)
      have e : b' = 4 * (exp (-(2 * t * cutμ m)) / κ) := by rw [hb']; ring
      rw [e]
      linarith only [h4, hw₁]
  have hfirst : modeμ n 1 / 2 * (exp (-(2 * t * modeμ n 1)) / (κ + 1)) ≤
      2 * cos (modeE n 1 * ((a + b : ℕ) : ℝ)) * (1 - cos (modeE n 1 * ((b : ℝ) - a))) * modeW n κ t 1 := by
    rw [← hmdef]
    have hC := hc4 _ (by positivity) hmE
    have hdE : modeE n 1 ≤ modeE n 1 * ((b : ℝ) - a) := le_mul_of_one_le_right hE1pos.le hdR
    have hdEle : modeE n 1 * ((b : ℝ) - a) ≤ π / 4 :=
      (mul_le_mul_of_nonneg_left hdm hE1pos.le).trans hmE
    have hD : cos (modeE n 1 * ((b : ℝ) - a)) ≤ cos (modeE n 1) :=
      cos_le_cos_of_nonneg_of_le_pi hE1pos.le (by linarith only [hdEle, pi_pos]) hdE
    have hμeq : modeμ n 1 / 2 = 1 - cos (modeE n 1) := by
      unfold modeμ
      ring
    have hfac : modeμ n 1 / 2 ≤ 2 * cos (modeE n 1 * (m : ℝ)) * (1 - cos (modeE n 1 * ((b : ℝ) - a))) := by
      rw [hμeq]
      have h1 : 0 ≤ 1 - cos (modeE n 1) := by
        rw [← hμeq]
        positivity
      nlinarith only [hC, hD, h1]
    have hw : exp (-(2 * t * modeμ n 1)) / (κ + 1) ≤ modeW n κ t 1 := by
      unfold modeW
      exact div_le_div₀ (exp_pos _).le le_rfl (by positivity) (by linarith only [hμ1le])
    exact (mul_le_mul_of_nonneg_left hw (by positivity)).trans
      (mul_le_mul_of_nonneg_right hfac (hwpos 1))
  have h1mem : 1 ∈ Finset.range (2 * n) := Finset.mem_range.mpr (by omega)
  have hsum : modeμ n 1 / 2 * (exp (-(2 * t * modeμ n 1)) / (κ + 1)) - 2 * (n : ℝ) * b' ≤
      ∑ j ∈ Finset.range (2 * n),
        2 * cos (modeE n j * ((a + b : ℕ) : ℝ)) * (1 - cos (modeE n j * ((b : ℝ) - a))) * modeW n κ t j := by
    rw [← Finset.add_sum_erase _ _ h1mem]
    have hrest : -(2 * (n : ℝ) * b') ≤ ∑ j ∈ (Finset.range (2 * n)).erase 1,
        2 * cos (modeE n j * ((a + b : ℕ) : ℝ)) * (1 - cos (modeE n j * ((b : ℝ) - a))) * modeW n κ t j := by
      have hc : (((Finset.range (2 * n)).erase 1).card : ℝ) ≤ 2 * n := by
        have := Finset.card_erase_le (s := Finset.range (2 * n)) (a := 1)
        rw [Finset.card_range] at this
        exact_mod_cast this
      have hle := Finset.card_nsmul_le_sum ((Finset.range (2 * n)).erase 1)
        (fun j => 2 * cos (modeE n j * ((a + b : ℕ) : ℝ)) * (1 - cos (modeE n j * ((b : ℝ) - a))) * modeW n κ t j)
        (-b') (fun j hj => hterm j (Finset.mem_of_mem_erase hj))
      rw [nsmul_eq_mul] at hle
      nlinarith only [hle, hc, hb'pos]
    linarith only [hrest, hfirst]
  have hpos : 0 < modeμ n 1 / 2 * (exp (-(2 * t * modeμ n 1)) / (κ + 1)) - 2 * (n : ℝ) * b' := by
    have e : modeμ n 1 / 2 * (exp (-(2 * t * modeμ n 1)) / (κ + 1)) - 2 * (n : ℝ) * b' =
        exp (-(2 * t * cutμ m)) * (modeμ n 1 / (2 * (κ + 1)) * exp (2 * t * (cutμ m - modeμ n 1)) - 8 * n / κ) := by
      have hsplit : exp (-(2 * t * modeμ n 1)) = exp (-(2 * t * cutμ m)) * exp (2 * t * (cutμ m - modeμ n 1)) := by
        rw [← exp_add]
        congr 1
        ring
      rw [hsplit, hb']
      field_simp
      ring
    rw [e]
    refine mul_pos (exp_pos _) (sub_pos.mpr ?_)
    have hden : 0 < κ * modeμ n 1 := by positivity
    rw [div_lt_iff₀ hden] at hlarge
    rw [div_lt_iff₀ hκ]
    have e₂ : modeμ n 1 / (2 * (κ + 1)) * exp (2 * t * (cutμ m - modeμ n 1)) * κ =
        (exp (2 * t * (cutμ m - modeμ n 1)) * (κ * modeμ n 1)) / (2 * (κ + 1)) := by ring
    rw [e₂, lt_div_iff₀ (by positivity)]
    nlinarith only [hlarge]
  have hsd := chain_minor_sum n κ t a b
  have hp : (0 : ℝ) < 1 / (2 * n : ℝ) := by positivity
  have := mul_pos hp (lt_of_lt_of_le hpos hsum)
  linarith only [hsd, this]

/-- Reflection positivity of the chain at the sites strictly away from the reflection plane at time `0`, up to the
opposite plane. -/
def ChainRP (t : ℝ) : Prop :=
  ∀ (s : Finset ℕ) (f : ℕ → ℝ), (∀ i ∈ s, 1 ≤ i ∧ i ≤ n) → 0 ≤ ∑ i ∈ s, ∑ j ∈ s, f i * f j * chain n κ t (i + j)

/-- The negative direction is explicit: the difference of the observables at times `a` and `b`, both positive. -/
theorem chain_not_RP {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hmn : 4 * (a + b) ≤ n) (hκ : 0 < κ) {t : ℝ} (ht : 0 ≤ t)
    (hlarge : 16 * (n : ℝ) * (κ + 1) / (κ * modeμ n 1) < exp (2 * t * (cutμ (a + b) - modeμ n 1))) :
    ¬ ChainRP n κ t := by
  intro h
  have hne : a ≠ b := hab.ne
  have hg := h {a, b} (fun i => if i = a then 1 else -1) (by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · omega
    · rw [Finset.mem_singleton.mp hi]
      omega)
  rw [Finset.sum_pair hne, Finset.sum_pair hne, Finset.sum_pair hne] at hg
  simp only [if_true, if_neg hne.symm] at hg
  have := chain_minor_negative n κ hab hmn hκ ht hlarge
  have e₁ : a + a = 2 * a := by ring
  have e₂ : b + b = 2 * b := by ring
  have e₃ : b + a = a + b := by ring
  rw [e₁, e₂, e₃] at hg
  linarith only [hg, this]

/-- The summand of the minor at times `a, b`. -/
def minorT (t : ℝ) (a b j : ℕ) : ℝ :=
  2 * cos (modeE n j * ((a + b : ℕ) : ℝ)) * (1 - cos (modeE n j * ((b : ℝ) - a))) * modeW n κ t j

theorem modeE_reflect (hn : 0 < n) (j : ℕ) (hj : j ≤ 2 * n) : modeE n (2 * n - j) = 2 * π - modeE n j := by
  have hnR : (n : ℝ) ≠ 0 := by positivity
  unfold modeE
  rw [Nat.cast_sub hj]
  push_cast
  field_simp

theorem minorT_reflect (hn : 0 < n) (t : ℝ) {a b j : ℕ} (hab : a < b) (hj : j ≤ 2 * n) :
    minorT n κ t a b (2 * n - j) = minorT n κ t a b j := by
  have hE := modeE_reflect n hn j hj
  have hμ : modeμ n (2 * n - j) = modeμ n j := by
    unfold modeμ
    rw [hE, cos_two_pi_sub]
  have hd : (b : ℝ) - a = ((b - a : ℕ) : ℝ) := by
    rw [Nat.cast_sub hab.le]
  have hc (m : ℕ) : cos (modeE n (2 * n - j) * (m : ℝ)) = cos (modeE n j * (m : ℝ)) := by
    rw [hE]
    have e : (2 * π - modeE n j) * (m : ℝ) = (m : ℝ) * (2 * π) - modeE n j * (m : ℝ) := by ring
    rw [e, cos_nat_mul_two_pi_sub]
  unfold minorT modeW
  rw [hμ, hc, hd, hc]

/-- Summing over the circle is summing twice over the half circle, the ends once each. -/
theorem minor_fold (hn : 0 < n) (t : ℝ) {a b : ℕ} (hab : a < b) :
    ∑ j ∈ Finset.range (2 * n), minorT n κ t a b j =
      ∑ j ∈ Finset.range n, minorT n κ t a b j + ∑ j ∈ Finset.Ico 1 (n + 1), minorT n κ t a b j := by
  rw [two_mul, Finset.sum_range_add]
  congr 1
  rw [← Finset.sum_range_reflect, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr (by simp) fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  have e : n + (n - 1 - j) = 2 * n - (1 + j) := by omega
  rw [e, minorT_reflect n κ hn t hab (by omega)]

section Physical
variable {n κ}

theorem minorT_nonneg (hκ : 0 < κ) (t : ℝ) (a b j : ℕ) (h : 0 ≤ cos (modeE n j * ((a + b : ℕ) : ℝ))) :
    0 ≤ minorT n κ t a b j := by
  unfold minorT modeW
  have := modeμ_nonneg n j
  have h1 := cos_le_one (modeE n j * ((b : ℝ) - a))
  have : 0 ≤ exp (-(2 * t * modeμ n j)) / (κ + modeμ n j) := by positivity
  exact mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr h1)) this

theorem modeμ_lower (hn : 0 < n) {j : ℕ} (hj : j ≤ n) : 4 * (j : ℝ) ^ 2 / (n : ℝ) ^ 2 ≤ modeμ n j := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hjR : (j : ℝ) ≤ n := by exact_mod_cast hj
  have hE0 : 0 ≤ modeE n j := by unfold modeE; positivity
  have hEπ : modeE n j ≤ π := by
    unfold modeE
    rw [div_le_iff₀ hnR]
    nlinarith only [hjR, pi_pos]
  have h := cos_le_one_sub_mul_cos_sq (x := modeE n j) (by rw [abs_of_nonneg hE0]; exact hEπ)
  have e : 2 / π ^ 2 * modeE n j ^ 2 = 2 * (j : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
    unfold modeE
    have hpi := pi_ne_zero
    field_simp
  rw [e] at h
  unfold modeμ
  have e₂ : 4 * (j : ℝ) ^ 2 / (n : ℝ) ^ 2 = 2 * (2 * (j : ℝ) ^ 2 / (n : ℝ) ^ 2) := by ring
  rw [e₂]
  linarith only [h]

/-- The weight that controls the high modes at flow time `c (2n)²`. -/
def tailF (c : ℝ) (j : ℕ) : ℝ := (j : ℝ) ^ 2 * exp (-(32 * c) * j)

theorem tailF_nonneg (c : ℝ) (j : ℕ) : 0 ≤ tailF c j := by
  unfold tailF
  positivity

theorem tailF_summable {c : ℝ} (hc : 0 < c) : Summable (tailF c) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul 2 (r := 32 * c) (by positivity)
  refine h.congr fun j => ?_
  unfold tailF
  congr 2

/-- A negative high mode at flow time `c (2n)²` is bounded by the tail weight, independently of `n`. -/
theorem minorT_lower {c : ℝ} (hc : 0 < c) (hn : 0 < n) (hκ : 0 < κ) {a b j : ℕ} (hab : a < b) (hj : j ≤ n) (hj1 : 1 ≤ j) :
    -((((a + b : ℕ) : ℝ) / n) ^ 2 * π ^ 2 / (κ + modeμ n 1) * tailF c j) ≤
      minorT n κ (c * (2 * (n : ℝ)) ^ 2) a b j := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hE1 : modeE n 1 = π / n := by
    unfold modeE
    simp
  have hmono : modeμ n 1 ≤ modeμ n j := by
    unfold modeμ
    have hle : cos (modeE n j) ≤ cos (modeE n 1) := by
      refine cos_le_cos_of_nonneg_of_le_pi (by unfold modeE; positivity) ?_ ?_
      · unfold modeE
        have hjn : (j : ℝ) ≤ n := by exact_mod_cast hj
        rw [div_le_iff₀ hnR]
        nlinarith only [hjn, pi_pos]
      · unfold modeE
        simp only [Nat.cast_one, mul_one]
        have := mul_le_mul_of_nonneg_left hjR pi_pos.le
        exact div_le_div_of_nonneg_right (by linarith only [this]) hnR.le
    linarith only [hle]
  have hμlow := modeμ_lower hn hj
  have hw : modeW n κ (c * (2 * (n : ℝ)) ^ 2) j ≤ exp (-(32 * c) * j) / (κ + modeμ n 1) := by
    unfold modeW
    refine div_le_div₀ (exp_pos _).le (exp_le_exp.mpr ?_) (by have := modeμ_nonneg n 1; positivity)
      (by linarith only [hmono])
    have h₁ : 2 * (c * (2 * (n : ℝ)) ^ 2) * (4 * (j : ℝ) ^ 2 / (n : ℝ) ^ 2) ≤
        2 * (c * (2 * (n : ℝ)) ^ 2) * modeμ n j := mul_le_mul_of_nonneg_left hμlow (by positivity)
    have e : 2 * (c * (2 * (n : ℝ)) ^ 2) * (4 * (j : ℝ) ^ 2 / (n : ℝ) ^ 2) = 32 * c * (j : ℝ) ^ 2 := by
      field_simp
      ring
    rw [e] at h₁
    have h₂ : 32 * c * (j : ℝ) ≤ 32 * c * (j : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith only [hjR]) (by positivity)
    linarith only [h₁, h₂]
  have hw0 : 0 ≤ modeW n κ (c * (2 * (n : ℝ)) ^ 2) j := by
    unfold modeW
    have := modeμ_nonneg n j
    positivity
  set m : ℝ := ((a + b : ℕ) : ℝ) with hm
  have hdm : |(b : ℝ) - a| ≤ m := by
    have h0 : (0 : ℝ) ≤ a := by positivity
    have h1 : (a : ℝ) < b := by exact_mod_cast hab
    rw [abs_of_pos (by linarith only [h1]), hm]
    push_cast
    linarith only [h0]
  have hsec : 1 - cos (modeE n j * ((b : ℝ) - a)) ≤ m ^ 2 * (π * j / n) ^ 2 / 2 := by
    have h := one_sub_sq_div_two_le_cos (x := modeE n j * ((b : ℝ) - a))
    have hEj : 0 ≤ modeE n j := by unfold modeE; positivity
    have h₂ : (modeE n j * ((b : ℝ) - a)) ^ 2 ≤ (modeE n j * m) ^ 2 := by
      rw [mul_pow, mul_pow]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hdm 2
    unfold modeE at h₂ h ⊢
    have e : (π * (j : ℝ) / n * m) ^ 2 = m ^ 2 * (π * j / n) ^ 2 := by ring
    rw [e] at h₂
    linarith only [h, h₂]
  have hsec0 : 0 ≤ 1 - cos (modeE n j * ((b : ℝ) - a)) := sub_nonneg.mpr (cos_le_one _)
  have hC : -1 ≤ cos (modeE n j * m) := neg_one_le_cos _
  have hfac : -(m ^ 2 * (π * j / n) ^ 2) ≤ 2 * cos (modeE n j * m) * (1 - cos (modeE n j * ((b : ℝ) - a))) := by
    nlinarith only [hC, hsec, hsec0]
  have hfac0 : 0 ≤ m ^ 2 * (π * j / n) ^ 2 := by positivity
  unfold minorT
  rw [← hm]
  have hstep : -(m ^ 2 * (π * j / n) ^ 2) * modeW n κ (c * (2 * (n : ℝ)) ^ 2) j ≤
      2 * cos (modeE n j * m) * (1 - cos (modeE n j * ((b : ℝ) - a))) * modeW n κ (c * (2 * (n : ℝ)) ^ 2) j :=
    mul_le_mul_of_nonneg_right hfac hw0
  have hstep₂ : m ^ 2 * (π * j / n) ^ 2 * modeW n κ (c * (2 * (n : ℝ)) ^ 2) j ≤
      m ^ 2 * (π * j / n) ^ 2 * (exp (-(32 * c) * j) / (κ + modeμ n 1)) :=
    mul_le_mul_of_nonneg_left hw hfac0
  have e : m ^ 2 * (π * j / n) ^ 2 * (exp (-(32 * c) * j) / (κ + modeμ n 1)) =
      (m / n) ^ 2 * π ^ 2 / (κ + modeμ n 1) * tailF c j := by
    unfold tailF
    field_simp
  rw [e] at hstep₂
  linarith only [hstep, hstep₂]

/-- **The chain fails a minor at fixed physical positive times, at fixed physical flow time.** For every `c > 0` there is
`ρ > 0` such that at flow time `t = c (2n)²`, for every `n` and every `κ > 0`, the two-point minor at lattice times
`a < b` fails whenever `a + b ≤ ρ n` and `b ≥ 2a`. In physical units on the circle of length one, the times are
`q = a/2n` and `q' = b/2n`, so this is every pair with `q' ≥ 2q ≥ 0` and `q + q' ≤ ρ/2`. Neither `n` nor `κ` needs to be
large. -/
theorem chain_physical_times {c : ℝ} (hc : 0 < c) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (n : ℕ) (κ : ℝ) (a b : ℕ), 0 < κ → a < b → ((a + b : ℕ) : ℝ) ≤ ρ * n → 2 * a ≤ b →
      chain n κ (c * (2 * (n : ℝ)) ^ 2) (2 * a) + chain n κ (c * (2 * (n : ℝ)) ^ 2) (2 * b) <
        2 * chain n κ (c * (2 * (n : ℝ)) ^ 2) (a + b) := by
  set ε : ℝ := exp (-(80 * c)) / (10 * π ^ 2) with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp (tailF_summable hc) ε hεpos
  set J : ℕ := s.sup id + 2 with hJ
  have hJ2 : 2 ≤ J := by omega
  have hdisj {u : Finset ℕ} (hu : ∀ i ∈ u, J ≤ i) : ∑ i ∈ u, tailF c i < ε := by
    have hd : Disjoint u s := by
      rw [Finset.disjoint_left]
      intro i hi his
      have h₁ := hu i hi
      have h₂ : i ≤ s.sup id := Finset.le_sup (f := id) his
      omega
    have h := hs u hd
    rwa [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => tailF_nonneg c i)] at h
  refine ⟨1 / (2 * (J : ℝ)), by positivity, fun n κ a b hκ hab hρ h2 => ?_⟩
  have hm1 : 1 ≤ a + b := by omega
  have hm1R : (1 : ℝ) ≤ ((a + b : ℕ) : ℝ) := by exact_mod_cast hm1
  set m : ℝ := ((a + b : ℕ) : ℝ) with hm
  have hJR : (2 : ℝ) ≤ J := by exact_mod_cast hJ2
  have hnJ : 2 * (J : ℝ) * m ≤ n := by
    have hJp : (0 : ℝ) < 2 * (J : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hρ hJp.le
    have e : 2 * (J : ℝ) * (1 / (2 * (J : ℝ)) * n) = n := by
      field_simp
    linarith only [this, e]
  have hnR : (0 : ℝ) < n := by nlinarith only [hnJ, hJR, hm1R]
  have hn : 0 < n := by exact_mod_cast hnR
  have hn4 : 4 * m ≤ n := by nlinarith only [hnJ, hJR, hm1R]
  have hnge : (1 : ℝ) ≤ n := by linarith only [hn4, hm1R]
  have hE1 : modeE n 1 = π / n := by
    unfold modeE
    simp
  have hE1pos : 0 < modeE n 1 := by
    rw [hE1]
    exact div_pos pi_pos hnR
  have hμ1 : 0 ≤ modeμ n 1 := modeμ_nonneg n 1
  set A : ℝ := (m / n) ^ 2 * π ^ 2 / (κ + modeμ n 1) with hA
  have hApos : 0 < A := by positivity
  -- the bad modes
  have hbad {u : Finset ℕ} (hu : ∀ i ∈ u, i ≤ n) :
      -(A * ε) ≤ ∑ i ∈ u, minorT n κ (c * (2 * (n : ℝ)) ^ 2) a b i := by
    classical
    set bad := u.filter fun i => cos (modeE n i * m) < 0 with hbaddef
    have hnegJ (i : ℕ) (hi : i ∈ bad) : J ≤ i ∧ 1 ≤ i := by
      have hiu := (Finset.mem_filter.mp hi).1
      have hneg := (Finset.mem_filter.mp hi).2
      by_contra hcon
      have hlt : i < J := by
        by_contra h'
        push_neg at h'
        refine hcon ⟨h', by omega⟩
      have hiR : (i : ℝ) ≤ J := by exact_mod_cast hlt.le
      have h₀ : 0 ≤ cos (modeE n i * m) := by
        refine cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
        · have : 0 ≤ modeE n i * m := by unfold modeE; positivity
          linarith only [this, pi_pos]
        · unfold modeE
          rw [div_mul_eq_mul_div, div_le_iff₀ hnR]
          have h₁ : (i : ℝ) * m ≤ J * m := mul_le_mul_of_nonneg_right hiR (by positivity)
          nlinarith only [h₁, hnJ, pi_pos]
      linarith only [h₀, hneg]
    have h₁ : ∑ i ∈ bad, minorT n κ (c * (2 * (n : ℝ)) ^ 2) a b i ≤
        ∑ i ∈ u, minorT n κ (c * (2 * (n : ℝ)) ^ 2) a b i := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i hi hni => ?_
      refine minorT_nonneg hκ _ a b i ?_
      by_contra hcon
      exact hni (Finset.mem_filter.mpr ⟨hi, not_le.mp hcon⟩)
    have h₂ : ∑ i ∈ bad, -(A * tailF c i) ≤ ∑ i ∈ bad, minorT n κ (c * (2 * (n : ℝ)) ^ 2) a b i :=
      Finset.sum_le_sum fun i hi =>
        minorT_lower hc hn hκ hab (hu i (Finset.mem_filter.mp hi).1) (hnegJ i hi).2
    have h₃ : ∑ i ∈ bad, tailF c i < ε := hdisj fun i hi => (hnegJ i hi).1
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum] at h₂
    have h₄ : A * ∑ i ∈ bad, tailF c i ≤ A * ε := mul_le_mul_of_nonneg_left h₃.le hApos.le
    linarith only [h₁, h₂, h₄]
  -- the first mode
  have hfirst : (2 / 9) * (m / n) ^ 2 * (exp (-(80 * c)) / (κ + modeμ n 1)) ≤
      minorT n κ (c * (2 * (n : ℝ)) ^ 2) a b 1 := by
    have hs2 : (1 : ℝ) ≤ sqrt 2 := by
      rw [show (1 : ℝ) = sqrt 1 by simp]
      exact sqrt_le_sqrt (by norm_num)
    have hmE : modeE n 1 * m ≤ π / 4 := by
      rw [hE1, div_mul_eq_mul_div, div_le_iff₀ hnR]
      nlinarith only [hn4, pi_pos]
    have hC : 1 / 2 ≤ cos (modeE n 1 * m) := by
      have h : sqrt 2 / 2 ≤ cos (modeE n 1 * m) := by
        rw [← cos_pi_div_four]
        exact cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith only [pi_pos]) hmE
      linarith only [h, hs2]
    have hab3 : m ≤ 3 * ((b : ℝ) - a) := by
      have h2R : 2 * (a : ℝ) ≤ b := by exact_mod_cast h2
      rw [hm]
      push_cast
      linarith only [h2R]
    have hdpos : 0 < (b : ℝ) - a := by
      have : (a : ℝ) < b := by exact_mod_cast hab
      linarith only [this]
    have hdle : (b : ℝ) - a ≤ m := by
      rw [hm]
      push_cast
      have : (0 : ℝ) ≤ a := by positivity
      linarith only [this]
    have hsec : (2 / 9) * (m / n) ^ 2 ≤ 1 - cos (modeE n 1 * ((b : ℝ) - a)) := by
      have hx0 : 0 ≤ modeE n 1 * ((b : ℝ) - a) := by positivity
      have hxπ : modeE n 1 * ((b : ℝ) - a) ≤ π :=
        ((mul_le_mul_of_nonneg_left hdle hE1pos.le).trans hmE).trans (by linarith only [pi_pos])
      have h := cos_le_one_sub_mul_cos_sq (x := modeE n 1 * ((b : ℝ) - a)) (by rwa [abs_of_nonneg hx0])
      have e : 2 / π ^ 2 * (modeE n 1 * ((b : ℝ) - a)) ^ 2 = 2 * (((b : ℝ) - a) / n) ^ 2 := by
        rw [hE1]
        have hpi := pi_ne_zero
        field_simp
      rw [e] at h
      have hd2 : (m / n) ^ 2 ≤ 9 * (((b : ℝ) - a) / n) ^ 2 := by
        have e₂ : 9 * (((b : ℝ) - a) / n) ^ 2 = (3 * ((b : ℝ) - a) / n) ^ 2 := by ring
        rw [e₂]
        refine pow_le_pow_left₀ (by positivity) ?_ 2
        exact div_le_div_of_nonneg_right hab3 hnR.le
      nlinarith only [h, hd2]
    have hw : exp (-(80 * c)) / (κ + modeμ n 1) ≤ modeW n κ (c * (2 * (n : ℝ)) ^ 2) 1 := by
      unfold modeW
      refine div_le_div_of_nonneg_right (exp_le_exp.mpr ?_) (by positivity)
      have hμhi : modeμ n 1 ≤ 10 / (n : ℝ) ^ 2 := by
        have h := one_sub_sq_div_two_le_cos (x := modeE n 1)
        have hpi : π ^ 2 < 10 := by nlinarith only [pi_lt_d2, pi_pos]
        unfold modeμ
        have e : modeE n 1 ^ 2 = π ^ 2 / (n : ℝ) ^ 2 := by
          rw [hE1, div_pow]
        have h₃ : π ^ 2 / (n : ℝ) ^ 2 ≤ 10 / (n : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hpi.le (by positivity)
        rw [e] at h
        linarith only [h, h₃]
      have h₁ := mul_le_mul_of_nonneg_left hμhi (by positivity : 0 ≤ 2 * (c * (2 * (n : ℝ)) ^ 2))
      have e : 2 * (c * (2 * (n : ℝ)) ^ 2) * (10 / (n : ℝ) ^ 2) = 80 * c := by
        field_simp
        ring
      rw [e] at h₁
      linarith only [h₁]
    have hfac : (2 / 9) * (m / n) ^ 2 ≤ 2 * cos (modeE n 1 * m) * (1 - cos (modeE n 1 * ((b : ℝ) - a))) := by
      have h0 : 0 ≤ (2 / 9) * (m / n) ^ 2 := by positivity
      nlinarith only [hC, hsec, h0]
    have hfac0 : 0 ≤ (2 / 9) * (m / n) ^ 2 := by positivity
    unfold minorT
    rw [← hm]
    calc (2 / 9) * (m / n) ^ 2 * (exp (-(80 * c)) / (κ + modeμ n 1))
        ≤ (2 / 9) * (m / n) ^ 2 * modeW n κ (c * (2 * (n : ℝ)) ^ 2) 1 := mul_le_mul_of_nonneg_left hw hfac0
      _ ≤ _ := mul_le_mul_of_nonneg_right hfac (by unfold modeW; positivity)
  -- assemble
  have hn1 : 1 < n + 1 := by omega
  have hsum : (2 / 9) * (m / n) ^ 2 * (exp (-(80 * c)) / (κ + modeμ n 1)) - 2 * (A * ε) ≤
      ∑ j ∈ Finset.range (2 * n), minorT n κ (c * (2 * (n : ℝ)) ^ 2) a b j := by
    rw [minor_fold n κ hn _ hab, Finset.sum_eq_sum_Ico_succ_bot hn1]
    have h₁ := hbad (u := Finset.range n) fun i hi => (Finset.mem_range.mp hi).le
    have h₂ := hbad (u := Finset.Ico (1 + 1) (n + 1)) fun i hi => by
      have := (Finset.mem_Ico.mp hi).2
      omega
    linarith only [h₁, h₂, hfirst]
  have hpos : 0 < (2 / 9) * (m / n) ^ 2 * (exp (-(80 * c)) / (κ + modeμ n 1)) - 2 * (A * ε) := by
    have hd : 0 < κ + modeμ n 1 := by positivity
    have e : (2 / 9) * (m / n) ^ 2 * (exp (-(80 * c)) / (κ + modeμ n 1)) - 2 * (A * ε) =
        (m / n) ^ 2 * (exp (-(80 * c)) / (κ + modeμ n 1)) * (2 / 9 - 1 / 5) := by
      rw [hA, hε]
      have hpi := pi_ne_zero
      field_simp
      ring
    rw [e]
    have : (0 : ℝ) < 2 / 9 - 1 / 5 := by norm_num
    positivity
  have hsd := chain_minor_sum n κ (c * (2 * (n : ℝ)) ^ 2) a b
  have hp : (0 : ℝ) < 1 / (2 * n : ℝ) := by positivity
  have := mul_pos hp (lt_of_lt_of_le hpos hsum)
  unfold minorT at this
  rw [← hm] at this
  rw [← hm] at hsd
  linarith only [hsd, this]

end Physical

/-- The chain at physical flow time is not reflection positive at positive sites, for every stiffness, once the lattice
sites `1, 2` lie in the window. The identification of the chain with a gauge mode is not formalized. -/
theorem chain_physical_not_RP {c : ℝ} (hc : 0 < c) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (n : ℕ) (κ : ℝ), 0 < κ → 3 ≤ ρ * n → ¬ ChainRP n κ (c * (2 * (n : ℝ)) ^ 2) := by
  obtain ⟨ρ, hρ, h⟩ := chain_physical_times hc
  have hρ' : 0 < min ρ (1 / 4) := lt_min hρ (by norm_num)
  refine ⟨min ρ (1 / 4), hρ', fun n κ hκ hn hRP => ?_⟩
  have hn₁ : (3 : ℝ) ≤ ρ * n := hn.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  have hn₂ : (3 : ℝ) ≤ 1 / 4 * n := hn.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity))
  have h₀ := h n κ 1 2 hκ (by norm_num) (by norm_num; linarith only [hn₁]) (by norm_num)
  have hn12 : (12 : ℝ) ≤ n := by linarith only [hn₂]
  have hn12' : 12 ≤ n := by exact_mod_cast hn12
  have hg := hRP {1, 2} (fun i => if i = 1 then 1 else -1) (by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · omega
    · rw [Finset.mem_singleton.mp hi]
      omega)
  rw [Finset.sum_pair (by norm_num), Finset.sum_pair (by norm_num), Finset.sum_pair (by norm_num)] at hg
  norm_num at hg h₀
  linarith only [hg, h₀]

end FreeChain

/-! ### What restores exact reflection positivity -/

section Rescue
variable (n : ℕ) [NeZero n] (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- Any observable determined by the links of the closed upper half is half-supported. This includes spatial
smearing or spatial flow within a fixed positive time slice, however long, which keeps a cusp in time. It does not
include four-dimensional flow. -/
theorem upperLocal_of_closed (F : Configuration (Vertex (2 * n)) G → ℂ)
    (h : ∀ U U', (∀ p, ClosedPositive n p → linkAt n G U p = linkAt n G U' p) → F U = F U') :
    UpperLocalC n G F :=
  fun b x y => h _ _ fun p hp => assemble_closed_link n G p hp b x y 1

end Rescue

section SliceFlow
open TwistedFlow
open WilsonSingleLinkStaples (Q character character_re)

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

/-- The static field built from one time slice: temporal links are one, and every spatial link is copied from time
`τ`. On such a field the Wilson flow has no temporal force, so its flow is a three-dimensional flow of that slice;
this hand remark is not used and not formalized. -/
def staticCfg (τ : ZMod (2 * n)) (U : Configuration V' Q) : Configuration V' Q :=
  TwistedLandau.ofLink fun x μ => if μ = 0 then 1 else linkValue (2 * n) Q U (Function.update x 0 τ) μ

theorem staticCfg_continuous (τ : ZMod (2 * n)) : Continuous (staticCfg n τ) := by
  refine continuous_pi fun e => ?_
  unfold staticCfg TwistedLandau.ofLink
  by_cases h : (edgeCoordinates (2 * n) e).2 = 0
  · simp only [h, if_true]
    exact continuous_const
  · simp only [h, if_false]
    exact TwistedSlice.continuous_linkValue n _ _

theorem linkValue_eq_linkAt (U : Configuration V' Q) (x : V') (μ : Fin 4) :
    linkValue (2 * n) Q U x μ = linkAt n Q U (x, μ) := by
  have h := TwistedIBP.linkValue_coords n U ((edgeCoordinates (2 * n)).symm (x, μ))
  simp only [Equiv.apply_symm_apply] at h
  exact h

/-- **Anything computed from one positive time slice is half-supported, however long the flow.** So the Gram form of
such observables is nonnegative exactly at every lattice size, with no approximation. -/
theorem static_upper (τ : ZMod (2 * n)) (hτ : τ.val ≤ n) (G : Configuration V' Q → ℂ) :
    UpperLocalC n Q fun U => G (staticCfg n τ U) := by
  refine upperLocal_of_closed n Q _ fun U U' h => ?_
  congr 1
  funext e
  unfold staticCfg TwistedLandau.ofLink
  by_cases hμ : (edgeCoordinates (2 * n) e).2 = 0
  · simp only [hμ, if_true]
  · simp only [hμ, if_false]
    rw [linkValue_eq_linkAt, linkValue_eq_linkAt]
    refine h _ (closed_spatial n _ _ hμ ?_)
    simpa using hτ

variable (N : ℕ → ℕ) [∀ k, NeZero (N k)] (t : ℕ → ℝ)

/-- Plaquettes after flowing the static field of their own time slice, at flow time `t k`, which may be of order
`N²`. These replace the four-dimensional flowed labels wherever reflection positivity is wanted. -/
def sliceLabels : LabelSystem Q N PhysLabel where
  obs k l U := (su2Labels N).obs k l (wf (N k) (t k) (staticCfg (N k) (site (N k) l.1 0) U))
  cont k l := ((su2Labels N).cont k l).comp ((continuous_wf_right (N k) (t k)).comp (staticCfg_continuous (N k) _))
  bound := (su2Labels N).bound
  bound_nonneg := (su2Labels N).bound_nonneg
  obs_le k l _ := (su2Labels N).obs_le k l _

/-- A physical point in the closed lower end of the upper half of the time circle. Time zero is allowed: a slice
observable at the reflection plane is half-supported, and is the one fixed by the reflection. -/
def ClosedPosLabel (l : PhysLabel) : Prop := 0 ≤ l.1 0 ∧ l.1 0 < 1 / 2

theorem site_val_lt (m : ℕ) [NeZero m] (q : Fin 4 → ℚ) (h0 : 0 ≤ q 0) (h1 : q 0 < 1 / 2) : (site m q 0).val < m := by
  have hmq : (0 : ℚ) < m := by exact_mod_cast NeZero.pos m
  have hfl : 0 ≤ ⌊q 0 * ((2 * m : ℕ) : ℚ)⌋ := Int.floor_nonneg.mpr (by positivity)
  have hlt : ⌊q 0 * ((2 * m : ℕ) : ℚ)⌋ < (m : ℤ) := by
    rw [Int.floor_lt]
    push_cast
    nlinarith only [h1, hmq]
  obtain ⟨r, hr⟩ := Int.eq_ofNat_of_zero_le hfl
  have hval : (site m q 0).val = r := by
    unfold site
    rw [hr, Int.cast_natCast, ZMod.val_natCast_of_lt (by omega)]
  rw [hval]
  omega

theorem sliceLabels_upper (l : PhysLabel) (hl : ClosedPosLabel l) (k : ℕ) :
    UpperLocalC (N k) Q ((sliceLabels N t).obs k l) :=
  static_upper (N k) (site (N k) l.1 0) (site_val_lt (N k) l.1 hl.1 hl.2).le
    fun V => (su2Labels N).obs k l (wf (N k) (t k) V)

/-- **A flowed family with exact reflection positivity in the limit.** For every trajectory and every sequence of
flow times, some subsequence converges and the limit has all of `LimitPackage`, reflection positivity included. This
family is bounded, so compactness is automatic and it says nothing about whether anything survives. On `β → ∞` the
limit is the constant (`sliceFlow_limit_is_constant`). -/
theorem sliceFlow_limit_exists (β : ℕ → ℝ) :
    ∃ (W : List PhysLabel × List PhysLabel → ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ a b, Tendsto (fun k => osEntry (sliceLabels N t) (fun k => spatialTwist (N k)) character β 2 (φ k) a b)
        atTop (𝓝 (W (a, b)))) ∧
      LimitPackage (sliceLabels N t) ClosedPosLabel W :=
  exists_limit _ _ character β 2 (fun k => spatialTwist_invariant (N k))
    WilsonSingleLinkStaples.character_continuous WilsonSingleLinkStaples.character_classFunction
    WilsonSingleLinkStaples.character_inverse_re ClosedPosLabel
    (fun l hl => Eventually.of_forall (sliceLabels_upper N t l hl))

end SliceFlow

/-! ### Slice flow has the mean bound, the collapse, and exact symmetries

Slice observables are half-supported, which is why they are reflection positive. Here is what else is true of them. Their
means obey the same bound as four-dimensional flowed ones, so the plaquette limit collapses on `β → ∞`
(`slice_term_mean`, `slice_os_tendsto`, `sliceFlow_limit_is_constant`). So slice flow repairs reflection positivity and
gains nothing for nontriviality at plaquette level. They are also the one flowed family with exact translation
covariance, time included, in reflected form (`sliceObs_Rκ`, `sliceObs_reflect`, `slice_entry_shift`). -/

section SliceSymmetry
open TwistedFlow TwistedLocalization
open WilsonSingleLinkStaples (Q character character_re)

variable (n : ℕ) [NeZero n]
local notation "V'" => Vertex (2 * n)

theorem static_link (τ : ZMod (2 * n)) (U : Configuration V' Q) (x : V') (μ : Fin 4) :
    linkValue (2 * n) Q (staticCfg n τ U) x μ =
      if μ = 0 then 1 else linkValue (2 * n) Q U (Function.update x 0 τ) μ := rfl

theorem update_step_ne (τ : ZMod (2 * n)) (x : V') (μ : Fin 4) (hμ : μ ≠ 0) :
    Function.update (step (2 * n) x μ) 0 τ = step (2 * n) (Function.update x 0 τ) μ := by
  funext a
  by_cases ha : a = 0
  · subst ha
    simp [step, Function.update, hμ.symm]
  · simp [step, Function.update, ha]

theorem update_step_zero (τ : ZMod (2 * n)) (x : V') :
    Function.update (step (2 * n) x 0) 0 τ = Function.update x 0 τ := by
  funext a
  by_cases ha : a = 0
  · subst ha
    simp
  · simp [step, Function.update, ha]

theorem character_one : (character (1 : Q)).re = 2 := by
  rw [character_re]
  simp

/-- Temporal plaquettes of a static field have no defect. -/
theorem term_static_temporal (τ : ZMod (2 * n)) (U : Configuration V' Q) (x : V') (ν : Fin 4) (h : (0 : Fin 4) < ν) :
    term n Q (spatialTwist n) character 2 (staticCfg n τ U) (x, ⟨(0, ν), h⟩) = 0 := by
  classical
  have hν : ν ≠ 0 := h.ne'
  unfold term plaquetteProduct
  simp only [static_link, if_true, if_neg hν, update_step_zero]
  have hz : spatialTwist n (x, ⟨(0, ν), h⟩) = 1 := by
    unfold spatialTwist
    simp
  rw [hz]
  simp [character_one]

/-- Spatial plaquettes of a static field are those of the slice. -/
theorem term_static_spatial (τ : ZMod (2 * n)) (U : Configuration V' Q) (x : V') (μ ν : Fin 4) (h : μ < ν) (hμ : μ ≠ 0) :
    term n Q (spatialTwist n) character 2 (staticCfg n τ U) (x, ⟨(μ, ν), h⟩) =
      term n Q (spatialTwist n) character 2 U (Function.update x 0 τ, ⟨(μ, ν), h⟩) := by
  classical
  have hν : ν ≠ 0 := by
    intro e
    subst e
    exact absurd h (Fin.not_lt_zero _)
  unfold term plaquetteProduct
  simp only [static_link, if_neg hμ, if_neg hν, update_step_ne _ _ _ _ hμ, update_step_ne _ _ _ _ hν]
  have hz : spatialTwist n (x, ⟨(μ, ν), h⟩) = spatialTwist n (Function.update x 0 τ, ⟨(μ, ν), h⟩) := by
    unfold spatialTwist
    simp
  rw [hz]

theorem term_static_le (τ : ZMod (2 * n)) (U : Configuration V' Q) (x : V') (P : Plane) :
    term n Q (spatialTwist n) character 2 (staticCfg n τ U) (x, P) ≤
      term n Q (spatialTwist n) character 2 U (Function.update x 0 τ, P) := by
  rcases P with ⟨⟨μ, ν⟩, h⟩
  by_cases hμ : μ = 0
  · subst hμ
    rw [term_static_temporal]
    exact TwistedFlat.term_nonneg n U _
  · rw [term_static_spatial n τ U x μ ν h hμ]

theorem link_Rκ (κ : Fin 4) (U : Configuration V' Q) (x : V') (μ : Fin 4) :
    linkValue (2 * n) Q (Rκ n κ U) x μ = sgn n κ (ed n x μ) * linkValue (2 * n) Q U (step (2 * n) x κ) μ := rfl

theorem config_ext {U U' : Configuration V' Q} (h : ∀ x μ, linkValue (2 * n) Q U x μ = linkValue (2 * n) Q U' x μ) :
    U = U' := by
  funext e
  rw [← TwistedIBP.linkValue_coords n U e, ← TwistedIBP.linkValue_coords n U' e]
  exact h _ _

theorem static_Rκ_zero (τ : ZMod (2 * n)) (U : Configuration V' Q) :
    Rκ n 0 (staticCfg n τ U) = staticCfg n τ U := by
  classical
  refine config_ext n fun x μ => ?_
  rw [link_Rκ, static_link, static_link, update_step_zero]
  have : sgn n 0 (ed n x μ) = 1 := by
    have hc : ¬ sgnCond n 0 x μ := by
      unfold sgnCond
      simp
    unfold sgn
    exact if_neg hc
  rw [this, one_mul]

theorem static_Rκ_ne (τ : ZMod (2 * n)) (κ : Fin 4) (hκ : κ ≠ 0) (U : Configuration V' Q) :
    Rκ n κ (staticCfg n τ U) = staticCfg n τ (Rκ n κ U) := by
  classical
  refine config_ext n fun x μ => ?_
  rw [link_Rκ, static_link, static_link, link_Rκ, update_step_ne _ _ _ _ hκ]
  by_cases hμ : μ = 0
  · subst hμ
    have : sgn n κ (ed n x 0) = 1 := by
      have hc : ¬ sgnCond n κ x 0 := by
        unfold sgnCond
        simp
      unfold sgn
      exact if_neg hc
    simp [this]
  · simp only [if_neg hμ]
    congr 1

variable (β : ℝ)

theorem continuous_slice_term (τ : ZMod (2 * n)) (t : ℝ) (p : PlaquetteIndex (2 * n)) :
    Continuous fun U : Configuration V' Q =>
      term n Q (spatialTwist n) character 2 (wf n t (staticCfg n τ U)) p :=
  (continuous_termW n t p).comp (staticCfg_continuous n τ)

theorem slice_step (τ : ZMod (2 * n)) (t : ℝ) (P : Plane) (κ : Fin 4) (y : V') :
    ∫ U, term n Q (spatialTwist n) character 2 (wf n t (staticCfg n τ U)) (step (2 * n) y κ, P) ∂twistedLaw n β =
      ∫ U, term n Q (spatialTwist n) character 2 (wf n t (staticCfg n τ U)) (y, P) ∂twistedLaw n β := by
  by_cases hκ : κ = 0
  · subst hκ
    refine integral_congr_ae (Eventually.of_forall fun U => ?_)
    change term n Q (spatialTwist n) character 2 (wf n t (staticCfg n τ U)) (step (2 * n) y 0, P) =
      term n Q (spatialTwist n) character 2 (wf n t (staticCfg n τ U)) (y, P)
    rw [← term_Rκ, ← wf_Rκ, static_Rκ_zero]
  · rw [← law_Rκ n β κ (continuous_slice_term n τ t (y, P))]
    refine integral_congr_ae (Eventually.of_forall fun U => ?_)
    change term n Q (spatialTwist n) character 2 (wf n t (staticCfg n τ U)) (step (2 * n) y κ, P) =
      term n Q (spatialTwist n) character 2 (wf n t (staticCfg n τ (Rκ n κ U))) (y, P)
    rw [← term_Rκ, ← wf_Rκ, static_Rκ_ne n τ κ hκ]

/-- **Slice-flowed plaquettes obey the same mean bound as 4D-flowed ones**, uniformly in lattice size and flow time. -/
theorem slice_term_mean (τ : ZMod (2 * n)) {t : ℝ} (ht : 0 ≤ t) (hβ : 1 / 32 ≤ β) (p : PlaquetteIndex (2 * n)) :
    ∫ U, term n Q (spatialTwist n) character 2 (wf n t (staticCfg n τ U)) p ∂twistedLaw n β ≤
      4 * Real.log (SU2GaussianMass.cap (24 * β)) / β := by
  set C := 4 * Real.log (SU2GaussianMass.cap (24 * β)) / β with hC
  rcases p with ⟨x₀, P₀⟩
  have hiW (x : V') (P : Plane) := integrable_law n β (continuous_slice_term n τ t (x, P))
  have hconst (x : V') (P : Plane) :
      ∫ U, term n Q (spatialTwist n) character 2 (wf n t (staticCfg n τ U)) (x, P) ∂twistedLaw n β =
        ∫ U, term n Q (spatialTwist n) character 2 (wf n t (staticCfg n τ U)) (x₀, P) ∂twistedLaw n β :=
    const_of_step n (fun y => ∫ U, term n Q (spatialTwist n) character 2 (wf n t (staticCfg n τ U)) (y, P) ∂twistedLaw n β)
      (fun κ y => slice_step n β τ t P κ y) x₀ x
  have hstatic : Continuous fun U : Configuration V' Q => actionOne n (staticCfg n τ U) :=
    (continuous_actionOne n).comp (staticCfg_continuous n τ)
  -- the flowed action of the static field, in terms of one site
  have h1 : ∫ U, actionOne n (wf n t (staticCfg n τ U)) ∂twistedLaw n β =
      (Fintype.card V' : ℕ) * ∑ P : Plane, ∫ U, term n Q (spatialTwist n) character 2 (wf n t (staticCfg n τ U)) (x₀, P) ∂twistedLaw n β := by
    simp only [actionOne_sum]
    rw [integral_finset_sum _ fun x _ => integrable_finset_sum _ fun P _ => hiW x P]
    simp only [integral_finset_sum _ fun P _ => hiW _ P, hconst]
    simp
  have h2 : ∫ U, actionOne n (wf n t (staticCfg n τ U)) ∂twistedLaw n β ≤
      ∫ U, actionOne n (staticCfg n τ U) ∂twistedLaw n β := by
    refine integral_mono (integrable_law n β ((continuous_actionOne n).comp
      ((continuous_wf_right n t).comp (staticCfg_continuous n τ)))) (integrable_law n β hstatic) fun U => ?_
    have := action_wf_antitone n (staticCfg n τ U) ht
    simpa only [wf_zero] using this
  have hiV (x : V') (P : Plane) : Integrable (fun U => term n Q (spatialTwist n) character 2 (staticCfg n τ U) (x, P)) (twistedLaw n β) :=
    integrable_law n β ((continuous_term' n (x, P)).comp (staticCfg_continuous n τ))
  have hiU (x : V') (P : Plane) := integrable_law n β (continuous_term' n (x, P))
  have h3 : ∫ U, actionOne n (staticCfg n τ U) ∂twistedLaw n β ≤ (Fintype.card V' : ℕ) * C := by
    simp only [actionOne_sum]
    rw [integral_finset_sum _ fun x _ => integrable_finset_sum _ fun P _ => hiV x P]
    have : ∀ x : V', ∫ U, ∑ P : Plane, term n Q (spatialTwist n) character 2 (staticCfg n τ U) (x, P) ∂twistedLaw n β ≤ C := by
      intro x
      rw [integral_finset_sum _ fun P _ => hiV x P]
      have hb := law_plaquette_mean_wf n β le_rfl hβ (Function.update x 0 τ)
      simp only [wf_zero] at hb
      refine le_trans (Finset.sum_le_sum fun P _ => ?_) hb
      exact integral_mono (hiV x P) (hiU _ P) fun U => term_static_le n τ U x P
    refine (Finset.sum_le_sum fun x _ => this x).trans_eq ?_
    simp
  have hV := card_vertex_pos n
  have hsum : ∑ P : Plane, ∫ U, term n Q (spatialTwist n) character 2 (wf n t (staticCfg n τ U)) (x₀, P) ∂twistedLaw n β ≤ C := by
    have h4 := h2.trans h3
    rw [h1] at h4
    exact le_of_mul_le_mul_left h4 hV
  refine le_trans ?_ hsum
  exact Finset.single_le_sum (f := fun P : Plane =>
    ∫ U, term n Q (spatialTwist n) character 2 (wf n t (staticCfg n τ U)) (x₀, P) ∂twistedLaw n β)
    (fun P _ => integral_nonneg fun U => TwistedFlat.term_nonneg n _ _) (Finset.mem_univ P₀)

/-! ### Exact symmetries of the slice observable -/

/-- A slice observable, at a lattice site, read as a real number. -/
def sliceObs (t : ℝ) (x : V') (P : Plane) (U : Configuration V' Q) : ℝ :=
  plaqReal Q n character (wf n t (staticCfg n (x 0) U)) (x, P)

theorem continuous_sliceObs (t : ℝ) (x : V') (P : Plane) : Continuous (sliceObs n t x P) :=
  (plaqReal_continuous Q n character WilsonSingleLinkStaples.character_continuous _).comp
    ((continuous_wf_right n t).comp (staticCfg_continuous n _))

theorem static_Rκ_time (τ : ZMod (2 * n)) (U : Configuration V' Q) :
    staticCfg n τ (Rκ n 0 U) = staticCfg n (τ + 1) U := by
  classical
  refine config_ext n fun x μ => ?_
  rw [static_link, static_link]
  by_cases hμ : μ = 0
  · simp only [hμ, if_true]
  · simp only [if_neg hμ]
    rw [link_Rκ]
    have hs : sgn n 0 (ed n (Function.update x 0 τ) μ) = 1 := by
      have hc : ¬ sgnCond n 0 (Function.update x 0 τ) μ := by
        unfold sgnCond
        simp
      unfold sgn
      exact if_neg hc
    have hx : step (2 * n) (Function.update x 0 τ) 0 = Function.update x 0 (τ + 1) := by
      funext a
      by_cases ha : a = 0
      · subst ha
        simp [step]
      · simp [step, Function.update, ha]
    rw [hs, hx, one_mul]

theorem static_reflect (τ : ZMod (2 * n)) (U : Configuration V' Q) :
    staticCfg n τ (reflectConfiguration (2 * n) Q U) = staticCfg n (-τ) U := by
  classical
  refine config_ext n fun x μ => ?_
  rw [static_link, static_link]
  by_cases hμ : μ = 0
  · simp only [hμ, if_true]
  · simp only [if_neg hμ]
    rw [reflect_link_spatial (2 * n) Q U _ μ hμ]
    congr 1
    funext a
    by_cases ha : a = 0
    · subst ha
      simp [reflectVertex]
    · simp [reflectVertex, ha]

/-- A flowed static field does not depend on time: its plaquette values are the same one step later in time. -/
theorem plaq_static_step (t : ℝ) (τ : ZMod (2 * n)) (U : Configuration V' Q) (x : V') (P : Plane) :
    plaqReal Q n character (wf n t (staticCfg n τ U)) (step (2 * n) x 0, P) =
      plaqReal Q n character (wf n t (staticCfg n τ U)) (x, P) := by
  rw [← plaqReal_Rκ, ← wf_Rκ, static_Rκ_zero]

theorem plaq_static_time (t : ℝ) (τ : ZMod (2 * n)) (U : Configuration V' Q) (x : V') (P : Plane) (σ : ZMod (2 * n)) :
    plaqReal Q n character (wf n t (staticCfg n τ U)) (Function.update x 0 σ, P) =
      plaqReal Q n character (wf n t (staticCfg n τ U)) (x, P) := by
  have hnat (m : ℕ) : plaqReal Q n character (wf n t (staticCfg n τ U)) (Function.update x 0 (x 0 + (m : ZMod (2 * n))), P) =
      plaqReal Q n character (wf n t (staticCfg n τ U)) (x, P) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [← ih, ← plaq_static_step n t τ U (Function.update x 0 (x 0 + (m : ZMod (2 * n)))) P]
      congr 2
      funext a
      by_cases ha : a = 0
      · subst ha
        simp [step, add_assoc]
      · simp [step, Function.update, ha]
  have hval : x 0 + ((σ - x 0).val : ZMod (2 * n)) = σ := by
    rw [ZMod.natCast_zmod_val]
    ring
  rw [← hval]
  exact hnat _

/-- **The slice observable is covariant under every step of the compensated translation**, time included. -/
theorem sliceObs_Rκ (t : ℝ) (κ : Fin 4) (x : V') (P : Plane) (U : Configuration V' Q) :
    sliceObs n t x P (Rκ n κ U) = sliceObs n t (step (2 * n) x κ) P U := by
  unfold sliceObs
  by_cases hκ : κ = 0
  · subst hκ
    have e : step (2 * n) x 0 0 = x 0 + 1 := by simp [step]
    rw [static_Rκ_time, e, plaq_static_step]
  · have e : step (2 * n) x κ 0 = x 0 := by
      simp [step, Ne.symm hκ]
    rw [← static_Rκ_ne n _ κ hκ, wf_Rκ, plaqReal_Rκ, e]

/-- **The reflection acts on slice observables by reflecting the label.** So at positive flow time the reflected word
of a slice family is an ordinary word of the same family. This fails for four-dimensional flow. -/
theorem sliceObs_reflect (t : ℝ) (x : V') (P : Plane) (U : Configuration V' Q) :
    sliceObs n t x P (reflectConfiguration (2 * n) Q U) = sliceObs n t (reflectVertex (2 * n) x) P U := by
  unfold sliceObs
  have e : reflectVertex (2 * n) x 0 = -x 0 := by simp [reflectVertex]
  rw [static_reflect, e]
  have hx : reflectVertex (2 * n) x = Function.update x 0 (-x 0) := by
    funext a
    by_cases ha : a = 0
    · subst ha
      simp [reflectVertex]
    · simp [reflectVertex, ha]
  rw [hx, plaq_static_time]

theorem reflectVertex_add (x y : V') :
    reflectVertex (2 * n) (x + y) = reflectVertex (2 * n) x + reflectVertex (2 * n) y := by
  funext a
  by_cases ha : a = 0
  · subst ha
    simp [reflectVertex]
    ring
  · simp [reflectVertex, ha]

/-- A word of slice observables at sites shifted by `s`. -/
def sliceWord (t : ℝ) (w : List (V' × Plane)) (s : V') (U : Configuration V' Q) : ℂ :=
  word (fun (l : V' × Plane) U => ((sliceObs n t (l.1 + s) l.2 U : ℝ) : ℂ)) w U

theorem sliceWord_continuous (t : ℝ) (w : List (V' × Plane)) (s : V') : Continuous (sliceWord n t w s) :=
  word_continuous _ (fun _ => Complex.continuous_ofReal.comp (continuous_sliceObs n t _ _)) w

theorem sliceWord_step (t : ℝ) (w : List (V' × Plane)) (s : V') (κ : Fin 4) (U : Configuration V' Q) :
    sliceWord n t w (step (2 * n) s κ) U = sliceWord n t w s (Rκ n κ U) := by
  induction w with
  | nil => simp [sliceWord]
  | cons l w ih =>
    unfold sliceWord at ih ⊢
    rw [word_cons, word_cons, ih, sliceObs_Rκ]
    have e : step (2 * n) (l.1 + s) κ = l.1 + step (2 * n) s κ := by
      simp only [step, add_assoc]
    rw [e]

theorem sliceWord_integral (β t : ℝ) (w : List (V' × Plane)) (s : V') :
    ∫ U, sliceWord n t w s U ∂twistedLaw n β = ∫ U, sliceWord n t w 0 U ∂twistedLaw n β := by
  have hstep (κ : Fin 4) (y : V') : ∫ U, sliceWord n t w (step (2 * n) y κ) U ∂twistedLaw n β =
      ∫ U, sliceWord n t w y U ∂twistedLaw n β := by
    simp only [sliceWord_step]
    exact law_Rκ_complex n β κ (sliceWord_continuous n t w y)
  have hre := const_of_step n (fun s => (∫ U, sliceWord n t w s U ∂twistedLaw n β).re)
    (fun κ y => congrArg Complex.re (hstep κ y)) 0 s
  have him := const_of_step n (fun s => (∫ U, sliceWord n t w s U ∂twistedLaw n β).im)
    (fun κ y => congrArg Complex.im (hstep κ y)) 0 s
  exact Complex.ext hre him

theorem star_word_real {ι : Type*} (f : ι → Configuration V' Q → ℝ) (w : List ι) (U : Configuration V' Q) :
    star (word (fun l U => ((f l U : ℝ) : ℂ)) w U) = word (fun l U => ((f l U : ℝ) : ℂ)) w U := by
  induction w with
  | nil => simp [word]
  | cons i w ih =>
    rw [word_cons, star_mul', ih, Complex.star_def, Complex.conj_ofReal]

/-- The reflected integrand of a slice family, at sites shifted by `s` on the left and `θ s` on the right, is one word
at sites shifted by `s`. -/
theorem slice_integrand (t : ℝ) (a b : List (V' × Plane)) (s : V') (U : Configuration V' Q) :
    star (word (fun (l : V' × Plane) U => ((sliceObs n t (l.1 + s) l.2 U : ℝ) : ℂ)) a U) *
        word (fun (l : V' × Plane) U => ((sliceObs n t (l.1 + reflectVertex (2 * n) s) l.2 U : ℝ) : ℂ)) b
          (reflectConfiguration (2 * n) Q U) =
      sliceWord n t (a ++ b.map fun l => (reflectVertex (2 * n) l.1, l.2)) s U := by
  have hb : ∀ b : List (V' × Plane),
      word (fun (l : V' × Plane) U => ((sliceObs n t (l.1 + reflectVertex (2 * n) s) l.2 U : ℝ) : ℂ)) b
          (reflectConfiguration (2 * n) Q U) =
        sliceWord n t (b.map fun l => (reflectVertex (2 * n) l.1, l.2)) s U := by
    intro b
    induction b with
    | nil => simp [sliceWord]
    | cons l b ih =>
      unfold sliceWord at ih ⊢
      rw [List.map_cons, word_cons, word_cons, ih, sliceObs_reflect, reflectVertex_add,
        reflectVertex_twice]
  rw [star_word_real, hb]
  unfold sliceWord
  simp [word]

/-- **Lattice translations of reflected slice functions.** The left word moves by `s`, the right one by `θ s`, at any
flow time, for every lattice vector, time direction included. -/
theorem slice_entry_shift (β t : ℝ) (a b : List (V' × Plane)) (s : V') :
    ∫ U, star (word (fun (l : V' × Plane) U => ((sliceObs n t (l.1 + s) l.2 U : ℝ) : ℂ)) a U) *
        word (fun (l : V' × Plane) U => ((sliceObs n t (l.1 + reflectVertex (2 * n) s) l.2 U : ℝ) : ℂ)) b
          (reflectConfiguration (2 * n) Q U) ∂twistedLaw n β =
      ∫ U, star (word (fun (l : V' × Plane) U => ((sliceObs n t l.1 l.2 U : ℝ) : ℂ)) a U) *
        word (fun (l : V' × Plane) U => ((sliceObs n t l.1 l.2 U : ℝ) : ℂ)) b
          (reflectConfiguration (2 * n) Q U) ∂twistedLaw n β := by
  simp only [slice_integrand n t a b s]
  rw [sliceWord_integral n β t _ s, ← sliceWord_integral n β t _ 0]
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  have h := slice_integrand n t a b 0 U
  simp only [add_zero] at h
  have e : reflectVertex (2 * n) (0 : V') = 0 := by
    funext a
    by_cases ha : a = 0 <;> simp [reflectVertex, ha]
  simp only [e, add_zero] at h
  exact h.symm

end SliceSymmetry

section SliceLimit
open TwistedFlow TwistedLocalization
open WilsonSingleLinkStaples (Q character character_re)

variable (N : ℕ → ℕ) [∀ k, NeZero (N k)] (t : ℕ → ℝ) {β : ℕ → ℝ}

/-- **The slice-flowed reflected functions collapse to the same constant on every trajectory with `β → ∞`.** -/
theorem slice_os_tendsto (hβ : Tendsto β atTop atTop) (ht : ∀ k, 0 ≤ t k) (a b : List PhysLabel) :
    Tendsto (fun k => osEntry (sliceLabels N t) (fun k => spatialTwist (N k)) character β 2 k a b) atTop
      (𝓝 (((2 : ℝ) : ℂ) ^ (a.length + b.length))) := by
  refine os_tendsto_of_mean N (sliceLabels N t) (fun k l U => (sliceLabels N t).obs_le k l U) (fun l => ?_) a b
  have hbound : Tendsto (fun k => ∫ U, term (N k) Q (spatialTwist (N k)) character 2
      (wf (N k) (t k) (staticCfg (N k) (site (N k) l.1 0) U)) (site (N k) l.1, l.2) ∂twistedLaw (N k) (β k)) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => TwistedFlat.term_nonneg _ _ _) ?_
      (eventually_mean_small hβ)
    filter_upwards [hβ.eventually_ge_atTop (1 / 32)] with k hk
    exact slice_term_mean (N k) (β k) _ (ht k) hk _
  exact hbound.congr fun k => integral_congr_ae (Eventually.of_forall fun U => (plaq_sub_two (N k) _ _).symm)

/-- So on every trajectory with `β → ∞` and `t ≥ 0`, the limit in `sliceFlow_limit_exists` is the rank-one constant.
Reflection positivity is recovered at positive flow time, and nothing is gained for nontriviality at plaquette level. -/
theorem sliceFlow_limit_is_constant (hβ : Tendsto β atTop atTop) (ht : ∀ k, 0 ≤ t k)
    (W : List PhysLabel × List PhysLabel → ℂ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hW : ∀ a b, Tendsto (fun k => osEntry (sliceLabels N t) (fun k => spatialTwist (N k)) character β 2 (φ k) a b)
        atTop (𝓝 (W (a, b)))) :
    W = fun p => ((2 : ℝ) : ℂ) ^ (p.1.length + p.2.length) := by
  funext p
  exact tendsto_nhds_unique (hW p.1 p.2) ((slice_os_tendsto N t hβ ht p.1 p.2).comp hφ.tendsto_atTop)

/-- A rational point that is a site of the lattice of side `2m`. -/
def OnGrid (m : ℕ) (c : Fin 4 → ℚ) : Prop := ∀ μ, ∃ z : ℤ, c μ * ((2 * m : ℕ) : ℚ) = z

/-- Every rational point is eventually a site on the trajectory `N k = (k + 1)!`. -/
theorem factorial_onGrid (c : Fin 4 → ℚ) : ∀ᶠ k : ℕ in atTop, OnGrid ((k + 1).factorial) c := factorial_grid c

/-- The time reflection of a physical point. -/
def reflectTime (c : Fin 4 → ℚ) : Fin 4 → ℚ := Function.update c 0 (-c 0)

/-- The time reflection of a label. -/
def reflectLabel (l : PhysLabel) : PhysLabel := (reflectTime l.1, l.2)

theorem OnGrid.reflect {m : ℕ} {c : Fin 4 → ℚ} (hc : OnGrid m c) : OnGrid m (reflectTime c) := by
  intro μ
  obtain ⟨z, hz⟩ := hc μ
  by_cases hμ : μ = 0
  · subst hμ
    refine ⟨-z, ?_⟩
    simp only [reflectTime, Function.update_self]
    rw [neg_mul, hz]
    push_cast
    rfl
  · refine ⟨z, ?_⟩
    simpa [reflectTime, hμ] using hz

theorem site_reflect (m : ℕ) [NeZero m] {c : Fin 4 → ℚ} (hc : OnGrid m c) :
    site m (reflectTime c) = reflectVertex (2 * m) (site m c) := by
  funext μ
  obtain ⟨z, hz⟩ := hc μ
  by_cases hμ : μ = 0
  · subst hμ
    simp only [site, reflectTime, reflectVertex, Function.update_self, if_true]
    rw [neg_mul, hz, ← Int.cast_neg, Int.floor_intCast, Int.floor_intCast]
    push_cast
    rfl
  · simp [site, reflectTime, reflectVertex, hμ]

/-- A word of slice labels is a word of slice observables at the lattice sites of its labels. -/
theorem slice_word_site (k : ℕ) (w : List PhysLabel) (U : Configuration (Vertex (2 * N k)) Q) :
    word ((sliceLabels N t).obs k) w U =
      word (fun (l : Vertex (2 * N k) × Plane) U => ((sliceObs (N k) (t k) l.1 l.2 U : ℝ) : ℂ))
        (w.map fun l => (site (N k) l.1, l.2)) U := by
  induction w with
  | nil => simp
  | cons l w ih =>
    rw [List.map_cons, word_cons, word_cons, ih]
    rfl

/-- The same word after a translation by a site. -/
theorem slice_word_shift (k : ℕ) (c : Fin 4 → ℚ) (hc : OnGrid (N k) c) (w : List PhysLabel)
    (U : Configuration (Vertex (2 * N k)) Q) :
    word ((sliceLabels N t).obs k) (w.map (shiftLabel c)) U =
      word (fun (l : Vertex (2 * N k) × Plane) U => ((sliceObs (N k) (t k) (l.1 + site (N k) c) l.2 U : ℝ) : ℂ))
        (w.map fun l => (site (N k) l.1, l.2)) U := by
  induction w with
  | nil => simp
  | cons l w ih =>
    rw [List.map_cons, List.map_cons, word_cons, word_cons, ih]
    congr 1
    change ((sliceObs (N k) (t k) (site (N k) (l.1 + c)) l.2 U : ℝ) : ℂ) = _
    rw [site_add (N k) c l.1 hc]

/-- **Exact lattice translation of the reflected slice functions.** Moving the left word by a site `c` and the right
word by its reflection leaves every entry fixed, at any flow time and in every direction, time included. -/
theorem slice_osEntry_shift (β : ℕ → ℝ) (k : ℕ) (c : Fin 4 → ℚ) (hc : OnGrid (N k) c) (a b : List PhysLabel) :
    osEntry (sliceLabels N t) (fun k => spatialTwist (N k)) character β 2 k (a.map (shiftLabel c))
        (b.map (shiftLabel (reflectTime c))) =
      osEntry (sliceLabels N t) (fun k => spatialTwist (N k)) character β 2 k a b := by
  have h := slice_entry_shift (N k) (β k) (t k) (a.map fun l => (site (N k) l.1, l.2))
    (b.map fun l => (site (N k) l.1, l.2)) (site (N k) c)
  unfold osEntry
  simp only [slice_word_shift N t k c hc, slice_word_shift N t k _ hc.reflect, site_reflect (N k) hc]
  simp only [slice_word_site N t k]
  exact h

/-- **A reflected slice function is an ordinary one.** If the right word is on the lattice, its reflection can be moved
to the left, so the reflected entry is the Schwinger function of the labels and their mirror images. -/
theorem slice_osEntry_word (β : ℕ → ℝ) (k : ℕ) (a b : List PhysLabel) (hb : ∀ l ∈ b, OnGrid (N k) l.1) :
    osEntry (sliceLabels N t) (fun k => spatialTwist (N k)) character β 2 k a b =
      osEntry (sliceLabels N t) (fun k => spatialTwist (N k)) character β 2 k (a ++ b.map reflectLabel) [] := by
  unfold osEntry
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  have h := slice_integrand (N k) (t k) (a.map fun l => (site (N k) l.1, l.2))
    (b.map fun l => (site (N k) l.1, l.2)) 0 U
  have e0 : reflectVertex (2 * N k) (0 : Vertex (2 * N k)) = 0 := by
    funext a
    by_cases ha : a = 0 <;> simp [reflectVertex, ha]
  simp only [e0, add_zero] at h
  simp only [slice_word_site N t k]
  rw [h]
  have hmap : ((a ++ b.map reflectLabel).map fun l => (site (N k) l.1, l.2)) =
      (a.map fun l => (site (N k) l.1, l.2)) ++
        (b.map fun l => (site (N k) l.1, l.2)).map fun l => (reflectVertex (2 * N k) l.1, l.2) := by
    rw [List.map_append, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun l hl => ?_
    simp only [Function.comp, reflectLabel, site_reflect (N k) (hb l hl)]
  rw [hmap]
  simp only [List.map_nil, word, List.prod_nil, mul_one]
  have hr := star_word_real (N k) (fun (l : Vertex (2 * N k) × Plane) U => sliceObs (N k) (t k) l.1 l.2 U)
    ((a.map fun l => (site (N k) l.1, l.2)) ++
        (b.map fun l => (site (N k) l.1, l.2)).map fun l => (reflectVertex (2 * N k) l.1, l.2)) U
  unfold word at hr
  rw [hr]
  simp [sliceWord, word]

/-- **A positive-flow family with both reflection positivity and translation invariance in the limit.** On a trajectory
whose lattices eventually contain every rational point, such as `N k = (k + 1)!`, for any couplings and flow times,
some subsequence converges with: the formal package, with reflection positivity on the closed half; invariance under
every rational translation, the left word moving by `c` and the right by its reflection; and the reduction of reflected
functions to ordinary ones.

This is closedness, on top of exact lattice symmetries. It holds for every coupling sequence. On `β → ∞` this limit is
the constant (`sliceFlow_limit_is_constant`). Whether a nonconstant limit exists at any flow time, on any trajectory that
could be a continuum limit, is open. -/
theorem sliceFlow_os_limit (β : ℕ → ℝ) (hgrid : ∀ c : Fin 4 → ℚ, ∀ᶠ k in atTop, OnGrid (N k) c) :
    ∃ (W : List PhysLabel × List PhysLabel → ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ a b, Tendsto (fun k => osEntry (sliceLabels N t) (fun k => spatialTwist (N k)) character β 2 (φ k) a b)
        atTop (𝓝 (W (a, b)))) ∧
      LimitPackage (sliceLabels N t) ClosedPosLabel W ∧
      (∀ c a b, W (a.map (shiftLabel c), b.map (shiftLabel (reflectTime c))) = W (a, b)) ∧
      (∀ a b, W (a, b) = W (a ++ b.map reflectLabel, [])) := by
  obtain ⟨W, φ, hφ, hW, hP⟩ := sliceFlow_limit_exists N t β
  refine ⟨W, φ, hφ, hW, hP, fun c a b => ?_, fun a b => ?_⟩
  · refine tendsto_nhds_unique (hW _ _) ((hW a b).congr' ?_)
    filter_upwards [hφ.tendsto_atTop.eventually (hgrid c)] with k hk
    exact (slice_osEntry_shift N t β (φ k) c hk a b).symm
  · refine tendsto_nhds_unique (hW a b) ((hW _ _).congr' ?_)
    have hev : ∀ᶠ k in atTop, ∀ l ∈ b.toFinset, OnGrid (N (φ k)) l.1 := by
      classical
      rw [Filter.eventually_all_finset]
      exact fun l _ => hφ.tendsto_atTop.eventually (hgrid l.1)
    filter_upwards [hev] with k hk
    exact (slice_osEntry_word N t β (φ k) a b fun l hl => hk l (List.mem_toFinset.mpr hl)).symm

end SliceLimit

/-! ### A nonconstant limit: winding loops, and what it says about nontriviality

Winding loops in the direction `3`, which misses the twist, have the physical size of the torus. So the collapse theorems
above do not apply to them. Their mean vanishes exactly, by the slab flip, at every coupling and size. When `β` is much
larger than `N⁴`, Stokes and the twist force each loop to a common sign, so the limit is the two-state mixture `parityW`,
with rank two. This is not a continuum theory: it is the long-range order of a center sign on a free torus, and
flip-even functions are constant in it. It shows that the `LimitPackage` does have nonconstant models on the actual law,
and that a nonzero connected separated two-point function is not what Target A wants unless restricted to neutral
observables. It is not proved at `β ~ log N`. -/

section Polyakov
open TwistedFlow TwistedLocalization TwistedRectangle TwistedStability TwistedFlat
open WilsonSingleLinkStaples (Q character character_re)
open scoped Quaternion

variable (n : ℕ) [NeZero n]
local notation "V'" => Vertex (2 * n)

/-- The holonomy once around the torus in the direction `3`, based at `x`. This direction does not meet the twist. -/
def polyHol (x : V') (U : Configuration V' Q) : Q := run (linkValue (2 * n) Q U) 3 x (2 * n)

/-- The winding loop in direction `3`, read as half its trace. A loop of the physical size of the torus. -/
def polyR (x : V') (U : Configuration V' Q) : ℝ := ((polyHol n x U : Q) : ℍ[ℝ]).re

theorem continuous_run (μ : Fin 4) (x : V') (m : ℕ) :
    Continuous fun U : Configuration V' Q => run (linkValue (2 * n) Q U) μ x m := by
  induction m with
  | zero => exact continuous_const
  | succ m ih => exact ih.mul (TwistedSlice.continuous_linkValue n _ _)

theorem continuous_polyR (x : V') : Continuous (polyR n x) :=
  Quaternion.continuous_re.comp (continuous_subtype_val.comp (continuous_run n 3 x (2 * n)))

theorem polyR_abs_le (x : V') (U : Configuration V' Q) : |polyR n x U| ≤ 1 := TwistedFlat.re_le_one _

/-- The slab flip in direction `3` multiplies every winding loop in direction `3` by `-1`. -/
theorem polyR_flip (x : V') (U : Configuration V' Q) :
    polyR n x (TwistedNeutral.flip4 (2 * n) 3 0 U) = -polyR n x U := by
  have hrun : ∀ m : ℕ, run (linkValue (2 * n) Q (TwistedNeutral.flip4 (2 * n) 3 0 U)) 3 x m =
      ω ^ (∑ k ∈ Finset.range m, if (x 3 + (k : ZMod (2 * n)) = 0) then 1 else 0) *
        run (linkValue (2 * n) Q U) 3 x m := by
    intro m
    induction m with
    | zero => simp [run]
    | succ m ih =>
      simp only [run, Finset.sum_range_succ, ih, pow_add]
      have hl : linkValue (2 * n) Q (TwistedNeutral.flip4 (2 * n) 3 0 U) (walk 3 x m) 3 =
          (if x 3 + (m : ZMod (2 * n)) = 0 then ω else 1) * linkValue (2 * n) Q U (walk 3 x m) 3 := by
        have hc : walk 3 x m 3 = x 3 + (m : ZMod (2 * n)) := walk_apply_same 3 x m
        change TwistedNeutral.flip4 (2 * n) 3 0 U ⟨walk 3 x m, step (2 * n) (walk 3 x m) 3, forward (2 * n) (walk 3 x m) 3⟩ = _
        rw [TwistedNeutral.flip4_apply]
        simp only [true_and, hc]
        split_ifs
        · rfl
        · rw [one_mul]
          rfl
      rw [hl]
      by_cases hz : x 3 + (m : ZMod (2 * n)) = 0
      · simp only [if_pos hz, pow_one]
        rw [← mul_assoc, mul_assoc (ω ^ _), ((ω_commute _).symm).eq]
        simp only [mul_assoc]
      · simp only [if_neg hz, pow_zero, one_mul, mul_one]
        simp only [mul_assoc]
  unfold polyR polyHol
  rw [hrun, TwistedFlat.indicator_sum, pow_one]
  change ((-1 : ℍ[ℝ]) * _).re = _
  simp

theorem reflect_walk (y : V') (m : ℕ) :
    reflectVertex (2 * n) (walk 3 y m) = walk 3 (reflectVertex (2 * n) y) m := by
  funext a
  by_cases ha : a = 0
  · subst ha
    simp [reflectVertex, walk]
  · simp [reflectVertex, walk, ha]

/-- **The reflection moves a winding loop to the reflected base.** Direction `3` is spatial. -/
theorem polyR_reflect (y : V') (U : Configuration V' Q) :
    polyR n y (reflectConfiguration (2 * n) Q U) = polyR n (reflectVertex (2 * n) y) U := by
  have hrun : ∀ m : ℕ, run (linkValue (2 * n) Q (reflectConfiguration (2 * n) Q U)) 3 y m =
      run (linkValue (2 * n) Q U) 3 (reflectVertex (2 * n) y) m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      simp only [run, ih]
      rw [reflect_link_spatial (2 * n) Q U _ 3 (by decide), reflect_walk]
  unfold polyR polyHol
  rw [hrun]

/-- The sum of plaquette defects on a sheet. -/
def polyErr (μ ν : Fin 4) (x : V') (a b : ℕ) (U : Configuration V' Q) : ℝ :=
  ∑ j ∈ Finset.range b, ∑ i ∈ Finset.range a,
    TwistedStability.defect (linkValue (2 * n) Q U) μ ν (walk μ (walk ν x j) i)

theorem polyErr_nonneg (μ ν : Fin 4) (x : V') (a b : ℕ) (U : Configuration V' Q) : 0 ≤ polyErr n μ ν x a b U :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => TwistedStability.defect_nonneg _ _ _ _

theorem re_conj' (g X : Q) : ((g * X * g⁻¹ : Q) : ℍ[ℝ]).re = (X : ℍ[ℝ]).re := by
  have e : ((g * X * g⁻¹ : Q) : ℍ[ℝ]) = ((g * X : Q) : ℍ[ℝ]) * ((g⁻¹ : Q) : ℍ[ℝ]) := rfl
  rw [e, TwistedActionJet.re_comm]
  have e₂ : ((g⁻¹ : Q) : ℍ[ℝ]) * ((g * X : Q) : ℍ[ℝ]) = ((g⁻¹ * (g * X) : Q) : ℍ[ℝ]) := rfl
  rw [e₂, inv_mul_cancel_left]

/-- **Moving a winding loop transversally costs only the defects of the sheet it sweeps.** -/
theorem polyR_move (κ : Fin 4) (x : V') (b : ℕ) (U : Configuration V' Q) :
    |polyR n (walk κ x b) U - polyR n x U| ≤ polyErr n κ 3 x b (2 * n) U := by
  set L := linkValue (2 * n) Q U with hL
  have h := rectangle_error L κ 3 (twistExp κ 3) (TwistedStability.defect L κ 3)
    (fun y => cell_of_defect _ _ _ _ _ _ le_rfl) x b (2 * n)
  have hz : (∑ j ∈ Finset.range (2 * n), ∑ i ∈ Finset.range b, twistExp (N := 2 * n) κ 3 (walk κ (walk 3 x j) i)) = 0 := by
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => ?_
    simp [twistExp]
  rw [hz, pow_zero, one_mul, walk_card] at h
  set B := run L κ x b with hB
  set W' := run L 3 (walk κ x b) (2 * n) with hW'
  set W := run L 3 x (2 * n) with hW
  have h₁ : TwistedStability.d (B * W' * B⁻¹) W ≤ polyErr n κ 3 x b (2 * n) U := by
    have e := TwistedStability.d_mul_right B⁻¹ (B * W') (W * B)
    have e₂ : W * B * B⁻¹ = W := by group
    rw [e₂] at e
    rw [e]
    exact h
  have h₂ := TwistedSliceLift.abs_re_sub_le (B * W' * B⁻¹) W
  rw [re_conj'] at h₂
  exact h₂.trans h₁

theorem polyR_walk3 (x : V') (b : ℕ) (U : Configuration V' Q) : polyR n (walk 3 x b) U = polyR n x U := by
  have h := polyR_move n 3 x b U
  have hz : polyErr n 3 3 x b (2 * n) U = 0 := by
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => ?_
    unfold TwistedStability.defect TwistedStability.d twistExp
    simp
  rw [hz] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

theorem walk_decomp (y : V') :
    y = walk 3 (walk 0 (walk 1 (walk 2 (0 : V') (y 2).val) (y 1).val) (y 0).val) (y 3).val := by
  funext a
  fin_cases a <;> simp [-ZMod.natCast_val, walk, ZMod.natCast_zmod_val]

/-- Every base is joined to the origin by three sheets. -/
def polyDist (y : V') (U : Configuration V' Q) : ℝ :=
  polyErr n 0 3 (walk 1 (walk 2 (0 : V') (y 2).val) (y 1).val) (y 0).val (2 * n) U +
    polyErr n 1 3 (walk 2 (0 : V') (y 2).val) (y 1).val (2 * n) U + polyErr n 2 3 (0 : V') (y 2).val (2 * n) U

theorem polyR_to_zero (y : V') (U : Configuration V' Q) : |polyR n y U - polyR n 0 U| ≤ polyDist n y U := by
  conv_lhs => rw [walk_decomp n y, polyR_walk3]
  have h0 := polyR_move n 0 (walk 1 (walk 2 (0 : V') (y 2).val) (y 1).val) (y 0).val U
  have h1 := polyR_move n 1 (walk 2 (0 : V') (y 2).val) (y 1).val U
  have h2 := polyR_move n 2 (0 : V') (y 2).val U
  unfold polyDist
  have t₀ := abs_sub_le (polyR n (walk 0 (walk 1 (walk 2 (0 : V') (y 2).val) (y 1).val) (y 0).val) U)
    (polyR n (walk 1 (walk 2 (0 : V') (y 2).val) (y 1).val) U) (polyR n 0 U)
  have t₁ := abs_sub_le (polyR n (walk 1 (walk 2 (0 : V') (y 2).val) (y 1).val) U)
    (polyR n (walk 2 (0 : V') (y 2).val) U) (polyR n 0 U)
  linarith only [h0, h1, h2, t₀, t₁]

/-- The total defect of the three sheets through the origin that enter the winding relations. -/
def polyCore (U : Configuration V' Q) : ℝ :=
  polyErr n 1 2 (0 : V') (2 * n) (2 * n) U + polyErr n 1 3 (0 : V') (2 * n) (2 * n) U +
    polyErr n 2 3 (0 : V') (2 * n) (2 * n) U

theorem polyCore_nonneg (U : Configuration V' Q) : 0 ≤ polyCore n U :=
  add_nonneg (add_nonneg (polyErr_nonneg _ _ _ _ _ _ _) (polyErr_nonneg _ _ _ _ _ _ _)) (polyErr_nonneg _ _ _ _ _ _ _)

/-- **A winding loop in direction `3` is near `±1` when the three sheets through the origin are nearly flat.** The bound
is linear in the defects because it is applied in mean. This uses the twist through `near_central`: the windings in
directions `1, 2` nearly anticommute, and the loop nearly commutes with both. -/
theorem polyR_sq_lower (U : Configuration V' Q) : 1 - polyR n 0 U ^ 2 ≤ 8 * polyCore n U := by
  set L := linkValue (2 * n) Q U with hL
  set e := polyCore n U with he
  have he0 : 0 ≤ e := polyCore_nonneg n U
  have hr := polyR_abs_le n 0 U
  by_cases he1 : e ≤ 1
  · have hwind (μ ν : Fin 4) := winding_error L μ ν (twistExp μ ν) (TwistedStability.defect L μ ν)
      (fun y => cell_of_defect _ _ _ _ _ _ le_rfl) (0 : V')
    have h12 := hwind 1 2
    have h13 := hwind 1 3
    have h23 := hwind 2 3
    rw [twist_total, pow_one] at h12
    rw [exp_sum_zero 1 3 (by decide), pow_zero, one_mul] at h13
    rw [exp_sum_zero 2 3 (by decide), pow_zero, one_mul] at h23
    have p₁ := polyErr_nonneg n 1 2 (0 : V') (2 * n) (2 * n) U
    have p₂ := polyErr_nonneg n 1 3 (0 : V') (2 * n) (2 * n) U
    have p₃ := polyErr_nonneg n 2 3 (0 : V') (2 * n) (2 * n) U
    have hc := near_central _ _ (polyHol n 0 U) e he0 he1
      (h12.trans (by change polyErr n 1 2 (0 : V') (2 * n) (2 * n) U ≤ e; rw [he]; unfold polyCore; linarith only [p₂, p₃]))
      (by
        rw [d_comm]
        exact h13.trans (by change polyErr n 1 3 (0 : V') (2 * n) (2 * n) U ≤ e; rw [he]; unfold polyCore; linarith only [p₁, p₃]))
      (by
        rw [d_comm]
        exact h23.trans (by change polyErr n 2 3 (0 : V') (2 * n) (2 * n) U ≤ e; rw [he]; unfold polyCore; linarith only [p₁, p₂]))
    set W : Q := polyHol n 0 U with hW
    have hre : polyR n 0 U = (W : ℍ[ℝ]).re := rfl
    have hrb := abs_le.mp hr
    rw [hre] at hrb ⊢
    have he2 : e ^ 2 ≤ e := by nlinarith only [he0, he1]
    rcases hc with h | h
    · have hsqd := pow_le_pow_left₀ (TwistedStability.d_nonneg _ _) h 2
      have e₀ := SU2GaussianMass.chord_square W
      have e₁ : TwistedStability.d W 1 = ‖(W : ℍ[ℝ]) - 1‖ := rfl
      rw [e₁, e₀] at hsqd
      nlinarith only [hsqd, hrb.1, hrb.2, he2]
    · have hsqd := pow_le_pow_left₀ (TwistedStability.d_nonneg _ _) h 2
      rw [show TwistedStability.d W ω ^ 2 = 2 - 2 * TwistedLandau.rePart W ω from TwistedLandau.d_sq_eq W ω] at hsqd
      have hinv : (ω : Q)⁻¹ = ω := inv_eq_of_mul_eq_one_left TwistedTransfer.ω_mul_ω
      have hp : TwistedLandau.rePart W ω = -(W : ℍ[ℝ]).re := by
        simp only [TwistedLandau.rePart, hinv, ω_coe]
        simp
      rw [hp] at hsqd
      nlinarith only [hsqd, hrb.1, hrb.2, he2]
  · push_neg at he1
    nlinarith only [he1, sq_nonneg (polyR n 0 U)]

/-- Two winding loops at any two bases agree in sign, up to the defects of the sheets between them. -/
theorem polyR_pair (x y : V') (U : Configuration V' Q) :
    |polyR n x U * polyR n y U - 1| ≤ 8 * polyCore n U + polyDist n x U + polyDist n y U := by
  have hx := polyR_to_zero n x U
  have hy := polyR_to_zero n y U
  have h0 := polyR_sq_lower n U
  have ax := abs_le.mp (polyR_abs_le n x U)
  have a0 := abs_le.mp (polyR_abs_le n 0 U)
  have hsq : polyR n 0 U ^ 2 ≤ 1 := by nlinarith only [a0.1, a0.2]
  have e : polyR n x U * polyR n y U - 1 =
      polyR n x U * (polyR n y U - polyR n 0 U) + polyR n 0 U * (polyR n x U - polyR n 0 U) + (polyR n 0 U ^ 2 - 1) := by
    ring
  rw [e]
  have h₁ : |polyR n x U * (polyR n y U - polyR n 0 U)| ≤ polyDist n y U := by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (polyR_abs_le n x U)).trans hy
  have h₂ : |polyR n 0 U * (polyR n x U - polyR n 0 U)| ≤ polyDist n x U := by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (polyR_abs_le n 0 U)).trans hx
  have h₃ : |polyR n 0 U ^ 2 - 1| ≤ 8 * polyCore n U := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith only [hsq])]
    exact h0
  exact (abs_add_three _ _ _).trans (by linarith only [h₁, h₂, h₃])

/-! The mean of a plaquette defect -/

theorem integral_add_three {α : Type*} [MeasurableSpace α] {ν : Measure α} {f g h : α → ℝ} (hf : Integrable f ν)
    (hg : Integrable g ν) (hh : Integrable h ν) :
    ∫ U, f U + g U + h U ∂ν = ∫ U, f U ∂ν + ∫ U, g U ∂ν + ∫ U, h U ∂ν := by
  have hfg : Integrable (fun U => f U + g U) ν := hf.add hg
  rw [integral_add hfg hh, integral_add hf hg]

theorem continuous_defect (μ ν : Fin 4) (x : V') :
    Continuous fun U : Configuration V' Q => TwistedStability.defect (linkValue (2 * n) Q U) μ ν x := by
  unfold TwistedStability.defect TwistedStability.d
  refine continuous_norm.comp (Continuous.sub ?_ continuous_const)
  refine continuous_subtype_val.comp ?_
  exact (((TwistedSlice.continuous_linkValue n _ _).mul (TwistedSlice.continuous_linkValue n _ _)).mul
    (TwistedSlice.continuous_linkValue n _ _).inv).mul (TwistedSlice.continuous_linkValue n _ _).inv

variable (β : ℝ)

/-- The mean of a plaquette defect, after any continuous map under which the mean squared defect is bounded. -/
theorem defect_mean_of (T : Configuration V' Q → Configuration V' Q) (hT : Continuous T) {μ ν : Fin 4} (h : μ < ν) (x : V')
    {C : ℝ} (hterm : ∫ U, term n Q (spatialTwist n) character 2 (T U) (x, ⟨(μ, ν), h⟩) ∂twistedLaw n β ≤ C) :
    ∫ U, TwistedStability.defect (linkValue (2 * n) Q (T U)) μ ν x ∂twistedLaw n β ≤ Real.sqrt C := by
  haveI : IsProbabilityMeasure (twistedLaw n β) :=
    law_probability n Q (spatialTwist n) character WilsonSingleLinkStaples.character_continuous β 2
  have hc : Continuous fun U => TwistedStability.defect (linkValue (2 * n) Q (T U)) μ ν x :=
    (continuous_defect n μ ν x).comp hT
  have hi := integrable_law n β hc
  have hi2 := integrable_law n β (hc.pow 2)
  set m := ∫ U, TwistedStability.defect (linkValue (2 * n) Q (T U)) μ ν x ∂twistedLaw n β with hm
  have hvar : 0 ≤ ∫ U, (TwistedStability.defect (linkValue (2 * n) Q (T U)) μ ν x - m) ^ 2 ∂twistedLaw n β :=
    integral_nonneg fun _ => sq_nonneg _
  have hexp : ∫ U, (TwistedStability.defect (linkValue (2 * n) Q (T U)) μ ν x - m) ^ 2 ∂twistedLaw n β =
      ∫ U, TwistedStability.defect (linkValue (2 * n) Q (T U)) μ ν x ^ 2 ∂twistedLaw n β - m ^ 2 := by
    have e : (fun U : Configuration V' Q => (TwistedStability.defect (linkValue (2 * n) Q (T U)) μ ν x - m) ^ 2) =
        fun U => TwistedStability.defect (linkValue (2 * n) Q (T U)) μ ν x ^ 2 -
          2 * m * TwistedStability.defect (linkValue (2 * n) Q (T U)) μ ν x + m ^ 2 := by
      funext U
      ring
    have hj : Integrable (fun U : Configuration V' Q => TwistedStability.defect (linkValue (2 * n) Q (T U)) μ ν x ^ 2 -
        2 * m * TwistedStability.defect (linkValue (2 * n) Q (T U)) μ ν x) (twistedLaw n β) := hi2.sub (hi.const_mul _)
    rw [e, integral_add hj (integrable_const _), integral_sub hi2 (hi.const_mul _),
      integral_const_mul, integral_const]
    simp only [probReal_univ, one_smul]
    rw [← hm]
    ring
  have hterm' : ∫ U, TwistedStability.defect (linkValue (2 * n) Q (T U)) μ ν x ^ 2 ∂twistedLaw n β ≤ C := by
    simpa only [term_eq_defect_sq n _ x μ ν h] using hterm
  apply Real.le_sqrt_of_sq_le
  linarith only [hvar, hexp, hterm']

theorem defect_mean_le (hβ : 1 / 32 ≤ β) {μ ν : Fin 4} (h : μ < ν) (x : V') :
    ∫ U, TwistedStability.defect (linkValue (2 * n) Q U) μ ν x ∂twistedLaw n β ≤
      Real.sqrt (4 * Real.log (SU2GaussianMass.cap (24 * β)) / β) := by
  refine defect_mean_of n β id continuous_id h x ?_
  have ht := law_term_mean_wf n β (le_refl (0 : ℝ)) hβ (x, ⟨(μ, ν), h⟩)
  simpa only [wf_zero] using ht

theorem polyErr_mean_of (T : Configuration V' Q → Configuration V' Q) (hT : Continuous T) {μ ν : Fin 4} (h : μ < ν)
    {C : ℝ} (hterm : ∀ y, ∫ U, term n Q (spatialTwist n) character 2 (T U) (y, ⟨(μ, ν), h⟩) ∂twistedLaw n β ≤ C)
    (x : V') (a b : ℕ) (ha : a ≤ 2 * n) (hb : b ≤ 2 * n) :
    ∫ U, polyErr n μ ν x a b (T U) ∂twistedLaw n β ≤ ((2 * n : ℕ) : ℝ) ^ 2 * Real.sqrt C := by
  set R := Real.sqrt C with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hi (j i : ℕ) : Integrable (fun U => TwistedStability.defect (linkValue (2 * n) Q (T U)) μ ν (walk μ (walk ν x j) i))
      (twistedLaw n β) := integrable_law n β ((continuous_defect n μ ν (walk μ (walk ν x j) i)).comp hT)
  unfold polyErr
  rw [integral_finset_sum _ fun j _ => integrable_finset_sum _ fun i _ => hi j i]
  simp only [integral_finset_sum _ fun i _ => hi _ i]
  have hb' : (b : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast hb
  have ha' : (a : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast ha
  calc _ ≤ ∑ _j ∈ Finset.range b, ∑ _i ∈ Finset.range a, R :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => defect_mean_of n β T hT h _ (hterm _)
    _ = (b : ℝ) * ((a : ℝ) * R) := by simp
    _ ≤ ((2 * n : ℕ) : ℝ) * (((2 * n : ℕ) : ℝ) * R) :=
        mul_le_mul hb' (mul_le_mul_of_nonneg_right ha' hR0) (by positivity) (by positivity)
    _ = _ := by ring

theorem polyErr_mean_le (hβ : 1 / 32 ≤ β) {μ ν : Fin 4} (h : μ < ν) (x : V') (a b : ℕ) (ha : a ≤ 2 * n)
    (hb : b ≤ 2 * n) :
    ∫ U, polyErr n μ ν x a b U ∂twistedLaw n β ≤
      ((2 * n : ℕ) : ℝ) ^ 2 * Real.sqrt (4 * Real.log (SU2GaussianMass.cap (24 * β)) / β) := by
  refine polyErr_mean_of n β id continuous_id h (fun y => ?_) x a b ha hb
  have ht := law_term_mean_wf n β (le_refl (0 : ℝ)) hβ (y, ⟨(μ, ν), h⟩)
  simpa only [wf_zero] using ht

theorem integrable_polyErr (μ ν : Fin 4) (x : V') (a b : ℕ) : Integrable (polyErr n μ ν x a b) (twistedLaw n β) :=
  integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun i _ =>
    integrable_law n β (continuous_defect n μ ν (walk μ (walk ν x j) i))

theorem val_le_two (a : ZMod (2 * n)) : a.val ≤ 2 * n := (ZMod.val_lt a).le

theorem polyDist_mean_le (hβ : 1 / 32 ≤ β) (y : V') :
    ∫ U, polyDist n y U ∂twistedLaw n β ≤
      3 * (((2 * n : ℕ) : ℝ) ^ 2 * Real.sqrt (4 * Real.log (SU2GaussianMass.cap (24 * β)) / β)) := by
  unfold polyDist
  rw [integral_add_three (integrable_polyErr n β _ _ _ _ _) (integrable_polyErr n β _ _ _ _ _)
    (integrable_polyErr n β _ _ _ _ _)]
  have h₀ := polyErr_mean_le n β hβ (μ := 0) (ν := 3) (by decide) (walk 1 (walk 2 (0 : V') (y 2).val) (y 1).val)
    (y 0).val (2 * n) (val_le_two n _) le_rfl
  have h₁ := polyErr_mean_le n β hβ (μ := 1) (ν := 3) (by decide) (walk 2 (0 : V') (y 2).val)
    (y 1).val (2 * n) (val_le_two n _) le_rfl
  have h₂ := polyErr_mean_le n β hβ (μ := 2) (ν := 3) (by decide) (0 : V') (y 2).val (2 * n) (val_le_two n _) le_rfl
  linarith only [h₀, h₁, h₂]

theorem polyCore_mean_le (hβ : 1 / 32 ≤ β) :
    ∫ U, polyCore n U ∂twistedLaw n β ≤
      3 * (((2 * n : ℕ) : ℝ) ^ 2 * Real.sqrt (4 * Real.log (SU2GaussianMass.cap (24 * β)) / β)) := by
  unfold polyCore
  rw [integral_add_three (integrable_polyErr n β _ _ _ _ _) (integrable_polyErr n β _ _ _ _ _)
    (integrable_polyErr n β _ _ _ _ _)]
  have h₀ := polyErr_mean_le n β hβ (μ := 1) (ν := 2) (by decide) (0 : V') (2 * n) (2 * n) le_rfl le_rfl
  have h₁ := polyErr_mean_le n β hβ (μ := 1) (ν := 3) (by decide) (0 : V') (2 * n) (2 * n) le_rfl le_rfl
  have h₂ := polyErr_mean_le n β hβ (μ := 2) (ν := 3) (by decide) (0 : V') (2 * n) (2 * n) le_rfl le_rfl
  linarith only [h₀, h₁, h₂]

/-- **The mean of `|r_x r_y - 1|` at any two bases**, at every size and every `β ≥ 1/32`. -/
theorem polyR_pair_mean (hβ : 1 / 32 ≤ β) (x y : V') :
    ∫ U, |polyR n x U * polyR n y U - 1| ∂twistedLaw n β ≤
      30 * (((2 * n : ℕ) : ℝ) ^ 2 * Real.sqrt (4 * Real.log (SU2GaussianMass.cap (24 * β)) / β)) := by
  have hdist (z : V') : Integrable (polyDist n z) (twistedLaw n β) :=
    ((integrable_polyErr n β _ _ _ _ _).add (integrable_polyErr n β _ _ _ _ _)).add (integrable_polyErr n β _ _ _ _ _)
  have hcore : Integrable (polyCore n) (twistedLaw n β) :=
    ((integrable_polyErr n β _ _ _ _ _).add (integrable_polyErr n β _ _ _ _ _)).add (integrable_polyErr n β _ _ _ _ _)
  have hc : Continuous fun U => |polyR n x U * polyR n y U - 1| :=
    (((continuous_polyR n x).mul (continuous_polyR n y)).sub continuous_const).abs
  have hmono := integral_mono (integrable_law n β hc) (((hcore.const_mul 8).add (hdist x)).add (hdist y))
    (fun U => polyR_pair n x y U)
  refine hmono.trans ?_
  have e : ∫ U, ((fun U => 8 * polyCore n U) + polyDist n x + polyDist n y) U ∂twistedLaw n β =
      8 * ∫ U, polyCore n U ∂twistedLaw n β + ∫ U, polyDist n x U ∂twistedLaw n β + ∫ U, polyDist n y U ∂twistedLaw n β := by
    simp only [Pi.add_apply]
    rw [integral_add_three (hcore.const_mul 8) (hdist x) (hdist y), integral_const_mul]
  rw [e]
  linarith only [polyCore_mean_le n β hβ, polyDist_mean_le n β hβ x, polyDist_mean_le n β hβ y]

/-- A word of winding loops at a list of bases. -/
def polyWord (vs : List V') (U : Configuration V' Q) : ℝ := (vs.map fun v => polyR n v U).prod

theorem polyWord_cons (v : V') (vs : List V') (U : Configuration V' Q) :
    polyWord n (v :: vs) U = polyR n v U * polyWord n vs U := by
  simp [polyWord]

theorem polyWord_append (vs ws : List V') (U : Configuration V' Q) :
    polyWord n (vs ++ ws) U = polyWord n vs U * polyWord n ws U := by
  simp [polyWord]

theorem polyWord_abs_le (vs : List V') (U : Configuration V' Q) : |polyWord n vs U| ≤ 1 := by
  induction vs with
  | nil => simp [polyWord]
  | cons v vs ih =>
    rw [polyWord_cons, abs_mul]
    exact mul_le_one₀ (polyR_abs_le n v U) (abs_nonneg _) ih

theorem continuous_polyWord (vs : List V') : Continuous (polyWord n vs) := by
  induction vs with
  | nil => simpa [polyWord] using continuous_const
  | cons v vs ih =>
    have : polyWord n (v :: vs) = fun U => polyR n v U * polyWord n vs U := funext fun U => polyWord_cons n v vs U
    rw [this]
    exact (continuous_polyR n v).mul ih

theorem polyWord_flip (vs : List V') (U : Configuration V' Q) :
    polyWord n vs (TwistedNeutral.flip4 (2 * n) 3 0 U) = (-1) ^ vs.length * polyWord n vs U := by
  induction vs with
  | nil => simp [polyWord]
  | cons v vs ih =>
    rw [polyWord_cons, polyWord_cons, polyR_flip, ih, List.length_cons, pow_succ]
    ring

/-- **The selection rule, exact at every size and coupling.** A word of odd length in the winding loops has mean zero. -/
theorem polyWord_odd (β : ℝ) {vs : List V'} (h : Odd vs.length) :
    ∫ U, ((polyWord n vs U : ℝ) : ℂ) ∂twistedLaw n β = 0 := by
  refine TwistedNeutral.odd_expectation n _ _ WilsonSingleLinkStaples.character_continuous β 2 3 0 _ fun U => ?_
  rw [polyWord_flip, h.neg_one_pow]
  push_cast
  ring

theorem polyWord_even_mean (β : ℝ) (hβ : 1 / 32 ≤ β) (m : ℕ) (vs : List V') (hvs : vs.length = 2 * m) :
    ∫ U, |polyWord n vs U - 1| ∂twistedLaw n β ≤
      m * (30 * (((2 * n : ℕ) : ℝ) ^ 2 * Real.sqrt (4 * Real.log (SU2GaussianMass.cap (24 * β)) / β))) := by
  haveI : IsProbabilityMeasure (twistedLaw n β) :=
    law_probability n Q (spatialTwist n) character WilsonSingleLinkStaples.character_continuous β 2
  induction m generalizing vs with
  | zero =>
    have hnil : vs = [] := List.length_eq_zero_iff.mp (by simpa using hvs)
    subst hnil
    simp [polyWord]
  | succ m ih =>
    rcases vs with _ | ⟨x, _ | ⟨y, w⟩⟩
    · simp at hvs
    · simp at hvs
      omega
    · have hw : w.length = 2 * m := by
        simp only [List.length_cons] at hvs
        omega
      have hcW : Continuous fun U => |polyWord n w U - 1| := ((continuous_polyWord n w).sub continuous_const).abs
      have hcP : Continuous fun U => |polyR n x U * polyR n y U - 1| :=
        (((continuous_polyR n x).mul (continuous_polyR n y)).sub continuous_const).abs
      have hcL : Continuous fun U => |polyWord n (x :: y :: w) U - 1| :=
        ((continuous_polyWord n _).sub continuous_const).abs
      have hle : ∀ U, |polyWord n (x :: y :: w) U - 1| ≤ |polyR n x U * polyR n y U - 1| + |polyWord n w U - 1| := by
        intro U
        rw [polyWord_cons, polyWord_cons]
        have e : polyR n x U * (polyR n y U * polyWord n w U) - 1 =
            (polyR n x U * polyR n y U - 1) * polyWord n w U + (polyWord n w U - 1) := by ring
        rw [e]
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (polyWord_abs_le n w U)
      have hI := integral_mono (integrable_law n β hcL) ((integrable_law n β hcP).add (integrable_law n β hcW)) hle
      have hS : ∫ U, ((fun U => |polyR n x U * polyR n y U - 1|) + fun U => |polyWord n w U - 1|) U ∂twistedLaw n β =
          ∫ U, |polyR n x U * polyR n y U - 1| ∂twistedLaw n β + ∫ U, |polyWord n w U - 1| ∂twistedLaw n β := by
        simp only [Pi.add_apply]
        exact integral_add (integrable_law n β hcP) (integrable_law n β hcW)
      rw [hS] at hI
      have h₁ := polyR_pair_mean n β hβ x y
      have h₂ := ih w hw
      push_cast at h₁ h₂ ⊢
      linarith only [hI, h₁, h₂]

end Polyakov

section PolyakovLimit
open TwistedFlow TwistedLocalization TwistedRectangle TwistedStability TwistedFlat
open WilsonSingleLinkStaples (Q character character_re)

/-- A physical point, naming the winding loop in direction `3` through it. -/
abbrev PolyLabel := Fin 4 → ℚ

variable (N : ℕ → ℕ) [∀ k, NeZero (N k)]

/-- Winding loops through physical points. They have the physical size of the torus, and are bounded by one. -/
def polyLabels : LabelSystem Q N PolyLabel where
  obs k l U := ((polyR (N k) (site (N k) l) U : ℝ) : ℂ)
  cont k l := Complex.continuous_ofReal.comp (continuous_polyR (N k) _)
  bound _ := 1
  bound_nonneg _ := zero_le_one
  obs_le k l U := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact polyR_abs_le (N k) _ U

/-- A point in the closed lower end of the upper half of the time circle. -/
def PolyPos (l : PolyLabel) : Prop := 0 ≤ l 0 ∧ l 0 < 1 / 2

theorem polyHol_upper (n : ℕ) [NeZero n] (x : Vertex (2 * n)) (hx : (x 0).val ≤ n) :
    UpperLocalC n Q fun U => ((polyR n x U : ℝ) : ℂ) := by
  refine upperLocal_of_closed n Q _ fun U U' h => ?_
  have hrun : ∀ m : ℕ, run (linkValue (2 * n) Q U) 3 x m = run (linkValue (2 * n) Q U') 3 x m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      simp only [run, ih]
      rw [linkValue_eq_linkAt, linkValue_eq_linkAt]
      congr 1
      refine h _ (closed_spatial n _ 3 (by decide) ?_)
      rw [walk_apply_other 3 0 (by decide)]
      exact hx
  change ((polyR n x U : ℝ) : ℂ) = ((polyR n x U' : ℝ) : ℂ)
  unfold polyR polyHol
  rw [hrun]

theorem polyLabels_upper (l : PolyLabel) (hl : PolyPos l) (k : ℕ) :
    UpperLocalC (N k) Q ((polyLabels N).obs k l) :=
  polyHol_upper (N k) _ (site_val_lt (N k) l hl.1 hl.2).le

theorem polyLabels_word (k : ℕ) (a : List PolyLabel) (U : Configuration (Vertex (2 * N k)) Q) :
    word ((polyLabels N).obs k) a U = ((polyWord (N k) (a.map (site (N k))) U : ℝ) : ℂ) := by
  induction a with
  | nil => simp [polyWord]
  | cons l a ih =>
    rw [word_cons, ih, List.map_cons, polyWord_cons]
    push_cast
    rfl

theorem polyWord_reflect (n : ℕ) [NeZero n] (b : List (Vertex (2 * n))) (U : Configuration (Vertex (2 * n)) Q) :
    polyWord n b (reflectConfiguration (2 * n) Q U) = polyWord n (b.map (reflectVertex (2 * n))) U := by
  induction b with
  | nil => simp [polyWord]
  | cons v b ih =>
    rw [polyWord_cons, List.map_cons, polyWord_cons, ih, polyR_reflect]

/-- A reflected entry of winding loops is the mean of one word of winding loops. -/
theorem polyLabels_entry (β : ℕ → ℝ) (k : ℕ) (a b : List PolyLabel) :
    osEntry (polyLabels N) (fun k => spatialTwist (N k)) character β 2 k a b =
      ∫ U, ((polyWord (N k) (a.map (site (N k)) ++ (b.map (site (N k))).map (reflectVertex (2 * N k))) U : ℝ) : ℂ)
        ∂twistedLaw (N k) (β k) := by
  unfold osEntry
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  beta_reduce
  rw [polyLabels_word, polyLabels_word, polyWord_reflect, polyWord_append, Complex.star_def, Complex.conj_ofReal]
  push_cast
  rfl

/-- The limit of the winding loops: one on words of even total length, and zero on words of odd total length. -/
def parityW (p : List PolyLabel × List PolyLabel) : ℂ := if Even (p.1.length + p.2.length) then 1 else 0

variable {β : ℕ → ℝ}

/-- The scale at which loops of the size of the torus are forced to be flat by the proved plaquette bound. -/
def loopScale (k : ℕ) : ℝ :=
  ((2 * N k : ℕ) : ℝ) ^ 2 * Real.sqrt (4 * Real.log (SU2GaussianMass.cap (24 * β k)) / β k)

/-- **The winding loops have a nonconstant limit on the actual law, when `β` is much larger than `N⁴`.** If `β → ∞` and
`(2N)² √(4 log cap(24β)/β) → 0`, the reflected functions of the winding loops converge, whole sequence, to `parityW`. Odd
words vanish at every size and coupling, by the flip. Even words tend to one, because every loop is near a common sign,
by Stokes, the twist and `near_central`. This is the expected limit of a free twisted torus. It does not cover `β ~ log N`. -/
theorem polyakov_os_tendsto (hβ : Tendsto β atTop atTop) (hs : Tendsto (loopScale N (β := β)) atTop (𝓝 0))
    (a b : List PolyLabel) :
    Tendsto (fun k => osEntry (polyLabels N) (fun k => spatialTwist (N k)) character β 2 k a b) atTop
      (𝓝 (parityW (a, b))) := by
  unfold parityW
  dsimp only
  by_cases hev : Even (a.length + b.length)
  · rw [if_pos hev]
    obtain ⟨m, hm⟩ := hev
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : Tendsto (fun k => (m : ℝ) * (30 * loopScale N (β := β) k)) atTop (𝓝 0) := by
      simpa using (hs.const_mul 30).const_mul (m : ℝ)
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
    filter_upwards [hβ.eventually_ge_atTop (1 / 32)] with k hk
    haveI : IsProbabilityMeasure (twistedLaw (N k) (β k)) :=
      law_probability (N k) Q (spatialTwist (N k)) character WilsonSingleLinkStaples.character_continuous (β k) 2
    rw [polyLabels_entry]
    set vs := a.map (site (N k)) ++ (b.map (site (N k))).map (reflectVertex (2 * N k)) with hvs
    have hlen : vs.length = 2 * m := by
      simp only [hvs, List.length_append, List.length_map]
      omega
    have hmean := polyWord_even_mean (N k) (β k) hk m vs hlen
    have hC : Continuous fun U => ((polyWord (N k) vs U : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_polyWord (N k) vs)
    have hi : Integrable (fun U => ((polyWord (N k) vs U : ℝ) : ℂ)) (twistedLaw (N k) (β k)) :=
      hC.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have e : ∫ U, ((polyWord (N k) vs U : ℝ) : ℂ) ∂twistedLaw (N k) (β k) - 1 =
        ∫ U, (((polyWord (N k) vs U - 1 : ℝ)) : ℂ) ∂twistedLaw (N k) (β k) := by
      push_cast
      rw [integral_sub hi (integrable_const _)]
      simp
    rw [e]
    refine (norm_integral_le_integral_norm _).trans ?_
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact hmean
  · rw [if_neg hev]
    refine tendsto_const_nhds.congr fun k => ?_
    rw [polyLabels_entry]
    refine (polyWord_odd (N k) (β k) ?_).symm
    simp only [List.length_append, List.length_map]
    exact Nat.not_even_iff_odd.mp hev

/-- The limit has the whole formal package, with reflection positivity on winding loops at nonnegative times. -/
theorem polyakov_package (hβ : Tendsto β atTop atTop) (hs : Tendsto (loopScale N (β := β)) atTop (𝓝 0)) :
    LimitPackage (polyLabels N) PolyPos parityW := by
  obtain ⟨W, φ, hφ, hW, hP⟩ := exists_limit (polyLabels N) (fun k => spatialTwist (N k)) character β 2
    (fun k => spatialTwist_invariant (N k)) WilsonSingleLinkStaples.character_continuous
    WilsonSingleLinkStaples.character_classFunction WilsonSingleLinkStaples.character_inverse_re PolyPos
    (fun l hl => Eventually.of_forall (polyLabels_upper N l hl))
  have e : W = parityW := by
    funext p
    exact tendsto_nhds_unique (hW p.1 p.2) ((polyakov_os_tendsto N hβ hs p.1 p.2).comp hφ.tendsto_atTop)
  rw [← e]
  exact hP

/-- **A connected separated two-point function that does not vanish, at every separation.** For all labels, and however
far apart: the reflected connected function of two winding loops tends to one. So a nonzero connected separated
two-point function does not by itself mean a nontrivial continuum theory, and item 2 of Target A has to be read on the
neutral sector. This one is long-range order of a `Z₂` sign. -/
theorem polyakov_connected_tendsto (hβ : Tendsto β atTop atTop) (hs : Tendsto (loopScale N (β := β)) atTop (𝓝 0))
    (l l' : PolyLabel) :
    Tendsto (fun k => osEntry (polyLabels N) (fun k => spatialTwist (N k)) character β 2 k [l] [l'] -
      osEntry (polyLabels N) (fun k => spatialTwist (N k)) character β 2 k [l] [] *
        osEntry (polyLabels N) (fun k => spatialTwist (N k)) character β 2 k [] [l']) atTop (𝓝 1) := by
  have h := (polyakov_os_tendsto N hβ hs [l] [l']).sub
    ((polyakov_os_tendsto N hβ hs [l] []).mul (polyakov_os_tendsto N hβ hs [] [l']))
  simpa [parityW] using h

/-- The limit is not constant: it separates the empty word from one loop. So its Gram form has rank at least two, while
the plaquette limits of `constant_gram` have rank one. -/
theorem parityW_separates (l l' : PolyLabel) :
    parityW ([], []) = 1 ∧ parityW ([l], []) = 0 ∧ parityW ([], [l']) = 0 ∧ parityW ([l], [l']) = 1 := by
  simp [parityW]

/-- Its Gram form has rank exactly two: one square for the even part of the coefficient vector, and one for the odd
part. -/
theorem parityW_gram {J : Type*} [DecidableEq J] (s : Finset J) (w : J → List PolyLabel) (e : J → ℂ) :
    ∑ i ∈ s, ∑ j ∈ s, star (e i) * e j * parityW (w i, w j) =
      star (∑ j ∈ s.filter (fun j => Even (w j).length), e j) * (∑ j ∈ s.filter (fun j => Even (w j).length), e j) +
      star (∑ j ∈ s.filter (fun j => ¬ Even (w j).length), e j) * (∑ j ∈ s.filter (fun j => ¬ Even (w j).length), e j) := by
  classical
  rw [star_sum, star_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_filter, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_filter, Finset.sum_filter]
  by_cases hi : Even (w i).length
  · simp only [hi, not_true_eq_false, if_true, if_false, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : Even (w j).length
    · simp [parityW, hi, hj, Nat.even_add]
    · simp [parityW, hi, hj, Nat.even_add]
  · simp only [hi, not_false_eq_true, if_true, if_false, zero_add]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : Even (w j).length
    · simp [parityW, hi, hj, Nat.even_add]
    · simp [parityW, hi, hj, Nat.even_add]

/-- On the flip-even words the limit is the constant one. So in this family the whole nonconstant part is the sign,
and flip-even functions of winding loops are connected-trivial in this regime. -/
theorem parityW_even {a b : List PolyLabel} (ha : Even a.length) (hb : Even b.length) : parityW (a, b) = 1 := by
  simp [parityW, Nat.even_add, ha, hb]

/-- The hypothesis of the winding limit is met on every sequence of sizes, for `β` large enough at each size. -/
theorem exists_loop_trajectory :
    ∃ β : ℕ → ℝ, Tendsto β atTop atTop ∧ Tendsto (loopScale N (β := β)) atTop (𝓝 0) := by
  have hC : Tendsto (fun b : ℝ => Real.sqrt (4 * Real.log (SU2GaussianMass.cap (24 * b)) / b)) atTop (𝓝 0) := by
    have h₀ := (log_cap_div_tendsto.const_mul (4 : ℝ))
    simp only [mul_zero] at h₀
    have h₁ : Tendsto (fun b : ℝ => 4 * Real.log (SU2GaussianMass.cap (24 * b)) / b) atTop (𝓝 0) :=
      h₀.congr fun b => by ring
    simpa using h₁.sqrt
  have hex (k : ℕ) : ∃ b : ℝ, (k : ℝ) ≤ b ∧ ((2 * N k : ℕ) : ℝ) ^ 2 *
      Real.sqrt (4 * Real.log (SU2GaussianMass.cap (24 * b)) / b) ≤ 1 / ((k : ℝ) + 1) := by
    have hk : Tendsto (fun b : ℝ => ((2 * N k : ℕ) : ℝ) ^ 2 *
        Real.sqrt (4 * Real.log (SU2GaussianMass.cap (24 * b)) / b)) atTop (𝓝 0) := by
      simpa using hC.const_mul (((2 * N k : ℕ) : ℝ) ^ 2)
    have hev := hk.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1)))
    obtain ⟨b, hb₁, hb₂⟩ := (hev.and (eventually_ge_atTop (k : ℝ))).exists
    exact ⟨b, hb₂, hb₁⟩
  choose b hb₁ hb₂ using hex
  refine ⟨b, tendsto_atTop_mono hb₁ tendsto_natCast_atTop_atTop, ?_⟩
  refine squeeze_zero (fun k => ?_) hb₂ tendsto_one_div_add_atTop_nhds_zero_nat
  unfold loopScale
  positivity

end PolyakovLimit

/-! ### Physical-size contractible loops: the family on which nontriviality is open

Rectangles of physical size, with the sign of the twist they enclose, carried on one time slice by slice flow. They are
bounded, so compactness is free. They are half-supported, so reflection positivity is exact. They do not change under slab
flips except when wrapping, so they are not the winding sign of the last section. On trajectories with `β ≫ N⁴ log N` they
collapse too, because Stokes bounds the rectangle by the sum of the defects it encloses. Elsewhere, including the
trajectories of Target A, the bound is empty, and nothing is known. `SliceLoopConnected` names this open statement, and it is
assumed nowhere. Translation covariance of rectangles, which needs Stokes for the compensating signs, is not proved. -/

section Rectangles
open TwistedFlow TwistedLocalization TwistedRectangle TwistedStability TwistedFlat
open WilsonSingleLinkStaples (Q character character_re)
open scoped Quaternion

variable (n : ℕ) [NeZero n]
local notation "V'" => Vertex (2 * n)

/-- The holonomy around a rectangle of sides `a, b` in the plane `μ, ν`. -/
def rectHol (L : V' → Fin 4 → Q) (μ ν : Fin 4) (x : V') (a b : ℕ) : Q :=
  (run L μ x a * run L ν (walk μ x a) b) * (run L ν x b * run L μ (walk ν x b) a)⁻¹

/-- The number of twisted plaquettes inside a rectangle. -/
def rectExp (μ ν : Fin 4) (x : V') (a b : ℕ) : ℕ :=
  ∑ j ∈ Finset.range b, ∑ i ∈ Finset.range a, twistExp (N := 2 * n) μ ν (walk μ (walk ν x j) i)

/-- The rectangle with the sign of the twist it encloses, as a trace. It is `2` on a flat twisted field. -/
def rectObs (μ ν : Fin 4) (x : V') (a b : ℕ) (U : Configuration V' Q) : ℝ :=
  (-1) ^ rectExp n μ ν x a b * (2 * ((rectHol n (linkValue (2 * n) Q U) μ ν x a b : Q) : ℍ[ℝ]).re)

theorem re_ω_pow (k : ℕ) : (((ω ^ k : Q) : ℍ[ℝ])).re = (-1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : ((ω ^ (k + 1) : Q) : ℍ[ℝ]) = ((ω ^ k : Q) : ℍ[ℝ]) * ((ω : Q) : ℍ[ℝ]) := by
      rw [pow_succ]
      rfl
    rw [e, ω_coe, pow_succ, ← ih]
    simp

theorem neg_one_pow_abs (k : ℕ) : |((-1 : ℝ) ^ k)| = 1 := by simp

theorem continuous_rectHol (μ ν : Fin 4) (x : V') (a b : ℕ) :
    Continuous fun U : Configuration V' Q => rectHol n (linkValue (2 * n) Q U) μ ν x a b :=
  ((continuous_run n μ x a).mul (continuous_run n ν _ b)).mul
    ((continuous_run n ν x b).mul (continuous_run n μ _ a)).inv

theorem continuous_rectObs (μ ν : Fin 4) (x : V') (a b : ℕ) : Continuous (rectObs n μ ν x a b) :=
  continuous_const.mul (continuous_const.mul
    (Quaternion.continuous_re.comp (continuous_subtype_val.comp (continuous_rectHol n μ ν x a b))))

theorem rectObs_abs_le (μ ν : Fin 4) (x : V') (a b : ℕ) (U : Configuration V' Q) : |rectObs n μ ν x a b U| ≤ 2 := by
  unfold rectObs
  rw [abs_mul, neg_one_pow_abs, one_mul, abs_mul]
  have := TwistedFlat.re_le_one (rectHol n (linkValue (2 * n) Q U) μ ν x a b)
  norm_num
  linarith only [this]

/-- **Stokes for a rectangle.** The rectangle differs from its flat value by at most twice the defects it encloses. -/
theorem rectObs_sub_le (μ ν : Fin 4) (x : V') (a b : ℕ) (U : Configuration V' Q) :
    |rectObs n μ ν x a b U - 2| ≤ 2 * polyErr n μ ν x a b U := by
  set L := linkValue (2 * n) Q U with hL
  have h := rectangle_error L μ ν (twistExp μ ν) (TwistedStability.defect L μ ν)
    (fun y => cell_of_defect _ _ _ _ _ _ le_rfl) x a b
  set A := run L μ x a * run L ν (walk μ x a) b with hA
  set B := run L ν x b * run L μ (walk ν x b) a with hB
  have hE : (∑ j ∈ Finset.range b, ∑ i ∈ Finset.range a, twistExp (N := 2 * n) μ ν (walk μ (walk ν x j) i)) =
      rectExp n μ ν x a b := rfl
  rw [hE] at h
  set E := rectExp n μ ν x a b with hEd
  have h₁ : TwistedStability.d (A * B⁻¹) (ω ^ E) ≤ polyErr n μ ν x a b U := by
    have e := TwistedStability.d_mul_right B⁻¹ A (ω ^ E * B)
    have e₂ : ω ^ E * B * B⁻¹ = ω ^ E := by group
    rw [e₂] at e
    rw [e]
    exact h
  have h₂ := (TwistedSliceLift.abs_re_sub_le (A * B⁻¹) (ω ^ E)).trans h₁
  rw [re_ω_pow] at h₂
  have hhol : rectHol n L μ ν x a b = A * B⁻¹ := rfl
  have hs : ((-1 : ℝ) ^ E) * (-1) ^ E = 1 := by
    rw [← mul_pow]
    simp
  unfold rectObs
  rw [← hL, hhol, ← hEd]
  have e : (-1 : ℝ) ^ E * (2 * ((A * B⁻¹ : Q) : ℍ[ℝ]).re) - 2 =
      (-1) ^ E * (2 * (((A * B⁻¹ : Q) : ℍ[ℝ]).re - (-1) ^ E)) := by
    linear_combination 2 * hs
  rw [e, abs_mul, neg_one_pow_abs, one_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith only [h₂]

end Rectangles

section RectangleLimit
open TwistedFlow TwistedLocalization
open WilsonSingleLinkStaples (Q character character_re)

/-- A physical rectangle: a base point, a plane and two rational sides. -/
abbrev LoopLabel := (Fin 4 → ℚ) × Plane × ℚ × ℚ

/-- A physical length in lattice units, at most once around the torus. -/
def side (m : ℕ) (r : ℚ) : ℕ := min (2 * m) ⌊r * ((2 * m : ℕ) : ℚ)⌋₊

theorem side_le (m : ℕ) (r : ℚ) : side m r ≤ 2 * m := min_le_left _ _

variable (N : ℕ → ℕ) [∀ k, NeZero (N k)] (t : ℕ → ℝ)

/-- The physical rectangle on the `k`-th lattice. -/
def loopObs (k : ℕ) (l : LoopLabel) (V : Configuration (Vertex (2 * N k)) Q) : ℝ :=
  rectObs (N k) l.2.1.1.1 l.2.1.1.2 (site (N k) l.1) (side (N k) l.2.2.1) (side (N k) l.2.2.2) V

/-- Physical rectangles, flowed in their own time slice. A label is the data of the rectangle, and any plane is allowed
as a label, but only spatial planes lie in one slice before the flow. -/
def sliceLoopLabels : LabelSystem Q N LoopLabel where
  obs k l U := ((loopObs N k l (wf (N k) (t k) (staticCfg (N k) (site (N k) l.1 0) U)) : ℝ) : ℂ)
  cont k l := Complex.continuous_ofReal.comp ((continuous_rectObs (N k) _ _ _ _ _).comp
    ((continuous_wf_right (N k) (t k)).comp (staticCfg_continuous (N k) _)))
  bound _ := 2
  bound_nonneg _ := by norm_num
  obs_le k l U := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact rectObs_abs_le (N k) _ _ _ _ _ _

/-- A rectangle whose base time lies in the closed lower end of the upper half. -/
def LoopPos (l : LoopLabel) : Prop := 0 ≤ l.1 0 ∧ l.1 0 < 1 / 2

/-- **Physical rectangles have the formal package at every trajectory, with exact reflection positivity.** -/
theorem sliceLoop_limit_exists (β : ℕ → ℝ) :
    ∃ (W : List LoopLabel × List LoopLabel → ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ a b, Tendsto (fun k => osEntry (sliceLoopLabels N t) (fun k => spatialTwist (N k)) character β 2 (φ k) a b)
        atTop (𝓝 (W (a, b)))) ∧
      LimitPackage (sliceLoopLabels N t) LoopPos W :=
  exists_limit _ _ character β 2 (fun k => spatialTwist_invariant (N k))
    WilsonSingleLinkStaples.character_continuous WilsonSingleLinkStaples.character_classFunction
    WilsonSingleLinkStaples.character_inverse_re LoopPos
    (fun l hl => Eventually.of_forall fun k => static_upper (N k) (site (N k) l.1 0)
      (site_val_lt (N k) l.1 hl.1 hl.2).le fun V => ((loopObs N k l (wf (N k) (t k) V) : ℝ) : ℂ))

variable {β : ℕ → ℝ}

/-- **Physical rectangles collapse when `β ≫ N⁴ log N`**, at any flow times. The proved plaquette bound reaches physical
size only here, because the Stokes bound is the area times the mean defect. Below this scale the bound is empty, and
the behaviour of these functions is open. -/
theorem sliceLoop_os_tendsto (hβ : Tendsto β atTop atTop) (ht : ∀ k, 0 ≤ t k)
    (hs : Tendsto (loopScale N (β := β)) atTop (𝓝 0)) (a b : List LoopLabel) :
    Tendsto (fun k => osEntry (sliceLoopLabels N t) (fun k => spatialTwist (N k)) character β 2 k a b) atTop
      (𝓝 (((2 : ℝ) : ℂ) ^ (a.length + b.length))) := by
  refine os_tendsto_of_mean N (sliceLoopLabels N t) (fun k l U => (sliceLoopLabels N t).obs_le k l U) (fun l => ?_) a b
  have hb : Tendsto (fun k => 2 * loopScale N (β := β) k) atTop (𝓝 0) := by
    simpa using hs.const_mul 2
  refine squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => norm_nonneg _) ?_ hb
  filter_upwards [hβ.eventually_ge_atTop (1 / 32)] with k hk
  set T : Configuration (Vertex (2 * N k)) Q → Configuration (Vertex (2 * N k)) Q :=
    fun U => wf (N k) (t k) (staticCfg (N k) (site (N k) l.1 0) U) with hT
  have hTc : Continuous T := (continuous_wf_right (N k) (t k)).comp (staticCfg_continuous (N k) _)
  by_cases hlt : l.2.1.1.1 < l.2.1.1.2
  · have hE := polyErr_mean_of (N k) (β k) T hTc hlt (C := 4 * Real.log (SU2GaussianMass.cap (24 * β k)) / β k)
      (fun y => slice_term_mean (N k) (β k) _ (ht k) hk _) (site (N k) l.1)
      (side (N k) l.2.2.1) (side (N k) l.2.2.2) (side_le _ _) (side_le _ _)
    have hci : Integrable (fun U => polyErr (N k) l.2.1.1.1 l.2.1.1.2 (site (N k) l.1) (side (N k) l.2.2.1)
        (side (N k) l.2.2.2) (T U)) (twistedLaw (N k) (β k)) :=
      integrable_law (N k) (β k) (continuous_finset_sum _ fun j _ => continuous_finset_sum _ fun i _ =>
        (continuous_defect (N k) _ _ _).comp hTc)
    have hcl : Continuous fun U => ‖(sliceLoopLabels N t).obs k l U - ((2 : ℝ) : ℂ)‖ :=
      (((sliceLoopLabels N t).cont k l).sub continuous_const).norm
    refine (integral_mono (integrable_law (N k) (β k) hcl) (hci.const_mul 2) fun U => ?_).trans ?_
    · change ‖((loopObs N k l (T U) : ℝ) : ℂ) - ((2 : ℝ) : ℂ)‖ ≤ _
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact rectObs_sub_le (N k) _ _ _ _ _ _
    · rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hE (by norm_num)
  · exact absurd l.2.1.2 hlt

/-- **The open statement.** On a trajectory of sizes, flow times and couplings, some subsequential limit of slice-flowed
physical rectangles has a nonzero connected reflected two-point function. This is a form of item 2 of Target A in which
neither the winding sign nor a plaquette can do the work. It is open at `β ~ log N`. It is assumed nowhere. -/
def SliceLoopConnected (β : ℕ → ℝ) : Prop :=
  ∃ (W : List LoopLabel × List LoopLabel → ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
    (∀ a b, Tendsto (fun k => osEntry (sliceLoopLabels N t) (fun k => spatialTwist (N k)) character β 2 (φ k) a b)
      atTop (𝓝 (W (a, b)))) ∧
    ∃ l l', W ([l], [l']) ≠ W ([l], []) * W ([], [l'])

/-- It is false on the trajectories where the Stokes bound reaches physical size. -/
theorem not_sliceLoopConnected (hβ : Tendsto β atTop atTop) (ht : ∀ k, 0 ≤ t k)
    (hs : Tendsto (loopScale N (β := β)) atTop (𝓝 0)) : ¬ SliceLoopConnected N t β := by
  rintro ⟨W, φ, hφ, hW, l, l', hne⟩
  have e (p : List LoopLabel × List LoopLabel) : W p = ((2 : ℝ) : ℂ) ^ (p.1.length + p.2.length) :=
    tendsto_nhds_unique (hW p.1 p.2) ((sliceLoop_os_tendsto N t hβ ht hs p.1 p.2).comp hφ.tendsto_atTop)
  apply hne
  rw [e, e, e]
  simp [pow_two]

end RectangleLimit

/-! ### Other compact groups -/

section Groups

/-- A sign twist realized by a central element multiplies the representation by `-1`. A group with trivial center
has none unless the character vanishes. So `G₂`, `F₄` and `E₈` admit no center twist. A real sign on a stack of
plaquettes can still be written, and `exists_limit` accepts it, but it is then a defect in the action and not a
choice of bundle, and it does not have translation invariance up to a change of variables. -/
theorem no_sign_twist_of_trivial_center {G : Type*} [Group G] (hc : Subgroup.center G = ⊥) (χ : G → ℂ)
    (ζ : G) (hζ : ζ ∈ Subgroup.center G) (h : ∀ g, χ (ζ * g) = -χ g) (g : G) : χ g = 0 := by
  have h1 : ζ = 1 := by
    rw [hc] at hζ
    exact Subgroup.mem_bot.mp hζ
  have := h g
  rw [h1, one_mul] at this
  have h2 : (2 : ℂ) * χ g = 0 := by
    linear_combination this
  simpa using h2

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (N : ℕ → ℕ) [∀ k, NeZero (N k)]

/-- The whole package exists for every compact group, with no use of `SU(2)`. It says nothing about that group's
Yang-Mills theory. -/
theorem physical_limit_exists (hN : Tendsto N atTop atTop) (χ : G → ℂ) (hcχ : Continuous χ) (hχ : ClassFunction G χ)
    (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ g, ‖χ g‖ ≤ B) (β : ℕ → ℝ) (c : ℝ) :
    ∃ (W : List PhysLabel × List PhysLabel → ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ a b, Tendsto (fun k => osEntry (physLabels G N χ hcχ B hB0 hB) (fun k => spatialTwist (N k)) χ β c (φ k) a b)
        atTop (𝓝 (W (a, b)))) ∧
      LimitPackage (physLabels G N χ hcχ B hB0 hB) PosLabel W :=
  exists_limit _ _ χ β c (fun k => spatialTwist_invariant (N k)) hcχ hχ hinv PosLabel
    (fun l hl => physLabels_upper G N hN χ hcχ B hB0 hB l hl)

end Groups

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedLimit
