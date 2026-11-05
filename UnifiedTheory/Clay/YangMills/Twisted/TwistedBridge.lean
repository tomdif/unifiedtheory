/- A finite-box mixing criterion for finite-volume lattice laws, what it implies, where it holds, and a proof that the
links at a vertex cannot satisfy it at weak coupling, even when tested only on gauge-invariant observables.

**The criterion** (`BoxCriterionOn 𝓐`, and `BoxCriterion` for `𝓐` all continuous functions). Blocks `b k` of
coordinates carry influence coefficients `κ k j i`: changing one boundary coordinate `j` of a block moves the
expectation of an observable of the class `𝓐`, with the exterior frozen, by at most `∑ i, κ k j i * d i`, with `d` its
coordinate oscillations (`BlockInfluenceOn`). Blocks of one colour share no factor. Every coordinate has margin
`∑_{k ∋ i} (1 - ∑_j κ k j i) ≥ ε`. `fiber_congr` shows the two conditional laws involved depend on the outside only
through the box boundary.

**The criterion has no size constraint.** The whole lattice as one block satisfies it at every coupling (`whole_box`),
with rate `0` and empty conclusions. It is not, by itself, a statement about small boxes. Uniformity in the volume
has content only for a block family, a number of colours and a margin held fixed as the lattice grows.

**Proved from the criterion, for any finite family of local factors on a product of compact spaces and any class of
observables that box updates map to itself** (`Stable`): contraction of the total oscillation at rate `1 - ε/C`, with
`C` colours (`budget`, `iterate_osc`, `mixing`); exponential clustering with a constant depending only on the size of
a support (`covariance_decay_local`); and `ε Var(F) ≤ ∑_c E[(F - E_c F)²]` (`poincare`). The new input is `E_union`:
non-interacting boxes are conditionally independent. Dynamics here are auxiliary. Nothing identifies them with
physical time, and nothing here concerns the transfer operator. The gauge-invariant observables form such a class
(`gaugeClass_stable`).

**Proved to hold at strong coupling for the actual twisted law** (`twisted_criterion`): for every covering box
family of size at most `m`, when `36 β m < 1`, with margin `1 - 36 β m`. For the links at a vertex and colours
mod 4 this gives clustering in the torus distance (`twisted_law_covariance`) and a Poincaré inequality
(`twisted_poincare`) for `β < 1/288`, when `4` divides the side `2n`, at rates free of `n`. The estimate is crude,
since it charges the whole box for each boundary coordinate, and its range is smaller than the single-link
`β < 1/36` known for the untwisted law.

**Proved to fail at weak coupling for the links at a vertex** (`star_margin_of_expectation`, `star_no_go`,
`star_no_go_gauge`, `star_no_go_on`, `exists_threshold`): at every coupling the margin is at most `2 - 4 w`, with `w` a
lower bound for the expectation of the closed rectangles at flat boundary condition, and for all large `β`, on every
lattice of side `2n ≥ 4`, no coefficients and no colouring satisfy the criterion with `ε ≥ 0`, on any class containing
the closed rectangles `loopObs`, in particular on the gauge-invariant observables. The reason is exact (`loop_cross_bound`). A center flip of the links of the box and its
boundary only (`tflip`) preserves the plaquettes touching the box and reverses a straight line through it. The line
closes into a contractible rectangle whose other links do not meet the box or its boundary, so the rectangle is
reversed and sees the changed boundary links only through the conditional law. So the influence of those boundary
links on the line is at least the conditional expectation of the rectangle, at every coupling. Four disjoint boundary
sets each carry that much, while the margin allows only two (`row_lower`, `star_margin`). The flip is not a gauge
transformation: it leaves defects on plaquettes away from the box, which the conditional law does not see.

**Not proved.** This says nothing about whether the twisted law mixes at weak coupling. Only this criterion fails, and
only for this block family and for classes containing the rectangles. A class avoiding them is not treated. The
rectangle is a bare lattice observable, so the size of `w` reflects a lattice self-energy and is not by itself a
physical scale. Boxes other than the links at a vertex are not treated in the no-go, and the criterion for a larger fixed family at weak
coupling is not established or excluded. No statement here is uniform in `β` near the physical trajectory, and no
bridge from small to large volume follows. Identification of the box laws across lattice sizes is not formalized
beyond `fiber_congr`. -/
import UnifiedTheory.Clay.YangMills.FiniteFactorContraction
import UnifiedTheory.Clay.YangMills.CompactGibbsOscillation
import UnifiedTheory.Clay.YangMills.ContinuousUpdateGap
import UnifiedTheory.Clay.YangMills.Twisted.TwistedLocalization
import UnifiedTheory.Clay.YangMills.WilsonCoordinateLaw
import UnifiedTheory.Clay.YangMills.WilsonInfluenceGeometry
import UnifiedTheory.Clay.YangMills.WilsonSlabBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedBridge
noncomputable section
open MeasureTheory FiniteProductInfluence CompactGibbsBlockFiber CompactGibbsBlockUpdate
open FiniteFactorConditional (action action_continuous)
open FiniteFactorParallelKernel (actionMap)

/-! ### Box geometry -/
section Geometry
variable {I P : Type*} [Fintype P] [DecidableEq I]

/-- The coordinates outside `S` that share a factor with `S`: the boundary of the box. -/
def nbr (D : P → Finset I) (S : Finset I) : Finset I :=
  ((Finset.univ.filter fun p => ¬ Disjoint (D p) S).biUnion D) \ S

theorem mem_nbr (D : P → Finset I) (S : Finset I) (j : I) :
    j ∈ nbr D S ↔ j ∉ S ∧ ∃ p, j ∈ D p ∧ ¬ Disjoint (D p) S := by
  simp only [nbr, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨⟨p, hp, hj⟩, hS⟩
    exact ⟨hS, p, hj, hp⟩
  · rintro ⟨hS, p, hj, hp⟩
    exact ⟨⟨p, hp, hj⟩, hS⟩

/-- Two boxes are non-interacting if they are disjoint and no factor touches both. -/
def NonInteract (D : P → Finset I) (S T : Finset I) : Prop :=
  Disjoint S T ∧ ∀ p, Disjoint (D p) S ∨ Disjoint (D p) T

theorem NonInteract.symm {D : P → Finset I} {S T : Finset I} (h : NonInteract D S T) :
    NonInteract D T S :=
  ⟨h.1.symm, fun p => (h.2 p).symm⟩

theorem NonInteract.nbr_disjoint {D : P → Finset I} {S T : Finset I} (h : NonInteract D S T) :
    Disjoint (nbr D S) T := by
  rw [Finset.disjoint_left]
  intro j hj hjT
  obtain ⟨-, p, hjp, hp⟩ := (mem_nbr D S j).1 hj
  rcases h.2 p with h' | h'
  · exact hp h'
  · exact Finset.disjoint_left.1 h' hjp hjT

end Geometry

/-! ### The conditional law of a box -/
section Fiber
variable {I P X : Type*} [Fintype I] [Fintype P] [DecidableEq I]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]
  (D : P → Finset I) (Φ : P → (I → X) → ℝ) (hΦc : ∀ p, Continuous (Φ p))

/-- The conditional law of the box `S` with boundary condition `U`, in auxiliary full coordinates. -/
def fiber (S : Finset I) (U : I → X) : Measure (I → X) :=
  CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ))
    (fun V => actionMap Φ hΦc (overwrite S U V))

instance fiber_probability (S : Finset I) (U : I → X) :
    IsProbabilityMeasure (fiber μ Φ hΦc S U) :=
  CompactGibbsContinuity.law_probability _ _
    ((actionMap Φ hΦc).continuous.comp (overwrite S U).continuous)

/-- The conditional-expectation operator of the box, as an actual continuous map. -/
abbrev E (S : Finset I) (F : C(I → X, ℝ)) : C(I → X, ℝ) := blockAverage μ (actionMap Φ hΦc) S F

theorem E_apply (S : Finset I) (F : C(I → X, ℝ)) (U : I → X) :
    E μ Φ hΦc S F U = ∫ V, F (overwrite S U V) ∂fiber μ Φ hΦc S U :=
  blockAverage_full_fiber μ _ S F U

theorem overwrite_apply (S : Finset I) (U V : I → X) (i : I) :
    overwrite S U V i = if i ∈ S then V i else U i := rfl

variable {D Φ} (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
include hΦ

/-- The conditional law of a box depends on the exterior only through its boundary. -/
theorem fiber_congr (S : Finset I) (x y : I → X) (hxy : ∀ i ∈ nbr D S, x i = y i) :
    fiber μ Φ hΦc S x = fiber μ Φ hΦc S y := by
  classical
  let c : ℝ := ∑ p, if Disjoint (D p) S then Φ p x - Φ p y else 0
  have hstep (V : I → X) (p : P) : Φ p (overwrite S x V) =
      (if Disjoint (D p) S then Φ p x - Φ p y else 0) + Φ p (overwrite S y V) := by
    by_cases hp : Disjoint (D p) S
    · have h1 : Φ p (overwrite S x V) = Φ p x := hΦ p (fun i hi => by
        have : i ∉ S := Finset.disjoint_left.1 hp hi
        simp [overwrite_apply, this])
      have h2 : Φ p (overwrite S y V) = Φ p y := hΦ p (fun i hi => by
        have : i ∉ S := Finset.disjoint_left.1 hp hi
        simp [overwrite_apply, this])
      rw [h1, h2, if_pos hp]
      ring
    · rw [if_neg hp, zero_add]
      refine hΦ p (fun i hi => ?_)
      by_cases hS : i ∈ S
      · simp [overwrite_apply, hS]
      · have : i ∈ nbr D S := (mem_nbr D S i).2 ⟨hS, p, hi, hp⟩
        simp [overwrite_apply, hS, hxy i this]
  have hall (V : I → X) : actionMap Φ hΦc (overwrite S x V) =
      c + actionMap Φ hΦc (overwrite S y V) := by
    change action Φ _ = c + action Φ _
    simp only [action, c, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p _ => hstep V p)
  unfold fiber
  rw [funext hall]
  exact GibbsConstantShift.law_const_add _ _
    ((actionMap Φ hΦc).continuous.comp (overwrite S y).continuous) c

omit hΦ in
/-- An observable that does not see the box is fixed by the box update. -/
theorem E_of_outside (S : Finset I) (F : C(I → X, ℝ))
    (hF : ∀ x y : I → X, (∀ i, i ∉ S → x i = y i) → F x = F y) (U : I → X) :
    E μ Φ hΦc S F U = F U := by
  rw [E_apply]
  have h (V : I → X) : F (overwrite S U V) = F U := hF _ _ (fun i hi => by
    simp [overwrite_apply, hi])
  simp [h]

/-- The box update of a local observable is local. -/
theorem E_depends (S A : Finset I) (F : C(I → X, ℝ)) (hF : DependsOn (F : (I → X) → ℝ) (A : Set I))
    (x y : I → X) (hxy : ∀ i ∈ (A \ S) ∪ nbr D S, x i = y i) :
    E μ Φ hΦc S F x = E μ Φ hΦc S F y := by
  rw [E_apply, E_apply, fiber_congr μ hΦc hΦ S x y
    (fun i hi => hxy i (Finset.mem_union_right _ hi))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  refine hF (fun i hi => ?_)
  by_cases hS : i ∈ S
  · simp [overwrite_apply, hS]
  · have : i ∈ (A \ S) ∪ nbr D S :=
      Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨by exact_mod_cast hi, hS⟩)
    simp [overwrite_apply, hS, hxy i this]

end Fiber

/-! ### Non-interacting boxes factorize -/
section Union
variable {I P X : Type*} [Fintype I] [Fintype P] [DecidableEq I]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- Taking the box coordinates from one independent sample and the rest from another gives a sample. -/
theorem mix_integral (S : Finset I) (H : C(I → X, ℝ)) :
    (∫ Y, H Y ∂Measure.pi (fun _ : I => μ)) =
      ∫ V, ∫ W, H (overwrite S W V) ∂Measure.pi (fun _ : I => μ)
        ∂Measure.pi (fun _ : I => μ) := by
  classical
  set π := Measure.pi (fun _ : I => μ) with hπ
  let M : (I → X) × (I → X) → (I → X) := fun z => overwrite S z.2 z.1
  have hM : Measurable M := by
    refine measurable_pi_iff.2 fun i => ?_
    by_cases hi : i ∈ S
    · simpa [M, overwrite_apply, hi] using (measurable_pi_apply i).comp measurable_fst
    · simpa [M, overwrite_apply, hi] using (measurable_pi_apply i).comp measurable_snd
  have hmap : (π.prod π).map M = π := by
    symm
    refine Measure.pi_eq fun s hs => ?_
    have hset : Set.pi Set.univ s ∈ {t | MeasurableSet t} :=
      MeasurableSet.univ_pi hs
    rw [Measure.map_apply hM hset]
    have hpre : M ⁻¹' Set.pi Set.univ s =
        (Set.pi Set.univ fun i => if i ∈ S then s i else Set.univ) ×ˢ
          (Set.pi Set.univ fun i => if i ∈ S then Set.univ else s i) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_prod, M,
        overwrite_apply]
      constructor
      · intro h
        refine ⟨fun i => ?_, fun i => ?_⟩
        · by_cases hi : i ∈ S
          · simpa [hi] using h i
          · simp [hi]
        · by_cases hi : i ∈ S
          · simp [hi]
          · simpa [hi] using h i
      · rintro ⟨h1, h2⟩ i
        by_cases hi : i ∈ S
        · simpa [hi] using h1 i
        · simpa [hi] using h2 i
    rw [hpre, Measure.prod_prod, hπ, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : i ∈ S <;> simp [hi]
  have he : (∫ Y, H Y ∂π) = ∫ z, H (M z) ∂π.prod π := by
    conv_lhs => rw [← hmap]
    exact integral_map hM.aemeasurable H.continuous.aestronglyMeasurable
  rw [he]
  refine integral_prod (μ := π) (ν := π) (fun z : (I → X) × (I → X) => H (M z)) ?_
  have hc : Continuous fun z : (I → X) × (I → X) => H (M z) := by
    refine H.continuous.comp (continuous_pi fun i => ?_)
    by_cases hi : i ∈ S
    · simpa [M, overwrite_apply, hi] using (continuous_apply i).comp continuous_fst
    · simpa [M, overwrite_apply, hi] using (continuous_apply i).comp continuous_snd
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

variable {D : P → Finset I} {Φ : P → (I → X) → ℝ} (hΦc : ∀ p, Continuous (Φ p))
  (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
include hΦ

/-- **Non-interacting boxes are conditionally independent.** The update of the union is the
composition of the updates. -/
theorem E_union (S T : Finset I) (hST : NonInteract D S T) (F : C(I → X, ℝ)) (U : I → X) :
    E μ Φ hΦc (S ∪ T) F U = E μ Φ hΦc S (E μ Φ hΦc T F) U := by
  classical
  set π := Measure.pi (fun _ : I => μ) with hπ
  let A := actionMap Φ hΦc
  have hAc : Continuous A := A.continuous
  -- the mixed coordinates
  have hov (V W : I → X) : overwrite (S ∪ T) U (overwrite S W V) =
      overwrite T (overwrite S U V) W := by
    funext i
    by_cases hS : i ∈ S
    · have hT : i ∉ T := Finset.disjoint_left.1 hST.1 hS
      simp [overwrite_apply, hS, hT]
    · by_cases hT : i ∈ T <;> simp [overwrite_apply, hS, hT]
  -- the action splits
  have hfac (V W : I → X) (p : P) :
      Φ p (overwrite T (overwrite S U V) W) =
        Φ p (overwrite S U V) + Φ p (overwrite T U W) - Φ p U := by
    rcases hST.2 p with hp | hp
    · have h1 : Φ p (overwrite T (overwrite S U V) W) = Φ p (overwrite T U W) :=
        hΦ p (fun i hi => by
          have : i ∉ S := Finset.disjoint_left.1 hp hi
          by_cases hT : i ∈ T <;> simp [overwrite_apply, hT, this])
      have h2 : Φ p (overwrite S U V) = Φ p U := hΦ p (fun i hi => by
        have : i ∉ S := Finset.disjoint_left.1 hp hi
        simp [overwrite_apply, this])
      rw [h1, h2]
      ring
    · have h1 : Φ p (overwrite T (overwrite S U V) W) = Φ p (overwrite S U V) :=
        hΦ p (fun i hi => by
          have : i ∉ T := Finset.disjoint_left.1 hp hi
          simp [overwrite_apply, this])
      have h2 : Φ p (overwrite T U W) = Φ p U := hΦ p (fun i hi => by
        have : i ∉ T := Finset.disjoint_left.1 hp hi
        simp [overwrite_apply, this])
      rw [h1, h2]
      ring
  have hact (V W : I → X) : A (overwrite T (overwrite S U V) W) =
      A (overwrite S U V) + A (overwrite T U W) - A U := by
    change action Φ _ = action Φ _ + action Φ _ - action Φ _
    simp only [action, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun p _ => hfac V W p)
  have hexp (R : Finset I) (W : I → X) (G : (I → X) → ℝ) :
      (∫ V, G V ∂fiber μ Φ hΦc R W) =
        (∫ V, Real.exp (-A (overwrite R W V)) * G V ∂π) /
          (∫ V, Real.exp (-A (overwrite R W V)) ∂π) := by
    have hpos := CompactGibbsContinuity.partition_positive π
      (fun V => A (overwrite R W V)) (hAc.comp (overwrite R W).continuous)
    exact LocalGibbsComparison.weighted_integral π _
      (Real.continuous_exp.comp (hAc.comp (overwrite R W).continuous).neg).measurable
      (fun _ => (Real.exp_pos _).le) hpos G
  -- right-hand side: the inner law does not see the first box
  have hinner (V : I → X) : (E μ Φ hΦc T F) (overwrite S U V) =
      (∫ W, Real.exp (-A (overwrite T U W)) * F (overwrite T (overwrite S U V) W) ∂π) /
        ∫ W, Real.exp (-A (overwrite T U W)) ∂π := by
    rw [E_apply, fiber_congr μ hΦc hΦ T (overwrite S U V) U (fun i hi => by
      have : i ∉ S := Finset.disjoint_left.1 hST.symm.nbr_disjoint hi
      simp [overwrite_apply, this]), hexp]
  rw [E_apply, E_apply, hexp, hexp]
  simp_rw [hinner]
  set Zb := ∫ W, Real.exp (-A (overwrite T U W)) ∂π with hZb
  have hZbpos : 0 < Zb := CompactGibbsContinuity.partition_positive π
    (fun V => A (overwrite T U V)) (hAc.comp (overwrite T U).continuous)
  have hZapos : 0 < ∫ V, Real.exp (-A (overwrite S U V)) ∂π :=
    CompactGibbsContinuity.partition_positive π
      (fun V => A (overwrite S U V)) (hAc.comp (overwrite S U).continuous)
  -- numerator and denominator of the left-hand side, through the mixing identity
  let H₁ : C(I → X, ℝ) :=
    ⟨fun Y => Real.exp (-A (overwrite (S ∪ T) U Y)) * F (overwrite (S ∪ T) U Y),
    (Real.continuous_exp.comp (hAc.comp (overwrite (S ∪ T) U).continuous).neg).mul
      (F.continuous.comp (overwrite (S ∪ T) U).continuous)⟩
  let H₂ : C(I → X, ℝ) := ⟨fun Y => Real.exp (-A (overwrite (S ∪ T) U Y)),
    Real.continuous_exp.comp (hAc.comp (overwrite (S ∪ T) U).continuous).neg⟩
  have hnum : (∫ Y, Real.exp (-A (overwrite (S ∪ T) U Y)) * F (overwrite (S ∪ T) U Y) ∂π) =
      Real.exp (A U) * ∫ V, Real.exp (-A (overwrite S U V)) *
        ∫ W, Real.exp (-A (overwrite T U W)) * F (overwrite T (overwrite S U V) W) ∂π ∂π := by
    refine (mix_integral μ S H₁).trans ?_
    change (∫ V, ∫ W, Real.exp (-A (overwrite (S ∪ T) U (overwrite S W V))) *
      F (overwrite (S ∪ T) U (overwrite S W V)) ∂π ∂π) = _
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
    change ∫ W, _ ∂π = Real.exp (A U) * (Real.exp (-A (overwrite S U V)) * _)
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
    change Real.exp _ * F _ = _
    rw [hov, hact]
    rw [show -(A (overwrite S U V) + A (overwrite T U W) - A U) =
      A U + (-A (overwrite S U V) + -A (overwrite T U W)) by ring, Real.exp_add, Real.exp_add]
    ring
  have hden : (∫ Y, Real.exp (-A (overwrite (S ∪ T) U Y)) ∂π) =
      Real.exp (A U) * ((∫ V, Real.exp (-A (overwrite S U V)) ∂π) * Zb) := by
    refine (mix_integral μ S H₂).trans ?_
    change (∫ V, ∫ W, Real.exp (-A (overwrite (S ∪ T) U (overwrite S W V))) ∂π ∂π) = _
    rw [← integral_mul_const, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
    change ∫ W, _ ∂π = Real.exp (A U) * (Real.exp (-A (overwrite S U V)) * Zb)
    rw [hZb, ← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
    change Real.exp _ = _
    rw [hov, hact]
    rw [show -(A (overwrite S U V) + A (overwrite T U W) - A U) =
      A U + (-A (overwrite S U V) + -A (overwrite T U W)) by ring, Real.exp_add, Real.exp_add]
  rw [hnum, hden]
  have hpull : (∫ V, Real.exp (-A (overwrite S U V)) *
      ((∫ W, Real.exp (-A (overwrite T U W)) * F (overwrite T (overwrite S U V) W) ∂π) / Zb) ∂π) =
      (∫ V, Real.exp (-A (overwrite S U V)) *
        ∫ W, Real.exp (-A (overwrite T U W)) * F (overwrite T (overwrite S U V) W) ∂π ∂π) / Zb := by
    rw [← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
    change _ * (_ / Zb) = (_ * _) / Zb
    ring
  rw [hpull]
  have he := (Real.exp_pos (A U)).ne'
  field_simp

end Union

/-! ### The block influence inequality and its propagation -/
section Influence
variable {I P X : Type*} [Fintype I] [Fintype P] [DecidableEq I]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]
  (D : P → Finset I) (Φ : P → (I → X) → ℝ) (hΦc : ∀ p, Continuous (Φ p))

/-- **Block influence on a class of observables.** A statement about two conditional laws of the box `S` whose
boundary conditions differ in one boundary coordinate `j`, tested on the observables of a class `𝓐`. The exterior
of the test function is frozen, so only the change of the law is charged. -/
def BlockInfluenceOn (𝓐 : Submodule ℝ C(I → X, ℝ)) (S : Finset I) (κ : I → I → ℝ) : Prop :=
  ∀ F ∈ 𝓐, ∀ d : I → ℝ, OscBound F d → (∀ i, 0 ≤ d i) → ∀ j ∈ nbr D S,
    ∀ x y : I → X, (∀ l, l ≠ j → x l = y l) →
      |(∫ V, F (overwrite S x V) ∂fiber μ Φ hΦc S x) -
        ∫ V, F (overwrite S x V) ∂fiber μ Φ hΦc S y| ≤ ∑ i ∈ S, κ j i * d i

/-- Block influence tested on every continuous function. -/
abbrev BlockInfluence (S : Finset I) (κ : I → I → ℝ) : Prop :=
  BlockInfluenceOn μ D Φ hΦc ⊤ S κ

/-- A class of observables mapped to itself by every box update. -/
def Stable (𝓐 : Submodule ℝ C(I → X, ℝ)) : Prop :=
  ∀ (S : Finset I), ∀ F ∈ 𝓐, E μ Φ hΦc S F ∈ 𝓐

theorem stable_top : Stable μ Φ hΦc ⊤ := fun _ _ _ => Submodule.mem_top

variable {μ D Φ hΦc}

/-- What a block update does to the coordinate oscillations. -/
def stepBound (D : P → Finset I) (S : Finset I) (κ : I → I → ℝ) (d : I → ℝ) (j : I) : ℝ :=
  if j ∈ S then 0 else d j + if j ∈ nbr D S then ∑ i ∈ S, κ j i * d i else 0

variable (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
include hΦ

theorem E_osc {𝓐 : Submodule ℝ C(I → X, ℝ)} {S : Finset I} {κ : I → I → ℝ}
    (hinf : BlockInfluenceOn μ D Φ hΦc 𝓐 S κ)
    (F : C(I → X, ℝ)) (hFA : F ∈ 𝓐) (d : I → ℝ) (hF : OscBound F d) (hd : ∀ i, 0 ≤ d i) :
    OscBound (E μ Φ hΦc S F) (stepBound D S κ d) := by
  intro j x y hxy
  rw [E_apply, E_apply]
  by_cases hjS : j ∈ S
  · have hov (V : I → X) : overwrite S x V = overwrite S y V := by
      funext i
      by_cases hi : i ∈ S
      · simp [overwrite_apply, hi]
      · have : i ≠ j := fun h => hi (h ▸ hjS)
        simp [overwrite_apply, hi, hxy i this]
    have hf : fiber μ Φ hΦc S x = fiber μ Φ hΦc S y := by
      unfold fiber
      simp only [hov]
    simp [hov, hf, stepBound, hjS]
  · have hint (R : Finset I) (W Z : I → X) :
        Integrable (fun V => F (overwrite R Z V)) (fiber μ Φ hΦc R W) :=
      (F.continuous.comp (overwrite R Z).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have h2 : |(∫ V, F (overwrite S x V) ∂fiber μ Φ hΦc S y) -
        ∫ V, F (overwrite S y V) ∂fiber μ Φ hΦc S y| ≤ d j := by
      rw [← integral_sub (hint _ _ _) (hint _ _ _)]
      have hb (V : I → X) : ‖F (overwrite S x V) - F (overwrite S y V)‖ ≤ d j := by
        rw [Real.norm_eq_abs]
        refine hF j _ _ fun l hl => ?_
        by_cases hi : l ∈ S
        · simp [overwrite_apply, hi]
        · simp [overwrite_apply, hi, hxy l hl]
      simpa using norm_integral_le_of_norm_le_const (μ := fiber μ Φ hΦc S y)
        (Filter.Eventually.of_forall hb)
    have h1 : |(∫ V, F (overwrite S x V) ∂fiber μ Φ hΦc S x) -
        ∫ V, F (overwrite S x V) ∂fiber μ Φ hΦc S y| ≤
          if j ∈ nbr D S then ∑ i ∈ S, κ j i * d i else 0 := by
      by_cases hj : j ∈ nbr D S
      · rw [if_pos hj]
        exact hinf F hFA d hF hd j hj x y hxy
      · rw [if_neg hj, fiber_congr μ hΦc hΦ S x y (fun i hi => hxy i fun h => hj (h ▸ hi))]
        simp
    simp only [stepBound, hjS, if_false]
    calc _ ≤ _ := abs_sub_le _ (∫ V, F (overwrite S x V) ∂fiber μ Φ hΦc S y) _
      _ ≤ _ := by linarith

omit hΦ in
theorem E_empty (F : C(I → X, ℝ)) : E μ Φ hΦc (∅ : Finset I) F = F := by
  ext U
  exact E_of_outside μ hΦc ∅ F (fun x y h => by
    congr 1
    funext i
    exact h i (by simp)) U

variable {K : Type*} [DecidableEq K]

/-- What the union of pairwise non-interacting blocks does to the coordinate oscillations. -/
def famBound (D : P → Finset I) (b : K → Finset I) (κ : K → I → I → ℝ) (K₀ : Finset K) (d : I → ℝ)
    (j : I) : ℝ :=
  if j ∈ K₀.biUnion b then 0 else
    d j + ∑ k ∈ K₀, if j ∈ nbr D (b k) then ∑ i ∈ b k, κ k j i * d i else 0

omit hΦ [Fintype I] [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] in
theorem famBound_nonneg (b : K → Finset I) (κ : K → I → I → ℝ) (hκ : ∀ k j i, 0 ≤ κ k j i)
    (K₀ : Finset K) (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) (j : I) : 0 ≤ famBound D b κ K₀ d j := by
  unfold famBound
  split
  · exact le_rfl
  · refine add_nonneg (hd j) (Finset.sum_nonneg fun k _ => ?_)
    split
    · exact Finset.sum_nonneg fun i _ => mul_nonneg (hκ k j i) (hd i)
    · exact le_rfl

omit hΦ [Fintype I] [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] in
theorem noninteract_biUnion (b : K → Finset I) (k : K) (K₀ : Finset K)
    (hsep : ∀ k' ∈ K₀, NonInteract D (b k) (b k')) : NonInteract D (b k) (K₀.biUnion b) := by
  refine ⟨(Finset.disjoint_biUnion_right _ _ _).2 fun k' hk' => (hsep k' hk').1, fun p => ?_⟩
  by_cases hp : Disjoint (D p) (b k)
  · exact Or.inl hp
  · refine Or.inr ((Finset.disjoint_biUnion_right _ _ _).2 fun k' hk' => ?_)
    exact (hsep k' hk').2 p |>.resolve_left hp

/-- The oscillation bound through a union of pairwise non-interacting blocks. -/
theorem E_family_osc {𝓐 : Submodule ℝ C(I → X, ℝ)} (hst : Stable μ Φ hΦc 𝓐)
    (b : K → Finset I) (κ : K → I → I → ℝ)
    (hinf : ∀ k, BlockInfluenceOn μ D Φ hΦc 𝓐 (b k) (κ k)) (hκ : ∀ k j i, 0 ≤ κ k j i)
    (K₀ : Finset K) (hsep : ∀ k ∈ K₀, ∀ k' ∈ K₀, k ≠ k' → NonInteract D (b k) (b k'))
    (F : C(I → X, ℝ)) (hFA : F ∈ 𝓐) (d : I → ℝ) (hF : OscBound F d) (hd : ∀ i, 0 ≤ d i) :
    OscBound (E μ Φ hΦc (K₀.biUnion b) F) (famBound D b κ K₀ d) := by
  induction K₀ using Finset.induction_on with
  | empty =>
    rw [Finset.biUnion_empty, E_empty]
    simpa [OscBound, famBound] using hF
  | @insert k K₀ hk ih =>
    have hsep' : ∀ k₁ ∈ K₀, ∀ k₂ ∈ K₀, k₁ ≠ k₂ → NonInteract D (b k₁) (b k₂) :=
      fun k₁ h₁ k₂ h₂ => hsep k₁ (Finset.mem_insert_of_mem h₁) k₂ (Finset.mem_insert_of_mem h₂)
    have hk' : ∀ k' ∈ K₀, NonInteract D (b k) (b k') := fun k' h' =>
      hsep k (Finset.mem_insert_self _ _) k' (Finset.mem_insert_of_mem h') (fun h => hk (h ▸ h'))
    have hni := noninteract_biUnion b k K₀ hk'
    have hE : E μ Φ hΦc ((insert k K₀).biUnion b) F =
        E μ Φ hΦc (b k) (E μ Φ hΦc (K₀.biUnion b) F) := by
      ext U
      rw [Finset.biUnion_insert]
      exact E_union μ hΦc hΦ _ _ hni F U
    rw [hE]
    have hstep := E_osc hΦ (hinf k) _ (hst _ _ hFA) _ (ih hsep') (famBound_nonneg b κ hκ K₀ d hd)
    intro j x y hxy
    refine (hstep j x y hxy).trans (le_of_eq ?_)
    -- the two oscillation budgets agree
    have hin (i : I) (hi : i ∈ b k) : famBound D b κ K₀ d i = d i := by
      have hnot : i ∉ K₀.biUnion b := fun h => Finset.disjoint_left.1 hni.1 hi h
      simp only [famBound, hnot, if_false]
      rw [Finset.sum_eq_zero, add_zero]
      intro k' hk''
      have : i ∉ nbr D (b k') := fun h =>
        Finset.disjoint_left.1 (hk' k' hk'').symm.nbr_disjoint h hi
      simp [this]
    simp only [stepBound, famBound, Finset.biUnion_insert, Finset.mem_union,
      Finset.sum_insert hk]
    by_cases hj1 : j ∈ b k
    · simp [hj1]
    · by_cases hj2 : j ∈ K₀.biUnion b
      · have : j ∉ nbr D (b k) := fun h => Finset.disjoint_left.1 hni.nbr_disjoint h hj2
        simp [hj1, hj2, this]
      · simp only [hj1, hj2, or_self, if_false]
        have hsum : (∑ i ∈ b k, κ k j i * famBound D b κ K₀ d i) =
            ∑ i ∈ b k, κ k j i * d i :=
          Finset.sum_congr rfl fun i hi => by rw [hin i hi]
        simp only [famBound] at hsum
        rw [hsum]
        ring

end Influence

/-! ### The finite-box criterion -/
section Criterion
variable {I P X K Color : Type*} [Fintype I] [Fintype P] [DecidableEq I]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [Fintype K] [DecidableEq K] [Fintype Color] [DecidableEq Color] [Nonempty Color]
  (μ : Measure X) [IsProbabilityMeasure μ]
  (D : P → Finset I) (Φ : P → (I → X) → ℝ) (hΦc : ∀ p, Continuous (Φ p))

/-- The blocks of one colour, as one large box. -/
def colorBlock (b : K → Finset I) (color : K → Color) (c : Color) : Finset I :=
  (Finset.univ.filter fun k => color k = c).biUnion b

/-- Boundary influence received by coordinate `i` in block `k`. -/
def row (D : P → Finset I) (b : K → Finset I) (κ : K → I → I → ℝ) (k : K) (i : I) : ℝ :=
  ∑ j ∈ nbr D (b k), κ k j i

/-- **The finite-box criterion on a class of observables.** Blocks `b k` carrying block influences `κ k` on `𝓐`,
where blocks of one colour do not interact, and every coordinate has total margin at least `ε`, summed over the
blocks containing it. A coordinate near the edge of one block may have row above one, so long as the blocks
containing it average below one.

Nothing in this structure bounds the size of a block. Each hypothesis is local to one block only when the block
is small. The whole lattice as one block satisfies it trivially (`whole_box`), with empty conclusions. Anything
about uniformity in the volume has content only for a block family, `C` and `ε` held fixed as the lattice grows. -/
structure BoxCriterionOn (𝓐 : Submodule ℝ C(I → X, ℝ)) (b : K → Finset I) (κ : K → I → I → ℝ)
    (color : K → Color) (ε : ℝ) : Prop where
  influence : ∀ k, BlockInfluenceOn μ D Φ hΦc 𝓐 (b k) (κ k)
  nonneg : ∀ k j i, 0 ≤ κ k j i
  separated : ∀ k k', k ≠ k' → color k = color k' → NonInteract D (b k) (b k')
  margin : ∀ i, ε ≤ ∑ k ∈ Finset.univ.filter (fun k => i ∈ b k), (1 - row D b κ k i)

/-- The finite-box criterion, tested on every continuous function. -/
abbrev BoxCriterion (b : K → Finset I) (κ : K → I → I → ℝ) (color : K → Color) (ε : ℝ) : Prop :=
  BoxCriterionOn μ D Φ hΦc ⊤ b κ color ε

variable {μ D Φ hΦc} in
/-- A criterion on a class gives the criterion on any smaller class. -/
theorem BoxCriterionOn.mono {𝓐 𝓑 : Submodule ℝ C(I → X, ℝ)} (h𝓐 : 𝓐 ≤ 𝓑) {b : K → Finset I}
    {κ : K → I → I → ℝ} {color : K → Color} {ε : ℝ} (hc : BoxCriterionOn μ D Φ hΦc 𝓑 b κ color ε) :
    BoxCriterionOn μ D Φ hΦc 𝓐 b κ color ε :=
  ⟨fun k F hF => hc.influence k F (h𝓐 hF), hc.nonneg, hc.separated, hc.margin⟩

/-- **The criterion alone is not a statement about small boxes.** The whole lattice, taken as a single block with
zero influences, satisfies it with margin one, for any factors and at every coupling. Then the rate is `0` and the
Poincaré inequality reads `Var F ≤ Var F`. -/
theorem whole_box :
    BoxCriterion μ D Φ hΦc (K := Unit) (Color := Unit) (fun _ => Finset.univ) (fun _ _ _ => 0)
      (fun _ => ()) 1 := by
  refine ⟨fun _ F _ d _ _ j hj => ?_, fun _ _ _ => le_rfl, fun k k' h _ => (h rfl).elim, fun i => ?_⟩
  · exact absurd ((mem_nbr D _ j).1 hj).1 (by simp)
  · simp [row]

/-- The actual global Gibbs law. -/
abbrev gibbs : Measure (I → X) := FiniteFactorContraction.law μ Φ hΦc

/-- One step of the dynamics: choose a colour uniformly and resample its blocks from their true conditional
law. This is an auxiliary update, not physical time. -/
def update (b : K → Finset I) (color : K → Color) (F : C(I → X, ℝ)) : C(I → X, ℝ) :=
  (Fintype.card Color : ℝ)⁻¹ • ∑ c : Color, E μ Φ hΦc (colorBlock b color c) F

/-- The contraction rate of the criterion, depending only on the margin and the number of colours. -/
def rate (Color : Type*) [Fintype Color] (ε : ℝ) : ℝ := 1 - ε / Fintype.card Color

variable {μ D Φ hΦc}

theorem update_apply (b : K → Finset I) (color : K → Color) (F : C(I → X, ℝ)) (U : I → X) :
    update μ Φ hΦc b color F U =
      (Fintype.card Color : ℝ)⁻¹ * ∑ c : Color, E μ Φ hΦc (colorBlock b color c) F U := by
  simp [update, ContinuousMap.sum_apply]

theorem integrable_cont (ν : Measure (I → X)) [IsProbabilityMeasure ν] (G : C(I → X, ℝ)) :
    Integrable (G : (I → X) → ℝ) ν :=
  G.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem update_stationary (b : K → Finset I) (color : K → Color) (F : C(I → X, ℝ)) :
    (∫ U, update μ Φ hΦc b color F U ∂gibbs μ Φ hΦc) = ∫ U, F U ∂gibbs μ Φ hΦc := by
  simp only [update_apply, integral_const_mul]
  rw [integral_finset_sum Finset.univ fun c _ => integrable_cont _ _]
  simp_rw [gibbs, FiniteFactorContraction.law, E, blockAverage_stationary]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]

theorem update_reversible (b : K → Finset I) (color : K → Color) (F H : C(I → X, ℝ)) :
    (∫ U, F U * update μ Φ hΦc b color H U ∂gibbs μ Φ hΦc) =
      ∫ U, update μ Φ hΦc b color F U * H U ∂gibbs μ Φ hΦc := by
  have hleft (U : I → X) : F U * update μ Φ hΦc b color H U =
      (Fintype.card Color : ℝ)⁻¹ * ∑ c : Color, F U * E μ Φ hΦc (colorBlock b color c) H U := by
    rw [update_apply, ← mul_assoc, mul_comm (F U) _, mul_assoc, Finset.mul_sum]
  have hright (U : I → X) : update μ Φ hΦc b color F U * H U =
      (Fintype.card Color : ℝ)⁻¹ * ∑ c : Color, E μ Φ hΦc (colorBlock b color c) F U * H U := by
    rw [update_apply, mul_assoc, Finset.sum_mul]
  simp_rw [hleft, hright]
  rw [integral_const_mul, integral_const_mul]
  congr 1
  have hL (c : Color) : Integrable (fun U => F U * E μ Φ hΦc (colorBlock b color c) H U)
      (gibbs μ Φ hΦc) := integrable_cont _ (F * E μ Φ hΦc (colorBlock b color c) H)
  have hR (c : Color) : Integrable (fun U => E μ Φ hΦc (colorBlock b color c) F U * H U)
      (gibbs μ Φ hΦc) := integrable_cont _ (E μ Φ hΦc (colorBlock b color c) F * H)
  rw [integral_finset_sum Finset.univ fun c _ => hL c,
    integral_finset_sum Finset.univ fun c _ => hR c]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact blockAverage_reversible μ (actionMap Φ hΦc) _ F H

/-- Total oscillation after one colour. -/
theorem famBound_sum (b : K → Finset I) (κ : K → I → I → ℝ) (hκ : ∀ k j i, 0 ≤ κ k j i)
    (K₀ : Finset K) (hdisj : ∀ k ∈ K₀, ∀ k' ∈ K₀, k ≠ k' → Disjoint (b k) (b k'))
    (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) :
    ∑ j, famBound D b κ K₀ d j ≤
      ∑ j, d j - ∑ k ∈ K₀, ∑ i ∈ b k, (1 - row D b κ k i) * d i := by
  have hX (k : K) : (∑ j, if j ∈ nbr D (b k) then ∑ i ∈ b k, κ k j i * d i else 0) =
      ∑ i ∈ b k, row D b κ k i * d i := by
    simp only [Finset.sum_ite_mem, Finset.univ_inter, row, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hS : (∑ j ∈ K₀.biUnion b, d j) = ∑ k ∈ K₀, ∑ i ∈ b k, d i :=
    Finset.sum_biUnion (fun k hk k' hk' h => hdisj k hk k' hk' h)
  have hle (j : I) : famBound D b κ K₀ d j ≤
      (if j ∈ K₀.biUnion b then 0 else d j) +
        ∑ k ∈ K₀, if j ∈ nbr D (b k) then ∑ i ∈ b k, κ k j i * d i else 0 := by
    have hn : 0 ≤ ∑ k ∈ K₀, if j ∈ nbr D (b k) then ∑ i ∈ b k, κ k j i * d i else 0 :=
      Finset.sum_nonneg fun k _ => by
        split
        · exact Finset.sum_nonneg fun i _ => mul_nonneg (hκ k j i) (hd i)
        · exact le_rfl
    unfold famBound
    split
    · simpa using hn
    · exact le_rfl
  have hout : (∑ j, if j ∈ K₀.biUnion b then (0 : ℝ) else d j) =
      ∑ j, d j - ∑ j ∈ K₀.biUnion b, d j := by
    have h := Finset.sum_ite_mem Finset.univ (K₀.biUnion b) d
    simp only [Finset.univ_inter] at h
    rw [← h, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split <;> simp
  calc _ ≤ ∑ j, ((if j ∈ K₀.biUnion b then 0 else d j) +
        ∑ k ∈ K₀, if j ∈ nbr D (b k) then ∑ i ∈ b k, κ k j i * d i else 0) :=
        Finset.sum_le_sum fun j _ => hle j
    _ = (∑ j, d j - ∑ j ∈ K₀.biUnion b, d j) +
        ∑ k ∈ K₀, ∑ i ∈ b k, row D b κ k i * d i := by
        rw [Finset.sum_add_distrib, hout, Finset.sum_comm]
        simp only [hX]
    _ = _ := by
        rw [hS]
        simp only [sub_mul, one_mul, Finset.sum_sub_distrib]
        ring

/-- **One step of the criterion contracts the total oscillation by `rate`.** -/
theorem budget (b : K → Finset I) (κ : K → I → I → ℝ) (color : K → Color) (ε : ℝ)
    (hκ : ∀ k j i, 0 ≤ κ k j i)
    (hsep : ∀ k k', k ≠ k' → color k = color k' → NonInteract D (b k) (b k'))
    (hm : ∀ i, ε ≤ ∑ k ∈ Finset.univ.filter (fun k => i ∈ b k), (1 - row D b κ k i))
    (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) :
    ∑ j, ((Fintype.card Color : ℝ)⁻¹ *
        ∑ c : Color, famBound D b κ (Finset.univ.filter fun k => color k = c) d j) ≤
      rate Color ε * ∑ j, d j := by
  have hC : (0 : ℝ) < Fintype.card Color := by exact_mod_cast Fintype.card_pos
  have hdisj (c : Color) : ∀ k ∈ (Finset.univ.filter fun k => color k = c),
      ∀ k' ∈ (Finset.univ.filter fun k => color k = c), k ≠ k' → Disjoint (b k) (b k') := by
    intro k hk k' hk' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk hk'
    exact (hsep k k' h (hk.trans hk'.symm)).1
  have h1 : ∑ c : Color, ∑ j, famBound D b κ (Finset.univ.filter fun k => color k = c) d j ≤
      ∑ c : Color, (∑ j, d j - ∑ k ∈ Finset.univ.filter (fun k => color k = c),
        ∑ i ∈ b k, (1 - row D b κ k i) * d i) :=
    Finset.sum_le_sum fun c _ => famBound_sum b κ hκ _ (hdisj c) d hd
  have hfib : (∑ c : Color, ∑ k ∈ Finset.univ.filter (fun k => color k = c),
      ∑ i ∈ b k, (1 - row D b κ k i) * d i) =
        ∑ k, ∑ i ∈ b k, (1 - row D b κ k i) * d i :=
    Finset.sum_fiberwise _ _ _
  have hswap : (∑ k, ∑ i ∈ b k, (1 - row D b κ k i) * d i) =
      ∑ i, (∑ k ∈ Finset.univ.filter (fun k => i ∈ b k), (1 - row D b κ k i)) * d i := by
    simp only [Finset.sum_mul, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Finset.sum_ite_mem]
  have hmass : ε * ∑ i, d i ≤ ∑ k, ∑ i ∈ b k, (1 - row D b κ k i) * d i := by
    rw [hswap, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hm i) (hd i)
  simp only [← Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [inv_mul_le_iff₀ hC]
  refine h1.trans ?_
  rw [Finset.sum_sub_distrib, hfib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold rate
  have : (Fintype.card Color : ℝ) * ((1 - ε / (Fintype.card Color : ℝ)) * ∑ j, d j) =
      (Fintype.card Color : ℝ) * ∑ j, d j - ε * ∑ j, d j := by
    field_simp
  rw [this]
  linarith

variable (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
variable {b : K → Finset I} {κ : K → I → I → ℝ} {color : K → Color} {ε : ℝ}
  {𝓐 : Submodule ℝ C(I → X, ℝ)}

omit [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X] [BorelSpace X] in
/-- The margin is at most the number of colours, since a coordinate lies in at most one block per colour. -/
theorem margin_le_card [Nonempty I] (hκ : ∀ k j i, 0 ≤ κ k j i)
    (hsep : ∀ k k', k ≠ k' → color k = color k' → NonInteract D (b k) (b k'))
    (hm : ∀ i, ε ≤ ∑ k ∈ Finset.univ.filter (fun k => i ∈ b k), (1 - row D b κ k i)) :
    ε ≤ Fintype.card Color := by
  obtain ⟨i⟩ := ‹Nonempty I›
  have h1 : (∑ k ∈ Finset.univ.filter (fun k => i ∈ b k), (1 - row D b κ k i)) ≤
      ∑ _k ∈ Finset.univ.filter (fun k => i ∈ b k), (1 : ℝ) := by
    refine Finset.sum_le_sum fun k _ => ?_
    have : 0 ≤ row D b κ k i := Finset.sum_nonneg fun j _ => hκ k j i
    linarith
  have h2 : (Finset.univ.filter (fun k => i ∈ b k)).card ≤ Fintype.card Color := by
    rw [← Finset.card_univ]
    refine Finset.card_le_card_of_injOn color (fun _ _ => Finset.mem_univ _) ?_
    intro k hk k' hk' he
    by_contra hne
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hk hk'
    exact Finset.disjoint_left.1 (hsep k k' hne he).1 hk hk'
  have h3 : ((Finset.univ.filter (fun k => i ∈ b k)).card : ℝ) ≤ Fintype.card Color := by
    exact_mod_cast h2
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h1
  linarith [hm i]

theorem rate_nonneg (hε : ε ≤ Fintype.card Color) : 0 ≤ rate Color ε := by
  have hC : (0 : ℝ) < Fintype.card Color := by exact_mod_cast Fintype.card_pos
  unfold rate
  rw [sub_nonneg, div_le_one hC]
  exact hε

theorem rate_lt_one (hε : 0 < ε) : rate Color ε < 1 := by
  have hC : (0 : ℝ) < Fintype.card Color := by exact_mod_cast Fintype.card_pos
  unfold rate
  have := div_pos hε hC
  linarith

/-- A stable class is mapped to itself by the dynamics. -/
theorem update_mem (hst : Stable μ Φ hΦc 𝓐) (b : K → Finset I) (color : K → Color) (F : C(I → X, ℝ))
    (hF : F ∈ 𝓐) : update μ Φ hΦc b color F ∈ 𝓐 :=
  𝓐.smul_mem _ (𝓐.sum_mem fun _ _ => hst _ _ hF)

theorem iterate_mem (hst : Stable μ Φ hΦc 𝓐) (b : K → Finset I) (color : K → Color) (F : C(I → X, ℝ))
    (hF : F ∈ 𝓐) (k : ℕ) : ParallelOscillation.updateIterate (update μ Φ hΦc b color) k F ∈ 𝓐 := by
  induction k with
  | zero => exact hF
  | succ k ih => exact update_mem hst b color _ ih

include hΦ

theorem update_osc (hst : Stable μ Φ hΦc 𝓐) (hc : BoxCriterionOn μ D Φ hΦc 𝓐 b κ color ε)
    (F : C(I → X, ℝ)) (hFA : F ∈ 𝓐) (d : I → ℝ)
    (hF : OscBound F d) (hd : ∀ i, 0 ≤ d i) :
    OscBound (update μ Φ hΦc b color F) (fun j => (Fintype.card Color : ℝ)⁻¹ *
        ∑ c : Color, famBound D b κ (Finset.univ.filter fun k => color k = c) d j) := by
  intro j x y hxy
  rw [update_apply, update_apply, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Nat.cast_nonneg _))
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  refine E_family_osc hΦ hst b κ hc.influence hc.nonneg _ ?_ F hFA d hF hd j x y hxy
  intro k hk k' hk' h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk hk'
  exact hc.separated k k' h (hk.trans hk'.symm)

/-- The total oscillation contracts geometrically along the dynamics, at a rate that sees only `ε` and the
number of colours. -/
theorem iterate_osc [Nonempty I] (hst : Stable μ Φ hΦc 𝓐) (hc : BoxCriterionOn μ D Φ hΦc 𝓐 b κ color ε)
    (F : C(I → X, ℝ)) (hFA : F ∈ 𝓐)
    (d : I → ℝ) (hF : OscBound F d) (hd : ∀ i, 0 ≤ d i) (k : ℕ) :
    ∃ d' : I → ℝ, OscBound (ParallelOscillation.updateIterate (update μ Φ hΦc b color) k F) d' ∧
      (∀ i, 0 ≤ d' i) ∧ ∑ i, d' i ≤ rate Color ε ^ k * ∑ i, d i := by
  have hC : (0 : ℝ) < Fintype.card Color := by exact_mod_cast Fintype.card_pos
  have hr := rate_nonneg (Color := Color) (margin_le_card hc.nonneg hc.separated hc.margin)
  induction k with
  | zero => exact ⟨d, hF, hd, by simp⟩
  | succ k ih =>
    obtain ⟨d', h1, h2, h3⟩ := ih
    refine ⟨_, update_osc hΦ hst hc _ (iterate_mem hst b color F hFA k) d' h1 h2, fun j => ?_, ?_⟩
    · exact mul_nonneg (inv_nonneg.2 hC.le) (Finset.sum_nonneg fun c _ =>
        famBound_nonneg b κ hc.nonneg _ d' h2 j)
    · refine (budget b κ color ε hc.nonneg hc.separated hc.margin d' h2).trans ?_
      rw [pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left h3 hr

/-- **Mixing.** After `k` steps, from every configuration, the expectation of an observable of the class is within
`rate^k` times its total oscillation of the true Gibbs value. The volume enters only through `F`, the number of
colours and `ε`. -/
theorem mixing [Nonempty I] (hst : Stable μ Φ hΦc 𝓐) (hc : BoxCriterionOn μ D Φ hΦc 𝓐 b κ color ε)
    (F : C(I → X, ℝ)) (hFA : F ∈ 𝓐)
    (d : I → ℝ) (hF : OscBound F d) (hd : ∀ i, 0 ≤ d i) (k : ℕ) (x : I → X) :
    |ParallelOscillation.updateIterate (update μ Φ hΦc b color) k F x -
        ∫ y, F y ∂gibbs μ Φ hΦc| ≤ rate Color ε ^ k * ∑ i, d i := by
  obtain ⟨d', h1, h2, h3⟩ := iterate_osc hΦ hst hc F hFA d hF hd k
  set P := update μ Φ hΦc b color
  have hmean := ParallelOscillation.updateIterate_mean (gibbs μ Φ hΦc) P
    (update_stationary b color) F k
  rw [← hmean]
  have hi := integrable_cont (gibbs μ Φ hΦc) (ParallelOscillation.updateIterate P k F)
  have he : ParallelOscillation.updateIterate P k F x -
      (∫ y, ParallelOscillation.updateIterate P k F y ∂gibbs μ Φ hΦc) =
      ∫ y, ParallelOscillation.updateIterate P k F x -
        ParallelOscillation.updateIterate P k F y ∂gibbs μ Φ hΦc := by
    rw [integral_sub (integrable_const _) hi]
    simp
  rw [he]
  have hb (y : I → X) : ‖ParallelOscillation.updateIterate P k F x -
      ParallelOscillation.updateIterate P k F y‖ ≤ rate Color ε ^ k * ∑ i, d i := by
    rw [Real.norm_eq_abs]
    exact (ParallelOscillation.global_difference _ d' h1 x y).trans h3
  simpa using norm_integral_le_of_norm_le_const (μ := gibbs μ Φ hΦc)
    (Filter.Eventually.of_forall hb)

/-! ### Locality and clustering -/

/-- Fatten a set by the blocks meeting it and their boundaries. -/
def grow (D : P → Finset I) (b : K → Finset I) (A : Finset I) : Finset I :=
  A ∪ (Finset.univ.filter fun k => ¬ Disjoint (b k) A).biUnion fun k => b k ∪ nbr D (b k)

/-- The set reached from `A` in `k` steps. -/
def growN (D : P → Finset I) (b : K → Finset I) (A : Finset I) : ℕ → Finset I
  | 0 => A
  | k + 1 => grow D b (growN D b A k)

/-- In the update of colour `c`, only the blocks meeting the support of `F` act on `F`. -/
theorem E_color_split (hsep : ∀ k k', k ≠ k' → color k = color k' → NonInteract D (b k) (b k'))
    (A : Finset I) (F : C(I → X, ℝ)) (hF : DependsOn (F : (I → X) → ℝ) (A : Set I)) (c : Color) :
    E μ Φ hΦc (colorBlock b color c) F =
      E μ Φ hΦc ((Finset.univ.filter fun k => color k = c ∧ ¬ Disjoint (b k) A).biUnion b) F := by
  classical
  set K₁ := Finset.univ.filter fun k => color k = c ∧ ¬ Disjoint (b k) A with hK₁
  set K₂ := Finset.univ.filter fun k => color k = c ∧ Disjoint (b k) A with hK₂
  have hunion : colorBlock b color c = K₁.biUnion b ∪ K₂.biUnion b := by
    unfold colorBlock
    rw [← Finset.union_biUnion]
    congr 1
    ext k
    simp only [hK₁, hK₂, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    tauto
  have hpair (k : K) (hk : k ∈ K₁) (k' : K) (hk' : k' ∈ K₂) : NonInteract D (b k) (b k') := by
    simp only [hK₁, hK₂, Finset.mem_filter, Finset.mem_univ, true_and] at hk hk'
    refine hsep k k' (fun h => hk.2 (h ▸ hk'.2)) (hk.1.trans hk'.1.symm)
  have hni : NonInteract D (K₁.biUnion b) (K₂.biUnion b) := by
    refine ⟨(Finset.disjoint_biUnion_left _ _ _).2 fun k hk =>
      (noninteract_biUnion b k K₂ (hpair k hk)).1, fun p => ?_⟩
    by_cases hp : Disjoint (D p) (K₂.biUnion b)
    · exact Or.inr hp
    · refine Or.inl ((Finset.disjoint_biUnion_right _ _ _).2 fun k hk => ?_)
      exact ((noninteract_biUnion b k K₂ (hpair k hk)).2 p).resolve_right hp
  have hout : E μ Φ hΦc (K₂.biUnion b) F = F := by
    ext U
    refine E_of_outside μ hΦc _ F (fun x y h => hF fun i hi => h i fun hmem => ?_) U
    obtain ⟨k, hk, hik⟩ := Finset.mem_biUnion.1 hmem
    simp only [hK₂, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact Finset.disjoint_left.1 hk.2 hik (by exact_mod_cast hi)
  ext U
  rw [hunion, E_union μ hΦc hΦ _ _ hni F U, hout]

/-- One step grows the support by at most one layer. -/
theorem update_depends (hsep : ∀ k k', k ≠ k' → color k = color k' → NonInteract D (b k) (b k'))
    (A : Finset I) (F : C(I → X, ℝ)) (hF : DependsOn (F : (I → X) → ℝ) (A : Set I)) :
    DependsOn (update μ Φ hΦc b color F : (I → X) → ℝ) (grow D b A : Set I) := by
  intro x y hxy
  rw [update_apply, update_apply]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [E_color_split hΦ hsep A F hF c]
  refine E_depends μ hΦc hΦ _ A F hF x y fun i hi => hxy i ?_
  have hmem : i ∈ grow D b A := by
    rcases Finset.mem_union.1 hi with h | h
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.1 h).1
    · obtain ⟨hnS, p, hip, hp⟩ := (mem_nbr D _ i).1 h
      obtain ⟨z, hz1, hz2⟩ := Finset.not_disjoint_iff.1 hp
      obtain ⟨k, hk, hzk⟩ := Finset.mem_biUnion.1 hz2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨k, by simpa using hk.2, ?_⟩)
      refine Finset.mem_union_right _ ((mem_nbr D _ i).2 ⟨fun hik => hnS ?_, p, hip,
        Finset.not_disjoint_iff.2 ⟨z, hz1, hzk⟩⟩)
      exact Finset.mem_biUnion.2 ⟨k, by simpa using hk, hik⟩
  exact_mod_cast hmem

/-- If no block meets both supports, one step does not change the pairing. -/
theorem update_pairing (hsep : ∀ k k', k ≠ k' → color k = color k' → NonInteract D (b k) (b k'))
    (A B : Finset I) (F G : C(I → X, ℝ)) (hF : DependsOn (F : (I → X) → ℝ) (A : Set I))
    (hG : DependsOn (G : (I → X) → ℝ) (B : Set I))
    (hAB : ∀ k, ¬ Disjoint (b k) A → Disjoint (b k) B) :
    (∫ U, update μ Φ hΦc b color F U * G U ∂gibbs μ Φ hΦc) = ∫ U, F U * G U ∂gibbs μ Φ hΦc := by
  have hC : (Fintype.card Color : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hone (c : Color) : (∫ U, E μ Φ hΦc (colorBlock b color c) F U * G U ∂gibbs μ Φ hΦc) =
      ∫ U, F U * G U ∂gibbs μ Φ hΦc := by
    rw [E_color_split hΦ hsep A F hF c]
    set S := (Finset.univ.filter fun k => color k = c ∧ ¬ Disjoint (b k) A).biUnion b with hS
    have hE : E μ Φ hΦc S G = G := by
      ext U
      refine E_of_outside μ hΦc _ G (fun x y h => hG fun i hi => h i fun hmem => ?_) U
      obtain ⟨k, hk, hik⟩ := Finset.mem_biUnion.1 hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact Finset.disjoint_left.1 (hAB k hk.2) hik (by exact_mod_cast hi)
    have hr := blockAverage_reversible μ (actionMap Φ hΦc) S F G
    change (∫ U, F U * E μ Φ hΦc S G U ∂gibbs μ Φ hΦc) =
      ∫ U, E μ Φ hΦc S F U * G U ∂gibbs μ Φ hΦc at hr
    rw [← hr, hE]
  have hexp (U : I → X) : update μ Φ hΦc b color F U * G U =
      (Fintype.card Color : ℝ)⁻¹ * ∑ c : Color, E μ Φ hΦc (colorBlock b color c) F U * G U := by
    rw [update_apply, mul_assoc, Finset.sum_mul]
  simp_rw [hexp]
  have hR (c : Color) : Integrable (fun U => E μ Φ hΦc (colorBlock b color c) F U * G U)
      (gibbs μ Φ hΦc) := integrable_cont _ (E μ Φ hΦc (colorBlock b color c) F * G)
  rw [integral_const_mul, integral_finset_sum Finset.univ fun c _ => hR c]
  simp only [hone, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hC, one_mul]

/-- The support of an iterate, and the invariance of the pairing, up to the first contact. -/
theorem iterate_local (hsep : ∀ k k', k ≠ k' → color k = color k' → NonInteract D (b k) (b k'))
    (A : Finset I) (F : C(I → X, ℝ)) (hF : DependsOn (F : (I → X) → ℝ) (A : Set I)) (k : ℕ) :
    DependsOn (ParallelOscillation.updateIterate (update μ Φ hΦc b color) k F : (I → X) → ℝ)
      (growN D b A k : Set I) := by
  induction k with
  | zero => exact hF
  | succ k ih => exact update_depends hΦ hsep _ _ ih

theorem iterate_pairing (hsep : ∀ k k', k ≠ k' → color k = color k' → NonInteract D (b k) (b k'))
    (A B : Finset I) (F G : C(I → X, ℝ)) (hF : DependsOn (F : (I → X) → ℝ) (A : Set I))
    (hG : DependsOn (G : (I → X) → ℝ) (B : Set I)) (k : ℕ)
    (hk : ∀ j, j < k → ∀ m, ¬ Disjoint (b m) (growN D b A j) → Disjoint (b m) B) :
    (∫ U, ParallelOscillation.updateIterate (update μ Φ hΦc b color) k F U * G U ∂gibbs μ Φ hΦc) =
      ∫ U, F U * G U ∂gibbs μ Φ hΦc := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← ih fun j hj => hk j (Nat.lt_succ_of_lt hj)]
    exact update_pairing hΦ hsep _ B _ G (iterate_local hΦ hsep A F hF k) hG (hk k (Nat.lt_succ_self k))

/-- **Clustering.** If the supports are not reached by `k` layers of blocks, the covariance of an observable `F` of
the class with any `G`, under the true Gibbs law, is at most `rate^k` times the total oscillation of `F` times
`‖G‖`. -/
theorem covariance_decay [Nonempty I] (hst : Stable μ Φ hΦc 𝓐)
    (hone : ContinuousMap.const (I → X) (1 : ℝ) ∈ 𝓐) (hc : BoxCriterionOn μ D Φ hΦc 𝓐 b κ color ε)
    (A B : Finset I) (F G : C(I → X, ℝ)) (hFA : F ∈ 𝓐) (hF : DependsOn (F : (I → X) → ℝ) (A : Set I))
    (hG : DependsOn (G : (I → X) → ℝ) (B : Set I)) (d : I → ℝ) (hFd : OscBound F d)
    (hd : ∀ i, 0 ≤ d i) (k : ℕ)
    (hk : ∀ j, j < k → ∀ m, ¬ Disjoint (b m) (growN D b A j) → Disjoint (b m) B) :
    |(∫ U, F U * G U ∂gibbs μ Φ hΦc) -
        (∫ U, F U ∂gibbs μ Φ hΦc) * ∫ U, G U ∂gibbs μ Φ hΦc| ≤
      rate Color ε ^ k * (∑ i, d i) * ‖G‖ := by
  set m := ∫ U, F U ∂gibbs μ Φ hΦc with hm
  let Ft : C(I → X, ℝ) := F - ContinuousMap.const _ m
  have hFt : DependsOn (Ft : (I → X) → ℝ) (A : Set I) := fun x y hxy => by
    change F x - m = F y - m
    rw [hF hxy]
  have hFtd : OscBound Ft d := fun j x y hxy => by
    change |(F x - m) - (F y - m)| ≤ d j
    rw [sub_sub_sub_cancel_right]
    exact hFd j x y hxy
  have hmean : (∫ U, Ft U ∂gibbs μ Φ hΦc) = 0 := by
    change (∫ U, F U - m ∂gibbs μ Φ hΦc) = 0
    rw [integral_sub (integrable_cont _ F) (integrable_const _)]
    simp [hm]
  have hcov : (∫ U, F U * G U ∂gibbs μ Φ hΦc) - m * ∫ U, G U ∂gibbs μ Φ hΦc =
      ∫ U, Ft U * G U ∂gibbs μ Φ hΦc := by
    have h1 : Integrable (fun U => F U * G U) (gibbs μ Φ hΦc) := integrable_cont _ (F * G)
    have h2 : Integrable (fun U => m * G U) (gibbs μ Φ hΦc) :=
      integrable_cont _ (ContinuousMap.const _ m * G)
    rw [← integral_const_mul, ← integral_sub h1 h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    change F U * G U - m * G U = (F U - m) * G U
    ring
  have hFtA : Ft ∈ 𝓐 := by
    have h1 : m • ContinuousMap.const (I → X) (1 : ℝ) = ContinuousMap.const _ m := by
      ext U
      simp
    exact 𝓐.sub_mem hFA (h1 ▸ 𝓐.smul_mem m hone)
  rw [hcov, ← iterate_pairing hΦ hc.separated A B Ft G hFt hG k hk]
  have hb (U : I → X) : ‖ParallelOscillation.updateIterate (update μ Φ hΦc b color) k Ft U * G U‖ ≤
      rate Color ε ^ k * (∑ i, d i) * ‖G‖ := by
    have h1 := mixing hΦ hst hc Ft hFtA d hFtd hd k U
    rw [hmean, sub_zero] at h1
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul h1 (ContinuousMap.norm_coe_le_norm G U) (norm_nonneg _)
      ((abs_nonneg _).trans h1)
  simpa using norm_integral_le_of_norm_le_const (μ := gibbs μ Φ hΦc)
    (Filter.Eventually.of_forall hb)

/-- The same bound with a constant depending only on the size of the support of `F`. -/
theorem covariance_decay_local [Nonempty I] (hst : Stable μ Φ hΦc 𝓐)
    (hone : ContinuousMap.const (I → X) (1 : ℝ) ∈ 𝓐) (hc : BoxCriterionOn μ D Φ hΦc 𝓐 b κ color ε)
    (A B : Finset I) (F G : C(I → X, ℝ)) (hFA : F ∈ 𝓐) (hF : DependsOn (F : (I → X) → ℝ) (A : Set I))
    (hG : DependsOn (G : (I → X) → ℝ) (B : Set I)) (k : ℕ)
    (hk : ∀ j, j < k → ∀ m, ¬ Disjoint (b m) (growN D b A j) → Disjoint (b m) B) :
    |(∫ U, F U * G U ∂gibbs μ Φ hΦc) -
        (∫ U, F U ∂gibbs μ Φ hΦc) * ∫ U, G U ∂gibbs μ Φ hΦc| ≤
      rate Color ε ^ k * (2 * A.card * ‖F‖) * ‖G‖ := by
  let d : I → ℝ := fun i => if i ∈ A then 2 * ‖F‖ else 0
  have hd : ∀ i, 0 ≤ d i := fun i => by
    simp only [d]
    split <;> positivity
  have hFd : OscBound F d := fun j x y hxy => by
    by_cases hj : j ∈ A
    · simp only [d, hj, if_true]
      exact ParallelOscillation.uniform_oscillation F j x y hxy
    · simp only [d, hj, if_false]
      rw [hF fun i hi => hxy i fun h => hj (h ▸ (by exact_mod_cast hi))]
      simp
  have hsum : ∑ i, d i = 2 * A.card * ‖F‖ := by
    simp only [d, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [← hsum]
  exact covariance_decay hΦ hst hone hc A B F G hFA hF hG d hFd hd k hk

omit hΦ in
theorem iterate_eq (P : C(I → X, ℝ) → C(I → X, ℝ)) (F : C(I → X, ℝ)) (k : ℕ) :
    ContinuousUpdateGap.iterate P k F = ParallelOscillation.updateIterate P k F := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [ContinuousUpdateGap.iterate, ParallelOscillation.updateIterate, ih]

/-- **A Poincaré inequality from the boxes.** For an observable of the class, `ε` times the variance under the true
Gibbs law is at most the sum of the conditional variances over the colours. The factor `ε` does not depend on the
number of coordinates. This is uniform in the volume only for `ε` and a block family fixed as the lattice grows. -/
theorem poincare [Nonempty I] (hst : Stable μ Φ hΦc 𝓐)
    (hone : ContinuousMap.const (I → X) (1 : ℝ) ∈ 𝓐) (hc : BoxCriterionOn μ D Φ hΦc 𝓐 b κ color ε)
    (F : C(I → X, ℝ)) (hFA : F ∈ 𝓐) :
    ε * ∫ U, (F U - ∫ V, F V ∂gibbs μ Φ hΦc) ^ 2 ∂gibbs μ Φ hΦc ≤
      ∑ c : Color, ∫ U, (F U - E μ Φ hΦc (colorBlock b color c) F U) ^ 2 ∂gibbs μ Φ hΦc := by
  have hCpos : (0 : ℝ) < Fintype.card Color := by exact_mod_cast Fintype.card_pos
  have hr := rate_nonneg (Color := Color) (margin_le_card hc.nonneg hc.separated hc.margin)
  set m := ∫ V, F V ∂gibbs μ Φ hΦc with hm
  let Ft : C(I → X, ℝ) := F - ContinuousMap.const _ m
  have hmean : (∫ U, Ft U ∂gibbs μ Φ hΦc) = 0 := by
    change (∫ U, F U - m ∂gibbs μ Φ hΦc) = 0
    rw [integral_sub (integrable_cont _ F) (integrable_const _)]
    simp [hm]
  have hFtA : Ft ∈ 𝓐 := by
    have h1 : m • ContinuousMap.const (I → X) (1 : ℝ) = ContinuousMap.const _ m := by
      ext U
      simp
    exact 𝓐.sub_mem hFA (h1 ▸ 𝓐.smul_mem m hone)
  set P := update μ Φ hΦc b color with hP
  -- decay of the moments of the reversible dynamics
  have hdecay (k : ℕ) : |ContinuousUpdateGap.pairing (gibbs μ Φ hΦc) Ft
      (ContinuousUpdateGap.iterate P k Ft)| ≤
        (‖Ft‖ * ∑ _i : I, 2 * ‖Ft‖) * rate Color ε ^ k := by
    rw [iterate_eq]
    unfold ContinuousUpdateGap.pairing
    have hb (U : I → X) : ‖Ft U * ParallelOscillation.updateIterate P k Ft U‖ ≤
        (‖Ft‖ * ∑ _i : I, 2 * ‖Ft‖) * rate Color ε ^ k := by
      have h1 := mixing hΦ hst hc Ft hFtA (fun _ => 2 * ‖Ft‖) (ParallelOscillation.uniform_oscillation Ft)
        (fun _ => by positivity) k U
      rw [hmean, sub_zero] at h1
      rw [norm_mul, Real.norm_eq_abs]
      calc _ ≤ ‖Ft‖ * (rate Color ε ^ k * ∑ _i : I, 2 * ‖Ft‖) :=
            mul_le_mul (ContinuousMap.norm_coe_le_norm Ft U) h1 (abs_nonneg _) (norm_nonneg _)
        _ = _ := by ring
    simpa using norm_integral_le_of_norm_le_const (μ := gibbs μ Φ hΦc)
      (Filter.Eventually.of_forall hb)
  have hgap := ContinuousUpdateGap.dirichlet_gap (gibbs μ Φ hΦc) P
    (fun F G => update_reversible b color F G) Ft (rate Color ε) _ hr hdecay
  -- identify the Dirichlet form with the sum of the residuals
  have hEt (c : Color) : E μ Φ hΦc (colorBlock b color c) Ft =
      E μ Φ hΦc (colorBlock b color c) F - ContinuousMap.const _ m := by
    change blockAverage μ (actionMap Φ hΦc) _ (F - ContinuousMap.const _ m) = _
    rw [blockAverage_sub, blockAverage_const]
  have hres (c : Color) :
      (∫ U, Ft U * (Ft U - E μ Φ hΦc (colorBlock b color c) Ft U) ∂gibbs μ Φ hΦc) =
        ∫ U, (F U - E μ Φ hΦc (colorBlock b color c) F U) ^ 2 ∂gibbs μ Φ hΦc := by
    have h := block_dirichlet_eq_residual μ (actionMap Φ hΦc) (colorBlock b color c) Ft
    refine h.trans (integral_congr_ae (Filter.Eventually.of_forall fun U => ?_))
    change (Ft U - E μ Φ hΦc (colorBlock b color c) Ft U) ^ 2 = _
    rw [hEt]
    change ((F U - m) - (E μ Φ hΦc (colorBlock b color c) F U - m)) ^ 2 = _
    ring
  have hform : (∫ U, Ft U * (Ft U - P Ft U) ∂gibbs μ Φ hΦc) =
      (Fintype.card Color : ℝ)⁻¹ * ∑ c : Color,
        ∫ U, (F U - E μ Φ hΦc (colorBlock b color c) F U) ^ 2 ∂gibbs μ Φ hΦc := by
    have hexp (U : I → X) : Ft U * (Ft U - P Ft U) = (Fintype.card Color : ℝ)⁻¹ *
        ∑ c : Color, Ft U * (Ft U - E μ Φ hΦc (colorBlock b color c) Ft U) := by
      rw [hP, update_apply]
      have hC0 := hCpos.ne'
      simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      field_simp
    simp_rw [hexp]
    have hR (c : Color) : Integrable
        (fun U => Ft U * (Ft U - E μ Φ hΦc (colorBlock b color c) Ft U)) (gibbs μ Φ hΦc) :=
      integrable_cont _ (Ft * (Ft - E μ Φ hΦc (colorBlock b color c) Ft))
    rw [integral_const_mul, integral_finset_sum Finset.univ fun c _ => hR c]
    simp only [hres]
  have hsq : (∫ U, Ft U ^ 2 ∂gibbs μ Φ hΦc) = ∫ U, (F U - m) ^ 2 ∂gibbs μ Φ hΦc := rfl
  rw [hform, hsq] at hgap
  unfold rate at hgap
  have hsimp : 1 - (1 - ε / (Fintype.card Color : ℝ)) = ε / (Fintype.card Color : ℝ) := by ring
  rw [hsimp, div_mul_eq_mul_div, div_le_iff₀ hCpos, inv_mul_eq_div, div_mul_cancel₀ _ hCpos.ne'] at hgap
  exact hgap

end Criterion

/-! ### Discharging the criterion from factor oscillations -/
section Oscillation
variable {I P X K Color : Type*} [Fintype I] [Fintype P] [DecidableEq I]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [Fintype K] [DecidableEq K] [Fintype Color] [DecidableEq Color] [Nonempty Color]
  {μ : Measure X} [IsProbabilityMeasure μ]
  {D : P → Finset I} {Φ : P → (I → X) → ℝ} {hΦc : ∀ p, Continuous (Φ p)}

/-- The total oscillation of the factors joining the boundary coordinate `j` to the box `S`, halved. -/
def kappaOf (D : P → Finset I) (w : P → ℝ) (S : Finset I) (j : I) : ℝ :=
  (∑ p ∈ Finset.univ.filter (fun p => j ∈ D p ∧ ¬ Disjoint (D p) S), w p) / 2

/-- The total boundary influence on a box, computed from factor oscillations only. -/
def bdryWeight (D : P → Finset I) (w : P → ℝ) (S : Finset I) : ℝ :=
  ∑ j ∈ nbr D S, kappaOf D w S j

/-- **Influence of a boundary coordinate on a box from the oscillations of its factors.** The conditional
laws of the box differ by at most this in the sense of the block influence inequality. It makes no use of
smallness. It is useful only when the bound is small, which at fixed box means strong coupling. -/
theorem blockInfluence_of_osc (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I)) (w : P → ℝ)
    (hw0 : ∀ p, 0 ≤ w p) (hw : FiniteFactorInfluence.OscillationBound Φ w) (S : Finset I) :
    BlockInfluence μ D Φ hΦc S (fun j _ => kappaOf D w S j) := by
  intro F _ d hF hd j hj x y hxy
  have hjS : j ∉ S := ((mem_nbr D S j).1 hj).1
  set W := ∑ p ∈ Finset.univ.filter (fun p => j ∈ D p ∧ ¬ Disjoint (D p) S), w p with hWdef
  have hW : 0 ≤ W := Finset.sum_nonneg fun p _ => hw0 p
  let G : C(I → X, ℝ) := F.comp (overwrite S x)
  let d' : I → ℝ := fun i => if i ∈ S then d i else 0
  have hG : OscBound G d' := by
    intro i V V' hV
    by_cases hi : i ∈ S
    · simp only [d', hi, if_true]
      refine hF i _ _ fun l hl => ?_
      by_cases hlS : l ∈ S
      · simp [overwrite_apply, hlS, hV l hl]
      · simp [overwrite_apply, hlS]
    · have he : overwrite S x V = overwrite S x V' := by
        funext l
        by_cases hlS : l ∈ S
        · have : l ≠ i := fun h => hi (h ▸ hlS)
          simp [overwrite_apply, hlS, hV l this]
        · simp [overwrite_apply, hlS]
      simp [d', hi, G, he]
  have hsum : ∑ i, d' i = ∑ i ∈ S, d i := by
    simp only [d', Finset.sum_ite_mem, Finset.univ_inter]
  have hGd (V V' : I → X) : |G V - G V'| ≤ ∑ i ∈ S, d i :=
    hsum ▸ ParallelOscillation.global_difference _ d' hG V V'
  haveI : Nonempty (I → X) := ⟨x⟩
  obtain ⟨c, hc, hI⟩ := ParallelOscillation.interval_of_oscillation G (∑ i ∈ S, d i) hGd
  set π := Measure.pi (fun _ : I => μ)
  let A := actionMap Φ hΦc
  let c₀ : ℝ := ∑ p, if j ∈ D p ∧ Disjoint (D p) S then Φ p x - Φ p y else 0
  have hfac (V : I → X) (p : P) :
      |Φ p (overwrite S x V) - Φ p (overwrite S y V) -
        (if j ∈ D p ∧ Disjoint (D p) S then Φ p x - Φ p y else 0)| ≤
          if j ∈ D p ∧ ¬ Disjoint (D p) S then w p else 0 := by
    by_cases hj' : j ∈ D p
    · by_cases hp : Disjoint (D p) S
      · have h1 : Φ p (overwrite S x V) = Φ p x := hΦ p fun i hi => by
          have : i ∉ S := Finset.disjoint_left.1 hp hi
          simp [overwrite_apply, this]
        have h2 : Φ p (overwrite S y V) = Φ p y := hΦ p fun i hi => by
          have : i ∉ S := Finset.disjoint_left.1 hp hi
          simp [overwrite_apply, this]
        simp [hj', hp, h1, h2]
      · simp only [hj', hp, true_and, not_false_eq_true, if_true, if_false, sub_zero]
        exact hw p _ _
    · have h1 : Φ p (overwrite S x V) = Φ p (overwrite S y V) := hΦ p fun i hi => by
        have hij : i ≠ j := fun h => hj' (h ▸ (by exact_mod_cast hi))
        by_cases hS : i ∈ S
        · simp [overwrite_apply, hS]
        · simp [overwrite_apply, hS, hxy i hij]
      simp [hj', h1]
  have hdiff (V : I → X) : A (overwrite S x V) - A (overwrite S y V) ∈ Set.Icc (c₀ - W) (c₀ + W) := by
    have he : A (overwrite S x V) - A (overwrite S y V) - c₀ =
        ∑ p, (Φ p (overwrite S x V) - Φ p (overwrite S y V) -
          (if j ∈ D p ∧ Disjoint (D p) S then Φ p x - Φ p y else 0)) := by
      change action Φ _ - action Φ _ - c₀ = _
      simp only [action, c₀, Finset.sum_sub_distrib]
    have hb : |A (overwrite S x V) - A (overwrite S y V) - c₀| ≤ W := by
      rw [he, hWdef, Finset.sum_filter]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => hfac V p)
    have := abs_le.1 hb
    constructor <;> linarith [this.1, this.2]
  have hAx : Continuous fun V => A (overwrite S x V) := A.continuous.comp (overwrite S x).continuous
  have hAy : Continuous fun V => A (overwrite S y V) := A.continuous.comp (overwrite S y).continuous
  have h := CompactGibbsOscillation.action_expectation_difference π _ _ G hAx hAy G.continuous
    (c₀ - W) (c₀ + W) c (c + ∑ i ∈ S, d i) (by linarith) hc hdiff hI
  rw [abs_sub_comm]
  refine h.trans (le_of_eq ?_)
  change _ = ∑ i ∈ S, kappaOf D w S j * d i
  rw [← Finset.mul_sum]
  unfold kappaOf
  rw [← hWdef]
  ring

/-- **The criterion holds as soon as the factor-oscillation weight of each box is below one**, for any block
family covering the coordinates with non-interacting colours. -/
theorem criterion_of_osc (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I)) (w : P → ℝ) (hw0 : ∀ p, 0 ≤ w p)
    (hw : FiniteFactorInfluence.OscillationBound Φ w) (b : K → Finset I) (color : K → Color)
    (hsep : ∀ k k', k ≠ k' → color k = color k' → NonInteract D (b k) (b k'))
    (hcover : ∀ i, ∃ k, i ∈ b k) (r : ℝ) (hr1 : r < 1) (hr : ∀ k, bdryWeight D w (b k) ≤ r) :
    BoxCriterion μ D Φ hΦc b (fun k j _ => kappaOf D w (b k) j) color (1 - r) := by
  refine ⟨fun k => blockInfluence_of_osc hΦ w hw0 hw (b k), fun k j _ => ?_, hsep, fun i => ?_⟩
  · exact div_nonneg (Finset.sum_nonneg fun p _ => hw0 p) (by norm_num)
  · obtain ⟨k₀, hk₀⟩ := hcover i
    have hrow (k : K) : row D b (fun k j _ => kappaOf D w (b k) j) k i = bdryWeight D w (b k) := rfl
    have hnn (k : K) : 0 ≤ 1 - row D b (fun k j _ => kappaOf D w (b k) j) k i := by
      rw [hrow]
      linarith [hr k]
    have hmem : k₀ ∈ Finset.univ.filter (fun k => i ∈ b k) := by simpa using hk₀
    have h := Finset.single_le_sum (f := fun k => 1 - row D b (fun k j _ => kappaOf D w (b k) j) k i)
      (fun k _ => hnn k) hmem
    refine le_trans ?_ h
    simp only [hrow]
    linarith [hr k₀]

/-- The boundary weight of a box is at most a universal multiple of its size. -/
theorem bdryWeight_le (w : P → ℝ) (W : ℝ) (hw : ∀ p, w p ≤ W) (hW : 0 ≤ W) (S : Finset I) (c t : ℕ)
    (hc : ∀ p, ¬ Disjoint (D p) S → (D p \ S).card ≤ c)
    (ht : ∀ i, (Finset.univ.filter (fun p => i ∈ D p)).card ≤ t) :
    bdryWeight D w S ≤ W / 2 * (c * t * S.card) := by
  have hstep (j : I) : kappaOf D w S j ≤ W / 2 *
      ∑ p, if j ∈ D p ∧ ¬ Disjoint (D p) S then (1 : ℝ) else 0 := by
    unfold kappaOf
    rw [Finset.sum_filter, div_mul_eq_mul_div, Finset.mul_sum]
    refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun p _ => ?_) (by norm_num)
    split
    · simpa using hw p
    · simp
  have hswap : (∑ j ∈ nbr D S, ∑ p, if j ∈ D p ∧ ¬ Disjoint (D p) S then (1 : ℝ) else 0) ≤
      ∑ p, if ¬ Disjoint (D p) S then (c : ℝ) else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun p _ => ?_
    by_cases hp : Disjoint (D p) S
    · simp [hp]
    · simp only [hp, not_false_eq_true, and_true, if_true]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hsub : (nbr D S).filter (fun j => j ∈ D p) ⊆ D p \ S := by
        intro j hj
        obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hj
        exact Finset.mem_sdiff.2 ⟨h2, ((mem_nbr D S j).1 h1).1⟩
      exact_mod_cast (Finset.card_le_card hsub).trans (hc p hp)
  have htouch : (∑ p, if ¬ Disjoint (D p) S then (1 : ℝ) else 0) ≤ t * S.card := by
    classical
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hsub : (Finset.univ.filter fun p => ¬ Disjoint (D p) S) ⊆
        S.biUnion fun i => Finset.univ.filter (fun p => i ∈ D p) := by
      intro p hp
      obtain ⟨z, hz1, hz2⟩ := Finset.not_disjoint_iff.1 (Finset.mem_filter.1 hp).2
      exact Finset.mem_biUnion.2 ⟨z, hz2, Finset.mem_filter.2 ⟨Finset.mem_univ _, hz1⟩⟩
    have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have hle : ∑ i ∈ S, (Finset.univ.filter (fun p => i ∈ D p)).card ≤ S.card * t := by
      simpa using Finset.sum_le_card_nsmul _ _ t fun i _ => ht i
    have : (Finset.univ.filter fun p => ¬ Disjoint (D p) S).card ≤ S.card * t := hcard.trans hle
    calc _ ≤ ((S.card * t : ℕ) : ℝ) := by exact_mod_cast this
      _ = _ := by push_cast; ring
  have hc' : (∑ p, if ¬ Disjoint (D p) S then (c : ℝ) else 0) ≤ c * (t * S.card) := by
    have : (∑ p, if ¬ Disjoint (D p) S then (c : ℝ) else 0) =
        c * ∑ p, if ¬ Disjoint (D p) S then (1 : ℝ) else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      split <;> simp
    rw [this]
    exact mul_le_mul_of_nonneg_left htouch (Nat.cast_nonneg _)
  unfold bdryWeight
  calc _ ≤ ∑ j ∈ nbr D S, (W / 2 * ∑ p, if j ∈ D p ∧ ¬ Disjoint (D p) S then (1 : ℝ) else 0) :=
        Finset.sum_le_sum fun j _ => hstep j
    _ = W / 2 * ∑ j ∈ nbr D S, ∑ p, if j ∈ D p ∧ ¬ Disjoint (D p) S then (1 : ℝ) else 0 :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ W / 2 * (c * (t * S.card)) :=
        mul_le_mul_of_nonneg_left (hswap.trans hc') (by positivity)
    _ = _ := by ring

end Oscillation

/-! ### A map preserving the factors touching a box gives a lower bound on every block influence -/
section Symmetry
variable {I P X : Type*} [Fintype I] [Fintype P] [DecidableEq I]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsProbabilityMeasure μ]
  {D : P → Finset I} {Φ : P → (I → X) → ℝ} {hΦc : ∀ p, Continuous (Φ p)}

omit [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] in
/-- Changing the coordinates in `J` costs at most the oscillations in `J`. -/
theorem osc_finset {G : (I → X) → ℝ} {g : I → ℝ} (hG : OscBound G g) (J : Finset I) (x y : I → X)
    (h : ∀ j, j ∉ J → x j = y j) : |G x - G y| ≤ ∑ j ∈ J, g j := by
  let H : (I → X) → ℝ := fun z => G fun i => if i ∈ J then z i else y i
  let g' : I → ℝ := fun i => if i ∈ J then g i else 0
  have hH : OscBound H g' := by
    intro i u v huv
    by_cases hi : i ∈ J
    · simp only [g', hi, if_true]
      refine hG i _ _ fun l hl => ?_
      by_cases hlJ : l ∈ J
      · simp [hlJ, huv l hl]
      · simp [hlJ]
    · have he : (fun l => if l ∈ J then u l else y l) = fun l => if l ∈ J then v l else y l := by
        funext l
        by_cases hlJ : l ∈ J
        · have : l ≠ i := fun e => hi (e ▸ hlJ)
          simp [hlJ, huv l this]
        · simp [hlJ]
      simp [H, g', hi, he]
  have hx : H x = G x := by
    change G _ = G x
    congr 1
    funext l
    by_cases hl : l ∈ J
    · simp [hl]
    · simp [hl, h l hl]
  have hy : H y = G y := by
    change G _ = G y
    congr 1
    funext l
    by_cases hl : l ∈ J <;> simp [hl]
  have := ParallelOscillation.global_difference H g' hH x y
  rw [hx, hy] at this
  simpa only [g', Finset.sum_ite_mem, Finset.univ_inter] using this

/-- The conditional law as a normalized Haar integral. -/
theorem fiber_integral (R : Finset I) (W : I → X) (G : (I → X) → ℝ) :
    (∫ V, G V ∂fiber μ Φ hΦc R W) =
      (∫ V, Real.exp (-actionMap Φ hΦc (overwrite R W V)) * G V ∂Measure.pi (fun _ : I => μ)) /
        ∫ V, Real.exp (-actionMap Φ hΦc (overwrite R W V)) ∂Measure.pi (fun _ : I => μ) := by
  have hc := (actionMap Φ hΦc).continuous.comp (overwrite R W).continuous
  exact LocalGibbsComparison.weighted_integral _ _ (Real.continuous_exp.comp hc.neg).measurable
    (fun _ => (Real.exp_pos _).le) (CompactGibbsContinuity.partition_positive _ _ hc) G

/-- **A map commuting with overwriting transports the block update.** It need not preserve the whole action: the
factors touching the box are enough, since the others do not see the box coordinates. -/
theorem E_symm (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I)) (T : C(I → X, I → X))
    (hpres : (Measure.pi (fun _ : I => μ)).map T = Measure.pi (fun _ : I => μ)) (S : Finset I)
    (hA : ∀ p, ¬ Disjoint (D p) S → ∀ U, Φ p (T U) = Φ p U)
    (hov : ∀ x V : I → X, overwrite S (T x) (T V) = T (overwrite S x V)) (F : C(I → X, ℝ))
    (x : I → X) : E μ Φ hΦc S F (T x) = E μ Φ hΦc S (F.comp T) x := by
  classical
  have hint (H : C(I → X, ℝ)) : (∫ V, H V ∂Measure.pi (fun _ : I => μ)) =
      ∫ V, H (T V) ∂Measure.pi (fun _ : I => μ) := by
    conv_lhs => rw [← hpres]
    exact integral_map T.continuous.aemeasurable H.continuous.aestronglyMeasurable
  have hAc := (actionMap Φ hΦc).continuous
  -- the untouched factors contribute a constant
  let c : ℝ := ∑ p, if Disjoint (D p) S then Φ p (T x) - Φ p x else 0
  have hstep (V : I → X) (p : P) : Φ p (T (overwrite S x V)) =
      (if Disjoint (D p) S then Φ p (T x) - Φ p x else 0) + Φ p (overwrite S x V) := by
    by_cases hp : Disjoint (D p) S
    · have h1 : Φ p (T (overwrite S x V)) = Φ p (T x) := hΦ p (fun i hi => by
        have hi' : i ∉ S := Finset.disjoint_left.1 hp (by exact_mod_cast hi)
        rw [← hov]
        simp [overwrite_apply, hi'])
      have h2 : Φ p (overwrite S x V) = Φ p x := hΦ p (fun i hi => by
        have hi' : i ∉ S := Finset.disjoint_left.1 hp (by exact_mod_cast hi)
        simp [overwrite_apply, hi'])
      rw [h1, h2, if_pos hp]
      ring
    · rw [if_neg hp, zero_add]
      exact hA p hp _
  have hshift (V : I → X) : actionMap Φ hΦc (T (overwrite S x V)) =
      c + actionMap Φ hΦc (overwrite S x V) := by
    change action Φ _ = c + action Φ _
    simp only [action, c, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p _ => hstep V p)
  rw [E_apply, E_apply, fiber_integral, fiber_integral]
  let N : C(I → X, ℝ) := ⟨fun V => Real.exp (-actionMap Φ hΦc (overwrite S (T x) V)) *
    F (overwrite S (T x) V), (Real.continuous_exp.comp (hAc.comp
      (overwrite S (T x)).continuous).neg).mul (F.continuous.comp (overwrite S (T x)).continuous)⟩
  let M : C(I → X, ℝ) := ⟨fun V => Real.exp (-actionMap Φ hΦc (overwrite S (T x) V)),
    Real.continuous_exp.comp (hAc.comp (overwrite S (T x)).continuous).neg⟩
  have h1 := hint N
  have h2 := hint M
  change (∫ V, Real.exp (-actionMap Φ hΦc (overwrite S (T x) V)) * F (overwrite S (T x) V) ∂_) =
    ∫ V, Real.exp (-actionMap Φ hΦc (overwrite S (T x) (T V))) * F (overwrite S (T x) (T V)) ∂_ at h1
  change (∫ V, Real.exp (-actionMap Φ hΦc (overwrite S (T x) V)) ∂_) =
    ∫ V, Real.exp (-actionMap Φ hΦc (overwrite S (T x) (T V))) ∂_ at h2
  rw [h1, h2]
  simp only [hov, hshift, neg_add, Real.exp_add, mul_assoc, ContinuousMap.comp_apply]
  rw [integral_const_mul, integral_const_mul, mul_div_mul_left _ _ (Real.exp_pos _).ne']

/-- **Lower bound on block influence.** If a map commuting with overwriting preserves the factors touching the box,
reverses the sign of an observable of the class, and moves the boundary condition `x` only on `J`, and the
observable does not see `J` outside the box, then the influence of `J` on the box is at least the size of the
conditional expectation at `x`. This holds at every coupling. -/
theorem antisym_bound (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I)) {𝓐 : Submodule ℝ C(I → X, ℝ)} {S : Finset I}
    {κ : I → I → ℝ} (hinf : BlockInfluenceOn μ D Φ hΦc 𝓐 S κ) (T : C(I → X, I → X))
    (hpres : (Measure.pi (fun _ : I => μ)).map T = Measure.pi (fun _ : I => μ))
    (hA : ∀ p, ¬ Disjoint (D p) S → ∀ U, Φ p (T U) = Φ p U)
    (hov : ∀ x V : I → X, overwrite S (T x) (T V) = T (overwrite S x V))
    (F : C(I → X, ℝ)) (hFA : F ∈ 𝓐) (d : I → ℝ) (hF : OscBound F d) (hd : ∀ i, 0 ≤ d i)
    (hanti : ∀ U, F (T U) = -F U) (J : Finset I) (hd0 : ∀ j ∈ J, j ∉ S → d j = 0) (x : I → X)
    (hJ : ∀ j, j ∉ J → T x j = x j) :
    2 * |E μ Φ hΦc S F x| ≤ ∑ j ∈ J, if j ∈ nbr D S then ∑ i ∈ S, κ j i * d i else 0 := by
  have h1 := E_osc hΦ hinf F hFA d hF hd
  have h2 : E μ Φ hΦc S F (T x) = -E μ Φ hΦc S F x := by
    rw [E_symm hΦ T hpres S hA hov F x, E_apply, E_apply, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
    exact hanti _
  have h3 := osc_finset h1 J (T x) x hJ
  rw [h2] at h3
  have h4 : |(-E μ Φ hΦc S F x) - E μ Φ hΦc S F x| = 2 * |E μ Φ hΦc S F x| := by
    rw [show (-E μ Φ hΦc S F x) - E μ Φ hΦc S F x = -(2 * E μ Φ hΦc S F x) by ring, abs_neg, abs_mul]
    simp
  rw [h4] at h3
  refine h3.trans (le_of_eq (Finset.sum_congr rfl fun j hjJ => ?_))
  unfold stepBound
  by_cases hj : j ∈ S
  · have : j ∉ nbr D S := fun h => ((mem_nbr D S j).1 h).1 hj
    simp [hj, this]
  · simp [hj, hd0 j hjJ hj]

end Symmetry

/-! ### The twisted law -/
section Twisted
open PeriodicLattice4 WilsonIndependentBlocks RegulatedGauge PeriodicPlaquetteReflection
open PeriodicTimeReflection TwistedReflection
open WilsonSingleLinkStaples (Q character character_continuous)
open WilsonCoordinateInfluence (toConfiguration)

variable (n : ℕ) [NeZero n]

local instance linkDecidableEq : DecidableEq (Link (2 * n)) := Classical.decEq _
local instance plaqDecidableEq : DecidableEq (PlaquetteIndex (2 * n)) := Classical.decEq _

/-- One plaquette factor of the twisted action in positive-link coordinates. -/
def twFactor (β : ℝ) (p : PlaquetteIndex (2 * n)) (U : Link (2 * n) → Q) : ℝ :=
  β * TwistedReflection.term n Q (spatialTwist n) character 2 (toConfiguration (2 * n) U) p

/-- The four links of a plaquette. -/
abbrev twSupp (p : PlaquetteIndex (2 * n)) : Finset (Link (2 * n)) :=
  WilsonInfluenceGeometry.incidentLinks (2 * n) p

theorem plaq_coord (U : Link (2 * n) → Q) (x : Vertex (2 * n)) (μ ν : Fin 4) :
    plaquetteProduct (2 * n) Q (toConfiguration (2 * n) U) x μ ν =
      U (x, μ) * U (step (2 * n) x μ, ν) * (U (step (2 * n) x ν, μ))⁻¹ * (U (x, ν))⁻¹ := rfl

theorem toConfiguration_continuous :
    Continuous (toConfiguration (2 * n) : (Link (2 * n) → Q) → _) :=
  continuous_pi fun e => continuous_apply (edgeCoord (2 * n) e)

theorem twFactor_continuous (β : ℝ) (p : PlaquetteIndex (2 * n)) : Continuous (twFactor n β p) :=
  continuous_const.mul ((continuous_term n Q (spatialTwist n) character character_continuous 2 p).comp
    (toConfiguration_continuous n))

theorem twFactor_depends (β : ℝ) (p : PlaquetteIndex (2 * n)) :
    DependsOn (twFactor n β p) (twSupp n p : Set (Link (2 * n))) := by
  intro U V h
  have h1 : U (p.1, p.2.1.1) = V (p.1, p.2.1.1) := h _ (by simp [WilsonInfluenceGeometry.incidentLinks])
  have h2 : U (step (2 * n) p.1 p.2.1.1, p.2.1.2) = V (step (2 * n) p.1 p.2.1.1, p.2.1.2) :=
    h _ (by simp [WilsonInfluenceGeometry.incidentLinks])
  have h3 : U (step (2 * n) p.1 p.2.1.2, p.2.1.1) = V (step (2 * n) p.1 p.2.1.2, p.2.1.1) :=
    h _ (by simp [WilsonInfluenceGeometry.incidentLinks])
  have h4 : U (p.1, p.2.1.2) = V (p.1, p.2.1.2) := h _ (by simp [WilsonInfluenceGeometry.incidentLinks])
  unfold twFactor TwistedReflection.term
  rw [plaq_coord, plaq_coord, h1, h2, h3, h4]

/-- The sum of the factors is the literal twisted action. -/
theorem twAction_eq (β : ℝ) (U : Link (2 * n) → Q) :
    actionMap (twFactor n β) (twFactor_continuous n β) U =
      TwistedReflection.action n Q (spatialTwist n) character β 2 (toConfiguration (2 * n) U) := by
  change FiniteFactorConditional.action _ U = _
  simp only [FiniteFactorConditional.action, twFactor, TwistedReflection.action, Finset.mul_sum]

/-- The coordinate Gibbs law is the twisted law. -/
theorem twGibbs_integral (β : ℝ) (F : Configuration (Vertex (2 * n)) Q → ℝ) :
    (∫ U, F (toConfiguration (2 * n) U)
      ∂gibbs SU2HaarTilt.haar (twFactor n β) (twFactor_continuous n β)) =
      ∫ U, F U ∂TwistedLocalization.twistedLaw n β := by
  have hS := TwistedReflection.continuous_action n Q (spatialTwist n) character character_continuous β 2
  have h := WilsonCoordinateLaw.gibbs_preserving (2 * n)
    (TwistedReflection.action n Q (spatialTwist n) character β 2) hS
  have hact : (actionMap (twFactor n β) (twFactor_continuous n β) : (Link (2 * n) → Q) → ℝ) =
      fun U => TwistedReflection.action n Q (spatialTwist n) character β 2 (toConfiguration (2 * n) U) :=
    funext (twAction_eq n β)
  have := h.integral_comp (WilsonCoordinateLaw.configEquiv (2 * n)).measurableEmbedding F
  change (∫ U, F (WilsonCoordinateLaw.configEquiv (2 * n) U) ∂_) = _ at this
  simp only [WilsonCoordinateLaw.configEquiv_eq_toConfiguration] at this
  unfold gibbs FiniteFactorContraction.law
  rw [hact]
  exact this

/-- Each plaquette factor has oscillation at most `4β`. -/
theorem twFactor_osc (β : ℝ) (hβ : 0 ≤ β) :
    FiniteFactorInfluence.OscillationBound (twFactor n β) (fun _ => 4 * β) := by
  intro p U V
  have hre (g : Q) : -2 ≤ (character g).re ∧ (character g).re ≤ 2 := by
    have h := WilsonSlabBounds.characterDefect_bounds g
    constructor <;> linarith [h.1, h.2]
  have hz : spatialTwist n p = 1 ∨ spatialTwist n p = -1 := by
    unfold spatialTwist
    split <;> simp
  unfold twFactor TwistedReflection.term
  have hU := hre (plaquetteProduct (2 * n) Q (toConfiguration (2 * n) U) p.1 p.2.1.1 p.2.1.2)
  have hV := hre (plaquetteProduct (2 * n) Q (toConfiguration (2 * n) V) p.1 p.2.1.1 p.2.1.2)
  rw [← mul_sub, abs_mul, abs_of_nonneg hβ, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ hβ
  rw [abs_le]
  rcases hz with hz | hz <;> rw [hz] <;> constructor <;> linarith [hU.1, hU.2, hV.1, hV.2]

/-- A plaquette touching a box has at most three links outside it. -/
theorem twSupp_outside (S : Finset (Link (2 * n))) (p : PlaquetteIndex (2 * n))
    (hp : ¬ Disjoint (twSupp n p) S) : (twSupp n p \ S).card ≤ 3 := by
  obtain ⟨z, hz1, hz2⟩ := Finset.not_disjoint_iff.1 hp
  have hsub : twSupp n p \ S ⊆ (twSupp n p).erase z := by
    intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hi
    exact Finset.mem_erase.2 ⟨fun h => h2 (h ▸ hz2), h1⟩
  have hcard : (twSupp n p).card ≤ 4 := Finset.card_le_four
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hz1] at this
  omega

/-- A link is in at most six plaquettes. -/
theorem twSupp_touching (i : Link (2 * n)) :
    (Finset.univ.filter fun p => i ∈ twSupp n p).card ≤ 6 := by
  have hsub : (Finset.univ.filter fun p => i ∈ twSupp n p) ⊆
      SingleLinkWilsonOscillation.affected (2 * n) i.1 i.2 := by
    intro p hp
    obtain ⟨-, h⟩ := Finset.mem_filter.1 hp
    exact (WilsonInfluenceGeometry.affected_iff_incident (2 * n) p i).2
      ((WilsonInfluenceGeometry.mem_incidentLinks (2 * n) p i).1 h)
  exact (Finset.card_le_card hsub).trans (SingleLinkWilsonOscillation.affected_card (2 * n) _ _)

/-- **The boundary weight of a box on the twisted lattice is at most `36 β |S|`.** At `|S| = 1` this is the
known single-link threshold `β < 1/36`. -/
theorem twBdry_le (β : ℝ) (hβ : 0 ≤ β) (S : Finset (Link (2 * n))) :
    bdryWeight (twSupp n) (fun _ => 4 * β) S ≤ 36 * β * S.card := by
  have h := bdryWeight_le (D := twSupp n) (fun _ => 4 * β) (4 * β) (fun _ => le_rfl) (by positivity) S 3 6
    (twSupp_outside n S) (twSupp_touching n)
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

variable {K Color : Type*} [Fintype K] [DecidableEq K] [Fintype Color] [DecidableEq Color]
  [Nonempty Color]

/-- **The finite-box criterion holds at strong coupling for the actual twisted law**, for any covering
family of boxes of size at most `m` and any non-interacting colouring, whenever `36 β m < 1`. The margin
`1 - 36 β m` depends on neither the lattice size nor the twist. -/
theorem twisted_criterion (β : ℝ) (hβ : 0 ≤ β) (b : K → Finset (Link (2 * n))) (color : K → Color)
    (hsep : ∀ k k', k ≠ k' → color k = color k' → NonInteract (twSupp n) (b k) (b k'))
    (hcover : ∀ i, ∃ k, i ∈ b k) (m : ℕ) (hm : ∀ k, (b k).card ≤ m) (hsmall : 36 * β * m < 1) :
    BoxCriterion SU2HaarTilt.haar (twSupp n) (twFactor n β) (twFactor_continuous n β) b
      (fun k j _ => kappaOf (twSupp n) (fun _ => 4 * β) (b k) j) color (1 - 36 * β * m) :=
  criterion_of_osc (twFactor_depends n β) (fun _ => 4 * β) (fun _ => by positivity)
    (twFactor_osc n β hβ) b color hsep hcover _ hsmall fun k =>
    (twBdry_le n β hβ (b k)).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hm k) (by positivity))

/-! ### A concrete family: the links at a vertex -/

/-- Being at most one step forward from `y` in each coordinate. -/
def Near (y u : Vertex (2 * n)) : Prop := ∀ κ, u κ - y κ = 0 ∨ u κ - y κ = 1

/-- The torus distance, in the form of a predicate. -/
def Close (r : ℕ) (x y : Vertex (2 * n)) : Prop := ∀ κ, (x κ - y κ).valMinAbs.natAbs ≤ r

omit [NeZero n] in
theorem near_self (y : Vertex (2 * n)) : Near n y y := fun κ => by simp

omit [NeZero n] in
theorem near_step (y : Vertex (2 * n)) (ρ : Fin 4) : Near n y (step (2 * n) y ρ) := fun κ => by
  by_cases h : κ = ρ
  · subst h
    simp [step]
  · simp [step, Pi.single_apply, h]

omit [NeZero n] in
theorem near_step2 (y : Vertex (2 * n)) (μ ν : Fin 4) (hμν : μ ≠ ν) :
    Near n y (step (2 * n) (step (2 * n) y μ) ν) := fun κ => by
  by_cases h1 : κ = μ
  · subst h1
    simp [step, Pi.single_apply, hμν]
  · by_cases h2 : κ = ν
    · subst h2
      simp [step, Pi.single_apply, h1]
    · simp [step, Pi.single_apply, h1, h2]

theorem close_mono {r s : ℕ} (h : r ≤ s) {x y : Vertex (2 * n)} (hc : Close n r x y) :
    Close n s x y := fun κ => (hc κ).trans h

theorem close_symm {r : ℕ} {x y : Vertex (2 * n)} (hc : Close n r x y) : Close n r y x := fun κ => by
  have := hc κ
  rwa [← neg_sub, ZMod.natAbs_valMinAbs_neg]

theorem close_trans {r s : ℕ} {x y z : Vertex (2 * n)} (h1 : Close n r x y) (h2 : Close n s y z) :
    Close n (r + s) x z := fun κ => by
  have he : x κ - z κ = (x κ - y κ) + (y κ - z κ) := by ring
  rw [he]
  refine (ZMod.natAbs_valMinAbs_add_le _ _).trans ?_
  exact (Int.natAbs_add_le _ _).trans (add_le_add (h1 κ) (h2 κ))

theorem natAbs_one_le : (1 : ZMod (2 * n)).valMinAbs.natAbs ≤ 1 := by
  rw [ZMod.valMinAbs_natAbs_eq_min]
  exact (min_le_left _ _).trans (le_of_eq (ZMod.val_one'' (by omega)))

theorem near_close {y a c : Vertex (2 * n)} (h1 : Near n y a) (h2 : Near n y c) : Close n 1 a c := by
  intro κ
  have he : a κ - c κ = (a κ - y κ) - (c κ - y κ) := by ring
  rw [he]
  rcases h1 κ with h | h <;> rcases h2 κ with h' | h' <;> rw [h, h']
  · simp
  · rw [zero_sub, ZMod.natAbs_valMinAbs_neg]
    exact natAbs_one_le n
  · simpa using natAbs_one_le n
  · simp

theorem near_cast (h4 : 4 ∣ 2 * n) {y a c : Vertex (2 * n)} (h1 : Near n y a) (h2 : Near n y c)
    (hcast : ∀ κ, ZMod.castHom h4 (ZMod 4) (a κ) = ZMod.castHom h4 (ZMod 4) (c κ)) : a = c := by
  funext κ
  have he : a κ - c κ = (a κ - y κ) - (c κ - y κ) := by ring
  have hz : ZMod.castHom h4 (ZMod 4) (a κ - c κ) = 0 := by
    rw [map_sub, hcast κ, sub_self]
  rw [he] at hz
  have h10 : (1 : ZMod 4) ≠ 0 := by decide
  have hm10 : (-1 : ZMod 4) ≠ 0 := by decide
  have hzero : a κ - c κ = 0 := by
    rw [he]
    rcases h1 κ with h | h <;> rcases h2 κ with h' | h' <;> rw [h, h'] at hz ⊢
    · simp
    · simp only [zero_sub, map_neg, map_one] at hz
      exact absurd hz hm10
    · simp only [sub_zero, map_one] at hz
      exact absurd hz h10
    · simp
  exact sub_eq_zero.1 hzero

/-- The links at a vertex. -/
def star (v : Vertex (2 * n)) : Finset (Link (2 * n)) :=
  Finset.univ.filter fun i => i.1 = v ∨ step (2 * n) i.1 i.2 = v

theorem mem_star (v : Vertex (2 * n)) (i : Link (2 * n)) :
    i ∈ star n v ↔ i.1 = v ∨ step (2 * n) i.1 i.2 = v := by
  simp [star]

theorem star_near (v : Vertex (2 * n)) (i : Link (2 * n)) (h : i ∈ star n v) : Near n i.1 v := by
  rcases (mem_star n v i).1 h with h | h
  · rw [← h]
    exact near_self n _
  · rw [← h]
    exact near_step n _ _

theorem star_card (v : Vertex (2 * n)) : (star n v).card ≤ 8 := by
  classical
  let f : Fin 4 × Bool → Link (2 * n) := fun z =>
    if z.2 then (v, z.1) else (v - Pi.single z.1 1, z.1)
  have hsub : star n v ⊆ Finset.univ.image f := by
    intro i hi
    refine Finset.mem_image.2 ?_
    rcases (mem_star n v i).1 hi with h | h
    · exact ⟨(i.2, true), Finset.mem_univ _, by simp [f, ← h]⟩
    · refine ⟨(i.2, false), Finset.mem_univ _, ?_⟩
      simp only [f, Bool.false_eq_true, if_false]
      ext1
      · rw [← h]
        simp [step]
      · rfl
  have := (Finset.card_le_card hsub).trans Finset.card_image_le
  simpa using this

/-- The base and endpoint of a link of a plaquette are near its base. -/
theorem incident_near (p : PlaquetteIndex (2 * n)) (i : Link (2 * n)) (hi : i ∈ twSupp n p) :
    Near n p.1 i.1 ∧ Near n p.1 (step (2 * n) i.1 i.2) := by
  have hne : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
  rcases (WilsonInfluenceGeometry.mem_incidentLinks (2 * n) p i).1 hi with h | h | h | h
  · subst h
    exact ⟨near_self n _, near_step n _ _⟩
  · subst h
    exact ⟨near_step n _ _, near_step2 n _ _ _ hne⟩
  · subst h
    refine ⟨near_step n _ _, ?_⟩
    change Near n p.1 (step (2 * n) (step (2 * n) p.1 p.2.1.2) p.2.1.1)
    rw [step_comm]
    exact near_step2 n _ _ _ hne
  · subst h
    exact ⟨near_self n _, near_step n _ _⟩

theorem star_plaq_near (v : Vertex (2 * n)) (p : PlaquetteIndex (2 * n))
    (hp : ¬ Disjoint (twSupp n p) (star n v)) : Near n p.1 v := by
  obtain ⟨i, hi, hiv⟩ := Finset.not_disjoint_iff.1 hp
  rcases (mem_star n v i).1 hiv with h | h
  · rw [← h]
    exact (incident_near n p i hi).1
  · rw [← h]
    exact (incident_near n p i hi).2

/-- Colour a vertex by its coordinates mod 4. -/
def starColor (h4 : 4 ∣ 2 * n) (v : Vertex (2 * n)) : Fin 4 → ZMod 4 :=
  fun κ => ZMod.castHom h4 (ZMod 4) (v κ)

theorem star_sep (h4 : 4 ∣ 2 * n) (v v' : Vertex (2 * n)) (hne : v ≠ v')
    (hc : starColor n h4 v = starColor n h4 v') : NonInteract (twSupp n) (star n v) (star n v') := by
  have hcast : ∀ κ, ZMod.castHom h4 (ZMod 4) (v κ) = ZMod.castHom h4 (ZMod 4) (v' κ) :=
    fun κ => congrFun hc κ
  refine ⟨?_, fun p => ?_⟩
  · rw [Finset.disjoint_left]
    intro i h1 h2
    exact hne (near_cast n h4 (star_near n v i h1) (star_near n v' i h2) hcast)
  · by_contra hcon
    push_neg at hcon
    exact hne (near_cast n h4 (star_plaq_near n v p hcon.1) (star_plaq_near n v' p hcon.2) hcast)

theorem star_cover (i : Link (2 * n)) : ∃ v, i ∈ star n v :=
  ⟨i.1, (mem_star n _ i).2 (Or.inl rfl)⟩

/-- The rate of the star criterion at strong coupling. -/
def starRate (β : ℝ) : ℝ := rate (Fin 4 → ZMod 4) (1 - 288 * β)

theorem starRate_lt_one (β : ℝ) (hs : 288 * β < 1) : starRate β < 1 :=
  rate_lt_one (by linarith)

/-- The criterion for the links at each vertex, at `β < 1/288`, when `4` divides the side `2n`. -/
theorem star_criterion (h4 : 4 ∣ 2 * n) (β : ℝ) (hβ : 0 ≤ β) (hs : 288 * β < 1) :
    BoxCriterion SU2HaarTilt.haar (twSupp n) (twFactor n β) (twFactor_continuous n β) (star n)
      (fun k j _ => kappaOf (twSupp n) (fun _ => 4 * β) (star n k) j) (starColor n h4)
      (1 - 288 * β) := by
  have h := twisted_criterion n β hβ (star n) (starColor n h4) (star_sep n h4) (star_cover n) 8
    (star_card n) (by norm_num; linarith)
  have he : 36 * β * ((8 : ℕ) : ℝ) = 288 * β := by norm_num; ring
  rwa [he] at h

/-! ### Exponential clustering in the torus distance -/

theorem growN_close (A : Finset (Link (2 * n))) (j : ℕ) (i : Link (2 * n))
    (hi : i ∈ growN (twSupp n) (star n) A j) : ∃ a ∈ A, Close n (2 * j) i.1 a.1 := by
  induction j generalizing i with
  | zero =>
    refine ⟨i, hi, fun κ => by simp⟩
  | succ j ih =>
    change i ∈ grow (twSupp n) (star n) (growN (twSupp n) (star n) A j) at hi
    rcases Finset.mem_union.1 hi with h | h
    · obtain ⟨a, ha, hc⟩ := ih i h
      exact ⟨a, ha, close_mono n (by omega) hc⟩
    · obtain ⟨m, hm, hmem⟩ := Finset.mem_biUnion.1 h
      have hm' := (Finset.mem_filter.1 hm).2
      obtain ⟨i', hi'1, hi'2⟩ := Finset.not_disjoint_iff.1 hm'
      obtain ⟨a, ha, hc⟩ := ih i' hi'2
      refine ⟨a, ha, ?_⟩
      have h1 : Close n 1 m i'.1 := near_close n (star_near n m i' hi'1) (near_self n _)
      have h2 : Close n 1 i.1 m := by
        rcases Finset.mem_union.1 hmem with h3 | h3
        · exact close_symm n (near_close n (star_near n m i h3) (near_self n _))
        · obtain ⟨-, p, hip, hp⟩ := (mem_nbr _ _ i).1 h3
          exact near_close n (incident_near n p i hip).1 (star_plaq_near n m p hp)
      have := close_trans n (close_trans n h2 h1) hc
      exact close_mono n (by omega) this

/-- Far supports are not joined by any star within `k` layers. -/
theorem star_far (A B : Finset (Link (2 * n))) (k : ℕ)
    (hfar : ∀ a ∈ A, ∀ c ∈ B, ¬ Close n (2 * k) a.1 c.1) :
    ∀ j, j < k → ∀ m, ¬ Disjoint (star n m) (growN (twSupp n) (star n) A j) → Disjoint (star n m) B := by
  intro j hj m hm
  rw [Finset.disjoint_left]
  intro c hc hcB
  obtain ⟨i, hi1, hi2⟩ := Finset.not_disjoint_iff.1 hm
  obtain ⟨a, ha, hac⟩ := growN_close n A j i hi2
  refine hfar a ha c hcB ?_
  have h1 : Close n 1 i.1 m := close_symm n (near_close n (star_near n m i hi1) (near_self n _))
  have h2 : Close n 1 m c.1 := near_close n (star_near n m c hc) (near_self n _)
  have h3 := close_trans n (close_trans n (close_symm n hac) h1) h2
  exact close_mono n (by omega) h3

/-- **Exponential clustering of the actual twisted law at strong coupling, uniform in the volume.** The block family
is the links at a vertex, fixed as `n` grows. The rate depends only on `β`. The constant depends only on the size of
the support of `F`. -/
theorem twisted_covariance (h4 : 4 ∣ 2 * n) (β : ℝ) (hβ : 0 ≤ β) (hs : 288 * β < 1)
    (A B : Finset (Link (2 * n))) (F G : C(Link (2 * n) → Q, ℝ))
    (hF : DependsOn (F : (Link (2 * n) → Q) → ℝ) (A : Set (Link (2 * n))))
    (hG : DependsOn (G : (Link (2 * n) → Q) → ℝ) (B : Set (Link (2 * n)))) (k : ℕ)
    (hfar : ∀ a ∈ A, ∀ c ∈ B, ¬ Close n (2 * k) a.1 c.1) :
    |(∫ U, F U * G U ∂gibbs SU2HaarTilt.haar (twFactor n β) (twFactor_continuous n β)) -
        (∫ U, F U ∂gibbs SU2HaarTilt.haar (twFactor n β) (twFactor_continuous n β)) *
          ∫ U, G U ∂gibbs SU2HaarTilt.haar (twFactor n β) (twFactor_continuous n β)| ≤
      starRate β ^ k * (2 * A.card * ‖F‖) * ‖G‖ :=
  covariance_decay_local (twFactor_depends n β) (stable_top _ _ _) Submodule.mem_top
    (star_criterion n h4 β hβ hs) A B F G Submodule.mem_top hF hG k (star_far n A B k hfar)

/-! ### Center flips of the lattice -/

open TwistedFlat (ω ω_commute ω_coe flatLink)

def sgn (R : Finset (Vertex (2 * n))) (w : Vertex (2 * n)) : Q := if w ∈ R then ω else 1

/-- The sign picked up by a link when the vertices of `R` are flipped. -/
def flipCoef (R : Finset (Vertex (2 * n))) (i : Link (2 * n)) : Q :=
  sgn n R i.1 * sgn n R (step (2 * n) i.1 i.2)

/-- The links with exactly one endpoint in `R`. -/
def cross (R : Finset (Vertex (2 * n))) : Finset (Link (2 * n)) :=
  Finset.univ.filter fun i => ¬ (i.1 ∈ R ↔ step (2 * n) i.1 i.2 ∈ R)

theorem ω_mul_ω : (ω : Q) * ω = 1 := by
  apply Subtype.ext
  change (-1 : Quaternion ℝ) * (-1) = 1
  norm_num

theorem ω_inv : (ω : Q)⁻¹ = ω := inv_eq_of_mul_eq_one_left ω_mul_ω

theorem flipCoef_cross (R : Finset (Vertex (2 * n))) (i : Link (2 * n)) (h : i ∈ cross n R) :
    flipCoef n R i = ω := by
  have h' := (Finset.mem_filter.1 h).2
  unfold flipCoef sgn
  by_cases h1 : i.1 ∈ R
  · have h2 : step (2 * n) i.1 i.2 ∉ R := fun h2 => h' ⟨fun _ => h2, fun _ => h1⟩
    simp [h1, h2]
  · have h2 : step (2 * n) i.1 i.2 ∈ R := by
      by_contra h2
      exact h' ⟨fun h3 => absurd h3 h1, fun h3 => absurd h3 h2⟩
    simp [h1, h2]

theorem flipCoef_not_cross (R : Finset (Vertex (2 * n))) (i : Link (2 * n)) (h : i ∉ cross n R) :
    flipCoef n R i = 1 := by
  have h' : i.1 ∈ R ↔ step (2 * n) i.1 i.2 ∈ R := by
    by_contra hc
    exact h (Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩)
  unfold flipCoef sgn
  by_cases h1 : i.1 ∈ R
  · simp [h1, h'.1 h1, ω_mul_ω]
  · have h2 : step (2 * n) i.1 i.2 ∉ R := fun h2 => h1 (h'.2 h2)
    simp [h1, h2]

/-- Flip the vertices of `R`. This is a center gauge transformation. -/
def flip (R : Finset (Vertex (2 * n))) : C(Link (2 * n) → Q, Link (2 * n) → Q) :=
  ⟨fun U i => flipCoef n R i * U i,
    continuous_pi fun i => continuous_const.mul (continuous_apply i)⟩

theorem flip_apply (R : Finset (Vertex (2 * n))) (U : Link (2 * n) → Q) (i : Link (2 * n)) :
    flip n R U i = flipCoef n R i * U i := rfl

/-- Center signs cancel around a plaquette. -/
theorem plaq_signs (a b c e A B C D : Q) (ha : a = 1 ∨ a = ω) (hb : b = 1 ∨ b = ω)
    (hc : c = 1 ∨ c = ω) (he : e = 1 ∨ e = ω) :
    (a * b * A) * (b * c * B) * (e * c * C)⁻¹ * (a * e * D)⁻¹ = A * B * C⁻¹ * D⁻¹ := by
  have comm (g : Q) : g * ω = ω * g := ((ω_commute g).eq).symm
  have comm2 (g h : Q) : g * (ω * h) = ω * (g * h) := by
    rw [← mul_assoc, comm, mul_assoc]
  have h2 (h : Q) : ω * (ω * h) = h := by rw [← mul_assoc, ω_mul_ω, one_mul]
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases he with rfl | rfl <;>
    simp only [one_mul, mul_one, inv_one, mul_inv_rev, ω_inv, mul_assoc, ω_mul_ω, comm A, comm B,
      comm C⁻¹, comm D⁻¹, comm2 A, comm2 B, comm2 C⁻¹, comm2 D⁻¹, h2]

theorem sgn_cases (R : Finset (Vertex (2 * n))) (w : Vertex (2 * n)) :
    sgn n R w = 1 ∨ sgn n R w = ω := by
  unfold sgn
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem flip_plaq (R : Finset (Vertex (2 * n))) (U : Link (2 * n) → Q) (x : Vertex (2 * n))
    (μ ν : Fin 4) :
    plaquetteProduct (2 * n) Q (toConfiguration (2 * n) (flip n R U)) x μ ν =
      plaquetteProduct (2 * n) Q (toConfiguration (2 * n) U) x μ ν := by
  rw [plaq_coord, plaq_coord]
  simp only [flip_apply, flipCoef]
  rw [step_comm (2 * n) x ν μ]
  exact plaq_signs _ _ _ _ _ _ _ _ (sgn_cases n R _) (sgn_cases n R _) (sgn_cases n R _)
    (sgn_cases n R _)

theorem flip_factor (β : ℝ) (R : Finset (Vertex (2 * n))) (U : Link (2 * n) → Q)
    (p : PlaquetteIndex (2 * n)) : twFactor n β p (flip n R U) = twFactor n β p U := by
  unfold twFactor TwistedReflection.term
  rw [flip_plaq]

/-- Flip the vertices of `R`, but only on the links of the box `S` and its boundary. Unlike `flip` this is not a
gauge transformation: it leaves a center defect on plaquettes that do not touch the box, which the conditional law
of the box does not see. -/
def tflipCoef (R : Finset (Vertex (2 * n))) (S : Finset (Link (2 * n))) (i : Link (2 * n)) : Q :=
  if i ∈ S ∪ nbr (twSupp n) S then flipCoef n R i else 1

def tflip (R : Finset (Vertex (2 * n))) (S : Finset (Link (2 * n))) :
    C(Link (2 * n) → Q, Link (2 * n) → Q) :=
  ⟨fun U i => tflipCoef n R S i * U i,
    continuous_pi fun i => continuous_const.mul (continuous_apply i)⟩

theorem tflip_apply (R : Finset (Vertex (2 * n))) (S : Finset (Link (2 * n))) (U : Link (2 * n) → Q)
    (i : Link (2 * n)) : tflip n R S U i = tflipCoef n R S i * U i := rfl

/-- The truncated flip preserves the factors touching the box. -/
theorem tflip_factor (β : ℝ) (R : Finset (Vertex (2 * n))) (S : Finset (Link (2 * n)))
    (p : PlaquetteIndex (2 * n)) (hp : ¬ Disjoint (twSupp n p) S) (U : Link (2 * n) → Q) :
    twFactor n β p (tflip n R S U) = twFactor n β p U := by
  rw [← flip_factor n β R U p]
  refine twFactor_depends n β p fun i hi => ?_
  have hi' : i ∈ twSupp n p := by exact_mod_cast hi
  have hbox : i ∈ S ∪ nbr (twSupp n) S := by
    by_cases hS : i ∈ S
    · exact Finset.mem_union_left _ hS
    · exact Finset.mem_union_right _ ((mem_nbr _ _ i).2 ⟨hS, p, hi', hp⟩)
  simp only [tflip_apply, flip_apply, tflipCoef, hbox, if_true]

theorem tflip_preserving (R : Finset (Vertex (2 * n))) (S : Finset (Link (2 * n))) :
    (Measure.pi fun _ : Link (2 * n) => SU2HaarTilt.haar).map (tflip n R S) =
      Measure.pi fun _ : Link (2 * n) => SU2HaarTilt.haar := by
  have hm (i : Link (2 * n)) : Measurable fun q : Q => tflipCoef n R S i * q :=
    (continuous_const.mul continuous_id).measurable
  have h := Measure.pi_map_pi (μ := fun _ : Link (2 * n) => SU2HaarTilt.haar)
    (f := fun i q => tflipCoef n R S i * q) (fun i => (hm i).aemeasurable)
  change (Measure.pi fun _ : Link (2 * n) => SU2HaarTilt.haar).map
    (fun U i => tflipCoef n R S i * U i) = _
  rw [h]
  congr 1
  funext i
  exact map_mul_left_eq_self _ _

theorem tflip_overwrite (R : Finset (Vertex (2 * n))) (T S : Finset (Link (2 * n)))
    (x V : Link (2 * n) → Q) :
    overwrite S (tflip n R T x) (tflip n R T V) = tflip n R T (overwrite S x V) := by
  funext i
  by_cases hi : i ∈ S <;> simp [overwrite_apply, tflip_apply, hi]

/-! ### The straight line through a vertex star -/

/-- The vertex just before `v` in the direction `0`. -/
def prev (v : Vertex (2 * n)) : Vertex (2 * n) := v - Pi.single 0 1

omit [NeZero n] in
theorem step_prev (v : Vertex (2 * n)) : step (2 * n) (prev n v) 0 = v := by
  simp [step, prev]

omit [NeZero n] in
theorem prev_zero (v : Vertex (2 * n)) : prev n v 0 = v 0 - 1 := by
  simp [prev]

omit [NeZero n] in
theorem step_zero (v : Vertex (2 * n)) : step (2 * n) v 0 0 = v 0 + 1 := by
  simp [step]

omit [NeZero n] in
theorem step_of_ne (v : Vertex (2 * n)) (ρ κ : Fin 4) (h : κ ≠ ρ) : step (2 * n) v ρ κ = v κ := by
  simp [step, h]

/-- The two-link line through `v`, as a function of the links of the box. It is invariant under gauge transformations
at the center of the box, and gauge variant only through its ends on the boundary. -/
def lineObs (v : Vertex (2 * n)) : C(Link (2 * n) → Q, ℝ) :=
  ⟨fun U => ((U (prev n v, 0) * U (v, 0) : Q) : Quaternion ℝ).re, by
    have h : Continuous fun U : Link (2 * n) → Q => U (prev n v, 0) * U (v, 0) :=
      (continuous_apply _).mul (continuous_apply _)
    exact Quaternion.continuous_re.comp (continuous_subtype_val.comp h)⟩

/-- The oscillation vector of the line. -/
def lineOsc (v : Vertex (2 * n)) (i : Link (2 * n)) : ℝ :=
  (if i = (prev n v, 0) then 2 else 0) + if i = (v, 0) then 2 else 0

theorem lineOsc_nonneg (v : Vertex (2 * n)) (i : Link (2 * n)) : 0 ≤ lineOsc n v i := by
  unfold lineOsc
  split <;> split <;> norm_num

theorem line_mem_star (v : Vertex (2 * n)) :
    (prev n v, (0 : Fin 4)) ∈ star n v ∧ (v, (0 : Fin 4)) ∈ star n v :=
  ⟨(mem_star n v _).2 (Or.inr (step_prev n v)), (mem_star n v _).2 (Or.inl rfl)⟩

/-- The sum of the influence of a boundary coordinate on the two links of the line. -/
theorem line_sum (κ : Link (2 * n) → Link (2 * n) → ℝ) (v : Vertex (2 * n)) (j : Link (2 * n)) :
    ∑ i ∈ star n v, κ j i * lineOsc n v i = 2 * (κ j (prev n v, 0) + κ j (v, 0)) := by
  simp only [lineOsc, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' , Finset.sum_ite_eq']
  simp only [(line_mem_star n v).1, (line_mem_star n v).2, if_true]
  ring

/-! ### Four disjoint crossing sets -/

/-- The hyperplane at level `t` in direction `0`. -/
def hyp (t : ZMod (2 * n)) : Finset (Vertex (2 * n)) := Finset.univ.filter fun w => w 0 = t

theorem cross_hyp (t : ZMod (2 * n)) (j : Link (2 * n)) (h : j ∈ cross n (hyp n t)) :
    j.2 = 0 ∧ (j.1 0 = t ∨ j.1 0 + 1 = t) := by
  have h' := (Finset.mem_filter.1 h).2
  simp only [hyp, Finset.mem_filter, Finset.mem_univ, true_and] at h'
  have h0 : j.2 = 0 := by
    by_contra hne
    have : step (2 * n) j.1 j.2 0 = j.1 0 := step_of_ne n _ _ _ (Ne.symm hne)
    rw [this] at h'
    exact h' Iff.rfl
  refine ⟨h0, ?_⟩
  rw [h0, step_zero] at h'
  by_contra hcon
  push_neg at hcon
  exact h' ⟨fun e => absurd e hcon.1, fun e => absurd e hcon.2⟩

theorem cross_single (w : Vertex (2 * n)) (j : Link (2 * n)) (h : j ∈ cross n {w}) :
    j.1 = w ∨ step (2 * n) j.1 j.2 = w := by
  have h' := (Finset.mem_filter.1 h).2
  simp only [Finset.mem_singleton] at h'
  by_contra hcon
  push_neg at hcon
  exact h' ⟨fun e => absurd e hcon.1, fun e => absurd e hcon.2⟩

variable {n} in
theorem two_ne (hn : 2 ≤ n) : (2 : ZMod (2 * n)) ≠ 0 := by
  have h := (ZMod.natCast_eq_zero_iff 2 (2 * n)).not.2 (fun hd => by
    have := Nat.le_of_dvd (by norm_num) hd
    omega)
  simpa using h

variable {n} in
theorem three_ne (hn : 2 ≤ n) : (3 : ZMod (2 * n)) ≠ 0 := by
  have h := (ZMod.natCast_eq_zero_iff 3 (2 * n)).not.2 (fun hd => by
    have := Nat.le_of_dvd (by norm_num) hd
    omega)
  simpa using h

variable {n} in
theorem one_ne : (1 : ZMod (2 * n)) ≠ 0 := by
  haveI : NeZero (2 * n) := inferInstance
  haveI : Fact (1 < 2 * n) := ⟨by have := NeZero.pos n; omega⟩
  exact one_ne_zero

/-- A coordinate step is `0` or `1`. -/
theorem step_coord (u : Vertex (2 * n)) (ρ : Fin 4) :
    step (2 * n) u ρ 0 = u 0 ∨ step (2 * n) u ρ 0 = u 0 + 1 := by
  by_cases h : ρ = 0
  · subst h
    exact Or.inr (step_zero n u)
  · exact Or.inl (step_of_ne n u ρ 0 (Ne.symm h))

/-- A link of the boundary of the star has base and endpoint within one step of `v` in every direction. -/
theorem nbr_coord (hn : 2 ≤ n) (v : Vertex (2 * n)) (ρ : Fin 4) (j : Link (2 * n))
    (hj : j ∈ nbr (twSupp n) (star n v)) :
    (j.1 ρ - v ρ ≠ -2 ∧ j.1 ρ - v ρ ≠ 2) ∧
      (step (2 * n) j.1 j.2 ρ - v ρ ≠ -2 ∧ step (2 * n) j.1 j.2 ρ - v ρ ≠ 2) := by
  obtain ⟨-, p, hjp, hp⟩ := (mem_nbr _ _ j).1 hj
  have hv := star_plaq_near n v p hp
  obtain ⟨h1, h2⟩ := incident_near n p j hjp
  have h20 := two_ne hn
  have h30 := three_ne hn
  have h10 := one_ne (n := n)
  have key (w : Vertex (2 * n)) (hw : Near n p.1 w) : w ρ - v ρ ≠ -2 ∧ w ρ - v ρ ≠ 2 := by
    constructor
    · intro e
      rcases hw ρ with a | a <;> rcases hv ρ with c | c
      · exact h20 (by linear_combination e - a + c)
      · exact h10 (by linear_combination e - a + c)
      · exact h30 (by linear_combination e - a + c)
      · exact h20 (by linear_combination e - a + c)
    · intro e
      rcases hw ρ with a | a <;> rcases hv ρ with c | c
      · exact h20 (by linear_combination -e + a - c)
      · exact h30 (by linear_combination -e + a - c)
      · exact h10 (by linear_combination -e + a - c)
      · exact h20 (by linear_combination -e + a - c)
  exact ⟨key _ h1, key _ h2⟩

/-- The same for the links of the star itself. -/
theorem star_coord (hn : 2 ≤ n) (v : Vertex (2 * n)) (ρ : Fin 4) (j : Link (2 * n))
    (hj : j ∈ star n v) :
    (j.1 ρ - v ρ ≠ -2 ∧ j.1 ρ - v ρ ≠ 2) ∧
      (step (2 * n) j.1 j.2 ρ - v ρ ≠ -2 ∧ step (2 * n) j.1 j.2 ρ - v ρ ≠ 2) := by
  have h20 := two_ne hn
  have h30 := three_ne hn
  have h10 := one_ne (n := n)
  have hA := star_near n v j hj ρ
  have hB := near_step n j.1 j.2 ρ
  refine ⟨⟨fun e => ?_, fun e => ?_⟩, ⟨fun e => ?_, fun e => ?_⟩⟩
  · rcases hA with a | a
    · exact h20 (by linear_combination e + a)
    · exact h10 (by linear_combination e + a)
  · rcases hA with a | a
    · exact h20 (by linear_combination -e - a)
    · exact h30 (by linear_combination -e - a)
  · rcases hA with a | a <;> rcases hB with c | c
    · exact h20 (by linear_combination e - c + a)
    · exact h30 (by linear_combination e - c + a)
    · exact h10 (by linear_combination e - c + a)
    · exact h20 (by linear_combination e - c + a)
  · rcases hA with a | a <;> rcases hB with c | c
    · exact h20 (by linear_combination -e + c - a)
    · exact h10 (by linear_combination -e + c - a)
    · exact h30 (by linear_combination -e + c - a)
    · exact h20 (by linear_combination -e + c - a)

/-- The four vertex sets used. -/
def regionA (v : Vertex (2 * n)) : Finset (Vertex (2 * n)) := {prev n v}
def regionB (v : Vertex (2 * n)) : Finset (Vertex (2 * n)) := {step (2 * n) v 0}
def regionC (v : Vertex (2 * n)) : Finset (Vertex (2 * n)) := hyp n (v 0 - 1)
def regionD (v : Vertex (2 * n)) : Finset (Vertex (2 * n)) := hyp n (v 0 + 1)

theorem regionA_ok (hn : 2 ≤ n) (v : Vertex (2 * n)) :
    (prev n v, (0 : Fin 4)) ∈ cross n (regionA n v) ∧ (v, (0 : Fin 4)) ∉ cross n (regionA n v) := by
  have h20 := two_ne hn
  have h10 := one_ne (n := n)
  have e1 : v ≠ prev n v := fun e => h10 (by
    have := congrFun e 0
    rw [prev_zero] at this
    linear_combination this)
  have e2 : step (2 * n) v 0 ≠ prev n v := fun e => h20 (by
    have := congrFun e 0
    rw [prev_zero, step_zero] at this
    linear_combination this)
  constructor
  · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    simp only [regionA, Finset.mem_singleton, step_prev]
    exact fun h => e1 (h.1 trivial)
  · intro h
    refine (Finset.mem_filter.1 h).2 ?_
    simp only [regionA, Finset.mem_singleton]
    exact ⟨fun e => absurd e e1, fun e => absurd e e2⟩

theorem regionB_ok (hn : 2 ≤ n) (v : Vertex (2 * n)) :
    (prev n v, (0 : Fin 4)) ∉ cross n (regionB n v) ∧ (v, (0 : Fin 4)) ∈ cross n (regionB n v) := by
  have h20 := two_ne hn
  have h10 := one_ne (n := n)
  have e1 : v ≠ step (2 * n) v 0 := fun e => h10 (by
    have := congrFun e 0
    rw [step_zero] at this
    linear_combination -this)
  have e2 : prev n v ≠ step (2 * n) v 0 := fun e => h20 (by
    have := congrFun e 0
    rw [prev_zero, step_zero] at this
    linear_combination -this)
  constructor
  · intro h
    refine (Finset.mem_filter.1 h).2 ?_
    simp only [regionB, Finset.mem_singleton, step_prev]
    exact ⟨fun e => absurd e e2, fun e => absurd e e1⟩
  · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    simp only [regionB, Finset.mem_singleton]
    exact fun h => e1 (h.2 trivial)

theorem regionC_ok (hn : 2 ≤ n) (v : Vertex (2 * n)) :
    (prev n v, (0 : Fin 4)) ∈ cross n (regionC n v) ∧ (v, (0 : Fin 4)) ∉ cross n (regionC n v) := by
  have h20 := two_ne hn
  have h10 := one_ne (n := n)
  have e1 : ¬ v 0 = v 0 - 1 := fun e => h10 (by linear_combination e)
  have e2 : ¬ v 0 + 1 = v 0 - 1 := fun e => h20 (by linear_combination e)
  constructor
  · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    simp only [regionC, hyp, Finset.mem_filter, Finset.mem_univ, true_and, step_prev, prev_zero]
    exact fun h => e1 (h.1 trivial)
  · intro h
    refine (Finset.mem_filter.1 h).2 ?_
    simp only [regionC, hyp, Finset.mem_filter, Finset.mem_univ, true_and, step_zero]
    exact ⟨fun e => absurd e e1, fun e => absurd e e2⟩

theorem regionD_ok (hn : 2 ≤ n) (v : Vertex (2 * n)) :
    (prev n v, (0 : Fin 4)) ∉ cross n (regionD n v) ∧ (v, (0 : Fin 4)) ∈ cross n (regionD n v) := by
  have h20 := two_ne hn
  have h10 := one_ne (n := n)
  have e1 : ¬ v 0 = v 0 + 1 := fun e => h10 (by linear_combination -e)
  have e2 : ¬ v 0 - 1 = v 0 + 1 := fun e => h20 (by linear_combination -e)
  constructor
  · intro h
    refine (Finset.mem_filter.1 h).2 ?_
    simp only [regionD, hyp, Finset.mem_filter, Finset.mem_univ, true_and, step_prev, prev_zero]
    exact ⟨fun e => absurd e e2, fun e => absurd e e1⟩
  · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    simp only [regionD, hyp, Finset.mem_filter, Finset.mem_univ, true_and, step_zero]
    exact fun h => e1 (h.2 trivial)

/-- Membership of a link of the boundary in a crossing set, unpacked. -/
theorem cross_pair (hn : 2 ≤ n) (v : Vertex (2 * n)) (j : Link (2 * n))
    (hj : j ∈ nbr (twSupp n) (star n v)) :
    ¬ (j ∈ cross n (regionA n v) ∧ j ∈ cross n (regionB n v)) ∧
    ¬ (j ∈ cross n (regionA n v) ∧ j ∈ cross n (regionC n v)) ∧
    ¬ (j ∈ cross n (regionA n v) ∧ j ∈ cross n (regionD n v)) ∧
    ¬ (j ∈ cross n (regionB n v) ∧ j ∈ cross n (regionC n v)) ∧
    ¬ (j ∈ cross n (regionB n v) ∧ j ∈ cross n (regionD n v)) ∧
    ¬ (j ∈ cross n (regionC n v) ∧ j ∈ cross n (regionD n v)) := by
  have h20 := two_ne hn
  have h30 := three_ne hn
  have h10 := one_ne (n := n)
  have hnS : j ∉ star n v := ((mem_nbr _ _ j).1 hj).1
  obtain ⟨⟨hb1, hb2⟩, ⟨he1, he2⟩⟩ := nbr_coord n hn v 0 j hj
  -- `A`: `j` touches `prev v`
  have hA (h : j ∈ cross n (regionA n v)) : j.1 0 = v 0 - 1 ∨ step (2 * n) j.1 j.2 0 = v 0 - 1 := by
    rcases cross_single n _ j h with e | e
    · exact Or.inl (by rw [e, prev_zero])
    · exact Or.inr (by rw [e, prev_zero])
  have hB (h : j ∈ cross n (regionB n v)) : j.1 0 = v 0 + 1 ∨ step (2 * n) j.1 j.2 0 = v 0 + 1 := by
    rcases cross_single n _ j h with e | e
    · exact Or.inl (by rw [e, step_zero])
    · exact Or.inr (by rw [e, step_zero])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- A and B
    rintro ⟨h1, h2⟩
    have hs := step_coord n j.1 j.2
    rcases hA h1 with a | a <;> rcases hB h2 with b | b <;> rcases hs with s | s
    all_goals first
      | exact h20 (by linear_combination a - b)
      | exact h20 (by linear_combination a - b + s)
      | exact h10 (by linear_combination a - b + s)
      | exact h20 (by linear_combination a - b - s)
      | exact h30 (by linear_combination a - b - s)
  · -- A and C: the only candidates are in the star or two steps away
    rintro ⟨h1, h2⟩
    obtain ⟨h0, hc⟩ := cross_hyp n _ j h2
    rcases cross_single n _ j h1 with e | e
    · exact hnS ((mem_star n v j).2 (Or.inr (by
        rw [h0, e]
        exact step_prev n v)))
    · have hs : j.1 0 + 1 = v 0 - 1 := by
        have := congrFun e 0
        rwa [h0, step_zero, prev_zero] at this
      exact hb1 (by linear_combination hs)
  · -- A and D
    rintro ⟨h1, h2⟩
    obtain ⟨h0, hc⟩ := cross_hyp n _ j h2
    have hs : step (2 * n) j.1 j.2 0 = j.1 0 + 1 := by rw [h0, step_zero]
    rcases hA h1 with a | a <;> rcases hc with c | c
    · exact h20 (by linear_combination a - c)
    · exact h10 (by linear_combination a - c)
    · rw [hs] at a
      exact h30 (by linear_combination a - c)
    · rw [hs] at a
      exact h20 (by linear_combination a - c)
  · -- B and C
    rintro ⟨h1, h2⟩
    obtain ⟨h0, hc⟩ := cross_hyp n _ j h2
    have hs : step (2 * n) j.1 j.2 0 = j.1 0 + 1 := by rw [h0, step_zero]
    rcases hB h1 with a | a <;> rcases hc with c | c
    · exact h20 (by linear_combination c - a)
    · exact h30 (by linear_combination c - a)
    · rw [hs] at a
      exact h10 (by linear_combination c - a)
    · rw [hs] at a
      exact h20 (by linear_combination c - a)
  · -- B and D: the only candidates are in the star or two steps away
    rintro ⟨h1, h2⟩
    obtain ⟨h0, hc⟩ := cross_hyp n _ j h2
    rcases cross_single n _ j h1 with e | e
    · have hs : step (2 * n) j.1 j.2 0 = v 0 + 1 + 1 := by
        rw [h0, step_zero, e, step_zero]
      exact he2 (by linear_combination hs)
    · have hu : j.1 = v := by
        rw [h0] at e
        have e' : j.1 + Pi.single 0 1 = v + Pi.single 0 1 := e
        exact add_right_cancel e'
      exact hnS ((mem_star n v j).2 (Or.inl hu))
  · -- C and D
    rintro ⟨h1, h2⟩
    obtain ⟨-, c⟩ := cross_hyp n _ j h1
    obtain ⟨-, c'⟩ := cross_hyp n _ j h2
    rcases c with c | c <;> rcases c' with c' | c'
    · exact h20 (by linear_combination c - c')
    · exact h10 (by linear_combination c - c')
    · exact h30 (by linear_combination c - c')
    · exact h20 (by linear_combination c - c')

/-! ### The flat boundary condition -/

theorem factor_action (β : ℝ) (U : Link (2 * n) → Q) :
    actionMap (twFactor n β) (twFactor_continuous n β) U =
      β * TwistedLocalization.actionOne n (toConfiguration (2 * n) U) := by
  rw [twAction_eq, TwistedLocalization.action_eq_mul]

theorem term_nonneg (U : Configuration (Vertex (2 * n)) Q) (p : PlaquetteIndex (2 * n)) :
    0 ≤ TwistedReflection.term n Q (spatialTwist n) character 2 U p := by
  obtain ⟨x, ⟨⟨μ, ν⟩, h⟩⟩ := p
  rw [TwistedStability.term_eq_defect_sq]
  positivity

theorem actionOne_eq (U : Configuration (Vertex (2 * n)) Q) :
    TwistedLocalization.actionOne n U =
      ∑ p, TwistedReflection.term n Q (spatialTwist n) character 2 U p := by
  unfold TwistedLocalization.actionOne TwistedReflection.action
  rw [one_mul]

theorem actionOne_nonneg (U : Configuration (Vertex (2 * n)) Q) :
    0 ≤ TwistedLocalization.actionOne n U := by
  rw [actionOne_eq]
  exact Finset.sum_nonneg fun p _ => term_nonneg n U p

/-- A product of two links is near one when the two plaquettes through them, with their other links fixed
to matching values, are satisfied. -/
theorem line_le_action (v : Vertex (2 * n)) (U : Link (2 * n) → Q)
    (h₁ : U (step (2 * n) (prev n v) 1, 0) = 1) (h₂ : U (step (2 * n) v 1, 0) = 1) (q : Q)
    (h₃ : U (prev n v, 1) = q) (h₄ : U (step (2 * n) v 0, 1) = q) :
    1 - lineObs n v U ≤ TwistedLocalization.actionOne n (toConfiguration (2 * n) U) := by
  have hne : prev n v ≠ v := fun e => one_ne (n := n) (by
    have := congrFun e 0
    rw [prev_zero] at this
    linear_combination -this)
  have h01 : (0 : Fin 4) < 1 := by decide
  let p₁ : PlaquetteIndex (2 * n) := (prev n v, ⟨(0, 1), h01⟩)
  let p₂ : PlaquetteIndex (2 * n) := (v, ⟨(0, 1), h01⟩)
  have hp : p₁ ≠ p₂ := fun e => hne (congrArg Prod.fst e)
  set A := U (prev n v, 0)
  set B := U (v, 1)
  set C := U (v, 0)
  have hd1 : TwistedReflection.term n Q (spatialTwist n) character 2 (toConfiguration (2 * n) U) p₁ =
      TwistedStability.d (A * B * q⁻¹) 1 ^ 2 := by
    change TwistedReflection.term n Q (spatialTwist n) character 2 (toConfiguration (2 * n) U)
      (prev n v, ⟨(0, 1), h01⟩) = _
    rw [TwistedStability.term_eq_defect_sq]
    unfold TwistedStability.defect
    have e1 : PeriodicTimeReflection.linkValue (2 * n) Q (toConfiguration (2 * n) U) (prev n v) 0 = A :=
      rfl
    have e2 : PeriodicTimeReflection.linkValue (2 * n) Q (toConfiguration (2 * n) U)
        (step (2 * n) (prev n v) 0) 1 = B := by
      rw [step_prev]
      rfl
    have e3 : PeriodicTimeReflection.linkValue (2 * n) Q (toConfiguration (2 * n) U)
        (step (2 * n) (prev n v) 1) 0 = 1 := h₁
    have e4 : PeriodicTimeReflection.linkValue (2 * n) Q (toConfiguration (2 * n) U) (prev n v) 1 = q :=
      h₃
    rw [e1, e2, e3, e4]
    simp [TwistedFlat.twistExp]
  have hd2 : TwistedReflection.term n Q (spatialTwist n) character 2 (toConfiguration (2 * n) U) p₂ =
      TwistedStability.d (C * q * B⁻¹) 1 ^ 2 := by
    change TwistedReflection.term n Q (spatialTwist n) character 2 (toConfiguration (2 * n) U)
      (v, ⟨(0, 1), h01⟩) = _
    rw [TwistedStability.term_eq_defect_sq]
    unfold TwistedStability.defect
    have e1 : PeriodicTimeReflection.linkValue (2 * n) Q (toConfiguration (2 * n) U) v 0 = C := rfl
    have e2 : PeriodicTimeReflection.linkValue (2 * n) Q (toConfiguration (2 * n) U)
        (step (2 * n) v 0) 1 = q := h₄
    have e3 : PeriodicTimeReflection.linkValue (2 * n) Q (toConfiguration (2 * n) U)
        (step (2 * n) v 1) 0 = 1 := h₂
    have e4 : PeriodicTimeReflection.linkValue (2 * n) Q (toConfiguration (2 * n) U) v 1 = B := rfl
    rw [e1, e2, e3, e4]
    simp [TwistedFlat.twistExp]
  -- the line is a product of the first plaquette and a conjugate of the second
  set P₁ := A * B * q⁻¹ with hP₁
  set P₂ := C * q * B⁻¹ with hP₂
  set c := q * B⁻¹ with hc
  have hprod : A * C = P₁ * (c * P₂ * c⁻¹) := by
    rw [hP₁, hP₂, hc]
    group
  have hconj : TwistedStability.d (c * P₂ * c⁻¹) 1 = TwistedStability.d P₂ 1 := by
    have h1 := TwistedStability.d_mul_left c (P₂ * c⁻¹) c⁻¹
    have h2 := TwistedStability.d_mul_right c⁻¹ P₂ 1
    rw [mul_inv_cancel, ← mul_assoc] at h1
    rw [one_mul] at h2
    rw [h1, h2]
  have htri : TwistedStability.d (A * C) 1 ≤ TwistedStability.d P₁ 1 + TwistedStability.d P₂ 1 := by
    rw [hprod]
    have h1 := TwistedStability.d_triangle (P₁ * (c * P₂ * c⁻¹)) (c * P₂ * c⁻¹) 1
    have h2 := TwistedStability.d_mul_right (c * P₂ * c⁻¹) P₁ 1
    rw [one_mul] at h2
    rw [h2, hconj] at h1
    exact h1
  have hre : 1 - lineObs n v U = TwistedStability.d (A * C) 1 ^ 2 / 2 := by
    change 1 - ((A * C : Q) : Quaternion ℝ).re = _
    have h := SU2GaussianMass.chord_square (A * C)
    unfold TwistedStability.d
    have e : (((1 : Q) : Quaternion ℝ)) = 1 := rfl
    rw [e, h]
    ring
  have hn1 := TwistedStability.d_nonneg (A * C) 1
  have hn2 := TwistedStability.d_nonneg P₁ 1
  have hn3 := TwistedStability.d_nonneg P₂ 1
  have hsq : TwistedStability.d (A * C) 1 ^ 2 / 2 ≤
      TwistedStability.d P₁ 1 ^ 2 + TwistedStability.d P₂ 1 ^ 2 := by
    have := pow_le_pow_left₀ hn1 htri 2
    nlinarith only [this, sq_nonneg (TwistedStability.d P₁ 1 - TwistedStability.d P₂ 1)]
  rw [hre, actionOne_eq]
  refine hsq.trans ?_
  rw [← hd1, ← hd2]
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (s := {p₁, p₂}) (t := Finset.univ)
    (f := TwistedReflection.term n Q (spatialTwist n) character 2 (toConfiguration (2 * n) U))
    (Finset.subset_univ _) (fun p _ _ => term_nonneg n _ p)
  rwa [Finset.sum_pair hp] at hsum

/-- The zero-action field in link coordinates. -/
def flatState : Link (2 * n) → Q := fun i => flatLink i.1 i.2

theorem distSq_overwrite (S : Finset (Link (2 * n))) (V : Link (2 * n) → Q) :
    TwistedLocalization.distSq n (PeriodicTimeReflection.linkValue (2 * n) Q
      (toConfiguration (2 * n) (overwrite S (flatState n) V))) =
      ∑ i ∈ S, TwistedStability.d (V i) (flatState n i) ^ 2 := by
  unfold TwistedLocalization.distSq
  rw [Finset.sum_comm]
  have hS : (∑ i ∈ S, TwistedStability.d (V i) (flatState n i) ^ 2) =
      ∑ i, if i ∈ S then TwistedStability.d (V i) (flatState n i) ^ 2 else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [hS, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ => ?_
  change TwistedStability.d (overwrite S (flatState n) V (x, μ)) (flatLink x μ) ^ 2 = _
  by_cases h : (x, μ) ∈ S
  · simp [overwrite_apply, h, flatState]
  · simp [overwrite_apply, h, flatState, TwistedStability.d]

theorem toConfig_overwrite_continuous (S : Finset (Link (2 * n))) (x : Link (2 * n) → Q) :
    Continuous fun V => TwistedLocalization.actionOne n
      (toConfiguration (2 * n) (overwrite S x V)) := by
  have h := TwistedReflection.continuous_action n Q (spatialTwist n) character character_continuous 1 2
  exact h.comp ((toConfiguration_continuous n).comp (overwrite S x).continuous)

/-- **The energy of a box with flat boundary condition.** Its expected action is at most
`(2/β) |S| log cap(24β)`, with no reference to the lattice outside `S`. -/
theorem flat_energy (S : Finset (Link (2 * n))) (β : ℝ) (hβ : 1 / 32 ≤ β) (m : ℕ) (hm : S.card ≤ m) :
    (∫ V, TwistedLocalization.actionOne n (toConfiguration (2 * n) (overwrite S (flatState n) V))
        ∂fiber SU2HaarTilt.haar (twFactor n β) (twFactor_continuous n β) S (flatState n)) ≤
      2 / β * (m * Real.log (SU2GaussianMass.cap (24 * β))) := by
  have hβ0 : 0 < β := by linarith
  set π := Measure.pi fun _ : Link (2 * n) => SU2HaarTilt.haar with hπ
  let s : (Link (2 * n) → Q) → ℝ := fun V =>
    TwistedLocalization.actionOne n (toConfiguration (2 * n) (overwrite S (flatState n) V))
  have hs : Continuous s := toConfig_overwrite_continuous n S _
  have hs0 (V : Link (2 * n) → Q) : 0 ≤ s V := actionOne_nonneg n _
  set ν := fiber SU2HaarTilt.haar (twFactor n β) (twFactor_continuous n β) S (flatState n) with hν
  have hint (G : (Link (2 * n) → Q) → ℝ) (hG : Continuous G) :
      Integrable G π := hG.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hintν (G : (Link (2 * n) → Q) → ℝ) (hG : Continuous G) :
      Integrable G ν := hG.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hexp (G : (Link (2 * n) → Q) → ℝ) :
      (∫ V, G V ∂ν) = (∫ V, Real.exp (-(β * s V)) * G V ∂π) / ∫ V, Real.exp (-(β * s V)) ∂π := by
    rw [hν, fiber_integral]
    simp only [factor_action]
    rfl
  set Z := ∫ V, Real.exp (-(β * s V)) ∂π with hZ
  have hcZ : Continuous fun V => Real.exp (-(β * s V)) :=
    Real.continuous_exp.comp (continuous_const.mul hs).neg
  have hZpos : 0 < Z := by
    have := CompactGibbsContinuity.partition_positive π (fun V => β * s V) (continuous_const.mul hs)
    simpa [hZ] using this
  -- Jensen for the exponential
  set m₀ := ∫ V, s V ∂ν with hm₀
  have hJ : Real.exp (β / 2 * m₀) ≤ ∫ V, Real.exp (β / 2 * s V) ∂ν := by
    have hpt (V : Link (2 * n) → Q) : Real.exp (β / 2 * m₀) * (β / 2 * (s V - m₀) + 1) ≤
        Real.exp (β / 2 * s V) := by
      have h1 := Real.add_one_le_exp (β / 2 * (s V - m₀))
      have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (β / 2 * m₀)).le
      rw [← Real.exp_add] at h2
      rwa [show β / 2 * m₀ + β / 2 * (s V - m₀) = β / 2 * s V by ring] at h2
    have hc1 : Continuous fun V => Real.exp (β / 2 * m₀) * (β / 2 * (s V - m₀) + 1) :=
      continuous_const.mul ((continuous_const.mul (hs.sub continuous_const)).add continuous_const)
    have hc2 : Continuous fun V => Real.exp (β / 2 * s V) :=
      Real.continuous_exp.comp (continuous_const.mul hs)
    have hmono := integral_mono (hintν _ hc1) (hintν _ hc2) hpt
    have heval : (∫ V, Real.exp (β / 2 * m₀) * (β / 2 * (s V - m₀) + 1) ∂ν) = Real.exp (β / 2 * m₀) := by
      have i1 : Integrable (fun V => β / 2 * (s V - m₀)) ν :=
        hintν _ (continuous_const.mul (hs.sub continuous_const))
      rw [integral_const_mul, integral_add i1 (integrable_const _), integral_const_mul,
        integral_sub (hintν _ hs) (integrable_const _)]
      simp [hm₀]
    rwa [heval] at hmono
  have hupper : (∫ V, Real.exp (β / 2 * s V) ∂ν) ≤ 1 / Z := by
    rw [hexp]
    refine div_le_div_of_nonneg_right ?_ hZpos.le
    have hpt (V : Link (2 * n) → Q) : Real.exp (-(β * s V)) * Real.exp (β / 2 * s V) ≤ 1 := by
      rw [← Real.exp_add]
      apply Real.exp_le_one_iff.2
      nlinarith [hs0 V]
    have hc : Continuous fun V => Real.exp (-(β * s V)) * Real.exp (β / 2 * s V) :=
      hcZ.mul (Real.continuous_exp.comp (continuous_const.mul hs))
    have := integral_mono (hint _ hc) (integrable_const (1 : ℝ)) hpt
    simpa using this
  -- the partition function from below
  set M := SU2GaussianMass.mass (24 * β) with hM
  have hMpos : 0 < M := SU2GaussianMass.mass_pos _
  have hZlow : M ^ S.card ≤ Z := by
    have hprod : (∫ V : Link (2 * n) → Q, ∏ i, (if i ∈ S then
        Real.exp (-(24 * β) * TwistedStability.d (V i) (flatState n i) ^ 2) else 1) ∂π) = M ^ S.card := by
      have h := integral_fintype_prod_eq_prod (ι := Link (2 * n)) (E := fun _ => Q)
        (fun i q => if i ∈ S then
          Real.exp (-(24 * β) * TwistedStability.d q (flatState n i) ^ 2) else (1 : ℝ))
        (μ := fun _ => compactHaar Q)
      refine h.trans ?_
      have hone (i : Link (2 * n)) : (∫ q : Q, (if i ∈ S then
          Real.exp (-(24 * β) * TwistedStability.d q (flatState n i) ^ 2) else (1 : ℝ)) ∂compactHaar Q) =
          if i ∈ S then M else 1 := by
        by_cases hi : i ∈ S
        · simp only [hi, if_true]
          exact TwistedLocalization.gaussian_translate _ _
        · simp [hi]
      simp only [hone, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
    rw [← hprod]
    refine integral_mono (hint _ ?_) (hint _ hcZ) fun V => ?_
    · refine continuous_finset_prod _ fun i _ => ?_
      by_cases hi : i ∈ S
      · simp only [hi, if_true]
        unfold TwistedStability.d
        fun_prop
      · simp only [hi, if_false]
        exact continuous_const
    · have he : ∏ i, (if i ∈ S then
          Real.exp (-(24 * β) * TwistedStability.d (V i) (flatState n i) ^ 2) else 1) =
          Real.exp (∑ i ∈ S, -(24 * β) * TwistedStability.d (V i) (flatState n i) ^ 2) := by
        rw [Real.exp_sum, Finset.prod_ite_mem, Finset.univ_inter]
      change ∏ i, (if i ∈ S then
          Real.exp (-(24 * β) * TwistedStability.d (V i) (flatState n i) ^ 2) else 1) ≤ _
      rw [he]
      apply Real.exp_le_exp.2
      have h1 := TwistedLocalization.actionOne_le n
        (toConfiguration (2 * n) (overwrite S (flatState n) V))
      rw [distSq_overwrite] at h1
      rw [← Finset.mul_sum]
      nlinarith [mul_le_mul_of_nonneg_left h1 hβ0.le]
  -- logarithms
  have hmc := SU2GaussianMass.mass_cap_lower (24 * β) (by linarith)
  have hcap0 := SU2GaussianMass.cap_nonneg (24 * β) (by linarith)
  have hcappos : 0 < SU2GaussianMass.cap (24 * β) := by
    by_contra hcon
    have : SU2GaussianMass.cap (24 * β) = 0 := le_antisymm (not_lt.1 hcon) hcap0
    rw [this, mul_zero] at hmc
    linarith
  have hM1 : M ≤ 1 := by
    have h := SU2GaussianMass.mass_antitone (show (0 : ℝ) ≤ 24 * β by linarith)
    have h0 : SU2GaussianMass.mass 0 = 1 := by
      unfold SU2GaussianMass.mass SU2GaussianMass.weight
      simp
    rwa [h0] at h
  have hlog1 : -Real.log M ≤ Real.log (SU2GaussianMass.cap (24 * β)) := by
    have := Real.log_nonneg hmc
    rw [Real.log_mul hMpos.ne' hcappos.ne'] at this
    linarith
  have hlogM : Real.log M ≤ 0 := Real.log_nonpos hMpos.le hM1
  have hL0 : 0 ≤ Real.log (SU2GaussianMass.cap (24 * β)) := by linarith
  have hkey : β / 2 * m₀ ≤ m * Real.log (SU2GaussianMass.cap (24 * β)) := by
    have h1 : Real.exp (β / 2 * m₀) ≤ 1 / Z := hJ.trans hupper
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp, one_div, Real.log_inv] at h2
    have h3 : (S.card : ℝ) * Real.log M ≤ Real.log Z := by
      have := Real.log_le_log (pow_pos hMpos _) hZlow
      rwa [Real.log_pow] at this
    have h4 : (S.card : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [mul_le_mul_of_nonneg_right h4 hL0,
      mul_le_mul_of_nonneg_left hlog1 (Nat.cast_nonneg S.card)]
  rw [div_mul_eq_mul_div, le_div_iff₀ hβ0]
  linarith

/-- The defect of the line, as a function of the coupling only. -/
def lineDefect (β : ℝ) : ℝ := 2 / β * ((8 : ℕ) * Real.log (SU2GaussianMass.cap (24 * β)))

/-- **At flat boundary condition the two-link line is near one, uniformly in the volume.** -/
theorem line_expectation (v : Vertex (2 * n)) (β : ℝ) (hβ : 1 / 32 ≤ β) :
    1 - lineDefect β ≤
      E SU2HaarTilt.haar (twFactor n β) (twFactor_continuous n β) (star n v) (lineObs n v)
        (flatState n) := by
  rw [E_apply]
  set ν := fiber SU2HaarTilt.haar (twFactor n β) (twFactor_continuous n β) (star n v) (flatState n)
  have hsv := flat_energy n (star n v) β hβ 8 (star_card n v)
  have h10 := one_ne (n := n)
  have hcont := toConfig_overwrite_continuous n (star n v) (flatState n)
  have hG : Continuous fun V => lineObs n v (overwrite (star n v) (flatState n) V) :=
    (lineObs n v).continuous.comp (overwrite (star n v) (flatState n)).continuous
  have hinteg (G : (Link (2 * n) → Q) → ℝ) (hG : Continuous G) :
      Integrable G ν := hG.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpt (V : Link (2 * n) → Q) : 1 - TwistedLocalization.actionOne n
      (toConfiguration (2 * n) (overwrite (star n v) (flatState n) V)) ≤
        lineObs n v (overwrite (star n v) (flatState n) V) := by
    have hnot1 : (step (2 * n) (prev n v) 1, (0 : Fin 4)) ∉ star n v := by
      rw [mem_star]
      rintro (e | e)
      · have := congrFun e 1
        exact h10 (by simpa [step, prev] using this)
      · have := congrFun e 1
        exact h10 (by simpa [step, prev] using this)
    have hnot2 : (step (2 * n) v 1, (0 : Fin 4)) ∉ star n v := by
      rw [mem_star]
      rintro (e | e)
      · have := congrFun e 1
        exact h10 (by simpa [step] using this)
      · have := congrFun e 1
        exact h10 (by simpa [step] using this)
    have hnot3 : (prev n v, (1 : Fin 4)) ∉ star n v := by
      rw [mem_star]
      rintro (e | e)
      · have := congrFun e 0
        exact h10 (by simpa [prev] using this)
      · have := congrFun e 0
        exact h10 (by simpa [step, prev] using this)
    have hnot4 : (step (2 * n) v 0, (1 : Fin 4)) ∉ star n v := by
      rw [mem_star]
      rintro (e | e)
      · have := congrFun e 0
        exact h10 (by simpa [step] using this)
      · have := congrFun e 0
        exact h10 (by simpa [step] using this)
    have hq : flatLink (prev n v) 1 = flatLink (step (2 * n) v 0) 1 := by
      have e : prev n v 1 = step (2 * n) v 0 1 := by simp [prev, step]
      have l (y : Vertex (2 * n)) : flatLink y 1 = if y 1 = 0 then TwistedFlat.qI else 1 := by
        simp [flatLink]
      rw [l, l, e]
    have h := line_le_action n v (overwrite (star n v) (flatState n) V)
      (by simp [overwrite_apply, hnot1, flatState, flatLink])
      (by simp [overwrite_apply, hnot2, flatState, flatLink]) (flatLink (prev n v) 1)
      (by simp [overwrite_apply, hnot3, flatState])
      (by simp [overwrite_apply, hnot4, flatState, hq])
    linarith
  have hmono := integral_mono (hinteg _ (continuous_const.sub hcont)) (hinteg _ hG) hpt
  rw [integral_sub (integrable_const _) (hinteg _ hcont)] at hmono
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hmono
  unfold lineDefect
  linarith

/-! ### A closed rectangle running straight through the star

The two-link line is gauge variant only through its ends. A fixed path outside the boundary of the star closes it
into a contractible rectangle, which is gauge invariant. With the exterior frozen, the box sees the same function
of its links, so the no-go below is not an artifact of testing on gauge-variant functions. -/

/-- The point `v + s e₀ + t e₁`. -/
def pt (v : Vertex (2 * n)) (s t : ZMod (2 * n)) : Vertex (2 * n) :=
  v + Pi.single 0 s + Pi.single 1 t

omit [NeZero n] in
theorem pt_step0 (v : Vertex (2 * n)) (s t s' : ZMod (2 * n)) (h : s + 1 = s') :
    step (2 * n) (pt n v s t) 0 = pt n v s' t := by
  subst h
  simp only [step, pt, Pi.single_add]
  abel

omit [NeZero n] in
theorem pt_step1 (v : Vertex (2 * n)) (s t t' : ZMod (2 * n)) (h : t + 1 = t') :
    step (2 * n) (pt n v s t) 1 = pt n v s t' := by
  subst h
  simp only [step, pt, Pi.single_add]
  abel

omit [NeZero n] in
theorem pt_coord0 (v : Vertex (2 * n)) (s t : ZMod (2 * n)) : pt n v s t 0 = v 0 + s := by
  simp [pt]

omit [NeZero n] in
theorem pt_coord1 (v : Vertex (2 * n)) (s t : ZMod (2 * n)) : pt n v s t 1 = v 1 + t := by
  simp [pt]

/-- The ten links closing the line, outside the star and its boundary. -/
def loopRest (v : Vertex (2 * n)) : Finset (Link (2 * n)) :=
  {(pt n v 1 0, 0), (pt n v 2 0, 1), (pt n v 2 1, 1), (pt n v 1 2, 0), (pt n v 0 2, 0),
    (pt n v (-1) 2, 0), (pt n v (-2) 2, 0), (pt n v (-2) 1, 1), (pt n v (-2) 0, 1), (pt n v (-2) 0, 0)}

/-- The transport along the closing path, from `v + e₀` around to `v - e₀`. -/
def restVal (v : Vertex (2 * n)) (U : Link (2 * n) → Q) : Q :=
  U (pt n v 1 0, 0) * U (pt n v 2 0, 1) * U (pt n v 2 1, 1) * (U (pt n v 1 2, 0))⁻¹ *
    (U (pt n v 0 2, 0))⁻¹ * (U (pt n v (-1) 2, 0))⁻¹ * (U (pt n v (-2) 2, 0))⁻¹ *
    (U (pt n v (-2) 1, 1))⁻¹ * (U (pt n v (-2) 0, 1))⁻¹ * U (pt n v (-2) 0, 0)

theorem restVal_congr (v : Vertex (2 * n)) (U U' : Link (2 * n) → Q)
    (h : ∀ i ∈ loopRest n v, U i = U' i) : restVal n v U = restVal n v U' := by
  unfold restVal
  rw [h (pt n v 1 0, 0) (by simp [loopRest]), h (pt n v 2 0, 1) (by simp [loopRest]),
    h (pt n v 2 1, 1) (by simp [loopRest]), h (pt n v 1 2, 0) (by simp [loopRest]),
    h (pt n v 0 2, 0) (by simp [loopRest]), h (pt n v (-1) 2, 0) (by simp [loopRest]),
    h (pt n v (-2) 2, 0) (by simp [loopRest]), h (pt n v (-2) 1, 1) (by simp [loopRest]),
    h (pt n v (-2) 0, 1) (by simp [loopRest]), h (pt n v (-2) 0, 0) (by simp [loopRest])]

theorem restVal_continuous (v : Vertex (2 * n)) : Continuous (restVal n v) := by
  unfold restVal
  fun_prop

omit n in
theorem re_continuous : Continuous fun q : Q => ((q : Q) : Quaternion ℝ).re :=
  Quaternion.continuous_re.comp continuous_subtype_val

/-- **The closed rectangle through `v`**, four by two in the plane of directions `0` and `1`. Half the real trace of
its holonomy, based at `v - e₀`. Its net winding is zero in every direction, so it is contractible on the torus. -/
def loopObs (v : Vertex (2 * n)) : C(Link (2 * n) → Q, ℝ) :=
  ⟨fun U => ((U (prev n v, 0) * U (v, 0) * restVal n v U : Q) : Quaternion ℝ).re,
    re_continuous.comp (((continuous_apply (prev n v, (0 : Fin 4))).mul
      (continuous_apply (v, (0 : Fin 4)))).mul (restVal_continuous n v))⟩

theorem loopObs_apply (v : Vertex (2 * n)) (U : Link (2 * n) → Q) :
    loopObs n v U = ((U (prev n v, 0) * U (v, 0) * restVal n v U : Q) : Quaternion ℝ).re := rfl

/-- The closing links miss the star and its boundary. -/
theorem loopRest_far (hn : 2 ≤ n) (v : Vertex (2 * n)) (j : Link (2 * n)) (hj : j ∈ loopRest n v) :
    j ∉ star n v ∧ j ∉ nbr (twSupp n) (star n v) := by
  have key (ρ : Fin 4) (hfar : (j.1 ρ - v ρ = -2 ∨ j.1 ρ - v ρ = 2) ∨
      (step (2 * n) j.1 j.2 ρ - v ρ = 2)) :
      j ∉ star n v ∧ j ∉ nbr (twSupp n) (star n v) := by
    constructor
    · intro h
      obtain ⟨⟨h1, h2⟩, ⟨-, h3⟩⟩ := star_coord n hn v ρ j h
      rcases hfar with (e | e) | e
      · exact h1 e
      · exact h2 e
      · exact h3 e
    · intro h
      obtain ⟨⟨h1, h2⟩, ⟨-, h3⟩⟩ := nbr_coord n hn v ρ j h
      rcases hfar with (e | e) | e
      · exact h1 e
      · exact h2 e
      · exact h3 e
  simp only [loopRest, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with h | h | h | h | h | h | h | h | h | h <;> subst h
  · refine key 0 (Or.inr ?_)
    rw [pt_step0 n v 1 0 2 (by norm_num), pt_coord0]
    ring
  · refine key 0 (Or.inl (Or.inr ?_))
    change pt n v 2 0 0 - v 0 = 2
    rw [pt_coord0]
    ring
  · refine key 0 (Or.inl (Or.inr ?_))
    change pt n v 2 1 0 - v 0 = 2
    rw [pt_coord0]
    ring
  · refine key 1 (Or.inl (Or.inr ?_))
    change pt n v 1 2 1 - v 1 = 2
    rw [pt_coord1]
    ring
  · refine key 1 (Or.inl (Or.inr ?_))
    change pt n v 0 2 1 - v 1 = 2
    rw [pt_coord1]
    ring
  · refine key 1 (Or.inl (Or.inr ?_))
    change pt n v (-1) 2 1 - v 1 = 2
    rw [pt_coord1]
    ring
  · refine key 1 (Or.inl (Or.inr ?_))
    change pt n v (-2) 2 1 - v 1 = 2
    rw [pt_coord1]
    ring
  · refine key 0 (Or.inl (Or.inl ?_))
    change pt n v (-2) 1 0 - v 0 = -2
    rw [pt_coord0]
    ring
  · refine key 0 (Or.inl (Or.inl ?_))
    change pt n v (-2) 0 0 - v 0 = -2
    rw [pt_coord0]
    ring
  · refine key 0 (Or.inl (Or.inl ?_))
    change pt n v (-2) 0 0 - v 0 = -2
    rw [pt_coord0]
    ring

/-- The oscillation vector of the rectangle. -/
def loopOsc (v : Vertex (2 * n)) (i : Link (2 * n)) : ℝ :=
  lineOsc n v i + if i ∈ loopRest n v then 2 else 0

theorem loopOsc_nonneg (v : Vertex (2 * n)) (i : Link (2 * n)) : 0 ≤ loopOsc n v i := by
  unfold loopOsc
  have := lineOsc_nonneg n v i
  split <;> linarith

theorem loopObs_osc (v : Vertex (2 * n)) : OscBound (loopObs n v) (loopOsc n v) := by
  intro j U V h
  have hb (g : Q) := abs_le.1 (TwistedFlat.re_le_one g)
  have hdiff : |loopObs n v U - loopObs n v V| ≤ 2 := by
    rw [loopObs_apply, loopObs_apply, abs_le]
    have h2 := hb (U (prev n v, 0) * U (v, 0) * restVal n v U)
    have h3 := hb (V (prev n v, 0) * V (v, 0) * restVal n v V)
    constructor <;> linarith [h2.1, h2.2, h3.1, h3.2]
  have hl0 := lineOsc_nonneg n v j
  have hr0 : (0 : ℝ) ≤ if j ∈ loopRest n v then 2 else 0 := by split <;> norm_num
  by_cases h1 : j = (prev n v, 0)
  · have : (2 : ℝ) ≤ lineOsc n v j := by
      have hn0 : (0 : ℝ) ≤ if j = (v, 0) then 2 else 0 := by split <;> norm_num
      simp only [lineOsc]
      rw [if_pos h1]
      linarith
    unfold loopOsc
    linarith
  by_cases h2 : j = (v, 0)
  · have : (2 : ℝ) ≤ lineOsc n v j := by
      have hn0 : (0 : ℝ) ≤ if j = (prev n v, 0) then 2 else 0 := by split <;> norm_num
      simp only [lineOsc]
      rw [if_pos h2]
      linarith
    unfold loopOsc
    linarith
  by_cases h3 : j ∈ loopRest n v
  · unfold loopOsc
    rw [if_pos h3]
    linarith
  · have e1 : U (prev n v, 0) = V (prev n v, 0) := h _ fun e => h1 e.symm
    have e2 : U (v, 0) = V (v, 0) := h _ fun e => h2 e.symm
    have e3 : restVal n v U = restVal n v V :=
      restVal_congr n v U V fun i hi => h i fun e => h3 (e ▸ hi)
    rw [loopObs_apply, loopObs_apply, e1, e2, e3, sub_self, abs_zero]
    unfold loopOsc
    linarith

/-- A truncated flip reversing exactly one link of the line reverses the rectangle, because it does not touch the
closing links. -/
theorem loop_anti (hn : 2 ≤ n) (v : Vertex (2 * n)) (R : Finset (Vertex (2 * n)))
    (hR : ((prev n v, (0 : Fin 4)) ∈ cross n R ∧ (v, (0 : Fin 4)) ∉ cross n R) ∨
      ((prev n v, (0 : Fin 4)) ∉ cross n R ∧ (v, (0 : Fin 4)) ∈ cross n R))
    (U : Link (2 * n) → Q) : loopObs n v (tflip n R (star n v) U) = -loopObs n v U := by
  have hrest : restVal n v (tflip n R (star n v) U) = restVal n v U := by
    refine restVal_congr n v _ _ fun i hi => ?_
    obtain ⟨h1, h2⟩ := loopRest_far n hn v i hi
    have : i ∉ star n v ∪ nbr (twSupp n) (star n v) := by simp [h1, h2]
    simp [tflip_apply, tflipCoef, this]
  have hin (i : Link (2 * n)) (hi : i ∈ star n v) : tflipCoef n R (star n v) i = flipCoef n R i := by
    simp [tflipCoef, hi]
  rw [loopObs_apply, loopObs_apply, hrest, tflip_apply, tflip_apply,
    hin _ (line_mem_star n v).1, hin _ (line_mem_star n v).2]
  set r := restVal n v U
  rcases hR with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [flipCoef_cross n R _ h1, flipCoef_not_cross n R _ h2, one_mul]
    have : ((ω * U (prev n v, 0) * U (v, 0) * r : Q) : Quaternion ℝ) =
        -((U (prev n v, 0) * U (v, 0) * r : Q) : Quaternion ℝ) := by
      change ((-1 : Quaternion ℝ) * (U (prev n v, 0) : Quaternion ℝ)) * (U (v, 0) : Quaternion ℝ) *
        (r : Quaternion ℝ) = -((U (prev n v, 0) : Quaternion ℝ) * (U (v, 0) : Quaternion ℝ) * (r : Quaternion ℝ))
      noncomm_ring
    rw [this]
    simp
  · rw [flipCoef_not_cross n R _ h1, flipCoef_cross n R _ h2, one_mul]
    have : ((U (prev n v, 0) * (ω * U (v, 0)) * r : Q) : Quaternion ℝ) =
        -((U (prev n v, 0) * U (v, 0) * r : Q) : Quaternion ℝ) := by
      change (U (prev n v, 0) : Quaternion ℝ) * ((-1 : Quaternion ℝ) * (U (v, 0) : Quaternion ℝ)) *
        (r : Quaternion ℝ) = -((U (prev n v, 0) : Quaternion ℝ) * (U (v, 0) : Quaternion ℝ) * (r : Quaternion ℝ))
      noncomm_ring
    rw [this]
    simp

/-- The two-link sum against the oscillation of the rectangle. -/
theorem loop_sum (hn : 2 ≤ n) (κ : Link (2 * n) → Link (2 * n) → ℝ) (v : Vertex (2 * n)) (j : Link (2 * n)) :
    ∑ i ∈ star n v, κ j i * loopOsc n v i = 2 * (κ j (prev n v, 0) + κ j (v, 0)) := by
  rw [← line_sum n κ v j]
  refine Finset.sum_congr rfl fun i hi => ?_
  have : i ∉ loopRest n v := fun h => (loopRest_far n hn v i h).1 hi
  simp [loopOsc, this]

/-- **The influence of a crossing set on the line is at least the conditional expectation of the closed
rectangle.** No smallness or coupling hypothesis. The test observable is gauge invariant whenever the class
contains the rectangle. This is the exact statement behind the failure at weak coupling. -/
theorem loop_cross_bound (hn : 2 ≤ n) (β : ℝ) {𝓐 : Submodule ℝ C(Link (2 * n) → Q, ℝ)}
    (κ : Link (2 * n) → Link (2 * n) → ℝ) (v : Vertex (2 * n)) (hmem : loopObs n v ∈ 𝓐)
    (hinf : BlockInfluenceOn SU2HaarTilt.haar (twSupp n) (twFactor n β) (twFactor_continuous n β) 𝓐
      (star n v) κ)
    (R : Finset (Vertex (2 * n)))
    (hR : ((prev n v, (0 : Fin 4)) ∈ cross n R ∧ (v, (0 : Fin 4)) ∉ cross n R) ∨
      ((prev n v, (0 : Fin 4)) ∉ cross n R ∧ (v, (0 : Fin 4)) ∈ cross n R))
    (x : Link (2 * n) → Q) :
    |E SU2HaarTilt.haar (twFactor n β) (twFactor_continuous n β) (star n v) (loopObs n v) x| ≤
      ∑ j ∈ cross n R, if j ∈ nbr (twSupp n) (star n v) then κ j (prev n v, 0) + κ j (v, 0) else 0 := by
  set J := (cross n R).filter fun j => j ∈ star n v ∪ nbr (twSupp n) (star n v) with hJdef
  have h := antisym_bound (twFactor_depends n β) hinf (tflip n R (star n v)) (tflip_preserving n R _)
    (fun p hp U => tflip_factor n β R _ p hp U) (fun x V => tflip_overwrite n R _ _ x V)
    (loopObs n v) hmem (loopOsc n v) (loopObs_osc n v) (loopOsc_nonneg n v)
    (loop_anti n hn v R hR) J (fun j hj hjS => ?_) x (fun j hj => ?_)
  · have he : (∑ j ∈ J, if j ∈ nbr (twSupp n) (star n v) then
        ∑ i ∈ star n v, κ j i * loopOsc n v i else 0) =
        2 * ∑ j ∈ cross n R, if j ∈ nbr (twSupp n) (star n v) then
          κ j (prev n v, 0) + κ j (v, 0) else 0 := by
      rw [Finset.mul_sum, hJdef, Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h1 : j ∈ nbr (twSupp n) (star n v)
      · simp [h1, loop_sum n hn κ v j]
      · by_cases h2 : j ∈ star n v <;> simp [h1, h2]
    rw [he] at h
    linarith
  · have hbox := (Finset.mem_filter.1 hj).2
    have hnb : j ∈ nbr (twSupp n) (star n v) := (Finset.mem_union.1 hbox).resolve_left hjS
    have h1 : j ≠ (prev n v, 0) := fun e => hjS (e ▸ (line_mem_star n v).1)
    have h2 : j ≠ (v, 0) := fun e => hjS (e ▸ (line_mem_star n v).2)
    have h3 : j ∉ loopRest n v := fun h => (loopRest_far n hn v j h).2 hnb
    simp [loopOsc, lineOsc, h1, h2, h3]
  · rw [tflip_apply]
    have : tflipCoef n R (star n v) j = 1 := by
      unfold tflipCoef
      by_cases hbox : j ∈ star n v ∪ nbr (twSupp n) (star n v)
      · rw [if_pos hbox]
        refine flipCoef_not_cross n R j fun hc => hj (Finset.mem_filter.2 ⟨hc, hbox⟩)
      · rw [if_neg hbox]
    rw [this, one_mul]

/-- **At flat boundary condition the rectangle is near one.** The closing links are frozen at flat values with
trivial transport, so the box sees exactly the two-link line. -/
theorem loop_expectation (hn : 2 ≤ n) (v : Vertex (2 * n)) (β : ℝ) (hβ : 1 / 32 ≤ β) :
    1 - lineDefect β ≤
      E SU2HaarTilt.haar (twFactor n β) (twFactor_continuous n β) (star n v) (loopObs n v)
        (flatState n) := by
  have hflat : restVal n v (flatState n) = 1 := by
    have l0 (y : Vertex (2 * n)) : flatLink y 0 = 1 := by simp [flatLink]
    have l1 (y : Vertex (2 * n)) : flatLink y 1 = if y 1 = 0 then TwistedFlat.qI else 1 := by
      simp [flatLink]
    simp only [restVal, flatState, l0, l1, pt_coord1, inv_one, mul_one, one_mul, mul_inv_cancel_right,
      mul_inv_cancel]
  have hpt (V : Link (2 * n) → Q) : loopObs n v (overwrite (star n v) (flatState n) V) =
      lineObs n v (overwrite (star n v) (flatState n) V) := by
    have hr : restVal n v (overwrite (star n v) (flatState n) V) = 1 := by
      rw [← hflat]
      refine restVal_congr n v _ _ fun i hi => ?_
      simp [overwrite_apply, (loopRest_far n hn v i hi).1]
    rw [loopObs_apply, hr, mul_one]
    rfl
  have h := line_expectation n v β hβ
  rw [E_apply] at h ⊢
  simp only [hpt]
  exact h

/-- **The two links of the line receive total boundary influence at least four times the expectation of the
rectangle at flat boundary condition.** The four crossing sets are disjoint, and each carries that much. No coupling
hypothesis. -/
theorem row_lower (hn : 2 ≤ n) (v : Vertex (2 * n)) (β : ℝ) (w : ℝ)
    (hw : w ≤ E SU2HaarTilt.haar (twFactor n β) (twFactor_continuous n β) (star n v) (loopObs n v) (flatState n))
    {𝓐 : Submodule ℝ C(Link (2 * n) → Q, ℝ)} (hmem : loopObs n v ∈ 𝓐)
    (κ : Link (2 * n) → Link (2 * n) → ℝ) (hκ : ∀ j i, 0 ≤ κ j i)
    (hinf : BlockInfluenceOn SU2HaarTilt.haar (twSupp n) (twFactor n β) (twFactor_continuous n β) 𝓐
      (star n v) κ) :
    4 * w ≤ ∑ j ∈ nbr (twSupp n) (star n v), (κ j (prev n v, 0) + κ j (v, 0)) := by
  set f : Link (2 * n) → ℝ := fun j => κ j (prev n v, 0) + κ j (v, 0) with hf
  have hf0 (j : Link (2 * n)) : 0 ≤ f j := add_nonneg (hκ _ _) (hκ _ _)
  have hbound (R : Finset (Vertex (2 * n)))
      (hR : ((prev n v, (0 : Fin 4)) ∈ cross n R ∧ (v, (0 : Fin 4)) ∉ cross n R) ∨
        ((prev n v, (0 : Fin 4)) ∉ cross n R ∧ (v, (0 : Fin 4)) ∈ cross n R)) :
      w ≤ ∑ j, if j ∈ cross n R ∧ j ∈ nbr (twSupp n) (star n v) then f j else 0 := by
    have h := loop_cross_bound n hn β κ v hmem hinf R hR (flatState n)
    have he : (∑ j ∈ cross n R, if j ∈ nbr (twSupp n) (star n v) then
        κ j (prev n v, 0) + κ j (v, 0) else 0) =
        ∑ j, if j ∈ cross n R ∧ j ∈ nbr (twSupp n) (star n v) then f j else 0 := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j ∈ cross n R)
        (fun j => if j ∈ cross n R ∧ j ∈ nbr (twSupp n) (star n v) then f j else 0)]
      rw [Finset.sum_eq_zero (s := Finset.univ.filter fun j => ¬ j ∈ cross n R), add_zero]
      · have hfilter : (Finset.univ.filter fun j => j ∈ cross n R) = cross n R := by
          ext j
          simp
        rw [hfilter]
        refine Finset.sum_congr rfl fun j hj => ?_
        simp [hj, hf]
      · intro j hj
        have : j ∉ cross n R := (Finset.mem_filter.1 hj).2
        simp [this]
    rw [he] at h
    exact hw.trans ((le_abs_self _).trans h)
  have hA := hbound _ (Or.inl (regionA_ok n hn v))
  have hB := hbound _ (Or.inr (regionB_ok n hn v))
  have hC := hbound _ (Or.inl (regionC_ok n hn v))
  have hD := hbound _ (Or.inr (regionD_ok n hn v))
  have hsum : (∑ j, if j ∈ cross n (regionA n v) ∧ j ∈ nbr (twSupp n) (star n v) then f j else 0) +
      (∑ j, if j ∈ cross n (regionB n v) ∧ j ∈ nbr (twSupp n) (star n v) then f j else 0) +
      (∑ j, if j ∈ cross n (regionC n v) ∧ j ∈ nbr (twSupp n) (star n v) then f j else 0) +
      (∑ j, if j ∈ cross n (regionD n v) ∧ j ∈ nbr (twSupp n) (star n v) then f j else 0) ≤
      ∑ j ∈ nbr (twSupp n) (star n v), f j := by
    simp only [← Finset.sum_add_distrib]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j ∈ nbr (twSupp n) (star n v))]
    rw [Finset.sum_eq_zero (s := Finset.univ.filter fun j => ¬ j ∈ nbr (twSupp n) (star n v)), add_zero]
    · have hfilter : (Finset.univ.filter fun j => j ∈ nbr (twSupp n) (star n v)) =
          nbr (twSupp n) (star n v) := by
        ext j
        simp
      rw [hfilter]
      refine Finset.sum_le_sum fun j hj => ?_
      obtain ⟨p1, p2, p3, p4, p5, p6⟩ := cross_pair n hn v j hj
      have hfj := hf0 j
      by_cases a : j ∈ cross n (regionA n v) <;> by_cases b : j ∈ cross n (regionB n v) <;>
        by_cases c : j ∈ cross n (regionC n v) <;> by_cases d : j ∈ cross n (regionD n v) <;>
        simp_all
    · intro j hj
      have : j ∉ nbr (twSupp n) (star n v) := (Finset.mem_filter.1 hj).2
      simp [this]
  linarith

/-- **The margin of the star criterion in terms of the rectangle.** If the expectation of every rectangle at flat
boundary condition is at least `w`, then `ε ≤ 2 - 4 w`, whatever the influences, on any class of observables
containing the rectangles. No coupling hypothesis. So the criterion needs `w ≤ 1/2`. -/
theorem star_margin_of_expectation {Color : Type*} [Fintype Color] [DecidableEq Color] [Nonempty Color]
    (hn : 2 ≤ n) (β : ℝ) (w : ℝ)
    (hw : ∀ v, w ≤ E SU2HaarTilt.haar (twFactor n β) (twFactor_continuous n β) (star n v) (loopObs n v)
      (flatState n))
    {𝓐 : Submodule ℝ C(Link (2 * n) → Q, ℝ)} (hmem : ∀ v, loopObs n v ∈ 𝓐)
    (κ : Vertex (2 * n) → Link (2 * n) → Link (2 * n) → ℝ)
    (color : Vertex (2 * n) → Color) (ε : ℝ)
    (hc : BoxCriterionOn SU2HaarTilt.haar (twSupp n) (twFactor n β) (twFactor_continuous n β) 𝓐 (star n)
      κ color ε) : ε ≤ 2 - 4 * w := by
  have h10 := one_ne (n := n)
  have hstep (u : Vertex (2 * n)) : u ≠ step (2 * n) u 0 := fun e => h10 (by
    have := congrFun e 0
    rw [step_zero] at this
    linear_combination -this)
  have hfilter (u : Vertex (2 * n)) :
      (Finset.univ.filter fun k => (u, (0 : Fin 4)) ∈ star n k) = {u, step (2 * n) u 0} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton,
      mem_star]
    constructor
    · rintro (e | e)
      · exact Or.inl e.symm
      · exact Or.inr e.symm
    · rintro (e | e)
      · exact Or.inl e.symm
      · exact Or.inr e.symm
  have hmargin (u : Vertex (2 * n)) : ε ≤ 2 - row (twSupp n) (star n) κ u (u, 0) -
      row (twSupp n) (star n) κ (step (2 * n) u 0) (u, 0) := by
    have := hc.margin (u, 0)
    rw [hfilter, Finset.sum_pair (hstep u)] at this
    linarith
  have hsum : (Fintype.card (Vertex (2 * n)) : ℝ) * ε ≤ ∑ u, (2 - row (twSupp n) (star n) κ u (u, 0) -
      row (twSupp n) (star n) κ (step (2 * n) u 0) (u, 0)) := by
    have := Finset.sum_le_sum (s := Finset.univ) fun u _ => hmargin u
    simpa using this
  have hshift : (∑ u, row (twSupp n) (star n) κ (step (2 * n) u 0) (u, 0)) =
      ∑ v, row (twSupp n) (star n) κ v (prev n v, 0) := by
    have hg : ∀ g : Vertex (2 * n) → ℝ, (∑ u, g (step (2 * n) u 0)) = ∑ v, g v := fun g =>
      Equiv.sum_comp (Equiv.addRight (Pi.single 0 1 : Vertex (2 * n))) g
    rw [← hg fun v => row (twSupp n) (star n) κ v (prev n v, 0)]
    refine Finset.sum_congr rfl fun u _ => ?_
    have e : prev n (step (2 * n) u 0) = u := by simp [prev, step]
    simp only [e]
  have hrow (v : Vertex (2 * n)) : 4 * w ≤
      row (twSupp n) (star n) κ v (v, 0) + row (twSupp n) (star n) κ v (prev n v, 0) := by
    have h := row_lower n hn v β w (hw v) (hmem v) (κ v) (hc.nonneg v) (hc.influence v)
    unfold row
    rw [← Finset.sum_add_distrib]
    refine h.trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    ring
  have hV : (0 : ℝ) < Fintype.card (Vertex (2 * n)) := by exact_mod_cast Fintype.card_pos
  have hrows : (Fintype.card (Vertex (2 * n)) : ℝ) * (4 * w) ≤
      ∑ v, (row (twSupp n) (star n) κ v (v, 0) + row (twSupp n) (star n) κ v (prev n v, 0)) := by
    have := Finset.sum_le_sum (s := Finset.univ) fun v _ => hrow v
    simpa using this
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hshift] at hsum
  rw [Finset.sum_add_distrib] at hrows
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hfin : (Fintype.card (Vertex (2 * n)) : ℝ) * ε ≤
      (Fintype.card (Vertex (2 * n)) : ℝ) * (2 - 4 * w) := by
    nlinarith
  exact le_of_mul_le_mul_left hfin hV

/-- The margin of the star criterion is bounded above by the line defect. -/
theorem star_margin {Color : Type*} [Fintype Color] [DecidableEq Color] [Nonempty Color] (hn : 2 ≤ n)
    (β : ℝ) (hβ : 1 / 32 ≤ β) {𝓐 : Submodule ℝ C(Link (2 * n) → Q, ℝ)} (hmem : ∀ v, loopObs n v ∈ 𝓐)
    (κ : Vertex (2 * n) → Link (2 * n) → Link (2 * n) → ℝ)
    (color : Vertex (2 * n) → Color) (ε : ℝ)
    (hc : BoxCriterionOn SU2HaarTilt.haar (twSupp n) (twFactor n β) (twFactor_continuous n β) 𝓐 (star n)
      κ color ε) : ε ≤ 4 * lineDefect β - 2 := by
  have h := star_margin_of_expectation n hn β (1 - lineDefect β)
    (fun v => loop_expectation n hn v β hβ) hmem κ color ε hc
  linarith

/-- **No-go for the star criterion at weak coupling.** Once `lineDefect β < 1/2`, no block influences of any
size, and no colouring, satisfy the criterion with nonnegative margin, on any lattice of side `2n ≥ 4`, even when
the influences are tested only on a class of observables containing the closed rectangles. The threshold does not
depend on the lattice size. It is the failure of this criterion for this block family, not of mixing. -/
theorem star_no_go_on {Color : Type*} [Fintype Color] [DecidableEq Color] [Nonempty Color] (hn : 2 ≤ n)
    (β : ℝ) (hβ : 1 / 32 ≤ β) (hδ : lineDefect β < 1 / 2)
    {𝓐 : Submodule ℝ C(Link (2 * n) → Q, ℝ)} (hmem : ∀ v, loopObs n v ∈ 𝓐)
    (κ : Vertex (2 * n) → Link (2 * n) → Link (2 * n) → ℝ) (color : Vertex (2 * n) → Color) (ε : ℝ)
    (hε : 0 ≤ ε) :
    ¬ BoxCriterionOn SU2HaarTilt.haar (twSupp n) (twFactor n β) (twFactor_continuous n β) 𝓐 (star n)
      κ color ε := fun hc => by
  have := star_margin n hn β hβ hmem κ color ε hc
  linarith

/-- The no-go for the criterion tested on every continuous function. -/
theorem star_no_go {Color : Type*} [Fintype Color] [DecidableEq Color] [Nonempty Color] (hn : 2 ≤ n)
    (β : ℝ) (hβ : 1 / 32 ≤ β) (hδ : lineDefect β < 1 / 2)
    (κ : Vertex (2 * n) → Link (2 * n) → Link (2 * n) → ℝ) (color : Vertex (2 * n) → Color) (ε : ℝ)
    (hε : 0 ≤ ε) :
    ¬ BoxCriterion SU2HaarTilt.haar (twSupp n) (twFactor n β) (twFactor_continuous n β) (star n)
      κ color ε :=
  star_no_go_on n hn β hβ hδ (fun _ => Submodule.mem_top) κ color ε hε

/-! ### Gauge-invariant observables -/

/-- A gauge transformation acting on link coordinates. -/
def gaugeAct (g : Vertex (2 * n) → Q) : C(Link (2 * n) → Q, Link (2 * n) → Q) :=
  ⟨fun U i => g i.1 * U i * (g (step (2 * n) i.1 i.2))⁻¹,
    continuous_pi fun i => (continuous_const.mul (continuous_apply i)).mul continuous_const⟩

theorem gaugeAct_apply (g : Vertex (2 * n) → Q) (U : Link (2 * n) → Q) (i : Link (2 * n)) :
    gaugeAct n g U i = g i.1 * U i * (g (step (2 * n) i.1 i.2))⁻¹ := rfl

theorem gauge_plaq (g : Vertex (2 * n) → Q) (U : Link (2 * n) → Q) (x : Vertex (2 * n)) (μ ν : Fin 4) :
    plaquetteProduct (2 * n) Q (toConfiguration (2 * n) (gaugeAct n g U)) x μ ν =
      g x * plaquetteProduct (2 * n) Q (toConfiguration (2 * n) U) x μ ν * (g x)⁻¹ := by
  rw [plaq_coord, plaq_coord]
  simp only [gaugeAct_apply]
  rw [step_comm (2 * n) x ν μ]
  group

theorem gauge_factor (β : ℝ) (g : Vertex (2 * n) → Q) (p : PlaquetteIndex (2 * n)) (U : Link (2 * n) → Q) :
    twFactor n β p (gaugeAct n g U) = twFactor n β p U := by
  unfold twFactor TwistedReflection.term
  rw [gauge_plaq, WilsonSingleLinkStaples.character_classFunction]

theorem gauge_preserving (g : Vertex (2 * n) → Q) :
    (Measure.pi fun _ : Link (2 * n) => SU2HaarTilt.haar).map (gaugeAct n g) =
      Measure.pi fun _ : Link (2 * n) => SU2HaarTilt.haar := by
  have hm (i : Link (2 * n)) :
      Measurable fun q : Q => g i.1 * q * (g (step (2 * n) i.1 i.2))⁻¹ :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have h := Measure.pi_map_pi (μ := fun _ : Link (2 * n) => SU2HaarTilt.haar)
    (f := fun i q => g i.1 * q * (g (step (2 * n) i.1 i.2))⁻¹) (fun i => (hm i).aemeasurable)
  change (Measure.pi fun _ : Link (2 * n) => SU2HaarTilt.haar).map
    (fun U i => g i.1 * U i * (g (step (2 * n) i.1 i.2))⁻¹) = _
  rw [h]
  congr 1
  funext i
  have hl : Measurable fun q : Q => g i.1 * q := (continuous_const.mul continuous_id).measurable
  have hr : Measurable fun q : Q => q * (g (step (2 * n) i.1 i.2))⁻¹ :=
    (continuous_id.mul continuous_const).measurable
  have hc : (fun q : Q => g i.1 * q * (g (step (2 * n) i.1 i.2))⁻¹) =
      (fun q => q * (g (step (2 * n) i.1 i.2))⁻¹) ∘ fun q => g i.1 * q := rfl
  change (SU2HaarTilt.haar).map (fun q : Q => g i.1 * q * (g (step (2 * n) i.1 i.2))⁻¹) = SU2HaarTilt.haar
  rw [hc, ← Measure.map_map hr hl, map_mul_left_eq_self, map_mul_right_eq_self]

theorem gauge_overwrite (g : Vertex (2 * n) → Q) (S : Finset (Link (2 * n))) (x V : Link (2 * n) → Q) :
    overwrite S (gaugeAct n g x) (gaugeAct n g V) = gaugeAct n g (overwrite S x V) := by
  funext i
  by_cases hi : i ∈ S <;> simp [overwrite_apply, gaugeAct_apply, hi]

/-- The gauge-invariant continuous observables, for the group `SU(2)` on links. -/
def gaugeClass : Submodule ℝ C(Link (2 * n) → Q, ℝ) where
  carrier := {F | ∀ (g : Vertex (2 * n) → Q) (U : Link (2 * n) → Q), F (gaugeAct n g U) = F U}
  add_mem' := fun {F G} hF hG g U => by
    change F _ + G _ = F _ + G _
    rw [hF g U, hG g U]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c {F} hF g U => by
    change c • F _ = c • F _
    rw [hF g U]

theorem mem_gaugeClass (F : C(Link (2 * n) → Q, ℝ)) :
    F ∈ gaugeClass n ↔ ∀ (g : Vertex (2 * n) → Q) (U : Link (2 * n) → Q), F (gaugeAct n g U) = F U :=
  Iff.rfl

theorem const_mem_gaugeClass (c : ℝ) : ContinuousMap.const (Link (2 * n) → Q) c ∈ gaugeClass n :=
  fun _ _ => rfl

/-- **The conditional expectation of a box preserves gauge invariance.** So the dynamics act on gauge-invariant
observables, and mixing and the Poincaré inequality may be asked of them alone. -/
theorem gaugeClass_stable (β : ℝ) :
    Stable SU2HaarTilt.haar (twFactor n β) (twFactor_continuous n β) (gaugeClass n) := by
  intro S F hF g U
  rw [E_symm (twFactor_depends n β) (gaugeAct n g) (gauge_preserving n g) S
    (fun p _ U => gauge_factor n β g p U) (fun x V => gauge_overwrite n g S x V) F U]
  have hcomp : F.comp (gaugeAct n g) = F := by
    ext V
    exact hF g V
  rw [hcomp]

/-- Half the real trace is a class function. -/
theorem re_conj (g X : Q) : ((g * X * g⁻¹ : Q) : Quaternion ℝ).re = (X : Quaternion ℝ).re := by
  have h := WilsonSingleLinkStaples.realTrace_cyclic g (X * g⁻¹)
  have e1 : g * (X * g⁻¹) = g * X * g⁻¹ := (mul_assoc _ _ _).symm
  have e2 : X * g⁻¹ * g = X := by group
  rw [e1, e2] at h
  linarith

/-- **The rectangle is gauge invariant.** -/
theorem loopObs_mem_gaugeClass (v : Vertex (2 * n)) : loopObs n v ∈ gaugeClass n := by
  intro g U
  have e1 : step (2 * n) (pt n v 1 0) 0 = pt n v 2 0 := pt_step0 n v 1 0 2 (by norm_num)
  have e2 : step (2 * n) (pt n v 2 0) 1 = pt n v 2 1 := pt_step1 n v 2 0 1 (by norm_num)
  have e3 : step (2 * n) (pt n v 2 1) 1 = pt n v 2 2 := pt_step1 n v 2 1 2 (by norm_num)
  have e4 : step (2 * n) (pt n v 1 2) 0 = pt n v 2 2 := pt_step0 n v 1 2 2 (by norm_num)
  have e5 : step (2 * n) (pt n v 0 2) 0 = pt n v 1 2 := pt_step0 n v 0 2 1 (by norm_num)
  have e6 : step (2 * n) (pt n v (-1) 2) 0 = pt n v 0 2 := pt_step0 n v (-1) 2 0 (by norm_num)
  have e7 : step (2 * n) (pt n v (-2) 2) 0 = pt n v (-1) 2 := pt_step0 n v (-2) 2 (-1) (by ring)
  have e8 : step (2 * n) (pt n v (-2) 1) 1 = pt n v (-2) 2 := pt_step1 n v (-2) 1 2 (by norm_num)
  have e9 : step (2 * n) (pt n v (-2) 0) 1 = pt n v (-2) 1 := pt_step1 n v (-2) 0 1 (by norm_num)
  have e10 : step (2 * n) (pt n v (-2) 0) 0 = prev n v := by
    rw [pt_step0 n v (-2) 0 (-1) (by ring)]
    simp [pt, prev, sub_eq_add_neg, Pi.single_neg]
  have e11 : step (2 * n) v 0 = pt n v 1 0 := by
    simp [pt, step]
  have hprod : gaugeAct n g U (prev n v, 0) * gaugeAct n g U (v, 0) * restVal n v (gaugeAct n g U) =
      g (prev n v) * (U (prev n v, 0) * U (v, 0) * restVal n v U) * (g (prev n v))⁻¹ := by
    simp only [restVal, gaugeAct_apply, step_prev, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
    group
  rw [loopObs_apply, loopObs_apply, hprod, re_conj]

/-- **The star no-go on gauge-invariant observables.** Restricting the influences to gauge-invariant test functions
does not rescue the star at weak coupling. -/
theorem star_no_go_gauge {Color : Type*} [Fintype Color] [DecidableEq Color] [Nonempty Color] (hn : 2 ≤ n)
    (β : ℝ) (hβ : 1 / 32 ≤ β) (hδ : lineDefect β < 1 / 2)
    (κ : Vertex (2 * n) → Link (2 * n) → Link (2 * n) → ℝ) (color : Vertex (2 * n) → Color) (ε : ℝ)
    (hε : 0 ≤ ε) :
    ¬ BoxCriterionOn SU2HaarTilt.haar (twSupp n) (twFactor n β) (twFactor_continuous n β) (gaugeClass n)
      (star n) κ color ε :=
  star_no_go_on n hn β hβ hδ (loopObs_mem_gaugeClass n) κ color ε hε

/-- The contrast: at strong coupling the star criterion does hold on gauge-invariant observables, so the no-go is a
statement about the coupling and not about the class. -/
theorem star_criterion_gauge (h4 : 4 ∣ 2 * n) (β : ℝ) (hβ : 0 ≤ β) (hs : 288 * β < 1) :
    BoxCriterionOn SU2HaarTilt.haar (twSupp n) (twFactor n β) (twFactor_continuous n β) (gaugeClass n) (star n)
      (fun k j _ => kappaOf (twSupp n) (fun _ => 4 * β) (star n k) j) (starColor n h4) (1 - 288 * β) :=
  (star_criterion n h4 β hβ hs).mono le_top

/-- The line defect tends to zero. -/
theorem lineDefect_tendsto : Filter.Tendsto lineDefect Filter.atTop (nhds 0) := by
  have hcap1 : 0 < SU2GaussianMass.cap 1 := by
    have h := SU2GaussianMass.mass_cap_lower 1 (by norm_num)
    have h0 := SU2GaussianMass.cap_nonneg 1 (by norm_num)
    by_contra hcon
    have : SU2GaussianMass.cap 1 = 0 := le_antisymm (not_lt.1 hcon) h0
    rw [this, mul_zero] at h
    linarith
  have hlog : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
    simpa using this
  have h24 : Filter.Tendsto (fun β : ℝ => 24 * β) Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop (by norm_num)
  have hl := hlog.comp h24
  have hinv : Filter.Tendsto (fun β : ℝ => β⁻¹) Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  have hlim := (hinv.const_mul (16 * Real.log (SU2GaussianMass.cap 1))).add
    (hl.const_mul (16 * 24 * (3 / 2)))
  simp only [mul_zero, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with β hβ
  have hs : (0 : ℝ) < 24 * β := by positivity
  have hcapv : SU2GaussianMass.cap (24 * β) =
      SU2GaussianMass.cap 1 * ((24 * β) * Real.sqrt (24 * β)) := by
    unfold SU2GaussianMass.cap
    simp only [Real.sqrt_one, mul_one]
    ring
  have hsq : Real.log (Real.sqrt (24 * β)) = Real.log (24 * β) / 2 := by
    rw [Real.log_sqrt hs.le]
  have hsq0 : 0 < Real.sqrt (24 * β) := Real.sqrt_pos.2 hs
  simp only [Function.comp, lineDefect]
  rw [hcapv, Real.log_mul hcap1.ne' (by positivity), Real.log_mul hs.ne' hsq0.ne', hsq]
  push_cast
  field_simp
  ring

/-- There is a coupling above which the star criterion fails on every lattice. -/
theorem exists_threshold : ∃ β₀ : ℝ, ∀ β, β₀ ≤ β → 1 / 32 ≤ β ∧ lineDefect β < 1 / 2 := by
  have h := (lineDefect_tendsto.eventually_lt_const (show (0 : ℝ) < 1 / 2 by norm_num)).and
    (Filter.eventually_ge_atTop (1 / 32 : ℝ))
  obtain ⟨β₀, hβ₀⟩ := Filter.eventually_atTop.1 h
  exact ⟨β₀, fun β hβ => ⟨(hβ₀ β hβ).2, (hβ₀ β hβ).1⟩⟩

/-! ### The strong-coupling statements for the twisted law -/

/-- **A volume-free Poincaré inequality for the twisted law at strong coupling.** The right side is the sum of
conditional variances over the 256 colours of vertex stars. -/
theorem twisted_poincare (h4 : 4 ∣ 2 * n) (β : ℝ) (hβ : 0 ≤ β) (hs : 288 * β < 1)
    (F : C(Link (2 * n) → Q, ℝ)) :
    (1 - 288 * β) * ∫ U, (F U - ∫ V, F V
        ∂gibbs SU2HaarTilt.haar (twFactor n β) (twFactor_continuous n β)) ^ 2
        ∂gibbs SU2HaarTilt.haar (twFactor n β) (twFactor_continuous n β) ≤
      ∑ c : Fin 4 → ZMod 4, ∫ U, (F U - E SU2HaarTilt.haar (twFactor n β) (twFactor_continuous n β)
        (colorBlock (star n) (starColor n h4) c) F U) ^ 2
        ∂gibbs SU2HaarTilt.haar (twFactor n β) (twFactor_continuous n β) :=
  poincare (twFactor_depends n β) (stable_top _ _ _) Submodule.mem_top
    (star_criterion n h4 β hβ hs) F Submodule.mem_top

/-- **Exponential clustering in the torus distance for the twisted law at strong coupling.** Stated for
observables of the configuration under the literal law `twistedLaw`. Supports are given in link coordinates. The
rate depends only on `β` and the constant only on the size of the support of `F`, not on `n`. -/
theorem twisted_law_covariance (h4 : 4 ∣ 2 * n) (β : ℝ) (hβ : 0 ≤ β) (hs : 288 * β < 1)
    (A B : Finset (Link (2 * n))) (F G : C(Configuration (Vertex (2 * n)) Q, ℝ))
    (hF : DependsOn (fun U : Link (2 * n) → Q => F (toConfiguration (2 * n) U)) (A : Set (Link (2 * n))))
    (hG : DependsOn (fun U : Link (2 * n) → Q => G (toConfiguration (2 * n) U)) (B : Set (Link (2 * n))))
    (k : ℕ) (hfar : ∀ a ∈ A, ∀ c ∈ B, ¬ Close n (2 * k) a.1 c.1) :
    |(∫ U, F U * G U ∂TwistedLocalization.twistedLaw n β) -
        (∫ U, F U ∂TwistedLocalization.twistedLaw n β) *
          ∫ U, G U ∂TwistedLocalization.twistedLaw n β| ≤
      starRate β ^ k * (2 * A.card * ‖F‖) * ‖G‖ := by
  let T : C(Link (2 * n) → Q, Configuration (Vertex (2 * n)) Q) :=
    ⟨toConfiguration (2 * n), toConfiguration_continuous n⟩
  have h := twisted_covariance n h4 β hβ hs A B (F.comp T) (G.comp T) hF hG k hfar
  have hFn : ‖F.comp T‖ ≤ ‖F‖ :=
    (ContinuousMap.norm_le _ (norm_nonneg F)).2 fun x => F.norm_coe_le_norm _
  have hGn : ‖G.comp T‖ ≤ ‖G‖ :=
    (ContinuousMap.norm_le _ (norm_nonneg G)).2 fun x => G.norm_coe_le_norm _
  have hr : 0 ≤ starRate β := rate_nonneg (by
    have hC : (1 : ℝ) ≤ Fintype.card (Fin 4 → ZMod 4) := by
      exact_mod_cast Fintype.card_pos (α := Fin 4 → ZMod 4)
    linarith [mul_nonneg (show (0 : ℝ) ≤ 288 by norm_num) hβ])
  rw [← twGibbs_integral n β (fun U => F U * G U), ← twGibbs_integral n β (fun U => F U),
    ← twGibbs_integral n β (fun U => G U)]
  refine h.trans ?_
  have hp := pow_nonneg hr k
  have hA : (0 : ℝ) ≤ 2 * A.card := by positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hFn hA) hp) hGn
    (norm_nonneg _) (by positivity)

end Twisted

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedBridge
