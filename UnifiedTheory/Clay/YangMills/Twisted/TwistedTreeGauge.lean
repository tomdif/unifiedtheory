/- Exact tree-gauge reduction on a spatial slice. Fixing the existing coordinate-tree gauge is a
measure-preserving change of variables on Haar measure: off-tree links stay independent Haar and no
Jacobian appears. Gauge-invariant integrals, and the quadratic form of the twisted transfer operator,
reduce exactly to the off-tree links. Seam links are off-tree. No estimate is made here. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedVacuum
import UnifiedTheory.Clay.YangMills.WilsonAxialGauge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedTreeGauge
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonSlabGauge RegulatedGauge
open WilsonAxialGauge TwistedTransfer

/-! ### The abstract change of variables -/

section Abstract
variable {E V G : Type*} [Fintype E] [DecidableEq E] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G]

/-- The left-right translation of one link by a gauge depending on the tree links. -/
def treeMap (p : E → Prop) [DecidablePred p] (tail head : E → V) (g : (E → G) → V → G)
    (u : E → G) : E → G :=
  fun e => if p e then u e else g u (tail e) * u e * (g u (head e))⁻¹

/-- If the gauge depends only on tree links and continuously, `treeMap` preserves product Haar. -/
theorem treeMap_preserving (p : E → Prop) [DecidablePred p] (tail head : E → V)
    (g : (E → G) → V → G) (hg : ∀ u u' : E → G, (∀ e, p e → u e = u' e) → g u = g u')
    (hc : ∀ v, Continuous fun u => g u v) :
    MeasurePreserving (treeMap p tail head g)
      (Measure.pi fun _ : E => compactHaar G) (Measure.pi fun _ : E => compactHaar G) := by
  let μ : E → Measure G := fun _ => compactHaar G
  let split := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : E => G) p
  have hsplit : MeasurePreserving split (Measure.pi μ) _ :=
    measurePreserving_piEquivPiSubtypeProd μ p
  -- the gauge as a function of the tree part
  let g' : ({e // p e} → G) → V → G := fun a => g (split.symm (a, fun _ => 1))
  have hg' (u : E → G) : g u = g' (split u).1 := by
    apply hg
    intro e he
    change u e = (split.symm ((split u).1, fun _ => 1)) e
    simp [split, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, he]
  have hg'c (v : V) : Continuous fun a : {e // p e} → G => g' a v := by
    refine (hc v).comp ?_
    refine continuous_pi fun e => ?_
    by_cases he : p e
    · have : (fun a : {e // p e} → G => (split.symm (a, fun _ => 1)) e) =
          fun a => a ⟨e, he⟩ := by
        funext a
        simp [split, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, he]
      rw [this]
      exact continuous_apply _
    · have : (fun a : {e // p e} → G => (split.symm (a, fun _ => 1)) e) = fun _ => 1 := by
        funext a
        simp [split, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, he]
      rw [this]
      exact continuous_const
  let τ : ({e // p e} → G) → ({e // ¬ p e} → G) → ({e // ¬ p e} → G) :=
    fun a c e => g' a (tail e) * c e * (g' a (head e))⁻¹
  have hτc : Continuous (Function.uncurry τ) := by
    refine continuous_pi fun e => ?_
    have h1 : Continuous fun z : ({e // p e} → G) × ({e // ¬ p e} → G) => g' z.1 (tail e) :=
      (hg'c _).comp continuous_fst
    have h2 : Continuous fun z : ({e // p e} → G) × ({e // ¬ p e} → G) => g' z.1 (head e) :=
      (hg'c _).comp continuous_fst
    have h3 : Continuous fun z : ({e // p e} → G) × ({e // ¬ p e} → G) => z.2 e :=
      (continuous_apply e).comp continuous_snd
    exact (h1.mul h3).mul h2.inv
  have hτ (a : {e // p e} → G) :
      MeasurePreserving (τ a) (Measure.pi fun i : {e // ¬ p e} => μ i)
        (Measure.pi fun i : {e // ¬ p e} => μ i) := by
    refine measurePreserving_pi (fun i : {e // ¬ p e} => μ i) (fun i : {e // ¬ p e} => μ i)
      (f := fun e q => g' a (tail e) * q * (g' a (head e))⁻¹) (fun e => ?_)
    have h1 := measurePreserving_mul_left (compactHaar G) (g' a (tail e))
    have h2 := measurePreserving_mul_right (compactHaar G) (g' a (head e))⁻¹
    exact h2.comp h1
  have hskew := (MeasurePreserving.id (Measure.pi fun i : {e // p e} => μ i)).skew_product
    (g := τ) (μc := Measure.pi fun i : {e // ¬ p e} => μ i)
    (μd := Measure.pi fun i : {e // ¬ p e} => μ i) hτc.measurable
    (Filter.Eventually.of_forall fun a => (hτ a).map_eq)
  have hfact : treeMap p tail head g =
      split.symm ∘ (fun z => (id z.1, τ z.1 z.2)) ∘ split := by
    funext u e
    simp only [treeMap, Function.comp]
    rw [hg' u]
    by_cases he : p e
    · simp [split, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, he]
    · simp [split, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, he, τ]
  rw [hfact]
  exact hsplit.symm.comp (hskew.comp hsplit)

end Abstract

/-! ### The coordinate tree on a slice -/

variable (n : ℕ) [NeZero n]

/-- The links of the coordinate tree. Seam links are excluded. -/
def isTree (e : SpatialVertex n × Fin 3) : Prop :=
  (e.2 = 0 ∧ e.1 1 = 0 ∧ e.1 2 = 0 ∧ (e.1 0).val + 1 < n) ∨
    (e.2 = 1 ∧ e.1 2 = 0 ∧ (e.1 1).val + 1 < n) ∨ (e.2 = 2 ∧ (e.1 2).val + 1 < n)

open scoped Classical in
instance : DecidablePred (isTree n) := Classical.decPred _

theorem vertex_eta (x : SpatialVertex n) : vertex n (x 0).val (x 1).val (x 2).val = x := by
  funext i
  fin_cases i <;> simp [vertex]

theorem line_congr (u u' : Slice n) (x : SpatialVertex n) (i : Fin 3) (m : ℕ)
    (h : ∀ k < m, u (axis n x i k, i) = u' (axis n x i k, i)) : line n u x i m = line n u' x i m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [line]
    rw [ih fun k hk => h k (by omega), h m (by omega)]

theorem val_lt_of (k m : ℕ) (hk : k < m) (hm : m < n) : ((k : ZMod n)).val + 1 < n := by
  rw [ZMod.val_natCast_of_lt (by omega)]
  omega

/-- The tree gauge reads only tree links. -/
theorem gauge_congr (u u' : Slice n) (h : ∀ e, isTree n e → u e = u' e) :
    WilsonAxialGauge.gauge n u = WilsonAxialGauge.gauge n u' := by
  funext x
  have ha : (x 0).val < n := ZMod.val_lt _
  have hb : (x 1).val < n := ZMod.val_lt _
  have hc : (x 2).val < n := ZMod.val_lt _
  unfold WilsonAxialGauge.gauge path
  congr 1
  · congr 1
    · apply line_congr
      intro k hk
      rw [axis_vertex_zero]
      apply h
      refine Or.inl ⟨rfl, by simp [vertex], by simp [vertex], ?_⟩
      exact val_lt_of n k _ hk ha
    · apply line_congr
      intro k hk
      rw [axis_vertex_one]
      apply h
      refine Or.inr (Or.inl ⟨rfl, by simp [vertex], ?_⟩)
      exact val_lt_of n k _ hk hb
  · apply line_congr
    intro k hk
    rw [axis_vertex_two]
    apply h
    refine Or.inr (Or.inr ⟨rfl, ?_⟩)
    exact val_lt_of n k _ hk hc

/-- In the tree gauge every tree link is the identity. -/
theorem gauge_tree (u : Slice n) (e : SpatialVertex n × Fin 3) (he : isTree n e) :
    gaugeSlice (WilsonAxialGauge.gauge n u) u e = 1 := by
  rcases e with ⟨x, i⟩
  have hsub : ∀ {j : Fin 3}, x j = 0 → (x j).val = 0 := fun h => by rw [h, ZMod.val_zero]
  rcases he with ⟨hi, h1, h2, hv⟩ | ⟨hi, h2, hv⟩ | ⟨hi, hv⟩
  · change i = 0 at hi
    subst hi
    have h1' : x 1 = 0 := h1
    have h2' : x 2 = 0 := h2
    have hx : vertex n (x 0).val 0 0 = x := by
      have := vertex_eta n x
      rwa [hsub h1', hsub h2'] at this
    have := tree_zero n u (x 0).val hv
    rwa [hx] at this
  · change i = 1 at hi
    subst hi
    have h2' : x 2 = 0 := h2
    have hx : vertex n (x 0).val (x 1).val 0 = x := by
      have := vertex_eta n x
      rwa [hsub h2'] at this
    have := tree_one n u (x 0).val (x 1).val (ZMod.val_lt _) hv
    rwa [hx] at this
  · change i = 2 at hi
    subst hi
    have := tree_two n u (x 0).val (x 1).val (x 2).val (ZMod.val_lt _) (ZMod.val_lt _) hv
    rwa [vertex_eta] at this

theorem line_continuous (x : SpatialVertex n) (i : Fin 3) (m : ℕ) :
    Continuous fun u : Slice n => line n u x i m := by
  induction m with
  | zero => exact continuous_const
  | succ m ih =>
    simp only [line]
    exact ih.mul (continuous_apply _)

theorem gauge_continuous (x : SpatialVertex n) : Continuous fun u : Slice n => WilsonAxialGauge.gauge n u x := by
  unfold WilsonAxialGauge.gauge path
  exact ((line_continuous n _ _ _).mul (line_continuous n _ _ _)).mul (line_continuous n _ _ _)

/-- Replace tree links by the identity. -/
def treeFix (w : Slice n) : Slice n := fun e => if isTree n e then 1 else w e

theorem treeFix_continuous : Continuous (treeFix n) := by
  refine continuous_pi fun e => ?_
  unfold treeFix
  by_cases h : isTree n e
  · simp only [if_pos h]
    exact continuous_const
  · simp only [if_neg h]
    exact continuous_apply e

/-- The change of variables on the slice. -/
abbrev sliceMap : Slice n → Slice n :=
  treeMap (isTree n) (fun e => e.1) (fun e => spatialStep n e.1 e.2) (WilsonAxialGauge.gauge n)

theorem sliceMap_preserving :
    MeasurePreserving (sliceMap n) (WilsonSlabOperator.measure n) (WilsonSlabOperator.measure n) :=
  treeMap_preserving _ _ _ _ (gauge_congr n) (gauge_continuous n)

theorem gaugeSlice_eq (u : Slice n) : gaugeSlice (WilsonAxialGauge.gauge n u) u = treeFix n (sliceMap n u) := by
  funext e
  simp only [treeFix, sliceMap, treeMap]
  by_cases h : isTree n e
  · simp only [if_pos h]
    exact gauge_tree n u e h
  · simp only [if_neg h]
    rfl

/-- **Exact reduction of gauge-invariant integrals to off-tree links.** -/
theorem integral_invariant (F : C(Slice n, ℝ))
    (hF : ∀ (h : SliceGauge n WilsonSlabOperator.Q) u, F (gaugeSlice h u) = F u) :
    ∫ u, F u ∂WilsonSlabOperator.measure n = ∫ w, F (treeFix n w) ∂WilsonSlabOperator.measure n := by
  have hmp := sliceMap_preserving n
  have hc : Continuous fun w => F (treeFix n w) := F.continuous.comp (treeFix_continuous n)
  calc ∫ u, F u ∂WilsonSlabOperator.measure n
      = ∫ u, F (treeFix n (sliceMap n u)) ∂WilsonSlabOperator.measure n := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        dsimp only
        rw [← gaugeSlice_eq, hF]
    _ = ∫ w, F (treeFix n w) ∂Measure.map (sliceMap n) (WilsonSlabOperator.measure n) :=
        (integral_map hmp.measurable.aemeasurable hc.aestronglyMeasurable).symm
    _ = _ := by rw [hmp.map_eq]

/-! ### The twisted transfer form -/

theorem defect_gauge (h : SliceGauge n WilsonSlabOperator.Q) (u : Slice n) :
    defect n (gaugeSlice h u) = defect n u := by
  unfold defect
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun p _ => ?_
  rw [spatialHolonomy_gauge, WilsonSingleLinkStaples.character_classFunction]

theorem twistedKernel_gauge_left (β : ℝ) (h : SliceGauge n WilsonSlabOperator.Q) (u v : Slice n) :
    twistedKernel n β (gaugeSlice h u, v) = twistedKernel n β (u, v) := by
  simp only [twistedKernel_apply, weightRatio, defect_gauge]
  congr 2
  exact kernel_gauge_left _ WilsonSingleLinkStaples.character_classFunction
    WilsonSingleLinkStaples.character_inverse_re β 2 u v h

theorem twistedKernel_gauge_right (β : ℝ) (h : SliceGauge n WilsonSlabOperator.Q) (u v : Slice n) :
    twistedKernel n β (u, gaugeSlice h v) = twistedKernel n β (u, v) := by
  simp only [twistedKernel_apply, weightRatio, defect_gauge]
  congr 2
  exact kernel_gauge_right _ WilsonSingleLinkStaples.character_classFunction β 2 u v h

/-- **The transfer form on off-tree links.** For gauge-invariant real `f, g`, the quadratic form of
the actual twisted operator is the same integral with all tree links set to the identity. -/
theorem form_reduction (β : ℝ) (f g : C(Slice n, ℝ))
    (hf : ∀ (h : SliceGauge n WilsonSlabOperator.Q) u, f (gaugeSlice h u) = f u)
    (hg : ∀ (h : SliceGauge n WilsonSlabOperator.Q) u, g (gaugeSlice h u) = g u) :
    ∫ u, f u * (∫ v, twistedKernel n β (u, v) * g v ∂WilsonSlabOperator.measure n)
        ∂WilsonSlabOperator.measure n =
      ∫ a, f (treeFix n a) * (∫ b, twistedKernel n β (treeFix n a, treeFix n b) * g (treeFix n b)
        ∂WilsonSlabOperator.measure n) ∂WilsonSlabOperator.measure n := by
  -- reduce the inner integral
  have hinner (u : Slice n) :
      (∫ v, twistedKernel n β (u, v) * g v ∂WilsonSlabOperator.measure n) =
        ∫ b, twistedKernel n β (u, treeFix n b) * g (treeFix n b)
          ∂WilsonSlabOperator.measure n := by
    let F : C(Slice n, ℝ) :=
      ⟨fun v => twistedKernel n β (u, v) * g v,
        ((twistedKernel n β).continuous.comp (continuous_const.prodMk continuous_id)).mul
          g.continuous⟩
    refine integral_invariant n F fun h v => ?_
    change twistedKernel n β (u, gaugeSlice h v) * g (gaugeSlice h v) = _
    rw [twistedKernel_gauge_right, hg]
    rfl
  simp only [hinner]
  -- the outer function
  let g' : C(Slice n, ℝ) := g.comp ⟨treeFix n, treeFix_continuous n⟩
  let k' : C(Slice n × Slice n, ℝ) :=
    (twistedKernel n β).comp ⟨fun p => (p.1, treeFix n p.2),
      continuous_fst.prodMk ((treeFix_continuous n).comp continuous_snd)⟩
  let sm := WilsonPositiveGroundState.realSmoothing (WilsonSlabOperator.measure n) k' g'
  have hsm (u : Slice n) : sm u = ∫ b, twistedKernel n β (u, treeFix n b) * g (treeFix n b)
      ∂WilsonSlabOperator.measure n :=
    WilsonPositiveGroundState.realSmoothing_integral _ _ _ _
  let G : C(Slice n, ℝ) := f * sm
  have hG : ∀ (h : SliceGauge n WilsonSlabOperator.Q) u, G (gaugeSlice h u) = G u := by
    intro h u
    change f (gaugeSlice h u) * sm (gaugeSlice h u) = f u * sm u
    rw [hf, hsm, hsm]
    simp only [twistedKernel_gauge_left]
  have := integral_invariant n G hG
  change ∫ u, f u * sm u ∂_ = ∫ w, f (treeFix n w) * sm (treeFix n w) ∂_ at this
  simp only [hsm] at this
  exact this

/-- **The norm on off-tree links.** With `form_reduction`, the Rayleigh quotient of a gauge-invariant
function is unchanged by setting tree links to the identity. -/
theorem inner_reduction (f g : C(Slice n, ℝ))
    (hf : ∀ (h : SliceGauge n WilsonSlabOperator.Q) u, f (gaugeSlice h u) = f u)
    (hg : ∀ (h : SliceGauge n WilsonSlabOperator.Q) u, g (gaugeSlice h u) = g u) :
    ∫ u, f u * g u ∂WilsonSlabOperator.measure n =
      ∫ a, f (treeFix n a) * g (treeFix n a) ∂WilsonSlabOperator.measure n :=
  integral_invariant n (f * g) fun h u => by
    change f (gaugeSlice h u) * g (gaugeSlice h u) = f u * g u
    rw [hf, hg]

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedTreeGauge
