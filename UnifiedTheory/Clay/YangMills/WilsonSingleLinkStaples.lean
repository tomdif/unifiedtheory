/- Exact six-staple dictionary for the actual periodic four-dimensional Wilson action.
For n > 1, all six incident plaquettes are distinct. Their actual oriented
products give explicit exterior staple triples for every selected direction.
The fundamental quaternion SU(2) action and arbitrary weighted plaquette source
are derived in the true exterior/link split, with volume-independent vector
bounds. No affine-action premise, Haar slice formula, or continuum claim is used. -/
import UnifiedTheory.Clay.YangMills.WilsonIndependentBlocks
import UnifiedTheory.Clay.YangMills.PeriodicPlaquetteReflection
import UnifiedTheory.Clay.YangMills.WilsonBlockIntegration
import UnifiedTheory.Clay.YangMills.SU2QuaternionEquivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonSingleLinkStaples
noncomputable section
open RegulatedGauge PeriodicLattice4 PeriodicTimeReflection PeriodicPlaquetteReflection
open WilsonUniformVariance SingleLinkWilsonOscillation WilsonIndependentBlocks
open scoped BigOperators

variable (n : ℕ) [NeZero n] [Fact (1 < n)]
local instance : DecidableEq (Edge (Vertex n)) := Classical.decEq _

def backward (x : Vertex n) (ν : Fin 4) : Vertex n := x - Pi.single ν 1

omit [NeZero n] [Fact (1 < n)] in
@[simp] theorem step_backward (x : Vertex n) (ν : Fin 4) :
    step n (backward n x ν) ν = x := by simp [step, backward]

omit [NeZero n] in
theorem backward_ne (x : Vertex n) (ν : Fin 4) : backward n x ν ≠ x := by
  intro he
  have h := step_backward n x ν
  rw [he] at h
  exact PeriodicPlaquetteNontriviality.step_ne n x ν h

omit [NeZero n] in
/-- All six affected plaquettes are distinct on the nondegenerate periodic lattice. -/
theorem affected_card_eq_six (x : Vertex n) (μ : Fin 4) :
    (affected n x μ).card = 6 := by
  classical
  unfold affected
  rw [Finset.card_biUnion]
  · have hp (p : Plane) :
        ({(x, p), (x - Pi.single (transverse μ p) 1, p)} : Finset (PlaquetteIndex n)).card = 2 := by
      have hne : (x, p) ≠ (x - Pi.single (transverse μ p) 1, p) := by
        intro h
        exact backward_ne n x (transverse μ p) (congrArg Prod.fst h).symm
      simp [hne]
    simp_rw [hp]
    simp [planes_card]
  · intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro a hap haq
    have ha : a.2 = p := by
      rcases Finset.mem_insert.mp hap with h | h
      · exact congrArg Prod.snd h
      · exact congrArg Prod.snd (Finset.mem_singleton.mp h)
    have hb : a.2 = q := by
      rcases Finset.mem_insert.mp haq with h | h
      · exact congrArg Prod.snd h
      · exact congrArg Prod.snd (Finset.mem_singleton.mp h)
    exact hpq (ha.symm.trans hb)

variable (G : Type*) [Group G]

def replaceLink (U : Configuration (Vertex n) G) (x : Vertex n) (μ : Fin 4) (q : G) :
    Configuration (Vertex n) G := Function.update U (selectedLink n x μ) q

omit [NeZero n] [Fact (1 < n)] [Group G] in
@[simp] theorem link_replace_self (U : Configuration (Vertex n) G)
    (x : Vertex n) (μ : Fin 4) (q : G) :
    linkValue n G (replaceLink n G U x μ q) x μ = q := by
  change Function.update U (selectedLink n x μ) q (selectedLink n x μ) = q
  simp

omit [NeZero n] [Fact (1 < n)] [Group G] in
theorem link_replace_other (U : Configuration (Vertex n) G)
    (x y : Vertex n) (μ ν : Fin 4) (q : G) (hne : (y, ν) ≠ (x, μ)) :
    linkValue n G (replaceLink n G U x μ q) y ν = linkValue n G U y ν := by
  have he : selectedLink n y ν ≠ selectedLink n x μ := by
    intro h
    exact hne (congrArg (edgeCoord n) h)
  exact Function.update_of_ne he _ _

/-- The forward staple uses the three exterior links of the square based at x. -/
def forwardStaple (U : Configuration (Vertex n) G) (x : Vertex n) (μ ν : Fin 4) : G :=
  linkValue n G U x ν * linkValue n G U (step n x ν) μ *
    (linkValue n G U (step n x μ) ν)⁻¹

/-- The backward staple uses the three exterior links of the preceding square. -/
def backwardStaple (U : Configuration (Vertex n) G) (x : Vertex n) (μ ν : Fin 4) : G :=
  (linkValue n G U (backward n x ν) ν)⁻¹ * linkValue n G U (backward n x ν) μ *
    linkValue n G U (step n (backward n x ν) μ) ν

omit [NeZero n] in
theorem plaquette_replace_forward (U : Configuration (Vertex n) G)
    (x : Vertex n) (μ ν : Fin 4) (hμν : μ ≠ ν) (q : G) :
    plaquetteProduct n G (replaceLink n G U x μ q) x μ ν =
      q * (forwardStaple n G U x μ ν)⁻¹ := by
  have hdir (y : Vertex n) : (y, ν) ≠ (x, μ) := fun h => hμν (congrArg Prod.snd h).symm
  have hstep : (step n x ν, μ) ≠ (x, μ) :=
    fun h => PeriodicPlaquetteNontriviality.step_ne n x ν (congrArg Prod.fst h)
  simp only [plaquetteProduct, link_replace_self,
    link_replace_other n G U x _ μ ν q (hdir _),
    link_replace_other n G U x _ μ μ q hstep]
  unfold forwardStaple
  group

omit [NeZero n] in
theorem plaquette_replace_backward (U : Configuration (Vertex n) G)
    (x : Vertex n) (μ ν : Fin 4) (hμν : μ ≠ ν) (q : G) :
    plaquetteProduct n G (replaceLink n G U x μ q) (backward n x ν) μ ν =
      linkValue n G U (backward n x ν) μ *
        linkValue n G U (step n (backward n x ν) μ) ν * q⁻¹ *
          (linkValue n G U (backward n x ν) ν)⁻¹ := by
  have hdir (y : Vertex n) : (y, ν) ≠ (x, μ) := fun h => hμν (congrArg Prod.snd h).symm
  have hbase : (backward n x ν, μ) ≠ (x, μ) :=
    fun h => backward_ne n x ν (congrArg Prod.fst h)
  simp only [plaquetteProduct, step_backward, link_replace_self,
    link_replace_other n G U x _ μ ν q (hdir _),
    link_replace_other n G U x _ μ μ q hbase]

omit [NeZero n] [Fact (1 < n)] in
theorem plaquette_swap (U : Configuration (Vertex n) G) (x : Vertex n) (μ ν : Fin 4) :
    plaquetteProduct n G U x ν μ = (plaquetteProduct n G U x μ ν)⁻¹ := by
  unfold plaquetteProduct
  group

/-- The actual staple assigned to each affected canonically oriented plaquette. -/
def staple (U : Configuration (Vertex n) G) (x : Vertex n) (μ : Fin 4)
    (p : PlaquetteIndex n) : G :=
  if p.1 = x then forwardStaple n G U x μ (transverse μ p.2)
  else backwardStaple n G U x μ (transverse μ p.2)

omit [NeZero n] [Fact (1 < n)] in
theorem trace_plaquette_order (tr : G → ℝ) (hinv : ∀ q, tr q⁻¹ = tr q)
    (U : Configuration (Vertex n) G) (x : Vertex n) (μ : Fin 4) (p : Plane)
    (hp : p ∈ planes μ) :
    tr (plaquetteProduct n G U x p.1.1 p.1.2) =
      tr (plaquetteProduct n G U x μ (transverse μ p)) := by
  have hplane : p.1.1 = μ ∨ p.1.2 = μ := by simpa [planes] using hp
  rcases hplane with h | h
  · simp [transverse, h]
  · have hn : p.1.1 ≠ μ := by rw [← h]; exact ne_of_lt p.2
    simp only [transverse, if_neg hn, h]
    rw [plaquette_swap, hinv]

omit [NeZero n] in
theorem trace_plaquette_replace (tr : G → ℝ)
    (hcyc : ∀ a b, tr (a * b) = tr (b * a)) (hinv : ∀ q, tr q⁻¹ = tr q)
    (U : Configuration (Vertex n) G) (x : Vertex n) (μ : Fin 4)
    (q : G) (p : PlaquetteIndex n) (hp : p ∈ affected n x μ) :
    tr (plaquetteProduct n G (replaceLink n G U x μ q) p.1 p.2.1.1 p.2.1.2) =
      tr (q * (staple n G U x μ p)⁻¹) := by
  obtain ⟨hplane, hbase⟩ := (mem_affected_iff n x μ p).mp hp
  have hμν : μ ≠ transverse μ p.2 := by
    have ht : p.2.1.1 = μ ∨ p.2.1.2 = μ := by simpa [planes] using hplane
    rcases ht with h | h
    · simp only [transverse, h, ite_true]
      rw [← h]
      exact ne_of_lt p.2.2
    · have hn : p.2.1.1 ≠ μ := by rw [← h]; exact ne_of_lt p.2.2
      simpa only [transverse, if_neg hn] using hn.symm
  rw [trace_plaquette_order n G tr hinv _ _ μ _ hplane]
  rcases hbase with hbase | hbase
  · rw [staple, if_pos hbase, hbase]
    exact congrArg tr (plaquette_replace_forward n G U x μ _ hμν q)
  · have hb : p.1 = backward n x (transverse μ p.2) := hbase
    have hn : p.1 ≠ x := hb ▸ backward_ne n x _
    rw [staple, if_neg hn, hb]
    rw [plaquette_replace_backward n G U x μ _ hμν q]
    let a := linkValue n G U (backward n x (transverse μ p.2)) μ
    let b := linkValue n G U (step n (backward n x (transverse μ p.2)) μ)
      (transverse μ p.2)
    let d := linkValue n G U (backward n x (transverse μ p.2)) (transverse μ p.2)
    change tr (a * b * q⁻¹ * d⁻¹) = tr (q * (d⁻¹ * a * b)⁻¹)
    calc
      _ = tr ((a * b * q⁻¹ * d⁻¹)⁻¹) := (hinv _).symm
      _ = tr (d * (q * b⁻¹ * a⁻¹)) := congrArg tr (by group)
      _ = tr ((q * b⁻¹ * a⁻¹) * d) := hcyc _ _
      _ = _ := congrArg tr (by group)

/-- Unit quaternions carry the already constructed fundamental SU(2) representation. -/
abbrev Q := SU2QuaternionEquivalence.UnitQuaternion

def character (q : Q) : ℂ := Matrix.trace (SU2QuaternionCoordinates.toMatrix q)

theorem character_re (q : Q) : (character q).re = 2 * (q : Quaternion ℝ).re :=
  SU2QuaternionCoordinates.realTrace_toMatrix q

theorem character_continuous : Continuous character := by
  have he : character = (fun q : Q => ((2 * (q : Quaternion ℝ).re : ℝ) : ℂ)) := by
    funext q
    exact SU2QuaternionCoordinates.trace_toMatrix q
  rw [he]
  exact Complex.continuous_ofReal.comp
    (continuous_const.mul (Quaternion.continuous_re.comp continuous_subtype_val))

theorem character_mul_comm (a b : Q) : character (a * b) = character (b * a) := by
  change Matrix.trace (SU2QuaternionCoordinates.toMatrix
    ((a : Quaternion ℝ) * (b : Quaternion ℝ))) =
    Matrix.trace (SU2QuaternionCoordinates.toMatrix ((b : Quaternion ℝ) * (a : Quaternion ℝ)))
  rw [SU2QuaternionCoordinates.toMatrix_mul, SU2QuaternionCoordinates.toMatrix_mul]
  exact Matrix.trace_mul_comm _ _

theorem character_classFunction : ClassFunction Q character := by
  intro g h
  calc
    character (g * h * g⁻¹) = character (g * (h * g⁻¹)) := congrArg character (mul_assoc _ _ _)
    _ = character ((h * g⁻¹) * g) := character_mul_comm _ _
    _ = character h := by group

theorem realTrace_cyclic (a b : Q) :
    2 * ((a * b : Q) : Quaternion ℝ).re = 2 * ((b * a : Q) : Quaternion ℝ).re := by
  change 2 * ((a : Quaternion ℝ) * (b : Quaternion ℝ)).re =
    2 * ((b : Quaternion ℝ) * (a : Quaternion ℝ)).re
  simp only [Quaternion.re_mul]
  ring

theorem realTrace_inverse (q : Q) :
    2 * ((q⁻¹ : Q) : Quaternion ℝ).re = 2 * (q : Quaternion ℝ).re := by
  change 2 * (star (q : Quaternion ℝ)).re = _
  simp

theorem character_inverse_re (q : Q) : (character q⁻¹).re = (character q).re := by
  rw [character_re, character_re]
  exact realTrace_inverse q

/-- The source coefficient vector retains the actual six individual weights. -/
def weightedStaple (U : Configuration (Vertex n) Q) (x : Vertex n) (μ : Fin 4)
    (f : PlaquetteIndex n → ℝ) : Quaternion ℝ :=
  ∑ p ∈ affected n x μ, f p • (staple n Q U x μ p : Quaternion ℝ)

def stapleSum (U : Configuration (Vertex n) Q) (x : Vertex n) (μ : Fin 4) : Quaternion ℝ :=
  weightedStaple n U x μ (fun _ => 1)

omit [NeZero n] in
/-- Each actual updated plaquette trace is linear in the quaternion coordinates. -/
theorem plaquette_character_replace (U : Configuration (Vertex n) Q)
    (x : Vertex n) (μ : Fin 4) (q : Q) (p : PlaquetteIndex n)
    (hp : p ∈ affected n x μ) :
    (character (plaquetteProduct n Q (replaceLink n Q U x μ q)
      p.1 p.2.1.1 p.2.1.2)).re =
        2 * inner ℝ (q : Quaternion ℝ) (staple n Q U x μ p : Quaternion ℝ) := by
  rw [character_re, trace_plaquette_replace n Q
    (fun a => 2 * (a : Quaternion ℝ).re) realTrace_cyclic realTrace_inverse U x μ q p hp]
  rfl

omit [NeZero n] in
theorem plaquetteTerm_replace (U : Configuration (Vertex n) Q)
    (x : Vertex n) (μ : Fin 4) (q : Q) (p : PlaquetteIndex n)
    (hp : p ∈ affected n x μ) :
    plaquetteTerm n Q character 2 (replaceLink n Q U x μ q) p =
      2 - 2 * inner ℝ (q : Quaternion ℝ) (staple n Q U x μ p : Quaternion ℝ) := by
  unfold plaquetteTerm WilsonMomentBounds.loopObservable
  change 2 - (character (holonomy (Quiver.Symmetrify (Vertex n)) Q
    (orientedExtension (Vertex n) Q (replaceLink n Q U x μ q))
      (plaquette n p.1 p.2.1.1 p.2.1.2))).re = _
  rw [plaquette_holonomy_eq_product, plaquette_character_replace n U x μ q p hp]

omit [NeZero n] in
/-- Exact local weighted insertion, before taking any conditional expectation. -/
theorem affected_source_replace (U : Configuration (Vertex n) Q)
    (x : Vertex n) (μ : Fin 4) (f : PlaquetteIndex n → ℝ) (q : Q) :
    (∑ p ∈ affected n x μ, f p * plaquetteTerm n Q character 2
      (replaceLink n Q U x μ q) p) =
        2 * (∑ p ∈ affected n x μ, f p) - 2 * inner ℝ (q : Quaternion ℝ)
          (weightedStaple n U x μ f) := by
  have ht : (∑ p ∈ affected n x μ, f p * plaquetteTerm n Q character 2
      (replaceLink n Q U x μ q) p) =
      ∑ p ∈ affected n x μ, f p *
        (2 - 2 * inner ℝ (q : Quaternion ℝ) (staple n Q U x μ p : Quaternion ℝ)) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [plaquetteTerm_replace n U x μ q p hp]
  rw [ht]
  simp only [weightedStaple, inner_sum, inner_smul_right, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- The exact source constant obtained by fixing the selected link to the identity. -/
def sourceConstant (U : Configuration (Vertex n) Q) (x : Vertex n) (μ : Fin 4)
    (f : PlaquetteIndex n → ℝ) : ℝ :=
  WilsonBlockIntegration.source n Q character 2 f (replaceLink n Q U x μ 1) +
    2 * inner ℝ (1 : Quaternion ℝ) (weightedStaple n U x μ f)

/-- All unaffected plaquettes cancel, giving the full interacting source dictionary. -/
theorem source_replace (U : Configuration (Vertex n) Q)
    (x : Vertex n) (μ : Fin 4) (f : PlaquetteIndex n → ℝ) (q : Q) :
    WilsonBlockIntegration.source n Q character 2 f (replaceLink n Q U x μ q) =
      sourceConstant n U x μ f - 2 * inner ℝ (q : Quaternion ℝ) (weightedStaple n U x μ f) := by
  have hd : WilsonBlockIntegration.source n Q character 2 f (replaceLink n Q U x μ q) -
      WilsonBlockIntegration.source n Q character 2 f (replaceLink n Q U x μ 1) =
      (∑ p ∈ affected n x μ, f p * plaquetteTerm n Q character 2
        (replaceLink n Q U x μ q) p) -
      (∑ p ∈ affected n x μ, f p * plaquetteTerm n Q character 2
        (replaceLink n Q U x μ 1) p) := by
    unfold WilsonBlockIntegration.source
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp
    have hh := plaquette_unchanged n Q x μ p hp
      (replaceLink n Q U x μ q) (replaceLink n Q U x μ 1) (by
        intro e he
        simp [replaceLink, Function.update_of_ne he])
    unfold plaquetteTerm WilsonMomentBounds.loopObservable
    change f p * (2 - (character _).re) - f p * (2 - (character _).re) = 0
    rw [hh]
    ring
  rw [affected_source_replace, affected_source_replace] at hd
  unfold sourceConstant
  change _ = _ + 2 * inner ℝ ((1 : Q) : Quaternion ℝ) (weightedStaple n U x μ f) - _
  linarith

/-- The actual Wilson action has the six-staple affine form with coefficient 2β. -/
theorem action_replace (U : Configuration (Vertex n) Q)
    (x : Vertex n) (μ : Fin 4) (β : ℝ) (q : Q) :
    orientedWilsonAction (Vertex n) Q character (base n) (loops n) β 2
      (replaceLink n Q U x μ q) =
        β * sourceConstant n U x μ (fun _ => 1) -
          2 * β * inner ℝ (q : Quaternion ℝ) (stapleSum n U x μ) := by
  have ha : orientedWilsonAction (Vertex n) Q character (base n) (loops n) β 2
      (replaceLink n Q U x μ q) =
      β * WilsonBlockIntegration.source n Q character 2 (fun _ => 1)
        (replaceLink n Q U x μ q) := by
    simp only [WilsonBlockIntegration.source, one_mul, plaquetteTerm]
    rfl
  rw [ha, source_replace]
  unfold stapleSum
  ring

omit [NeZero n] [Fact (1 < n)] in
/-- Unit staples give a bound independent of the lattice volume and exterior. -/
theorem weightedStaple_norm_le (U : Configuration (Vertex n) Q)
    (x : Vertex n) (μ : Fin 4) (f : PlaquetteIndex n → ℝ) :
    ‖weightedStaple n U x μ f‖ ≤ ∑ p ∈ affected n x μ, |f p| := by
  unfold weightedStaple
  calc
    _ ≤ ∑ p ∈ affected n x μ, ‖f p • (staple n Q U x μ p : Quaternion ℝ)‖ :=
      norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      rw [norm_smul, Real.norm_eq_abs, CStarRing.norm_coe_unitary, mul_one]

omit [NeZero n] in
theorem stapleSum_norm_le_six (U : Configuration (Vertex n) Q)
    (x : Vertex n) (μ : Fin 4) : ‖stapleSum n U x μ‖ ≤ 6 := by
  have h := weightedStaple_norm_le n U x μ (fun _ => 1)
  simpa only [stapleSum, abs_one, Finset.sum_const, nsmul_eq_mul,
    mul_one, affected_card_eq_six, Nat.cast_ofNat] using h

/-- The configuration fixed by an actual exterior, with the eliminated link set to one. -/
def exteriorConfig (x : Vertex n) (μ : Fin 4) (r : Exterior n Q x μ) :
    Configuration (Vertex n) Q :=
  SingleCoordinateProduct.assemble (selectedLink n x μ) (r, 1)

/-- The unweighted staple vector is a function only of retained exterior links. -/
def exteriorStaple (x : Vertex n) (μ : Fin 4) (r : Exterior n Q x μ) : Quaternion ℝ :=
  stapleSum n (exteriorConfig n x μ r) x μ

def exteriorWeightedStaple (x : Vertex n) (μ : Fin 4) (r : Exterior n Q x μ)
    (f : PlaquetteIndex n → ℝ) : Quaternion ℝ :=
  weightedStaple n (exteriorConfig n x μ r) x μ f

def exteriorSourceConstant (x : Vertex n) (μ : Fin 4) (r : Exterior n Q x μ)
    (f : PlaquetteIndex n → ℝ) : ℝ :=
  sourceConstant n (exteriorConfig n x μ r) x μ f

omit [Fact (1 < n)] in
theorem replaceLink_exteriorConfig (x : Vertex n) (μ : Fin 4) (r : Exterior n Q x μ)
    (q : Q) : replaceLink n Q (exteriorConfig n x μ r) x μ q =
      SingleCoordinateProduct.assemble (selectedLink n x μ) (r, q) := by
  funext e
  by_cases he : e = selectedLink n x μ
  · subst e
    simp [replaceLink, SingleCoordinateProduct.assemble_self]
  · simp [replaceLink, exteriorConfig, Function.update_of_ne he,
      SingleCoordinateProduct.assemble_other _ _ he]

/-- Exact full weighted Wilson source in the actual exterior/link coordinate split. -/
theorem source_assemble (x : Vertex n) (μ : Fin 4) (r : Exterior n Q x μ)
    (f : PlaquetteIndex n → ℝ) (q : Q) :
    WilsonBlockIntegration.source n Q character 2 f
      (SingleCoordinateProduct.assemble (selectedLink n x μ) (r, q)) =
        exteriorSourceConstant n x μ r f -
          2 * inner ℝ (q : Quaternion ℝ) (exteriorWeightedStaple n x μ r f) := by
  rw [← replaceLink_exteriorConfig]
  exact source_replace n (exteriorConfig n x μ r) x μ f q

/-- The actual conditioned Wilson action, with no supplied affine-action hypothesis. -/
theorem action_assemble (x : Vertex n) (μ : Fin 4) (r : Exterior n Q x μ)
    (β : ℝ) (q : Q) :
    orientedWilsonAction (Vertex n) Q character (base n) (loops n) β 2
      (SingleCoordinateProduct.assemble (selectedLink n x μ) (r, q)) =
        β * exteriorSourceConstant n x μ r (fun _ => 1) -
          2 * β * inner ℝ (q : Quaternion ℝ) (exteriorStaple n x μ r) := by
  rw [← replaceLink_exteriorConfig]
  exact action_replace n (exteriorConfig n x μ r) x μ β q

/-- Subtracting the exterior action leaves the exact local tilt relative to q=1. -/
theorem localAction_assemble (x : Vertex n) (μ : Fin 4) (r : Exterior n Q x μ)
    (β : ℝ) (q : Q) :
    WilsonUniformVariance.localAction n Q character β 2 x μ (r, q) =
      -2 * β * inner ℝ ((q : Quaternion ℝ) - 1) (exteriorStaple n x μ r) := by
  unfold WilsonUniformVariance.localAction WilsonUniformVariance.exteriorAction
  rw [action_assemble, action_assemble]
  simp only [inner_sub_left]
  change _ = -2 * β * (inner ℝ (q : Quaternion ℝ) (exteriorStaple n x μ r) -
    inner ℝ ((1 : Q) : Quaternion ℝ) (exteriorStaple n x μ r))
  ring

omit [NeZero n] in
theorem exteriorStaple_norm_le_six (x : Vertex n) (μ : Fin 4) (r : Exterior n Q x μ) :
    ‖exteriorStaple n x μ r‖ ≤ 6 :=
  stapleSum_norm_le_six n (exteriorConfig n x μ r) x μ

omit [NeZero n] [Fact (1 < n)] in
theorem exteriorWeightedStaple_norm_le (x : Vertex n) (μ : Fin 4) (r : Exterior n Q x μ)
    (f : PlaquetteIndex n → ℝ) :
    ‖exteriorWeightedStaple n x μ r f‖ ≤ ∑ p ∈ affected n x μ, |f p| :=
  weightedStaple_norm_le n (exteriorConfig n x μ r) x μ f

omit [NeZero n] [Fact (1 < n)] in
/-- The explicit exterior triples vary continuously with the original link variables. -/
theorem staple_continuous (x : Vertex n) (μ : Fin 4) (p : PlaquetteIndex n) :
    Continuous (fun U : Configuration (Vertex n) Q => staple n Q U x μ p) := by
  unfold staple
  split_ifs
  · unfold forwardStaple linkValue link
    fun_prop
  · unfold backwardStaple linkValue link
    fun_prop

omit [NeZero n] [Fact (1 < n)] in
theorem weightedStaple_continuous (x : Vertex n) (μ : Fin 4) (f : PlaquetteIndex n → ℝ) :
    Continuous (fun U : Configuration (Vertex n) Q => weightedStaple n U x μ f) := by
  unfold weightedStaple
  apply continuous_finset_sum
  intro p _
  exact continuous_const.smul (continuous_subtype_val.comp (staple_continuous n x μ p))

omit [Fact (1 < n)] in
theorem exteriorConfig_continuous (x : Vertex n) (μ : Fin 4) :
    Continuous (exteriorConfig n x μ) :=
  (SingleCoordinateProduct.assemble_continuous (selectedLink n x μ)).comp
    (continuous_id.prodMk continuous_const)

omit [Fact (1 < n)] in
theorem exteriorWeightedStaple_continuous (x : Vertex n) (μ : Fin 4)
    (f : PlaquetteIndex n → ℝ) : Continuous (fun r => exteriorWeightedStaple n x μ r f) :=
  (weightedStaple_continuous n x μ f).comp (exteriorConfig_continuous n x μ)

omit [Fact (1 < n)] in
theorem exteriorStaple_continuous (x : Vertex n) (μ : Fin 4) :
    Continuous (exteriorStaple n x μ) :=
  exteriorWeightedStaple_continuous n x μ (fun _ => 1)

end
end UnifiedTheory.Clay.YangMills.WilsonSingleLinkStaples
