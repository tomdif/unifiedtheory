/- The valley in tree gauge, for the fixed-`n` chart.

* `slice_near_flat`: a slice with twisted potential at most `ε²` is, after a gauge and possibly the center flip, within
  `11 · scale n ε` of the flat slice on every link. This is `axial_near_flat` applied to the static lift.
* `treeGauge_close`, `treeGauge_gauge`: the tree gauge is Lipschitz with constant `6 n + 1` in the link distance, and a
  gauge transformation acts on it as one global rotation.
* `valley_close`: on the valley, with `√σ ≤ 1/(308 n³)`, the off-tree links in tree gauge lie within `1/2` of a single
  rotated reference. The center flip is excluded by `holo > 0`.
* `integral_valley_chart`: the chart identity for gauge-invariant functions supported in that valley, with no open
  hypothesis.

All of this is at fixed `n`. The threshold `σ ~ n⁻⁶` is far below the valley size used elsewhere, the three frame
directions are still in the coordinates, and the kernel is not treated. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedFixedN
import UnifiedTheory.Clay.YangMills.Twisted.TwistedNearFlat

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedValleyChart
noncomputable section
open MeasureTheory
open PeriodicLattice4 TwistedFlat TwistedStability TwistedLandau TwistedAxial TwistedNearFlat TwistedSeams
open WilsonTimeSlab WilsonSlabOperator TwistedTransfer TwistedTreeGauge TwistedSliceLift TwistedSemiclassical
open TwistedRectangle
open TwistedFixedN

variable (n : ℕ) [NeZero n]

/-! ### The tree gauge is Lipschitz -/

theorem d_mul_mul (a b c e : Q) : d (a * b) (c * e) ≤ d a c + d b e := by
  have h1 : d (a * b) (c * b) = d a c := d_mul_right b a c
  have h2 : d (c * b) (c * e) = d b e := d_mul_left c b e
  linarith only [d_triangle (a * b) (c * b) (c * e), h1, h2]

theorem d_inv (a b : Q) : d a⁻¹ b⁻¹ = d a b :=
  calc d a⁻¹ b⁻¹ = d (a⁻¹ * b * b⁻¹) (a⁻¹ * a * b⁻¹) := by rw [mul_inv_cancel_right, inv_mul_cancel, one_mul]
    _ = d (a⁻¹ * b) (a⁻¹ * a) := d_mul_right _ _ _
    _ = d b a := d_mul_left _ _ _
    _ = d a b := TwistedStability.d_comm _ _

theorem line_close (u v : Slice n) (δ : ℝ) (h : ∀ e, d (u e) (v e) ≤ δ) (x : SpatialVertex n) (i : Fin 3)
    (m : ℕ) : d (WilsonAxialGauge.line n u x i m) (WilsonAxialGauge.line n v x i m) ≤ m * δ := by
  induction m with
  | zero => simp [WilsonAxialGauge.line, d_self]
  | succ m ih =>
    simp only [WilsonAxialGauge.line]
    have := d_mul_mul (WilsonAxialGauge.line n u x i m) (u (WilsonAxialGauge.axis n x i m, i))
      (WilsonAxialGauge.line n v x i m) (v (WilsonAxialGauge.axis n x i m, i))
    push_cast
    linarith only [this, ih, h (WilsonAxialGauge.axis n x i m, i)]

theorem gauge_close (u v : Slice n) (δ : ℝ) (h : ∀ e, d (u e) (v e) ≤ δ) (x : SpatialVertex n) :
    d (WilsonAxialGauge.gauge n u x) (WilsonAxialGauge.gauge n v x) ≤ 3 * n * δ := by
  have hδ : 0 ≤ δ := (d_nonneg _ _).trans (h (x, 0))
  have hb (j : Fin 3) (y : SpatialVertex n) (i : Fin 3) :
      d (WilsonAxialGauge.line n u y i (x j).val) (WilsonAxialGauge.line n v y i (x j).val) ≤ n * δ := by
    refine (line_close n u v δ h y i _).trans (mul_le_mul_of_nonneg_right ?_ hδ)
    exact_mod_cast (ZMod.val_lt (x j)).le
  unfold WilsonAxialGauge.gauge WilsonAxialGauge.path
  refine (d_mul_mul _ _ _ _).trans ?_
  have := d_mul_mul (WilsonAxialGauge.line n u (WilsonAxialGauge.vertex n 0 0 0) 0 (x 0).val)
    (WilsonAxialGauge.line n u (WilsonAxialGauge.vertex n (x 0).val 0 0) 1 (x 1).val)
    (WilsonAxialGauge.line n v (WilsonAxialGauge.vertex n 0 0 0) 0 (x 0).val)
    (WilsonAxialGauge.line n v (WilsonAxialGauge.vertex n (x 0).val 0 0) 1 (x 1).val)
  linarith only [this, hb 0 (WilsonAxialGauge.vertex n 0 0 0) 0,
    hb 1 (WilsonAxialGauge.vertex n (x 0).val 0 0) 1, hb 2 (WilsonAxialGauge.vertex n (x 0).val (x 1).val 0) 2]

/-- A field in the coordinate-tree gauge. -/
def treeGauge (u : Slice n) : Slice n := gaugeSlice (WilsonAxialGauge.gauge n u) u

/-- **The tree gauge is Lipschitz**, with constant `6 n + 1`. -/
theorem treeGauge_close (u v : Slice n) (δ : ℝ) (h : ∀ e, d (u e) (v e) ≤ δ) (e : SpatialVertex n × Fin 3) :
    d (treeGauge n u e) (treeGauge n v e) ≤ (6 * n + 1) * δ := by
  unfold treeGauge gaugeSlice
  have g1 := gauge_close n u v δ h e.1
  have g2 := gauge_close n u v δ h (spatialStep n e.1 e.2)
  rw [← d_inv] at g2
  have m1 := d_mul_mul (WilsonAxialGauge.gauge n u e.1 * u e) (WilsonAxialGauge.gauge n u (spatialStep n e.1 e.2))⁻¹
    (WilsonAxialGauge.gauge n v e.1 * v e) (WilsonAxialGauge.gauge n v (spatialStep n e.1 e.2))⁻¹
  have m2 := d_mul_mul (WilsonAxialGauge.gauge n u e.1) (u e) (WilsonAxialGauge.gauge n v e.1) (v e)
  linarith only [m1, m2, g1, g2, h e]

theorem line_gauge (k : SliceGauge n Q) (u : Slice n) (x : SpatialVertex n) (i : Fin 3) (m : ℕ) :
    WilsonAxialGauge.line n (gaugeSlice k u) x i m =
      k x * WilsonAxialGauge.line n u x i m * (k (WilsonAxialGauge.axis n x i m))⁻¹ := by
  induction m with
  | zero => simp [WilsonAxialGauge.line, WilsonAxialGauge.axis]
  | succ m ih =>
    have hs : spatialStep n (WilsonAxialGauge.axis n x i m) i = WilsonAxialGauge.axis n x i (m + 1) := by
      unfold spatialStep WilsonAxialGauge.axis
      rw [add_assoc, ← Pi.single_add]
      push_cast
      rfl
    simp only [WilsonAxialGauge.line, ih, gaugeSlice, hs]
    group

theorem gauge_gauge (k : SliceGauge n Q) (u : Slice n) :
    WilsonAxialGauge.gauge n (gaugeSlice k u) =
      fun x => k (WilsonAxialGauge.vertex n 0 0 0) * WilsonAxialGauge.gauge n u x * (k x)⁻¹ := by
  funext x
  unfold WilsonAxialGauge.gauge WilsonAxialGauge.path
  rw [line_gauge, line_gauge, line_gauge, WilsonAxialGauge.axis_vertex_zero, WilsonAxialGauge.axis_vertex_one,
    WilsonAxialGauge.axis_vertex_two, vertex_eta]
  group

/-- **A gauge transformation acts on the tree gauge as one global rotation.** -/
theorem treeGauge_gauge (k : SliceGauge n Q) (u : Slice n) :
    treeGauge n (gaugeSlice k u) = gaugeSlice (fun _ => k (WilsonAxialGauge.vertex n 0 0 0)) (treeGauge n u) := by
  unfold treeGauge
  rw [gauge_gauge]
  funext e
  simp only [gaugeSlice]
  group

theorem line_one (x : SpatialVertex n) (i : Fin 3) (m : ℕ) :
    WilsonAxialGauge.line n (fun _ => (1 : Q)) x i m = 1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [WilsonAxialGauge.line, ih]

/-- A field already in tree gauge is its own tree gauge. -/
theorem treeGauge_treeGlue (x : {e : SpatialVertex n × Fin 3 // ¬ isTree n e} → Q) :
    treeGauge n (treeGlue n x) = treeGlue n x := by
  have hg : WilsonAxialGauge.gauge n (treeGlue n x) = fun _ => 1 := by
    rw [gauge_congr n (treeGlue n x) (fun _ => 1) fun e he => by simp [treeGlue, he]]
    funext y
    simp [WilsonAxialGauge.gauge, WilsonAxialGauge.path, line_one]
  unfold treeGauge
  rw [hg]
  funext e
  simp [gaugeSlice]

/-! ### The slice near the flat slice -/

/-- A spatial vertex at time `0`. -/
def emb (y : SpatialVertex n) : Vertex n := Fin.cons 0 y

theorem sp_emb (y : SpatialVertex n) : sp n (emb n y) = y := by
  funext i
  simp [sp, emb]

theorem step_emb (y : SpatialVertex n) (i : Fin 3) : step n (emb n y) i.succ = emb n (spatialStep n y i) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [step, emb, Fin.succ_ne_zero]
  · by_cases h : j = i
    · subst h
      simp [step, emb, spatialStep]
    · have h' : j.succ ≠ i.succ := fun e => h (Fin.succ_injective _ e)
      simp [step, emb, spatialStep, Pi.single_apply, h, h']

/-- The flat slice: `qI` across `y₀ = 0` in direction 0, `qJ` across `y₁ = 0` in direction 1. -/
def sliceFlat : Slice n := fun e => flatLink (emb n e.1) e.2.succ

/-- The center shift of the direction-2 links on the sheet `y₂ = 0`. -/
def shiftSlice (c : Q) (u : Slice n) : Slice n := fun e => if e.2 = 2 ∧ e.1 2 = 0 then c * u e else u e

theorem sgn_emb (c₃ c₀ : Q) (y : SpatialVertex n) (i : Fin 3) :
    sgn c₃ c₀ (emb n y) i.succ = if i = 2 ∧ y 2 = 0 then c₃ else 1 := by
  fin_cases i <;> simp [sgn, emb] <;> rfl

theorem central_conj (s R a b c : Q) (hs : ∀ g : Q, s * g = g * s) :
    s * (R * (a * b * c⁻¹) * R⁻¹) = (R * a) * (s * b) * (R * c)⁻¹ := by
  have e : (R * a) * (s * b) * (R * c)⁻¹ = ((R * a) * s) * b * c⁻¹ * R⁻¹ := by group
  rw [e, ← hs (R * a)]
  group

theorem lift_defect_le (u : Slice n) (ε : ℝ) (h0 : 0 ≤ ε) (hS : twistedPotential n u ≤ ε ^ 2) (x : Vertex n)
    (μ ν : Fin 4) (h : μ < ν) : TwistedStability.defect (lift n u) μ ν x ≤ ε := by
  induction μ using Fin.cases with
  | zero =>
    induction ν using Fin.cases with
    | zero => exact absurd h (lt_irrefl _)
    | succ j =>
      unfold TwistedStability.defect
      rw [lift_plaquette_time]
      have : twistExp (N := n) 0 j.succ x = 0 := by simp [twistExp]
      rw [this, pow_zero, d_self]
      exact h0
  | succ i =>
    induction ν using Fin.cases with
    | zero => exact absurd h (Fin.not_lt_zero _)
    | succ j =>
      have hij : i < j := Fin.succ_lt_succ_iff.mp h
      have h1 := defect_sq_le_potential n u (sp n x) ⟨(i, j), hij⟩ x rfl
      exact abs_le_of_sq_le_sq' (h1.trans hS) h0 |>.2

/-- **A slice of small twisted potential is near the flat slice.** After a slice gauge and possibly the center flip of
the sheet `y₂ = 0`, every link is within `11 · scale n ε` of the flat slice. -/
theorem slice_near_flat (u : Slice n) (ε : ℝ) (h0 : 0 ≤ ε) (hS : twistedPotential n u ≤ ε ^ 2)
    (hsmall : 3 * scale n ε ≤ 1 / 2) :
    ∃ (k : SliceGauge n Q) (c : Q), (c = 1 ∨ c = ω) ∧
      ∀ e, d (gaugeSlice k (shiftSlice n c u) e) (sliceFlat n e) ≤ 11 * scale n ε := by
  have hN : 1 ≤ n := NeZero.pos n
  obtain ⟨g₀, hax⟩ := exists_axial (lift n u)
  have hdef : ∀ x μ ν, μ < ν → TwistedStability.defect (act g₀ (lift n u)) μ ν x ≤ ε := by
    intro x μ ν h
    rw [defect_act]
    exact lift_defect_le n u ε h0 hS x μ ν h
  obtain ⟨R, c₃, c₀, h₃, h₀, hb⟩ := axial_near_flat (N := n) hN _ hax ε h0 hdef hsmall
  refine ⟨fun y => R * g₀ (emb n y), c₃, h₃, ?_⟩
  rintro ⟨y, i⟩
  have hc : ∀ g : Q, c₃ * g = g * c₃ := by
    rcases h₃ with rfl | rfl
    · simp
    · exact fun g => (ω_commute g).eq
  have key := hb (emb n y) i.succ
  rw [sgn_emb] at key
  have hA : act g₀ (lift n u) (emb n y) i.succ =
      g₀ (emb n y) * u (y, i) * (g₀ (emb n (spatialStep n y i)))⁻¹ := by
    simp only [act, lift_succ, sp_emb, step_emb]
  rw [hA] at key
  change d ((R * g₀ (emb n y)) * shiftSlice n c₃ u (y, i) * (R * g₀ (emb n (spatialStep n y i)))⁻¹)
    (flatLink (emb n y) i.succ) ≤ _
  unfold shiftSlice
  by_cases hi : i = 2 ∧ y 2 = 0
  · simp only [hi, and_self, if_true] at key ⊢
    rw [← central_conj c₃ R _ _ _ hc]
    exact key
  · simp only [hi, if_false, one_mul] at key ⊢
    have e : R * g₀ (emb n y) * u (y, i) * (R * g₀ (emb n (spatialStep n y i)))⁻¹ =
        R * (g₀ (emb n y) * u (y, i) * (g₀ (emb n (spatialStep n y i)))⁻¹) * R⁻¹ := by group
    rw [e]
    exact key

/-! ### The valley in tree gauge -/

theorem holo_close (u v : Slice n) (δ : ℝ) (h : ∀ e, d (u e) (v e) ≤ δ) :
    |holo n u - holo n v| ≤ n * δ := by
  have h1 := abs_re_sub_le (wind3 n u) (wind3 n v)
  have h2 := run_lipschitz (lift n u) (lift n v) 3 (base n) n
  have h3 : ∑ k ∈ Finset.range n,
      d (lift n u (walk 3 (base n) k) 3) (lift n v (walk 3 (base n) k) 3) ≤ n * δ := by
    calc _ ≤ ∑ _k ∈ Finset.range n, δ :=
          Finset.sum_le_sum fun k _ => h (sp n (walk 3 (base n) k), 2)
      _ = n * δ := by simp
  exact h1.trans (h2.trans h3)

theorem holo_sliceFlat : holo n (sliceFlat n) = 1 := by
  have hl : ∀ x : Vertex n, lift n (sliceFlat n) x 3 = 1 := by
    intro x
    change flatLink (emb n (sp n x)) 3 = 1
    simp [flatLink]
  have hr : ∀ m, run (lift n (sliceFlat n)) 3 (base n) m = 1 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => simp [run, ih, hl]
  unfold holo wind3
  rw [hr]
  simp

theorem shiftSlice_one (u : Slice n) : shiftSlice n 1 u = u := by
  funext e
  simp [shiftSlice]

theorem shiftSlice_omega (u : Slice n) : shiftSlice n ω u = TwistedTransfer.flip n 2 0 u := rfl

/-- The reference: the flat slice in tree gauge, on the off-tree links. -/
def refField : {e : SpatialVertex n × Fin 3 // ¬ isTree n e} → Q := fun e => treeGauge n (sliceFlat n) e.1

theorem scale_le (ε : ℝ) (h0 : 0 ≤ ε) : scale n ε ≤ 2 * (n : ℝ) ^ 2 * ε := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast NeZero.pos n
  have : (n : ℝ) * ε ≤ n * n * ε := by
    have := mul_le_mul_of_nonneg_right hn (mul_nonneg (by linarith only [hn] : (0 : ℝ) ≤ n) h0)
    linarith only [this]
  calc scale n ε = (n : ℝ) * ε + n * n * ε := by unfold scale; ring
    _ ≤ n * n * ε + n * n * ε := by linarith only [this]
    _ = 2 * (n : ℝ) ^ 2 * ε := by ring

/-- **The valley in tree gauge is near one rotated reference.** If `√σ ≤ 1/(308 n³)` and the tree-gauge field with
off-tree links `x` lies in `valley n σ`, then some rotation brings the reference within `1/2` of every off-tree link. The
center flip is excluded by `holo > 0`. -/
theorem valley_close (σ : ℝ) (hσ : Real.sqrt σ ≤ 1 / (308 * (n : ℝ) ^ 3))
    (x : {e : SpatialVertex n × Fin 3 // ¬ isTree n e} → Q) (hx : treeGlue n x ∈ valley n σ) :
    ∃ h : Q, ∀ e, d (x e) (h * refField n e * h⁻¹) ≤ 1 / 2 := by
  set ε := Real.sqrt σ with hε
  set u := treeGlue n x with hu
  have h0 : 0 ≤ ε := Real.sqrt_nonneg _
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast NeZero.pos n
  have hσ0 : 0 ≤ σ := (TwistedSliceLift.potential_nonneg n u).trans hx.1.le
  have hS : twistedPotential n u ≤ ε ^ 2 := by
    rw [hε, Real.sq_sqrt hσ0]
    exact hx.1.le
  have hn3 : ε * (308 * (n : ℝ) ^ 3) ≤ 1 := (le_div_iff₀ (by positivity)).mp hσ
  have hsc := scale_le n ε h0
  have hsc0 : 0 ≤ scale n ε := by
    unfold scale
    positivity
  have hn23 : (n : ℝ) ^ 2 * ε ≤ (n : ℝ) ^ 3 * ε :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hn1 (by norm_num)) h0
  set δ := 11 * scale n ε with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  have hδ : (6 * n + 1) * δ ≤ 1 / 2 := by
    have a1 : (6 * (n : ℝ) + 1) * δ ≤ 7 * n * δ := mul_le_mul_of_nonneg_right (by linarith only [hn1]) hδ0
    have a2 : 7 * (n : ℝ) * δ ≤ 7 * n * (22 * (n : ℝ) ^ 2 * ε) :=
      mul_le_mul_of_nonneg_left (by linarith only [hsc]) (by positivity)
    have a3 : 7 * (n : ℝ) * (22 * (n : ℝ) ^ 2 * ε) = 154 * ((n : ℝ) ^ 3 * ε) := by ring
    have a4 : ε * (308 * (n : ℝ) ^ 3) = 308 * ((n : ℝ) ^ 3 * ε) := by ring
    linarith only [a1, a2, a3, a4, hn3]
  have hsmall : 3 * scale n ε ≤ 1 / 2 := by
    have a4 : ε * (308 * (n : ℝ) ^ 3) = 308 * ((n : ℝ) ^ 3 * ε) := by ring
    linarith only [hsc, hn23, hn3, a4]
  have hnδ : n * δ < 1 := by
    have a1 : (n : ℝ) * δ ≤ n * (22 * (n : ℝ) ^ 2 * ε) :=
      mul_le_mul_of_nonneg_left (by linarith only [hsc]) (by positivity)
    have a2 : (n : ℝ) * (22 * (n : ℝ) ^ 2 * ε) = 22 * ((n : ℝ) ^ 3 * ε) := by ring
    have a4 : ε * (308 * (n : ℝ) ^ 3) = 308 * ((n : ℝ) ^ 3 * ε) := by ring
    linarith only [a1, a2, a4, hn3]
  obtain ⟨k, c, hc, hk⟩ := slice_near_flat n u ε h0 hS hsmall
  have hc1 : c = 1 := by
    rcases hc with hc | hc
    · exact hc
    · exfalso
      have hh := holo_close n _ _ δ hk
      rw [holo_gauge, hc, shiftSlice_omega, holo_flip, holo_sliceFlat] at hh
      have hpos : 0 < holo n u := hx.2
      have := (abs_le.mp hh).1
      linarith only [this, hpos, hnδ]
  subst hc1
  rw [shiftSlice_one] at hk
  set K := k (WilsonAxialGauge.vertex n 0 0 0) with hK
  refine ⟨K⁻¹, fun e => ?_⟩
  have ht := treeGauge_close n _ _ δ hk e.1
  rw [treeGauge_gauge, hu, treeGauge_treeGlue] at ht
  have hxe : treeGlue n x e.1 = x e := by simp [treeGlue, e.2]
  simp only [gaugeSlice, hxe] at ht
  rw [← d_conj K (x e) _]
  have e1 : K * (K⁻¹ * refField n e * K⁻¹⁻¹) * K⁻¹ = refField n e := by group
  rw [e1]
  exact ht.trans hδ

/-- **The chart identity on the valley, with no open hypothesis.** For a gauge-invariant function supported in
`valley n σ` with `√σ ≤ 1/(308 n³)`, the integral is the integral over gnomonic coordinates around the flat reference,
divided by the frame weight, which is at least `ballMass (1/4)` on the support. -/
theorem integral_valley_chart (σ : ℝ) (hσ : Real.sqrt σ ≤ 1 / (308 * (n : ℝ) ^ 3)) (F : C(Slice n, ℝ))
    (hF : ∀ (h : SliceGauge n Q) u, F (gaugeSlice h u) = F u) (hsupp : ∀ u, F u ≠ 0 → u ∈ valley n σ) :
    ∫ u, F u ∂WilsonSlabOperator.measure n =
      ∫ t : {e : SpatialVertex n × Fin 3 // ¬ isTree n e} → EuclideanSpace ℝ (Fin 3),
        F (treeGlue n fun e => refField n e * gnomQ (t e)) /
          frameWeight (refField n) (fun e => refField n e * gnomQ (t e)) ∂(Measure.pi fun _ => gnomMeasure) := by
  have hs2 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  exact integral_tree_chart_of_close n F hF (refField n) (1 / 2) (1 / 4) (by norm_num) (by linarith only [hs2])
    fun x hx => valley_close n σ hσ x (hsupp _ hx)

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedValleyChart
