/- A slice lifted to a static 4D link field, with trivial temporal links. This transports the
Stokes and winding estimates to slices. The holonomy `W₃` defines a gauge-invariant bounded function
that changes sign under the center flip and is near `±1` when the twisted potential is small. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedTreeGauge
import UnifiedTheory.Clay.YangMills.Twisted.TwistedLandau
import UnifiedTheory.Clay.YangMills.Twisted.TwistedSeams
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedSliceLift
noncomputable section
open PeriodicLattice4 TwistedRectangle TwistedFlat TwistedStability TwistedLandau TwistedSeams
open WilsonTimeSlab WilsonSlabOperator TwistedTransfer
open WilsonSingleLinkStaples (character character_re)
open scoped Quaternion

variable (n : ℕ) [NeZero n]

/-- The spatial part of a 4D vertex. -/
def sp (x : Vertex n) : SpatialVertex n := fun i => x i.succ

/-- The static lift of a slice. -/
def lift (u : Slice n) : Vertex n → Fin 4 → Q :=
  fun x μ => Fin.cases 1 (fun i => u (sp n x, i)) μ

theorem lift_zero (u : Slice n) (x : Vertex n) : lift n u x 0 = 1 := rfl

theorem lift_succ (u : Slice n) (x : Vertex n) (i : Fin 3) :
    lift n u x i.succ = u (sp n x, i) := rfl

theorem sp_step_zero (x : Vertex n) : sp n (step n x 0) = sp n x := by
  funext i
  simp [sp, step, Fin.succ_ne_zero]

theorem sp_step_succ (x : Vertex n) (i : Fin 3) :
    sp n (step n x i.succ) = spatialStep n (sp n x) i := by
  funext j
  by_cases h : j = i
  · subst h
    simp [sp, step, spatialStep]
  · have h' : j.succ ≠ i.succ := fun e => h (Fin.succ_injective _ e)
    simp [sp, step, spatialStep, h, h']

/-- A slice gauge lifts to a 4D gauge. -/
theorem lift_gauge (h : SliceGauge n Q) (v : Slice n) :
    lift n (gaugeSlice h v) = act (fun x => h (sp n x)) (lift n v) := by
  funext x μ
  refine Fin.cases ?_ (fun i => ?_) μ
  · simp only [lift_zero, act, sp_step_zero]
    group
  · simp only [lift_succ, act, sp_step_succ]
    rfl

/-- The plaquette of the lift in a spatial plane is the spatial holonomy. -/
theorem lift_plaquette (u : Slice n) (x : Vertex n) (i j : Fin 3) :
    lift n u x i.succ * lift n u (step n x i.succ) j.succ *
        (lift n u (step n x j.succ) i.succ)⁻¹ * (lift n u x j.succ)⁻¹ =
      spatialHolonomy u (sp n x) i j := by
  simp only [lift_succ, sp_step_succ]
  rfl

/-- Temporal plaquettes of the lift are trivial. -/
theorem lift_plaquette_time (u : Slice n) (x : Vertex n) (i : Fin 3) :
    lift n u x 0 * lift n u (step n x 0) i.succ * (lift n u (step n x i.succ) 0)⁻¹ *
        (lift n u x i.succ)⁻¹ = 1 := by
  simp only [lift_zero, lift_succ, sp_step_zero]
  group

/-- The spatial twist has the sign of `twistExp` in lifted coordinates. -/
theorem spatialSign_eq (x : Vertex n) (p : SpatialPlane) :
    spatialSign n (sp n x) p = if twistExp (N := n) p.1.1.succ p.1.2.succ x = 1 then -1 else 1 := by
  classical
  unfold spatialSign twistExp
  rcases p with ⟨⟨i, j⟩, h⟩
  by_cases hc : (i, j) = ((0, 1) : Fin 3 × Fin 3) ∧ sp n x 0 = 0 ∧ sp n x 1 = 0
  · obtain ⟨h1, h2, h3⟩ := hc
    have hi : i = 0 := congrArg Prod.fst h1
    have hj : j = 1 := congrArg Prod.snd h1
    subst hi hj
    have hx1 : x 1 = 0 := h2
    have hx2 : x 2 = 0 := h3
    simp [hx1, hx2, sp]
  · have hne : ¬ ((i : Fin 3).succ = 1 ∧ (j : Fin 3).succ = 2 ∧ x 1 = 0 ∧ x 2 = 0) := by
      rintro ⟨h1, h2, h3, h4⟩
      apply hc
      have hi : i = 0 := Fin.succ_injective _ (by simpa using h1)
      have hj : j = 1 := Fin.succ_injective _ (by simpa using h2)
      subst hi hj
      exact ⟨rfl, h3, h4⟩
    have hne' : ¬ ((i, j) = ((0, 1) : Fin 3 × Fin 3) ∧ sp n x 0 = 0 ∧ sp n x 1 = 0) := hc
    simp only [if_neg hne', if_neg hne]
    simp

/-- Each potential term of the twisted slice is a squared defect of the lift. -/
theorem potential_term_eq (u : Slice n) (x : Vertex n) (p : SpatialPlane) :
    2 - spatialSign n (sp n x) p * (character (spatialHolonomy u (sp n x) p.1.1 p.1.2)).re =
      TwistedStability.defect (lift n u) p.1.1.succ p.1.2.succ x ^ 2 := by
  unfold TwistedStability.defect
  rw [lift_plaquette, spatialSign_eq, character_re, d_sq_eq]
  generalize spatialHolonomy u (sp n x) p.1.1 p.1.2 = P
  rcases (by unfold twistExp; split_ifs <;> simp :
    twistExp (N := n) p.1.1.succ p.1.2.succ x = 0 ∨ twistExp (N := n) p.1.1.succ p.1.2.succ x = 1)
    with hc | hc
  · rw [hc]
    simp [rePart]
  · rw [hc]
    have hinv : (ω : Q)⁻¹ = ω := inv_eq_of_mul_eq_one_left TwistedTransfer.ω_mul_ω
    simp only [if_true, pow_one, rePart, hinv, ω_coe]
    simp

/-- The twisted potential is nonnegative termwise, and any one term is bounded by it. -/
theorem defect_sq_le_potential (u : Slice n) (y : SpatialVertex n) (p : SpatialPlane) (x : Vertex n)
    (hx : sp n x = y) :
    TwistedStability.defect (lift n u) p.1.1.succ p.1.2.succ x ^ 2 ≤ twistedPotential n u := by
  rw [← potential_term_eq, hx]
  unfold twistedPotential
  have nonneg : ∀ (z : SpatialVertex n) (q : SpatialPlane),
      0 ≤ 2 - spatialSign n z q * (character (spatialHolonomy u z q.1.1 q.1.2)).re := by
    intro z q
    obtain ⟨t, ht⟩ : ∃ t : Vertex n, sp n t = z := ⟨Fin.cases 0 z, rfl⟩
    have := potential_term_eq n u t q
    rw [ht] at this
    rw [this]
    exact sq_nonneg _
  calc _ ≤ ∑ q : SpatialPlane, (2 - spatialSign n y q * (character (spatialHolonomy u y q.1.1 q.1.2)).re) :=
        Finset.single_le_sum (f := fun q : SpatialPlane =>
          2 - spatialSign n y q * (character (spatialHolonomy u y q.1.1 q.1.2)).re)
          (fun q _ => nonneg y q) (Finset.mem_univ p)
    _ ≤ _ := Finset.single_le_sum (f := fun z : SpatialVertex n => ∑ q : SpatialPlane,
          (2 - spatialSign n z q * (character (spatialHolonomy u z q.1.1 q.1.2)).re))
          (fun z _ => Finset.sum_nonneg fun q _ => nonneg z q) (Finset.mem_univ y)

theorem potential_nonneg (u : Slice n) : 0 ≤ twistedPotential n u := by
  have := defect_sq_le_potential n u 0 ⟨(0, 1), by decide⟩ 0 (by funext i; rfl)
  exact (sq_nonneg _).trans this

/-! ### The holonomy function -/

/-- The base point. -/
abbrev base : Vertex n := 0

/-- The `W₃` winding of the lift through the base point. -/
def wind3 (u : Slice n) : Q := run (lift n u) 3 (base n) n

/-- The sign-like holonomy observable. -/
def holo (u : Slice n) : ℝ := ((wind3 n u : Q) : ℍ[ℝ]).re

theorem holo_abs_le (u : Slice n) : |holo n u| ≤ 1 := re_le_one _

/-- Winding under a gauge transformation. -/
theorem run_act {N : ℕ} (g : Vertex N → Q) (L : Vertex N → Fin 4 → Q) (μ : Fin 4) (x : Vertex N)
    (m : ℕ) : run (act g L) μ x m = g x * run L μ x m * (g (walk μ x m))⁻¹ := by
  induction m with
  | zero =>
    simp [run, walk_zero]
  | succ m ih =>
    simp only [run, act, ih, walk_succ]
    group

/-- `holo` is gauge invariant. -/
theorem holo_gauge (h : SliceGauge n Q) (u : Slice n) : holo n (gaugeSlice h u) = holo n u := by
  unfold holo wind3
  rw [lift_gauge, run_act, walk_card]
  set g := h (sp n (base n))
  set W := run (lift n u) 3 (base n) n
  change ((g : ℍ[ℝ]) * (W : ℍ[ℝ]) * ((g⁻¹ : Q) : ℍ[ℝ])).re = _
  have : ((g⁻¹ : Q) : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 := congrArg Subtype.val (inv_mul_cancel g)
  rw [mul_assoc, TwistedActionJet.re_comm, mul_assoc, this, mul_one]

/-- Winding holonomies are Lipschitz in the links along the line. -/
theorem run_lipschitz {N : ℕ} (L L' : Vertex N → Fin 4 → Q) (μ : Fin 4) (x : Vertex N) (m : ℕ) :
    d (run L μ x m) (run L' μ x m) ≤
      ∑ k ∈ Finset.range m, d (L (walk μ x k) μ) (L' (walk μ x k) μ) := by
  induction m with
  | zero => simp [run, d]
  | succ m ih =>
    simp only [run, Finset.sum_range_succ]
    have t := d_triangle (run L μ x m * L (walk μ x m) μ) (run L' μ x m * L (walk μ x m) μ)
      (run L' μ x m * L' (walk μ x m) μ)
    rw [d_mul_right, d_mul_left] at t
    linarith only [t, ih]

theorem abs_re_sub_le (g h : Q) : |((g : Q) : ℍ[ℝ]).re - ((h : Q) : ℍ[ℝ]).re| ≤ d g h := by
  unfold d
  set x := (g : ℍ[ℝ]) - (h : ℍ[ℝ]) with hx
  have hre : ((g : Q) : ℍ[ℝ]).re - ((h : Q) : ℍ[ℝ]).re = x.re := by simp [hx]
  rw [hre]
  apply abs_le_of_sq_le_sq _ (norm_nonneg _)
  rw [sq (‖x‖), ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
  nlinarith only [sq_nonneg x.imI, sq_nonneg x.imJ, sq_nonneg x.imK]

/-- A kinetic term is a squared chord. -/
theorem kinetic_term (a b : Q) : 2 - (character (a⁻¹ * b)).re = d a b ^ 2 := by
  rw [character_re]
  have e := d_mul_left a⁻¹ a b
  rw [inv_mul_cancel] at e
  rw [← e, d_comm]
  unfold d
  have := SU2GaussianMass.chord_square (a⁻¹ * b)
  change _ = ‖(((a⁻¹ * b : Q) : ℍ[ℝ])) - 1‖ ^ 2
  rw [this]
  ring

/-- `holo` is Lipschitz with respect to the kinetic action. -/
theorem holo_lipschitz (u v : Slice n) :
    (holo n u - holo n v) ^ 2 ≤ n * kineticAction character 2 u v := by
  have h1 := abs_re_sub_le (wind3 n u) (wind3 n v)
  have h2 := run_lipschitz (lift n u) (lift n v) 3 (base n) n
  set line : ℕ → SpatialVertex n × Fin 3 := fun k => (sp n (walk 3 (base n) k), 2) with hline
  have hlink (w : Slice n) (k : ℕ) : lift n w (walk 3 (base n) k) 3 = w (line k) := rfl
  simp only [hlink] at h2
  have hCS : (∑ k ∈ Finset.range n, d (u (line k)) (v (line k))) ^ 2 ≤
      n * ∑ k ∈ Finset.range n, d (u (line k)) (v (line k)) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range n)
      (f := fun k => d (u (line k)) (v (line k)))
    simpa using this
  have hinj : Set.InjOn line (Finset.range n : Set ℕ) := by
    intro a ha b hb hab
    have hc := congrArg (fun e => e.1 2) hab
    have hval (k : ℕ) : (line k).1 2 = (k : ZMod n) := by
      simp only [hline, sp, walk]
      simp
    simp only [hval] at hc
    have ha' : a < n := Finset.mem_range.mp ha
    have hb' : b < n := Finset.mem_range.mp hb
    have := congrArg ZMod.val hc
    rwa [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] at this
  have hsum : ∑ k ∈ Finset.range n, d (u (line k)) (v (line k)) ^ 2 ≤
      kineticAction character 2 u v := by
    have hk : kineticAction character 2 u v = ∑ e, d (u e) (v e) ^ 2 := by
      unfold kineticAction
      exact Finset.sum_congr rfl fun e _ => kinetic_term _ _
    rw [hk, ← Finset.sum_image (f := fun e => d (u e) (v e) ^ 2) hinj]
    exact Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have habs : |holo n u - holo n v| ≤ ∑ k ∈ Finset.range n, d (u (line k)) (v (line k)) := h1.trans h2
  have hsq : (holo n u - holo n v) ^ 2 ≤ (∑ k ∈ Finset.range n, d (u (line k)) (v (line k))) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  exact hsq.trans (hCS.trans (mul_le_mul_of_nonneg_left hsum hn0))

/-- The flip changes the sign of the winding. -/
theorem holo_flip (u : Slice n) : holo n (TwistedTransfer.flip n 2 0 u) = -holo n u := by
  have hrun : ∀ m : ℕ, run (lift n (TwistedTransfer.flip n 2 0 u)) 3 (base n) m =
      ω ^ (∑ k ∈ Finset.range m, if ((base n) 3 + (k : ZMod n) = 0) then 1 else 0) *
        run (lift n u) 3 (base n) m := by
    intro m
    induction m with
    | zero => simp [run]
    | succ m ih =>
      simp only [run, Finset.sum_range_succ, ih, pow_add]
      have hl : lift n (TwistedTransfer.flip n 2 0 u) (walk 3 (base n) m) 3 =
          (if (base n) 3 + (m : ZMod n) = 0 then ω else 1) * lift n u (walk 3 (base n) m) 3 := by
        have hc : (sp n (walk 3 (base n) m)) 2 = (base n) 3 + (m : ZMod n) := by
          change walk 3 (base n) m 3 = _
          exact walk_apply_same 3 (base n) m
        change TwistedTransfer.flip n 2 0 u (sp n (walk 3 (base n) m), 2) = _
        unfold TwistedTransfer.flip
        simp only [true_and, hc]
        split_ifs
        · rfl
        · rw [one_mul]
          rfl
      rw [hl]
      have hcomm := fun (k : ℕ) (g : Q) => ((ω_commute g).pow_left k)
      by_cases hz : (base n) 3 + (m : ZMod n) = 0
      · simp only [if_pos hz, pow_one]
        rw [← mul_assoc, mul_assoc (ω ^ _), ((ω_commute _).symm).eq]
        simp only [mul_assoc]
      · simp only [if_neg hz, pow_zero, one_mul, mul_one]
        simp only [mul_assoc]
  unfold holo wind3
  rw [hrun n, indicator_sum, pow_one]
  change ((-1 : ℍ[ℝ]) * _).re = _
  simp

/-- **Stability on a slice.** A small twisted potential forces `holo² ≥ 1/2`. -/
theorem holo_sq_of_small (u : Slice n) (hS : twistedPotential n u < 1 / (16 * (n : ℝ) ^ 4)) :
    1 / 2 ≤ holo n u ^ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  set ε := 1 / (4 * (n : ℝ) ^ 2) with hε
  have hε0 : 0 ≤ ε := by positivity
  have hsq : 1 / (16 * (n : ℝ) ^ 4) = ε ^ 2 := by
    rw [hε]
    field_simp
    norm_num
  set L := lift n u with hL
  have hdef (i j : Fin 3) (hij : i < j) (x : Vertex n) :
      TwistedStability.defect L i.succ j.succ x ≤ ε := by
    have h := defect_sq_le_potential n u (sp n x) ⟨(i, j), hij⟩ x rfl
    have h2 : TwistedStability.defect L i.succ j.succ x ^ 2 ≤ ε ^ 2 := by
      rw [← hsq]
      exact h.trans hS.le
    exact abs_le_of_sq_le_sq' h2 hε0 |>.2
  have hsumle (μ ν : Fin 4) (hb : ∀ x, TwistedStability.defect L μ ν x ≤ ε) :
      (∑ j ∈ Finset.range n, ∑ i ∈ Finset.range n,
        TwistedStability.defect L μ ν (walk μ (walk ν (base n) j) i)) ≤ 1 / 4 := by
    calc _ ≤ ∑ _j ∈ Finset.range n, ∑ _i ∈ Finset.range n, ε :=
          Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => hb _
      _ = (n : ℝ) * ((n : ℝ) * ε) := by simp
      _ = 1 / 4 := by
          rw [hε]
          field_simp
  have hwind (μ ν : Fin 4) (hb : ∀ x, TwistedStability.defect L μ ν x ≤ ε) :=
    (winding_error L μ ν (twistExp μ ν) (TwistedStability.defect L μ ν)
      (fun y => cell_of_defect _ _ _ _ _ _ le_rfl) (base n)).trans (hsumle μ ν hb)
  have h12 := hwind 1 2 (hdef 0 1 (by decide))
  have h13 := hwind 1 3 (hdef 0 2 (by decide))
  have h23 := hwind 2 3 (hdef 1 2 (by decide))
  rw [twist_total, pow_one] at h12
  rw [exp_sum_zero 1 3 (by decide), pow_zero, one_mul] at h13
  rw [exp_sum_zero 2 3 (by decide), pow_zero, one_mul] at h23
  have hc := near_central _ _ _ (1 / 4) (by norm_num) (by norm_num) h12
    (by rw [d_comm]; exact h13) (by rw [d_comm]; exact h23)
  set W : Q := run L 3 (base n) n with hW
  have hholo : holo n u = (W : ℍ[ℝ]).re := rfl
  rw [hholo]
  rcases hc with h | h
  · have hsqd := pow_le_pow_left₀ (d_nonneg _ _) h 2
    have e := SU2GaussianMass.chord_square W
    have e2 : d W 1 = ‖(W : ℍ[ℝ]) - 1‖ := rfl
    rw [e2, e] at hsqd
    have hre : 7 / 9 ≤ (W : ℍ[ℝ]).re := by nlinarith only [hsqd]
    nlinarith only [hre]
  · have hsqd := pow_le_pow_left₀ (d_nonneg _ _) h 2
    rw [show d W ω ^ 2 = 2 - 2 * TwistedLandau.rePart W ω from TwistedLandau.d_sq_eq W ω] at hsqd
    have hinv : (ω : Q)⁻¹ = ω := inv_eq_of_mul_eq_one_left TwistedTransfer.ω_mul_ω
    have hp : TwistedLandau.rePart W ω = -(W : ℍ[ℝ]).re := by
      simp only [TwistedLandau.rePart, hinv, ω_coe]
      simp
    rw [hp] at hsqd
    have hre : (W : ℍ[ℝ]).re ≤ -(7 / 9) := by nlinarith only [hsqd]
    nlinarith only [hre]

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedSliceLift
