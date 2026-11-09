/- SU(2) fields of zero twisted action for the spatial twist n₁₂ = 1. An explicit
such field exists. For every one, the winding holonomies in directions 1 and 2
anticommute, so those in directions 0 and 3 are ±1. This is the gauge-invariant
form of the absence of flat zero modes. It says nothing about the quantum theory. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedReflection
import UnifiedTheory.Clay.YangMills.Twisted.TwistedRectangle
import UnifiedTheory.Clay.YangMills.WilsonSingleLinkStaples

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedFlat
noncomputable section
open PeriodicLattice4 TwistedRectangle
open WilsonSingleLinkStaples (Q character character_re)
open scoped Quaternion

/-- The central involution of SU(2). -/
def ω : Q := ⟨-1, by simp [Unitary.mem_iff]⟩

@[simp] theorem ω_coe : ((ω : Q) : ℍ[ℝ]) = -1 := rfl

theorem ω_commute (g : Q) : Commute ω g := by
  apply Subtype.ext
  change ((-1 : ℍ[ℝ]) * (g : ℍ[ℝ])) = (g : ℍ[ℝ]) * (-1)
  simp

theorem unit_normSq (q : Q) :
    (q : ℍ[ℝ]).re ^ 2 + (q : ℍ[ℝ]).imI ^ 2 + (q : ℍ[ℝ]).imJ ^ 2 + (q : ℍ[ℝ]).imK ^ 2 = 1 := by
  have h : star (q : ℍ[ℝ]) * (q : ℍ[ℝ]) = 1 := Unitary.coe_star_mul_self q
  rw [Quaternion.star_mul_self] at h
  have h2 := congrArg QuaternionAlgebra.re h
  simp only [Quaternion.re_coe, Quaternion.re_one] at h2
  rw [Quaternion.normSq_def'] at h2
  exact h2

/-- A unit quaternion commuting with two anticommuting unit quaternions is ±1. -/
theorem central_of_anticommuting (a b q : Q) (hab : a * b = ω * (b * a))
    (hqa : q * a = a * q) (hqb : q * b = b * q) : q = 1 ∨ q = ω := by
  have na := unit_normSq a
  have nb := unit_normSq b
  have nq := unit_normSq q
  have hab' : (a : ℍ[ℝ]) * (b : ℍ[ℝ]) = -1 * ((b : ℍ[ℝ]) * (a : ℍ[ℝ])) :=
    congrArg (Subtype.val) hab
  have hqa' : (q : ℍ[ℝ]) * (a : ℍ[ℝ]) = (a : ℍ[ℝ]) * (q : ℍ[ℝ]) := congrArg Subtype.val hqa
  have hqb' : (q : ℍ[ℝ]) * (b : ℍ[ℝ]) = (b : ℍ[ℝ]) * (q : ℍ[ℝ]) := congrArg Subtype.val hqb
  generalize (a : ℍ[ℝ]) = A at *
  generalize (b : ℍ[ℝ]) = B at *
  have hq0 : ((q : ℍ[ℝ]) = 1 ∨ (q : ℍ[ℝ]) = -1) := by
    generalize (q : ℍ[ℝ]) = C at *
    rcases A with ⟨a0, a1, a2, a3⟩
    rcases B with ⟨b0, b1, b2, b3⟩
    rcases C with ⟨q0, v1, v2, v3⟩
    simp only [] at na nb nq
    have e0 := congrArg QuaternionAlgebra.re hab'
    have e1 := congrArg QuaternionAlgebra.imI hab'
    have e2 := congrArg QuaternionAlgebra.imJ hab'
    have e3 := congrArg QuaternionAlgebra.imK hab'
    have f1 := congrArg QuaternionAlgebra.imI hqa'
    have f2 := congrArg QuaternionAlgebra.imJ hqa'
    have f3 := congrArg QuaternionAlgebra.imK hqa'
    have g1 := congrArg QuaternionAlgebra.imI hqb'
    have g2 := congrArg QuaternionAlgebra.imJ hqb'
    have g3 := congrArg QuaternionAlgebra.imK hqb'
    simp only [neg_mul, one_mul] at e0 e1 e2 e3
    simp only [Quaternion.re_neg, Quaternion.imI_neg, Quaternion.imJ_neg, Quaternion.imK_neg,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
      at e0 e1 e2 e3 f1 f2 f3 g1 g2 g3
    -- b has vanishing real part, a·b = 0.
    have hb0 : b0 = 0 := by
      have : b0 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + a3 ^ 2) = 0 := by
        linear_combination (a0 / 2) * e0 + (a1 / 2) * e1 + (a2 / 2) * e2 + (a3 / 2) * e3
      rw [na] at this
      linarith
    have ha0 : a0 = 0 := by
      have : a0 * (b0 ^ 2 + b1 ^ 2 + b2 ^ 2 + b3 ^ 2) = 0 := by
        linear_combination (b0 / 2) * e0 + (b1 / 2) * e1 + (b2 / 2) * e2 + (b3 / 2) * e3
      rw [nb] at this
      linarith
    subst hb0 ha0
    have hdot : a1 * b1 + a2 * b2 + a3 * b3 = 0 := by linear_combination (-1 / 2) * e0
    -- v ⟂ a, using v×b = 0 and a·b = 0.
    have hva : v1 * a1 + v2 * a2 + v3 * a3 = 0 := by
      have : (v1 * a1 + v2 * a2 + v3 * a3) * (b1 ^ 2 + b2 ^ 2 + b3 ^ 2) = 0 := by
        have c1 : v2 * b3 - v3 * b2 = 0 := by linarith only [g1]
        have c2 : v3 * b1 - v1 * b3 = 0 := by linarith only [g2]
        have c3 : v1 * b2 - v2 * b1 = 0 := by linarith only [g3]
        linear_combination (v1 * b1 + v2 * b2 + v3 * b3) * hdot +
          (a2 * b3 - a3 * b2) * c1 + (a3 * b1 - a1 * b3) * c2 + (a1 * b2 - a2 * b1) * c3
      have hb : b1 ^ 2 + b2 ^ 2 + b3 ^ 2 = 1 := by linarith only [nb]
      rw [hb] at this
      linarith
    -- Lagrange: |v|²|a|² = |v×a|² + (v·a)².
    have hv : v1 ^ 2 + v2 ^ 2 + v3 ^ 2 = 0 := by
      have c1 : v2 * a3 - v3 * a2 = 0 := by linarith only [f1]
      have c2 : v3 * a1 - v1 * a3 = 0 := by linarith only [f2]
      have c3 : v1 * a2 - v2 * a1 = 0 := by linarith only [f3]
      have ha : a1 ^ 2 + a2 ^ 2 + a3 ^ 2 = 1 := by linarith only [na]
      have : (v1 ^ 2 + v2 ^ 2 + v3 ^ 2) * (a1 ^ 2 + a2 ^ 2 + a3 ^ 2) = 0 := by
        linear_combination (v2 * a3 - v3 * a2) * c1 + (v3 * a1 - v1 * a3) * c2 +
          (v1 * a2 - v2 * a1) * c3 + (v1 * a1 + v2 * a2 + v3 * a3) * hva
      rwa [ha, mul_one] at this
    have h1 : v1 = 0 := by nlinarith [sq_nonneg v1, sq_nonneg v2, sq_nonneg v3]
    have h2 : v2 = 0 := by nlinarith [sq_nonneg v1, sq_nonneg v2, sq_nonneg v3]
    have h3 : v3 = 0 := by nlinarith [sq_nonneg v1, sq_nonneg v2, sq_nonneg v3]
    subst h1 h2 h3
    have hq : (q0 - 1) * (q0 + 1) = 0 := by linear_combination nq
    rcases mul_eq_zero.mp hq with h | h
    · left
      have : q0 = 1 := by linarith
      subst this
      ext <;> simp
    · right
      have : q0 = -1 := by linarith
      subst this
      ext <;> simp
  rcases hq0 with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

variable {N : ℕ}

/-- Exponent of ω on each plaquette for the twist `n₁₂ = 1`. -/
def twistExp (μ ν : Fin 4) (x : Vertex N) : ℕ :=
  if μ = 1 ∧ ν = 2 ∧ x 1 = 0 ∧ x 2 = 0 then 1 else 0

/-- Every plaquette below the twist equals the corresponding power of ω. -/
def TwistedFlatField (L : Vertex N → Fin 4 → Q) : Prop :=
  ∀ x μ ν, μ < ν →
    L x μ * L (step N x μ) ν * (L (step N x ν) μ)⁻¹ * (L x ν)⁻¹ = ω ^ twistExp μ ν x

theorem cell_of_flat (L : Vertex N → Fin 4 → Q) (h : TwistedFlatField L) (μ ν : Fin 4)
    (hμν : μ < ν) (y : Vertex N) :
    L y μ * L (step N y μ) ν = ω ^ twistExp μ ν y * (L y ν * L (step N y ν) μ) := by
  rw [← h y μ ν hμν]
  group

theorem walk_apply_same (μ : Fin 4) (x : Vertex N) (k : ℕ) : walk μ x k μ = x μ + k := by
  simp [walk]

theorem walk_apply_other (μ κ : Fin 4) (hκ : κ ≠ μ) (x : Vertex N) (k : ℕ) :
    walk μ x k κ = x κ := by
  simp [walk, hκ]

theorem indicator_sum [NeZero N] (a : ZMod N) :
    (∑ i ∈ Finset.range N, if a + (i : ZMod N) = 0 then 1 else 0) = 1 := by
  have hc (i : ℕ) (hi : i ∈ Finset.range N) :
      (if a + (i : ZMod N) = 0 then 1 else 0) = if i = (-a).val then 1 else 0 := by
    have hlt : i < N := Finset.mem_range.mp hi
    have : a + (i : ZMod N) = 0 ↔ i = (-a).val := by
      constructor
      · intro h
        have : (i : ZMod N) = -a := by linear_combination h
        rw [← this, ZMod.val_natCast_of_lt hlt]
      · intro h
        rw [h, ZMod.natCast_zmod_val]
        ring
    simp only [this]
  rw [Finset.sum_congr rfl hc, Finset.sum_ite_eq']
  simp [ZMod.val_lt]

theorem twist_total [NeZero N] (x : Vertex N) :
    (∑ j ∈ Finset.range N, ∑ i ∈ Finset.range N,
      twistExp (N := N) 1 2 (walk 1 (walk 2 x j) i)) = 1 := by
  have h (i j : ℕ) : twistExp (N := N) 1 2 (walk 1 (walk 2 x j) i) =
      (if x 1 + (i : ZMod N) = 0 then 1 else 0) * (if x 2 + (j : ZMod N) = 0 then 1 else 0) := by
    have e1 : walk 1 (walk 2 x j) i 1 = x 1 + i := by
      rw [walk_apply_same, walk_apply_other 2 1 (by decide)]
    have e2 : walk 1 (walk 2 x j) i 2 = x 2 + j := by
      rw [walk_apply_other 1 2 (by decide), walk_apply_same]
    unfold twistExp
    rw [e1, e2]
    by_cases ha : x 1 + (i : ZMod N) = 0 <;> by_cases hb : x 2 + (j : ZMod N) = 0 <;> simp [ha, hb]
  simp only [h, ← Finset.sum_mul, indicator_sum, one_mul]

/-- Winding holonomy through `x` in direction `μ`. -/
def wind (L : Vertex N → Fin 4 → Q) (μ : Fin 4) (x : Vertex N) : Q := run L μ x N

theorem wind_commute_of_flat (L : Vertex N → Fin 4 → Q) (h : TwistedFlatField L) (μ ν : Fin 4)
    (hμν : μ < ν) (hne : ¬ (μ = 1 ∧ ν = 2)) (x : Vertex N) :
    wind L μ x * wind L ν x = wind L ν x * wind L μ x := by
  have hw := winding L ω ω_commute μ ν (twistExp μ ν) (cell_of_flat L h μ ν hμν) x
  have hz : ∀ y : Vertex N, twistExp μ ν y = 0 := by
    intro y
    unfold twistExp
    rw [if_neg]
    tauto
  simpa [hz] using hw

/-- The classification of twisted flat fields, in gauge-invariant form. -/
theorem wind_classification [NeZero N] (L : Vertex N → Fin 4 → Q) (h : TwistedFlatField L)
    (x : Vertex N) :
    wind L 1 x * wind L 2 x = ω * (wind L 2 x * wind L 1 x) ∧
      (wind L 0 x = 1 ∨ wind L 0 x = ω) ∧ (wind L 3 x = 1 ∨ wind L 3 x = ω) := by
  have h12 : wind L 1 x * wind L 2 x = ω * (wind L 2 x * wind L 1 x) := by
    have hw := winding L ω ω_commute 1 2 (twistExp 1 2) (cell_of_flat L h 1 2 (by decide)) x
    rw [twist_total, pow_one] at hw
    exact hw
  refine ⟨h12, ?_, ?_⟩
  · exact central_of_anticommuting _ _ _ h12
      (wind_commute_of_flat L h 0 1 (by decide) (by decide) x)
      (wind_commute_of_flat L h 0 2 (by decide) (by decide) x)
  · exact central_of_anticommuting _ _ _ h12
      (wind_commute_of_flat L h 1 3 (by decide) (by decide) x).symm
      (wind_commute_of_flat L h 2 3 (by decide) (by decide) x).symm

/-! ### An explicit twisted flat field -/

def qI : Q := ⟨⟨0, 1, 0, 0⟩, by
  rw [Unitary.mem_iff]; constructor <;> ext <;> simp⟩

def qJ : Q := ⟨⟨0, 0, 1, 0⟩, by
  rw [Unitary.mem_iff]; constructor <;> ext <;> simp⟩

theorem commutator_IJ : qI * qJ * qI⁻¹ * qJ⁻¹ = ω := by
  have hi : qI⁻¹ = ω * qI := by
    apply Subtype.ext
    change star ((qI : Q) : ℍ[ℝ]) = (-1) * ((qI : Q) : ℍ[ℝ])
    ext <;> simp [qI]
  have hj : qJ⁻¹ = ω * qJ := by
    apply Subtype.ext
    change star ((qJ : Q) : ℍ[ℝ]) = (-1) * ((qJ : Q) : ℍ[ℝ])
    ext <;> simp [qJ]
  rw [hi, hj]
  apply Subtype.ext
  change ((qI : ℍ[ℝ]) * (qJ : ℍ[ℝ]) * ((-1) * (qI : ℍ[ℝ])) * ((-1) * (qJ : ℍ[ℝ]))) = -1
  ext <;> simp [qI, qJ]

/-- Links `i` across `x₁ = 0`, `j` across `x₂ = 0`, identity otherwise. -/
def flatLink (x : Vertex N) (μ : Fin 4) : Q :=
  if μ = 1 ∧ x 1 = 0 then qI else if μ = 2 ∧ x 2 = 0 then qJ else 1

theorem step_other (x : Vertex N) (μ κ : Fin 4) (h : κ ≠ μ) : step N x μ κ = x κ := by
  simp [step, h]

theorem flatLink_flat : TwistedFlatField (N := N) flatLink := by
  intro x μ ν hμν
  have l1 (y : Vertex N) : flatLink y 1 = if y 1 = 0 then qI else 1 := by simp [flatLink]
  have l2 (y : Vertex N) : flatLink y 2 = if y 2 = 0 then qJ else 1 := by simp [flatLink]
  have l0 (y : Vertex N) : flatLink y 0 = 1 := by simp [flatLink]
  have l3 (y : Vertex N) : flatLink y 3 = 1 := by simp [flatLink]
  have e12 : step N x 1 2 = x 2 := step_other x 1 2 (by decide)
  have e21 : step N x 2 1 = x 1 := step_other x 2 1 (by decide)
  have e31 : step N x 3 1 = x 1 := step_other x 3 1 (by decide)
  have e32 : step N x 3 2 = x 2 := step_other x 3 2 (by decide)
  have e01 : step N x 0 1 = x 1 := step_other x 0 1 (by decide)
  have e02 : step N x 0 2 = x 2 := step_other x 0 2 (by decide)
  have p01 : flatLink x 0 * flatLink (step N x 0) 1 * (flatLink (step N x 1) 0)⁻¹ *
      (flatLink x 1)⁻¹ = ω ^ twistExp (N := N) 0 1 x := by
    simp only [l0, l1, e01, twistExp]
    by_cases h1 : x 1 = 0 <;> simp [h1]
  have p02 : flatLink x 0 * flatLink (step N x 0) 2 * (flatLink (step N x 2) 0)⁻¹ *
      (flatLink x 2)⁻¹ = ω ^ twistExp (N := N) 0 2 x := by
    simp only [l0, l2, e02, twistExp]
    by_cases h2 : x 2 = 0 <;> simp [h2]
  have p03 : flatLink x 0 * flatLink (step N x 0) 3 * (flatLink (step N x 3) 0)⁻¹ *
      (flatLink x 3)⁻¹ = ω ^ twistExp (N := N) 0 3 x := by
    simp [l0, l3, twistExp]
  have p12 : flatLink x 1 * flatLink (step N x 1) 2 * (flatLink (step N x 2) 1)⁻¹ *
      (flatLink x 2)⁻¹ = ω ^ twistExp (N := N) 1 2 x := by
    simp only [l1, l2, e12, e21, twistExp]
    by_cases h1 : x 1 = 0 <;> by_cases h2 : x 2 = 0 <;> simp [h1, h2, commutator_IJ]
  have p13 : flatLink x 1 * flatLink (step N x 1) 3 * (flatLink (step N x 3) 1)⁻¹ *
      (flatLink x 3)⁻¹ = ω ^ twistExp (N := N) 1 3 x := by
    simp only [l1, l3, e31, twistExp]
    by_cases h1 : x 1 = 0 <;> simp [h1]
  have p23 : flatLink x 2 * flatLink (step N x 2) 3 * (flatLink (step N x 3) 2)⁻¹ *
      (flatLink x 3)⁻¹ = ω ^ twistExp (N := N) 2 3 x := by
    simp only [l2, l3, e32, twistExp]
    by_cases h2 : x 2 = 0 <;> simp [h2]
  fin_cases μ <;> fin_cases ν <;> first
    | exact absurd hμν (by decide)
    | exact p01 | exact p02 | exact p03 | exact p12 | exact p13 | exact p23

/-! ### Zero action on the actual periodic lattice -/

open TwistedReflection PeriodicPlaquetteReflection PeriodicTimeReflection RegulatedGauge

variable (n : ℕ) [NeZero n]

theorem re_le_one (q : Q) : |(q : ℍ[ℝ]).re| ≤ 1 := by
  have h := unit_normSq q
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (q : ℍ[ℝ]).imI, sq_nonneg (q : ℍ[ℝ]).imJ,
    sq_nonneg (q : ℍ[ℝ]).imK, sq_nonneg ((q : ℍ[ℝ]).re - 1), sq_nonneg ((q : ℍ[ℝ]).re + 1)]

theorem eq_of_re_eq (q : Q) (s : ℝ) (hs : s * s = 1) (h : (q : ℍ[ℝ]).re = s) :
    (q : ℍ[ℝ]) = ⟨s, 0, 0, 0⟩ := by
  have hn := unit_normSq q
  rw [h] at hn
  have h1 : (q : ℍ[ℝ]).imI = 0 := by
    nlinarith [sq_nonneg (q : ℍ[ℝ]).imI, sq_nonneg (q : ℍ[ℝ]).imJ, sq_nonneg (q : ℍ[ℝ]).imK]
  have h2 : (q : ℍ[ℝ]).imJ = 0 := by
    nlinarith [sq_nonneg (q : ℍ[ℝ]).imI, sq_nonneg (q : ℍ[ℝ]).imJ, sq_nonneg (q : ℍ[ℝ]).imK]
  have h3 : (q : ℍ[ℝ]).imK = 0 := by
    nlinarith [sq_nonneg (q : ℍ[ℝ]).imI, sq_nonneg (q : ℍ[ℝ]).imJ, sq_nonneg (q : ℍ[ℝ]).imK]
  ext
  · exact h
  · exact h1
  · exact h2
  · exact h3

theorem spatialTwist_eq (x : Vertex (2 * n)) (μ ν : Fin 4) (h : μ < ν) :
    spatialTwist n (x, ⟨(μ, ν), h⟩) = if twistExp μ ν x = 1 then -1 else 1 := by
  classical
  by_cases hc : μ = 1 ∧ ν = 2 ∧ x 1 = 0 ∧ x 2 = 0
  · simp [spatialTwist, twistExp, hc]
  · have hc' : ¬ ((μ, ν) = ((1, 2) : Fin 4 × Fin 4) ∧ x 1 = 0 ∧ x 2 = 0) := by
      rintro ⟨h1, h2, h3⟩
      exact hc ⟨congrArg Prod.fst h1, congrArg Prod.snd h1, h2, h3⟩
    change (if ((μ, ν) = ((1, 2) : Fin 4 × Fin 4) ∧ x 1 = 0 ∧ x 2 = 0) then (-1 : ℝ) else 1) = _
    rw [if_neg hc']
    simp [twistExp, hc]

theorem term_nonneg (U : Configuration (Vertex (2 * n)) Q) (p : PlaquetteIndex (2 * n)) :
    0 ≤ term n Q (spatialTwist n) character 2 U p := by
  classical
  unfold term
  rw [character_re]
  have h := abs_le.mp (re_le_one (plaquetteProduct (2 * n) Q U p.1 p.2.1.1 p.2.1.2))
  unfold spatialTwist
  split_ifs <;> linarith [h.1, h.2]

theorem action_nonneg (β : ℝ) (hβ : 0 ≤ β) (U : Configuration (Vertex (2 * n)) Q) :
    0 ≤ action n Q (spatialTwist n) character β 2 U :=
  mul_nonneg hβ (Finset.sum_nonneg fun p _ => term_nonneg n U p)

/-- Every zero-action configuration of the spatially twisted SU(2) law is twisted flat. -/
theorem flat_of_action_zero (β : ℝ) (hβ : 0 < β) (U : Configuration (Vertex (2 * n)) Q)
    (h : action n Q (spatialTwist n) character β 2 U = 0) :
    TwistedFlatField (N := 2 * n) (linkValue (2 * n) Q U) := by
  intro x μ ν hμν
  have hs : ∑ p, term n Q (spatialTwist n) character 2 U p = 0 := by
    rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd h0 hβ.ne'
    · exact h0
  have ht := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => term_nonneg n U p)).mp hs
    (x, ⟨(μ, ν), hμν⟩) (Finset.mem_univ _)
  unfold term at ht
  rw [spatialTwist_eq, character_re] at ht
  change plaquetteProduct (2 * n) Q U x μ ν = _
  simp only at ht
  generalize hq : plaquetteProduct (2 * n) Q U x μ ν = q at ht ⊢
  by_cases hc : twistExp μ ν x = 1
  · rw [if_pos hc] at ht
    rw [hc, pow_one]
    have hre : (q : ℍ[ℝ]).re = -1 := by linarith
    apply Subtype.ext
    rw [eq_of_re_eq q (-1) (by norm_num) hre]
    ext <;> simp
  · rw [if_neg hc] at ht
    have h0 : twistExp μ ν x = 0 := by
      unfold twistExp at hc ⊢
      split_ifs at hc ⊢ with hh
      · exact absurd rfl hc
      · rfl
    rw [h0, pow_zero]
    have hre : (q : ℍ[ℝ]).re = 1 := by linarith
    apply Subtype.ext
    rw [eq_of_re_eq q 1 (by norm_num) hre]
    ext <;> simp

/-- The classification, for every minimizing configuration of the twisted action. -/
theorem wind_classification_of_action_zero (β : ℝ) (hβ : 0 < β)
    (U : Configuration (Vertex (2 * n)) Q)
    (h : action n Q (spatialTwist n) character β 2 U = 0) (x : Vertex (2 * n)) :
    wind (linkValue (2 * n) Q U) 1 x * wind (linkValue (2 * n) Q U) 2 x =
        ω * (wind (linkValue (2 * n) Q U) 2 x * wind (linkValue (2 * n) Q U) 1 x) ∧
      (wind (linkValue (2 * n) Q U) 0 x = 1 ∨ wind (linkValue (2 * n) Q U) 0 x = ω) ∧
      (wind (linkValue (2 * n) Q U) 3 x = 1 ∨ wind (linkValue (2 * n) Q U) 3 x = ω) :=
  wind_classification _ (flat_of_action_zero n β hβ U h) x

/-- The explicit configuration with links `flatLink`. -/
def flatConfiguration : Configuration (Vertex (2 * n)) Q :=
  fun e => flatLink (edgeCoordinates (2 * n) e).1 (edgeCoordinates (2 * n) e).2

theorem flatConfiguration_link : linkValue (2 * n) Q (flatConfiguration n) = flatLink := rfl

/-- The twisted action attains its minimum zero, so the classification is not vacuous. -/
theorem action_flatConfiguration (β : ℝ) :
    action n Q (spatialTwist n) character β 2 (flatConfiguration n) = 0 := by
  unfold action
  rw [Finset.sum_eq_zero, mul_zero]
  rintro ⟨x, ⟨⟨μ, ν⟩, hμν⟩⟩ _
  unfold term
  rw [spatialTwist_eq, character_re]
  have hf := flatLink_flat (N := 2 * n) x μ ν hμν
  change plaquetteProduct (2 * n) Q (flatConfiguration n) x μ ν = _ at hf
  simp only
  rw [hf]
  by_cases hc : twistExp (N := 2 * n) μ ν x = 1
  · simp [hc]
  · have h0 : twistExp (N := 2 * n) μ ν x = 0 := by
      unfold twistExp at hc ⊢
      split_ifs at hc ⊢ with hh
      · exact absurd rfl hc
      · rfl
    simp [h0]

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedFlat
